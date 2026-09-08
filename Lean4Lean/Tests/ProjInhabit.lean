import Lean4Lean.Tests.ShapeDecide
import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.Verify.Typing.Expr

/-!
Inhabitation of `TrProjCtor` on two hand-built inductive blocks: `Plain`, a two-field structure
whose fields have the same type, and `Dependent`, a `Sigma`-shaped one whose second field's type
mentions the first. Each block is declared through `VEnv.addInduct`, so its ι rule is registered
the way a translated environment registers one, and each projection's typing premise is derived
from the forward rules of `IsDefEq` alone -- for the dependent field, through the ι step on the
generic constructor spine, which is the derivation sketched in the module docstring of
`Theory/Proj.lean`. The kernel side of the same builders is `Tests/ProjShape.lean`.

The witnesses are sorry-free; the general construction, from an arbitrary kernel-accepted
projection, is the open `inferProj.WF_struct`.
-/

namespace Lean4Lean.Tests.ProjInhabit

open Lean4Lean
open Lean (Name mkRecName)

/-! ### A two-field structure with a constant motive -/

namespace Plain

def l1 : VLevel := .succ .zero
def Ac : VExpr := .const `A []
def Sc : VExpr := .const `S []
def mkc : VExpr := .const `S.mk []
def ctorTy : VExpr := .forallE Ac (.forallE Ac Sc)
def motiveTy : VExpr := .forallE Sc (.sort (.param 0))
def mkSpine : VExpr := .app (.app mkc (.bvar 1)) (.bvar 0)
def minorTy : VExpr := .forallE Ac (.forallE Ac (.app (.bvar 2) mkSpine))
def recTy : VExpr :=
  .forallE motiveTy (.forallE minorTy (.forallE Sc (.app (.bvar 2) (.bvar 0))))
def ruleRhs : VExpr :=
  .lam motiveTy (.lam minorTy (.lam Ac (.lam Ac (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)))))

def decl : VInductDecl where
  uvars := 0
  nparams := 0
  types := [{ name := `S, uvars := 0, type := .sort l1,
              ctors := [{ name := `S.mk, uvars := 0, type := ctorTy }] }]
  recs := [{ name := mkRecName `S, uvars := 1, type := recTy, all := [`S],
             numParams := 0, numMotives := 1, numMinors := 1, numIndices := 0, k := false,
             rules := [{ ctor := `S.mk, ctorParams := 0, nfields := 2, rhs := ruleRhs }] }]

def env0? : Option VEnv := VEnv.empty.addConst `A ⟨0, .sort l1⟩ |>.bind fun e => e.addInduct decl

theorem env0_isSome : env0?.isSome = true := rfl

def env : VEnv := env0?.get env0_isSome

theorem hA : env.constants `A = some ⟨0, .sort l1⟩ := rfl
theorem hS : env.constants `S = some ⟨0, .sort l1⟩ := rfl
theorem hmk : env.constants `S.mk = some ⟨0, ctorTy⟩ := rfl
theorem hrec : env.constants (mkRecName `S) = some ⟨1, recTy⟩ := rfl

theorem hclosed : ruleRhs.Closed := by decide

def patKey : Pattern := (SimplePattern.iota (mkRecName `S) (0+1+1+0) `S.mk (0+2)).toPattern
def rhsPair : patKey.RHS × patKey.Check :=
  (SimplePattern.iotaRHS (mkRecName `S) `S.mk 0 1 1 0 0 2 ruleRhs hclosed, .true)

theorem hpats : env.pats patKey rhsPair := Or.inl ⟨rfl, rfl⟩

/-! The projection expansion for field 0 and 1 (constant motive `A`). -/

def uss : Nat → List VLevel := fun _ => [l1]
def recC : VExpr := .const (mkRecName `S) [l1]
def M0 : VExpr := .lam Sc Ac
def sel0 : VExpr := .lam Ac (.lam Ac (.bvar 1))
def sel1 : VExpr := .lam Ac (.lam Ac (.bvar 0))
def minorTyM : VExpr := .forallE Ac (.forallE Ac (.app M0 mkSpine))

example : VExpr.projFn `S [] uss [] [Ac, Ac] 0 = .app (.app recC M0) sel0 := by decide
example : VExpr.projFn `S [] uss [] [Ac, Ac] 1 = .app (.app recC M0) sel1 := by decide
example : VExpr.projMotiveBody `S [] uss [] [Ac, Ac] 0 = Ac := by decide
example : VExpr.projMotiveBody `S [] uss [] [Ac, Ac] 1 = Ac := by decide

/-! Typing derivations, generic in the context. -/

theorem lvl1WF : ∀ l ∈ [l1], VLevel.WF 0 l := fun _ h => by
  cases h with
  | head => trivial
  | tail _ h => cases h

theorem hAt (Γ : List VExpr) : env.IsDefEq 0 Γ Ac Ac (.sort l1) :=
  .constDF hA nofun nofun rfl .nil
theorem hSt (Γ : List VExpr) : env.IsDefEq 0 Γ Sc Sc (.sort l1) :=
  .constDF hS nofun nofun rfl .nil
theorem hmkt (Γ : List VExpr) : env.IsDefEq 0 Γ mkc mkc ctorTy :=
  .constDF hmk nofun nofun rfl .nil
theorem hrect (Γ : List VExpr) : env.IsDefEq 0 Γ recC recC (recTy.instL [l1]) :=
  .constDF hrec lvl1WF lvl1WF rfl (.cons rfl .nil)

theorem hM (Γ : List VExpr) : env.IsDefEq 0 Γ M0 M0 (.forallE Sc (.sort l1)) :=
  .lamDF (hSt Γ) (hAt (Sc::Γ))

theorem hspine (Γ : List VExpr) : env.IsDefEq 0 (Ac::Ac::Γ) mkSpine mkSpine Sc :=
  .appDF (.appDF (hmkt _) (.bvar (.succ .zero))) (.bvar .zero)

theorem hbody0 (Γ : List VExpr) :
    env.IsDefEq 0 (Ac::Ac::Γ) (.app M0 mkSpine) Ac (.sort l1) :=
  .beta (hAt _) (hspine Γ)

theorem hselnat0 (Γ : List VExpr) :
    env.IsDefEq 0 Γ sel0 sel0 (.forallE Ac (.forallE Ac Ac)) :=
  .lamDF (hAt Γ) (.lamDF (hAt _) (.bvar (.succ .zero)))
theorem hselnat1 (Γ : List VExpr) :
    env.IsDefEq 0 Γ sel1 sel1 (.forallE Ac (.forallE Ac Ac)) :=
  .lamDF (hAt Γ) (.lamDF (hAt _) (.bvar .zero))

theorem hminorEq (Γ : List VExpr) :
    env.IsDefEq 0 Γ (.forallE Ac (.forallE Ac Ac)) minorTyM
      (.sort (.imax l1 (.imax l1 l1))) :=
  .forallEDF (hAt Γ) (.forallEDF (hAt _) (.symm (hbody0 Γ)))

theorem hsel0 (Γ : List VExpr) : env.IsDefEq 0 Γ sel0 sel0 minorTyM :=
  .defeqDF (hminorEq Γ) (hselnat0 Γ)
theorem hsel1 (Γ : List VExpr) : env.IsDefEq 0 Γ sel1 sel1 minorTyM :=
  .defeqDF (hminorEq Γ) (hselnat1 Γ)

theorem hstep1 (Γ : List VExpr) :
    env.IsDefEq 0 Γ (.app recC M0) (.app recC M0)
      (.forallE minorTyM (.forallE Sc (.app M0 (.bvar 0)))) :=
  .appDF (hrect Γ) (hM Γ)

theorem hbetax (Γ : List VExpr) :
    env.IsDefEq 0 (Sc::Γ) (.app M0 (.bvar 0)) Ac (.sort l1) :=
  .beta (hAt _) (.bvar .zero)

theorem htyEq (Γ : List VExpr) :
    env.IsDefEq 0 Γ (.forallE Sc (.app M0 (.bvar 0))) (.forallE Sc Ac)
      (.sort (.imax l1 l1)) :=
  .forallEDF (hSt Γ) (hbetax Γ)

theorem hProjFn0 (Γ : List VExpr) :
    env.IsDefEq 0 Γ (.app (.app recC M0) sel0) (.app (.app recC M0) sel0)
      (.forallE Sc Ac) :=
  .defeqDF (htyEq Γ) (.appDF (hstep1 Γ) (hsel0 Γ))
theorem hProjFn1 (Γ : List VExpr) :
    env.IsDefEq 0 Γ (.app (.app recC M0) sel1) (.app (.app recC M0) sel1)
      (.forallE Sc Ac) :=
  .defeqDF (htyEq Γ) (.appDF (hstep1 Γ) (hsel1 Γ))

/-! The inhabitation results. -/

/-- Field `0` of the two-field structure: the constant motive `A`. -/
theorem inhab0 :
    TrProjCtor env 0 [Sc] `S 0 (.bvar 0) (.app (.app (.app recC M0) sel0) (.bvar 0)) `S.mk
      [] uss [] 0 [Ac, Ac] :=
  { pat := ⟨rhsPair, hpats⟩
    params_length := rfl
    ctor := ⟨⟨0, ctorTy⟩, hmk, by decide, ctorTy, rfl, rfl⟩
    field_lt := by decide
    minor_arity := ⟨⟨1, recTy⟩, hrec, rfl⟩
    major_ty := .bvar .zero
    fn_ty := hProjFn0 [Sc]
    eq := rfl }

/-- Field `1`, same motive. -/
theorem inhab1 :
    TrProjCtor env 0 [Sc] `S 1 (.bvar 0) (.app (.app (.app recC M0) sel1) (.bvar 0)) `S.mk
      [] uss [] 0 [Ac, Ac] :=
  { inhab0 with
    field_lt := by decide
    fn_ty := hProjFn1 [Sc]
    eq := rfl }

theorem trProj0 : TrProj env 0 [Sc] `S 0 (.bvar 0) (.app (.app (.app recC M0) sel0) (.bvar 0)) :=
  ⟨_, _, _, _, _, _, inhab0⟩

end Plain

/-! ### A `Sigma`-shaped structure with a dependent second field -/

namespace Dependent

def l1 : VLevel := .succ .zero
def Ac : VExpr := .const `A []
def Bc : VExpr := .const `B []
def S2c : VExpr := .const `S2 []
def mk2c : VExpr := .const `S2.mk []
def Bx : VExpr := .app Bc (.bvar 0)
def BTy : VExpr := .forallE Ac (.sort l1)
def ctorTy2 : VExpr := .forallE Ac (.forallE Bx S2c)
def mk2Spine : VExpr := .app (.app mk2c (.bvar 1)) (.bvar 0)
def motiveTy2 : VExpr := .forallE S2c (.sort (.param 0))
def motiveTy2' : VExpr := .forallE S2c (.sort l1)
def minorTy2 : VExpr := .forallE Ac (.forallE Bx (.app (.bvar 2) mk2Spine))
def recTy2 : VExpr :=
  .forallE motiveTy2 (.forallE minorTy2 (.forallE S2c (.app (.bvar 2) (.bvar 0))))
def ruleRhs2 : VExpr :=
  .lam motiveTy2 (.lam minorTy2 (.lam Ac (.lam Bx (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)))))

def decl2 : VInductDecl where
  uvars := 0
  nparams := 0
  types := [{ name := `S2, uvars := 0, type := .sort l1,
              ctors := [{ name := `S2.mk, uvars := 0, type := ctorTy2 }] }]
  recs := [{ name := mkRecName `S2, uvars := 1, type := recTy2, all := [`S2],
             numParams := 0, numMotives := 1, numMinors := 1, numIndices := 0, k := false,
             rules := [{ ctor := `S2.mk, ctorParams := 0, nfields := 2, rhs := ruleRhs2 }] }]

def env0? : Option VEnv :=
  VEnv.empty.addConst `A ⟨0, .sort l1⟩ |>.bind (·.addConst `B ⟨0, BTy⟩)
    |>.bind fun e => e.addInduct decl2

theorem env0_isSome : env0?.isSome = true := rfl

def env : VEnv := env0?.get env0_isSome

theorem hA : env.constants `A = some ⟨0, .sort l1⟩ := rfl
theorem hB : env.constants `B = some ⟨0, BTy⟩ := rfl
theorem hS2 : env.constants `S2 = some ⟨0, .sort l1⟩ := rfl
theorem hmk2 : env.constants `S2.mk = some ⟨0, ctorTy2⟩ := rfl
theorem hrec2 : env.constants (mkRecName `S2) = some ⟨1, recTy2⟩ := rfl

theorem hclosed2 : ruleRhs2.Closed := by decide

def patKey2 : Pattern := (SimplePattern.iota (mkRecName `S2) (0+1+1+0) `S2.mk (0+2)).toPattern
def rhsPair2 : patKey2.RHS × patKey2.Check :=
  (SimplePattern.iotaRHS (mkRecName `S2) `S2.mk 0 1 1 0 0 2 ruleRhs2 hclosed2, .true)

theorem hpats2 : env.pats patKey2 rhsPair2 := Or.inl ⟨rfl, rfl⟩

/-! The projection expansion terms. -/

def uss : Nat → List VLevel := fun _ => [l1]
def rec2C : VExpr := .const (mkRecName `S2) [l1]
def M20 : VExpr := .lam S2c Ac
def sel20 : VExpr := .lam Ac (.lam Bx (.bvar 1))
def sel21 : VExpr := .lam Ac (.lam Bx (.bvar 0))
def P0' : VExpr := .app (.app rec2C M20) sel20
def M21 : VExpr := .lam S2c (.app Bc (.app P0' (.bvar 0)))
def P1' : VExpr := .app (.app rec2C M21) sel21
def minorTyM20 : VExpr := .forallE Ac (.forallE Bx (.app M20 mk2Spine))
def minorTyM21 : VExpr := .forallE Ac (.forallE Bx (.app M21 mk2Spine))

example : VExpr.projFn `S2 [] uss [] [Ac, Bx] 0 = P0' := by decide
example : VExpr.projFn `S2 [] uss [] [Ac, Bx] 1 = P1' := by decide
example : VExpr.projMotiveBody `S2 [] uss [] [Ac, Bx] 0 = Ac := by decide
example : VExpr.projMotiveBody `S2 [] uss [] [Ac, Bx] 1
    = .app Bc (.app P0' (.bvar 0)) := by decide

/-- The ι template, level-instantiated. -/
def T : VExpr :=
  .lam motiveTy2' (.lam minorTy2 (.lam Ac (.lam Bx (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)))))
example : ruleRhs2.instL [l1] = T := by decide

def bodyT : VExpr := .lam minorTy2 (.lam Ac (.lam Bx (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))
def inner3 : VExpr := .lam Ac (.lam Bx (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)))
def T1 : VExpr := .lam minorTyM20 inner3
def T2 : VExpr := .lam Ac (.lam Bx (.app (.app sel20 (.bvar 1)) (.bvar 0)))
def T3 : VExpr := .lam (.app Bc (.bvar 1)) (.app (.app sel20 (.bvar 2)) (.bvar 0))
def T5 : VExpr := .lam (.app Bc (.bvar 1)) (.bvar 2)

/-! Basic typings, generic in the context. -/

theorem lvl1WF : ∀ l ∈ [l1], VLevel.WF 0 l := fun _ h => by
  cases h with
  | head => trivial
  | tail _ h => cases h

theorem hAt (Γ : List VExpr) : env.IsDefEq 0 Γ Ac Ac (.sort l1) :=
  .constDF hA nofun nofun rfl .nil
theorem hBt (Γ : List VExpr) : env.IsDefEq 0 Γ Bc Bc (.forallE Ac (.sort l1)) :=
  .constDF hB nofun nofun rfl .nil
theorem hS2t (Γ : List VExpr) : env.IsDefEq 0 Γ S2c S2c (.sort l1) :=
  .constDF hS2 nofun nofun rfl .nil
theorem hmk2t (Γ : List VExpr) : env.IsDefEq 0 Γ mk2c mk2c ctorTy2 :=
  .constDF hmk2 nofun nofun rfl .nil
theorem hrec2t (Γ : List VExpr) : env.IsDefEq 0 Γ rec2C rec2C (recTy2.instL [l1]) :=
  .constDF hrec2 lvl1WF lvl1WF rfl (.cons rfl .nil)

/-- `B (bvar 0) : Sort 1` in any context headed by `A`. -/
theorem hBxt (Γ : List VExpr) : env.IsDefEq 0 (Ac::Γ) Bx Bx (.sort l1) :=
  .appDF (hBt _) (.bvar .zero)

/-- The generic constructor spine `mk2 a b : S2` over `Γ, a : A, b : B a`. -/
theorem hmk2spine (Γ : List VExpr) : env.IsDefEq 0 (Bx::Ac::Γ) mk2Spine mk2Spine S2c :=
  .appDF (.appDF (hmk2t _) (.bvar (.succ .zero))) (.bvar .zero)

/-! Field 0 (constant motive `A`). -/

theorem hM20 (Γ : List VExpr) : env.IsDefEq 0 Γ M20 M20 motiveTy2' :=
  .lamDF (hS2t Γ) (hAt (S2c::Γ))

theorem hbody20 (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::Γ) (.app M20 mk2Spine) Ac (.sort l1) :=
  .beta (hAt _) (hmk2spine Γ)

theorem hsel20nat (Γ : List VExpr) :
    env.IsDefEq 0 Γ sel20 sel20 (.forallE Ac (.forallE Bx Ac)) :=
  .lamDF (hAt Γ) (.lamDF (hBxt Γ) (.bvar (.succ .zero)))

theorem hminorEq20 (Γ : List VExpr) :
    env.IsDefEq 0 Γ (.forallE Ac (.forallE Bx Ac)) minorTyM20
      (.sort (.imax l1 (.imax l1 l1))) :=
  .forallEDF (hAt Γ) (.forallEDF (hBxt Γ) (.symm (hbody20 Γ)))

theorem hsel20M (Γ : List VExpr) : env.IsDefEq 0 Γ sel20 sel20 minorTyM20 :=
  .defeqDF (hminorEq20 Γ) (hsel20nat Γ)

theorem hstep20 (Γ : List VExpr) :
    env.IsDefEq 0 Γ (.app rec2C M20) (.app rec2C M20)
      (.forallE minorTyM20 (.forallE S2c (.app M20 (.bvar 0)))) :=
  .appDF (hrec2t Γ) (hM20 Γ)

theorem hbetax20 (Γ : List VExpr) :
    env.IsDefEq 0 (S2c::Γ) (.app M20 (.bvar 0)) Ac (.sort l1) :=
  .beta (hAt _) (.bvar .zero)

theorem hP0ty (Γ : List VExpr) : env.IsDefEq 0 Γ P0' P0' (.forallE S2c Ac) :=
  .defeqDF (.forallEDF (hS2t Γ) (hbetax20 Γ)) (.appDF (hstep20 Γ) (hsel20M Γ))

/-! Field 1: the dependent motive `fun x => B (P₀ x)`. -/

theorem hM21body (Γ : List VExpr) :
    env.IsDefEq 0 (S2c::Γ) (.app Bc (.app P0' (.bvar 0))) (.app Bc (.app P0' (.bvar 0)))
      (.sort l1) :=
  .appDF (hBt _) (.appDF (hP0ty _) (.bvar .zero))

theorem hM21 (Γ : List VExpr) : env.IsDefEq 0 Γ M21 M21 motiveTy2' :=
  .lamDF (hS2t Γ) (hM21body Γ)

/-! The ι step: `P₀ (mk2 a b) ≡ a` over `Γ, a : A, b : B a`. -/

/-- The redex `P₀ (mk2 a b)` is well-typed. -/
theorem hredex (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::Γ) (.app P0' mk2Spine) (.app P0' mk2Spine) Ac :=
  .appDF (hP0ty _) (hmk2spine Γ)

/-- The match of the ι pattern against `P₀ (mk2 a b)`, with the reduct it computes to. -/
theorem hmatch : ∃ m2, patKey2.Matches (.app P0' mk2Spine) [l1] m2 ∧
    rhsPair2.1.apply [l1] m2
      = .app (.app (.app (.app T M20) sel20) (.bvar 1)) (.bvar 0) := by
  refine ⟨_, .app (.var (.var .const)) (.var (.var .const)), ?_⟩
  rfl

/-- ι: the redex rewrites to the template applied to the matched arguments. -/
theorem hiota (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::Γ) (.app P0' mk2Spine)
      (.app (.app (.app (.app T M20) sel20) (.bvar 1)) (.bvar 0)) Ac := by
  obtain ⟨m2, hm, happly⟩ := hmatch
  have h := VEnv.IsDefEq.pat (Γ := Bx::Ac::Γ) hpats2 hm (hredex Γ) (chk := []) trivial nofun
  rwa [happly] at h

/-! β-reduction of the template applied to `[M20, sel20, a, b]`, step by step. -/

/-- The motive variable `C` at index 2, under `Γ, C, a, b`. -/
theorem hbvarC (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::motiveTy2'::Γ) (.bvar 2) (.bvar 2) (.forallE S2c (.sort l1)) :=
  .bvar (.succ (.succ .zero))

/-- The motive variable `C` applied to the generic spine, under `Γ, C, a, b`. -/
theorem hCapp (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::motiveTy2'::Γ) (.app (.bvar 2) mk2Spine) (.app (.bvar 2) mk2Spine)
      (.sort l1) :=
  .appDF (hbvarC Γ) (hmk2spine _)

/-- Well-formedness of the minor premise type under `C : motiveTy2'`. -/
theorem hminorTy2wf (Γ : List VExpr) :
    env.IsDefEq 0 (motiveTy2'::Γ) minorTy2 minorTy2 (.sort (.imax l1 (.imax l1 l1))) :=
  .forallEDF (hAt _) (.forallEDF (hBxt _) (hCapp Γ))

/-- The minor variable `m` at index 2, under `Γ, C, m, a, b`. -/
theorem hbvarM (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::minorTy2::motiveTy2'::Γ) (.bvar 2) (.bvar 2)
      (.forallE Ac (.forallE Bx (.app (.bvar 5) mk2Spine))) :=
  .bvar (.succ (.succ .zero))

/-- The template's inner spine `m a b`, typed under `Γ, C, m, a, b`. -/
theorem hmSpine1 (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::minorTy2::motiveTy2'::Γ) (.app (.bvar 2) (.bvar 1))
      (.app (.bvar 2) (.bvar 1))
      (.forallE (.app Bc (.bvar 1)) (.app (.bvar 4) (.app (.app mk2c (.bvar 2)) (.bvar 0)))) :=
  .appDF (hbvarM Γ) (.bvar (.succ .zero))

theorem hmSpine2 (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::minorTy2::motiveTy2'::Γ) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
      (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) (.app (.bvar 3) mk2Spine) :=
  .appDF (hmSpine1 Γ) (.bvar .zero)

/-- The template body `fun (m : minorTy2) (a : A) (b : B a) => m a b`, typed under
`C : motiveTy2'`. -/
theorem hbodyT (Γ : List VExpr) :
    env.IsDefEq 0 (motiveTy2'::Γ) bodyT bodyT
      (.forallE minorTy2 (.forallE Ac (.forallE Bx (.app (.bvar 3) mk2Spine)))) :=
  .lamDF (hminorTy2wf Γ) (.lamDF (hAt _) (.lamDF (hBxt _) (hmSpine2 Γ)))

/-- β₁: `T M20 ≡ T1`. -/
theorem hbeta1 (Γ : List VExpr) :
    env.IsDefEq 0 Γ (.app T M20) T1
      (.forallE minorTyM20 (.forallE Ac (.forallE Bx (.app M20 mk2Spine)))) :=
  .beta (hbodyT Γ) (hM20 Γ)

/-- c₁: the whole spine, after β₁, at raw type `M20 (mk2 a b)`. -/
theorem hc1 (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::Γ)
      (.app (.app (.app (.app T M20) sel20) (.bvar 1)) (.bvar 0))
      (.app (.app (.app T1 sel20) (.bvar 1)) (.bvar 0))
      (.app M20 mk2Spine) :=
  .appDF (.appDF (.appDF (hbeta1 _) (hsel20M _)) (.bvar (.succ .zero))) (.bvar .zero)

/-- The minor variable `m : minorTyM20` at index 2, under `Γ, m, a, b`. -/
theorem hbvarM' (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::minorTyM20::Γ) (.bvar 2) (.bvar 2)
      (.forallE Ac (.forallE Bx (.app M20 mk2Spine))) :=
  .bvar (.succ (.succ .zero))

/-- The spine `m a b` with `m : minorTyM20`, typed under `Γ, m, a, b`. -/
theorem hmSpine1' (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::minorTyM20::Γ) (.app (.bvar 2) (.bvar 1)) (.app (.bvar 2) (.bvar 1))
      (.forallE (.app Bc (.bvar 1)) (.app M20 (.app (.app mk2c (.bvar 2)) (.bvar 0)))) :=
  .appDF (hbvarM' Γ) (.bvar (.succ .zero))

theorem hmSpine2' (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::minorTyM20::Γ) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
      (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) (.app M20 mk2Spine) :=
  .appDF (hmSpine1' Γ) (.bvar .zero)

/-- `inner3` typed under the minor binder. -/
theorem hinner3 (Γ : List VExpr) :
    env.IsDefEq 0 (minorTyM20::Γ) inner3 inner3
      (.forallE Ac (.forallE Bx (.app M20 mk2Spine))) :=
  .lamDF (hAt _) (.lamDF (hBxt _) (hmSpine2' Γ))

/-- β₂: `T1 sel20 ≡ T2`. -/
theorem hbeta2 (Γ : List VExpr) :
    env.IsDefEq 0 Γ (.app T1 sel20) T2 (.forallE Ac (.forallE Bx (.app M20 mk2Spine))) :=
  .beta (hinner3 Γ) (hsel20M Γ)

theorem hc2 (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::Γ)
      (.app (.app (.app T1 sel20) (.bvar 1)) (.bvar 0))
      (.app (.app T2 (.bvar 1)) (.bvar 0))
      (.app M20 mk2Spine) :=
  .appDF (.appDF (hbeta2 _) (.bvar (.succ .zero))) (.bvar .zero)

/-- The body of `T2`, typed under its `A` binder. -/
theorem hinnerT2 (Γ : List VExpr) :
    env.IsDefEq 0 (Ac::Γ) (.lam Bx (.app (.app sel20 (.bvar 1)) (.bvar 0)))
      (.lam Bx (.app (.app sel20 (.bvar 1)) (.bvar 0)))
      (.forallE Bx Ac) :=
  .lamDF (hBxt _) (.appDF (.appDF (hsel20nat _) (.bvar (.succ .zero))) (.bvar .zero))

/-- β₃: `T2 a ≡ T3`. -/
theorem hbeta3 (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::Γ) (.app T2 (.bvar 1)) T3
      (.forallE (.app Bc (.bvar 1)) Ac) :=
  .beta (hinnerT2 _) (.bvar (.succ .zero))

theorem hc3 (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::Γ)
      (.app (.app T2 (.bvar 1)) (.bvar 0)) (.app T3 (.bvar 0)) Ac :=
  .appDF (hbeta3 Γ) (.bvar .zero)

/-- β₄: `T3 b ≡ sel20 a b`. -/
theorem hbeta4 (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::Γ) (.app T3 (.bvar 0))
      (.app (.app sel20 (.bvar 1)) (.bvar 0)) Ac :=
  .beta (.appDF (.appDF (hsel20nat _) (.bvar (.succ (.succ .zero)))) (.bvar .zero))
    (.bvar .zero)

/-- β₅: `sel20 a ≡ T5`. -/
theorem hbeta5 (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::Γ) (.app sel20 (.bvar 1)) T5
      (.forallE (.app Bc (.bvar 1)) Ac) :=
  .beta (.lamDF (hBxt _) (.bvar (.succ .zero))) (.bvar (.succ .zero))

theorem hc5 (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::Γ)
      (.app (.app sel20 (.bvar 1)) (.bvar 0)) (.app T5 (.bvar 0)) Ac :=
  .appDF (hbeta5 Γ) (.bvar .zero)

/-- β₆: `T5 b ≡ a`. -/
theorem hbeta6 (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::Γ) (.app T5 (.bvar 0)) (.bvar 1) Ac :=
  .beta (.bvar (.succ (.succ .zero))) (.bvar .zero)

/-- The ι+β chain: `P₀ (mk2 a b) ≡ a : A` over `Γ, a : A, b : B a`. -/
theorem hproj0red (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::Γ) (.app P0' mk2Spine) (.bvar 1) Ac :=
  ((((((hiota Γ).trans
    (.defeqDF (hbody20 Γ) (hc1 Γ))).trans
    (.defeqDF (hbody20 Γ) (hc2 Γ))).trans
    (hc3 Γ)).trans
    (hbeta4 Γ)).trans
    (hc5 Γ)).trans
    (hbeta6 Γ)

/-! Assembling the typing of `P₁`. -/

/-- `sel21`'s natural type. -/
theorem hsel21nat (Γ : List VExpr) :
    env.IsDefEq 0 Γ sel21 sel21 (.forallE Ac (.forallE Bx (.app Bc (.bvar 1)))) :=
  .lamDF (hAt Γ) (.lamDF (hBxt Γ) (.bvar .zero))

/-- `M21 (mk2 a b) ≡ B (P₀ (mk2 a b))`. -/
theorem hbody21 (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::Γ) (.app M21 mk2Spine) (.app Bc (.app P0' mk2Spine)) (.sort l1) :=
  .beta (hM21body _) (hmk2spine Γ)

/-- `B a ≡ M21 (mk2 a b)`, via the ι step. -/
theorem hbodyEq21 (Γ : List VExpr) :
    env.IsDefEq 0 (Bx::Ac::Γ) (.app Bc (.bvar 1)) (.app M21 mk2Spine) (.sort l1) :=
  .symm ((hbody21 Γ).trans (.symm (.appDF (hBt _) (.symm (hproj0red Γ)))))

theorem hminorEq21 (Γ : List VExpr) :
    env.IsDefEq 0 Γ (.forallE Ac (.forallE Bx (.app Bc (.bvar 1)))) minorTyM21
      (.sort (.imax l1 (.imax l1 l1))) :=
  .forallEDF (hAt Γ) (.forallEDF (hBxt Γ) (hbodyEq21 Γ))

theorem hsel21M (Γ : List VExpr) : env.IsDefEq 0 Γ sel21 sel21 minorTyM21 :=
  .defeqDF (hminorEq21 Γ) (hsel21nat Γ)

theorem hstep21 (Γ : List VExpr) :
    env.IsDefEq 0 Γ (.app rec2C M21) (.app rec2C M21)
      (.forallE minorTyM21 (.forallE S2c (.app M21 (.bvar 0)))) :=
  .appDF (hrec2t Γ) (hM21 Γ)

theorem hbetax21 (Γ : List VExpr) :
    env.IsDefEq 0 (S2c::Γ) (.app M21 (.bvar 0)) (.app Bc (.app P0' (.bvar 0))) (.sort l1) :=
  .beta (hM21body _) (.bvar .zero)

/-- **The typing premise of `TrProjCtor` for the dependent field:**
`P₁ : ∀ x : S2, B (P₀ x)`. -/
theorem hP1ty (Γ : List VExpr) :
    env.IsDefEq 0 Γ P1' P1' (.forallE S2c (.app Bc (.app P0' (.bvar 0)))) :=
  .defeqDF (.forallEDF (hS2t Γ) (hbetax21 Γ)) (.appDF (hstep21 Γ) (hsel21M Γ))

/-! The inhabitation results. -/

/-- Field `0` of the `Sigma`-shaped structure: the constant motive `A`. -/
theorem inhabDep0 :
    TrProjCtor env 0 [S2c] `S2 0 (.bvar 0) (.app P0' (.bvar 0)) `S2.mk [] uss [] 0 [Ac, Bx] :=
  { pat := ⟨rhsPair2, hpats2⟩
    params_length := rfl
    ctor := ⟨⟨0, ctorTy2⟩, hmk2, by decide, ctorTy2, rfl, rfl⟩
    field_lt := by decide
    minor_arity := ⟨⟨1, recTy2⟩, hrec2, rfl⟩
    major_ty := .bvar .zero
    fn_ty := hP0ty [S2c]
    eq := rfl }

/-- Field `1`, whose motive `fun x => B (P₀ x)` is the dependent one. -/
theorem inhabDep1 :
    TrProjCtor env 0 [S2c] `S2 1 (.bvar 0) (.app P1' (.bvar 0)) `S2.mk [] uss [] 0 [Ac, Bx] :=
  { inhabDep0 with
    field_lt := by decide
    fn_ty := hP1ty [S2c]
    eq := rfl }

theorem trProjDep1 : TrProj env 0 [S2c] `S2 1 (.bvar 0) (.app P1' (.bvar 0)) :=
  ⟨_, _, _, _, _, _, inhabDep1⟩

end Dependent

/-! ### Both witnesses are sorry-free -/

/-- info: 'Lean4Lean.Tests.ProjInhabit.Plain.inhab0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Plain.inhab0

/-- info: 'Lean4Lean.Tests.ProjInhabit.Plain.inhab1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Plain.inhab1

/--
info: 'Lean4Lean.Tests.ProjInhabit.Dependent.inhabDep0' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Dependent.inhabDep0

/--
info: 'Lean4Lean.Tests.ProjInhabit.Dependent.inhabDep1' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Dependent.inhabDep1

/-! ### Axiom profile of projection reduction

`TrEnv.proj_defeq` has no `sorry` of its own: the `sorryAx` below is inherited from unique
typing, Π-injectivity and `VEnv.WF.patsStrong`, and the `PersistentHashMap` axioms come with
the kernel environment lemmas. -/

/--
info: 'Lean4Lean.TrEnv.proj_defeq' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in #print axioms Lean4Lean.TrEnv.proj_defeq

end Lean4Lean.Tests.ProjInhabit
