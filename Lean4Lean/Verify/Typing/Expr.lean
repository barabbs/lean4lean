import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Proj
import Lean4Lean.Verify.NameGenerator
import Lean4Lean.Verify.VLCtx
import Lean4Lean.Verify.Axioms

namespace Lean4Lean
open Lean

def Closed : Expr → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .fvar _, _ | .sort .., _ | .const .., _ | .lit .., _ => True
  | .app f a, k => Closed f k ∧ Closed a k
  | .lam _ d b _, k
  | .forallE _ d b _, k => Closed d k ∧ Closed b (k+1)
  | .letE _ d v b _, k => Closed d k ∧ Closed v k ∧ Closed b (k+1)
  | .proj _ _ e, k | .mdata _ e, k => Closed e k
  | .mvar .., _ => False

nonrec abbrev _root_.Lean.Expr.Closed := @Closed

/-- This is very inefficient, only use for spec purposes -/
def _root_.Lean.Expr.fvarsList : Expr → List FVarId
  | .bvar _ | .sort .. | .const .. | .lit .. | .mvar .. => []
  | .fvar fv => [fv]
  | .app f a => f.fvarsList ++ a.fvarsList
  | .lam _ d b _
  | .forallE _ d b _ => d.fvarsList ++ b.fvarsList
  | .letE _ d v b _ => d.fvarsList ++ v.fvarsList ++ b.fvarsList
  | .proj _ _ e | .mdata _ e => e.fvarsList

variable (fvars : FVarId → Prop) in
def FVarsIn : Expr → Prop
  | .bvar _ => True
  | .fvar fv => fvars fv
  | .sort u => u.hasMVar' = false
  | .const _ us => ∀ u ∈ us, u.hasMVar' = false
  | .lit .. => True
  | .app f a => FVarsIn f ∧ FVarsIn a
  | .lam _ d b _
  | .forallE _ d b _ => FVarsIn d ∧ FVarsIn b
  | .letE _ d v b _ => FVarsIn d ∧ FVarsIn v ∧ FVarsIn b
  | .proj _ _ e | .mdata _ e => FVarsIn e
  | .mvar .. => False

nonrec abbrev _root_.Lean.Expr.FVarsIn := @FVarsIn

def VLocalDecl.WF (env : VEnv) (U : Nat) (Γ : List VExpr) : VLocalDecl → Prop
  | .vlam type => env.IsType U Γ type
  | .vlet type value => env.HasType U Γ value type

def VLCtx.FVWF : VLCtx → Prop
  | [] => True
  | (ofv, _) :: (Δ : VLCtx) =>
    VLCtx.FVWF Δ ∧ (∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ.fvars ∧ deps ⊆ Δ.fvars)

variable (env : VEnv) (U : Nat) in
def VLCtx.WF : VLCtx → Prop
  | [] => True
  | (ofv, d) :: (Δ : VLCtx) =>
    VLCtx.WF Δ ∧ (∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ.fvars ∧ deps ⊆ Δ.fvars) ∧
    VLocalDecl.WF env U Δ.toCtx d

theorem VLCtx.WF.fvwf : ∀ {Δ}, VLCtx.WF env U Δ → Δ.FVWF
  | [], h => h
  | _ :: _, ⟨h1, h2, _⟩ => ⟨h1.fvwf, h2⟩

/-- `TrProjCtor env U Γ S i e e' c` relates the translated structure value `e : S usS params`
to the translation `e'` of its `i`-th projection `.proj S i e`, with the structure's constructor
`c` exposed (`TrProj` hides it; `TrEnv.proj_defeq` needs it to tie the registered ι rule to the
constructor spine `e` reduces to). `VExpr` has no projection node; a projection is the
recursor expansion of Carneiro's thesis (`inv_x`, typesys.tex §"Undecidability"; `π₂`,
Wtypes.tex) applied to `e`:

    e' = P_i e,   P_i = S.rec (uss i) params (λ x : S usS params. F_i[f_j := P_j x]) (λ f. f_i)

(`VExpr.projFn`, `Theory/Proj.lean`), where `F₀ … F_{n-1}` is the constructor's field telescope
instantiated at `params` — read off `c`'s type as `inferProj` does (`instPis`/`piBinders`) —
and the earlier projections `P_j`, `j < i`, are the same expansions (`VExpr.projFns`,
well-founded on `i`). The motive of field `i` is the field's type with the earlier fields
replaced by their projections of the bound major, so that `P_i e : F_i[f_j := P_j e]`
(`VExpr.projTy`) — the kernel's `inferProj` result with `.proj S j e ↦ P_j e`. For field `0`
and for every field whose type does not mention earlier fields this is the constant motive
`λ _. F_i`.

What is pinned and why:
* the ι rule of `S.rec` on `c` (`env.pats`, key `iota S.rec (np+1+1+0) c (np+n)`): the only
  inductive metadata a `VEnv` retains, monotone under `VEnv.LE`; the `1+1+0` split says one
  motive, one minor, no indices — a non-nested, non-indexed single-constructor type;
* `fieldTys := piBinders ((c.type.instL usS).instPis params)`: `inferProj` verbatim, and it
  makes the expansion a *function* of `(S, c, usS, uss, params, i, e)` (`TrProj.uniq`). The
  constructor's type is `CtorHeaded` — its Π-telescope ends in a constant application, as every
  constructor type does — so that instantiating a variable cannot create binders and the
  telescope is stable under `TrProj.instN` (`VExpr.piBinders_inst_of_ctorHeaded`);
* `e : S usS params` and `P_i : ∀ x : S usS params, F_i[f_j := P_j x]`: the typing of the
  projection function. It is inhabited, for every kernel-accepted projection of a
  non-recursive structure, by β at the major, ι (`IsDefEq.pat`) on the generic constructor
  spine `c usS params f₀ … f_{n-1}` for each used `P_j`, and `IsDefEq.instDF` — no
  structure-η (derivation in the module docstring of `Theory/Proj.lean`);
* `uss j` is existential per field: the elimination level of `P_j` is the sort of `F_j`,
  which differs between fields (`Sigma.fst` at `u+1`, `Sigma.snd` at `v+1`); an unused `P_j`
  vanishes from `P_i` under substitution, so its `uss j` is irrelevant.

Scope: single-constructor, non-recursive, non-indexed inductives (Lean `structure`s other
than nested-recursive ones such as `Lean.Language.SnapshotTree`; all of `Init`/`Std`).
Nested structures (extra motives and minors) and indexed single-constructor families are
excluded by the `np+1+1+0` key. Reflexive structures (`structure Refl where next : Nat → Refl`)
have the key too — one motive, one minor, no indices — but their minor premise carries an
inductive-hypothesis binder after the fields, so `fieldSelector` (fields only) is not typed at
it and the typing premise fails: excluded by the typing, not by the key. Both are a
completeness boundary, not a soundness one. The model is slightly more permissive than
`inferProj`'s Prop gate: an *unused* non-Prop earlier field of a `Prop` structure does not
block a projection here (its `P_j` vanishes), while the kernel rejects it; harmless for a
refinement. -/
def TrProjCtor (env : VEnv) (U : Nat) (Γ : List VExpr)
    (S : Name) (i : Nat) (e e' : VExpr) (ctorName : Name) : Prop :=
  ∃ (usS : List VLevel) (uss : Nat → List VLevel) (params : List VExpr) (np : Nat)
    (ci : VConstant) (cty : VExpr) (fieldTys : List VExpr)
    (r : (SimplePattern.iota (mkRecName S) (np+1+1+0) ctorName (np+fieldTys.length)).toPattern.RHS ×
         (SimplePattern.iota (mkRecName S) (np+1+1+0) ctorName (np+fieldTys.length)).toPattern.Check),
    env.pats (SimplePattern.iota (mkRecName S) (np+1+1+0) ctorName (np+fieldTys.length)).toPattern r ∧
    params.length = np ∧
    env.constants ctorName = some ci ∧
    ci.type.CtorHeaded ∧
    (ci.type.instL usS).instPis params = some cty ∧
    fieldTys = cty.piBinders ∧
    i < fieldTys.length ∧
    env.HasType U Γ e ((VExpr.const S usS).mkApps params) ∧
    env.HasType U Γ (VExpr.projFn S usS uss params fieldTys i)
      (.forallE ((VExpr.const S usS).mkApps params)
        (VExpr.projMotiveBody S usS uss params fieldTys i)) ∧
    e' = .app (VExpr.projFn S usS uss params fieldTys i) e

/-- `TrProjCtor` with the constructor hidden. -/
def TrProj (env : VEnv) (U : Nat) (Γ : List VExpr) (S : Name) (i : Nat) (e e' : VExpr) : Prop :=
  ∃ ctorName, TrProjCtor env U Γ S i e e' ctorName

theorem TrProjCtor.toTrProj {env : VEnv} {U : Nat} {Γ : List VExpr} {S : Name} {i : Nat}
    {e e' : VExpr} {ctorName : Name} (H : TrProjCtor env U Γ S i e e' ctorName) :
    TrProj env U Γ S i e e' := ⟨_, H⟩

theorem TrProj.exists_ctorName {env : VEnv} {U : Nat} {Γ : List VExpr} {S : Name} {i : Nat}
    {e e' : VExpr} (H : TrProj env U Γ S i e e') :
    ∃ ctorName, TrProjCtor env U Γ S i e e' ctorName := H

def VEnv.ContainsLits (env : VEnv) : Literal → Prop
  | .natVal _ => env.contains ``Nat
  | .strVal _ => env.contains ``Char.ofNat ∧ env.contains ``String.ofList

variable (env : VEnv) (Us : List Name) in
inductive TrExprS : VLCtx → Expr → VExpr → Prop
  | bvar : Δ.find? (.inl i) = some (e, A) → TrExprS Δ (.bvar i) e
  | fvar : Δ.find? (.inr fv) = some (e, A) → TrExprS Δ (.fvar fv) e
  | sort : VLevel.ofLevel Us u = some u' → TrExprS Δ (.sort u) (.sort u')
  | const :
    env.constants c = some ci →
    us.mapM (VLevel.ofLevel Us) = some us' →
    us.length = ci.uvars →
    TrExprS Δ (.const c us) (.const c us')
  | app :
    env.HasType Us.length Δ.toCtx f' (.forallE A B) →
    env.HasType Us.length Δ.toCtx a' A →
    TrExprS Δ f f' → TrExprS Δ a a' → TrExprS Δ (.app f a) (.app f' a')
  | lam :
    env.IsType Us.length Δ.toCtx ty' →
    TrExprS Δ ty ty' → TrExprS ((none, .vlam ty') :: Δ) body body' →
    TrExprS Δ (.lam name ty body bi) (.lam ty' body')
  | forallE :
    env.IsType Us.length Δ.toCtx ty' →
    env.IsType Us.length (ty' :: Δ.toCtx) body' →
    TrExprS Δ ty ty' → TrExprS ((none, .vlam ty') :: Δ) body body' →
    TrExprS Δ (.forallE name ty body bi) (.forallE ty' body')
  | letE :
    env.HasType Us.length Δ.toCtx val' ty' →
    TrExprS Δ ty ty' → TrExprS Δ val val' →
    TrExprS ((none, .vlet ty' val') :: Δ) body body' →
    TrExprS Δ (.letE name ty val body nd) body'
  | lit : env.ContainsLits l → TrExprS Δ l.toConstructor e → TrExprS Δ (.lit l) e
  | mdata : TrExprS Δ e e' → TrExprS Δ (.mdata d e) e'
  | proj : TrExprS Δ e e' → TrProj env Us.length Δ.toCtx s i e' e'' → TrExprS Δ (.proj s i e) e''

def TrExpr (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) (e' : VExpr) : Prop :=
  ∃ e₂, TrExprS env Us Δ e e₂ ∧ env.IsDefEqU Us.length Δ.toCtx e₂ e'

def VExpr.bool : VExpr := .const ``Bool []
def VExpr.boolTrue : VExpr := .const ``Bool.true []
def VExpr.boolFalse : VExpr := .const ``Bool.false []
def VExpr.boolLit : Bool → VExpr
  | .false => .boolFalse
  | .true => .boolTrue

def VExpr.nat : VExpr := .const ``Nat []
def VExpr.natZero : VExpr := .const ``Nat.zero []
def VExpr.natSucc : VExpr := .const ``Nat.succ []
def VExpr.natLit : Nat → VExpr
  | 0 => .natZero
  | n+1 => .app .natSucc (.natLit n)

def VExpr.char : VExpr := .const ``Char []
def VExpr.string : VExpr := .const ``String []
def VExpr.stringOfList : VExpr := .const ``String.ofList []
def VExpr.listChar : VExpr := .app (.const ``List [.zero]) .char
def VExpr.listCharNil : VExpr := .app (.const ``List.nil [.zero]) .char
def VExpr.listCharCons : VExpr := .app (.const ``List.cons [.zero]) .char
def VExpr.charOfNat : VExpr := .const ``Char.ofNat []
def VExpr.listCharLit : List Char → VExpr
  | [] => .listCharNil
  | a :: as => .app (.app .listCharCons (.app .charOfNat (.natLit a.toNat))) (.listCharLit as)

def VExpr.trLiteral : Literal → VExpr
  | .natVal n => .natLit n
  | .strVal s => .app .stringOfList (.listCharLit s.toList)

def VEnv.ReflectsNatNatNat (env : VEnv) (fc : Name) (f : Nat → Nat → Nat) :=
  env.contains fc →
  ∀ a b, env.IsDefEqU 0 [] (.app (.app (.const fc []) (.natLit a)) (.natLit b)) (.natLit (f a b))

def VEnv.ReflectsNatNatBool (env : VEnv) (fc : Name) (f : Nat → Nat → Bool) :=
  env.contains fc →
  ∀ a b, env.IsDefEqU 0 [] (.app (.app (.const fc []) (.natLit a)) (.natLit b)) (.boolLit (f a b))

structure VEnv.HasPrimitives (env : VEnv) : Prop where
  bool : env.contains ``Bool → env.contains ``Bool.false ∧ env.contains ``Bool.true
  boolFalse : env.constants ``Bool.false = some ci → ci = { uvars := 0, type := .bool }
  boolTrue : env.constants ``Bool.true = some ci → ci = { uvars := 0, type := .bool }
  nat : env.contains ``Nat → env.contains ``Nat.zero ∧ env.contains ``Nat.succ
  natZero : env.constants ``Nat.zero = some ci → ci = { uvars := 0, type := .nat }
  natSucc : env.constants ``Nat.succ = some ci →
    ci = { uvars := 0, type := .forallE .nat .nat }
  natAdd : env.ReflectsNatNatNat ``Nat.add Nat.add
  natSub : env.ReflectsNatNatNat ``Nat.sub Nat.sub
  natMul : env.ReflectsNatNatNat ``Nat.mul Nat.mul
  natPow : env.ReflectsNatNatNat ``Nat.pow Nat.pow
  natGcd : env.ReflectsNatNatNat ``Nat.gcd Nat.gcd
  natMod : env.ReflectsNatNatNat ``Nat.mod Nat.mod
  natDiv : env.ReflectsNatNatNat ``Nat.div Nat.div
  natBEq : env.ReflectsNatNatBool ``Nat.beq Nat.beq
  natBLE : env.ReflectsNatNatBool ``Nat.ble Nat.ble
  natLAnd : env.ReflectsNatNatNat ``Nat.land Nat.land
  natLOr : env.ReflectsNatNatNat ``Nat.lor Nat.lor
  natXor : env.ReflectsNatNatNat ``Nat.xor Nat.xor
  natShiftLeft : env.ReflectsNatNatNat ``Nat.shiftLeft Nat.shiftLeft
  natShiftRight : env.ReflectsNatNatNat ``Nat.shiftRight Nat.shiftRight
  charOfNat : env.constants ``Char.ofNat = some ci →
    ci = { uvars := 0, type := .forallE .nat .char }
  stringOfList : env.constants ``String.ofList = some ci →
    ci = { uvars := 0, type := .forallE .listChar .string } ∧
    env.HasType 0 [] .listCharNil .listChar ∧
    env.HasType 0 [] .listCharCons (.forallE .char <| .forallE .listChar .listChar)
