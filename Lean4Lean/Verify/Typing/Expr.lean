import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Proj
import Lean4Lean.Theory.Typing.Env
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
constructor spine `e` reduces to). `VExpr` has no projection node; a projection is a recursor
expansion in the style of Carneiro's thesis's `inv_x` (typesys.tex §"Undecidability of
definitional equality") applied to `e`:

    e' = P_i e,   P_i = S.rec (uss i) params (λ x : S usS params. F_i[f_j := P_j x]) (λ f. f_i)

(`VExpr.projFn`, `Theory/Proj.lean`), where `F₀ … F_{n-1}` is the constructor's field telescope
instantiated at `params` — read off `c`'s type as `inferProj` does (`instPis`/`piBinders`) —
and the earlier projections `P_j`, `j < i`, are the same expansions (`VExpr.projFns`,
well-founded on `i`). The motive of field `i` is the field's type with the earlier fields
replaced by their projections of the bound major, so that `P_i e : F_i[f_j := P_j e]`
(`VExpr.projTy`) — the kernel's `inferProj` result with `.proj S j e ↦ P_j e`, and the
dependent typing shape of the thesis's *primitive* projections `π₂ p : β[π₁ p/x]`
(Wtypes.tex). For field `0` and for every field whose type does not mention earlier fields
this is the constant motive `λ _. F_i`.

What is pinned and why:
* the ι rule of `S.rec` on `c` (`env.pats`, key `iota S.rec (np+1+1+0) c (np+n)`): the only
  inductive metadata a `VEnv` retains, monotone under `VEnv.LE`; the `1+1+0` split says one
  motive, one minor, no indices — a non-nested, non-indexed single-constructor type;
* `fieldTys := piBinders ((c.type.instL usS).instPis params)`: `inferProj` verbatim, and it
  makes the expansion a *function* of `(S, c, usS, uss, params, i, e)` (`TrProj.uniq`). The
  constructor's type is `CtorHeaded` — its Π-telescope ends in a constant application, as every
  constructor type does — so that instantiating a variable cannot create binders and the
  telescope is stable under `TrProj.instN` (`VExpr.piBinders_inst_of_ctorHeaded`);
* `S.rec`'s binder `np+1` — its minor premise, by the key — has exactly `n` Π-binders
  (`VExpr.binderArity?`): the fields, and no inductive-hypothesis binder. The constructor is
  non-recursive, so the registered reduct applies the minor to the fields alone
  (`VInductDecl.WF.rule_shape`'s count), which is what `TrEnv.proj_defeq` β-reduces through
  `fieldSelector`;
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
inductive-hypothesis binder after the fields: excluded by the minor's arity pin (and, were
it dropped, by the typing premise — `fieldSelector` has only the fields as binders), not by
the key. Both are a completeness boundary, not a soundness one. The model is slightly more permissive than
`inferProj`'s Prop gate: an *unused* non-Prop earlier field of a `Prop` structure does not
block a projection here (its `P_j` vanishes), while the kernel rejects it; harmless for a
refinement. -/
def TrProjCtor (env : VEnv) (U : Nat) (Γ : List VExpr)
    (S : Name) (i : Nat) (e e' : VExpr) (ctorName : Name) : Prop :=
  ∃ (usS : List VLevel) (uss : Nat → List VLevel) (params : List VExpr) (np : Nat)
    (ci rci : VConstant) (cty : VExpr) (fieldTys : List VExpr)
    (r : (SimplePattern.iota (mkRecName S) (np+1+1+0) ctorName (np+fieldTys.length)).toPattern.RHS ×
         (SimplePattern.iota (mkRecName S) (np+1+1+0) ctorName (np+fieldTys.length)).toPattern.Check),
    env.pats (SimplePattern.iota (mkRecName S) (np+1+1+0) ctorName (np+fieldTys.length)).toPattern r ∧
    params.length = np ∧
    env.constants ctorName = some ci ∧
    ci.type.CtorHeaded ∧
    (ci.type.instL usS).instPis params = some cty ∧
    fieldTys = cty.piBinders ∧
    i < fieldTys.length ∧
    env.constants (mkRecName S) = some rci ∧
    rci.type.binderArity? (np+1) = some fieldTys.length ∧
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

@[simp] theorem VExpr.liftN_nat : VExpr.nat.liftN n k = .nat := rfl
@[simp] theorem VExpr.lift_nat : VExpr.nat.lift = .nat := rfl
@[simp] theorem VExpr.inst_nat : VExpr.nat.inst e k = .nat := rfl
@[simp] theorem VExpr.liftN_natZero : VExpr.natZero.liftN n k = .natZero := rfl
@[simp] theorem VExpr.liftN_natSucc : VExpr.natSucc.liftN n k = .natSucc := rfl
@[simp] theorem VExpr.inst_natZero : VExpr.natZero.inst e k = .natZero := rfl
@[simp] theorem VExpr.inst_natSucc : VExpr.natSucc.inst e k = .natSucc := rfl
@[simp] theorem VExpr.inst_natLit : (VExpr.natLit n).inst e k = .natLit n := by
  induction n <;> simp [VExpr.natLit, VExpr.inst, *]
@[simp] theorem VExpr.liftN_natLit : (VExpr.natLit m).liftN n k = .natLit m := by
  induction m <;> simp [VExpr.natLit, VExpr.liftN, VExpr.natSucc, VExpr.natZero, *]
@[simp] theorem VExpr.insts_nat : VExpr.nat.insts g = .nat := by simp [VExpr.nat]
@[simp] theorem VExpr.insts_natLit : (VExpr.natLit m).insts g = .natLit m := by
  induction m <;> simp [VExpr.natLit, VExpr.natSucc, VExpr.natZero, *]
@[simp] theorem VExpr.subst_nat : VExpr.nat.subst σ = .nat := rfl
@[simp] theorem VExpr.subst_natZero : VExpr.natZero.subst σ = .natZero := rfl
@[simp] theorem VExpr.subst_natSucc : VExpr.natSucc.subst σ = .natSucc := rfl
@[simp] theorem VExpr.subst_natLit : (VExpr.natLit m).subst σ = .natLit m := by
  induction m <;> simp [VExpr.natLit, VExpr.natSucc, VExpr.natZero, *]

@[simp] theorem VExpr.inst_bool : VExpr.bool.inst e k = .bool := rfl
@[simp] theorem VExpr.inst_boolFalse : VExpr.boolFalse.inst e k = .boolFalse := rfl
@[simp] theorem VExpr.inst_boolTrue : VExpr.boolTrue.inst e k = .boolTrue := rfl
@[simp] theorem VExpr.inst_boolLit : (VExpr.boolLit b).inst e k = .boolLit b := by
  cases b <;> rfl
@[simp] theorem VExpr.insts_bool : VExpr.bool.insts g = .bool := by simp [VExpr.bool]
@[simp] theorem VExpr.insts_boolLit : (VExpr.boolLit b).insts g = .boolLit b := by
  cases b <;> simp [VExpr.boolLit, VExpr.boolTrue, VExpr.boolFalse]
@[simp] theorem VExpr.subst_bool : VExpr.bool.subst σ = .bool := rfl
@[simp] theorem VExpr.subst_boolLit : (VExpr.boolLit b).subst σ = .boolLit b := by
  cases b <;> rfl

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

/-- `Bool → Bool → Bool` and `Nat → Nat → Nat`, the two halves of `Nat.bitwise`'s type. -/
def VExpr.boolOp2 : VExpr := .forallE .bool (.forallE .bool .bool)
def VExpr.natOp2 : VExpr := .forallE .nat (.forallE .nat .nat)

/-! ### Reflection

A term *reflects* a function when applying it to literals computes the literal answer. The
primed forms speak about an arbitrary term, so that they can be used both for a primitive
constant and for a partial application of one (`Nat.bitwise f`); the unprimed forms are the
primed ones at `.const fc []`, guarded by the constant's presence. -/

/-- The typing is part of reflection because a `Nat → Nat` primitive is consumed as an
*operator*: `Nat.sub`'s successor equation applies `Nat.pred` to the recursive call, and
congruence under an application needs the codomain to be known non-dependent. The evaluation
clause alone cannot supply that -- inverting an application leaves the codomain arbitrary.

It is quantified over `U` and `Γ` because the operator is used at whatever binder depth the
probes have reached, in a level context that is only propositionally empty. For the constant
this costs nothing: its recorded type is closed, so the `const` rule gives it at every `U`. -/
def VEnv.ReflectsNatNat' (env : VEnv) (e : VExpr) (f : Nat → Nat) :=
  env.HasType 0 [] e (.forallE .nat .nat) ∧
  ∀ a, env.IsDefEqU 0 [] (.app e (.natLit a)) (.natLit (f a))

/-- The typing clause is here for the same reason as in `ReflectsNatNat'`: `Nat.mul`'s successor
equation applies `Nat.add` to the recursive call, and `Nat.pow`'s applies `Nat.mul`. -/
def VEnv.ReflectsNatNatNat' (env : VEnv) (e : VExpr) (f : Nat → Nat → Nat) :=
  env.HasType 0 [] e (.forallE .nat (.forallE .nat .nat)) ∧
  ∀ a b, env.IsDefEqU 0 [] (.app (.app e (.natLit a)) (.natLit b)) (.natLit (f a b))

def VEnv.ReflectsNatNatBool' (env : VEnv) (e : VExpr) (f : Nat → Nat → Bool) :=
  env.HasType 0 [] e (.forallE .nat (.forallE .nat .bool)) ∧
  ∀ a b, env.IsDefEqU 0 [] (.app (.app e (.natLit a)) (.natLit b)) (.boolLit (f a b))

/-- The typing clause is here for the same reason as in the others, and for one more: an operator
that merely *evaluates* correctly at boolean literals need not be a `boolOp2` -- an `f` of type
`(x : Bool) → (if x then Bool else Bool)` satisfies the evaluation clause -- while `Nat.bitwise f`
is well typed only if it is one. Every producer has it: `bitwiseOperand` reads it off
`Nat.bitwise`'s recorded type through the application. -/
def VEnv.ReflectsBoolBoolBool' (env : VEnv) (e : VExpr) (f : Bool → Bool → Bool) :=
  env.HasType 0 [] e .boolOp2 ∧
  ∀ a b, env.IsDefEqU 0 [] (.app (.app e (.boolLit a)) (.boolLit b)) (.boolLit (f a b))

def VEnv.ReflectsNatNat (env : VEnv) (fc : Name) (f : Nat → Nat) :=
  env.contains fc → env.ReflectsNatNat' (.const fc []) f

def VEnv.ReflectsNatNatNat (env : VEnv) (fc : Name) (f : Nat → Nat → Nat) :=
  env.contains fc → env.ReflectsNatNatNat' (.const fc []) f

def VEnv.ReflectsNatNatBool (env : VEnv) (fc : Name) (f : Nat → Nat → Bool) :=
  env.contains fc → env.ReflectsNatNatBool' (.const fc []) f

/-- `Nat.bitwise` reflects `Nat.bitwise` for *any* operator that reflects a `Bool` operation.

The quantification over `env'` is load-bearing rather than decorative. The hypothesis on `f` is
an `IsDefEqU`, which is monotone, so in hypothesis position it makes the statement anti-monotone;
without the quantifier the fact could not be carried from the environment where `Nat.bitwise` is
checked to the one where `Nat.land` supplies its operator. Quantifying here keeps the recurrence
argument inside the proof of this field instead of putting it in the invariant. -/
def VEnv.ReflectsNatBitwise (env : VEnv) (fc : Name) :=
  env.contains fc →
  -- the recorded type, in the `stringOfList` style rather than as a `HasType`: the bitwise
  -- operations need `Bool`'s presence, and only this type mentions it
  (∀ ci, env.constants fc = some ci → ci = { uvars := 0, type := .forallE .boolOp2 .natOp2 }) ∧
  ∀ env', env ≤ env' → env'.WF →
  ∀ f g, env'.ReflectsBoolBoolBool' f g →
    env'.ReflectsNatNatNat' (.app (.const fc []) f) (Nat.bitwise g)

/-! ### The primitive invariant

`HasPrimitives` is a list of specifications rather than a record of fields. Each spec looks up
exactly one name -- the guard of a `Reflects*`, or the constant an equation is about -- and
everything else it says is monotone in the environment. That makes environment extension a
single theorem (`HasPrimitives.addConstDefEq`): every spec whose name is not the one being added
transfers by monotonicity, and the one that matches is the caller's obligation.

The case analysis in the monotonicity lemmas therefore ranges over the seven *shapes* below,
not over the twenty-odd primitives. -/

inductive PrimSpec where
  /-- The name's presence forces `ns` to be present. -/
  | containsImplies (ns : List Name)
  /-- The name is declared with exactly this type, and no universe parameters. -/
  | typeEq (type : VExpr)
  | reflectsNatNat (f : Nat → Nat)
  | reflectsNatNatNat (f : Nat → Nat → Nat)
  | reflectsNatNatBool (f : Nat → Nat → Bool)
  | reflectsBitwise
  | stringOfList

/-- `n` is the one name the spec looks up; everything it says about any other name is
monotone in the environment. -/
def PrimSpec.Holds (env : VEnv) (n : Name) : PrimSpec → Prop
  | .containsImplies ns => env.contains n → ∀ m ∈ ns, env.contains m
  | .typeEq type => ∀ ci, env.constants n = some ci → ci = { uvars := 0, type }
  | .reflectsNatNat f => env.ReflectsNatNat n f
  | .reflectsNatNatNat f => env.ReflectsNatNatNat n f
  | .reflectsNatNatBool f => env.ReflectsNatNatBool n f
  | .reflectsBitwise => env.ReflectsNatBitwise n
  | .stringOfList => ∀ ci, env.constants n = some ci →
    ci = { uvars := 0, type := .forallE .listChar .string } ∧
    env.HasType 0 [] .listCharNil .listChar ∧
    env.HasType 0 [] .listCharCons (.forallE .char <| .forallE .listChar .listChar)

/-- Keyed by name, in the same order as `Environment.primitives`, so that
`primSpecs.map (·.1)` evaluates to that list. -/
def primSpecs : List (Name × PrimSpec) :=
  [(``Bool, .containsImplies [``Bool.false, ``Bool.true]),
   (``Bool.false, .typeEq .bool),
   (``Bool.true, .typeEq .bool),
   (``Nat, .containsImplies [``Nat.zero, ``Nat.succ]),
   (``Nat.zero, .typeEq .nat),
   (``Nat.succ, .typeEq (.forallE .nat .nat)),
   (``Nat.add, .reflectsNatNatNat Nat.add),
   (``Nat.pred, .reflectsNatNat Nat.pred),
   (``Nat.sub, .reflectsNatNatNat Nat.sub),
   (``Nat.mul, .reflectsNatNatNat Nat.mul),
   (``Nat.pow, .reflectsNatNatNat Nat.pow),
   (``Nat.gcd, .reflectsNatNatNat Nat.gcd),
   (``Nat.mod, .reflectsNatNatNat Nat.mod),
   (``Nat.div, .reflectsNatNatNat Nat.div),
   (``Nat.beq, .reflectsNatNatBool Nat.beq),
   (``Nat.ble, .reflectsNatNatBool Nat.ble),
   (``Nat.bitwise, .reflectsBitwise),
   (``Nat.land, .reflectsNatNatNat Nat.land),
   (``Nat.lor, .reflectsNatNatNat Nat.lor),
   (``Nat.xor, .reflectsNatNatNat Nat.xor),
   (``Nat.shiftLeft, .reflectsNatNatNat Nat.shiftLeft),
   (``Nat.shiftRight, .reflectsNatNatNat Nat.shiftRight),
   (``String.ofList, .stringOfList),
   (``Char.ofNat, .typeEq (.forallE .nat .char))]

def VEnv.HasPrimitives (env : VEnv) : Prop := ∀ p ∈ primSpecs, p.2.Holds env p.1

/-! #### Accessors, so that call sites keep naming the primitive rather than the spec. -/

section
variable {env : VEnv}

theorem VEnv.HasPrimitives.bool (H : env.HasPrimitives) (h : env.contains ``Bool) :
    env.contains ``Bool.false ∧ env.contains ``Bool.true :=
  let h := H (``Bool, .containsImplies [``Bool.false, ``Bool.true]) (by simp [primSpecs]) h
  ⟨h _ (by simp), h _ (by simp)⟩

theorem VEnv.HasPrimitives.nat (H : env.HasPrimitives) (h : env.contains ``Nat) :
    env.contains ``Nat.zero ∧ env.contains ``Nat.succ :=
  let h := H (``Nat, .containsImplies [``Nat.zero, ``Nat.succ]) (by simp [primSpecs]) h
  ⟨h _ (by simp), h _ (by simp)⟩

theorem VEnv.HasPrimitives.boolFalse (H : env.HasPrimitives)
    (h : env.constants ``Bool.false = some ci) : ci = { uvars := 0, type := .bool } :=
  H (``Bool.false, .typeEq _) (by simp [primSpecs]) _ h

theorem VEnv.HasPrimitives.boolTrue (H : env.HasPrimitives)
    (h : env.constants ``Bool.true = some ci) : ci = { uvars := 0, type := .bool } :=
  H (``Bool.true, .typeEq _) (by simp [primSpecs]) _ h

theorem VEnv.HasPrimitives.natZero (H : env.HasPrimitives)
    (h : env.constants ``Nat.zero = some ci) : ci = { uvars := 0, type := .nat } :=
  H (``Nat.zero, .typeEq _) (by simp [primSpecs]) _ h

theorem VEnv.HasPrimitives.natSucc (H : env.HasPrimitives)
    (h : env.constants ``Nat.succ = some ci) :
    ci = { uvars := 0, type := .forallE .nat .nat } :=
  H (``Nat.succ, .typeEq _) (by simp [primSpecs]) _ h

theorem VEnv.HasPrimitives.charOfNat (H : env.HasPrimitives)
    (h : env.constants ``Char.ofNat = some ci) :
    ci = { uvars := 0, type := .forallE .nat .char } :=
  H (``Char.ofNat, .typeEq _) (by simp [primSpecs]) _ h

theorem VEnv.HasPrimitives.stringOfList (H : env.HasPrimitives)
    (h : env.constants ``String.ofList = some ci) :
    ci = { uvars := 0, type := .forallE .listChar .string } ∧
    env.HasType 0 [] .listCharNil .listChar ∧
    env.HasType 0 [] .listCharCons (.forallE .char <| .forallE .listChar .listChar) :=
  H (``String.ofList, .stringOfList) (by simp [primSpecs]) _ h

theorem VEnv.HasPrimitives.natPred (H : env.HasPrimitives) :
    env.ReflectsNatNat ``Nat.pred Nat.pred :=
  H (``Nat.pred, .reflectsNatNat _) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natAdd (H : env.HasPrimitives) :
    env.ReflectsNatNatNat ``Nat.add Nat.add :=
  H (``Nat.add, .reflectsNatNatNat _) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natSub (H : env.HasPrimitives) :
    env.ReflectsNatNatNat ``Nat.sub Nat.sub :=
  H (``Nat.sub, .reflectsNatNatNat _) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natMul (H : env.HasPrimitives) :
    env.ReflectsNatNatNat ``Nat.mul Nat.mul :=
  H (``Nat.mul, .reflectsNatNatNat _) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natPow (H : env.HasPrimitives) :
    env.ReflectsNatNatNat ``Nat.pow Nat.pow :=
  H (``Nat.pow, .reflectsNatNatNat _) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natGcd (H : env.HasPrimitives) :
    env.ReflectsNatNatNat ``Nat.gcd Nat.gcd :=
  H (``Nat.gcd, .reflectsNatNatNat _) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natMod (H : env.HasPrimitives) :
    env.ReflectsNatNatNat ``Nat.mod Nat.mod :=
  H (``Nat.mod, .reflectsNatNatNat _) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natDiv (H : env.HasPrimitives) :
    env.ReflectsNatNatNat ``Nat.div Nat.div :=
  H (``Nat.div, .reflectsNatNatNat _) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natBEq (H : env.HasPrimitives) :
    env.ReflectsNatNatBool ``Nat.beq Nat.beq :=
  H (``Nat.beq, .reflectsNatNatBool _) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natBLE (H : env.HasPrimitives) :
    env.ReflectsNatNatBool ``Nat.ble Nat.ble :=
  H (``Nat.ble, .reflectsNatNatBool _) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natBitwise (H : env.HasPrimitives) :
    env.ReflectsNatBitwise ``Nat.bitwise :=
  H (``Nat.bitwise, .reflectsBitwise) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natLAnd (H : env.HasPrimitives) :
    env.ReflectsNatNatNat ``Nat.land Nat.land :=
  H (``Nat.land, .reflectsNatNatNat _) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natLOr (H : env.HasPrimitives) :
    env.ReflectsNatNatNat ``Nat.lor Nat.lor :=
  H (``Nat.lor, .reflectsNatNatNat _) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natXor (H : env.HasPrimitives) :
    env.ReflectsNatNatNat ``Nat.xor Nat.xor :=
  H (``Nat.xor, .reflectsNatNatNat _) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natShiftLeft (H : env.HasPrimitives) :
    env.ReflectsNatNatNat ``Nat.shiftLeft Nat.shiftLeft :=
  H (``Nat.shiftLeft, .reflectsNatNatNat _) (by simp [primSpecs])
theorem VEnv.HasPrimitives.natShiftRight (H : env.HasPrimitives) :
    env.ReflectsNatNatNat ``Nat.shiftRight Nat.shiftRight :=
  H (``Nat.shiftRight, .reflectsNatNatNat _) (by simp [primSpecs])

end
