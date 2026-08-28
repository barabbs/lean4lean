import Lean4Lean.Theory.Typing.Basic
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

/-- Left fold of applications: `f.mkApps [a₀, …, aₙ] = f a₀ … aₙ`. -/
def VExpr.mkApps (f : VExpr) : List VExpr → VExpr := List.foldl .app f

/-- The λ-telescope over field types `Fs` that selects its `i`-th binder:
`fun (f₀ : Fs[0]) … (f_{n-1} : Fs[n-1]) => fᵢ`. In de Bruijn form the `i`-th
field (numbered from the outside) sits at index `Fs.length - 1 - i`. This is the
minor premise of a structure's recursor that reads out field `i`. -/
def VExpr.fieldSelector (Fs : List VExpr) (i : Nat) : VExpr :=
  Fs.foldr .lam (.bvar (Fs.length - 1 - i))

/-- `TrProj env U Γ S i e e'` relates the translated structure value `e` (of type
`structTy = S params`) to the translation `e'` of its `i`-th projection `S.i e`.
`VExpr` has no projection node, so a projection is expressed through the
structure's **recursor**: `e' = S.rec us params motive (fun fields => fieldᵢ) e`.
The recursor name, the parameter count `np`, the constructor, and the field count
are read out of the ι rule registered for `S` in `env.pats` — the only inductive
metadata a `VEnv` retains, and what makes `TrProj` monotone under `VEnv.LE`. A
structure is a single-constructor, non-recursive inductive with no indices, so
its recursor has one motive and one minor premise and no index arguments
(`numMotives = 1`, `numMinors = 1`, `numIndices = 0`), giving the argument list
`params ++ [motive, minor, major]`.

The `motive` is pinned to the **canonical constant motive** `fun _ => fieldTy`,
where `fieldTy` is the projection's own type. Pinning it (rather than leaving it
existential) is what makes `TrProj` a *functional* relation: two derivations
share a motive up to definitional equality as soon as their `structTy`/`fieldTy`
agree, which follows from unique typing — no inductive type-former injectivity is
needed for the motive (this is what `TrProj.uniq` requires). A free motive is
under-determined on a *neutral* major (well-typedness only constrains it on
constructor-shaped inputs, `C (mk params fields) ≡ fieldTys[i]`), so two
recursor spines with motives agreeing on constructors but differing on a variable
would both satisfy a loose `TrProj` yet not be defeq — breaking uniqueness. The
kernel avoids this via **structure-η** (`x ≡ mk (proj x)`), which the model's
`IsDefEq` does not have.

Scope: the constant motive is correct exactly for **non-dependent** structure
fields — where field `i`'s type does not mention earlier fields (all typeclass
projections, and everything but Σ/Subtype-shaped structures). This is precisely
the fragment for which Carneiro's thesis does *not* need structure-η; dependent
fields (the thesis's Σ, `Wtypes.tex:75-93`) require either structure-η in
`IsDefEq` or the recursor's dependent motive `fun x => fieldTyᵢ[proj x]`, both of
which are out of scope here. -/
def TrProj (env : VEnv) (U : Nat) (Γ : List VExpr)
    (S : Name) (i : Nat) (e e' : VExpr) : Prop :=
  ∃ (recName ctorName : Name) (us : List VLevel) (params fieldTys : List VExpr)
    (np : Nat) (structTy fieldTy : VExpr)
    (r : (SimplePattern.iota recName (np+1+1+0) ctorName (np+fieldTys.length)).toPattern.RHS ×
         (SimplePattern.iota recName (np+1+1+0) ctorName (np+fieldTys.length)).toPattern.Check),
    recName = mkRecName S ∧
    env.pats (SimplePattern.iota recName (np+1+1+0) ctorName (np+fieldTys.length)).toPattern r ∧
    params.length = np ∧ i < fieldTys.length ∧
    env.HasType U Γ e structTy ∧
    e' = (VExpr.const recName us).mkApps
           (params ++ [.lam structTy fieldTy.lift, VExpr.fieldSelector fieldTys i, e]) ∧
    env.HasType U Γ e' fieldTy

/-- `TrProjCtor` is `TrProj` with the constructor name `ctorName` **exposed** as a
parameter instead of buried under the leading existential. The two are equivalent
(`TrProjCtor.toTrProj` / `TrProj.exists_ctorName`); exposing `ctorName` is what lets
`TrEnv.proj_defeq` tie the registered ι rule's constructor to the constructor spine
`d` reduces to. -/
def TrProjCtor (env : VEnv) (U : Nat) (Γ : List VExpr)
    (S : Name) (i : Nat) (e e' : VExpr) (ctorName : Name) : Prop :=
  ∃ (recName : Name) (us : List VLevel) (params fieldTys : List VExpr)
    (np : Nat) (structTy fieldTy : VExpr)
    (r : (SimplePattern.iota recName (np+1+1+0) ctorName (np+fieldTys.length)).toPattern.RHS ×
         (SimplePattern.iota recName (np+1+1+0) ctorName (np+fieldTys.length)).toPattern.Check),
    recName = mkRecName S ∧
    env.pats (SimplePattern.iota recName (np+1+1+0) ctorName (np+fieldTys.length)).toPattern r ∧
    params.length = np ∧ i < fieldTys.length ∧
    env.HasType U Γ e structTy ∧
    e' = (VExpr.const recName us).mkApps
           (params ++ [.lam structTy fieldTy.lift, VExpr.fieldSelector fieldTys i, e]) ∧
    env.HasType U Γ e' fieldTy

theorem TrProjCtor.toTrProj {env : VEnv} {U : Nat} {Γ : List VExpr} {S : Name} {i : Nat}
    {e e' : VExpr} {ctorName : Name} (H : TrProjCtor env U Γ S i e e' ctorName) :
    TrProj env U Γ S i e e' :=
  let ⟨recName, us, params, fieldTys, np, structTy, fieldTy, r, h⟩ := H
  ⟨recName, ctorName, us, params, fieldTys, np, structTy, fieldTy, r, h⟩

theorem TrProj.exists_ctorName {env : VEnv} {U : Nat} {Γ : List VExpr} {S : Name} {i : Nat}
    {e e' : VExpr} (H : TrProj env U Γ S i e e') :
    ∃ ctorName, TrProjCtor env U Γ S i e e' ctorName :=
  let ⟨recName, ctorName, us, params, fieldTys, np, structTy, fieldTy, r, h⟩ := H
  ⟨ctorName, recName, us, params, fieldTys, np, structTy, fieldTy, r, h⟩

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
