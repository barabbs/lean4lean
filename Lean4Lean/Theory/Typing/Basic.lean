import Lean4Lean.Theory.VEnv

namespace Lean4Lean
open Lean4Lean

inductive Lookup : List VExpr → Nat → VExpr → Prop where
  | zero : Lookup (ty::Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (A::Γ) (n+1) ty.lift

namespace VEnv

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:30 => IsDefEq Γ e e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => IsDefEq Γ e1 e2 A
variable (env : VEnv) (uvars : Nat)

inductive IsDefEq : List VExpr → VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sortDF :
    l.WF uvars → l'.WF uvars → l ≈ l' →
    Γ ⊢ .sort l ≡ .sort l' : .sort (.succ l)
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    (∀ l ∈ ls', l.WF uvars) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ .const c ls ≡ .const c ls' : ci.type.instL ls
  | appDF :
    Γ ⊢ f ≡ f' : .forallE A B →
    Γ ⊢ a ≡ a' : A →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF :
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF :
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta :
    A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta :
    Γ ⊢ e : .forallE A B →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ h' : p
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls : df.type.instL ls
  | pat {p : Pattern} {r : p.RHS × p.Check} {m1 m2 chk} :
    env.pats p r → p.Matches e m1 m2 → Γ ⊢ e : A →
    r.2.Realizes m1 m2 chk →
    (∀ t ∈ chk, Γ ⊢ t.1 ≡ t.2.1 : t.2.2) →
    Γ ⊢ e ≡ r.1.apply m1 m2 : A

end

def HasType (env : VEnv) (U : Nat) (Γ : List VExpr) (e A : VExpr) : Prop :=
  IsDefEq env U Γ e e A

def IsType (env : VEnv) (U : Nat) (Γ : List VExpr) (A : VExpr) : Prop :=
  ∃ u, env.HasType U Γ A (.sort u)

def IsDefEqU (env : VEnv) (U : Nat) (Γ : List VExpr) (e₁ e₂ : VExpr) :=
  ∃ A, env.IsDefEq U Γ e₁ e₂ A

end VEnv

def VExpr.WF (env : VEnv) (U : Nat) (Γ : List VExpr) (e : VExpr) := env.IsDefEqU U Γ e e

def VConstant.WF (env : VEnv) (ci : VConstant) : Prop := env.IsType ci.uvars [] ci.type

def VDefEq.WF (env : VEnv) (df : VDefEq) : Prop :=
  env.HasType df.uvars [] df.lhs df.type ∧ env.HasType df.uvars [] df.rhs df.type

/-- The typing of a reduction rule `(p, r)`: the `VDefEq.WF` of a schematic rule (thesis
§2.6.4, `Γ, C:κ, e::ε, b::β ⊢ rec_P C e p[b] (c b) ≡ e_c b v` read as the typing of its two
sides). A *generic* instance of the redex — at the identity level instantiation
`VLevel.params U`, with the holes the reduct uses being exactly the variables of a context
`Γ` (`Pattern.RHS.Generic`) and the remaining holes arbitrary terms over `Γ` — and the
corresponding reduct are typed at a common type `B` in `Γ`. The side conditions `r.2` are not
assumed: a rule must be typed without them. -/
def VEnv.PatTyped (env : VEnv) (p : Pattern) (r : p.RHS × p.Check) : Prop :=
  ∃ U Γ e m2 B, p.Matches e (VLevel.params U) m2 ∧ r.1.Generic m2 Γ.length ∧
    env.HasType U Γ e B ∧ env.HasType U Γ (r.1.apply (VLevel.params U) m2) B

/-- Well-formedness of a reduction rule `(p, r)`: it is typed (`VEnv.PatTyped`), and it
computes — its reduct's head shape is a closed λ-template applied to arguments
(`Pattern.RHS.TemplateHeaded`, which pins the head, not the arguments), the head shape of
every ι reduct (`SimplePattern.iotaRHS`: the kernel's
`λ params motives minors fields, minor fields v` of `inductiveReduceRec`, applied to the
retained arguments; thesis `e_c b v` under its binders). The shape is what makes a `pats`
entry a *reduction* rule as opposed to a definitional axiom (`VEnv.defeqs`, whose sides are
arbitrary closed terms): a rule rewrites its redex to a β-redex over the matched arguments,
so the head of a reduct is fixed by the rule — no instance of it is a sort or a Π-type — and a
reduct is never a bare hole. This is the checked, monotone (`PatWF.mono`) admissibility
condition under which a rule may be registered (`Ordered.pat`, projected back out by
`Ordered.patWF`).

What it does **not** give: type preservation of the rule's other well-typed instances
(subject reduction). Under `Ordered`, whose `defeq` step admits arbitrary well-typed
definitional axioms, that is false for ι rules (an axiom `List Nat ≡ List Bool` makes
`List.rec Nat m n c (List.cons Bool true tl)` well-typed and its reduct ill-typed), so it is
not part of `Ordered`; it is the strong-system property `VEnv.PatsStrong`, which holds for
well-formed environments (`VEnv.WF.patsStrong`). Named `VEnv.PatWF` because
`Lean4Lean.Pattern.WF` is taken (`Experimental/SExpr.lean`). -/
def VEnv.PatWF (env : VEnv) (p : Pattern) (r : p.RHS × p.Check) : Prop :=
  env.PatTyped p r ∧ r.1.TemplateHeaded
