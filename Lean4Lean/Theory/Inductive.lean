import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Basic

namespace Lean4Lean

/-!
# Inductive declarations

The shapes of recursor types, constructor types and ι-rule reducts (`VExpr.RecShape`,
`VExpr.CtorShape`, `VExpr.RuleShape`, with `VExpr.MotiveShape`/`VExpr.MinorFor` for the
motive and minor premises), the staged environment extension `VEnv.addInduct` (type
formers, constructors, recursors, ι rules), and the declaration well-formedness predicate
`VInductDecl.WF` it is checked against.
-/

/-- `Nat.decidableExistsLT`, restated under `Decidable` so that instance search finds
it for bounded existentials `∃ m < n, p m`. -/
instance decidableExistsLT' {n : Nat} {p : Nat → Prop} [DecidablePred p] :
    Decidable (∃ m, m < n ∧ p m) := Nat.decidableExistsLT n

/-- Thesis §2.6.3, the motive `C : ∀ a::α. P a → U`: a Π-telescope ending in a sort whose
last binder is headed by a constant (`VExpr.motiveFormer?`, that head). *Which* constant is
not pinned here — a bare `VEnv` has no notion of type former — and `RecShape` ties only the
eliminated motive's head to the major premise's; the heads of the other motives of a
mutual/nested recursor are unconstrained. -/
def VExpr.MotiveShape (A : VExpr) : Prop :=
  (∃ u, A.piBody = .sort u) ∧ A.motiveFormer?.isSome = true

/-- Thesis §2.6.3, the head `C` of the minor premise `ε_c = ∀ b::β. ∀ v::δ. C p[b] (c b)`:
the Π-body of minor `i` (counted from the outermost minor binder) is headed by one of the
`nm` motives. Under the minor's own `piArity` binders, the motive binders — which precede
minor `i` by `i` minors — are `bvar (piArity + i + k)` for `k < nm` (motive `nm - 1 - k`). -/
def VExpr.MinorHeaded (A : VExpr) (i nm : Nat) : Prop :=
  ∃ k < nm, A.piBody.getAppFn = .bvar (A.piArity + i + k)

/-- Thesis §2.6.3, the minor premise `ε_c = ∀ b::β. ∀ v::δ. C p[b] (c b)` of constructor
`c`: a Π-telescope ending in an application of a bound variable (the motive, which
`RecShape` pins on the same binder) whose last argument is headed by `c`. -/
def VExpr.MinorFor (A : VExpr) (c : Name) : Prop :=
  A.RecHeaded ∧ ∃ x, A.piBody.getAppArgs.getLast? = some x ∧ x.headConst? = some c

/-- Thesis §2.6.3: the recursor telescope is `∀ params motives minors indices major,
motive_j indices major`, with motive `j` counted from the outermost motive binder. Motive
binders have the shape `MotiveShape`, minor binders end in an application of one of the
motives (`MinorHeaded`), the major premise is a constant application ending in the index
variables (`IndApp`), and `motive_j`'s last binder has the major premise's head constant.
Parameter and index binders are unconstrained. -/
def VExpr.RecShape (ty : VExpr) (np nm nmin nind : Nat) : Prop :=
  ty.piArity = np + nm + nmin + nind + 1 ∧
  (∀ i < nm, ∃ A, ty.piBinders[np + i]? = some A ∧ A.MotiveShape) ∧
  (∀ i < nmin, ∃ A, ty.piBinders[np + nm + i]? = some A ∧ A.MinorHeaded i nm) ∧
  ∃ j < nm, ∃ M, ty.piBinders[np + nm + nmin + nind]? = some M ∧ M.IndApp nind ∧
    (∃ A, ty.piBinders[np + j]? = some A ∧ A.motiveFormer? = M.headConst?) ∧
    ty.piBody = (VExpr.bvar (nind + nmin + 1 + (nm - 1 - j))).mkApps (VExpr.bvarsDesc 0 (nind + 1))

/-- The syntactic shape of a constructor type: exactly `arity` Π-binders ending in a constant
application (`CtorHeaded`). Which binders are parameters and whether the constant is a type
former, a bare `VEnv` cannot say. -/
def VExpr.CtorShape (ty : VExpr) (arity : Nat) : Prop := ty.piArity = arity ∧ ty.CtorHeaded

/-- The type former a recursor type with major index `idx` eliminates: the head constant of
its major premise (the `idx`-th Π-binder). -/
def VExpr.majorFormer? (ty : VExpr) (idx : Nat) : Option Name :=
  ty.piBinders[idx]?.bind VExpr.headConst?

/-- Thesis §2.6.4: the reduct of the ι rule using minor `j` (counted from the outermost
minor binder) is `λ params motives minors fields, minor_j fields v`, minor `j` applied
η-long to the fields and then to further arguments `v` (`recArgs`, an arbitrary list). The
terms `v` are not pinned, syntactically or through typing: `VInductDecl.WF.rules_wf` types
the reduct at the redex's type, which forces only the *types* of `v` — those of the minor's
binders after the fields (`δ`, themselves unpinned by `MinorFor`) — not that they are the
thesis's recursive calls `rec … (u_i x)`. -/
def VExpr.RuleShape (rhs : VExpr) (np nm nmin nf j : Nat) : Prop :=
  rhs.lamArity = np + nm + nmin + nf ∧
  ∃ recArgs : List VExpr,
    rhs.lamBody = (VExpr.bvar (nf + (nmin - 1 - j))).mkApps (VExpr.bvarsDesc 0 nf ++ recArgs)

instance {A : VExpr} : Decidable A.MotiveShape := by unfold VExpr.MotiveShape; infer_instance
instance {A : VExpr} {i nm : Nat} : Decidable (A.MinorHeaded i nm) := by
  unfold VExpr.MinorHeaded; infer_instance
instance {A : VExpr} {c : Name} : Decidable (A.MinorFor c) := by
  unfold VExpr.MinorFor; infer_instance
instance {ty : VExpr} {np nm nmin nind : Nat} : Decidable (ty.RecShape np nm nmin nind) := by
  unfold VExpr.RecShape; infer_instance
instance {ty : VExpr} {arity : Nat} : Decidable (ty.CtorShape arity) := by
  unfold VExpr.CtorShape; infer_instance
instance {rhs : VExpr} {np nm nmin nf j : Nat} : Decidable (rhs.RuleShape np nm nmin nf j) := by
  unfold VExpr.RuleShape; infer_instance

/-- A rule reduct is a λ-abstraction: its λ-arity counts at least the minor premises, of
which there is at least one (`j < nmin`). -/
theorem VExpr.RuleShape.lam {rhs : VExpr} {np nm nmin nf j : Nat}
    (h : rhs.RuleShape np nm nmin nf j) (hj : j < nmin) : ∃ A b, rhs = .lam A b := by
  have h1 := h.1
  cases rhs with
  | lam A b => exact ⟨A, b, rfl⟩
  | _ => simp [VExpr.lamArity] at h1; omega

/-- A minor premise headed by a motive is `RecHeaded`. -/
theorem VExpr.MinorHeaded.recHeaded {A : VExpr} {i nm : Nat} (h : A.MinorHeaded i nm) :
    A.RecHeaded :=
  let ⟨_, _, h⟩ := h; ⟨_, h⟩

/-- A recursor type is `RecHeaded`: its Π-body is a motive application. -/
theorem VExpr.RecShape.recHeaded {ty : VExpr} {np nm nmin nind : Nat}
    (h : ty.RecShape np nm nmin nind) : ty.RecHeaded := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hj⟩ := h
  exact ⟨_, by rw [hj, VExpr.getAppFn_mkApps]; rfl⟩

/-- Register recursor rule `ru` (of recursor `r`) as an ι rule: redex `r`'s spine (major
at `getMajorIdx`) applied to `ru.ctor`'s spine (`ctorParams + nfields` arguments),
reduct `SimplePattern.iotaRHS`. Fails if `ru.rhs` is not closed. Only the constructor
rule of thesis §2.6.4 is registered: K-like reduction (its second rule, on a
non-constructor major of a subsingleton eliminator) is not registered — a completeness
boundary, see `VInductDecl.WF`. -/
def VEnv.addRecRule (env : VEnv) (r : VRecursor) (ru : VRecRule) : Option VEnv :=
  if h : ru.rhs.Closed then
    some <| env.addPat
      (SimplePattern.iota r.name (r.numParams + r.numMotives + r.numMinors + r.numIndices)
        ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs h,
        .true)
  else none

/-! ### The stages of `addInduct`

The kernel (`Inductive/Add.lean`, `run`) declares all type formers, then all constructors
(in block order), then each recursor *together with its rules* (`mkRecRules` inside the
per-recursor loop, installed in one `recInfo`); for a nested block `Environment.addInductive`
inserts type by type (`Verify/Environment/Basic.lean`, `AddInduct.consts`). The model
re-groups this into four stages — all type formers, all constructors, all recursors, then
all ι rules — which yields the same resulting environment as the kernel's interleaving,
not its literal order. Each stage is
named so that `VInductDecl.WF` can type each kind of constant in the environment the kernel
checks it in. -/

/-- Stage 0: add the type formers as constants. -/
def VInductDecl.addTypes (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.types.foldlM (init := env) fun e t => e.addConst t.name t.toVConstVal.toVConstant

/-- Stage 1: add the constructors of every type former, in block order. -/
def VInductDecl.addCtors (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  (decl.types.flatMap (·.ctors)).foldlM (init := env) fun e c => e.addConst c.name c.toVConstant

/-- Stage 2: add the recursors as constants. -/
def VInductDecl.addRecs (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.recs.foldlM (init := env) fun e r => e.addConst r.name r.toVConstVal.toVConstant

/-- Stage 3: register every recursor rule as an ι rule. -/
def VInductDecl.addRules (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.recs.foldlM (init := env) fun e r =>
    r.rules.foldlM (init := e) fun e ru => e.addRecRule r ru

/-- Stages 0–1: the environment the recursors are checked in. -/
def VInductDecl.addTypesCtors (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.addTypes env >>= decl.addCtors

/-- Stages 0–2: the environment the ι rules are registered in. -/
def VInductDecl.addTypesCtorsRecs (decl : VInductDecl) (env : VEnv) : Option VEnv :=
  decl.addTypesCtors env >>= decl.addRecs

/-- The constants of the declaration as `(name, constant)` pairs, in stage order (type
formers, constructors, recursors): stages 0–2 are the `addConst` fold over this list
(`VInductDecl.addTypesCtorsRecs_eq`). -/
def VInductDecl.consts (decl : VInductDecl) : List (Name × VConstant) :=
  decl.types.map (fun t => (t.name, t.toVConstVal.toVConstant)) ++
  (decl.types.flatMap (·.ctors)).map (fun c => (c.name, c.toVConstant)) ++
  decl.recs.map (fun r => (r.name, r.toVConstVal.toVConstant))

/-- Extend `env` with the type formers, constructors, and recursors of `decl` (as
constants) and its ι-reduction rules (as `pats`), or `none` on a name clash or a
non-closed rule reduct. The chain of `VInductDecl.addTypes`, `addCtors`, `addRecs`,
`addRules`. -/
def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv :=
  decl.addTypesCtorsRecs env >>= decl.addRules

/-- Well-formedness of an inductive declaration, staged like the kernel's checks: the type
formers are typed in `env`, the constructors after the type formers are declared, the
recursors after the constructors, and the ι rules after the recursors (`rules_wf`, the
`VDefEq.WF` of a rule: its generic redex and reduct are typed at a common type); universe
parameters line up and the elimination level is pinned (`recs_elim`); the recursor
telescopes have the §2.6.3 shape (`rec_shape`: motives ending in a sort, their last binder
headed by a constant, minors ending in an application of one of the motives, the major
premise a constant application ending in the index variables, the eliminated motive's head
constant that of the major premise);
every type former has a recursor and every recursor over one of the block's type formers has
one rule per constructor (`types_have_rec`, `rules_total`, `rules_nodup`); the rule reducts
have the §2.6.4 shape tied to their minor premise (`rule_shape`: the rule for `c` reduces to
a minor whose last argument is headed by `c`); every rule's `ctor` is a declared constant of
`CtorShape` arity `ctorParams + nfields` (`rules_ctor` — a constants lookup and an arity,
not "is a constructor", which a bare `VEnv` cannot express), with `ctorParams` equal in
count to the recursor's when it is one of the block's own constructors
(`rules_own_params`); and every recursor records the declaration's parameter count
(`rec_params`) — all nested-safe.

**What is assumed rather than derived.** The thesis postulates the ι rule as an inference
rule of its *untyped* ideal definitional equality `Γ ⊢ e ≡ e'` (§2.6.4, over the
specification of §2.6.3); that both sides of every well-typed instance are typed is its
regularity lemmas (`typesys.tex`, "Regularity continued": `Γ ⊢ e : α` and `e ⇝ e'` give
`Γ ⊢ e ≡ e' : α`, i.e. subject reduction for `⇝`; `unique.tex`, "Regularity of reductions",
the same for `⇝_κ`). `rules_wf` is this model's admissibility condition for registering
that rule: the `VDefEq.WF`-style typing of the rule's two sides that `Ordered.pat` demands,
which no kernel check performs — the model-level analogue of that regularity, for the
generic rule. Here it is a field, checked by nothing, and what is derived from it is
`VEnv.Ordered` (`VEnv.addInduct_WF`) — not subject reduction of the rule's instances, which
is the separate strong-system obligation `VEnv.WF.patsStrong`.

**Not pinned syntactically, and only in type through `rules_wf`:** the field binders `b::β`
of a minor premise (those of its constructor) and the binders `v::δ` after them —
`MinorHeaded`/`MinorFor` fix only a minor's head (some motive) and the head constant of its
last argument, so `δ` is free. The
typing `rules_wf` forces the reduct's arguments `v` to have the types `δ` the minor expects,
but pins neither `δ` nor the terms `v`: a rule whose `v` are not the thesis's recursive
calls `rec … (u_i x)` passes every field — a case-analysis principle with fewer inductive
hypotheses, but equally a well-typed `v` that does not call the recursor on a subterm, or a
minor with an extra binder whose rule, though typed, need not normalise.

**Not pinned:** the parameter arguments of the type-former applications in the major premise
and in the motives (the thesis's shared `Γ`) — `IndApp` fixes only the index suffix of the
major premise and `motiveFormer?` only the head of a motive's last binder, and `rules_wf`
types the rule without tying those arguments to the parameter binders (for the auxiliary
recursors of a nested block they are not the parameters: `Tree.rec_1`'s major premise is
over `List Tree`); only the well-formedness of the recursor type constrains them. Likewise
`recs_elim` pins the number of a recursor's universe parameters and the sort its motives
eliminate into, but not that the block's constants occur in its type at the shifted levels
`param (i+1)` (a recursor mentioning the block at `param 0`, its elimination universe,
passes).

**Deliberately not pinned, because false for nested inductive blocks** (the auxiliary
recursor `Tree.rec_1` has two motives while `types = [Tree]`, fires on `List.nil`/`List.cons`,
and `recs.length ≠ types.length`): `numMotives = types.length`, `numMinors = Σ ctors`,
`recs.length = types.length`, `ru.ctor ∈` the block's own constructors, and any constraint on
`all`. `rule_shape` pins one minor per rule; a recursor may have minors without rules.

**Not modelled** (soundness-tier admissibility conditions on the declaration, deferred with
no placeholder proof): strict positivity; the universe constraints on the constructor
arguments (`imax(ℓ', ℓ) ≤ ℓ`); the large-elimination judgment `K LE` itself — `recs_elim`
ties the elimination level to the recursor's extra universe parameter but not that parameter
to the block (a `Prop`-valued block eliminating into `Sort u` passes).

**Completeness boundary, not an admissibility gap:** K-like reduction (thesis §2.6.4's
second rule, on a non-constructor major of a subsingleton eliminator) is not registered.
`addRecRule` installs only the constructor rule and the flag `k` is recorded but unused —
the `pats` registry is syntactic while the kernel's `toCtorWhenK` is type-directed — so the
model's ι reduces strictly less than the kernel's. The *equalities* K-like reduction
produces are nonetheless derivable: the thesis reads it as proof irrelevance followed by ι,
and `IsDefEq` has both (`proofIrrel`, `pat`). What is deferred is the refinement of the
kernel's `toCtorWhenK` step (`Verify/TypeChecker/WHNF.lean`, `reduceRecursor.WF`) and the
admissibility of the recorded `k` (the kernel's `isKTarget`). -/
structure VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop where
  /-- Type formers are typed in `env`. -/
  types_wf : ∀ t ∈ decl.types, t.toVConstVal.toVConstant.WF env
  /-- Constructors are typed once the type formers are declared. -/
  ctors_wf : ∀ envT, decl.addTypes env = some envT →
    ∀ t ∈ decl.types, ∀ c ∈ t.ctors, c.toVConstant.WF envT
  /-- Recursors are typed once the constructors are declared. -/
  recs_wf : ∀ envC, decl.addTypesCtors env = some envC →
    ∀ r ∈ decl.recs, r.toVConstVal.toVConstant.WF envC
  /-- Type formers share the declaration's universe parameters. -/
  types_uvars : ∀ t ∈ decl.types, t.uvars = decl.uvars
  /-- So do the constructors. -/
  ctors_uvars : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, c.uvars = decl.uvars
  /-- §2.6.3, κ: a recursor has the block's universe parameters, plus one extra — the
  first, `VLevel.param 0` — exactly when it eliminates into an arbitrary sort; every motive
  then ends in `Sort (param 0)`, and otherwise in `Prop`. -/
  recs_elim : ∀ r ∈ decl.recs, (r.uvars = decl.uvars ∨ r.uvars = decl.uvars + 1) ∧
    ∀ i < r.numMotives, ∃ A, r.type.piBinders[r.numParams + i]? = some A ∧
      A.piBody = .sort (if r.uvars = decl.uvars + 1 then .param 0 else .zero)
  /-- Every recursor records the declaration's parameter count. A count only: the
  parameter binders of the recursor type are unconstrained (`RecShape`). -/
  rec_params : ∀ r ∈ decl.recs, r.numParams = decl.nparams
  /-- §2.6.3: the recursor telescope split and the shapes of its motives, minors and
  major premise. -/
  rec_shape : ∀ r ∈ decl.recs, r.type.RecShape r.numParams r.numMotives r.numMinors r.numIndices
  /-- A recursor has at most one rule per constructor. -/
  rules_nodup : ∀ r ∈ decl.recs, (r.rules.map (·.ctor)).Nodup
  /-- Every rule's `ctor` is a constant of the stage-1 environment whose type is a
  Π-telescope of `ctorParams + nfields` binders ending in a constant application
  (`CtorShape`). A constants lookup plus an arity, nothing more: a bare `VEnv` records no
  constructors, so this does not say `ru.ctor` *is* a constructor — any constant of that
  shape passes. -/
  rules_ctor : ∀ envC, decl.addTypesCtors env = some envC → ∀ r ∈ decl.recs, ∀ ru ∈ r.rules,
    ∃ ci, envC.constants ru.ctor = some ci ∧ ci.type.CtorShape (ru.ctorParams + ru.nfields)
  /-- A rule on one of the block's own constructors records the recursor's parameter count.
  A count only: the constructor's parameter arguments in the generic redex are holes, tied
  to the recursor's parameters by nothing here (`Pattern.RHS.Generic`). -/
  rules_own_params : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules,
    ru.ctor ∈ decl.types.flatMap (·.ctors.map (·.name)) → ru.ctorParams = r.numParams
  /-- Every type former of the block is eliminated by a recursor of the block. -/
  types_have_rec : ∀ t ∈ decl.types, ∃ r ∈ decl.recs, r.type.majorFormer? r.getMajorIdx = some t.name
  /-- §2.6.3/§2.6.4, `ε` has the length of `K`: a recursor over one of the block's type
  formers has a rule for each of its constructors (exactly one, by `rules_nodup`). Vacuous
  for any recursor whose major premise is over a type former outside `decl.types` — the
  auxiliary recursors of a nested block, but equally a recursor declared over an older type
  former — since a bare `VEnv` records no constructors of older type formers and totality
  over them cannot be stated; such a recursor passes with any set of rules. -/
  rules_total : ∀ r ∈ decl.recs, ∀ t ∈ decl.types, r.type.majorFormer? r.getMajorIdx = some t.name →
    ∀ c ∈ t.ctors, ∃ ru ∈ r.rules, ru.ctor = c.name
  /-- §2.6.4, the reduct shape, tied to §2.6.3's constructor↔minor correspondence: the rule
  for `ru.ctor` reduces to minor `j`, a minor whose last argument is headed by `ru.ctor`
  (`MinorFor` pins that head constant only; nothing pins a unique such minor). -/
  rule_shape : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∃ j < r.numMinors,
    ru.rhs.RuleShape r.numParams r.numMotives r.numMinors ru.nfields j ∧
    ∃ A, r.type.piBinders[r.numParams + r.numMotives + j]? = some A ∧ A.MinorFor ru.ctor
  /-- §2.6.4 as a typing, the `VDefEq.WF` of an ι rule: as registered by `addRecRule`, in
  the stage-2 environment, the rule is typed (`VEnv.PatTyped`, the typing half of
  `VEnv.PatWF`; the other half, the template shape of the reduct, is `rule_shape`) — its
  generic redex `rec params motives minors idx (c cargs fields)` and reduct
  `rhs params motives minors fields` are typed at a common type in the context of the
  parameters, motives, minors and fields. -/
  rules_wf : ∀ envR, decl.addTypesCtorsRecs env = some envR → ∀ r ∈ decl.recs, ∀ ru ∈ r.rules,
    ∀ hc : ru.rhs.Closed,
    envR.PatTyped
      (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hc,
        .true)

/-- Every constructor of the block has a rule in some recursor of the block
(`types_have_rec` and `rules_total`). -/
theorem VInductDecl.WF.ctors_have_rules {env : VEnv} {decl : VInductDecl} (H : decl.WF env) :
    ∀ t ∈ decl.types, ∀ c ∈ t.ctors, ∃ r ∈ decl.recs, ∃ ru ∈ r.rules, ru.ctor = c.name := by
  intro t ht c hc
  obtain ⟨r, hr, hmaj⟩ := H.types_have_rec t ht
  obtain ⟨ru, hru, hctor⟩ := H.rules_total r hr t ht hmaj c hc
  exact ⟨r, hr, ru, hru, hctor⟩
