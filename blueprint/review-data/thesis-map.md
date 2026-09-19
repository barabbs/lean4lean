# The thesis and lean4lean: a structural map

Sources read in full: `lean-type-theory/{main,intro,axioms,typesys,unique,Wtypes,soundness,normalization,compilation}.tex`
(1 690 lines of LaTeX, of which `lstlean.tex` is a listings style and `test.tex` is empty).
Repository read: `lean4lean` on branch `trproj` (which has `iota` merged into it), commit `20ec229`.

---

## 1. What the thesis actually is

Mario Carneiro's *The Type Theory of Lean* is an eight-section article in three movements plus two
stubs.

**Movement 1 — the axioms (§2, `axioms.tex`, 244 lines).** This is the only chapter that *defines*
Lean. §2.1 gives the syntax and the seven typing rules; §2.2 gives the ideal definitional equality
`≡` (congruences, β, η, proof irrelevance) together with a syntactic derivation system for level
inequality `ℓ ≤ ℓ'+n`; §2.3 gives the *algorithmic* equality `⇔` — the relation Lean actually checks,
"in which the transitivity rule is notably absent" — and a head reduction `⇝`; §2.4 and §2.5 add
`let`/ζ and constants/δ, each with a one-paragraph conservativity argument; §2.6 is inductive types;
§2.7 adds quotients, `propext` and `choice`.

**Movement 2 — syntactic metatheory (§3–§4).** `typesys.tex` proves that `≡` is *undecidable* (via
`Acc` and a projection out of `intro`), that `⇔` is therefore not transitive, and that the
algorithmic typing judgment fails subject reduction; then it records Regularity, Weakening and
Substitution as "essentially trivial inductions… recorded here simply to keep track of the
invariants". `unique.tex` is the technical heart: to prove unique typing it stratifies the
judgments as `⊢ₙ` by the number of alternations between typing and conversion, splits `≡` into a
`βδζι`-reduction `⇝_κ` and a proof-irrelevance relation `≡_p`, proves Church–Rosser *modulo* `≡_p` by
Tait–Martin-Löf, and closes the induction with "definitional inversion" at `n+1`.

**Movement 3 — semantics (§5–§6).** `Wtypes.tex` replaces general inductive types by eight
primitives (⊥, Σ, +, `ulift`, ‖·‖, W, `=`, `Acc`) and translates `spec`/`ctor` derivations into
W-types plus a `good` predicate, with subsingleton eliminators going to a parameterised `Acc`.
`soundness.tex` splits proofs from data, interprets the result in ZFC with a hierarchy
`U₀={∅,{•}}, U_{n+1}=V_{κₙ}`, and proves soundness and relative consistency.

**The two stubs.** `normalization.tex` (§7) notes that the `K⁺` rule of §4 makes `⇝_κ`
non-terminating, defines a weaker `⇝_σ`, and stops at the word `UNFINISHED`. `compilation.tex` (§8)
is 24 lines with an unfinished grammar (`e ::=`). §6.5 (equality reflection) also breaks off
mid-sentence and ends `UNFINISHED`. **Anyone claiming to "follow the thesis" inherits an incomplete
document from §6.5 onward**, and two of its eight sections are not results at all.

Numbering note: the `§2.6.x` citations sprinkled through lean4lean's docstrings are *correct* for
these sources (§2 = The axioms, §2.6 = Inductive types, §2.6.1 specifications, §2.6.2 large
elimination, §2.6.3 the recursor, §2.6.4 the ι rule).

---

## 2. How lean4lean realises it

`Theory/` is §2 plus parts of §3–§4; `Verify/` has **no** thesis counterpart at all.

| thesis | lean4lean |
|---|---|
| §2.1 syntax | `Theory/VExpr.lean`, `Theory/VLevel.lean` — de Bruijn, no `let`, no `proj`, no literals |
| §2.1 typing + §2.2 `≡` | `Theory/Typing/Basic.lean` — **one** relation `VEnv.IsDefEq env U Γ e₁ e₂ A`, with `HasType e A := IsDefEq e e A` |
| §2.2 levels | `Theory/VLevel.lean` — the *semantics* taken as the definition; `Theory/LevelSat.lean` proves NP-hardness |
| §2.3 `⇔` | **nothing**; the algorithm is `TypeChecker.lean` and correctness is `Verify/TypeChecker/` |
| §2.3 `⇝` | `Theory/Typing/HeadReduction.lean` (`WHRed`, `StRed`, `InferType`) |
| §2.4 ζ | **no rule**; `Expr.letE` is substituted away in `TrExprS.letE` |
| §2.5 δ | `VEnv.defeqs` + `IsDefEq.extra` |
| §2.6 inductives | `Theory/VDecl.lean`, `Theory/Inductive.lean`, `Theory/Typing/Pattern.lean`, `InductiveLemmas.lean`, `InductiveParams.lean` — **the `iota` branch** |
| §2.7 quotients | `Theory/Quot.lean` (`quotDefEq` as a `VDefEq`), `Verify/Environment/Quot.lean` (615 lines, `iota`) |
| §3 Regularity/Weakening/Substitution | `Theory/Typing/Lemmas.lean` — realised and generalised (`Ctx.LiftN`, `Ctx.InstN`, `Ctx.SubstEq`) |
| §3 subject reduction for ι | `VEnv.PatsStrongOn` / **`VEnv.WF.patsStrong` — `sorry`** |
| §4 unique typing | `Theory/Typing/UniqueTyping.lean` — proved, but by a *different* route (`HasTypeStratified`, not `⊢ₙ`) |
| §4 `≡_p`, `≫_κ`, triangle, Church–Rosser | `Theory/Typing/ChurchRosser.lean` (`NormalEq`, `ParRed`, `CParRed`, `CRDefEq`) — two `sorry`s remain, in master |
| §4 definitional inversion | `Theory/Typing/Injectivity.lean` — **three `sorry`s, the whole file** |
| §4.1 rec-normal form / η-expansion | **no counterpart** (see §5 below) |
| §5 W-types | **nothing** |
| §6 ZFC model, soundness, consistency | **nothing** |
| §7–§8 | **nothing** (and the thesis has nothing either) |
| — | `Verify/` — kernel↔model correspondence (`TrExprS`, `TrEnv`, `TrProj`), no thesis analogue |

Two structural facts about the table are worth stating outright. First, **lean4lean's top-level
theorem is kernel correctness, not consistency**: the entire soundness half of the thesis is absent,
so no result in the repository entails that Lean is consistent. Second, **§2.3's `⇔` is never
formalized**, so the thesis results that are *about* the algorithmic relation (non-transitivity,
failure of subject reduction, "algorithmic equality implies definitional equality") have no
statements to point at; their practical stand-in is the `Verify/TypeChecker` chain.

---

## 3. (a) Inductive types: where the thesis treats them, and what `iota` did with it

The thesis opens §2.6 with a warning that reads, in hindsight, like a description of the `iota`
branch:

> Inductive types are by far the most complex feature of Lean's axiomatic system, and moreover are
> very tricky to prove properties about due to their notational complexity.

**Positivity (§2.6.1).** The thesis never uses the phrase "strict positivity". Positivity is
*built into the grammar* of the `ctor` judgment, whose two inductive cases it glosses:

> There are two kinds of arguments, represented by the two inductive cases here. The first kind is a
> nonrecursive argument. The type of this argument must not mention `t`, but it can be used in the
> types of later arguments. A recursive argument has the type `∀z::γ. t e`, and cannot be referenced
> in later arguments.

lean4lean does **not** reproduce this judgment. `Theory/Inductive.lean` (438 lines introduced on
`iota`) replaces it by flat predicates over an already-elaborated Π-type: `VExpr.CtorResult`
(arity, head constant, the parameter spine `bvarsDesc`, index count) and
`VExpr.CtorPositive`/`FieldPositive`/`ValidIndApp`/`MentionsConst`, which mirror the *kernel's*
`checkPositivity`/`isValidIndApp?` rather than the thesis's grammar. The docstrings claim §2.6.1 for
each. That is a defensible design for a kernel-facing model — the kernel receives elaborated types,
not derivations — but it is a different object, and **no lemma anywhere relates `CtorPositive` to the
thesis's `ctor` judgment**. Two gaps are documented in-source rather than papered over: the model
reads only *manifest* Π-binders where the kernel `whnf`s each field type first, and the universe
side condition `imax(ℓ',ℓ) ≤ ℓ` is hived off into `VInductDecl.WF.universes`.

The thesis also anticipates lean4lean's treatment of `μ`:

> In Lean, `μ t:F. K` and `c_{μ t:F.K}` are implemented as additional axiomatic constant symbols
> (with no free variables, by abstracting over the variables in `Γ`).

`VEnv.addInduct` takes exactly this route, in four staged passes (`addTypes`, `addCtors`, `addRecs`,
`addRules`) chosen so each kind of constant is typed in the environment the kernel checks it in.

**Elimination levels (§2.6.2).** The thesis's two reasons are quoted almost verbatim by
`VInductDecl.LargeElim`:

> There are two reasons an inductive type can be large eliminating: 1. The type family
> `t : ∀x::α. U_ℓ` lives in a universe `1 ≤ ℓ`… 2. The type family has at most one constructor, and
> all the non-recursive arguments to the constructor are either propositions or directly appear in
> the output type. This is called *subsingleton (SS) elimination*…

`LargeElim` is `ℓ.IsNeverZero ∨ (one former, no ctor) ∨ (one former, one ctor, every field a Prop or
`FieldInIndices`)`. Faithful. One consequence to note: because the Prop clause is a *typing*
judgment, `LargeElim` is undecidable; `LargeElimShape` is the decidable residue and
`LargeElim.shape` the only bridge. The kernel's `AddInductive.isLargeEliminator` is never proved to
agree with either.

**The recursor (§2.6.3) — the weakest link.** The thesis fixes three things:

> `κ = ∀a::α. P a → U_u` where `u` is a fresh universe variable if `Γ;t:F ⊢ K LE`, otherwise
> `κ = ∀a::α. P a → P`; `ε` is a sequence of the same length as `K`, where
> `ε_c = ∀b::β. ∀v::δ. C p[b] (c b)`; `δ` is a sequence of the same length as `γ`, where
> `δ_i = ∀x::ξ_i. C π_i[b,x] (u_i x)`.

`κ` is handled well: `VInductDecl.WF.recs_elim` says a recursor carries the block's universe
parameters plus exactly one extra — which must be `VLevel.param 0` — iff every motive ends in
`Sort (param 0)`, else `Prop`. The length of `ε` is `rec_counts` + `rules_total`. But `ε_c` itself is
**only partially pinned**: `VExpr.MinorFor`/`MinorHeaded` require that minor `i`'s Π-body is an
application of one of the motives whose last argument is headed by constructor `c`, and nothing
more. Neither the `b::β` prefix nor the inductive-hypothesis binders `δ_i` are constrained. The
source says so: *"the terms `v` are not pinned, syntactically or through typing"*, *"the heads of the
other motives of a mutual recursor are unconstrained"*. So `VInductDecl.WF` admits recursor types
whose minor premises are not the thesis's. Whether that suffices for the intended downstream
theorems is precisely the question a reviewer should press.

**The ι rule (§2.6.4) — the core of the contribution.** The thesis:

> `Γ, C:κ, e::ε, b::β ⊢ rec_P C e p[b] (c b) ≡ e_c b v` where `v::δ` is defined as
> `v_i = λx::ξ_i. rec_P C e π_i[b,x] (u_i x)`. (Technically, the reduction rule is all substitution
> instances of this rule for all the variables left of the turnstile.)

That parenthesis is what `iota` implements. Master already had `Pattern`/`Matches`/`RHS`/`Check`
(the schematic-rewrite machinery) but **nothing registered a pattern**: `VEnv` had no `pats` field
and `IsDefEq` had no `pat` rule. The `iota` branch adds `VEnv.pats`, `VEnv.addPat`, `IsDefEq.pat`,
`Ordered.pat`, `VEnv.PatTyped`/`PatWF`, the reduct builders `SimplePattern.iotaRHS'`/`iotaRHS`, and
`VEnv.addRecRule`, so that each `VRecRule` of a well-formed block becomes a registered rewrite with
redex `(rec).varN M ((c).varN N)` and reduct the kernel's stored `rhs` template. Three faithfulness
caveats, each documented in the source rather than hidden:

1. `v` is pinned only in **number** (`RuleShape`'s `recArgs.length = nrec`), not in shape. The
   thesis's `v_i = λx::ξ_i. rec_P C e π_i[b,x] (u_i x)` is *not* required.
2. The reduct template comes from the kernel's `RecursorRule`. What `VInductDecl.WF.rules_wf`
   asserts is "the kernel's rule is well-typed and template-headed" (`VEnv.PatTyped`), not "the
   kernel's rule is the thesis's rule".
3. `IsDefEq.pat` asserts the reduct at the **redex's** type with no typing premise on the reduct —
   the docstring calls this "the thesis's regularity theorem for ι taken as a rule".

**K-like reduction is not modelled at all.** The thesis:

> This rule suffices for the theoretical presentation, but there is a second reduction rule called
> "K-like reduction" used for subsingleton eliminators. It can be thought of as a combination of
> proof irrelevance to change the major premise into a constructor followed by the iota rule.

`VEnv.addRecRule`'s own docstring concedes the point ("K-like reduction … is not registered"), and
`VRecursor.k` is recorded and unused. The kernel implements it (`toCtorWhenK`). So the model's ι is
strictly weaker than Lean's conversion. Conversely — and this is not discussed anywhere in the repo
— the thesis's §4.1 `ι` rule is restricted to *non*-subsingleton inductives, with `K⁺` covering the
rest, whereas lean4lean registers ι for every constructor of every block. lean4lean therefore
diverges from §4 on **both** sides of that split, and happens to line up instead with §7's `⇝_σ`.

---

## 4. (b) Structure projections: what the thesis says, and what `trproj` claims

**The thesis has no treatment of Lean's `Expr.proj`.** It never mentions structures, structure η,
`inferProj`, or a projection node. Projections appear in exactly two places, both indirect.

**(i) Primitive Σ-projections, in the W-type chapter (§5.1).** Introducing the eight primitives that
*replace* general inductives, the thesis gives

> `Γ ⊢ p : Σx:α. β  ⟹  Γ ⊢ π₁ p : α`   and   `Γ ⊢ p : Σx:α. β  ⟹  Γ ⊢ π₂ p : β[π₁ p/x]`

with the ι rules `π₁(a,b) ≡ a`, `π₂(a,b) ≡ b`, and it then *adds* two η rules it admits Lean does
not have:

> The following additional "η rules" are needed for the reduction, which are provable but not
> definitional equalities in Lean. Since we are going for soundness only, we will help ourselves to
> this modest strengthening of the system… (These rules are also required for this axiomatization
> since we've omitted the recursors in favor of projections for Σ and `ulift`.)
> `↑↓x ≡ x`   `(π₁ x, π₂ x) ≡ x`

**(ii) The `inv_x` idiom, in the undecidability section (§3.1).** Proving `≡` undecidable, the
thesis needs to project the argument back out of `Acc.intro`:

> One interesting fact about `Acc` is that we can project out the argument given a proof of `Acc x`:
> `inv_x : Acc x → ∀y:α. y<x → Acc y`,
> `inv_x := λa:Acc x. λy:α. rec_Acc (λz. y<z → Acc y) (λz. λh:(∀w. w<z → Acc w). λ_. h y) x a`

and §4.1 generalises the idiom: "`inv_i` is an atomic projection function. These `inv_i` projection
operators can be defined using the recursor, like we demonstrated for `Acc`."

**What `trproj` claims and whether it holds up.** `Theory/Proj.lean`'s module docstring cites both
passages: it says the expansion's shape "is Carneiro's thesis's `inv_x` (typesys.tex
§'Undecidability of definitional equality')", and that the motive giving `P_i e : F_i[f_j := P_j e]`
is "the dependent typing shape of the thesis's *primitive* projections `π₂ p : β[π₁ p/x]`
(Wtypes.tex, whose W-type system omits the recursors for Σ in favour of projections)". The level
list `uss j` is attributed to §2.6.3's `κ`, "with `u` a *fresh* universe variable per use of
`rec_P`".

Those three citations are individually accurate. But they should be read for what they are: the
thesis contains **no theory of Lean's projections**, so "TrProj by the thesis's dependent motive" is
a borrowed *idiom*, not an inherited *result*. Two ironies are worth registering. First, `inv_x` is
introduced in the thesis to prove conversion **undecidable**; `trproj` reuses it as the
representation of every structure projection. Second, `π₂ p : β[π₁ p/x]` is a rule of the system the
thesis builds to *eliminate* general inductives — a system lean4lean does not formalize at all.

The realisation itself is sound work. `VExpr.projFn`/`projFns`/`projMotiveBody`/`projTy`/
`fieldSelector`/`instFields`/`instPis` build the expansion; `TrProjCtor` (in `Verify/Typing/Expr.lean`)
relates a structure value to the expansion of its `i`-th projection with eight explicit clauses,
including the registered-ι-rule witness (`pat`) and the minor-arity pin (`minor_arity`) that excludes
reflexive structures; `TrEnv.proj_defeq` *derives* the thesis's `π_i(a,b) ≡ a_i` rather than assuming
it, by firing the registered ι rule and β-reducing through `fieldSelector`. `Tests/ProjShape.lean`
validates the builders against the real kernel and `Tests/ProjInhabit.lean` inhabits `TrProjCtor` on
two hand-built blocks with `sorry`-free witnesses.

**The one thing the representation cannot carry is structure η**, and the docstring says so:
*"the checker's `tryEtaStruct` and `toCtorWhenStruct` equate a value with its expansion …, and
`IsDefEq` has no such rule (`tryEtaStructCore.WF` is the open obligation)."* Note the three-way
disagreement this produces: the **thesis** adds Σ-η while admitting Lean lacks it; the **Lean
kernel** has structure η; the **lean4lean model** has none. No two agree, and none of the three
justifies the kernel's rule.

Scope and openness. `TrProjCtor` covers only non-mutual, single-constructor, non-recursive,
non-indexed structures. `inferProj.WF` (master) and `inferProj.WF_struct` (added on `trproj`) are
both `sorry`; the branch narrowed the obligation and documented why the general one "is not provable
as stated", but did not close either.

---

## 5. What the thesis says that the repo's own docs flag as divergences

`divergences.md` is written against Lean's **C++ kernel**, not against the thesis, but several
entries bear directly on thesis items:

* **Level algebra (§2.2).** `divergences.md` records that lean4lean's `normalize'`/`isEquiv'`/`geq'`
  "fall back to a complete decision procedure for level algebra, so lean4lean decides level equality
  and ≥ for *more* pairs than either the standard library or the kernel". The thesis presents a
  *syntactic* derivation system for `ℓ ≤ ℓ'+n` and gives its semantics informally; lean4lean defines
  `VLevel.LE` **as** the semantics (`∀ ls, eval ls ≤ eval ls`), so it is complete by fiat and the
  thesis's algorithm is nowhere verified. `Theory/LevelSat.lean` then shows the problem is NP-hard —
  a fact the thesis does not mention.
* **`inferProj` / `toCtorWhenStruct` (no thesis counterpart).** lean4lean tests `isNeverZero` where
  Lean tests `!isAlwaysZero`, explicitly so that "`Expr.proj` [stays] no more powerful than the
  recursor the kernel generates for the same type". That is the *justification* for `trproj`'s
  whole representation choice, and it comes from `divergences.md`, not from the thesis.
* **Nested inductives (§2.6).** The thesis's `spec` judgment cannot express a nested inductive at
  all. `VInductDecl.WF` excludes them by design ("modelling that pass is future work"), while the
  kernel compiles them away via `ElimNestedInductive` — and `divergences.md` has three separate
  entries about how lean4lean's handling of that pass differs from Lean's. Thesis, model and kernel
  differ three ways here.
* **Quotients (§2.7.1).** The one divergence entry added by these branches is the `checkEqType`
  rejection of an `unsafe Eq` — from the `iota` quotient work.
* **Compilation (§8).** `reduceNative`/`reduceBool` is unsupported "because it would involve
  implementing verified compilation". Since §8 is itself a stub, nothing is lost relative to the
  thesis, but the chapter is doubly dead.

Documentation drift the branches did **not** fix: `README.md` was not touched at all. Its
`Theory` file breakdown still omits `LevelSat.lean`, `Proj.lean`, and `Typing/{ChurchRosser,
EnvLemmas, HeadReduction, InductiveLemmas, InductiveParams, Injectivity, Pattern}.lean`; its `Verify`
breakdown omits `Environment/Quot.lean` and the whole `Environment/Primitive/` tree; and it still
describes `Typing/UniqueTyping.lean` as "conjectures about the typing relation" although unique
typing is now proved there and the conjectures have moved to `Injectivity.lean`. Across `iota` and
`trproj` together, the documentation delta is **one line** in `divergences.md`.

---

## 6. Proof-state warnings a reviewer must carry into the rest of the review

1. **`VEnv.WF.patsStrong` is `sorry`** (`Theory/Typing/EnvLemmas.lean:334`, `iota`). It is exactly
   the thesis's *"If `Γ ⊢ e:α` and `e ⇝ e'`, then `Γ ⊢ e≡e':α`"* (§3.2, "Regularity continued")
   specialised to ι, and its docstring says so.
2. **It made a previously unconditional theorem conditional.** On `master`,
   `Ordered.strong : Ordered env → OnTypes env (EnvStrong env)` needed no side hypothesis. On `iota`
   it becomes `VEnv.WF.strong` with a `PatsStrong` premise, discharged only by the `sorry`. Since
   `VEnv.WF → OrderedStrong` now routes through it, **`IsDefEq.uniq` (unique typing) and everything
   downstream — including `trproj`'s `TrEnv.proj_defeq` — now depend on `sorryAx`**, where they did
   not before. The repo is transparent about it (`Tests/ProjInhabit.lean` contains a `#print axioms`
   guard showing `sorryAx` and naming the three causes), but it is a genuine regression in the proof
   state and should be weighed as such.
3. **`Theory/Typing/Injectivity.lean` is three `sorry`s and nothing else** (master). This is the
   thesis's Definition 4.3 (definitional inversion), obtained in the thesis *semantically* via §6.4's
   tagged types. `patsStrong`'s docstring names it as the missing ingredient. Neither branch touched
   it, although §4.2's completeness-of-κ argument — which the repo already formalizes — is the
   thesis's own route to it.
4. **Church–Rosser (§4.2) still has two `sorry`s in master** (`ChurchRosser.lean:1193, 1212`, the
   `extra` cases of `NormalEq.parRed`, i.e. the thesis's Lemma 4.8). Separately, the whole chapter is
   stated relative to a `VEnv.Params` typeclass which, before `iota`, **had no instance at all**.
   `VEnv.toParams`/`inductParams`/`IsDefEq.crDefEq_of_induct` supply the first one — a real advance —
   but only for environments built from axioms and inductives, because δ and the quotient rule live
   in `defeqs` rather than `pats` and so fail `DefEqsAsPats`.
5. **`inferProj.WF` and `inferProj.WF_struct` are `sorry`** (`Verify/TypeChecker/InferType.lean`),
   as is `reduceRecursor.WF` (master). `trproj`'s `inductiveReduceRecCore.WF` is a complete proof of
   the step *inside* `reduceRecursor.WF`, but the wrapper is still open.
6. **`Lean4Lean.Tests` is not in `defaultTargets`** (pre-existing, unchanged). The validation files
   `Tests/{IotaShape, ProjShape, ProjInhabit, ShapeDecide}.lean` — which are where the `iota`/`trproj`
   specifications are checked against the real kernel — do not run on a plain `lake build`.
