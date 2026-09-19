# Group `theory-typing` — `Lean4Lean/Theory/Typing/{Basic,Env,EnvLemmas,Lemmas,Meta,QuotLemmas,Injectivity}.lean`

All paths below are relative to
`/home/barabba/Documents/Research/Projects/Peregrine/lean4lean`.
Branch attribution comes from the precomputed per-line blame; **no line in this group is
`P` (trproj)** — every contributed line here belongs to the `iota` branch.

| file | lines | M (master) | I (iota) | P (trproj) |
|---|---|---|---|---|
| `Theory/Typing/Basic.lean` | 105 | 76 | 29 | 0 |
| `Theory/Typing/Env.lean` | 66 | 52 | 14 | 0 |
| `Theory/Typing/EnvLemmas.lean` | 343 | 106 | 237 | 0 |
| `Theory/Typing/Lemmas.lean` | 1059 | 985 | 74 | 0 |
| `Theory/Typing/Meta.lean` | 46 | 46 | 0 | 0 |
| `Theory/Typing/QuotLemmas.lean` | 60 | 33 | 27 | 0 |
| `Theory/Typing/Injectivity.lean` | 34 | 34 | 0 | 0 |

## 1. What the files do

**`Basic.lean`** is the abstract type theory of the thesis (`axioms.tex` §2.1–§2.2) in one
inductive: `Lean4Lean.VEnv.IsDefEq env U Γ e₁ e₂ A` simultaneously models
`Γ ⊢ e : α` (as the diagonal `IsDefEq Γ e e A`, abbreviated `HasType`) and `Γ ⊢ e ≡ e' : α`.
Master's rules are `bvar, symm, trans, sortDF, constDF, appDF, lamDF, forallEDF, defeqDF,
beta, eta, proofIrrel, extra` — a one-to-one match with `axioms.tex` §2.1/§2.2 plus the δ
rule as `extra` (a `VDefEq` axiom). The iota branch adds a fourteenth rule, `pat`
(`Basic.lean:60`), the ι/recursor computation rule of `axioms.tex` §2.6.4, and the two
predicates `VEnv.PatTyped` / `VEnv.PatWF` (`Basic.lean:92,104`) that say when a schematic
rule may be registered.

**`Env.lean`** is environment well-formedness: `VDecl.WF` (one declaration step: axiom, def,
mutual def, opaque, example, quot, induct), `VEnv.WF'` (a list of such steps) and
`VEnv.WF`. The iota addition is `VEnv.WFPrefix` (`Env.lean:57`), "`env₀` is the environment
reached by a prefix of `env`'s declaration list", plus its transitivity.

**`Lemmas.lean`** is master's structural metatheory — context liftings (`Ctx.LiftN`,
`Ctx.Lift'`, `Ctx.InstN`), `Lookup`, `OnCtx`/`CtxClosed`, `VEnv.Ordered` (the environment
invariant used by all the structural lemmas), and then weakening (`thm:weak`), level
instantiation, substitution (`thm:subst`), context conversion, regularity
(`IsDefEq.isType`, `closedN'`, `levelWF`), the Π/sort inversion lemmas, and simultaneous
substitution (`Ctx.SubstEq`). The iota branch touched it in 17 small places: one new
constructor `Ordered.pat`, two `addPat` lemmas, four new `Pat*` lemmas
(`PatTyped.mono`, `PatWF.mono`, `Ordered.patWF`, `Ordered.patHeaded`) and a `pat` case in
each of the ten inductions over `IsDefEq`.

**`EnvLemmas.lean`** is where the contribution is concentrated (237 of 343 lines). Master's
half ends at `VEnv.WF.ordered` (`:87`). The iota half rebuilds the bootstrap of the *strong*
system (`Theory/Typing/Strong.lean`) from `VEnv.WF` rather than from `VEnv.Ordered`:
`VEnv.PatsStrong` (`:130`) is the ι subject-reduction hypothesis, and
`foldlM_addConst_strong`, `addDefEqs_strong`, `addRules_strong`, `addQuot_strong`,
`addInduct_strong` thread it through every declaration form up to `VEnv.WF.strong` (`:263`).
The file ends with the open obligation `VEnv.WF.patsStrong := sorry` (`:334`) and the
derived `VEnv.WF.orderedStrong` + a `CoeOut` instance (`:339,343`).

**`QuotLemmas.lean`** types the four quotient constants and the quotient rule. Master proves
`addQuot_WF` and the `addQuot_*` projections; the iota addition is `addQuot_chain` (`:19`),
which exposes the four intermediate environments of `addQuot` so that `addQuot_strong` can
walk them.

**`Meta.lean`** (all master) is the `lookup_tac` / `type_tac` macro pair used to discharge
the closed typing goals of `QuotLemmas`.

**`Injectivity.lean`** (all master) is the file of three admitted inversion lemmas —
`IsDefEqU.sort_inv`, `IsDefEqU.forallE_inv_stratified`, `IsDefEqU.sort_forallE_inv` — with
`IsDefEqU.forallE_inv` derived from the second. These are `unique.tex` Theorem
\ref{thm:1dinv} items 1–3. Not contributed, but they matter here because the docstring of
`VEnv.WF.patsStrong` names them as what its proof will need.

## 2. Fit with the thesis

* `IsDefEq` = `axioms.tex` §2.1 + §2.2, with the thesis's `Γ ⊢ e ≡ e' : α` abbreviation made
  primitive. `Lemmas.lean` then reproves the thesis lemmas: `thm:weak` (`IsDefEq.weakN`,
  `:546`), `thm:subst`.2 (`IsDefEq.instN`, `:691`), `thm:subst`.3 (`IsDefEq.instDF`, `:952`),
  `thm:reg`.2 (`IsDefEq.closedN'`, `:329`), `thm:reg`.4 (`IsDefEq.isType'`, `:912`).
* `IsDefEq.pat` = `axioms.tex` §2.6.4, but **stated in the form of `typesys.tex` "Regularity
  continued" \ref{item:red_equiv} / `unique.tex` "Regularity of reductions" (1)** — "if
  `Γ ⊢ e : α` and `e ⇝ e'` then `Γ ⊢ e ≡ e' : α`" — rather than in the thesis's own form,
  where §2.6.4 gives `Γ, C, e, b ⊢ rec_P C e p[b] (c b) ≡ e_c b v` in a *fixed* context and
  regularity is then a derived lemma. The contribution's own docstring says exactly this
  (`Basic.lean:57–59`). This is the single most consequential design decision in the group
  and is discussed in §4.
* `VEnv.PatTyped` = the parenthetical in §2.6.4, "technically, the reduction rule is all
  substitution instances of this rule for all the variables left of the turnstile": the
  generic instance is the one whose reduct-used holes are exactly the variables of `Γ`.
* `VEnv.WF.patsStrong` = `unique.tex` "Regularity of reductions" (1) again, for the whole
  well-formed environment. The thesis dismisses it ("All parts are easy inductions"); the
  formalization finds it to need Π-injectivity and inversion of the redex's typing, i.e. the
  content of `Injectivity.lean`, and leaves it open. That divergence from the thesis is real
  and, to the author's credit, is documented at length (`EnvLemmas.lean:323–333`).
* `Injectivity.lean` = `unique.tex` \ref{thm:1dinv} 1–3 / `soundness.tex` §"Type
  injectivity".

## 3. Assessment of the contributed parts

### Design — mostly good

The `pats` registry (`VEnv.pats`, another group's file) plus `PatWF` gives the theory a
*schematic* rule form that `VDefEq`/`extra` could not express, and the split
`PatTyped ∧ TemplateHeaded` is well chosen:

* `PatTyped` is genuinely the `VDefEq.WF` analogue — both sides typed at a common type.
* `TemplateHeaded` is the part that earns its keep. Because every registered reduct is a
  closed λ applied to arguments, `Ordered.patHeaded` (`Lemmas.lean:488`) lets the
  Π/sort inversion lemmas survive the new rule with a one-line case
  (`Lemmas.lean:851, 895`): a reduct is never a sort or a Π, so a `pat` step cannot create
  one. Without this the whole inversion layer would have broken. This is the nicest idea in
  the contribution.
* `Pattern.Check.Realizes` (positivity-safe side conditions) is a correct solution to a real
  problem — `Check.OK` mentions the defeq relation and could not sit in the `IsDefEq`
  inductive.
* Keeping `VEnv.WF.strong` parametric in `hp : env.PatsStrong` rather than inlining the
  `sorry` isolates the gap cleanly, and the trailing comment at `EnvLemmas.lean:342` states
  it plainly.

### Design — the two weak points

1. **`IsDefEq.pat` assumes subject reduction.** The rule concludes
   `Γ ⊢ e ≡ r.apply m1 m2 : A` from `Γ ⊢ e : A` with *no* premise on the reduct, so
   `IsDefEq.hasType` immediately gives `Γ ⊢ r.apply m1 m2 : A`. The strong system's
   counterpart (`Strong.lean:89`, `IsDefEqStrong.pat`) does carry that premise, which is
   the right shape; the weak system does not, and the author's own counterexample
   (`EnvLemmas.lean:327–330`: under a definitional axiom `List Nat ≡ List Bool`,
   `List.rec Nat m n c (List.cons Bool true tl)` is well-typed and its reduct is not) shows
   the rule is *false* over a merely-`Ordered` environment. Consequence: every lemma in
   `Lemmas.lean` proved under `Ordered env` is a lemma about a relation that, in general, is
   strictly larger than the thesis's `≡`. Only over `VEnv.WF` environments is `IsDefEq`
   meant to be faithful — and that is exactly what `patsStrong` would show.
2. **`PatTyped` is weaker than it looks.** It is existential in `U`, `Γ`, `e`, `m2` and `B`,
   and `Pattern.RHS.Generic` constrains only the holes the reduct *uses*; the unused holes
   (indices, the constructor's copy of the parameters) may be filled with arbitrary terms
   over `Γ`. So `Ordered.pat` admits a rule that happens to typecheck at one convenient
   instantiation. The `Generic` docstring says so ("What ties them to the recursor's
   arguments is not this predicate but the well-formedness of the block"), which is honest,
   but it means `PatWF` carries much less than its name suggests and `Ordered.pat` is close
   to a bookkeeping condition.

### Proof quality — solid but verbose

The ten `pat` cases added to `Lemmas.lean` are uniform and minimal (5–6 lines each,
`rw [Pattern.RHS.*_apply]` then `refine .pat …` plus the `List.mem_map` bookkeeping for the
`chk` premises). Nothing is over-hypothesised; no new hypotheses were added to any master
lemma. `Ordered.patWF`/`patHeaded` mirror `Ordered.constWF`/`defEqWF` exactly.

The `EnvLemmas.lean` bootstrap is correct but heavy. Master proved the same entry point in
twelve lines (`master:Theory/Typing/Strong.lean:675`, `Ordered.strong`, by
`Ordered.induction`); the iota branch needs ~200 lines because `PatsStrong` is not a
property of `Ordered` and so cannot be threaded by `Ordered.induction` — the induction has
to be redone over `VEnv.WF'`, tracking for each intermediate environment that it is a
constant-only extension of a well-formed prefix. That cost is intrinsic to the design, not
sloppiness, but the plumbing is noisy:

* `VEnv.PatsStrong` (`EnvLemmas.lean:130`) takes `env₁ env₀` **explicitly** and six
  positional hypotheses; every call site reads `hp _ _ hpre₀ .rfl … rfl rfl hord`
  (`:279, 282, 291, 293, 305, 308`). Implicit environments, or a named relation
  "`env₀` is a constant-only extension of a WF prefix of `env`", would halve the noise.
* `addQuot_strong` (`:188`) hand-unrolls `addQuot`'s five steps into 25 lines of
  `l1 … l5 / d1 … d4 / p1 … p4 / O1 … O4 / I1 … I4` with explicit `.trans` chains. Correct,
  but brittle: adding a sixth quotient constant means editing every chain.

### Documentation — a strength

Every contributed declaration carries a docstring, and the docstrings are unusually good:
they say what the definition is *for*, name the thesis section, and — rare — name the
limitation. `EnvLemmas.lean:323–333` (the `patsStrong` docstring) is a model of this: it
states the theorem, gives the counterexample that shows it does not follow from `Ordered`,
names what a proof would need, and points at `Injectivity.lean`. `Basic.lean:96–103`
(`PatWF`) likewise explains why `TemplateHeaded` is the right side condition. This is better
documented than the master code it extends.

### Redundancy / dead code

* `Pattern.Check` is **currently exercised by nothing**. Every ι rule registered by
  `addRecRule` uses `Check.true` (`Theory/Inductive.lean:420–425`,
  `Theory/Typing/InductiveParams.lean:103,114`, `InductiveLemmas.lean:630,639`,
  `Verify/Environment/Lemmas.lean:688,763`), and K-like reduction — the rule that would need
  a defeq side condition — is explicitly not modelled (`Theory/Inductive.lean:332`). So the
  `chk`/`Realizes` premise of `IsDefEq.pat` and the `map_liftN`/`map_instN`/`map_instL`/
  `map_subst` lemmas supporting it are speculative generality. Defensible (the thesis's
  second §2.6.4 rule will need it), but it is ~10 lemmas and 10 induction-case lines of
  currently unreachable machinery.
* `addQuot_chain` (`QuotLemmas.lean:19`) re-derives, through the same `type_tac` calls, the
  four constant typings that `addQuot_WF` (`:7`) already establishes. `addQuot_WF` could be
  a three-line corollary of `addQuot_chain`; as it stands the two proofs duplicate each
  other.
* No dead declarations: `WFPrefix.trans`, `WFPrefix.le`, `VDecl.WF.le`, `addPat_self`,
  `PatTyped.mono`, `PatWF.mono`, `Ordered.patWF`, `patHeaded` are each used (some only via
  dot notation, so a plain grep understates them).

### Are the statements the right ones?

Mostly yes. `PatsStrong`'s quantification (a WF prefix, then any constant-only extension of
it inside `env`) is exactly what the five `*_strong` lemmas consume, so it is not
over-hypothesised for its purpose — but it is a *six-hypothesis open statement*, and since
it is `sorry` nobody has checked that it is provable in that generality. In particular
`env₁` ranges over WF prefixes, which already contain definitional axioms (the quotient rule
`quotDefEq`, every `def`'s δ rule), so a proof has to show ι subject reduction *in the
presence of δ* — plausibly as hard as the Church–Rosser development itself. If the intended
route goes through `ChurchRosser.lean`, note that `ChurchRosser.Params` requires
`env.WF` and `InductiveParams.toParams` builds it from `VEnv.WF.pat_*` facts; a circularity
check (does anything on that route already consume `OrderedStrong`?) is worth doing before
attempting the proof. As of this branch, `ChurchRosser.lean` does not mention
`OrderedStrong`, so the route appears open rather than circular.

## 4. The one thing a reviewer must not miss

`VEnv.WF.patsStrong` (`EnvLemmas.lean:334`) is `sorry`, and `EnvLemmas.lean:343` installs

```lean
instance : CoeOut (VEnv.WF env) env.OrderedStrong := ⟨(·.orderedStrong)⟩
```

so **any** `henv : env.WF` now silently coerces to the strong-system hypothesis. In master
the corresponding entry point, `Ordered.strong`, was a proved theorem. Downstream this
reaches the whole verified-typechecker layer: `Verify/Primitive.lean` alone was rewritten
from `Ordered` to `OrderedStrong` in 31 places on this branch (it had zero occurrences of
`OrderedStrong` on master), and `Verify/Environment/Primitive/*` uses
`ctx.Ewf.orderedStrong` throughout.

The honest framing is not "the branch broke a proof": master left `VInductDecl.WF`,
`VEnv.addInduct` and `addInduct_WF` as outright `sorry`
(`master:Theory/Inductive.lean:5,7`, `master:Theory/Typing/InductiveLemmas.lean:10`), i.e.
the inductive layer was *unspecified*. The iota branch replaces three stubbed definitions
with a real specification and pays one new open lemma for it. That is a good trade. But the
resulting `sorry` is load-bearing for everything above the strong system, it is reached
through an invisible coercion, and it is the thesis lemma the thesis itself calls "easy" —
all three facts deserve to be stated prominently in the blueprint rather than left in a
trailing `--` comment.
