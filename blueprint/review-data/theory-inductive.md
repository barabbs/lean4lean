# Group `theory-inductive` — inductive blocks, ι-reduction patterns, and the `Params` instance

Files (all paths relative to the repo root `/home/barabba/Documents/Research/Projects/Peregrine/lean4lean`):

| file | lines | M / I / P |
|---|---|---|
| `Lean4Lean/Theory/Inductive.lean` | 444 | 4 / 438 / 2 |
| `Lean4Lean/Theory/Typing/Pattern.lean` | 725 | 229 / 419 / 77 |
| `Lean4Lean/Theory/Typing/InductiveLemmas.lean` | 785 | 8 / 753 / 24 |
| `Lean4Lean/Theory/Typing/InductiveParams.lean` | 433 | 0 / 389 / 44 |

**Branch-attribution caveat.** `git diff iota trproj` on these four files is *empty* except for two line re-wraps and one docstring rewrite (`Inductive.lean:397`, `InductiveLemmas.lean:618`, `InductiveParams.lean:352-394`). Every block the precomputed blame tags `P` — `addRecRule_defeqs`/`addRules_defeqs`/`addInduct_defeqs`, `DefEqsAsPats.of_no_defeqs`/`inductParams`/`crDefEq_of_induct`, and `Pattern.RHS.apply_foldl_var`/`matches_varN_const`/`iotaRHS'_apply` — exists byte-identically on `iota`, because it was first committed on `trproj` (`b4aba6d`) and ported to `iota` as `3de1dcb`. So for review purposes **this whole group is the ι contribution**; `trproj` added nothing of substance here. I kept the blame's `P` tag in the JSON's `attribution` field and noted the duplication per node.

## What master looked like

This is the single most important fact for judging value. On `master`, `Lean4Lean/Theory/Inductive.lean` is seven lines:

```lean
def VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop := sorry
def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv := sorry
```

and `InductiveLemmas.lean` is `theorem addInduct_WF … := sorry`. Inductive types — "by far the most complex feature of Lean's axiomatic system" (axioms.tex §2.6.1) — were entirely unmodelled, which means every downstream statement quantifying over well-formed environments was vacuous at inductive declarations. The contribution replaces both `sorry`-definitions with real definitions and proves `addInduct_WF`, plus it makes the ι rule a first-class reduction rule of the type system (`IsDefEq.pat`, `VEnv.PatTyped`/`PatWF` in `Theory/Typing/Basic.lean`, also ι-attributed) and builds the first concrete `Params` instance for Mario's abstract Church–Rosser development.

## How the four files fit together and fit the thesis

`Inductive.lean` is the specification layer. It splits into (a) total syntactic readers of a `VExpr`'s Π/λ telescope and application spine — these actually live in `Theory/VExpr.lean` (`piArity`, `piBinders`, `piBody`, `lamArity`, `lamBody`, `getAppFn`, `getAppArgs`, `bvarsDesc`, `headConst?`, `motiveFormer?`, `RecHeaded`, `CtorHeaded`), another group's file but also ι work — and (b) predicates built on them:

* §2.6.1 (`\label{sec:inductive}`): `MentionsConst` ↔ kernel `hasIndOcc` (`Inductive/Add.lean:118`); `ValidIndApp` ↔ `isValidIndAppIdx` (`:157`); `FieldPositive`/`CtorPositive` ↔ `checkPositivity` (`:184`); `CtorResult` ↔ the `ctor` judgment's base case.
* §2.6.2 (`\label{sec:large_elim}`): `VInductDecl.LargeElim` ↔ `isLargeEliminator` (`:258`), with `LargeElimShape`/`FieldInIndices` as its decidable syntactic half.
* §2.6.3: `RecShape` (with `MotiveShape`, `MinorHeaded`, `MajorApp`) ↔ the type of $\rec_P$.
* §2.6.4 (`\label{sec:iota}`): `RuleShape`, `VEnv.addRecRule`, and `VInductDecl.WF.rules_wf`.

Two systematic, deliberate deviations from the thesis, both toward the *kernel*: the model carries a parameter/index split (`decl.nparams`) that the thesis's $t\;p[b]$ does not have, and it supports mutual blocks (`decl.types : List VInductiveType`) which the thesis's $\mu t:F.\,K$ does not. Both are right calls — the object being verified is Lean's kernel, not the thesis's calculus — and the docstrings say so.

I checked the de Bruijn arithmetic of `CtorResult` (`:44`), `MajorApp` (`:63`), `FieldPositive` (`:93`), `MinorHeaded` (`:128`), `RecShape` (`:143`) and `RuleShape` (`:174`) by hand against `bvarsDesc lo n = [bvar (lo+n-1), …, bvar lo]` and against `Nat.rec` and `Eq.rec`. All six are correct. This is not obvious code and it is right.

`VInductDecl.WF` (`Inductive.lean:335`) is the payload: a 19-field record, each field documented with its thesis reference, and — the best design decision in the group — **staged**: `types_wf` types the formers in `env`, `ctors_wf` in `addTypes env`, `recs_wf` in `addTypesCtors env`, `rules_wf` in `addTypesCtorsRecs env`, exactly where the kernel checks each. That staging is what makes `InductiveLemmas`' `addTypes_ordered`/`addCtors_ordered`/`addRecs_ordered`/`addRules_ordered` (`:171-219`) three lines each, and `addInduct_WF` (`:229`) a two-line composition.

`Pattern.lean` is Mario's abstract pattern machinery plus everything ι needs. The additions are strictly additive — `git diff master -- Lean4Lean/Theory/Typing/Pattern.lean` contains no deleted lines at all. Three of the additions are conceptually load-bearing:

* `Pattern.RHS.Generic` (`:181`) turns the thesis's "all substitution instances of this rule for all the variables left of the turnstile" into one typing obligation over a context of exactly the holes the reduct uses. `VEnv.PatTyped` (`Theory/Typing/Basic.lean:92`) is built on it.
* `Pattern.Check.Realizes` (`:307`) with `toOK` (`:318`) / `OK.exists_realizer` (`:332`) — a *pure* predicate version of the side conditions, which is what makes the new `| pat` constructor of `IsDefEq` (`Basic.lean:60`) legal (`Check.OK` mentions the defeq relation and cannot occur positively). Clean and necessary.
* `Pattern.RHS.TemplateHeaded` (`:690`) — "a reduction rule computes": the reduct is a closed λ-template applied to arguments, hence no instance is a sort or a Π-type (`apply_ne_sort`, `apply_ne_forallE`). This is the invariant that distinguishes a registered `pats` entry from a `defeqs` axiom and is what `Ordered.pat` requires.

`SimplePattern.iotaRHS'`/`iotaRHS` (`:569`, `:581`) build the reduct, and `iotaRHS'_apply` (`:625`) says what it evaluates to on a concrete match: the template applied to `recArgs.take k ++ ctorArgs.drop cnp` — the *exact* two slices the kernel's `inductiveReduceRecCore` takes. Together with `matches_varN_const` (`:598`) that is the whole bridge used at `Verify/TypeChecker/WHNF.lean:121` and `Verify/Environment/Lemmas.lean:1124`. These are the right statements; they were clearly written by looking at what the consumer needed.

`InductiveLemmas.lean` does the environment bookkeeping: monotonicity, stage decomposition (`addInduct_stages`, `:76`), registration (`addInduct_pat`, `:136`) and its converse (`addInduct_pats_origin'`, `:613`), `pats`/`defeqs` preservation for every *other* declaration kind, a complete specification of an `addConst` fold (including `addConst_comm` and `addConst_foldlM_perm`, which exist so the front end can reconcile the kernel's per-type insertion order with the model's four-stage order), and `addInduct_WF`.

`InductiveParams.lean` is the payoff attempt. `VEnv.PatsIota` (`:133`) is the registry invariant — every registered pattern is an ι redex whose recursor head is a registered `RecHeaded` constant, the recursor name fixes the spine arity, the constructor is a registered `CtorHeaded` constant, and a pattern determines its reduct — preserved by non-inductive steps (`of_le`, `:161`) and by `addInduct` (`induct`, `:181`, the meatiest proof in the group), hence true of every well-formed environment (`WF.patsIota`, `:232`). From it the five structural `Params` side conditions fall out (`:249-334`), with `PatsIota.rec_ne_ctor` (`:148`) — a recursor's type is `RecHeaded`, a constructor's is `CtorHeaded`, and no type is both — doing the real work.

## Assessment

**Design.** Good, and unusually well thought through. The staging of `VInductDecl.WF`, the `Generic`/`Realizes`/`TemplateHeaded` triple, the split of `iotaRHS'` (what reduction sees) from `iotaRHS` (the typed split), and the `PatsIota` invariant are all the right abstractions, and each is justified in prose in the file. The choice to state the syntactic predicates as `Prop`s and file the `Decidable` instances separately (`Tests/ShapeDecide.lean`) so the *tests* can `decide` them on real kernel data (`Tests/IotaShape.lean` runs the whole of `VInductDecl.WF` against `Nat`, `List`, a structure, `Vec`, the mutual `Ev`/`Od`, `Eq`, `Acc`, `False`, and a batch of `Init`/`Std` inductives, and checks `iotaRHS … |>.apply` against the executable `inductiveReduceRec`) is the single strongest piece of evidence that the specification is faithful. Very few formalisations validate their specifications this way.

**Proof quality.** Uniformly high and boringly short, which is the right shape for this material. No `sorry` in any of the four files. Tactic proofs are small and the term-mode ones (`family:ind-shape-corollaries`, the transport lemmas) are direct. The one heavy proof, `PatsIota.induct` (`InductiveParams.lean:181-231`), is well structured.

**Documentation.** The best in the repository, in places better than the code warrants. Every non-trivial declaration has a docstring naming its thesis section and, where it matters, its kernel counterpart by file and function. The "Not modelled" paragraph of `VInductDecl.WF` (`Inductive.lean:332-334`) and the 25-line `DefEqsAsPats` docstring (`InductiveParams.lean:351-377`) are model disclosures of what is *not* proved. Two documentation failures stand out against that standard, below.

**The three things I would push back on.**

1. **Nothing derives `VInductDecl.WF` from the kernel's checker.** `TrEnv'.induct` (`Verify/Environment/Basic.lean:583`) takes `decl.WF env` as a hypothesis; `Lean4Lean/Inductive/Add.lean` — the repository's own re-implementation of the kernel's `checkInductiveTypes`/`checkConstructors`/`isLargeEliminator` — is never related to it. So the refinement chain still has an axiom at exactly the hardest declaration kind. This is *better* than master (the assumption is now informative, and `Tests/IotaShape.lean` gives empirical evidence), but the contribution should be described as "specified and validated", not "verified". Two of the model's deliberate deviations actively obstruct closing this gap: the positivity and universe clauses read *manifest* Π-binders whereas the kernel `whnf`s (`Add.lean:190`), so the model is strictly stricter than the kernel; and nested inductives are excluded by `recs_over_block`/`rules_ctor`.

2. **`crDefEq_of_induct` (`InductiveParams.lean:426`) overstates.** Its docstring says "Church–Rosser for such an environment"; `IsDefEq.church_rosser` routes through `NormalEq.parRed`, which still has two `sorry`s (`ChurchRosser.lean:1193`, `:1212`). Nothing uses the theorem — it is a demonstration that `Params` is inhabitable — and the demonstration is on a toy environment (one inductive block, nothing else), because `Params.extra_pat` forces `DefEqsAsPats`, which fails the moment a `def` or `quot` appears. The `DefEqsAsPats` docstring is completely candid about that; the `crDefEq_of_induct` docstring is not candid about the `sorry`s.

3. **`RuleShape` is weaker than §2.6.4** (`Inductive.lean:174`). The thesis pins $v_i=\lambda x::\xi_i.\,\rec_P\,C\,e\,\pi_i[b,x]\,(u_i\,x)$; the model pins only *how many* such arguments there are, and `rules_wf` only forces them to be well-typed. So `VInductDecl.WF` admits ι rules Lean would never generate. The docstring flags it at length, so this is a known, priced-in weakening rather than an oversight — but it caps what any soundness theorem proved against this model can mean.

**Dead and redundant material** (all minor, all worth a cleanup pass): `VExpr.RecShape.one_le_numMotives` (`Inductive.lean:196`), `VExpr.RecShape.majorFormer?_eq` (`:202`) and `VInductDecl.LargeElim.shape` (`:242`) are referenced nowhere; the eight-declaration `Pattern.RHS.spine`/`iotaCounts` cluster (`Pattern.lean:509-678`, ~70 lines) is used only by itself and is purely documentary ("the reduct retains the template, `np+nm+nmin` and `nf`, and nothing else"); `nodup_map_inj_on` (`InductiveLemmas.lean:451`) is a pure `List` lemma in namespace `Lean4Lean.VEnv`, and the generic `foldlM_*` toolkit and the `addQuot_*`/`addDefEqs_*` lemmas sit in a file named `InductiveLemmas`; `Pattern.inter_app_const`/`_var`/`_app` (`InductiveParams.lean:43-57`) are `_root_.Pattern` lemmas declared inside `namespace VEnv` and belong beside `Pattern.inter`. `VEnv.addRecRule` (`Inductive.lean:259`) spells out `r.numParams + r.numMotives + r.numMinors + r.numIndices` where every lemma about it says `r.getMajorIdx`. `MotiveShape`'s "ends in a sort" clause is subsumed by `WF.recs_elim`, which pins the exact sort. `WF.universes` bundles the purely syntactic `decl.nparams ≤ t.type.piArity` into a clause guarded by stage 0 succeeding. And, pre-existing but touched by this work, `Pattern.Matches.uniq` (`Pattern.lean:143`) and `Pattern.matches_determ` (`:283`) are the same statement proved twice.

**Fidelity nits found by comparing with `Inductive/Add.lean`.** `ValidIndApp` (`Inductive.lean:75`) drops the kernel's exact-arity check `args.size == nparams + nindices[i]` (`Add.lean:161`), so it accepts a former over-applied in its index positions; such a field would be ill-typed and rejected by `WF.universes`, so this is imprecision, not a hole, but the docstring claims to mirror `isValidIndApp?`. `FieldInIndices` (`:107`) searches only the arguments past `nparams` while the kernel searches all of them (`Add.lean:272`); the two agree because `CtorResult` pins the first `np` arguments to be parameter variables, which no field variable can equal — an argument worth recording somewhere. `LargeElim` demands a typing at `.sort .zero` where the kernel tests `isAlwaysZero` on the inferred level; these agree only up to level defeq and uniqueness of typing, which is not proved here.
