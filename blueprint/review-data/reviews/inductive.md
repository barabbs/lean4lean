# Review of chapter inductive

Scope: `blueprint/src/chapters/inductive.tex` (74 nodes, 69 with a `\contrib` badge, 5
master). Sources read in full: `Lean4Lean/Theory/Inductive.lean` (444),
`Lean4Lean/Theory/Typing/Pattern.lean` (725), `Lean4Lean/Theory/Typing/InductiveLemmas.lean`
(785), `Lean4Lean/Theory/Typing/InductiveParams.lean` (433), plus
`Lean4Lean/Tests/ShapeDecide.lean`, `Lean4Lean/Tests/IotaShape.lean`,
`Lean4Lean/Theory/Typing/Basic.lean` (`PatTyped`/`PatWF`/`IsDefEq.pat`),
`Lean4Lean/Theory/VDecl.lean`, `Lean4Lean/Theory/VExpr.lean` (helpers),
`Lean4Lean/Inductive/Add.lean`, `Lean4Lean/Inductive/Reduce.lean`,
`Lean4Lean/Verify/Environment/Basic.lean`, `Lean4Lean/Theory/Typing/EnvLemmas.lean`,
`Lean4Lean/Theory/Typing/ChurchRosser.lean`. Every `\contrib` node was opened at its
`\srcloc`; all 5 master nodes were checked (the chapter has only 5, fewer than the 15 the
task asks for).

## Quality verdict

This is strong, genuinely useful work, not slop: `master` had `VInductDecl.WF := sorry`,
`VEnv.addInduct := sorry` and `addInduct_WF := sorry` (7 and 10 lines total, verified with
`git show master:`), and the branch replaces them with a 20-clause record, a four-stage
environment extension, and a `sorry`-free proof of `addInduct_WF` — no file in the group
contains a literal `sorry`, and only one declaration in the chapter is even transitively
sorry-tainted (`IsDefEq.crDefEq_of_induct`, via master's two `sorry`s in
`NormalEq.parRed`). The design choices hold up under reading: staging `WF` so each constant
kind is typed in the environment the kernel checks it in makes the three constant cases of
`addRules_ordered`/`add*_ordered` one to three lines each; `Check.Realizes`
(`Pattern.lean:307`) is a pure predicate precisely so that the new `IsDefEq.pat` constructor
(`Basic.lean:60`) can be legal, which `Check.OK` could not be; and `PatsIota`
(`InductiveParams.lean:133`) is calibrated to discharge all five structural `Params`
conditions while remaining preserved by `addInduct`. Validation is real rather than
decorative: `Tests/IotaShape.lean` decides `RecShape`/`CtorShape`/`RuleShape`/`MinorFor`/
`CtorPositive`/`LargeElim` on the translated kernel data of ~50 recursors and cross-checks
the `iotaRHS` reduct against the executable `inductiveReduceRec`, with `Tree` as a negative
control. The limits are real too and mostly self-declared: nothing derives `VInductDecl.WF`
from `Inductive/Add.lean` (so `TrEnv'.induct`, `Verify/Environment/Basic.lean:583`, still
assumes it), `RuleShape` counts recursive arguments without constraining them, K-like
reduction and structure η are not modelled, and `toParams`' `DefEqsAsPats` hypothesis holds
only for environments with no `def`/`quot` at all — so `inductParams` and
`crDefEq_of_induct` are a demonstration, not a usable instance. About 70 lines
(`RHS.spine`/`iotaCounts` cluster) and three lemmas are dead code.

## Confirmed code issues

- **`Lean4Lean/Verify/Environment/Basic.lean:583` — high.** `TrEnv'.induct` takes
  `decl.WF env` as a hypothesis and nothing relates `Lean4Lean/Inductive/Add.lean` (the
  repository's own kernel inductive checker) to it. The refinement chain therefore still has
  an assumption at the hardest declaration kind. `Tests/IotaShape.lean` is evidence, not a
  proof. This gap is not acknowledged in any docstring of `VInductDecl.WF`.
- **`Lean4Lean/Theory/Typing/InductiveParams.lean:426` — high.**
  `IsDefEq.crDefEq_of_induct` reads as a finished Church-Rosser result; it routes through
  `IsDefEq.church_rosser` → `NormalEq.parRed`, which still has two `sorry`s
  (`ChurchRosser.lean:1193`, `:1212`, both in the `extra` case, both master code). Confirmed
  from `decls.tsv`: axioms `propext,sorryAx,Classical.choice,Quot.sound`, `usesSorry=true`.
  The docstring gives no hint of the conditionality, and nothing consumes the theorem.
- **`Lean4Lean/Theory/Typing/InductiveParams.lean:393` — medium.** `toParams` is a `Params`
  instance only under `DefEqsAsPats`, which its own docstring admits fails as soon as one
  `def` or `quot` is present. So the Church-Rosser development is still not connected to any
  realistic well-formed environment; the only instance built, `inductParams` (`:419`), is a
  one-block toy.
- **`Lean4Lean/Theory/Inductive.lean:174` — medium.** `VExpr.RuleShape` pins only
  `recArgs.length = nrec`; `WF.rule_shape` sets `nrec = A.piArity - ru.nfields` and
  `rules_wf` only requires the instance to be well-typed. Nothing forces the recursive calls
  to be `rec … (u_i x)`, so `VInductDecl.WF` accepts ι rules Lean would never generate.
  Flagged in the field docstring.
- **`Lean4Lean/Theory/Inductive.lean:257` — medium.** K-like reduction is not registered:
  `addRecRule` installs only the constructor rule and `VRecursor.k` is recorded and unused,
  while the kernel performs it (`Inductive/Reduce.lean:29`, called at `:110`). For K-like
  recursors the model's reduction relation is strictly weaker than the kernel's.
- **`Lean4Lean/Theory/Inductive.lean:93` — medium.** `FieldPositive`/`CtorPositive` and
  `WF.universes` read manifest Π-binders where the kernel `whnf`s at every step
  (`Inductive/Add.lean:189` inside `checkPositivity.loop`). The model is strictly stricter
  than the kernel, which obstructs ever discharging the first item.
- **`Lean4Lean/Theory/Inductive.lean:335` — medium.** `recs_over_block`/`rules_ctor` require
  every recursor to eliminate one of the block's own formers, excluding nested inductives;
  `Environment.addInductive` does add such blocks, so `TrEnv'` can never be built for an
  environment containing one. Documented as future work.
- **`Lean4Lean/Theory/Inductive.lean:351` — low, undocumented.** `WF.universes` hides the
  purely syntactic `decl.nparams ≤ t.type.piArity` inside a clause guarded by `addTypes`
  succeeding, so the arity fact is unavailable if stage 0 fails; and no clause mentions
  `VRecursor.all` (it is pinned to the kernel's only downstream, by `TrRecursor.all`,
  `Verify/Environment/Basic.lean:240`). Neither is recorded in the source.
- **`Lean4Lean/Theory/Inductive.lean:196`, `:202`, `:242` — low, dead code.**
  `RecShape.one_le_numMotives`, `RecShape.majorFormer?_eq` and `LargeElim.shape` have no
  reference anywhere in the repository (checked repo-wide, including dot-notation).
- **`Lean4Lean/Theory/Typing/Pattern.lean:509`–`678` — low, dead code.** `RHS.spine`,
  `spine_foldl_var`, `RHS.iotaCounts`, `iotaPaths_countP_isLeft/isRight`, `iotaRHS'_spine`,
  `iotaRHS'_iotaCounts`, `iotaRHS_iotaCounts`: eight declarations, ~70 lines, with zero
  references outside `Pattern.lean` and, inside it, only from one another.
- **`Lean4Lean/Theory/Typing/InductiveLemmas.lean:451`, `:22`–`:168`, `:281`–`:302` — low,
  placement.** `nodup_map_inj_on` is a pure `List` lemma declared as
  `Lean4Lean.VEnv.nodup_map_inj_on`; the generic `foldlM`/`addConst_foldlM` toolkit and the
  `addQuot`/`addDefEqs` lemmas (about quotients and definitions) live in a file named
  `InductiveLemmas`. Similarly `Pattern.inter_app_const`/`_var`/`_app` are `_root_`
  `Pattern` lemmas declared inside `namespace VEnv`
  (`InductiveParams.lean:43`–`65`).
- **`Lean4Lean/Theory/Inductive.lean:259` — low, style.** `addRecRule` spells the major
  index as `r.numParams + r.numMotives + r.numMinors + r.numIndices` while every lemma about
  it uses `r.getMajorIdx` (definitionally equal, `VDecl.lean:46`).
- **`Lean4Lean/Theory/Inductive.lean:75`, `:107`, `:226` — low, fidelity.** `ValidIndApp`
  drops the kernel's `args.size == params.size + nindices[i]` check
  (`Inductive/Add.lean:159`) although its docstring claims to mirror `isValidIndApp?`;
  `FieldInIndices` searches only the arguments past `nparams` where the kernel searches all
  of them (`Inductive/Add.lean:275`), the two agreeing only by an unrecorded argument about
  `CtorResult`; `LargeElim` demands a typing at `sort 0` where the kernel tests
  `isAlwaysZero` on the inferred level (`Inductive/Add.lean:271`).
- **`Lean4Lean/Theory/Inductive.lean:134` — low.** `MinorFor` makes the
  constructor-to-minor map injective (`getLast?` and `headConst?` are functions), but no
  lemma derives that and nothing uses it; the proofs appeal to `rules_nodup` instead.

## Refuted claims

- **"`git diff iota trproj` is empty except for two line re-wraps and one docstring
  rewrite".** There are *two* docstring rewrites, both in `InductiveParams.lean`
  (`DefEqsAsPats` at `:351`, `toParams` at `:385`). They are the one thing `trproj` has in
  this group that `iota` does not — `iota` calls `DefEqsAsPats` a "**design hypothesis**"
  and lacks the whole δ/quotient analysis. The chapter's blanket "`trproj` added nothing of
  substance here" was therefore wrong about the documentation.
- **"`Pattern.inter` … with `var` absorbing `app`".** Backwards. `Pattern.inter`
  (`Pattern.lean:59`–`60`) sends `.var f ⊓ .app f' a'` to `.app (f ⊓ f') a'`: the `app`'s
  argument pattern survives, because a `var` hole matches any argument.
- **"`Pattern.LE` and `Arity` are declared but used nowhere in the repository".** `Arity`
  and `Arity.subpattern` are used in `Experimental/ShapeLogRel.lean:3436` and `:3620`
  (`LE_Interp.Matches.arity`, `pat_arity`); there is only one `Arity` in the environment
  (`all-constants.tsv:1505`). `Pattern.LE` is indeed unused.
- **"`Matches.uniq` and `matches_determ` … the ι work had to edit both `app` cases".**
  False. `git diff master HEAD -- Lean4Lean/Theory/Typing/Pattern.lean` is 493 insertions
  and **zero** deletions, and `git show master:…` gives byte-identical `app` cases for both
  proofs. The per-line blame's `I` tags on lines 148 and 287 are a blame artefact. (The
  chapter's own claim two paragraphs earlier, "the additions are strictly additive, no
  deleted lines", is the correct one.)
- **"matching a lifted or instantiated expression is equivalent to matching the original".**
  Only lifting is an iff (`matches_lift'`, `matches_liftN`). `matches_instN`
  (`Pattern.lean:232`) is a one-directional transport.
- **"`RHS.apply`, `Matches` and `Realizes` all commute with level instantiation, lifting,
  instantiation and arbitrary substitution" (node `family:pattern-transport-iota`).** In
  that node `RHS.apply` and `Matches` have only the `instL` and `subst` versions; the
  lifting and instantiation versions are master's (`family:pattern-transport-master`). Only
  `Realizes` has all four. Also `apply_levelWF` (`:371`) additionally requires every match
  level `m1` to be `WF U`, not merely the holes.
- **"[`CtorShape`] is what lets the registry invariant `PatsIota.ctor_shape` state it about
  an arbitrary registered constant".** `PatsIota.ctor_shape` (`InductiveParams.lean:141`)
  states `CtorHeaded`, not `CtorShape`. `CtorShape` is what `WF.rules_ctor_shape` /
  `addInduct_rule_ctor` state; `PatsIota.induct` keeps only its `CtorHeaded` half
  (`InductiveParams.lean:218`) and the front end only its arity half
  (`Verify/Environment/Basic.lean:514`).
- **"Six weaknesses, five of them documented in the source" (`VInductDecl.WF`).** Only
  three of the six listed were documented (nested inductives, K-like reduction,
  `rule_shape`'s count-only). The `universes` bundling and the silence about
  `VRecursor.all` are documented nowhere, and the chapter omitted a limitation the docstring
  *does* state (structure η is not modelled) and mis-scoped `VRecursor.all` — it is pinned
  to the kernel's downstream by `TrRecursor.all`.
- **"nothing constrains `VRecursor.all`".** Too broad: `VInductDecl.WF` does not, but the
  refinement does (`TrRecursor.all : r.all = rval.all`,
  `Verify/Environment/Basic.lean:240`).
- **srcloc errors.** `Inductive/Add.lean:161` for the kernel's exact-arity check (it is at
  `:159`; `:161` is the parameter comparison); `Inductive/Add.lean:173` for `checkPositivity`
  reducing to whnf (`:173` is `def isRecArg`; the whnf step is `:189`);
  `Inductive/Add.lean:272` for `isLargeEliminator` searching all result arguments (`:272` is
  `toCheck := toCheck.push arg`; the search is `:275`); `Inductive/Reduce.lean:109` for
  `toCtorWhenK` (defined at `:29`, called at `:110`).
- **Minor overstatements.** "The 25-line docstring" of `DefEqsAsPats` is 27 lines
  (`:351`–`:377`); "each constant stage is three lines" — `addTypes_ordered` and
  `addRecs_ordered` are one-liners, `addCtors_ordered` is three; "the de Bruijn index of the
  body head was checked by hand against `Nat.rec` and `Eq.rec`" is an unverifiable claim
  about the author's process; "every downstream statement … was vacuous" — with
  `WF := sorry` the hypothesis is opaque, so such statements were uninstantiable, not
  vacuously true.

Claims checked and **confirmed** (not refuted), worth recording: the line-attribution counts
(4/438/2, 8/753/24, 0/389/44, 229/419/77, total 2146 contributed of 2387); `master`'s
`Inductive.lean` being 7 lines with the two `sorry`-definitions; the `mixed` badge on
`VInductDecl.WF` (blame: 107 `I`, 2 `P`, the `types_have_rec` re-wrap) and on `addInduct_WF`
(1 master line, the statement, line 229); the `trproj` badges on
`apply_foldl_var`/`matches_varN_const`/`iotaRHS'_apply`/`of_no_defeqs`/`inductParams`/
`crDefEq_of_induct` (all `P` in blame); the dead-code lists; `WF'.pats_origin` having no
consumer; `VEnv.WF.patsStrong` being `sorry` at `EnvLemmas.lean:334`; `matches_varN_const`
being consumed at `Verify/TypeChecker/WHNF.lean:108` and
`Verify/Environment/Lemmas.lean:1099`, and `iotaRHS'_apply` at `:121`/`:1124`; the
`ctors_have_rules`/`rules_own_params` consumers at `Verify/Environment/Basic.lean:509`–`510`;
`TemplateHeaded` being used at `Theory/Typing/Lemmas.lean:851`/`:895` to exclude `forallE`
and `sort` reducts; the three `*_iff` spine lemmas having `Tests/ShapeDecide.lean` as their
only consumer; the twenty clauses of `VInductDecl.WF`; and the `\axfoot` on
`crDefEq_of_induct` matching `decls.tsv`.

## Fixes applied to the tex

All in `blueprint/src/chapters/inductive.tex`; checker clean afterwards
(`74 nodes, 0 errors, 0 warnings`; global `980 labels, 2865 uses edges, 0 cycles, 0 errors`).

1. Overview, attribution caveat: corrected to two line re-wraps **and two docstring
   rewrites**, with `\srcloc`s for all four, restricted the "byte for byte" claim to *code*
   blocks, and replaced "`trproj` added nothing of substance" with the accurate statement
   that the expanded `DefEqsAsPats`/`toParams` documentation is `trproj`'s own.
2. Overview, baseline: replaced "was vacuous at an inductive declaration" with the precise
   consequence (opaque proposition → no such environment provable well-formed → downstream
   theorems uninstantiable). Same fix in the `addInduct` review note.
3. `def:ind-ctor-positive`: disambiguated `bvarsDesc (i + piArity) np` (the arity is the
   *field's*, not `ty`'s).
4. `def:ind-field-in-indices`: srcloc `Add.lean:272` → `:275`, and spelled out the
   `bvarsDesc nf np` vs `bvar (nf-1-i)` argument that makes `drop np` sound.
5. `def:ind-minor-for`: removed the unsupported "this is what makes the correspondence
   injective" and replaced it with the true scope (its only theory use is inside
   `rule_shape`) plus a review note stating that the injectivity holds but is derived
   nowhere and used nowhere.
6. `def:ind-rec-shape`: dropped the unverifiable "checked by hand" claim; replaced with what
   `Tests/IotaShape.lean`'s `checkShapes` actually decides and over which recursors.
7. `def:ind-ctor-shape`: corrected the role of `CtorShape` (it is `rules_ctor_shape`, not
   `PatsIota.ctor_shape`, that states it) and added a review note recording that its two
   halves go to different clients.
8. `structure:ind-wf`: added the missing `rec_params`/`rec_counts` clauses to the body,
   clarified that `ℓ` is the common result sort of every type former; rewrote the review
   note into "four documented in the structure docstring (including structure η), a fifth in
   `rule_shape`'s, two undocumented (`universes` bundling, `VRecursor.all`), plus the
   undocumented absence of a derivation from the kernel checker", with `VRecursor.all`
   correctly scoped against `TrRecursor.all`. Extended `\uses` with
   `def:ind-field-ctx, def:pattern-iota-rhs, inductive:simple-pattern, def:getmajoridx,
   fam:vlevel-lattice`.
9. `def:ind-add-rec-rule` and the K-reduction review-note bullet: `Reduce.lean:109` → the
   definition at `:29` with the call site at `:110`.
10. `inductive:pattern-core`: corrected the `inter` direction (app's argument survives, with
    the equation spelled out); corrected the dead-code note (`Arity` is used in
    `Experimental/ShapeLogRel.lean`; only `Pattern.LE` is unused).
11. `family:pattern-transport-master`: replaced "equivalent" with the true split (lifting is
    an iff, instantiation is one-directional) and made the proof sketch match.
12. `family:pattern-transport-iota`: restricted the "all four" claim to `Realizes`, named
    `family:pattern-transport-master` for the lifting/instantiation halves, and added the
    `m1` level hypothesis of `apply_levelWF`. Added `fam:subst-basic` to `\uses`.
13. `def:ind-mentions-const`: noted that the `Decidable`-instance placement is stated and
    defended in the test file's header.
14. `family:indlem-stage-ordered`: "each constant stage is three lines" → "one to three
    lines each".
15. `def:indparams-defeqs-as-pats`: 25 → 27 lines with a `\srcloc`, and added that two
    thirds of the docstring is `trproj`-only and genuinely absent from `iota`.
16. `thm:indparams-cr-defeq-of-induct`: added `def:crdefeq` to `\uses`.
17. Review notes: corrected `Add.lean:161` → `:159` (with the actual test quoted),
    `Add.lean:173` → `:189` (`checkPositivity.loop`), added `Add.lean:275` and `:271` for
    the `isLargeEliminator` clauses; corrected the `Matches.uniq`/`matches_determ`
    redundancy bullet (the branches did **not** edit them — 493 insertions, no deletions);
    added a new "Low, undocumented limitations" bullet for the `universes` bundling and
    `VRecursor.all`.

No genuine criticism was softened; the `high`/`medium` bullets are unchanged in severity.
