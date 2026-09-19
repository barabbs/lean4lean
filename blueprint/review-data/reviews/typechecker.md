# Review of chapter typechecker

Adversarial faithfulness review of `blueprint/src/chapters/typechecker.tex` ("Soundness of the
type checker"). All three `\contrib`-badged nodes (`thm:vtc-iota-reduce-core` [iota],
`thm:vtc-inferproj-struct` [trproj], `thm:vtc-inferproj` [mixed]) were checked against
`Lean4Lean/Verify/TypeChecker/{Basic,Reduce,WHNF,InferType,IsDefEq}.lean` and
`Lean4Lean/Verify/TypeChecker.lean`, plus 20 master nodes chosen for importance (the `MLCtx`/
`VContext`/`VState.WF`/`M.WF`/`Methods.WF`/`RecM.WF` core, `withLocalDecl`, `unfoldDefinition`,
`whnfCore`/`whnf`, the `inferLambda`/`inferForall`/`inferApp`/`inferLet` group, `inferType'`,
`isDefEqCore`, `withFuel`, `toplevel`, and the three other open `sorry`s `reduceProjCore`,
`tryEtaStruct`, `isDefEqUnitLike`). Declaration existence, line counts (file sizes, the 2883/
2720/163 line-count triple, the 129/22-line contribution split) and attribution badges were all
cross-checked against `decls.tsv`, `all-constants.tsv`, `registry.tsv`, the per-file blame
listings in `.blueprint-work/blame/`, and `census-partial.md` §7.1's BFS dependency-path table;
one axiom-footprint claim was additionally checked by running a full transitive-dependency
closure over the compiled environment via the Lean LSP (`lean_run_code`), and two lemma
resolutions were checked with `lean_hover_info`. `check_chapter.py` and `check_global.py` both
report 0 errors/0 warnings after the fixes below.

## Quality verdict

The `iota` contribution in this chapter (`inductiveReduceRecCore.WF`, `WHNF.lean:17`-145, 129
lines) is genuinely good work: a complete, `sorry`-free-in-its-own-script proof of a fiddly
index-arithmetic argument (slicing two application spines and matching them against the pattern
machinery), with an accurate docstring about its own saturation caveat. Its weakness is not the
proof but its integration: it has no consumer anywhere in the repository (`reduceRecursor.WF`,
the lemma it was written to feed, is still `sorry`), and its major-premise hypothesis is
strictly stronger than what the kernel's real call site supplies, so as it stands it proves a
fact about a syntactic redex rather than about a step the kernel actually takes. The `trproj`
contribution here (`InferType.lean:392`-410, 22 lines) is not a proof at all: it repairs a
genuinely broken master signature (`inferProj.WF` previously asserted, via an unrelated
auto-bound implicit, that a *projection* translates to the translation of its own *subterm*)
and adds an honest, technically substantive docstring explaining why the general statement is
not provable without extending the model. That diagnosis is correct and valuable, but both
declarations it touches remain `sorry`, the new struct-scoped lemma (`inferProj.WF_struct`) has
zero dependents, and the gap it documents sits directly on the import path of the project's
headline soundness theorem (`inferType'.WF` / `checkType.WF`). Neither contribution changes
what is actually verified end to end in this file group; both are, respectively, a well-proved
but disconnected lemma and a well-documented but still-open hole.

## Confirmed code issues

- `Lean4Lean/Verify/TypeChecker/InferType.lean:407` — high. `inferProj.WF`'s own docstring
  states the lemma is not provable as stated (kernel-accepted projections of reflexive, indexed
  or nested single-constructor types have no `TrExprS` derivation at all), yet
  `inferType'.WF`/`checkType.WF` consume it with no hypothesis that their input is translatable,
  so an admitted-false lemma sits on the headline soundness theorem's import path.
- `Lean4Lean/Verify/TypeChecker/WHNF.lean:147` — medium. `reduceRecursor.WF` is `sorry` and is
  the only intended consumer of the `iota`-contributed `inductiveReduceRecCore.WF`; a
  repository-wide search finds no other reference to the latter, so the contribution is
  currently unreachable from anything else in the project.
- `Lean4Lean/Verify/TypeChecker/InferType.lean:392` — low (dead code). `inferProj.WF_struct` is
  `sorry` and has zero dependents (confirmed via the project's own reachability count in
  `census-partial.md` §7.2); its docstring advertises coverage of `TrProjCtor`, but `TrProjCtor`
  does not occur anywhere in its actual hypotheses.
- `Lean4Lean/Verify/TypeChecker/IsDefEq.lean:211` — low. A commented-out `have` is dead text
  left inside `tryEtaExpansionCore.WF`'s proof (master).
- `Lean4Lean/Verify/TypeChecker.lean:22` — low. `VEnvs.axiom_of_choice` is a deliberately
  misleading name for a three-way case split on `DefinitionSafety`; the docstring says so, but
  the name will still mislead a grep-based audit for appeals to choice.
- `Lean4Lean/TypeChecker.lean:837` (spec: `Lean4Lean/Verify/TypeChecker/IsDefEq.lean:486`) —
  documentation accuracy. `isDefEqUnitLike`'s actual "unit-like" test is
  `ctorInfo { numFields := 0, .. }` on a non-recursive, non-indexed, single-constructor type,
  i.e. the constructor must have *zero fields of any kind*; this is materially narrower than
  "no non-proof fields" (which would permit proof-valued fields), and the blueprint mischaracterized
  it before this pass.

## Refuted claims

- The overview's "Assessment" paragraph and the Review notes' "Context" bullet both asserted
  "Six `sorry`s remain, all master's," while including `thm:vtc-inferproj-struct` (attributed
  `trproj`, and per the file's own blame listing 100% `trproj`-authored — master has no such
  declaration) and `thm:vtc-inferproj` (attributed `mixed`, and per blame its signature and
  conclusion were rewritten by `trproj` over master's `theorem` keyword line) in the list of
  six. This directly contradicted the chapter's own `\contrib` badges and its own Contribution
  summary section. **True:** four of the six `sorry`s are master's outright
  (`reduceProjCore.WF`, `reduceRecursor.WF`, `tryEtaStructCore.WF`, `isDefEqUnitLike.WF`); the
  other two are not master's (`inferProj.WF_struct` is new on `trproj`, `inferProj.WF` is
  mixed).
- A Low review-note bullet on `thm:vtc-iota-reduce-core` claimed its `sorryAx` dependency
  reaches both `TrProj.uniq` and `TrProj.weak'_inv`. **True (checked by computing the full
  transitive constant-dependency closure of `inductiveReduceRecCore.WF` over the compiled
  environment):** it reaches `TrProj.uniq` but does *not* reach `TrProj.weak'_inv`. The `census`
  BFS table (`census-partial.md` §7.1) already only ever reported the `TrProj.uniq` path for
  this declaration; the chapter had added the `weak'_inv` claim without support.
- The same review-note bullet (and the inline `\reviewnote`) cited the commented-out `have` in
  `tryEtaExpansionCore.WF` as being at `IsDefEq.lean:212`. **True:** it is at line 211
  (off-by-one, checked directly against the source both times).
- `thm:vtc-isdefequnitlike`'s statement described the soundness condition as "a unit-like
  structure (one constructor, no non-proof fields)". **True:** the kernel's actual check
  (`Lean4Lean/TypeChecker.lean:837`) requires the constructor to have `numFields = 0`, i.e. no
  fields at all, not merely no *non-proof* fields.
- `thm:vtc-isdefeqcore`'s and `thm:vtc-whnfcore`'s proof `\uses` lists omitted
  `thm:vtc-methods-iface`, even though their Lean proofs directly invoke the `Methods`-bundle
  interface lemmas (`Inner.whnf.WF` in `isDefEqCore'.WF`'s Bool-literal shortcut,
  `Inner.whnfCore.WF` in `whnfCore'.WF`'s beta/recursor/proj/let branches) rather than
  recursing into themselves. **Confirmed by LSP hover resolution** of both call sites to
  `Lean4Lean.TypeChecker.Inner.{whnf,whnfCore}.WF` in `Basic.lean` (the bundle, not the
  primed/self lemma). Both `\uses` lists were missing this dependency.
- `thm:vtc-inferlambda`'s proof sketch stated the domain's type and sort come from "the
  recursive `inferType`" and "`ensureType`". **True (read directly off
  `InferType.lean:95`-169):** the proof calls `checkType.WF` and `ensureSortCore.WF`; there is
  no call to `ensureType` anywhere in `InferType.lean` (`ensureType.WF`/`ensureType.WF'` are
  different, outer `M`-level lemmas defined only in `TypeChecker.lean`). The parallel proofs of
  `thm:vtc-inferforall` and `thm:vtc-inferlet` make the same two calls (`inferType.WF'`/
  `checkType.WF` and `ensureSortCore.WF`) but were also missing `thm:vtc-methods-iface` (and, for
  `inferlet`, `thm:vtc-ensuresortcore`) from their proof `\uses`.
- `thm:vtc-ensuresortcore`'s `\uses{thm:vtc-methods-iface}` was attached to the *statement*, but
  the statement (about `ensureSortCore e e0`'s return shape) never mentions `whnf`; only the
  *proof* calls `whnf.WF`. Per `CONVENTIONS.md` ("uses of the proof go in the proof"), this was
  a placement error, not a content error.

## Fixes applied to the tex

- Rewrote the "Assessment" paragraph (overview) to state that four of the six remaining
  `sorry`s are master's and the other two (`thm:vtc-inferproj-struct`, `thm:vtc-inferproj`) are
  not, naming their real attribution.
- Rewrote the Review notes' "Context" bullet the same way, removing the "all of them master's"
  / "newly added on trproj" self-contradiction.
- Corrected the axiom-footprint review note on `thm:vtc-iota-reduce-core`: removed the
  unsupported `TrProj.weak'_inv` half of the claim and replaced it with the checked negative
  result (does not reach `weak'_inv`).
- Fixed the `IsDefEq.lean` line reference for the commented-out `have` from 212 to 211, in both
  the inline `\reviewnote` on `thm:vtc-tryetaexpansion` and the corresponding Review notes
  bullet.
- Corrected `thm:vtc-isdefequnitlike`'s statement to describe the real condition
  (`numFields = 0`, not "no non-proof fields").
- Added `thm:vtc-methods-iface` to the proof `\uses` of `thm:vtc-isdefeqcore` and
  `thm:vtc-whnfcore`.
- Moved `\uses{thm:vtc-methods-iface}` from the statement to the proof of
  `thm:vtc-ensuresortcore`.
- Fixed `thm:vtc-inferlambda`'s proof sketch to name `checkType.WF`/`ensureSortCore.WF` instead
  of "the recursive `inferType`"/"`ensureType`"; added `thm:vtc-methods-iface` and
  `thm:vtc-ensuresortcore` to its proof `\uses` and tightened its `\axfoot` accordingly.
- Added the missing `thm:vtc-methods-iface` to `thm:vtc-inferforall`'s proof `\uses`.
- Added the missing `thm:vtc-methods-iface` and `thm:vtc-ensuresortcore` to `thm:vtc-inferlet`'s
  proof `\uses`, updated its proof sketch to name `checkType.WF`/`ensureSortCore.WF`, and
  tightened its `\axfoot` accordingly.
- Verified (did not change): all `\lean{}` names, all other `\srcloc{}` anchors, the file-size
  and line-count claims in the overview, the `iota`/`trproj` attribution of every other node,
  and all other Review notes bullets, against the Lean source, `decls.tsv`, and the blame
  listings.
- Re-ran `check_chapter.py` (0 errors, 0 warnings) and `check_global.py` (0 cycles, 0 errors)
  after every edit; ran `rebuild_registry.py` afterward.
