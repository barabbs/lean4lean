# Review of chapter kernel

## Quality verdict

The two contributions in this chapter's scope are minimal, well-motivated, and exactly as
advertised: 22 of 4040 lines changed, both diffed against master and confirmed byte-for-byte.
`iota`'s change (`Lean4Lean/Quot.lean:24`, one line: `if info.isUnsafe then fail ...`) rejects an
`unsafe Eq` during quotient initialization; `git show 30897c0` confirms the commit message matches
the chapter's technical claims exactly, including that it let `addQuot.WF`/`addDecl.WF` drop the
`Environment.EqSafe` hypothesis entirely (verified: neither theorem's signature carries it).
`trproj`'s change (`Lean4Lean/Inductive/Reduce.lean:75-90,115`, 21 lines) extracts the pure ι step
of `inductiveReduceRec` into `inductiveReduceRecCore`; `git show 6fd8a1d` shows the extracted body
is master's verbatim save for one systematic substitution (the caller's bound `majorIdx` becomes
`rval.getMajorIdx`, the same value, at the two sites that used it), exactly as the chapter claims.
Both changes are proof-driven rather than stylistic, both are recorded in commit messages and
`divergences.md`, and both come with an honest scoping statement about what remains open
(`reduceRecursor.WF`, the K-like/structure-η preludes). This is careful, well-documented,
minimal-footprint work, not slop — and it is accurately and precisely described by the chapter's
`\contrib` nodes, which is itself notable given how much of this chapter's *other* content (see
below) needed correction.

## Confirmed code issues

- `Lean4Lean/Verify/Environment.lean:208` — MEDIUM — `addDecl.WF`'s `inductDecl` case is a literal
  `sorry` (confirmed by reading the source; `decls.tsv` marks it `usesSorry`). This is master's
  gap, correctly attributed as such by the chapter, but it is the largest single hole reachable
  from this chapter's central function and it is what keeps everything the `iota` branch proves
  about inductive blocks on the model side of the fence.
- `divergences.md:17` vs `divergences.md:19` — LOW (project documentation, not the blueprint) —
  internal inconsistency: entry 17 states plainly that lean4lean does **not** recheck the
  constructor/recursor declarations restored after nested-inductive elimination (only the
  `aux2nested` nested-application terms get `checkType`, per leanprover/lean4#14621). Entry 19
  instead asserts that "the restored constructor and recursor types are re-checked in the final
  environment ([#14621]), which lean4lean retains." Reading `Environment.addInductive`
  (`Lean4Lean/Inductive/Add.lean:733-777`) confirms entry 17 and the code: the restored
  declarations are inserted with a bare `.add`, with no further `checkType`/`isDefEq` call on the
  restored types, ctor names, or rule right-hand sides. Entry 19's parenthetical looks like a
  leftover error from an earlier edit of `divergences.md`. Not a blueprint issue (the chapter's own
  review note about this correctly says lean4lean "skips" the recheck), but worth flagging upstream
  since it is confusing for the next reader of `divergences.md`.
- `Lean4Lean/Inductive/Add.lean:453,470` — LOW — `AddInductive.run` computes its `isUnsafe` binding
  twice (identically), the second silently shadowing the first. Already flagged in the chapter,
  but at the wrong line (469 instead of 470); fixed.
- `Lean4Lean/ForEachExprV.lean` / `Lean4Lean/TypeChecker.lean` (`etaExpand`) — LOW — both are dead
  code with no call site anywhere under `Lean4Lean/` (confirmed by repo-wide grep); already
  correctly flagged in the chapter.
- `Lean4Lean/FuelConfig.lean:12` — LOW — the docstring's claim "Defaults are set so mathlib passes"
  has zero supporting evidence anywhere in the repository (a full-repo grep for "mathlib" outside
  `blueprint/`/`.blueprint-work/` returns nothing: no CI job, no test, no benchmark). Already
  correctly flagged in the chapter.
- `Main.lean:33` — LOW — `FuelConfig.toObj` calls `panic!` if the derived JSON encoding is not an
  object, inside a command-line argument parser; unreachable in practice but a poor failure mode.
  Already correctly flagged in the chapter, which also correctly caught that an earlier node-map
  pass had the wrong names for `toObj`/`fieldNames` (`toJsonObj`/`fields` in
  `.blueprint-work/understand/kernel-impl.json:1240`).

## Refuted claims

- **(Significant)** Definition `def:kernel-level-normalize`'s review note claimed: "Substantial new
  algorithmic content with no correctness statement anywhere in the repository: nothing proves
  `normalize u = normalize v ↔ u ≡ v`." This is false. `Lean4Lean/Verify/Level.lean` (3880 lines,
  covered by Chapter `levels`/`chap:levels`) proves exactly this, sorry-free:
  `Lean.Level.Normalize.normalize_complete : normalize u == normalize v ↔ u' ≈ v'` (line 3721) and
  `Lean.Level.isEquiv'_complete : isEquiv' u v ↔ u' ≈ v'` (line 3861), both with `usesSorry=false`
  in `decls.tsv`. The claim that unsoundness "would require normalize to identify genuinely
  inequivalent levels" is exactly what is ruled out by these theorems, which the chapter's author
  apparently did not check (Chapter `levels`, in the very same blueprint, documents this proof in
  detail). Fixed: the review note now correctly attributes the correctness result to Chapter
  `levels`.
- **(Significant, same root cause)** Definition `def:kernel-level-le`'s review note claimed the
  "Theorem 39 of the paper" citation "cannot be checked from the source" because the paper is
  "absent from the repository's bibliography." Two problems: (1) the paper (Yoan Géran, "A
  Canonical Form for Universe Levels in Impredicative Type Theory") is in fact named with a working
  URL earlier in the very same file (`Lean4Lean/Level.lean:27`); (2) more importantly, the claim is
  not resting on the citation at all — `NormLevel.le` is independently reproved correct in Lean,
  sorry-free, as `NormLevel.le_complete` and `geq'_complete` in Chapter `levels`. Fixed.
- Definition `def:kernel-addinductive-run`'s review note and the matching Review-notes bullet cited
  the second (shadowing) `isUnsafe` binding in `AddInductive.run` at `Lean4Lean/Inductive/Add.lean:469`;
  the actual line is 470 (469 is `let lctx ← getLCtx`). Fixed in both places.
- The Review-notes bullet duplicating the `Lean4Lean/Level.lean:160`/`:174` claims (no correctness
  statement; bibliography absence) repeated both errors above, plus added a third: "the soundness
  argument is the informal one in the `isEquiv'` docstring plus `divergences.md`" — also false, for
  the same reason. Since correcting it leaves no actual issue to report, the bullet was deleted
  rather than rewritten as a non-issue.

Everything else checked did **not** turn up an inaccuracy. This included exact verification (byte
comparison against source, line numbers, docstrings, commit messages, or `decls.tsv`/blame data)
of: the file list and 4040-line total in the overview; the "22 contributed lines" headline claim
(21 P-lines in `Reduce.lean` + 1 I-line in `Quot.lean`, confirmed against
`.blueprint-work/blame/`); `checkEqType`/`addQuot`/`quotReduceRec`; `inductiveReduceRecCore`/
`inductiveReduceRec` and the git diff of the split commit; the `TypeChecker.M`/`Methods.withFuel`
structures; `reduceRecursor`/`reduceProj`/`unfoldDefinition`/`reduceNat`/`whnf'`/`isDefEqCore'` and
their `\uses` edges; the two `ptrEq*` axioms and their exactly-two call sites
(`Verify/EquivManager.lean:264`, `Verify/TypeChecker/IsDefEq.lean:384`); `inferProj`'s hypotheses
(dependent-field vs. result proposition checks); the `AddInductive`/`ElimNestedInductive` pipeline
(`checkInductiveTypes`, `checkPositivity`, `checkConstructors`, `isLargeEliminator`, `isKTarget`,
`mkRecInfos`/`mkRecRules`); `Primitive.checkDef`/`checkInductive` and the `run_meta` self-test;
`family:kernel-add-decls`/`addDecl`'s dispatch and the ordering-invariant comment at
`Environment.lean:53`; the replay driver and `Main.lean`'s CLI; and every `\axfoot`/`\leanok`
assignment across all 70 nodes (cross-checked programmatically against
`.blueprint-work/understand/enriched/all.json`: no node in this chapter has `direct_sorry` or
`usesSorry` true, so every `\leanok` is correct and no `\axfoot` is missing).

## Fixes applied to the tex

- `def:kernel-level-normalize`: replaced the false "no correctness statement anywhere" review note
  with an accurate cross-reference to Chapter `levels`'s `normalize_complete`/`isEquiv'_complete`.
- `def:kernel-level-le`: replaced the misleading "paper absent from the repository's bibliography"
  review note with an accurate one (paper is named with a URL at `Level.lean:27`; the claim is
  independently reproved in Lean by `NormLevel.le_complete`/`geq'_complete` in Chapter `levels`).
- `def:kernel-addinductive-run`: corrected the second `isUnsafe`-binding line reference from 469 to
  470 (in the node's review note).
- Final Review-notes section: corrected the same 469→470 line reference; deleted the bullet
  repeating the two false Level.lean claims (now that they are corrected, there is no remaining
  issue to list there).
- Re-ran `check_chapter.py` (70 nodes, 0 errors, 0 warnings) and `check_global.py` (980 labels,
  2865 uses edges, 0 cycles, 0 errors) after every edit; ran `rebuild_registry.py` afterwards.
