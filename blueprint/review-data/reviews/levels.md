# Review of chapter levels

## Quality verdict

This chapter has no contributed nodes: a `git diff master trproj` (and `master iota`) on all
four covered files (`Verify/Level.lean`, `Verify/NormLt.lean`, `Verify/QSort.lean`,
`Verify/EquivManager.lean`) is empty, confirming the chapter's own "0 lines in each of the four
files" claim; the `iota`/`trproj` log entries that touch these paths are content-free merge
commits. Everything in the chapter is therefore a review of upstream (Mario Carneiro's, plus one
Lean-FRO-vendored) code. Spot-checking upward of 30 nodes against the actual Lean source
(`Verify/Level.lean`, `Verify/NormLt.lean`, `Verify/QSort.lean`, `Verify/EquivManager.lean`,
`Lean4Lean/Level.lean`, `Inductive/Add.lean`, `Tests/Level.lean`) — signatures, hypotheses,
proof tactics named, `\uses` targets, sorry/axiom taint via `decls.tsv` and the chapter-scoped
`enriched/all.json`, and every "Review notes" bullet's cited line — turned up essentially no
misattributions: `\lean` names match the real declarations, statement direction/hypotheses are
faithful (e.g. `NormLevel.le_eval`'s "Theorem 39" framing, the `RelevantEq.uniq` → `TrProj.uniq`
`sorryAx` chain, the exact three `usesSorry=true` nodes in `enriched/all.json` all carrying
`\axfoot`), and every "dead code" / "stale docstring" claim in the review notes reproduces
verbatim from the source. The only defects found were two small, low-severity descriptive
inaccuracies in the chapter overview (a proof-length estimate off by ~20%, and two "phase" line
ranges that silently overlapped), both fixed in place; no incorrect `\uses`, no wrong badge, and
no over/underclaiming of verification status were found.

## Confirmed code issues

(These are issues in the **tex**, found and fixed during this review — not issues in the Lean
code, which this master-only chapter does not attribute to the user's contributions.)

- `blueprint/src/chapters/levels.tex:707` (now fixed), severity low: the proof sketch for
  `thm:lvl-separation` said "About 90 lines, with no automation black boxes"; the actual body of
  `NormLevel.separation` (`Lean4Lean/Verify/Level.lean:2674`-2747) is 74 lines, not ~90. Fixed to
  "About 75 lines".
- `blueprint/src/chapters/levels.tex:22-25` (now fixed), severity low: the overview's "six
  phases" line-range summary listed "completeness and canonicity (2250--3180)" and "a flat fast
  path (2940--3800)" as if sequential, but these ranges overlap (2940--3180 was claimed for both)
  and neither phase is in fact a single contiguous block: canonicity work resumes at
  `Verify/Level.lean:3397` (`Node.subsume_hasSub` through `normalize_complete` at :3721) after the
  flat-path material begins at :2940, and the flat-path material itself concludes only at
  `normalize'_eq` (:3793), past the claimed 3800 boundary check (: 3880 is EOF). Fixed by
  splitting both ranges into their two physically disjoint pieces.

No further inaccuracies were confirmed after checking ~30 nodes (all master, since the chapter
carries no `\contrib` badges) chosen for importance/centrality: `def:lvl-getoffset`,
`fam:lvl-mkdata`, `thm:lvl-oflevel-of-not-hasparam`, `thm:lvl-getundefparam-none`,
`def:lvl-substparams`, `def:lvl-normlevel-eval`, `fam:lvl-eval-le`, `def:lvl-normlevel-wf`,
`thm:lvl-normalizeaux-wf`, `thm:lvl-normalizeaux-eval`, `fam:lvl-subsume-node`,
`thm:lvl-le-eval`, `thm:lvl-eval-congr`, `def:lvl-tree-eval`, `thm:lvl-tree-reify-eval`,
`def:lvl-dom-feas`, `thm:lvl-separation`, `thm:lvl-normalize-complete`, `thm:lvl-isequivlist-wf`,
`def:normlt-size-basecmp`, `def:normlt-normcmp`, `thm:normlt-aux-eq`, `thm:normlt-swo`,
`fam:qsort-perm-extract`, `thm:qsort-sort-spec`, `fam:qsort-partition-spec`,
`ind:eqvmgr-relevanteq`, `fam:eqvmgr-relevanteq-lemmas`, `thm:eqvmgr-relevanteq-uniq`,
`thm:eqvmgr-isdefeqe-trexpr`, `thm:eqvmgr-isdefeqe-uniq`, `thm:eqvmgr-isequiv-wf`,
`thm:eqvmgr-isdefeq-wf`, `fam:eqvmgr-primitives-wf`.

## Refuted claims

None. Every claim checked (statements, hypotheses, proof-sketch lemma names, `\uses` targets,
`\leanok`/`\axfoot` sorry-taint status, review-note bullets, thesis correspondence, and the "0
contributed lines" attribution claim) was confirmed against the Lean source, `decls.tsv`,
`all-constants.tsv`, the chapter-scoped slice of `enriched/all.json`, and `git diff master
trproj`/`master iota` on the four files. In particular:
- The 3 nodes flagged `usesSorry=true` in `enriched/all.json` for this chapter
  (`thm:eqvmgr-relevanteq-uniq`, `thm:eqvmgr-isdefeqe-trexpr`, `thm:eqvmgr-isdefeqe-uniq`) are
  exactly the 3 nodes carrying `\axfoot{sorryAx via Lean4Lean.TrProj.uniq ...}` in the tex, and
  `Lean4Lean/Verify/Typing/Lemmas.lean:992` is indeed `theorem TrProj.uniq ... := sorry`.
- The Tests/Level.lean stale-docstring claim, the LevelStd.lean stale-docstring claim, the
  NormLt.lean header overclaim ("shows it is a strict weak order"), the dead-code claims
  (`RelevantEq.symm`/`.trans`, `M.WF.bind_le`, `mkData_depth`/`_hasParam`/`_hasMVar`), the
  QSort.lean vendoring/copyright/module-system claims, and the `geq'`/`normalize'` unused-in-kernel
  claims were all verified character-for-character or by grep against the whole tree.

## Fixes applied to the tex

- Line 707: corrected the `thm:lvl-separation` proof-sketch line-count estimate from "About 90
  lines" to "About 75 lines" to match the actual 74-line body of `NormLevel.separation`.
- Lines 22-25: corrected the overview's six-phase line-range summary so "completeness and
  canonicity" and "a flat fast path" no longer claim overlapping, contiguous ranges; each is now
  given as two disjoint sub-ranges reflecting that the file physically interleaves the tail of the
  canonicity development with the flat-path material before returning to finish each.
- Re-ran `check_chapter.py blueprint/src/chapters/levels.tex`: 77 nodes, 0 errors, 0 warnings
  (unchanged from before the edit, as expected for prose-only fixes). Re-ran `check_global.py`:
  980 labels, 0 cycles, 0 errors.
