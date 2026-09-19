# Fact-check log — `blueprint/src/chapters/status.tex`

Method: read `CONVENTIONS.md` first. Read every source report the chapter names
(`census.md`, `sorry-grep.md`, `decls.tsv`, `decls-attrib.tsv`, `hygiene-review.md`,
`unused-contrib.md`, `claims-iota.md`, `claims-trproj.md`, `ISSUES.md`, the fourteen
module-chapter narratives and `reviews/*.md`). Cross-checked every number in the chapter
against the source report or a freshly-run command (`wc -l`, `grep -c`/`-n`, `git grep -cP`,
`awk` over `census.md`'s directory table and `decls-attrib.tsv`'s branch column) against the
live repository at HEAD `20ec229`. Extracted the full set of unique `\srcloc{file}{line}`
pairs (225 of them) with a script and dumped ±4 lines of the actual file at each location;
read that whole dump and confirmed every one points at the declaration/text the sentence
names. Confirmed every named Lean declaration against `grep -w` in `Lean4Lean/` or
`decls.tsv`/`all-constants.tsv`. Confirmed every `\ref{label}` resolves in `registry.tsv` or a
chapter `\label{}`, and that the resolved node's `\lean{}`/title matches what the sentence
means (checked all 52 distinct labels this chapter references). Spot-checked verdicts and
quantitative claims in a broad, source-diverse sample of the issue registry (all 15 High
entries; ~35 of 46 Medium; ~30 of 117 Low, including every entry with a specific number
attached) against the named review file, `hygiene-review.md` section, or `claims-*.md` row.
No file outside `blueprint/` and `.blueprint-work/` was modified; no `lake build`/
`leanblueprint`/git-mutating command was run. `check_chapter.py blueprint/src/chapters/status.tex`
and `check_global.py` were run before and after editing: both were already clean
(`status.tex: 0 nodes, 0 errors, 0 warnings`; global `993 labels, 2871 uses edges, 0 cycles, 0
errors`, since this chapter is prose with no graph nodes) and remained clean after every edit.

## Corrections

1. **§"Live sorries outside Experimental", restricted file-diff counts (was 25/27, now
   14/16).** The chapter claimed "restricting to files outside `Experimental/` ... gives 25
   working-tree files against master's 27" — but 25/27 are the *unrestricted* totals (stated
   one sentence earlier); they cannot also be the restricted ones, since 11 `Experimental/`
   files carry `sorry` on both revisions. Recomputed directly: `git grep -cP '\bsorry\b' master
   -- Lean4Lean ':!Lean4Lean/Experimental'` → 16 files; the same command on the working tree
   (no rev) → 14 files. Fixed the sentence to "14 working-tree files against master's 16".

2. **Same section, missing file in the itemized master-vs-working-tree diff.** The bullet list
   (Closed/Reduced/Increased/New file net zero/Unchanged) is meant to be exhaustive over the
   16+14 (master+working) outside-`Experimental/` files, but summed to only 17 of the 18
   distinct files in the union (4 closed + 1 reduced + 1 increased + 1 new-net-zero + 10
   unchanged = 17; master∪working = 16+14−12 common = 18). The missing file is
   `Theory/Typing/EnvLemmas.lean`: it exists on master with **zero** `sorry` matches (so it is
   absent from master's 16-file list) but carries the iota `patsStrong` sorry on the working
   tree (present in the 14-file list) — a live sorry, not a net-zero comment match like
   `ProjInhabit.lean`, so it did not fit any existing bullet. Added a new bullet, "New sorry,
   no prior match", for it. (The prose two paragraphs later already says "1 new sorry
   introduced (`patsStrong`, iota)", so the *summary* was already correct; only the itemized
   per-file list was missing an entry.)

3. **§"Issue registry", High/iota, wrong `\ref`.** "`IsDefEqStrong.pat`
   (`\ref{struct:orderedstrong}`, `Strong.lean:89`) has the correct shape" pointed at
   `struct:orderedstrong`, which is `Lean4Lean.VEnv.OrderedStrong` (a different declaration,
   the environment-hypothesis structure, at `Strong.lean:679`) — not the `pat` constructor of
   `IsDefEqStrong` the sentence is actually about. `registry.tsv` has the correct label for
   this exact node: `inductive:isdefeqstrong-pat`, `\lean{Lean4Lean.VEnv.IsDefEqStrong.pat}`,
   title "Strong ι rule, annotated with the reduct's typing". Fixed the `\ref` in both
   `status.tex` and `ISSUES.md` (the two occurrences kept in sync; the *other* use of
   `\ref{struct:orderedstrong}` two bullets later, about `Strong.lean:679` itself, was already
   correct and untouched).

4. **§"Issue registry", five spurious `unused-contrib.md` citations.** `unused-contrib.md`'s
   own recovery note documents that this pass's regenerated census differs from the original
   manually-verified one (889/78 vs. the confirmed 875/31, per task rule 5); separately, five
   citations in the issue registry named `unused-contrib.md` as a source for a claim that
   report does not contain at all (grepped the report for the declaration name and the exact
   `file:line`, both absent):
   - High/iota, `Verify/Environment/Basic.lean:583` (`VInductDecl.WF` not derived from the
     kernel checker) — cited `unused-contrib.md \#1`; entry \#1 of that report is
     `instDecidableRuleShapeAt`, an unrelated dead-instance finding. The claim itself is fully
     backed by `theory-inductive.md` line 62 (word-for-word), already cited as "inductive
     Review notes"; removed the `unused-contrib.md \#1` tag.
   - Master, `Verify/Environment.lean:208` (`addDecl.WF`'s `inductDecl` case leaves the whole
     `AddInduct` apparatus vacuous) — cited a bare `unused-contrib.md`; that report never
     mentions `addDecl.WF`, `inductDecl`, or "vacuous" (it is a dead-declaration census, not a
     no-producer census). Already independently backed by `hygiene-review.md` §(g) verbatim.
     Removed the tag.
   - Medium, `Verify/Environment/Basic.lean:240` (`TrRecursor.all`/`.k` never used) — cited a
     bare `unused-contrib.md`; not present there (confirmed independently by
     `reviews/trenv.md` and `verify-environment.md`, both already cited as "trenv Review
     notes"). Removed the tag.
   - Low, `Theory/VDecl.lean:51` (`VRecursor.getFirstIndexIdx` unused) — cited a bare
     `unused-contrib.md`; not present there, but independently confirmed by
     `hygiene-review.md` §(a) (already cited) and `reviews/syntax.md`. Removed the tag.
   - Low, `Verify/Expr.lean:745` (`getAppArgsRevList_mkAppList` has no consumer outside its
     file) — cited `unused-contrib.md \#76`, but entry \#76 of that report is about a
     *different* one of the same "three spine lemmas", `getAppFn_mkAppList` (a `@[simp]` lemma
     reachable through simp sets, the opposite finding). The actual claim, about
     `getAppArgsRevList_mkAppList`, is independently and verbatim confirmed by
     `reviews/trexpr.md` (already cited as "trexpr Review notes"). Removed the `\#76` tag.
   Left one similar-looking citation alone: `unused-contrib.md \#67` (`const_mkApps_spine`,
   Low/iota) — entry \#67 does describe exactly this declaration at the right file:line, and
   the claim is independently backed by `theory-syntax.md`; it is one of the report's own
   "19 new, not manually re-verified" entries (a caveat about *confidence*, not a citation
   error), so it was left as is per rule 5 (a specific `\#N` citation to an entry that
   genuinely matches, with the source's own caveat, is not the "present the 31, mention the 78
   with caveat" problem the rule targets — and the chapter states no 889/78/31 headline figure
   anywhere to correct).

5. **§"Issue registry", Low, branch misattribution.** The bullet about
   `Inductive/Reduce.lean:71` (`inductiveReduceRecCore` sitting in a `section` whose
   `variable`s it does not use) was filed under "master (pre-existing)", but
   `blame/Lean4Lean_Inductive_Reduce.lean.txt` tags lines 71–90 `P` (trproj) throughout, and
   `kernel-impl.md`'s own section header for this exact declaration is "`Lean4Lean/
   Inductive/Reduce.lean:71-89` and `:115` — `inductiveReduceRecCore` **(trproj)**" — the
   21-line ι-step extraction is explicitly a trproj contribution (per `hygiene-review.md` §(f)
   and `reviews/kernel.md`), not pre-existing master code. Moved the bullet from the Low/master
   subsection to the Low/trproj subsection (added one clause naming it as "the 21-line ι-step
   extraction trproj carved out of `inductiveReduceRec`" for clarity) in both `status.tex` and
   `ISSUES.md`. The *other* item at the same srcloc family, `Inductive/Reduce.lean:91` (the
   unchanged master docstring of `inductiveReduceRec` describing work now done in the extracted
   `Core` function), genuinely is about master's own unchanged text and was left under "master
   (pre-existing)".

6. **§"Blueprint limitations", claim count (was "roughly 90", now "110").** "`claims-iota.md`
   and `claims-trproj.md` between them adjudicate roughly 90 claims" — both files are exactly,
   sequentially numbered tables (`grep -cE '^\| [0-9]+ \|'`): 60 rows in `claims-iota.md` (IDs
   1–60), 50 in `claims-trproj.md` (IDs 1–50), no gaps or duplicates. 110 is not "rough" for a
   number this cheap to count exactly; fixed to "110 claims (60 iota, 50 trproj)".

## Verified-unchanged summary

Everything else checked came back correct; the highlights, by section:

- **Census** (§"Census"): the directory table (Theory/Verify/Experimental/Tests/kernel decls,
  sorryAx, %, master/iota/trproj-mixed) matches `census.md` §1 cell for cell, including the
  totals row (7833/629/8.0%/6199/549/309/241). The 274+88+77=439/1573=28% (Theory) and
  149+45+151=345/2700=13% (Verify) and 113+173+3=289/418=69% (Tests) derived percentages all
  recompute correctly. The "377 vs. 535" discrepancy claim about `census.md`'s own caption is
  exactly reproducible: `census.md:50` does say "(377 overall)", and summing `decls −
  (master+iota+trproj+mixed)` per directory from the table gives 163+199+99+65+9 = 535.
- **Live sorries**: the "17 listed rows, 1 false positive" claim matches `sorry-grep.md` §1's
  17 rows exactly, and the `ProjInhabit.lean:562` false positive (a doc-comment, not a `sorry`
  term) is independently confirmed by reading the file. The 16-genuine-sorry enumeration
  (11 master, 4 trproj, 1 iota) and every one of its srclocs, attributions and reach numbers
  (343/138/92/61/0) match `sorry-grep.md` §5 and a direct read of every listed file. Master
  sorry totals (131 lines / 27 files) and working-tree totals (125 lines / 25 files, 104 live /
  21 comment) all reproduce with a fresh `git grep`/`grep`. `hygiene-review.md`'s "5 added, 12
  removed" quote is verbatim.
- **Trust boundary**: 110 axioms + 12 opaques project-wide, and every per-cluster count (32 in
  `Verify/Axioms.lean`, 7 `bv_decide` certificates split 4+3 across `Verify/Expr.lean`/
  `Verify/Level.lean`, 2 in `PtrEq.lean`, 1 `Params.extra_pat`, 2×`mySorry`, 3 `DefEq*`, 11 in
  `MoreStepIndexed`/`StepIndexed`) sums to exactly 110 against `census.md` §3, and every
  reach number quoted (229/229/154/152/65/63/14/25/"up to 20") matches `census.md` §5 exactly.
  The `TrEnv.proj_defeq` seven-axiom profile quoted from `Tests/ProjInhabit.lean:586-595`
  matches the file's own `#guard_msgs` block verbatim (order-independent).
- **Issue registry — High (all 15 checked)**: every srcloc, declaration name and reach number
  confirmed by direct file read; every claim independently backed by the named chapter's
  Review notes and/or `reviews/*.md`/`hygiene-review.md`/`claims-*.md` row (spot-checked
  `claims-iota \#17,\#28` and `claims-trproj \#25,\#36` in full — all four verdicts and their
  supporting evidence match the High-severity sentence exactly).
- **Issue registry — Medium/Low (broad sample)**: numeric claims cross-checked against source
  include `Theory/` comment density 25.3% vs. master's 1.7% with the 56-line/27-line
  docstring extremes (`hygiene-review.md` §(c)), the 141-line `WHNF.lean` iota/trproj
  blame-misattribution (corroborated independently in `reader-summaries.md`,
  `verify-typechecker.md`, `contrib-iota.md`, `contrib-trproj.md`), the churn figures
  (net +7762/−363, gross +11439/−3399, ≈27%, 22/14/12/11 commits) and the duplicated-commit
  pairs `655dd3f`/`75ffde9` and `7a68882`/`6fd8a1d` (`hygiene-review.md` §(e)), "16 of the 398
  iota lines [in `Basic.lean`] are relocated master code" (`reviews/trenv.md` explicitly
  corrects an older "roughly 20" to "sixteen"; the chapter already used the corrected number),
  22 `Decidable` instances in `Tests/ShapeDecide.lean` (21 in `namespace VExpr`, counted
  directly), and the ~150-line `run_meta` block in `Tests/IotaShape.lean` (454–607). The
  `.github/workflows/ci.yml:25` claim about `Lean4Lean.Tests` and `defaultTargets` was checked
  against both files directly (`lakefile.toml:2` lists 4 targets, not including `.Tests`; a
  separate `Build Lean4Lean.Tests` CI step exists) and is accurate.
- **All 90 distinct `\ref{}` labels and 225 unique `\srcloc{}{}` pairs** resolve to the right
  node/location; **all `check_chapter.py`/`check_global.py` invariants** (label uniqueness,
  `\lean{}` names present in `all-constants.tsv`/`decls.tsv`, no unescaped underscores, no
  `\uses` cycles) hold before and after editing.

## Unresolved doubts

- Medium severity has no separate "trproj"/"master (pre-existing)" subsubsection the way High
  and Low do; several Medium items under the single `\subsubsection*{iota}` heading are
  individually tagged "(...; master)" in their own citation (all in the Experimental-logrel/
  -reduction clusters, which are genuinely master's own scratch work). Every individual
  citation is internally correct, so no content is misattributed, but the section heading
  itself is a loose "iota and adjacent" label rather than a strict branch partition. Left as
  is: this is a document-structure/heading-naming choice, not a wrong fact, number, srcloc,
  declaration or `\ref`, and restructuring the section would be a much larger edit than the
  fact-checking task asked for.
- `unused-contrib.md \#67` (`const_mkApps_spine`) is cited as a source for a Low/iota entry;
  it is one of the report's own 19 "not manually re-verified, treat as provisional" additions
  (per its recovery note), though the specific finding is independently confirmed by
  `theory-syntax.md`. Not changed (see Correction 4's note), but flagging the provenance here
  in case a future pass wants to swap the citation for the independent source only.
- Did not attempt a from-scratch branch-attribution audit (blame-tag vs. stated branch) of
  every one of the 178 issue-registry entries; only re-verified the ones sampled per the task's
  minimum (all High, ~35/46 Medium, ~30/117 Low) plus a few chosen for cross-file consistency.
  A full audit could in principle surface further misattributions like Correction 5's.
