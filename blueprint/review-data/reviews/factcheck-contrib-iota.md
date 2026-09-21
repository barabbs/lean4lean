# Fact-check pass — chapters/contrib-iota.tex

Method: every \srcloc, \ref, \lean-implicit declaration name, and standalone number in the
chapter was checked against the source files under the repository root
(git show/grep/wc -l/diff --stat), against `registry.tsv`/`decls.tsv`/`decls-attrib.tsv`, and
against the understand/ reports named in the task (`claims-iota.md`, `contrib-iota.md`,
`thesis-map.md`, `hygiene-review.md`, `unused-contrib.md`, `sorry-grep.md`, `census.md`,
`upstream-comparison.md`, `reviews/*.md`). `check_chapter.py` and `check_global.py` were run
before and after edits (0 errors/0 warnings both times; this chapter defines no graph nodes so
the node-level checks are vacuous — the load-bearing checks here were the manual srcloc/ref/
number audit).

## Corrections

1. **Sorry ledger miscount ("Sorry and axiom impact" and "Assessment").** The chapter said
   master had "Three master `sorry` *definitions*" that the branch closed, but only names two
   (`structure:ind-wf` = `VInductDecl.WF`, `def:ind-add-induct` = `VEnv.addInduct`) plus one
   *proof* (`thm:indlem-add-induct-wf` = `addInduct_WF`). Verified: `git show
   master:Lean4Lean/Theory/Inductive.lean` is exactly the two `:= sorry` definitions (7 lines);
   `InductiveLemmas.lean` on master is a 10-line file with one `:= sorry` proof. The "three
   definitions" figure is the cross-branch total from `census-partial.md`/`sorry-grep.md`
   (`VInductDecl.WF`, `VEnv.addInduct` on iota + `TrProj` on **trproj**) misapplied to iota
   alone. Fixed both occurrences to "Two master `sorry` definitions and one `sorry` proof".
2. **`family:pattern-iota-counts` declaration count.** Chapter said "seven declarations"; the
   node's own `lean` list (enriched/all.json) and a direct read of
   `Theory/Typing/Pattern.lean:499-680` show eight (`RHS.spine`, `spine_foldl_var`,
   `RHS.iotaCounts`, `iotaPaths_countP_isLeft`, `iotaPaths_countP_isRight`, `iotaRHS'_spine`,
   `iotaRHS'_iotaCounts`, `iotaRHS_iotaCounts`). `hygiene-review.md` itself mislabels this as
   "7-declaration" while listing 8 names; recomputed and fixed to "eight declarations".
3. **`toParams`/`inductParams`/`crDefEq_of_induct` grep count (claim 25).** Chapter said "all 14
   occurrences"; `contrib-iota.md` claim 25 said 14, but re-running
   `grep -rn 'toParams\|inductParams\|crDefEq_of_induct' Lean4Lean` today gives **13** hits, all
   inside `InductiveParams.lean` (the "no consumer in the library" half of the claim is
   unaffected). `claims-iota.md`'s own claim 25 does not restate the count. Fixed to "13".
4. **`lake build` module/olean conflation (claim 7).** Chapter said "120 modules have oleans";
   `claims-iota.md` claim 7 says 117 `.lean` modules each have an olean, for 120 oleans total
   (`find Lean4Lean -name '*.lean' | wc -l` = 117, confirmed). Fixed to "all 117 modules have
   oleans (120 total, under `.lake/build/lib/lean/`)".
5. **"≥97% iota by declaration count" for InductiveParams.lean/InductiveLemmas.lean.** Recomputed
   from `unused-contrib.md` §4's own per-file table: `InductiveLemmas.lean` is 70/73 = 96% iota,
   `InductiveParams.lean` is 22/25 = 88% iota — neither is ≥97%, and they differ enough that a
   single shared floor is misleading. (Cross-checked independently via `decls-attrib.tsv`
   attribution counts and via blame-line I/P ratios; both confirm InductiveParams.lean is well
   under 97% under any of the three metrics.) Replaced with the two actual percentages and their
   numerator/denominator.
6. **M5 milestone date range ("2026-09-08/09, 10 commits").** `git log master..iota` shows
   exactly 10 commits dated 2026-09-08 (`83fc0af, 4016efa, f53b727, 18805a4, 3046dff, 4307de3,
   30897c0, be30d35, a928c53, 7a68882`) and 2 more dated 2026-09-09 (`3de1dcb, 38ea0de`, already
   handled separately by the chapter as the "sidecar"/duplicated-commit doc pair). The stated
   "10 commits" is correct only for 09-08; sum-check: M1(8) + M2(3) + M3(3) + M4(2) + M5(10) +
   trailing docs(2) = 28, matching the chapter's own total. Fixed the date to "2026-09-08".
7. **Intro's chapter range.** "every technical object ... is a node defined in Chapters
   `\ref{chap:syntax}--\ref{chap:primitives-arith}`" (chapters 2-11) excludes chapter 12
   (`typechecker.tex`), which is where `thm:vtc-iota-reduce-core`
   (`TypeChecker.Inner.inductiveReduceRecCore.WF`, referenced at the end of the "AddInduct
   bookkeeping in Verify" paragraph) actually lives, per `registry.tsv`. Extended the range to
   `\ref{chap:typechecker}` (the other five referenced chapters — syntax, typing, metatheory,
   inductive, kernel, trenv — are all within 2-12).
8. **Unused-declaration census (rule 5).** The "Dead code" paragraph already led with the
   regenerated iota-only figures (565 contributed, 58 zero-reference, 10.3%) and correctly
   flagged the 78/28/19 breakdown and named 31 as "the trustworthy figure" — but it never gave
   the iota-specific share of that 31, which invites conflating the combined 31 with an
   iota-only figure right after quoting an iota-only 58/565/10.3%. Added the iota/trproj split
   (19/12) and the original population (875 = 553 iota + 322 trproj) from
   `reader-summaries.md:261,263`, and one clause stating the regenerated 58/565 is the
   uncorrected count against which 31 (19+12) is the confirmed one.

No other numeric, srcloc, `\ref`, or declaration-name errors were found (see next section for
the scope of what was checked and passed).

## Verified-unchanged summary

- All 62 `\srcloc{file}{line}` pointers in the chapter were opened at the given line and confirm
  the declaration/docstring the sentence is about (tolerance satisfied in every case; most are
  exact).
- All ~60 `\ref{...}` labels resolve in `registry.tsv` (node labels) or as a chapter/section
  `\label` in `blueprint/src/chapters/*.tex` (the four `chap:*` labels and the two `sec:*` labels
  local to this file), and in each case the referenced node/section is the one the sentence
  means (spot-checked against the registry's `lean`/`attribution`/`chapter` columns).
- Every named Lean declaration (`VInductDecl.WF`, `VEnv.addInduct`, `addInduct_WF`, `AddInduct`,
  `Aligned.addInduct`, `TrEnv'.induct`, `IsDefEq.pat`, `PatTyped`, `PatWF`, `toParams`,
  `inductParams`, `crDefEq_of_induct`, `DefEqsAsPats`, `checkEqType`/`checkEqType.WF`,
  `inductiveReduceRecCore`(`.WF`), `RecShape.one_le_numMotives`, `RecShape.majorFormer?_eq`,
  `LargeElim.shape`, `WF'.pats_origin`, the `family:pattern-iota-counts` octet, etc.) exists at
  the stated location.
- The 60-item Claims audit `\item[N (...)]` verdicts were diffed against `claims-iota.md`'s two
  tables item by item: all 60 verdicts (TRUE/FALSE/PARTIAL/UNVERIFIABLE and their qualifiers)
  match; only wording is condensed, no verdict is upgraded, softened, or invented beyond what
  `claims-iota.md` itself states.
- Recomputed independently and confirmed correct: master `Theory/Inductive.lean` = 7 lines,
  current file = 444(trproj)/443(iota); master `InductiveLemmas.lean` = 10 lines;
  `Verify/Environment/Quot.lean` = 615 lines; `VInductDecl.WF` = 20 fields (counted); `git diff
  --stat master..iota` = 45 files/+5628/-331/28 commits; `git diff --stat iota trproj` = 17
  files/+2273/-170, `Verify/Environment/Lemmas.lean` alone 557+102=659; non-Experimental sorry
  counts master 28 hits/23 real, iota 24 hits/21 real (claim 4); `Quot.lean` diff is exactly one
  added line; `grep -rn 'Ordered\.strong' Lean4Lean` empty; `Theory/Typing/Injectivity.lean` has
  exactly 3 sorries; 67 `OrderedStrong` occurrences (65 in the six named files + 2 in
  `Experimental/`) and 64 retyped declaration heads (claim 27); 19/16/6-name sorryAx-reach lists
  for Chapters primitives-core/primitives-arith/trenv, matched verbatim against
  `reviews/primitives-core.md`, `reviews/primitives-arith.md`, `reviews/trenv.md`; the
  `WHNF.lean:17` `inductiveReduceRecCore.WF` blame tag really is `P` despite being iota-attributed
  in the registry (confirms the chapter's own caveat about that node).
- Upstream section cross-checked line by line against `upstream-comparison.md` §1, §2f, §3, §5:
  PR #43 metadata, the "16 days of silence" arithmetic (2026-08-29 to 2026-09-14), the bot-review
  timing, the CI `action_required` sequence starting at `eddf009`, the "three weeks" maintainer
  quote (upstream-comparison.md uses that phrasing itself), the `AddsConsts` handshake claim, and
  PR #32's "four weeks"/"+24247/-1264" figures and the three-interface-change list (`VEnv` arity,
  `AddInduct` arity, `VEnv`/`Pattern` import order — correctly limited to iota's own three, since
  the fourth interface change in `upstream-comparison.md` §2f, `TrProj`'s arity, is trproj's).
- The `\S` citations used against `thesis-map.md` (§3(a), §5) and against the internal numbering
  of `axioms.tex` (§2, §2.6, §2.6.1-4) were checked against `thesis-map.md`'s own numbering note
  and its quoted thesis text; all match, including the three stated ι-rule caveats and the
  K-like/subsingleton double divergence.
- `Aligned.addInduct := nomatch H` on master was independently verified in
  `Verify/Environment/Lemmas.lean:66-68` — initially looked like a possible mix-up with
  `AddInduct.to_addInduct` (also `nomatch H`, in `Basic.lean`), but both are in fact proved by
  `nomatch` on master since `AddInduct` is an empty inductive; no error.

## Unresolved doubts

- The "primitives-core"/"primitives-arith" file lists for the 67 `OrderedStrong` occurrences omit
  the "+2 in Experimental/" detail that `claims-iota.md` claim 27 itself carries (the total 67 is
  still correct only including those two). Left as is since the total number is right and the
  sentence doesn't claim the listed files are exhaustive.
- Item 21's design-section list of "derived theorems" (`env_eq, le, wf, find?_mono, value_find,
  rec_find, rec_reg, ctor_find`, 8 names) versus claim 21's "seven bookkeeping theorems" (which
  excludes `le`) is internally consistent with `claims-iota.md`'s own claim 21 text, but a reader
  skimming only the Design section could plausibly miscount; not changed since neither sentence
  states an incorrect number on its own.
- Could not independently re-run `lake build` (forbidden by the task) to confirm claim 7's "120
  oleans" figure currently; a quick `find .lake/build/lib/lean -iname '*.olean' | grep -i
  lean4lean | wc -l` in this session returned 121, one more than `claims-iota.md`'s recorded 120.
  Kept `claims-iota.md`'s traceable figure (120) rather than substituting my own possibly
  environment-dependent recount, since the specific error being fixed was the module/olean
  conflation, not the olean count itself.
