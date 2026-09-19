# Fact-check: chapters/contrib-trproj.tex

Method: read CONVENTIONS.md and the chapter line by line against `understand/contrib-trproj.md`,
`understand/claims-trproj.md`, `understand/thesis-map.md`, `understand/hygiene-review.md`,
`understand/unused-contrib.md`, `understand/upstream-comparison.md`, `understand/reviews/trenv.md`,
`registry.tsv`, `decls.tsv`, `blame/*.txt`, and direct `git`/`grep` commands against the `trproj`
checkout at `20ec229`. `check_chapter.py` and `check_global.py` both pass (0 errors, 0 warnings)
after the edits below.

## Corrections

1. **Footprint number wrongly attributed (Goal and scope).** The chapter said the total
   `master..trproj` footprint is "49 files and +7762/-363 (understand/contrib-trproj.md, header
   table)". `contrib-trproj.md`'s header table actually says **50 files, +7763/-363** (confirmed
   by `git diff master..trproj --stat`, which includes the root `divergences.md` the branch also
   touches). The 49/+7762/-363 figure belongs to `hygiene-review.md`/`upstream-comparison.md`,
   whose scope is explicitly `-- Lean4Lean Main.lean` (confirmed those two files still cite
   49/+7762/-363 correctly elsewhere in the chapter, since they excludes `divergences.md`). Fixed
   the header-table citation to 50/+7763/-363; left the two hygiene-review.md/upstream-comparison.md
   citations (49/+7762/-363) alone since they are correct for their own cited source.

2. **d7ec0fa churn figure was mislabeled.** "$-405/+\dots$ lines, net $-203$" mirrored an
   ambiguity already in `contrib-trproj.md`, but `git show --numstat d7ec0fa -- Theory/Proj.lean`
   gives `101 304` (i.e. +101/-304), so 405 is the *combined churn* (101+304), not a directional
   "-405" figure. `claims-trproj.md` #21 makes exactly this correction against
   `contrib-trproj.json`. Reworded to "+101/-304 lines in the file, 405 lines of combined churn,
   net -203" so the numbers are unambiguous and independently checkable.

3. **`proj_defeq` consumer-grep line count.** The chapter said the six-line
   `grep -rn proj_defeq` result included "the theorem's own signature and docstring (srcloc{...}
   {1021} and the line above it)" — i.e. two matching lines from `Lemmas.lean`. Re-ran the grep:
   only line 1021 (the `theorem` line) matches in that file; the 8-line doc-comment above it
   (1013-1020) describes the theorem in prose without repeating its name, so it does not match.
   The six-line total is correct (1021 + Expr.lean:96,115 + ProjInhabit.lean:582,587,595 = 6);
   only the "and the line above it" clause was wrong. Fixed to say the doc-comment above never
   repeats the name.

4. **M4 commit count.** The chapter said M4 is "eight commits answering named findings" and then
   individually named six of them. `git log --oneline --no-merges` over the 2026-09-08 date range
   for this range (`2a901f4`..`6fd8a1d`) returns **eleven** commits, matching
   `contrib-trproj.json`'s own summary ("eight of the eleven commits answering named
   REVIEW_2026-09-07 findings") — `contrib-trproj.md`'s prose narrative had dropped the "of the
   eleven" and just said "Eight commits", which the chapter inherited verbatim. Fixed to "eleven
   commits, eight of them answering named findings, six of which are worth naming individually".

5. **Unused-declaration census (task rule 5).** The chapter presented the *regenerated*
   unused-contrib.md figures (78/889, 8.8%; 10.3% iota, 6.2% trproj) as the headline number, with
   no mention of the original manually-verified run, and its trproj-specific example list named
   "two never-projected `TrRecursor` fields" as trproj's — but `TrRecursor.all`/`TrRecursor.k`
   (`Verify/Environment/Basic.lean:240,245`) are blame-tagged `I` (iota), not `P` (trproj); they
   are `trenv.md`'s finding about *iota*'s `TrRecursor`, not trproj's. Rewrote the bullet to:
   - lead with the confirmed **31** zero-reference declarations out of 875 (19 iota, 12 trproj,
     3.5%), matching the task's authoritative figures and unused-contrib.md's own "Recovery note"
     (which says the 31 original findings "all reproduce unchanged in this run");
   - mention the regenerated 78/889 only with the caveat that it is inflated by 28 spurious
     `instance`-labeled-as-`def` hits and 19 entries never individually re-verified (both stated in
     unused-contrib.md's own recovery note);
   - replace the misattributed `TrRecursor` item with a cross-checked list of genuinely
     trproj-attributed, non-spurious, non-"new" dead declarations, derived by taking the current
     20-item trproj list in unused-contrib.md §2 and subtracting the 5 spurious `ShapeDecide.lean`
     instances and the 3 "new" entries (`Plain.env0?`, `Dependent.env0?`, `Tests.ProjShape.Refl`) —
     this reproduces exactly 12 items, cross-validating the task's "12 trproj" figure independently
     of the task statement. The surviving list: `trProj0`/`trProjDep1` (unread witness theorems),
     `V3.h`/`Refl.next` (unprojected test fixture fields), `projMotiveBody_zero`/`instFields_nil`
     (`@[simp]`, never invoked explicitly), and the two open unreferenced `sorry`s
     `VEnv.IsDefEq.crDefEq_of_induct` and `inferProj.WF_struct`.
   - kept `VExpr.projTy` but clarified it is not on the dead list (it is `unused-contrib.md` §3's
     "used only from Tests", not a zero-reference entry).

6. **Contributed-declaration length range.** "5.6--7.3 code lines per declaration against master's
   8.5--12.0" dropped the largest of the three cited "contributed" values.
   `hygiene-review.md` (d) gives Theory 7.5 (I) / 5.6 (P) vs 8.5, and Verify 7.3 (I) vs 12.0; the
   contributed-side values actually cited are 7.5, 5.6 and 7.3, so the upper bound of the range is
   7.5, not 7.3. Fixed to "5.6--7.5".

## Verified-unchanged summary

Extensively cross-checked and found correct (no edits needed):
- The four trproj `sorry`s and their exact locations: `Verify/Typing/Lemmas.lean:747,995` and
  `Verify/TypeChecker/InferType.lean:398,410`; `Verify/Environment/Lemmas.lean` has none
  (`grep -n -w sorry` empty) — matches a fresh `grep -n "\bsorry\b"` of the working tree exactly.
- `TrEnv.proj_defeq` has **zero** in-library consumers: `grep -rn proj_defeq --include="*.lean"
  Lean4Lean` returns exactly the six lines the chapter describes (its own definition, two
  `TrProjCtor` docstring mentions, three `#guard_msgs`/axiom-profile lines in
  `Tests/ProjInhabit.lean`). No theorem anywhere calls it for its conclusion.
- `Lean4Lean/Inductive/Reduce.lean` kernel refactor: `git diff master..trproj` (34 lines,
  +21/-13) confirms `inductiveReduceRecCore` is byte-for-byte the extracted original body with
  `majorIdx` (a removed local) replaced by `rval.getMajorIdx` at the one site that used it — an
  exact match to the chapter's description. `git diff iota..trproj` on this file is empty
  (iota independently carries the identical content via `7a68882`, matching `6fd8a1d` on trproj
  — confirmed same patch content, and the two commits' shared subject line is one of the two
  duplicated-subject pairs the chapter cites).
- Claims-audit summary (50 claims: 28 TRUE / 12 PARTIAL / 8 FALSE / 2 UNVERIFIABLE) and every
  individual verdict cited in the chapter's description-list (TRPROJ_CONTRIBUTION.md FALSE items,
  "every lemma was sorry" PARTIAL, "no new trust" PARTIAL, DELIVERED PARTIAL, B1-B4 FALSE) match
  `claims-trproj.md` verbatim, including the specific claim numbers.
- Thesis citations: `typesys.tex` §3.1 (`inv_x`), `Wtypes.tex` §5.1 (`π₂ p : β[π₁ p/x]`, and the
  η rule `(π₁ x, π₂ x) ≡ x` with its "modest strengthening" and "omitted the recursors in favour
  of projections for Σ and ulift" justification, at Wtypes.tex:91-92), `axioms.tex` §2.6.3 (fresh
  motive universe), and `unique.tex:109` (the `inv_i` generalisation, quoted verbatim) all verified
  directly against `../lean-type-theory/*.tex`. The "§5 W-types — nothing" table row and the eight
  W-type primitives are verified against `thesis-map.md`'s own table and prose.
- Commit-history facts: 24 commits `iota..trproj` (2026-08-26 to 2026-09-10); 52 commits ahead of
  master, 24 ahead of iota; `git merge-base --is-ancestor master trproj` succeeds; M1-M5 commit
  hashes and dates (`f252c3c`..`b6a5a38`, `7f62db2`, `fc9fbfc`..`f7dabf1`, `2a901f4`..`6fd8a1d`,
  `20ec229`) all match `git log` exactly; the `20ec229` merge changes exactly 1 line; commit
  subjects for `811a52a`, `7a5e96d`, `b6a5a38`, `7f62db2` match verbatim; `Theory/Pattern.lean`
  was created then deleted (`cb920e1`/`3bbdb22`) and does not exist at the tip; `655dd3f`/`75ffde9`
  share a patch-id, `7a68882`/`6fd8a1d` share a subject line.
- Churn numbers: `Verify/Environment/Lemmas.lean` 22 non-merge commits, +1734/-678;
  `Theory/Typing/InductiveParams.lean` 14 commits (with `--follow`, since the file was relocated
  and reverted in `cb920e1`/`3bbdb22`), +1039/-576 — both reproduced exactly via `git log --follow`.
- Sorry/axiom-cone numbers: master 23 / iota 21 / trproj 16 non-Experimental sorries; projection
  side 9 (master) -> 4 (trproj) sorries; 663 `Lean4Lean.*` declarations mention `TrExprS`/`TrExpr`/
  `TrProj`/`TrProjCtor` in their type, of which 614 are sorryAx-free; no new axiom/opaque
  declaration and no `native_decide` anywhere in `git diff master..trproj`.
- All `\ref{}` labels checked against `registry.tsv` exist and are in the chapters the chapter
  implies (`trenv`, `trexpr`, `proj`, `typechecker`, `inductive`); all `\srcloc{}` locations
  checked point at the declaration or text described, within tolerance.
- `TrProjCtor`'s eight fields (`pat`, `params_length`, `ctor`, `field_lt`, `minor_arity`,
  `major_ty`, `fn_ty`, `eq`) and their line range (90-131) verified directly against
  `Verify/Typing/Expr.lean`.
- Blame-derived counts: 2645 `P` / 5131 `I` / 22726 `M` lines total; `Theory/Proj.lean` (449),
  `Tests/ProjShape.lean` (185), `Tests/ProjInhabit.lean` (597) all 100% `P`; the 15-line
  contribution to `Tests/ShapeDecide.lean` (11) and `Tests/IotaShape.lean` (4) confirmed via blame.
- Tactic-density numbers (`omega` 2.0% vs master 0.4%; `decide` 1.1% vs master 0.2%) and the
  documentation-volume numbers (25.3% vs 1.7% comment lines; 56-line module header;
  27-line docstring on 5-line `DefEqsAsPats` at `InductiveParams.lean:351`, confirmed iota-blame)
  match `hygiene-review.md` exactly.

## Unresolved doubts

- The chapter's "(master, \srcloc{Lean4Lean/Verify/Typing/Expr.lean}{68})" citation for the old
  `def TrProj := sorry` points, at the current trproj HEAD the web build resolves `\srcloc` against,
  at unrelated content (the tail of `VLCtx.WF.fvwf` / start of the `TrProjCtor` docstring) rather
  than the quoted master definition. The line number is correct *for master* (verified against
  `git show master:...:68`), and the sentence explicitly labels it "(master, ...)", but
  `\srcloc`'s web-build link target is HEAD-only per CONVENTIONS.md, so a reader following the link
  would not land on the quoted text. This is a structural property of citing removed master-only
  code with the `\srcloc` macro as defined, not a numbers/attribution error introduced by the
  chapter, so I left it as is; flagging it in case the convention should eventually support a
  ref-qualified `\srcloc` for this recurring "master had X, here's where" pattern.
- Did not independently re-derive the original (pre-regeneration) 31-item unused-declaration list
  in full; unused-contrib.md's own recovery note states the original run's raw output was lost to
  a `/tmp` wipe. I cross-validated the "12 trproj" and "19 iota" split by subtracting the
  documented spurious/new entries from the current regenerated list and got exactly 12 for trproj,
  which matches the task's given figure, but I did not attempt the equivalent reconstruction for
  the iota side (19) since that branch's chapter is out of scope here.
