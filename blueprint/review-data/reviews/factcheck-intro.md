# Fact-check log — `blueprint/src/chapters/intro.tex`

Method: read every source report named in the task (`thesis-map.md`, `contrib-iota.md`,
`contrib-trproj.md`, `claims-iota.md`, `claims-trproj.md`, `hygiene-review.md`,
`unused-contrib.md`, `upstream-comparison.md`, `census.md`, `sorry-grep.md`,
`reviews/finalize-notes.md`); cross-checked every number, `\srcloc`, `\ref`, and named
declaration in `intro.tex` against the live repository at HEAD `20ec229` with `wc -l`, `find`,
`git show`/`diff --stat`/`merge-base`/`log`, `grep -n -w`, `sed -n`, and `awk` over
`understand/registry.tsv` / `understand/decls.tsv`; read the actual thesis sources in
`../lean-type-theory/*.tex` where `intro.tex` paraphrases them, since `thesis-map.md` itself
contains a couple of imprecisions that `intro.tex` inherited. No file outside
`blueprint/` and `.blueprint-work/` was modified; no `lake build`/`leanblueprint`/git-mutating
command was run. `check_chapter.py blueprint/src/chapters/intro.tex` and `check_global.py` were
run before and after editing: both were already clean (`intro.tex: 0 nodes, 0 errors, 0
warnings`; global `993 labels, 2871 uses edges, 0 cycles, 0 errors`) and remained clean after.

## Corrections

1. **Thesis line count, §"thesis and how the chapters map" (was 1690, now 1287).** The sentence
   names exactly eight thesis files (`intro,axioms,typesys,unique,Wtypes,soundness,normalization,
   compilation.tex`) and attaches a line count to them. `1690` is `wc -l` over the *whole*
   `lean-type-theory/` directory (10 files, including `lstlean.tex` (282 lines, a listings style)
   and `main.tex` (121 lines, the LaTeX preamble) — neither a "section"). The eight named files
   alone total 1287 (`wc -l intro.tex axioms.tex typesys.tex unique.tex Wtypes.tex soundness.tex
   normalization.tex compilation.tex` = 2+244+122+288+198+387+22+24). `thesis-map.md`'s own
   "1690" carries the same conflation; recomputed directly rather than propagated.
2. **§3 typesys: subject-reduction attribution.** Was "that $\Leftrightarrow$ is therefore not
   transitive and fails subject reduction", which grammatically pins the subject-reduction
   failure on $\Leftrightarrow$ itself. Read `typesys.tex:57-64`: the thesis states failure of
   subject reduction for a separate *algorithmic typing judgment* $\Gamma\Vdash e:\alpha$ (built
   using $\Leftrightarrow$ in the conversion rule), not for $\Leftrightarrow$ as a relation.
   Reworded to "that the algorithmic typing judgment consequently fails subject reduction",
   matching `thesis-map.md`'s own (correct) phrasing.
3. **§4 unique: `Injectivity.lean` "three `sorry`s and nothing else".** The file has **four**
   declarations (`sort_inv`, `forallE_inv_stratified`, `forallE_inv`, `sort_forallE_inv`); three
   are literal `sorry` (lines 12, 21, 34) but `forallE_inv` is a real (if `sorryAx`-tainted) proof
   built from `forallE_inv_stratified`. Verified by reading the file in full. Reworded to "three
   of whose four declarations are literal `sorry`s (the fourth merely derives from one of them)".
4. **§5 Wtypes: "two $\eta$ rules for $\Sigma$".** Read `Wtypes.tex:92-93`: the two admitted rules
   are $\uparrow\downarrow x\equiv x$ (for `ulift`) and $(\pi_1x,\pi_2x)\equiv x$ (for $\Sigma$) —
   one rule per primitive, not two for $\Sigma$. Fixed to "one for `ulift` and one for $\Sigma$".
5. **§5 Wtypes / §"two contributed branches": `def:trproj`'s chapter.** Two places
   (`\ref{def:trproj}` next to `Chapter~\ref{chap:proj}`, and the `\ref{def:trproj}` /
   `\ref{struct:trprojctor}` "in Chapter proj and Chapter trexpr respectively" sentence) placed
   `def:trproj` in Chapter `proj`. `registry.tsv` tags both `def:trproj` and `struct:trprojctor`
   `chapter=trexpr` (matching `CONVENTIONS.md`'s own chapter table: "8 trexpr.tex — verify-typing
   (contains TrProj/TrProjCtor, trproj focus)"; `proj.tex` is `theory-proj-and-tests`, home of the
   `Theory/Proj.lean` *builders* `projFn` etc., confirmed in `registry.tsv`). Fixed both mentions:
   the first now points at `chap:trexpr`; the second now says both labels are in `chap:trexpr`,
   "building on the projection-expansion machinery of Chapter proj".
6. **§7 normalization: "its own $\kappa^+$ rule".** The $K^+$ rule is defined in `unique.tex`
   (§4, `\autoref{sec:church_rosser}`) and merely *referenced* by `normalization.tex` (§7) as "the
   reduction relation $\rightsquigarrow_\kappa$ we set up in §sec:church\_rosser" — confirmed by
   reading both files. The paragraph's own next sentence already says "diverges from \S4's
   $\kappa^+$/$\iota$ split", internally contradicting "its own". Fixed to "\S4's $\kappa^+$
   rule".
7. **iota paragraph: `addQuot.WF` conflated with the file it lives in.** Was "the ... proof
   `addQuot.WF` ... is now a genuine 615-line sorry-free theorem". `addQuot.WF` itself is one
   ~115-line theorem starting at `Verify/Environment/Quot.lean:500`; 615 is the line count of the
   *file*, which contains other lemmas besides it (confirmed: file is 615 lines, theorem starts at
   500). Reworded to attach "615-line" to the file, not the theorem: "is now proved for real,
   sorry-free, in the new 615-line `Verify/Environment/Quot.lean`".
8. **trproj paragraph: "the nine structural lemmas about it".** Master has exactly **seven**
   `sorry` lemmas about `TrProj` in `Verify/Typing/Lemmas.lean` (`weak'`, `weak'_inv`, `defeqDFC`,
   `wf`, `uniq`, `instN`, `instL` — verified by `git grep -n -w sorry master --
   Lean4Lean/Verify/Typing/{Expr,Lemmas}.lean`, which gives 8 hits total: the `TrProj` definition
   itself plus these 7 lemmas). `contrib-trproj.md`'s own text lists exactly these seven names but
   then miscounts them as "nine `sorry`s in total" (already flagged as wrong by
   `claims-trproj.md` claim 1, which computes 8, not 9, for this scope). Fixed to "seven".
   (A *different*, correctly-computed "nine" appears later in the same paragraph — "six of the
   nine projection-side `sorry`s are closed" — which uses a wider scope that legitimately
   includes master's `inferProj.WF` sorry at `InferType.lean:391`; recomputed and left as is,
   see Verified-unchanged §6 below.)
9. **trproj paragraph: "130-line theorem" for `TrEnv.proj_defeq`.** Located the theorem's exact
   span: `theorem TrEnv.proj_defeq` at `Verify/Environment/Lemmas.lean:1021` runs through its
   final tactic line at `:1158` (next section comment starts at `:1160`), i.e. 138 lines, not 130.
   This matches `hygiene-review.md`'s own correction of the original `contrib-trproj.md` figure
   ("proj\_defeq measures 138 lines ... against the md's 131"), which under the task's rule 4
   (reviews/claims win over older reports) is the number to use. Fixed 130 → 138.
10. **Attribution-badges paragraph: "roughly 175 lines" of misattributed ι-consumer content.**
    `contrib-iota.md`'s own per-file breakdown for the duplicated commit (`7a68882`/`6fd8a1d`)
    lists `Verify/TypeChecker/WHNF.lean` (141), `Inductive/Reduce.lean` (21), `Verify/Expr.lean`
    (14) and 20 lines of `Verify/Environment/Lemmas.lean` — the same four files `intro.tex` names.
    Summed: 141+21+14+20 = 196, not 175 (confirmed independently against `git show --numstat
    6fd8a1d`, the commit actually present in the merged tree). No source has "175" anywhere.
    Fixed 175 → 196.
11. **"What lean4lean is": `Theory/` top-level file list was materially incomplete with no `\dots`
    marker.** The bullet lists 5 of `Theory/`'s 9 top-level files (`VExpr.lean`, `VDecl.lean`,
    `Inductive.lean`, `Proj.lean`, `Quot.lean`), silently omitting `VLevel.lean` (188 lines),
    `LevelSat.lean` (450 lines — itself discussed two paragraphs later in the same file),
    `Meta.lean` (112) and `VEnv.lean` (57): 807 of the top-level 3122 lines (26%) unaccounted for,
    with no ellipsis to signal incompleteness (unlike the immediately following `Typing/` and
    `Std/` lists in the same bullet block, which both end `\dots`). Added `VLevel.lean` and
    `LevelSat.lean` to the list plus a trailing `\dots`.
12. **Same bullet block, `Verify/` top-level file list, same problem.** Lists 4 of 14 top-level
    `Verify/*.lean` files (`Expr.lean`, `Level.lean`, `Primitive.lean`, `Environment.lean` =
    5902 of 8898 top-level lines), omitting `Axioms.lean` (510), `EquivManager.lean` (331),
    `LevelStd.lean` (540), `LocalContext.lean` (373), `NameGenerator.lean`, `Name.lean`,
    `NormLt.lean` (364), `QSort.lean` (392), `TypeChecker.lean` (252), `VLCtx.lean` — 2996 lines,
    again with no `\dots`. Added a trailing `\dots` (kept the file list itself unchanged to keep
    the edit minimal, since none of the omitted files is individually as prominent as
    `LevelSat.lean` above).

## Verified-unchanged summary

Everything not listed above was checked and left as written. Highlights, by section:

1. **All root line-count arithmetic in "What lean4lean is" is exact**, recomputed independently
   with `wc -l`/`find`: executable kernel 2876 (18 root files) + 138 (`Environment/Basic.lean`) +
   893 (`Inductive/{Add,Reduce}.lean`) + 786 (`Std/`) = 4693; `Theory/` 10455 (`Typing/` 7333 of
   it); `Verify/` 25976 (`Environment/` 11153, `TypeChecker/` 2631, `Typing/` 3294); `Tests/` 2131;
   `Experimental/` 13334; grand total under `Lean4Lean/` 56589; `Lean4Lean.lean` 48;
   `Main.lean` 148. Every file named in these bullets (all 18 root files, `Environment/Basic.lean`
   as the sole file in `Environment/`, `Inductive/Add.lean`+`Reduce.lean` as the sole files in
   `Inductive/`) was checked against `ls`.
2. **The node-count table (§"Node counts by chapter and attribution") is exact, every cell.**
   Recomputed the full chapter × attribution cross-tab from `registry.tsv` with `awk`
   independently of the chapter's own numbers: all 14 per-chapter rows match digit-for-digit
   (including the three chapters with no `trproj` row — `typing`, `metatheory`,
   `primitives-core`/`-arith` — and the two all-master chapters `levels`/`experimental-logrel`),
   and the totals (575/157/93/128/953, 378 touched, 61/74 for `inductive`, 51/68 for `proj`,
   27/26 mixed in the two primitives chapters) all reproduce exactly. `953` total nodes and "the
   four synthesis chapters ... add none" both confirmed (`check_chapter.py` reports 0 nodes for
   `intro.tex` itself; the fourteen content chapters' `registry.tsv` rows sum to 953).
3. **All three `\srcloc{file}{line}` pointers are exactly correct**, not just within tolerance:
   `Theory/Typing/EnvLemmas.lean:334` is the literal `theorem VEnv.WF.patsStrong ... := sorry`
   line; `Verify/Environment/Lemmas.lean:1021` is the literal `theorem TrEnv.proj_defeq` line;
   `Verify/Typing/Lemmas.lean:992` is the literal `theorem TrProj.uniq` line (its `sorry` token is
   three lines later, at 995 — within any reasonable tolerance and `decls.tsv`'s own line column,
   which points at the docstring start, differs from the signature line by more in both cases,
   confirming `\srcloc` is using the more precise convention, not a wrong one).
4. **Every `\ref{}` target exists** as a `\label` (all fourteen `chap:*` plus `chap:intro`,
   confirmed with `grep -H '\label{chap:'` over every chapter file) or as a row in
   `registry.tsv` (`def:trproj`, `rule:isdefeq-pat`, `struct:trprojctor`, `structure:ind-wf`,
   `thm:add-quot-wf`, `thm:tr-env-proj-defeq`, `thm:trproj-uniq`, `thm:vtc-inferproj`,
   `thm:vtc-inferproj-struct`, `thm:wf-patsstrong` — all present, one row each), and (beyond the
   one correction above) each referenced node's registry title/attribution matches what the
   sentence around it says (e.g. `thm:vtc-inferproj`'s title is literally "... (open, and
   documented as unprovable)", matching "documented in its own statement as not provable as
   stated").
5. **Every named Lean declaration exists**, checked by `grep -w`/exact-name lookup in
   `decls.tsv`: `VInductDecl.WF`, `VEnv.addInduct`, `addInduct_WF` (and that these are exactly
   master's three inductive-theory `sorry`s, via `git show master:...`), `VEnv.pats`,
   `addQuot.WF`, `Ordered.strong` (confirmed deleted on the branch, matching "was on master an
   unconditional theorem"), `OrderedStrong`, `TrProj`/`TrProj.uniq`, `TrProjCtor`,
   `TrExprS.uniq`, `reduceProjCore.WF`, `Ctx.LiftN`/`Ctx.InstN`/`Ctx.SubstEq`,
   `VEnv.defeqs`/`IsDefEq.extra`, `Theory/Typing/HeadReduction.lean`'s `WHRed`/`StRed`, the
   20-field `VInductDecl.WF` structure (counted the field names directly: exactly 20).
6. **All commit/diff-stat and ancestry claims**, recomputed with `git`, not copied: `master..iota`
   = 45 files, +5628/−331, 28 commits; `iota..trproj` = 17 files, +2273/−170, 24 commits; `master`
   is a strict ancestor of `iota` is a strict ancestor of `trproj` (`merge-base --is-ancestor`);
   both branches' commits are 100% authored by `Alessandro Sosso <sosso@cs.au.dk>` (`git log
   --format='%an <%ae>' master..trproj`). "Six of the nine projection-side `sorry`s are closed"
   (a *different* "nine" from the corrected item 8 above, this one legitimately spanning
   `Verify/Typing/{Expr,Lemmas}.lean` **and** `Verify/TypeChecker/InferType.lean:391`) reproduces
   exactly: master has 9 sorries in that wider scope, trproj has 4 (2 inherited unclosed + 1
   restated (`inferProj.WF`) + 1 new (`inferProj.WF_struct`)), so 6 of the original 9 are closed —
   left unchanged.
7. **Test-file line counts and content**: `Tests/IotaShape.lean` 607 lines, 48-entry `checkAll`
   (8 adversarial), `checkNested` over 9 blocks — all confirmed against `contrib-iota.md`'s
   verified figures and `wc -l`; `Tests/ProjShape.lean` 185 lines, `Tests/ProjInhabit.lean` 597
   lines — both confirmed with `wc -l`.
8. **`lakefile.toml`'s `defaultTargets`** = `["Lean4Lean", "lean4lean", "Lean4Lean.Theory",
   "Lean4Lean.Verify"]`, confirming "Not in `defaultTargets`" for `Tests/` and (implicitly)
   `Experimental/`. **No file under `Verify/` or `Theory/` imports `Experimental/`**
   (`grep -rl 'import Lean4Lean.Experimental'` over both trees is empty), confirming
   "not consumed by `Verify/`".
9. **"Twelve of the fourteen [chapters] ... carry a Contribution summary"** and **"every content
   chapter closes with a Review notes section"**: checked all 14 chapter files directly —
   exactly `levels.tex` and `experimental-logrel.tex` lack a Contribution-summary section; all 14
   have a Review-notes section.
10. **`lean-toolchain`** file content is exactly `leanprover/lean4:v4.33.0-rc2`, matching the
    stated toolchain. **`blueprint/lean_decls`** exists (3686 lines), consistent with the
    `checkdecls`-not-wired paragraph. **`\dochome`** in `web.tex` is set to
    `https://barabbs.github.io/lean4lean/docs`, a `leanprover-community`-style (doc-gen4) URL,
    consistent with the claim (whether that site is actually deployed was not independently
    re-verified here — see Unresolved doubts).
11. **The unused-declaration census (task rule 5, 31 vs 78/889)** does not appear anywhere in
    `intro.tex` — no number from `unused-contrib.md` is cited in this chapter — so no correction
    was needed on that count for this file specifically.
12. Ran `check_chapter.py`/`check_global.py` before and after: both clean throughout
    (`intro.tex: 0 nodes, 0 errors, 0 warnings`; global `993 labels, 2871 uses edges, 0 cycles,
    0 errors`), including `check_chapter.py`'s unescaped-underscore heuristic, so none of the
    corrections introduced a raw `_` outside `\texttt{}`/`\lean{}`/`\srcloc{}`/`\label{}`/`\ref{}`.

## Unresolved doubts

- **"No such [doc] site is built or deployed"** (Limits-of-this-blueprint bullet) was not
  independently re-verified against the live `barabbs.github.io/lean4lean/docs` URL in this pass
  (no source report explicitly confirms or denies it either); left as written since nothing
  contradicts it and it is a plausible, low-stakes infrastructure claim.
- **"the reviewing agents corrected this by hand where it was noticed, but the blame files
  themselves were not re-derived"** (attribution-badges paragraph): this specific sentence about
  *intro.tex's own* attribution caveat is not verbatim in any single source report, but the same
  pattern — an attribution overclaim in a chapter's overview corrected by hand during that
  chapter's own review pass, without touching the underlying blame files — is documented for at
  least Chapter `inductive` (`reviews/inductive.md`: "Overview, attribution caveat: corrected to
  two line re-wraps and two docstring rewrites ..."). Treated as adequately backed by that
  precedent; not independently confirmed for `intro.tex` itself.
- **"The branch also inherits `iota`'s two open design questions wholesale"** (end of the
  `trproj` paragraph): read as referring back to the two headline caveats named for `iota` two
  paragraphs earlier (the `patsStrong` sorry and the kernel-shaped-data-vs-thesis-generated
  divergence in `VInductDecl.WF`). This reading is internally consistent but the phrase "two open
  design questions" is not a fixed term used identically elsewhere in the source reports (which
  elsewhere count "four open maintainer questions" in the PR text — a different, unrelated list of
  four questions posed to the maintainer, not two design questions). Left unchanged since no
  numeric claim is actually being made about a different list, but flagging the phrase as an
  interpretation rather than a verbatim-sourced count.
- Did not re-verify the thesis-file byte contents beyond `wc -l` and targeted `grep`s (e.g. did
  not re-read `soundness.tex`, `axioms.tex` §2.1/§2.2 in full) since `intro.tex`'s claims about
  them matched `thesis-map.md` and the specific passages checked (`typesys.tex`, `unique.tex`,
  `Wtypes.tex`, `normalization.tex`, `compilation.tex`) all read as claimed.
