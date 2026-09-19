# Review of chapter experimental-reduction

Scope: `blueprint/src/chapters/experimental-reduction.tex` (47 nodes, 9 `mixed`-badged, 38
master). All 9 `\contrib` nodes were opened at their `\srcloc` and cross-checked against the
surrounding declarations; more than 15 master nodes were checked this way too (all of
`NormalEq.lean`'s and `ParallelReduction.lean`'s nodes, all of `Stratified.lean`/
`StratifiedUntyped.lean`/`Stronger.lean`, `class:expb-sexpr-params`, `family:expb-sexpr-syntax`,
`inductive:expb-sexpr-isdefeq`, `family:expb-sexpr-operational`, `inductive:expb-hastypes`,
`thm:expb-hastypes-uniq`, `thm:expb-uniq-sort`, `thm:expb-isdefeq-prime`,
`family:expb-thierry-domain`, `family:expb-thierry-mono`, `family:expb-thierry2-shape`,
`family:expb-thierry2-model`, `family:expb-stepindexed`, `family:expb-morestepindexed`,
`family:expb-morestepindexed-logrel`, `family:expb-domaintheory`). Sources read in full or in
targeted ranges: `Lean4Lean/Experimental/{NormalEq,ParallelReduction,Stratified,
StratifiedUntyped,Stronger,SExpr,UniqueTyping,Thierry,Thierry2,StepIndexed,MoreStepIndexed,
DomainTheory}.lean`, plus `Lean4Lean/Theory/Typing/{ChurchRosser,InductiveParams,Pattern,
Strong,Lemmas}.lean` for cross-references and the actual duplicate/non-duplicate
determinations. Branch attribution was checked against
`.blueprint-work/blame/Lean4Lean_Experimental_{NormalEq,ParallelReduction,Stratified,
StratifiedUntyped,Stronger}.lean.txt` and `..._Theory_Typing_Strong.lean.txt`. The Lean
toolchain was not built or invoked (`lake build` is forbidden by the task); all sorry/axiom
counts were verified by direct source reading and cross-checked against `decls.tsv`.

## Quality verdict

The chapter is accurate to an unusually high degree: every file-line-count claim in the
overview (513/913/340/324/628/1324/266/88/489/242/363/831, totalling 6321) matches `wc -l`
exactly; every cited sorry/axiom location I checked (NormalEq.lean, ParallelReduction.lean,
Stratified.lean, StratifiedUntyped.lean, Stronger.lean:624-628, SExpr.lean:679-680 and the
1008-1295 bridge list, Thierry.lean's 14-sorry count, Thierry2.lean's `#exit`/`TypeEqS`/
`TypeEq`/`TypeEq.mono` claims, MoreStepIndexed.lean's five-sorry-four-in-comments count, and
`Dom.out`'s `stop` tactic, which is indeed Lean core's `repeat sorry` macro) was correct
character-for-character; and the technical claims I spot-checked (the `Check.OK`/`Realizes`
strict-positivity argument, the `Ordered`-to-`OrderedStrong` strengthening being forced by
`OrderedStrong.pats : PatsStrongOn`, itself iota-authored in `Theory/Typing/Strong.lean`) hold
up against the code. The 28 lines `iota` actually contributed here (one field, one import, one
new inductive constructor with two consuming cases twice over, and one stub) are exactly as
described: minimal, mostly load-bearing compile-fixes with one genuine, correctly-made design
decision (the `IsDefEq1.pat` stratification). The one place the chapter over-generalised was in
attributing a "verbatim duplicate of `ChurchRosser.lean`" to *two* different `pat` cases in
`ParallelReduction.lean` when only one of them actually has a `ChurchRosser.lean` counterpart,
and misnaming that counterpart in the process (see Refuted claims). This is a real but narrow
mistake in an otherwise carefully source-checked chapter; nothing here reads as slop.

## Confirmed code issues

- `Lean4Lean/Experimental/SExpr.lean:981-997` — medium. `WHRed.determ` is `sorry` in all five
  case splits where an `extra` (pattern-rule) step meets anything on the other side, including
  another `extra` step. Determinism of weak-head reduction is therefore established only for
  the β/application fragment, not for the calculus as a whole. The chapter's own prose stated
  "is deterministic (`WHRed.determ`)" without this qualification (fixed, see below).
- `Lean4Lean/Experimental/Thierry2.lean:472,421` — medium (as the chapter already documents,
  now independently confirmed). `D.pi` and `DF.mk'` are literal `sorry`s inside the same
  `family:expb-thierry2-model` node whose sibling proof still carried `\leanok`; the
  `DefEqF`/`DefEqPiF`/`DefEqLamF` `mono`/`mono_r` theorems the proof actually establishes are
  textually sorry-free and structurally independent of `D`/`DF`/`interp` (verified by reading
  all five bodies in the enclosing `mutual` block, `Thierry2.lean:700-831`), but `decls.tsv`
  confirms all four still carry `sorryAx` in their compiled axiom list via the shared shape
  lattice lemmas, so the family is transitively, not just textually, incomplete either way.
- `Lean4Lean/Experimental/Thierry.lean:9` / `Thierry2.lean:9` — high (already documented).
  `axiom mySorry : α` is an inhabitant of every type, i.e. a proof of `False`, used inside
  `DF.comp`/`DF.bot` and elsewhere; both files are inconsistent by construction. Correctly
  flagged in the chapter with a matching `\axfoot`.
- `Lean4Lean/Experimental/Stronger.lean:28` — low (already documented). `pats _ _ := False`
  is `iota`'s one-line fix to keep `VEnv'.out` compiling after `VEnv` grew a `pats` field; it
  silently restricts every theorem in the file to ι-free environments, in a file that already
  dead-ends in four `sorry`s at `:624-628`.
- `Lean4Lean/Experimental/StratifiedUntyped.lean:51-55,103-104` — low (already documented).
  The `iota`-added `IsDefEqU1.pat` constructor is never eliminated: its only would-be consumer,
  `IsDefEqU1.induction`, is inside the commented-out block at lines 121-142.

## Refuted claims

- **"These three lines are the same argument as the `pat` case of `VEnv.IsDefEq.toParams` in
  `Theory/Typing/ChurchRosser.lean`"** (reviewnote inside `thm:expb-todyping`'s proof,
  `ParallelReduction.lean:857-859`). No declaration named `VEnv.IsDefEq.toParams` exists
  anywhere in the repository. The nearest name, `VEnv.toParams`, lives in
  `Theory/Typing/InductiveParams.lean:393`, not `ChurchRosser.lean`, and its `pat_wf` field
  goes the *opposite* logical direction (`Check.OK.exists_realizer`, OK → Realizes, to
  construct an `IsDefEq.pat` derivation) from `toTyping`'s `pat` case (`Realizes.toOK`,
  Realizes → OK, to discharge the interface's `pat_wf`), so it is not "the same argument"
  either way. `toTyping` in fact has no counterpart in `ChurchRosser.lean` at all, because that
  file proves its results directly about `env.IsDefEq` under a `[Params]` instance and never
  needs to bridge into a separate abstract record. The real duplicate — same three-line shape,
  same two `TODO: remove` files — is the *other* `pat` case in the same file,
  `VEnv.IsDefEqU.church_rosser` at `ParallelReduction.lean:909-913`, which mirrors
  `IsDefEq.church_rosser`'s `pat` case in `ChurchRosser.lean:1390-1394` line for line. Fixed:
  the false reviewnote was replaced and the correct cross-reference added.
- **"the two ι cases added here [`ParallelReduction.lean:857`] and at line 909 ... duplicate
  exactly what the branch added to `Theory/Typing/ChurchRosser.lean`"** (Review notes section,
  first bullet). Overbroad for the same reason: only the line-909 case duplicates
  `ChurchRosser.lean`; the line-857 `toTyping` case does not. Fixed: the bullet now anchors on
  line 909, names the actual duplicated declaration and field, and adds a sentence stating that
  line 857 is not a duplicate.
- **"Everything else is either a verbatim duplicate of code the branch already wrote in
  `ChurchRosser.lean`, or a stub (`pats _ _ := False`) in a file that dead-ends"** (chapter
  overview, "Assessment" paragraph). This two-way split leaves out `StratifiedUntyped.lean`'s
  8 lines, which duplicate `Stratified.lean`'s *own* stratification decision (not anything in
  `ChurchRosser.lean`), and `toTyping`'s 3 lines, which duplicate nothing at all. Fixed:
  rewritten as a three-way split (ChurchRosser.lean duplicates; the repeated
  Stratified/StratifiedUntyped decision; and the two pieces of one-off glue).
- **"`iota` changed 27 lines across five files: one field in `NormalEq.lean`, ..."** (overview
  and Contribution summary). `.blueprint-work/blame/Lean4Lean_Experimental_NormalEq.lean.txt`
  marks *two* lines `I`: the `pat_env` field (line 97) and a supporting
  `import Lean4Lean.Theory.Typing.Pattern` (line 2), needed because `Typing.Pat` now mentions
  `Pattern`. The other four files' counts (8/9/8/1) were independently re-verified against
  their blame files and are exactly right, so the true total is 28, not 27. Fixed in both the
  overview and the Contribution summary.
- **"Weak-head reduction `WHRed` (...) is deterministic (`WHRed.determ`) and closes to
  `WHRedS`"** (`family:expb-sexpr-operational`). `WHRed.determ`'s proof (`SExpr.lean:981-997`)
  is `sorry` in all five cases touching an `extra` step, so determinism holds only for the
  β/application fragment — precisely the kind of case the node's own reviewnote already flags
  as broken for the *other* operational lemmas, just not for this one. Fixed: the sentence now
  states the qualification and a new Review Notes bullet records it.
- **Checker-flagged, now resolved: `family:expb-thierry2-model`'s proof kept `\leanok` while
  its own `\lean{}` list includes `D.pi`, whose body is `:= sorry`.** Read the source to
  confirm this is a genuine direct sorry (not a heuristic false positive like the `stop`-tactic
  or transitive-`sorry` cases elsewhere in the chapter): `D.pi`'s entire body is the single
  token `sorry`. Per the blueprint convention, a proof whose bundled declarations contain a
  literal sorry cannot carry `\leanok`. Fixed: `\leanok` replaced with a `\textbf{Not proved in
  Lean.}` opening that also records, correctly, that the four `mono`/`mono_r` theorems this
  family is really about have no literal sorry in their own bodies (verified by reading all
  five mutually-defined declarations at `Thierry2.lean:700-831`) even though they remain
  `sorryAx`-tainted transitively per `decls.tsv`.

## Fixes applied to the tex

All in `blueprint/src/chapters/experimental-reduction.tex`; checker clean afterwards
(`47 nodes, 0 errors, 3 warnings` — the 3 warnings are pre-existing false positives from the
underscore-escaping heuristic firing on legitimate `$\Gamma_0$`/`$m_1$`-style math-mode
subscripts, not real issues; global check: `980 labels, 2871 uses edges, 0 cycles, 0 errors`).

1. Overview, "What the branches contributed": `27` → `28` lines; `NormalEq.lean`'s share
   corrected from "one field" to "one field plus one supporting import".
2. Overview, "Assessment": replaced the two-way "duplicate of ChurchRosser.lean, or a stub"
   split with an accurate three-way split (ChurchRosser.lean duplicates; the
   Stratified/StratifiedUntyped repeated decision; one-off glue with no duplicate anywhere);
   `27` → `28` lines.
3. `thm:expb-todyping`'s proof: replaced the false `VEnv.IsDefEq.toParams`/`ChurchRosser.lean`
   reviewnote with a correct one explaining why `toTyping` has no counterpart there and
   pointing to the real duplicate (`\ref{thm:expb-isdefequ-church-rosser}`).
4. `family:expb-sexpr-operational`: qualified the "`WHRed` ... is deterministic
   (`WHRed.determ`)" claim with the five live sorry sites (lines 987, 992, 995-997) and their
   scope (only `extra`-involving cases are unproved).
5. `family:expb-thierry2-model`'s proof: removed `\leanok`, added a `\textbf{Not proved in
   Lean.}` opening that correctly separates the sorry-tainted domain declarations (`D.pi`,
   `DF.mk'`) from the textually sorry-free but transitively tainted `mono`/`mono_r` theorems.
6. Contribution summary: `27` → `28` lines; noted the supporting import alongside
   `Typing.pat_env`.
7. Review notes: rewrote the first bullet to anchor on `ParallelReduction.lean:909` (the actual
   duplicate), name the duplicated declaration (`IsDefEq.church_rosser`'s `pat` case,
   `ChurchRosser.lean:1390-1394`) and field (`Params.pat_env`), and added a sentence stating
   that the line-857 `toTyping` case is *not* a duplicate. Added a new medium-severity bullet
   for the `WHRed.determ` overclaim.

No genuine criticism was softened; every severity level in the surviving bullets is unchanged
from the original, and every one of the chapter's other reviewnotes and axfoots that I checked
(the great majority of the chapter) was confirmed accurate and left untouched.
