# Group `experimental-b` — research modules in `Lean4Lean/Experimental/`

12 files, 5 253 lines. Eleven are pure upstream (Mario Carneiro) code; five carry a
total of **27 changed lines** from the `iota` branch and **zero** from `trproj`.

| file | lines | M | I | P | live `sorry`/`axiom` |
|---|---|---|---|---|---|
| `SExpr.lean` | 1324 | 1324 | 0 | 0 | 30 sorry, 1 axiom |
| `ParallelReduction.lean` | 913 | 905 | **8** | 0 | 2 sorry |
| `Thierry2.lean` | 831 | 831 | 0 | 0 | 26 sorry, `mySorry` |
| `Stronger.lean` | 628 | 627 | **1** | 0 | 4 sorry |
| `NormalEq.lean` | 513 | 511 | **2**¹ | 0 | none |
| `MoreStepIndexed.lean` | 489 | 489 | 0 | 0 | 5 sorry, 8 axioms |
| `Thierry.lean` | 363 | 363 | 0 | 0 | 14 sorry, `mySorry` |
| `Stratified.lean` | 340 | 331 | **9** | 0 | 1 live sorry (l. 96) |
| `StratifiedUntyped.lean` | 324 | 316 | **8** | 0 | 1 live sorry (l. 77) |
| `UniqueTyping.lean` | 266 | 266 | 0 | 0 | 0 textual, but *sorry-dependent* |
| `DomainTheory.lean` | 242 | 242 | 0 | 0 | `stop` (= `repeat sorry`) l. 223 |
| `StepIndexed.lean` | 88 | 88 | 0 | 0 | 3 axioms |

¹ the blame file tags `NormalEq.lean:2` (`import …Typing.Pattern`) as iota, but that
import is already on `master`; `git diff master..trproj` shows **one** changed line.

`Lean4Lean.Experimental` is **not** a `lake` default target (`lakefile.toml`), but
`.github/workflows/ci.yml` builds it explicitly ("WIP and deliberately not a default
target, but it still has to compile"). That is what forced the 27 lines: every one of
them is the minimum needed to keep an unrelated experiment compiling after `VEnv` grew
a `pats` field and `VEnv.IsDefEq` grew a `pat` constructor.

## What the files are, and where they sit in the thesis

Two clusters.

**(A) The `VExpr` cluster — Church-Rosser and stratification.**
`NormalEq.lean` + `ParallelReduction.lean` are a complete formalization of
*unique.tex* §`sec:kappa`–§`sec:church_rosser`: `NormalEq` (NormalEq.lean:165) *is* the
thesis's proof-irrelevance relation $\equiv_p$, rule for rule; `ParRed`
(ParallelReduction.lean:18) is $\gg_\kappa$, `CParRed` (:33) is $\ggg_\kappa$ with the
`NonNeutral` guard matching "the compatibility rules only apply if none of the
substantive rules are applicable"; `ParRed.triangle` (:282) is Lemma `thm:tri`,
`NormalEq.parRed` (:687) is Lemma `thm:gg_compat`, and `ParRedS.church_rosser` (:799)
is Theorem `thm:church_rosser`. Both files are headed
`-- TODO: remove, this is now part of ChurchRosser.lean`.

`Stratified.lean` / `StratifiedUntyped.lean` formalize *unique.tex* §`sec:unique`: the
$\vdash_n$ stratification used to break the circularity between unique typing and
Church-Rosser. `HasType1`/`IsDefEq1` are one layer (all cross-judgment appeals replaced
by parameters), `IsDefEq.induction1` (Stratified.lean:80) decomposes a real derivation
into one layer and `IsDefEq1.induction` (:142) collapses it back. Two thirds of each
file is commented-out unique-typing attempts. `Stronger.lean` is a third, abandoned
attack on the same problem via level-annotated judgments; it dead-ends at
`IsDefEqStrong.uniqL'` (Stronger.lean:575) with the comment
`-- looks like it needs unique typing :(`.

**(B) The `SExpr` cluster — normalization attempts.**
`SExpr.lean` (1324 lines) is the base: quotiented levels `SLevel`, a de Bruijn
substitution calculus that the shipping code explicitly cites
(`Theory/VExpr.lean:836`), a weak defeq `IsDefEq` with heterogeneous transitivity, and
operational judgments. `UniqueTyping.lean` proves type uniqueness over it and shows
`trans'` admissible. `StepIndexed.lean`, `MoreStepIndexed.lean`, `DomainTheory.lean`,
`Thierry.lean`, `Thierry2.lean` are five different unfinished semantic models
(coinductive classifiers; step-indexed logical relations over a `Shape` lattice; an
inverse-limit domain; two passes at Coquand–Huber adequacy). These correspond to
*normalization.tex*, which is 22 lines long and ends with the word `UNFINISHED`.

## The contributed lines, one by one

**1. `NormalEq.lean:97` — `Typing.pat_env : env.pats p r → Pat p r`.**
A new field of the abstract `Typing` interface, saying every ι rule registered in the
environment is one of the interface's abstract `Pat` rules. Correct and necessary for
the two `ParallelReduction` cases below. Two caveats: (i) `Lean4Lean.Typing` is *never
instantiated* anywhere in the repository, so the obligation is never discharged here —
the real content is the identical field on `VEnv.Params`
(`Theory/Typing/ChurchRosser.lean:32`), discharged at
`Theory/Typing/InductiveParams.lean:408` with `pat_env := id`; (ii) the ChurchRosser
field has a docstring, this one does not.

**2. `ParallelReduction.lean:857-859` — the `pat` case of `VEnv.IsDefEq.toTyping`.**
```
| pat hp hm _ hr _ ih ihall =>
  have hok := hr.toOK (defeq := TY.IsDefEqU _) fun t ht => (ihall t ht).1
  exact ⟨TY.pat_wf (TY.pat_env hp) hm ih.2 hok, ih.2⟩
```
Sound-looking and minimal: `Realizes.toOK` (`Theory/Typing/Pattern.lean:318`) converts
the rule's list-of-triples side-condition premise into the `Check.OK` form the abstract
interface wants, `pat_env` promotes the environment rule to a `Pat`, and `pat_wf` is
exactly the interface's ι-regularity field. The second component reuses `ih.2`, the
redex's typing — correct, because `IsDefEq.pat` types the reduct *at the redex's type*
by fiat.

**3. `ParallelReduction.lean:909-913` — the `pat` case of `VEnv.IsDefEqU.church_rosser`.**
Structurally identical to the pre-existing `extra` case three lines above: exhibit the
one-step witness as `ParRed.extra` firing the rule itself with every metavariable
reduced by `.rfl`, then close with reflexivity of $\equiv_p$ at the reduct. This is the
right shape — it is the only place where a ι step has to be realised as an actual
parallel reduction, and doing it in one step with no metavariable reduction is exactly
what the thesis's $\gg_\kappa$ ι rule permits.

Both cases are **byte-identical to the real ones** in
`Theory/Typing/ChurchRosser.lean:1390-1393`. That is the central redundancy criticism of
this group: the author maintained the ι rule in a second copy of a development that
upstream has marked for deletion. It is defensible (CI builds the tree), but neither
file got a comment pointing at the other.

**4. `Stratified.lean:71-75` — `IsDefEq1.pat`.** The best of the contributed pieces.
It is a faithful transcription of the core rule (`Theory/Typing/Basic.lean:60`) with
*correct stratification choices*: the typing premise `Γ ⊢ e : A` goes to the abstract
`HasType1` parameter (an alternation point, exactly as `beta`/`eta`/`proofIrrel` do),
while the side-condition premises stay at the recursive `IsDefEq1` (no alternation,
exactly as `appDF`/`trans` do). Getting that split wrong would have silently changed
what the stratification counts. The `Realizes` + explicit `chk` encoding, rather than
`Check.OK`, is forced by strict positivity, so it is not gratuitous — though no comment
says so.

**5. `Stratified.lean:121-122` and `:158` — the two `pat` cases.** The round trip is
complete: `induction1` produces the layer rule and `IsDefEq1.induction` collapses it
back into `VEnv.IsDefEq.pat` in one line (`exact .pat hp hm (hty he) hr ihall`). That
the constructor round-trips is decent evidence it is neither too strong nor too weak.

**6. `Stratified.lean:79` and `StratifiedUntyped.lean:59` — `Ordered env` →
`OrderedStrong env`.** Forced: on this branch `IsDefEq.strong`
(`Theory/Typing/Strong.lean:805`) requires `OrderedStrong`, which bundles `Ordered`
with `OnTypes EnvStrong` and `PatsStrongOn` (subject reduction of the registered ι
rules). `VEnv.WF.orderedStrong` (`Theory/Typing/EnvLemmas.lean:339`) shows any
well-formed environment qualifies, so nothing realistic is lost. But it is a **silent
weakening of an exported theorem** with no comment — a reviewer diffing against master
sees the hypothesis grow and has to go three files away to learn why.

**7. `StratifiedUntyped.lean:51-55` — `IsDefEqU1.pat`.** The weakest piece. Nothing
consumes it (the would-be consumer `IsDefEqU1.induction` is commented out at
:121-142), and in the type-erased setting the third component of each `chk` triple is
completely unconstrained by `Realizes`, so the rule is a more roundabout way of saying
`r.2.OK (IsDefEqU1 …) m1 m2`. Uniformity with the typed version is a fine reason to
keep the shape; a one-line comment saying so would have been better than nothing.

**8. `Stronger.lean:28` — `pats _ _ := False` in `VEnv'.out`.** One line, cheapest
possible fix. Sound, but narrowing: every theorem in the file about erased
environments is now only about ι-free ones, so this experiment can never be
reconnected to the ι development without a real `pats` field on `VEnv'`. Given the file
dead-ends in four `sorry`s, pragmatic.

## Candid assessment

**Design quality: good where it matters.** The single piece of real design judgement
required — how to stratify the ι rule's premises in `IsDefEq1` — was made correctly,
and the round-trip lemmas prove it. The `pat_env`/`Realizes.toOK` idiom used in
`ParallelReduction` is the same one the shipping `ChurchRosser.lean` uses, so it is
consistent with the branch's own conventions.

**Proof quality: minimal and correct, but all of it lands on unproved ground.**
`ParallelReduction.lean` carries two master `sorry`s (lines 699, 718 — precisely the
cases where a pattern reduction meets a proof-irrelevance step), so the ι case added to
`church_rosser` extends a theorem that is not proved in this file.
`Stratified.lean:96` and `StratifiedUntyped.lean:77` likewise pre-date the branch.
None of this is the contributor's fault, but a blueprint should not present these two
`church_rosser`/`induction1` nodes as `proved`.

**Documentation: thin.** None of the 27 contributed lines carries a comment or
docstring, in a branch whose shipping files (`Theory/Typing/Basic.lean:57-59`,
`Strong.lean:86-88`, `Pattern.lean:302-317`) are unusually well documented. The
`Ordered → OrderedStrong` change in particular should have been annotated.

**Redundancy and dead code:** items 1–3 duplicate `ChurchRosser.lean`; item 7 is dead;
item 8 is a stub in a dead file. Of the 27 lines, roughly 9 (`Stratified.lean`) do
verification work that nothing else does, and the rest are compile-keeping.

**Correct statements?** Yes, as far as they go. The one place where a *stronger*
statement was available and not taken is `Stronger.lean`: adding `pats` to `VEnv'`
rather than erasing it to `False` would have kept the experiment general. And the one
real *gap* the branch left in this group is `SExpr.lean`: the whole SExpr-side
development — `Params` (`SExpr.lean:23`), `IsDefEq` (:590), and everything built on
them (`UniqueTyping.lean`, `ShapeLogRel*`, `LogRel`, `StepIndexed`,
`MoreStepIndexed`) — still has **no ι rule at all** (the pattern-based rule is
commented out at :608-609, and reduction rules enter only via `env.defeqs` plus the
global `axiom Params.extra_pat` at :614). The two halves of the project now model ι
differently, and nothing in the tree flags it.

## Traps for the blueprint author

- `UniqueTyping.lean` has **zero textual `sorry`** but is entirely conditional on
  `SExpr.IsDefEq.strong` (`SExpr.lean:679`, `:= sorry`). Do not mark it complete.
- `DomainTheory.lean` also has zero textual `sorry` but `Dom.out` (:211) contains
  `stop` at :223, which is `repeat sorry`. Same for `LogRel.lean:320/361/364/369/377`
  and `ShapeLogRel.lean:1703`.
- `Thierry.lean:9` and `Thierry2.lean:9` declare `axiom mySorry : α` — a proof of
  `False`. These files are imported by nothing, but the axiom must be recorded.
- `MoreStepIndexed.lean:38-45` and `StepIndexed.lean:59-62` axiomatize the very
  objects the files are about (`WHRedUpToN`, `ParRedN`, `IsTy`, `IsTy.def`).
- The `Shape` approximation lattice exists in three near-copies
  (`Thierry2.lean:21-350`, `MoreStepIndexed.lean:63-336`, `ShapeLogRel.lean`), each
  with its own partly-`sorry`ed order laws.
