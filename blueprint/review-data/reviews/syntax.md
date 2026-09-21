# Review of chapter syntax

Adversarial faithfulness review of `blueprint/src/chapters/syntax.tex` (69 nodes) against the
Lean sources `Lean4Lean/Theory.lean`, `Theory/VLevel.lean`, `Theory/VExpr.lean`,
`Theory/VDecl.lean`, `Theory/VEnv.lean`, `Theory/Quot.lean`, `Theory/Meta.lean`,
`Theory/LevelSat.lean`, against `.blueprint-work/blame/`, against `decls.tsv`, and against the
thesis sources at `lean-type-theory/` (a sibling repository checkout).
All 32 `\contrib` nodes were opened at their `\srcloc`; so were 30 master nodes (every master
node in the chapter except the four purely structural `VDecl`/`VEnv` record nodes, which were
still read in the source).

## Quality verdict

The contributed code in this chapter is real specification work, not slop, and it is unusually
well documented: `VRecRule.ctorParams` carries a docstring that explains *why* a field the
direct-block well-formedness predicate makes redundant is nonetheless necessary as
specification (nested recursors such as `Tree.rec_1` fire on `List.cons`), and the `insts`
docstring argues the substitution-versus-applied-abstraction design choice rather than
restating the type. Nothing in these eight files depends on a `sorry`: every one of the 558
declarations in them is a definition or a fully proved theorem and none has `sorryAx` in its
axiom footprint (`decls.tsv`). The `trproj` organising idea — `lift'_eq_subst` plus
`Subst.liftN_lift_l_id`, so a builder lemma is proved once against `subst` and read off in
weakening and instantiation form — is genuinely load-bearing: `Theory/Proj.lean` consumes all
five `Subst.liftN` bookkeeping lemmas plus `subst_instN` and `liftN_subst_liftN`, and
`mkApps_subst` yields three corollaries from one induction. The weakness is hygiene, and it is
real: seven contributed declarations are dead (five mentioned nowhere, two surviving only by
feeding one of those five), one contributed lemma (`CtorHeaded.forallE`) is unused, proved by
`:= h`, and carries a docstring stating a different proposition than its statement, and the
`trproj` re-derivation of `lift'_inst_hi` orphaned a six-declaration master block on a file
that is otherwise shared verbatim with upstream — a pure merge-conflict cost with no benefit.

## Confirmed code issues

- `Lean4Lean/Theory/VExpr.lean:919`, **medium**. `lift_r_one` has no consumer anywhere. Master
  proved `lift'_inst_hi` at `master:VExpr.lean:903` with
  `simp [subst_lift', lift'_subst, lift_r_one, inst_eq]`; `trproj` moved the lemma to line 1018
  and re-derived it from the new `lift'_instN_hi`. The whole chain that existed only to feed
  `lift_r_one` died with it: `Subst.lift_r_comm` (911), `Subst.trunc` (908), `Subst.Depth.one`
  (885), `Subst.Depth.id` (858), `Subst.Depth` (796) — six declarations now mentioned only
  inside that block. (Verified by grep over `Lean4Lean/`, excluding the independent
  `Experimental/SExpr.lean` copies, where `lift_r_one` is still used at SExpr.lean:411.)
- `Lean4Lean/Theory/VExpr.lean:1232`, **medium**. `VExpr.CtorHeaded.forallE` is unused
  (grep: only its own declaration line), is `:= h` because it is definitionally trivial, and
  its docstring ("A `CtorHeaded` type is not a Π-telescope ending in a variable, so
  instantiation cannot create new leading binders") states the motivation for
  `piArity_inst_of_ctorHeaded` at line 1274, not this statement.
- `Lean4Lean/Theory/VExpr.lean:1256` and `1248`, **low**. `CtorHeaded.instL` is dead and
  `getAppFn_instL_const` survives only by feeding it. `CtorHeaded.inst` (1241) and
  `piArity_inst_of_ctorHeaded` (1274) are used from `Theory/Proj.lean:259,269,270`, so the
  `instL` pair reads as symmetry-driven rather than needed.
- `Lean4Lean/Theory/VExpr.lean:753,756`, **low**. `Lift.liftVar_consN_lt` and
  `Lift.liftVar_consN_succ` have no consumer, which makes `Lift.consN_fixes` (745) dead in
  effect too. Of the four-lemma `trproj` block at 744-758 only `consN_cons` is used, at
  VExpr.lean:1111 inside `piBinders_lift'`. (The `consN_cons` hits in
  `Verify/Environment/Primitive/Basic.lean` are a different declaration, `Subst.consN_cons`.)
- `Lean4Lean/Theory/VDecl.lean:51`, **low**. `VRecursor.getFirstIndexIdx` has no consumer
  anywhere. Every other `getFirstIndexIdx` in the repository is Lean's own `RecursorVal` field
  on a kernel `rval` (`Inductive/Reduce.lean:84`, `Verify/TypeChecker/WHNF.lean:29,33,35,37-39,62`)
  or a comment (`Theory/Typing/Pattern.lean:532`).
- `Lean4Lean/Theory/Inductive.lean:260`, **low**. `VEnv.addRecRule` spells
  `r.numParams + r.numMotives + r.numMinors + r.numIndices` out by hand instead of calling
  `VRecursor.getMajorIdx`, although its own docstring (line 251-252) says "major at
  `getMajorIdx`". So the one place that would use `getMajorIdx` does not.
- `Lean4Lean/Theory/VExpr.lean:1009` and `1032`, **low**. Three analogous redundancy pairs get
  three different treatments. `subst_instN` subsumes master's `subst_inst` (952) at `n = 0` and
  `liftN_subst_liftN` subsumes master's `lift_subst_lift` (947) at `i = 0` (its own docstring
  says so), yet both master lemmas keep independent hand proofs, while `lift'_inst_hi` in the
  same block *was* re-derived. `subst_instN`'s docstring says "under `m` binders" while the
  statement binds `n`; `lift'_instN_hi`'s docstring has the same `m`/statement mismatch in
  reverse (there the binder really is `m`).
- `Lean4Lean/Theory/VExpr.lean:1046`, **low**. Stale section docstring: it promises telescope
  and spine readers "with their decidability", but commit `ba118fd` ("file the head-shape
  decidability instances with the tests") moved them to `Lean4Lean/Tests/ShapeDecide.lean`, so
  the section contains no `Decidable` instance at all.
- `Lean4Lean/Theory/VEnv.lean:44`, **low**. `addPat` cannot fail: unlike `addConst` it performs
  no freshness or consistency check, so two conflicting reducts for the same pattern are
  admissible at this layer; the invariant is enforced only later. The asymmetry is not
  commented on.
- `Lean4Lean/Theory/VDecl.lean:41`, **low**. `VRecursor.k` is recorded but, as its own docstring
  admits, unused by the theory; the thesis's second ι rule (K-like reduction, `axioms.tex`
  §2.6.4) is outside the model.
- `Lean4Lean/Theory/Quot.lean:11`, **low**. After the `iota` work the model carries two
  mechanisms for computation rules (`defeqs` for `quotDefEq`, `pats` for ι), and nothing in the
  code acknowledges it: `Theory/Quot.lean` has no docstrings at all, and neither `VEnv.addPat`
  nor `Theory/Typing/Pattern.lean` mentions the quotient rule.
- `Lean4Lean/Theory/VExpr.lean:1200` and `1295`, **low**. The head-constructor tests exist only
  for the `Decidable` instances in the test file (the `isSort`/`isConst` hits in
  `TypeChecker.lean` and `Verify/TypeChecker/IsDefEq.lean` are `Lean.Expr` methods, not these),
  and their docstring is attached to `isSort` alone while describing all six declarations.
  `const_mkApps_spine` bundles two independent facts into one conjunction and is only ever
  consumed as `.1`/`.2`; neither it nor `eq_const_mkApps_of_spine` is used outside VExpr.lean.

## Refuted claims

Claims that were in the chapter and are false; each was corrected in the tex.

1. **Thesis section numbers were systematically off by one (9 occurrences).** Every `\S2.4`
   reference for constants, universe substitution and δ-reduction was wrong. In
   `lean-type-theory/axioms.tex` (an `article`, with `intro.tex` = §1), the subsections are 2.1
   Typing, 2.2 Definitional equality, 2.3 Reduction, 2.4 **let binders (ζ reduction)**, 2.5
   **Definitions (δ reduction)**, 2.6 Inductive types, 2.7 Non-primitive axioms. `τ_ℓ̄(c)`,
   `v_ℓ̄(c)`, the δ rule, the constant form `c_ū` and the quote "the universe variables in α
   and ℓ are contained in ū" are all in **§2.5** (axioms.tex:96-107), not §2.4. Affected:
   the overview, `def:vlevel-wf`, `def:vlevel-inst`, `ind:vexpr`, `def:instl`,
   `struct:vconstant`, `struct:venv`, `def:venv-basic`, `def:vconstval`. All other thesis
   references check out (§2.1 grammar, §2.2 level judgements, §2.6.1 spec/telescope/ctor,
   §2.6.3 recursor and motive κ, §2.6.4 ι rule and K-like reduction, §2.7.1 quotients;
   `typesys.tex` labels `thm:weak`, `thm:subst`, `item:subst_ty` all exist).
2. **`lamBinders` "exists solely to state `foldr_lam_lamBinders`, which is used twice, from
   `Theory/Proj.lean`".** Both halves false. `lamBinders` is used directly at
   `Verify/Environment/Lemmas.lean:1128` (`rhs.lamBinders.map (VExpr.instL (uss i))`), and
   `foldr_lam_lamBinders` is used at `Verify/Environment/Lemmas.lean:1133,1134`. Nothing in
   `Theory/Proj.lean` mentions any of the three.
3. **`lamBinders_length` "has no consumer: it is a `@[simp]` lemma that only ever fires on
   itself".** Not supportable. It is `@[simp]`, and the arity side condition at
   `Verify/Environment/Lemmas.lean:1132` (`by simp [hla]; omega`, with
   `hla : rhs.lamArity = np + nm + nmin + nf` destructured from `RuleShape`) needs exactly
   `lamBinders.length = lamArity` to close. Calling it dead is wrong.
4. **`fam:subst-liftn-algebra`: "four of the five are consumed from `Theory/Proj.lean`".** All
   five are: `Subst.lift_liftN` (Proj.lean:171,281), `Subst.liftN_liftN` (177,349,377),
   `Subst.lift_lift_l_id` (368), `Subst.liftN_lift_l_id` (343,369), `Subst.Fixes.liftN` (189).
5. **`fam:subst-liftn-algebra` proof: "All five by structural recursion on the number of lifts,
   the step being `congrArg Subst.lift` applied to the induction hypothesis".** Only
   `lift_liftN` and `liftN_liftN` are that. `Subst.lift_lift_l_id` is not a recursion at all
   (`rw [Subst.lift_l_lift, id_lift]`), `liftN_lift_l_id` recurses by `rw`, `Fixes.liftN`
   recurses through `Fixes.lift`.
6. **Contribution summary: "the stability lemmas `fam:pibinders-stability` and
   `fam:ctorheaded-stability` are what `Theory/Proj.lean` actually consumes".** Wrong consumer
   for `fam:pibinders-stability`: `piBinders_lift'`, `piBinders_instL` and `piArity_instL` are
   used from `Verify/Typing/Lemmas.lean:652,1598` and `Verify/Environment/Lemmas.lean:1051`,
   never from `Theory/Proj.lean`. Of `fam:ctorheaded-stability`, only `CtorHeaded.inst` and
   `piArity_inst_of_ctorHeaded` go to Proj.lean; `piBinders_inst_of_ctorHeaded` goes to
   `Verify/Typing/{Lemmas,Expr}.lean`.
7. **`mod:theory-root`: "The last import (line 5) is the single line the `iota` branch added".**
   Line 5 (`Theory.Typing.InductiveParams`) is the fifth of six imports and is indeed the only
   `I` line in the blame; the last import is line 6, `Theory.Typing.HeadReduction`, which is
   master. The surrounding prose also listed the imports out of file order, which is what made
   "last" look right.
8. **Overview: the two thesis gaps are "both recorded in the code's own docstrings".** Only the
   K-like-reduction gap is (`VDecl.lean:32` and `Inductive.lean:251`). The `defeqs`-vs-`pats`
   duplication is recorded nowhere; `Theory/Quot.lean` has no docstrings.
9. **`inst:dec-closedn`: the theory/test split "is nowhere written down".** The module docstring
   of `Lean4Lean/Tests/ShapeDecide.lean` (lines 3-11) does state the general policy. What is
   undocumented is why `decClosedN` is the exception — which is the interesting part, since it
   is the instance a *definition* needs (`if h : ru.rhs.Closed` in `VEnv.addRecRule`,
   `Inductive.lean:258`). The chapter's justification of the need itself is correct.
10. **`fam:vlevel-lattice` proof: "closes by `simp` or `omega` on `Nat`".** `Theory/VLevel.lean`
    contains no `omega` (grep count 0). The `≤` lemmas are term-mode applications of the
    matching `Nat` lemma under the `∀ ls`; the `≈` lemmas are `simp [equiv_def, eval]`.
11. **`def:subst`: "Substitutions form a monoid under `Subst.comp`".** Neither associativity nor
    unitality of `Subst.comp` is stated anywhere; only `Subst.comp_lift` and the action law
    `subst_subst`.
12. **`fam:levelsat-eval`: `small n` "is at most 1 exactly when the rails encode a consistent
    assignment with values in {0,1}".** There is no biconditional. There are three separate
    one-directional lemmas: `le_eval_small` (domination), `two_le_eval_small` (≥ 2 on an
    inconsistent variable), `eval_small_le_one` (≤ 1 under two hypotheses).
13. **`fam:subst-trunc-orphans` / review note 1: "four master declarations dead".** Six:
    `lift_r_one`, `Subst.lift_r_comm`, `Subst.trunc`, `Subst.Depth.one`, `Subst.Depth.id`,
    `Subst.Depth`. The overview's "roughly ten contributed declarations have no consumer" was
    also unverifiable as stated; the defensible count is seven (five unmentioned, two feeding
    one of those five).
14. **`def:getmajoridx` review note: "the `getFirstIndexIdx` occurrences in
    `Lean4Lean/Inductive/Reduce.lean` are Lean's own field".** True but incomplete — it omitted
    the eight occurrences in `Verify/TypeChecker/WHNF.lean` (also on a kernel `rval`) and the
    comment in `Theory/Typing/Pattern.lean:532`, which is where a reader would look first to
    disprove the "never used in the verification layer" claim.
15. **`def:quot-consts`: "`Quot.sound` … is added elsewhere" (vague to the point of being
    unverifiable).** Made precise: in Lean 4 `Quot.sound` is an ordinary `axiom`, not one of the
    four quotient primitives (`Lean4Lean/Quot.lean:39`'s `Environment.addQuot` checks the same
    four names), so it reaches the model through the generic `VDecl.axiom` path.

Claims checked and **confirmed** (not refuted), for the record: all 32 `\contrib` badges match
`.blueprint-work/blame/` exactly, including the three `mixed` splits (`bvarsDesc` 1081/1083
iota vs `getElem_bvarsDesc` 1085 trproj; `lamArity`/`lamBody` iota vs `lamBinders`/length/foldr
trproj; `VEnv.empty`'s `pats _ _ := False` line alone). The line census (1786 master / 254 iota
/ 195 trproj of 2235, and the 372-line block at VExpr.lean:963-1334) reproduces exactly from
the blame files. `RecHeaded.not_ctorHeaded` really is consumed by
`VEnv.PatsIota.rec_ne_ctor` (`Theory/Typing/InductiveParams.lean:157`).
`eq_const_mkApps_append_iff` really is what makes `CtorResult_iff` and `ValidIndApp_iff`
decidable (`Theory/Inductive.lean:58,79`). All proof sketches for the contributed `trproj`
lemmas name the tactics the Lean proofs actually use. No node has a proof `\leanok` it should
not have: no declaration in these eight modules contains a `sorry`, direct or transitive.

## Fixes applied to the tex

Only `blueprint/src/chapters/syntax.tex` was modified.

- Replaced all 9 `\S2.4` thesis references with `\S2.5`, and added a one-sentence note in the
  overview fixing the numbering basis so the convention is auditable.
- Rewrote `def:vlevel-le-equiv`'s `\thesisref` to point at §2.2's algorithmic `ℓ ≤ ℓ'+n` /
  `ℓ ≡ ℓ'` judgements and the sort congruence rule, noting that the constant congruence rule is
  §2.5.
- Added the missing `\srcloc` to `ind:vlevel` (VLevel.lean:8) and `ind:vexpr` (VExpr.lean:7);
  these were the only two nodes in the chapter without one.
- `mod:theory-root`: imports relisted in file order; "the last import (line 5)" corrected to
  "the fifth import (line 5, `InductiveParams`)", with line 6 named as the master last import.
- Overview: split the two thesis gaps, with `\srcloc`s for the docstrings that record the
  K-like one and an explicit statement that the second is recorded nowhere; corrected the dead
  counts to seven contributed and a six-declaration master block; added that no declaration in
  these files has `sorryAx`; replaced "quantifier-free biconditionals" with an accurate
  description.
- `fam:vlevel-lattice` proof rewritten to describe the actual proof style and to state that no
  `omega` occurs in the file.
- `def:subst` rewritten to state `comp_lift` and the action law instead of claiming a monoid.
- `fam:subst-liftn-algebra` proof rewritten per lemma, with the corrected "all five" consumer
  claim and the Proj.lean line numbers.
- `fam:mkapps-stability` proof: the "all four consumed later" claim made concrete with
  consumers; added `def:lift-prime` to the statement `\uses` (the statement mentions `lift'`);
  no cycle introduced (`check_global.py`: 0 cycles).
- `def:lam-telescope` review note replaced: records the single real consumer
  (`Verify/Environment/Lemmas.lean:1128-1134`), explains that `lamBinders_length` is reached
  through `simp` and should not be called dead.
- `def:getmajoridx` review note and the matching Review-notes bullet: all the non-`VRecursor`
  `getFirstIndexIdx` sites enumerated with `\srcloc`s.
- `inst:dec-closedn` review note rewritten: names the commit that moved the sibling instances,
  credits the ShapeDecide module docstring for the general policy, and locates the real gap
  (the unexplained exception) plus the `addRecRule` line that forces it.
- `fam:subst-trunc-orphans` review note and Review-notes bullet 1: six orphaned declarations
  named with line numbers, master's actual one-line proof quoted, and the surviving
  `Experimental/SExpr.lean` copies noted.
- `fam:levelsat-eval` statement rewritten as three one-directional lemmas.
- `def:quot-consts`: `Quot.sound`'s status made precise with the kernel-side `addQuot` srcloc.
- `def:venv-addquot` review note and its Review-notes bullet: "unifying them was explicitly not
  attempted" replaced with the verified fact that the duplication is acknowledged nowhere in
  the code.
- `thm:eq-mkapps-append` proof: "the right-hand sides are quantifier-free" replaced with what
  the right-hand sides actually are (spine equality + `List.IsPrefix` + length equation), with
  the ShapeDecide instances cited.
- Contribution summary: the consumer paragraph rewritten to split `Theory/Proj.lean` consumers
  from `Verify`-layer consumers; the `VEnv.LE` cost made concrete; the open-problems paragraph
  given the corrected dead list by name.

Checker state after the fixes: `check_chapter.py` reports 0 errors and 1 warning, and
`check_global.py` reports 980 labels, 2865 uses edges, 0 cycles, 0 errors. The single warning
is `mod:theory-root: no \lean{}`, which is expected and not real: the node describes a module
(`Lean4Lean/Theory.lean`), not a declaration, and the node body says so. `rebuild_registry.py`
was re-run.
