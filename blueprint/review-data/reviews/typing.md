# Review of chapter typing

Scope: `blueprint/src/chapters/typing.tex` (50 nodes), checked against
`Lean4Lean/Theory/Typing/{Basic,Env,Lemmas,EnvLemmas,Meta,QuotLemmas,Injectivity}.lean` at
HEAD 20ec229, against `master` (`git show master:…`, `git diff master...HEAD`), against
`.blueprint-work/blame/`, `understand/decls.tsv` and `understand/registry.tsv`.
All 21 contributed (`iota`/`mixed`) nodes were opened at their `\srcloc`; 18 master nodes
were opened as well (def:lookup, def:hastype-istype, def:vdecl-wf, def:venv-wf, fam:ctx-lift,
fam:lookup-struct, def:onctx, def:ontypes, fam:defeqdfc, thm:isdefeq-instdf, fam:substeq,
fam:typing-meta, thm:addquot-wf, fam:addquot-objs, fam:addconsts, thm:wf-ordered,
thm:injectivity-open, thm:foralle-inv-derived).

## Quality verdict

The `iota` contribution in this group (381 of 1713 lines, no `trproj` line) is real work, not
slop: every added declaration carries a docstring that states its purpose, its thesis
section and its limitation, and the central design choice is documented together with the
counterexample that shows it is not free (`EnvLemmas.lean:323-333`). The technically good
idea is the split of rule admissibility into `PatTyped` (a `VDefEq.WF` analogue) and
`TemplateHeaded` (a shape condition): because `TemplateHeaded` is monotone
(`PatWF.mono`) and recoverable from the environment (`Ordered.patHeaded`), the Π and sort
inversion lemmas survive a schematic reduction rule with a one-line case each
(`Lemmas.lean:851, 895`) instead of needing the open Π-injectivity of `Injectivity.lean`.
The nine `pat` cases added to inductions over `IsDefEq` are minimal (1-6 lines), no master
lemma gained a hypothesis, and only two master lines were deleted (the `VEnv.LE` anonymous
constructors in `addConst_le`/`addDefEq_le`, which grew a `pats` component).
The cost is concentrated and honestly placed but large: `VEnv.WF.patsStrong`
(`EnvLemmas.lean:334`) is `sorry`, a `CoeOut (VEnv.WF env) env.OrderedStrong` instance
(`:343`) makes every `VEnv.WF` hypothesis silently deliver it, and 343 constants now depend
on it — the widest reach of any hole in the non-experimental project, where master's
corresponding entry point `Ordered.strong` was a proved theorem in a `sorry`-free file.
The `EnvLemmas.lean` bootstrap (~200 lines replacing master's eleven) is correct but noisy:
`PatsStrong` takes both environments explicitly plus six positional hypotheses, so all eight
call sites read `hp _ _ hpre₀ .rfl … rfl rfl hord`, and `addQuot_strong` hand-unrolls the
quotient chain into 25 lines of `.trans` plumbing.

## Confirmed code issues

- `Lean4Lean/Theory/Typing/EnvLemmas.lean:334` — **high**. `VEnv.WF.patsStrong` is `sorry`
  (axioms `propext, sorryAx, Quot.sound`). With the `CoeOut` instance at line 343 it is
  reached from any `VEnv.WF` hypothesis with no visible cue; 343 constants depend on it
  (reverse reachability, `understand/reader-summaries.md:235`). `Verify/Primitive.lean`
  mentions `OrderedStrong`/`orderedStrong` in 30 places, all added on this branch (master: 0),
  and `Verify/Environment/Primitive/*` uses `ctx.Ewf.orderedStrong` 27 times.
- `Lean4Lean/Theory/Typing/Basic.lean:60` — **high**. `IsDefEq.pat` concludes
  `Γ ⊢ e ≡ r.1.apply m1 m2 : A` from `Γ ⊢ e : A` with no typing premise on the reduct, so with
  `IsDefEq.hasType` (`Lemmas.lean:248`) the judgment *assumes* ι subject reduction. The
  author's own counterexample (`EnvLemmas.lean:327-329`) shows it is false over a merely
  `Ordered` environment. `IsDefEqStrong.pat` (`Strong.lean:89`) has the premise and is the
  right shape.
- `Lean4Lean/Theory/Typing/Injectivity.lean:11,14,33` — **high (pre-existing, master)**.
  Three admitted inversion principles; the file is `git diff`-identical to master. They are
  what `patsStrong`'s docstring names as the missing ingredient.
- `Lean4Lean/Theory/Typing/Injectivity.lean:23` — **medium (new consequence, unchanged code)**.
  `IsDefEqU.forallE_inv` is byte-identical to master but now has two independent `sorry`
  sources: `forallE_inv_stratified` and, through `IsDefEq.strong`, `patsStrong`. `master`
  had `IsDefEq.strong (henv : Ordered env)` (`master:Strong.lean:689`); HEAD has
  `IsDefEq.strong (henv : OrderedStrong env)` (`Strong.lean:805`). A concrete instance of
  the `CoeOut` propagation.
- `Lean4Lean/Theory/Typing/Basic.lean:92` — **medium**. `VEnv.PatTyped` is existential in
  `U, Γ, e, m2, B` and `Pattern.RHS.Generic` (`Pattern.lean:181`) constrains only the holes
  the reduct *uses*, so a rule may be "typed" at one convenient instantiation; the unused
  holes (indices, the constructor's copy of the parameters) are arbitrary terms over `Γ`.
  The `Generic` docstring says so; the name `PatWF` does not.
- `Lean4Lean/Theory/Typing/EnvLemmas.lean:130` — **medium**. `PatsStrong` has explicit
  `env₁ env₀` and six positional hypotheses; call sites at lines 279, 282, 291, 293, 305,
  308, 316, 319 (eight, not six). Since it is only ever discharged by `sorry`, provability in
  this generality is unchecked, and `env₁` ranges over prefixes that already carry δ rules
  and `quotDefEq`.
- `Lean4Lean/Theory/Typing/EnvLemmas.lean:188` — **medium**. `addQuot_strong` hand-unrolls
  `addQuot` into `l1-l5 / d1-d4 / p1-p4 / O1-O4 / I1-I4` (lines 193-217); a sixth quotient
  constant means editing every `.trans` chain.
- `Lean4Lean/Theory/Typing/Basic.lean:62` — **medium**. The `Check`/`Realizes` side-condition
  machinery is exercised only at `Check.true`: the single registration point
  `VEnv.addRecRule` (`Inductive.lean:257`) hard-codes `.true` at line 264, and K-like
  reduction is explicitly not modelled (`Inductive.lean:332`). Seven lemmas
  (`OK.map`, `Realizes.toOK`, `OK.exists_realizer`, `map_liftN`, `map_instN`, `map_instL`,
  `map_subst`) plus one premise in each of nine induction cases serve no current consumer.
- `Lean4Lean/Theory/Typing/QuotLemmas.lean:19` — **low**. `addQuot_chain` re-derives with the
  same six `type_tac` calls the four constant typings `addQuot_WF` (`:7`) already proves;
  `addQuot_WF` could be a corollary.
- `Lean4Lean/Theory/Typing/Meta.lean:37` — **low (master defect, branch amplifies it)**.
  `type_tac` is a brute-force `first` chain with its own TODO. Call sites: 12 in
  `QuotLemmas.lean` (6 added by `addQuot_chain`) and 100 in the new, 100%-iota
  `Verify/Environment/Quot.lean` (615 lines, absent on master).
- `Lean4Lean/Theory/Typing/Basic.lean:58` — **low**. The `IsDefEq.pat` docstring cites
  `Params.pat_wf`, which is `VEnv.Params.pat_wf` in `ChurchRosser.lean:20` — a module that
  *imports* `Basic.lean`, so the reference is forward; an unrelated `Lean4Lean.Params.pat_wf`
  exists in `Experimental/SExpr.lean:30`.
- `Lean4Lean/Theory/Typing/QuotLemmas.lean:7` — **low**. The quotient computation rule is a
  `VDefEq` (δ on closed terms), not a `pats` entry, though the thesis calls it ι; a proof of
  `patsStrong` must handle this asymmetry since every WF prefix carries it.
- `Lean4Lean/Theory/Typing/Lemmas.lean:267` — **low**. `OnTypes` says nothing about `pats`,
  which is the structural reason `Ordered.induction` cannot carry `PatsStrong` and the
  200-line `EnvLemmas` rewrite was needed. A `pats`-aware `OnTypes` is not attempted.

## Refuted claims

Claims that were in the chapter and are false; all corrected in the tex.

1. **"axiom and opaque (add a constant whose type is a type)"** (def:vdecl-wf). False for
   `opaque`: `VDecl.opaque` takes a `VDefVal` and its premise is `VDefVal.WF`
   (`Env.lean:8,32-35`), i.e. the *value* must be typed, exactly as for `def`; it differs
   from `def` only in not adding the δ rule. `example` likewise requires `VDefVal.WF`.
   Only `axiom` (a `VConstVal`) has the "type is a type" premise.
2. **"a five-line case added to each of the ten inductions over `IsDefEq`"** (overview and
   Contribution summary). Nine inductions over `IsDefEq` gained a `pat` case
   (`Lemmas.lean:369, 412, 528, 573, 668, 729, 848, 892, 937`), of 1, 1, 4, 6, 6, 6, 4, 4 and
   3 lines; `Ordered.induction` (line 299) — which the chapter listed among them — is an
   induction over `Ordered`, as are `constWF` (449) and `defEqWF` (462).
3. **"four new lemmas"** (overview). Six: `addPat_le`, `addPat_self`, `PatTyped.mono`,
   `PatWF.mono`, `Ordered.patWF`, `Ordered.patHeaded` (`Lemmas.lean:198, 200, 464, 468,
   474, 488`), plus the two new predicates in `Basic.lean`.
4. **"master's twelve-line entry point … in `EnvLemmas.lean`"**. `Ordered.strong` was eleven
   lines (`master:Strong.lean:675-685`) and lived in `Strong.lean`; `master`'s
   `EnvLemmas.lean` ends at the `CoeOut … Ordered` instance (line 106), exactly where the
   blame file switches from M to I.
5. **"`Verify/Primitive.lean` … in 31 places"**. 30 occurrences of
   `OrderedStrong`/`orderedStrong` (20 + 10); master has 0.
6. **"`type_tac` is used on five closed terms only"**. 12 call sites in `QuotLemmas.lean` and
   100 in `Verify/Environment/Quot.lean`, all of the latter contributed.
7. **"a different `Params.pat_wf` also exists under `Experimental/ShapeLogRel.lean`"**. The
   second declaration is `Lean4Lean.Params.pat_wf` in `Experimental/SExpr.lean:30`
   (`all-constants.tsv`); `ShapeLogRel.lean` only uses it.
8. **"Both [`VDecl.WF.le` and `WFPrefix.le`] are used only inside `VEnv.WF.strong`"**.
   `VDecl.WF.le` is used only by `WFPrefix.le` (`EnvLemmas.lean:123`); only `WFPrefix.le` is
   used in `WF.strong` (line 274).
9. **"`addConsts` succeeds exactly when every name is fresh and the block's names are
   pairwise distinct"**. Only the "if" direction is proved (`exists_addConsts`,
   `EnvLemmas.lean:26`); there is no converse lemma.
10. **"`addRules` … stage 4 of `addInduct`"**. It is the last of four stages, but the source
    numbers stages from zero ("Stages 0-1", "Stages 0-2", `Inductive.lean:296,300`) and calls
    it stage 3, as does the `addRules_strong` docstring (`EnvLemmas.lean:174`).
11. **"since it now routes through `IsDefEq.strong`"** (thm:foralle-inv-derived). The routing
    is master's; `Injectivity.lean` is unchanged. What changed is `IsDefEq.strong`'s
    environment hypothesis (`Ordered` → `OrderedStrong`).
12. **Missing hypotheses.** `addDefEqs_strong` (`EnvLemmas.lean:162`) also requires
    `OnTypes env (EnvStrong env)`; `IsDefEq.instDF` (`Lemmas.lean:952`) also requires
    `Ordered env` and `OnCtx Γ (env.IsType U)`. Both were stated without them.
13. **"Injectivity.lean … states three inversion principles that are admitted"**. It also
    derives a fourth lemma (`forallE_inv`, line 23) from them, which the chapter itself
    nodes separately.

Claims checked and **upheld** (no change): the per-file line counts 237/74/29/27/14 of
343/1059/105/60/66 and "no `trproj` line" (blame); `Meta.lean` and `Injectivity.lean`
untouched (`git diff` empty); every `\srcloc` line number for a contributed `pat` case
(369-371, 412, 449, 462, 528-531, 573-578, 668-673, 729-734, 848-851, 892-895, 937);
the axiom footprints of `patsStrong` (`sorryAx, Quot.sound, propext`), `orderedStrong`
(`+ Classical.choice`) and `forallE_inv` (decls.tsv); `WF.strong` is *not* sorry-tainted
itself; master's `VInductDecl.WF`, `VEnv.addInduct` and `addInduct_WF` were `sorry`
(`master:Inductive.lean:5,7`, `master:InductiveLemmas.lean:10`); the 343-constant reach;
`ChurchRosser.lean` does not mention `OrderedStrong` (so the suggested proof route is open,
not circular); `Params` requires `env.WF` (`ChurchRosser.lean:14`) and `toParams`
(`InductiveParams.lean:393`) builds it from `henv.pat_*`; all 40 `\ref` targets resolve.

## Fixes applied to the tex

1. Overview: `Injectivity.lean` described as three admitted principles **plus one derived
   lemma**.
2. Overview "Contributions": six new lemmas named; "nine inductions over `IsDefEq`, cases of
   one to six lines" + "three inductions over `Ordered`"; the two deleted master lines
   recorded; `Ordered.strong` relocated to `Strong.lean` and recounted as eleven lines; the
   rewrite attributed to `Env.lean`/`QuotLemmas.lean`/`EnvLemmas.lean`, not `EnvLemmas` alone.
3. Overview "Assessment" and Contribution summary: master's inductive layer restated as two
   `sorry`-ed definitions **and** a `sorry`-ed soundness theorem.
4. def:vdecl-wf: correct premises for `axiom`, `def`, `opaque`, `example`.
5. fam:addconsts: "succeeds exactly when" → "succeeds if (only that direction is proved)".
6. thm:vdecl-wf-le proof: correct consumer chain (`VDecl.WF.le` → `WFPrefix.le` → `WF.strong`).
7. def:patsstrong review note: eight call sites, listed.
8. thm:adddefeqs-strong: added the `OnTypes E (EnvStrong E)` hypothesis.
9. thm:addrules-strong: "stage 4" → last of four, with the source's zero-based numbering noted.
10. thm:isdefeq-instdf: added `Ordered` and `OnCtx` hypotheses.
11. thm:isdefeq-closedn proof: removed the spurious `\uses{family:pattern-transport-master}`
    (the `pat` case uses only `apply_closedN`/`Matches.closedN`, both iota).
12. thm:foralle-inv-derived proof: the second gap explained as a hypothesis change in
    `IsDefEq.strong`, not new routing.
13. fam:typing-meta: real `type_tac` usage (12 + 100 call sites).
14. fam:patwf-mono proof: "two lines each" → "one line of proof each".
15. fam:addpat proof: "the same commit" → "the same change" (commit identity not verified).
16. Contribution summary: induction-case counts and line range corrected.
17. Review notes: 31 → 30 `OrderedStrong` places; `Check.true` cited at the registration point
    `addRecRule` (`Inductive.lean:257`, check at 264) instead of `rules_wf`; the seven
    `Check` lemmas named; eight `PatsStrong` call sites; `SExpr.lean` instead of
    `ShapeLogRel.lean` for the second `Params.pat_wf`, with the forward-reference point added;
    the `type_tac` note rewritten around the real call-site counts; **new Medium note** on
    `Injectivity.lean:23` silently acquiring the `patsStrong` taint without a source change.

`check_chapter.py typing.tex`: 50 nodes, 0 errors, 0 warnings.
`check_global.py`: 980 labels, 2863 uses edges, 0 cycles, 0 errors.
