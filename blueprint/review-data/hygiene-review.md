# Whole-diff hygiene and "slop" review — `master..trproj`, `Lean4Lean` + `Main.lean`

Scope: `git diff master..trproj -- Lean4Lean Main.lean` = **+7762 / −363** over 49 files, read
in full (Theory/ and Verify/ first). Quantitative claims below come from the per-line blame
tags in `../blame/` (M = master, I = iota, P = trproj-only), from `git log --stat master..trproj`,
and from greps over the working tree at HEAD `20ec229`.

Baseline numbers used throughout:

| | code lines | comment lines | declarations | code/decl | comment % |
|---|---|---|---|---|---|
| master (M) | 18531 | 2327 | 1698 | 10.9 | 10.2 % |
| iota (I) | 3720 | 942 | 518 | 7.2 | 18.4 % |
| trproj (P) | 1871 | 496 | 295 | 6.3 | 18.8 % |
| — Theory/ M | 4404 | 78 | 518 | 8.5 | **1.7 %** |
| — Theory/ I + P | 2410 | 816 | 344 | 7.0 | **25.3 %** |
| — Verify/ M | 11580 | 1802 | 964 | 12.0 | 13.5 % |
| — Verify/ I | 1253 | 157 | 172 | 7.3 | 11.1 % |
| — Verify/ P | 807 | 187 | 36 | 22.4 | 18.8 % |

Tactic density (share of that branch's code lines): bare `simp` M 6.8 % / I 2.8 % / P 2.7 %;
`simp only` M 1.2 % / I 1.5 % / P 2.7 %; `omega` M 0.4 % / I 0.2 % / **P 2.0 %**;
`decide` M 0.2 % / I 0.9 % / **P 1.1 %**.
Added lines containing `native_decide`, `maxHeartbeats`, `maxRecDepth`, `unsafe` (as a modifier),
`partial`, `noncomputable`, `admit`: **zero**. `sorry`: **5 added, 12 removed**.

---

## (a) Statement quality

- **HIGH** `Lean4Lean/Verify/TypeChecker/InferType.lean:407` — `inferProj.WF` is kept as a
  `sorry` whose own docstring says it is "not provable as stated", yet `inferType'.WF` (:479)
  consumes it, so `checkType.WF`/`inferType.WF'` rest on a statement the author believes false
  for projections outside `TrProj`'s scope.
- **MEDIUM** `Lean4Lean/Theory/Typing/Basic.lean:92` — `VEnv.PatTyped` is existential in
  `U, Γ, e, m2, B`, so "the rule is typed" means only that *some* instantiation is typable; it is
  the gate `Ordered.pat` registers a rule on, and the name oversells it.
- **MEDIUM** `Lean4Lean/Theory/VEnv.lean:44` — `addPat` is total, with no freshness or
  consistency check (unlike `addConst`), so an `Ordered` environment may carry two conflicting
  reducts for one pattern; functionality is only recovered later from `VEnv.WF`
  (`PatsIota.functional`, `InductiveParams.lean:180`).
- **MEDIUM** `Lean4Lean/Theory/Typing/EnvLemmas.lean:130` — `VEnv.PatsStrong` takes explicit env
  arguments plus six positional hypotheses; call sites read `hp _ _ hpre₀ .rfl … rfl rfl hord`
  (:279, :282, :291, :293, :305, :308), an interface unlike anything upstream in this file.
- **MEDIUM** `Lean4Lean/Theory/VExpr.lean:1232` — `CtorHeaded.forallE` is proved `:= h`, i.e.
  definitionally trivial (`piBody (forallE A B) = piBody B`), and has no consumer.
- **LOW** `Lean4Lean/Theory/Inductive.lean:196` and `:202` — `RecShape.one_le_numMotives` and
  `RecShape.majorFormer?_eq` have no consumer anywhere in the repo.
- **LOW** `Lean4Lean/Theory/Inductive.lean:242` — `LargeElim.shape`, the only bridge from the
  typing-level `LargeElim` to the decidable `LargeElimShape`, has no consumer; the test uses
  `LargeElimShape` directly.
- **LOW** `Lean4Lean/Theory/VDecl.lean:51` — `VRecursor.getFirstIndexIdx` is defined and
  documented but never used; the ι code calls the kernel's homonym instead.
- **LOW** `Lean4Lean/Theory/Proj.lean:205` — `@[simp] instFields_nil` is the defining equation
  stated as a `rfl` lemma, and is unused.
- **LOW** `Lean4Lean/Theory/Typing/InductiveParams.lean:37` — `app_subpattern_iota` is
  `(app_subpattern_iota' hs).1`, a wrapper around one projection of the lemma above it.
- **LOW** `Lean4Lean/Theory/Proj.lean:127` — `projTy`, documented as "the kernel's `inferProj`
  result", is referenced only by one `example` in `Tests/ProjShape.lean`; `TrProjCtor` types the
  projection through `projMotiveBody` instead, so the two readings of the same thing coexist.

## (b) Proof quality and brittleness

- **HIGH** `Lean4Lean/Theory/Typing/EnvLemmas.lean:334` — `VEnv.WF.patsStrong` is `sorry`; via
  the `CoeOut` at :343 plus 158 mechanically-rewritten master call sites (`Ordered` →
  `OrderedStrong`, counted by diffing the hunks), the strong system, the typing inversions,
  `Verify/Primitive*`, and the type-checker layer become conditional where master had them proved.
- **MEDIUM** `Lean4Lean/Verify/Environment/Lemmas.lean:523`, `:674`, `:826`, `:449` — four
  separate 10-case inductions over `TrEnv'` (111 + 72 + 74 + 52 = 309 lines) repeat the same
  per-constructor boilerplate (`rw [map_wf.find?_insert]; split; …`); only `pats_iota_inv_shape`
  factors its step through a helper (`IotaRule.step`).
- **MEDIUM** `Lean4Lean/Verify/Typing/Lemmas.lean:641`, `:1296`, `:1588` — `TrProj.weak'`,
  `.instN` and `.instL` each rebuild the same eight-field `TrProjCtor` record with the same
  `by rw [hlen]; exact H.…` per field; the "prove once against `subst`" factoring advertised in
  `Theory/Proj.lean:186` stops at the builder level and is not carried up to these three.
- **MEDIUM** `Lean4Lean/Verify/Environment/Lemmas.lean:1021` — `TrEnv.proj_defeq`, 131 lines, is
  the branch's longest proof: `generalize hM …; generalize hN …; revert r hpat` gymnastics,
  ~12 `omega`s, eight `by simp; omega` side conditions, and six `rw [show … by omega]` rewrites.
- **MEDIUM** `Lean4Lean/Verify/TypeChecker/WHNF.lean:17` — `inductiveReduceRecCore.WF`, 124
  lines, hand-splits `as`/`cargs` with `take`/`drop` and discharges nine index side conditions
  with `simp; omega`; brittle against any change to `mkAppRange_eq`'s shape.
- **MEDIUM** `Lean4Lean/Theory/Typing/EnvLemmas.lean:188` — `addQuot_strong` hand-unrolls five
  `addQuot` steps into `l1…l5 / d1…d4 / p1…p4 / O1…O4 / I1…I4` chains (~25 lines) that
  `foldlM_addConst_strong` would cover if `addQuot` were a fold rather than a bind chain.
- **MEDIUM** `Lean4Lean/Verify/Environment/Lemmas.lean:1021` (representative) — trproj's `omega`
  density is 5× master's (2.0 % vs 0.4 % of code lines) and its `decide` density 5× (1.1 % vs
  0.2 %); both are concentrated in `proj_defeq` and `inductiveReduceRecCore.WF`.
- **LOW** `Lean4Lean/Verify/Environment/Quot.lean:521` — `hn1 … hn4` repeat the same five-line
  `rw [addQuot, if_neg …]; generalize; cases` block four times, differing only in the constant
  name and the growing `simp only [hn1, hn2, …]` prefix.
- **LOW** `Lean4Lean/Verify/Environment/Quot.lean:584` — the `safePrimitives` field nests
  `Environment.find?_add_of_ne` chains four deep, writing the inner chains out twice; ~15 lines
  that read as machine-expanded rather than authored.
- **LOW** `Lean4Lean/Verify/Environment/Quot.lean:27` — ~30 `abbrev`s named
  `ng0/x1…x6/u/v/L1…L6/T1…T4/q1…q4/T1'…T4'`; reducibility is load-bearing for the `decide`s and
  `rfl`s, but it is a dense reducible surface in one namespace.
- **LOW** `Lean4Lean/Tests/ProjShape.lean:164`, `:166`, `:174` — four `by decide` on `VExpr`
  equalities of the `Sigma` expansion; kernel-evaluated `DecidableEq VExpr` at that term size is
  a latent build cost with no error message when it regresses.
- **LOW** non-terminal `simp` appears ~25 times in added lines, almost all of the harmless
  `simp [List.foldlM] at h; exact h ▸ …` shape (e.g. `Theory/Typing/InductiveLemmas.lean:92`);
  master uses bare `simp` 2.5× more densely, so this is not a divergence.

## (c) Documentation

I verified ~60 of the 369 added docstringed declarations against their statements
(all of `Theory/Inductive.lean` including its 24 `VInductDecl.WF` field docstrings, all of
`Theory/Proj.lean`, `Theory/VDecl.lean`, `Theory/VEnv.lean`, `Theory/Typing/Basic.lean`,
`Theory/Typing/Env.lean`, the `TrIndType`/`TrRecursor`/`AddInduct` fields, `TrProjCtor`'s seven
fields, and the `Pattern`/`Strong`/`EnvLemmas` additions). Six mismatches, all listed here; the
rest were accurate, and several are unusually good (they state *why* and name their own limits).

- **MEDIUM** `Lean4Lean/Theory/VExpr.lean:1232` — `CtorHeaded.forallE`'s docstring ("A
  `CtorHeaded` type is not a Π-telescope ending in a variable, so instantiation cannot create new
  leading binders") states a different proposition from the lemma
  (`(forallE A B).CtorHeaded → B.CtorHeaded`).
- **MEDIUM** `Lean4Lean/Theory/VExpr.lean:1047` — the section header still claims the telescope
  helpers come "with their decidability" after commit `ba118fd` relocated every such instance to
  `Lean4Lean/Tests/ShapeDecide.lean`.
- **LOW** `Lean4Lean/Verify/TypeChecker/InferType.lean:392` — `inferProj.WF_struct` is documented
  as being "for the structures the model covers (`TrProjCtor`)", but `TrProjCtor` occurs in none
  of its hypotheses, which are `InductiveVal`/kernel metadata facts.
- **LOW** `Lean4Lean/Theory/VExpr.lean:1008` — `subst_instN`'s docstring says "under `m` binders"
  while the statement binds `n`.
- **LOW** `Lean4Lean/Verify/Environment/Lemmas.lean:184` — `pull_insert` is documented as pulling
  back across "one fresh insertion", but freshness is not a hypothesis; the lemma needs only
  `q ≠ ci` (the values differ).
- **LOW** `Lean4Lean/Theory/Proj.lean:152` — `projMotiveBody_zero`'s docstring describes the
  motive `fun _ => Fs[0]`, the statement its *body* `(Fs.getD 0 default).lift`.
- **LOW** `Lean4Lean/Theory/Inductive.lean:257` — `addRecRule`'s docstring says the redex's major
  is "at `getMajorIdx`" while the definition inlines
  `numParams + numMotives + numMinors + numIndices`; equal by unfolding, but every consumer
  (`addRecRule_pats`, `addInduct_pat`, `rec_find`) restates it with `getMajorIdx`.
- **MEDIUM (volume)** `Lean4Lean/Theory/Proj.lean:3` — contributed `Theory/` code is **25.3 %
  comment lines against master's 1.7 %** in the same directory. Extremes: a 56-line module header
  on a 449-line file (`Theory/Proj.lean:3`) and a **27-line docstring on the 5-line
  `DefEqsAsPats`** (`Theory/Typing/InductiveParams.lean:351`, the longest docstring in `Theory/`;
  master's `Theory/` maximum outside `LevelSat` is 11 lines). This is the single loudest
  AI-authored-looking signal in the diff. Mitigating: master's own maxima elsewhere are
  comparable (105-line blocks in `Experimental/Stratified*.lean`, 57 in `Theory/LevelSat.lean`),
  and the long comments are substantive — derivations, thesis section numbers, explicit
  statements of what is *not* modelled — not restatements of the code.
- **LOW (positive)** `Lean4Lean/Tests/ProjInhabit.lean:564`–`:585` — `#guard_msgs in
  #print axioms` pins the axiom profile of the four `TrProjCtor` witnesses (`propext, Quot.sound`)
  and of `TrEnv.proj_defeq` (which shows `sorryAx`); the sorry inheritance is machine-checked
  rather than asserted in prose. No master file does this.

## (d) Consistency with upstream style

- **POSITIVE, quantified** — contributed declarations are *shorter* than master's in the same
  directories (Theory: 7.5 (I) / 5.6 (P) vs 8.5 code lines per declaration; Verify: 7.3 (I) vs
  12.0), and the longest contributed proof is 131 lines (`TrEnv.proj_defeq`) against master's
  887 (`unfoldNatWellFounded.WF'`), 359, 334, 319 and 231. "Very long tactic proofs" is not a
  defect of this branch. `Lean4Lean/Verify/Environment/Lemmas.lean:1021`.
- **POSITIVE** — zero added lines exceed the 100-column limit, zero carry trailing whitespace,
  two double-blank-lines in the whole diff (`Lean4Lean/Verify/Environment/Quot.lean:98`);
  naming follows upstream conventions throughout (`addRecRule_le`, `addConst_pats`,
  `foldlM_addConst_ordered`, `PatsIota.induct`, `WF.pat_uniq`, `.mono`/`.le`/`_iff`/`_eq`);
  edits to master's own inductions are surgical and uniform (one `| pat …` case per induction,
  no master lemma gained a hypothesis except the forced `Ordered → OrderedStrong`).
- **LOW** `Lean4Lean/Verify/Environment/Basic.lean:272` — the contribution prefers
  `structure … : Prop where` with named fields (`AddInduct`, `TrIndType`, `TrRecursor`,
  `TrProjCtor`, `PatsIota`, `OrderedStrong`, `TrEnv'.IotaRule`) where master models the analogous
  `AddQuot` as a nested `AddQuot1` existential chain and `TrConstant`/`TrConstVal` as
  `def … : Prop := _ ∧ _`. Better engineering, but a visible stylistic break.
- **LOW** `Lean4Lean/Verify/LocalContext.lean:183` — a global `instance : DecidableEq FVarId`
  for a Lean-core type (core genuinely lacks it — `#synth` fails) is declared inside
  `namespace Lean.LocalContext`, so it is named `Lean.LocalContext.instDecidableEqFVarId`, and it
  sits directly under a section header about "the empty context".
- **LOW** `Lean4Lean/Tests/ProjInhabit.lean:469` — ~50 namespace-level `theorem`s named `hbeta5`,
  `hc5`, `hbetax21`, `hmSpine2'`, `hselnat0` for one-use intermediate steps; upstream would write
  these as `have`s inside one proof, or at least `private`.
- **LOW** `Lean4Lean/Tests/ProjShape.lean:155` — `def usS`, `def ps`, `def Fs`, `def structTy`,
  `def P₀` at namespace level with maximally generic names, inside a `section` that does not
  scope them.

## (e) Churn

- **MEDIUM** `Lean4Lean/Verify/Environment/Lemmas.lean:1` — non-merge commits total
  **+11439 / −3399** against a net **+7762 / −363**, so roughly **3.0k of the branch's own lines
  (≈27 % of what was written) were written and then removed inside the branch**. Worst offenders
  by commit count: `Verify/Environment/Lemmas.lean` 22 commits +1734/−678;
  `Theory/Typing/InductiveParams.lean` 14 commits +1039/−576 (over half rewritten);
  `Verify/Environment/Basic.lean` 12 commits; `Theory/Typing/InductiveLemmas.lean` 11.
- **MEDIUM** `Lean4Lean/Theory/Typing/Pattern.lean:1` — a whole file
  `Lean4Lean/Theory/Pattern.lean` was created over 4 commits (+251 lines, `cb920e1 refactor:
  relocate Pattern core to Theory/Pattern`) and then deleted again (`3bbdb22 refactor: keep
  Pattern.lean in Theory/Typing (revert M0 relocation)`); it does not exist at the branch tip.
- **LOW** `Lean4Lean/Theory/Proj.lean:1` — 5 commits, +794/−345: `d7ec0fa refactor(theory): derive
  the projection builders' lift and inst lemmas from subst` discarded roughly the earlier half of
  the file's lemma set and re-derived it.
- **LOW** `Lean4Lean/Verify/Typing/Expr.lean:90` — `TrProjCtor` was first a
  `def … : Prop := ∃ …` and re-cut as a structure by `e9fefbe`; `TrEnv.proj_defeq` was exposed
  (`b6a5a38`), recorded as unreachable by the `rec_reg` route (`7f62db2 docs: record corrected
  proj_defeq residual`), and then proved by a different route (`e202975`).
- **LOW** git history — two commits share a patch-id (`655dd3f` / `75ffde9`, "pin the ι reduct's
  recursive-argument count") and two more share a subject (`7a68882` / `6fd8a1d`, "refine recursor
  reduction by the registered ι rules"): the branch carries duplicated commits from re-merging a
  rebased `iota`. An upstream maintainer would ask for a rebase before review.

## (f) Kernel edits — the artefact being verified

Both edits were checked by reading master's and trproj's versions side by side.

- **VERIFIED behaviour-preserving** `Lean4Lean/Inductive/Reduce.lean:75` — the 21 trproj lines
  extract the ι step verbatim into a pure `inductiveReduceRecCore`, with `inductiveReduceRec`
  reduced to `return inductiveReduceRecCore info ls recArgs major`. Same operations in the same
  order; `majorIdx` was bound as `info.getMajorIdx`, so `rval.getMajorIdx` is the same index;
  `let some rule := … | none` and `if c then none` inside the `Option` do-block short-circuit
  exactly where master's `| return none` / `return none` did. `majorIdx` remains live for
  `recArgs[majorIdx]?`. **No executable behaviour change.**
- **LOW** `Lean4Lean/Inductive/Reduce.lean:75` — the new definition sits inside the `section`
  whose `variable`s are `[Monad m] (env) (whnf) (inferType) (isDefEq)` and uses none of them; the
  arity is right today only because Lean binds `variable`s on use, so a future reference to `env`
  would silently change the signature `inductiveReduceRecCore.WF` is stated about.
- **MEDIUM, deliberate and documented** `Lean4Lean/Quot.lean:24` — the single iota kernel line
  `if info.isUnsafe then fail "'Eq' type is unsafe"` **does change executable behaviour**:
  `checkEqType` now rejects an environment whose `Eq` is declared `unsafe`, where the C++
  `quot.cpp`'s `check_eq_type` pins the shape of `Eq` but not its safety. It is the change that
  discharges the former `Environment.EqSafe` assumption and makes `addQuot.WF`/`addDecl.WF`
  unconditional, and it is documented as a divergence in `divergences.md:7` by the same commit
  (`30897c0`), alongside the pre-existing prelude-check divergences.
- **LOW** `Lean4Lean/Quot.lean:24` — the new check never fires on imported environments:
  `Environment.addQuot` returns early when `env.quotInit` is true and
  `Lean4Lean/Environment/Basic.lean:124` sets `quotInit := !imports.isEmpty`, so the removed
  `EqSafe` assumption is replaced only for from-scratch environments. Not stated anywhere.

## (g) AI-generated filler / redundancy

- **HIGH (value, not hygiene)** `Lean4Lean/Verify/Environment/Basic.lean:272` — the whole
  `AddInduct` layer (a 619-line `Basic.lean` plus ~1000 lines of lemmas across
  `Basic.lean`/`Lemmas.lean`/`InductiveLemmas.lean`) has **no producer**: `addDecl.WF`'s
  `inductDecl` case is still master's `sorry` (`Lean4Lean/Verify/Environment.lean:208`), so no
  verified path ever constructs an `AddInduct` witness. Master's `AddInduct` was literally
  uninhabited ("essentially a `sorry`"), so this is a strict improvement in specification with
  the closing step still open — but every theorem in the layer is currently hypothetical.
- **MEDIUM** `Lean4Lean/Theory/Typing/Pattern.lean:499`–`:680` — `RHS.spine`, `spine_foldl_var`,
  `RHS.iotaCounts`, `iotaPaths_countP_isLeft`, `iotaPaths_countP_isRight`, `iotaRHS'_spine`,
  `iotaRHS'_iotaCounts` and `iotaRHS_iotaCounts` form a closed 7-declaration, ~50-line cluster
  used only by each other; the terminal `iotaRHS_iotaCounts` (:675) has no consumer and exists to
  substantiate the section docstring's claim that a reduct "retains … nothing else of the
  telescope split". This is the clearest case of a lemma proved only to be cited in prose.
- **MEDIUM** `Lean4Lean/Theory/VExpr.lean:1009` and `:1032` — `subst_instN` and
  `liftN_subst_liftN` strictly subsume master's `subst_inst` (:952) and `lift_subst_lift` (:947)
  — the `n = 0` / `i = 0` instances are literally those statements — but neither master lemma is
  re-derived from the new one, so two pairs of coexisting statements remain.
- **MEDIUM** `Lean4Lean/Theory/VExpr.lean:919` — trproj moved and re-proved master's
  `lift'_inst_hi` as a corollary of the new `lift'_instN_hi`, deleting the only consumer of
  `lift_r_one`; that lemma (:919) and the chain it alone used — `Subst.lift_r_comm` (:911),
  `Subst.trunc` (:908), `Subst.Depth.one` (:885) — are now dead in `Theory/`.
- **MEDIUM** `Lean4Lean/Verify/TypeChecker/WHNF.lean:17` — `inductiveReduceRecCore.WF`, the
  branch's second-longest proof (124 lines), has no consumer: `reduceRecursor.WF` (:147), the
  obligation it was written for, is still `sorry`.
- **LOW** `Lean4Lean/Theory/VExpr.lean:753`, `:756` — `Lift.liftVar_consN_lt` and
  `liftVar_consN_succ` (and hence `consN_fixes`, :745) are unused; only `consN_cons` of that
  trproj block reaches a consumer.
- **LOW** `Lean4Lean/Theory/Typing/InductiveParams.lean:93` — `WF'.pats_origin`, 32 lines,
  documented as "First step of the deferred ι subject-reduction proof", has no consumer; it is a
  down payment on the `sorry` at `EnvLemmas.lean:334`.
- **LOW** `Lean4Lean/Theory/Typing/InductiveLemmas.lean:477` — `addTypes_pats` / `addCtors_pats` /
  `addRecs_pats` and `addTypes_defeqs` / `addCtors_defeqs` / `addRecs_defeqs` are six three-line
  wrappers over two generic lemmas, differing only in the name being `unfold`ed.
- **LOW** `Lean4Lean/Theory/Typing/InductiveLemmas.lean:565` — `addRecs_name_inj` and
  `addInduct_recs_name_inj` (`:704`) state the same conclusion at two stages; the second is a
  three-line wrapper.
- **LOW (positive counterweight)** `Lean4Lean/Tests/IotaShape.lean:454` — the `run_meta` block
  decides every syntactic `VInductDecl.WF` clause on ~45 real kernel inductives (`Nat`, `List`,
  `Vec`, `Acc`, `Eq`, `Std.Format`, …), runs ~20 hand-built negative controls (wrong telescope
  split, wrong field count, `rules_total` without `Nat.zero`, a minor headed by its own binder,
  a non-positive constructor, a two-constructor `Prop` asking for large elimination), and checks
  `SimplePattern.iotaRHS` against the executable kernel's `inductiveReduceRec` on twelve rules
  including a nested block's auxiliary recursor. `Tests/ProjShape.lean:68` does the dual for the
  projection builders by having the **real kernel** accept each expansion as a definition. This
  is genuine validation that the new specification is neither vacuous nor wrong, and it is the
  strongest evidence against a "slop" reading of the branch.

---

## Verdict

**Solid — roughly 70–75 % of the diff.** The specification work (`Theory/Inductive.lean`'s
`VInductDecl.WF` and its shape predicates, `Theory/Proj.lean`'s recursor-expansion model of
projections, `Theory/Typing/Pattern.lean`'s `Realizes`/`TemplateHeaded` layer,
`Theory/Typing/InductiveParams.lean`'s `PatsIota` invariant and the `Params` instance) is
carefully designed, honestly scoped, and validated against the real kernel by a test harness
that is itself high quality. The `Verify/` bridge (`AddInduct`, `Aligned.block`, `pats_iota'`
and its inverse, `structure_rec`, `proj_defeq`, `inductiveReduceRecCore.WF`,
`Verify/Environment/Quot.lean`) is real, non-trivial work. Five `sorry`s were added and twelve
removed, including four `sorry` *definitions* (`VInductDecl.WF`, `VEnv.addInduct`, `TrProj`,
`AddInduct`) that master had left as placeholders — replacing a `sorry` definition with a real
one is worth far more than replacing a `sorry` proof. The kernel edits are minimal, one is a
provably behaviour-preserving refactor, the other is a deliberate, documented divergence that
buys an unconditional `addQuot.WF`. Formatting, naming, granularity and proof length are all
within upstream norms; contributed proofs are *shorter* on average than master's, and there is
no `native_decide`, no `maxHeartbeats`, no `unsafe`/`partial`, no `admit`.

**Questionable — roughly 15 %.** Three clusters: (i) ~20 declarations with no consumer, of which
the `spine`/`iotaCounts` cluster (~50 lines) and `WF'.pats_origin` (32 lines) are the clearest
"written to make a point in a docstring" cases, and four master lemmas orphaned by trproj's
relocation of `lift'_inst_hi`; (ii) duplicated statements that were generalised but not
consolidated (`subst_instN` vs `subst_inst`, `liftN_subst_liftN` vs `lift_subst_lift`, six
three-line stage wrappers, `addRecs_name_inj` twice); (iii) repeated proof boilerplate that
should be one lemma — four 10-case `TrEnv'` inductions (309 lines) and three identical
`TrProjCtor` transport proofs. Add to this the 27 % intra-branch rework (a whole file created
and reverted, half of `InductiveParams.lean` rewritten, `TrProjCtor` re-cut from a `def` to a
structure) and two duplicated commits in the history.

**What an upstream maintainer would push back on, in order.**
1. `VEnv.WF.patsStrong` is `sorry` and is reached through a `CoeOut`, so 158 previously-proved
   master call sites silently became conditional. Mario proved `Ordered.strong`; this branch
   trades that for an admitted regularity lemma. That trade may well be right — master's
   inductive layer was stubbed — but it must be stated at the top of any claim, not discovered.
2. `inferProj.WF` is a retained `sorry` the author documents as *unprovable as stated*, and it is
   consumed by `inferType'.WF`. Keeping a knowingly-false statement in the dependency graph is
   worse than leaving master's (also wrong, also `sorry`) version; the honest move is to restrict
   the statement or remove the consumer.
3. The `AddInduct` layer has no producer — `addDecl.WF`'s `inductDecl` case is still `sorry` — so
   ~1000 lines of front-end refinement are currently hypothetical, and `inductiveReduceRecCore.WF`
   has no consumer because `reduceRecursor.WF` is still `sorry`. The branch builds the road up to
   the two remaining gaps without closing either.
4. Docstring volume in `Theory/`: 25 % comment lines against master's 1.7 %, a 27-line docstring
   on a 5-line definition. The content is good; the ratio is not Mario's and would be trimmed.
5. Dead declarations and the un-consolidated duplicate statements above.
6. History hygiene: rebase away the duplicated commits and the created-then-reverted
   `Theory/Pattern.lean` before asking anyone to read this.

**Is it slop?** No. Slop looks like grandiose docstrings over trivial lemmas, `simp`-spam,
`decide`/`omega` used to paper over statements nobody checked, and lemmas that restate what is
already there. This diff has a little of the last two (the `iotaCounts` cluster; `subst_instN`
vs `subst_inst`; trproj's 5× `omega` density) and a real over-documentation habit, but its
central artefacts — a non-vacuous `VInductDecl.WF` validated against ~45 real inductives, a
projection model whose expansions the actual Lean kernel accepts, sorry-free `TrProjCtor`
witnesses with `#print axioms` pinned by `#guard_msgs`, and a kernel refactor that is provably
behaviour-preserving — are exactly the things slop does not produce.
