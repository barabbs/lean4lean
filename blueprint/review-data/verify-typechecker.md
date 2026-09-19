# Group `verify-typechecker` — soundness of the executable kernel

Files (all paths relative to the repo root):

| file | lines | M | I | P |
|---|---|---|---|---|
| `Lean4Lean/Verify/TypeChecker.lean` | 252 | 252 | 0 | 0 |
| `Lean4Lean/Verify/TypeChecker/Basic.lean` | 1041 | 1041 | 0 | 0 |
| `Lean4Lean/Verify/TypeChecker/InferType.lean` | 519 | 497 | 0 | 22 |
| `Lean4Lean/Verify/TypeChecker/IsDefEq.lean` | 606 | 606 | 0 | 0 |
| `Lean4Lean/Verify/TypeChecker/Reduce.lean` | 156 | 156 | 0 | 0 |
| `Lean4Lean/Verify/TypeChecker/WHNF.lean` | 309 | 168 | 0 | 141 |

**Attribution caveat.** The precomputed blame tags the 141 new lines in `WHNF.lean` as `P`
(trproj), but `git diff iota trproj -- Lean4Lean/Verify/TypeChecker/WHNF.lean` is empty and
commits `7a68882` (iota) and `6fd8a1d` (trproj) are the same patch with the same author date.
Those lines are the **iota** contribution; trproj simply carries a duplicate of the commit and
then merges iota on top (`20ec229`). The blame tool picked the trproj-side commit. In the JSON
I attribute `inductiveReduceRecCore.WF` to `iota`.

## 1. What the group does

This is the bridge between the *executable* Lean 4 kernel re-implementation (`Lean4Lean/TypeChecker.lean`,
`Lean4Lean/Inductive/Reduce.lean`) and the *model* of Lean's type theory (`Lean4Lean/Theory/**`,
`Lean4Lean/Verify/Typing/**`). Concretely: every kernel function `f` gets a companion theorem
`f.WF` saying "if the inputs translate into the model, then whatever `f` returns is justified by
the model". Nothing says the kernel *succeeds* — this is soundness only, never completeness,
which is exactly the asymmetry Carneiro insists on (`typesys.tex`: "Lean's typechecker is not
complete"; algorithmic equality `⇔` is not even transitive).

The scaffolding lives in `Basic.lean`:

* `MLCtx` (`Basic.lean:106`) is a local context carrying kernel-side and model-side data in one
  structure, so `MLCtx.lctx` and `MLCtx.vlctx` can never drift; `MLCtx.WF` (`:158`) pins the
  translation invariant at every binder.
* `VContext` (`:190`) extends the runtime `Context` with a `VEnv`, a `TrEnv` translation, the
  primitive-constant discipline, and an `MLCtx` whose `lctx` is *definitionally* the runtime one.
* `VState.WF` (`:245`) is the state invariant, and this is the part with no thesis counterpart
  at all: it is what makes the kernel's five memo caches (`inferTypeI`, `inferTypeC`, two whnf
  caches, the delta cache) and the union-find `eqvManager` sound.
* `M.WF` (`:278`) / `RecM.WF` (`:325`) / `Methods.WF` (`:314`) are the Hoare predicates. The
  mutual recursion is tied off by fuel in `Methods.withFuel.WF` (`TypeChecker.lean:48`), so
  every individual proof may assume its recursive calls already sound.

The four bodies then discharge the four kernel entry points:

* `Reduce.lean` — primitive reduction. `reduceNative.WF` (never fires), `rawNatLitExt?.WF`,
  the fourteen GMP-accelerated `Nat` operations against `VEnv.HasPrimitives`
  (`reduceNat.WF`, `:89`), and `reduceProj.WF` (`:147`) modulo the open `reduceProjCore.WF` (`:143`).
* `WHNF.lean` — `whnfCore'.WF` (`:166`, beta/zeta/fvar-delta/recursor/projection with cache
  maintenance) and `whnf'.WF` (`:269`, the delta loop). Corresponds to `axioms.tex`'s
  `e ⇝* k` head reduction and the `β`, `δ`, `ζ`, `ι` rules.
* `InferType.lean` — `inferType'.WF` (`:432`), the `TrTyping` statement: kernel-accepted term
  ⇒ it translates, its inferred type translates, and the model types the one at the other.
* `IsDefEq.lean` — `isDefEqCore'.WF` (`:528`), the mechanised form of `typesys.tex`'s
  `item:alg_defn` ("if `Γ ⊢ e ⇔ e'` then `Γ ⊢ e ≡ e'`"), assembled from eleven stages.

`TypeChecker.lean` re-exports all of this at the `M` level (`whnf.WF` … `ensureType.WF`,
`:186`–`:252`) and supplies `M.WF.run` (`:105`), which is the statement that eventually feeds
`soundness.tex`'s corollary (`⊩ e : ⊥` ⇒ `⊢ e : ⊥` ⇒ contradiction with `⟦⊥⟧ = ∅`).

Six `sorry`s remain in the group: `reduceProjCore.WF` (`Reduce.lean:145`),
`reduceRecursor.WF` (`WHNF.lean:149`), `tryEtaStructCore.WF` (`IsDefEq.lean:227`),
`isDefEqUnitLike.WF` (`IsDefEq.lean:488`), and the two projection ones in `InferType.lean`
(`:398`, `:410`).

## 2. The iota contribution — `inductiveReduceRecCore.WF` (`WHNF.lean:17`–`145`)

This is the only substantive new *proof* in the group. Upstream, `inductiveReduceRec`
(`Lean4Lean/Inductive/Reduce.lean`) was one monolithic function; the iota commit split out the
pure ι step as `inductiveReduceRecCore` (`Inductive/Reduce.lean:75`) and then proved:

> if the recursor spine `recName ls as` translates to `e'`, its major argument is literally the
> constructor application `ctorName cls cargs`, and that application is exactly saturated
> (`|cargs| = cval.numParams + rule.nfields`), then the term the kernel builds is `FVarsBelow`
> the redex and translates to the **same** `e'`.

This is precisely `axioms.tex` §`sec:iota`, `rec_P C e p[b] (c b) ⇝ e_c b v`, at the level of
Lean's actual recursor-rule representation.

**Design quality — good.** The split of `inductiveReduceRec` is behaviour-preserving and is
the right refactor: the K-like conversion, literal-to-constructor conversion and structure-eta
of the major are *monadic* and belong in the caller; the ι step itself is pure and is the only
part that has to be matched against the model's ι registry. The proof structure is the natural
one: slice the recursor spine as `p1 ++ idx ++ major :: post` and the constructor spine as
`cpar ++ cfld`, rewrite the three `mkAppRange` calls into `mkAppList` (`Expr.mkAppRange_eq`),
invert the translation along the same slices (`TrExprS.mkAppList_inv`), match both constant
spines against the pattern (`Pattern.matches_varN_const`), pull the model equation from
`TrEnv.iota_rec`, identify `SimplePattern.iotaRHS` with the kernel's slicing
(`SimplePattern.iotaRHS'_apply` + `List.take_left'`/`drop_left'`), and rebuild.

**Proof quality — good.** 129 lines of tactic script for a genuinely fiddly index-arithmetic
argument, with four orienting comments in the right places (`:31`, `:47`, `:85`, `:107`,
`:124`). No `omega`-spam beyond the two length computations, no `simp` blowups, no leftover
`sorry`. `TrEnv.iota_rec` itself is `sorryAx`-free (checked with `#print axioms`).

**Documentation — good, with one omission.** The docstring (`:6`–`16`) explains the two
slicings and is explicit that `hsat` is an assumption "left to the caller". It does **not**
mention the bigger structural restriction, `hmaj`.

**Concerns.**

1. *No consumer.* `reduceRecursor.WF` (`WHNF.lean:147`) is still `sorry` and nothing else in
   the repository mentions `inductiveReduceRecCore.WF`. The lemma is currently dead code. The
   value of the contribution is entirely prospective.
2. *`hmaj` is stronger than the call site.* `inductiveReduceRecCore` is invoked
   (`Inductive/Reduce.lean:115`) on a `major` obtained from `recArgs[majorIdx]!` by
   `toCtorWhenK`, `whnf`, literal conversion and `toCtorWhenStruct`. The lemma instead demands
   `as[rval.getMajorIdx]? = some (mkAppList (.const ctorName cls) cargs)` — the *unreduced*
   spine element must already be the constructor application. A consumer has to rebuild the
   spine with the converted major and transport the translation across the resulting
   `IsDefEqU`; that bridging step is the part that actually connects to `whnf`, and it is
   neither done nor flagged. As it stands the lemma covers a syntactic redex, not a kernel step.
3. *`hsat` is a second deferred obligation.* "It is a consequence of the redex being well-typed"
   is plausible but unproved anywhere in the repo. It also silently excludes over-applied
   constructor applications, which is exactly the case where the kernel's "last `nfields`
   arguments" and the pattern's "arguments past `numParams`" genuinely disagree — i.e. the
   hypothesis is doing real work, not just convenience.
4. *`sorryAx`.* `#print axioms` on the lemma reports `sorryAx`, inherited through
   `TrExpr.rebuild_mkAppList` from the still-open `TrProj.uniq` / `TrProj.weak'_inv`
   (`Verify/Typing/Lemmas.lean:995`, `:747`). Not the contribution's doing, but it means the
   result should not be described as unconditional.

## 3. The trproj contribution — `inferProj.WF` / `WF_struct` (`InferType.lean:388`–`410`, `:479`)

22 lines, all in the projection case of type inference, and all of it statement-level (both
theorems are `sorry`).

**`inferProj.WF` was genuinely broken on master and is now fixed.** Master had

```lean
theorem inferProj.WF (he : c.TrExprS e e') (hty : c.TrExprS ety ety') (hasty : c.HasType e' ty') :
    (inferProj st i e ety).WF c s fun ty _ => ∃ ty', c.TrTyping (.proj st i e) ty e' ty' := sorry
```

Two defects: (a) the `ty'` in `hasty` is an *auto-bound implicit*, unrelated to the `ty'` bound
in the conclusion, so the hypothesis only said "`e'` has some type", which is free anyway;
(b) the conclusion asserted `TrTyping (.proj st i e) ty e' ty'`, i.e. that the *projection*
translates to `e'` — but `e'` is the translation of the projection's *subterm*. The trproj
version fixes both: `hasty : c.HasType e' ety'` is exactly what the caller supplies at
`InferType.lean:479` (from the recursive `inferType'` result), and the conclusion existentially
quantifies the projection's own translation `e''`. This is a real, correct, well-targeted fix,
and the caller's proof term needed only a one-token change.

**The new docstrings are the actual contribution.** `:400`–`:406` records that the general
statement is *not provable as stated*: `TrExprS.proj` (`Verify/Typing/Expr.lean:171`) requires a
`TrProj` derivation, and `TrProj`/`TrProjCtor` only exists for non-mutual, single-constructor,
non-indexed, non-recursive structures, while `inferProj` (`Lean4Lean/TypeChecker.lean:233`)
checks none of `isRec`, `all` and happily accepts projections of reflexive, indexed and nested
single-constructor types (the docstring names `Lean.Language.SnapshotTree.element`). It then
lists what closing the gap would require (a selector binding the inductive-hypothesis binders,
a motive abstracting the indices, extra motives/minors for a nested block, or a projection node
with its own ι and η rules). `inferProj.WF_struct` (`:392`) is the same statement scoped to the
structures the model covers.

**Assessment.** The diagnosis is correct and it is the most valuable thing in this group's
contributed material, because it is not a local gap: `inferType'.WF` consumes `inferProj.WF`, and
`checkType.WF` (`TypeChecker.lean:215`) has *no* hypothesis that its input is translatable. So
the project's headline soundness statement is, as of trproj, known to be unprovable for a class
of terms the real kernel accepts. Recording that honestly in the source is right. But note two
things a reviewer should weigh:

* Leaving a `theorem … := sorry` whose own docstring says it is unprovable, on the import path of
  `inferType'.WF`, is a stronger statement than "open": it is an admitted falsehood, and it is
  reached by every downstream `Verify/Environment/*` result. Some of the alternatives (weaken
  `inferType'.WF`'s conclusion, or add a scope hypothesis) are not discussed.
* `inferProj.WF_struct` is **unused** — referenced only from docstrings
  (`Tests/ProjInhabit.lean:15`, `Verify/Typing/Expr.lean:125`). And its hypotheses are
  kernel-side metadata facts (`ival.all = [st]`, `ival.ctors = [c]`, `numIndices = 0`,
  `isRec = false`), not `TrProjCtor`, even though the docstring calls it "`inferProj.WF` for the
  structures the model covers (`TrProjCtor`)". The implication *kernel facts ⇒ `TrProjCtor`
  inhabited* is precisely the unproved content, so the statement as written is not obviously
  the right intermediate goal.

**What is conspicuously missing.** The trproj branch closed five of master's seven `TrProj.*`
sorries in `Verify/Typing/Lemmas.lean` (`weak'`, `defeqDFC`, `wf`, `instN`, `instL`), which is
substantial infrastructure. Yet the two consumers in *this* group that the infrastructure exists
for — `reduceProjCore.WF` (`Reduce.lean:143`) and `tryEtaStructCore.WF` (`IsDefEq.lean:225`,
whose statement is literally `TrProjCtor.eq`'s shape) — were not attempted. Relative to the
supporting work, the payoff visible in `Verify/TypeChecker` is thin: one sorry'd scoped
statement, one signature fix, and a docstring.

## 4. Overall verdict for this group

* Master code here is dense and high quality; the proofs are terse but structured, and the
  statements are the right ones (partial correctness, `FVarsBelow` retained where callers need
  it, cache invariants folded into `VState.WF`).
* The **iota** contribution is the stronger of the two: a real theorem, carefully proved,
  correctly documented, and the right decomposition of the kernel function. It is one bridging
  lemma away from being useful, and that lemma is not written.
* The **trproj** contribution in this group is documentation and a signature repair, not a
  result. The signature repair is genuinely valuable (it fixed a statement that was wrong).
  The documentation is valuable in a different way: it converts an invisible hole in master's
  headline theorem into an explicit, well-analysed one. But three of the four declarations it
  touches remain `sorry`, and one of them is dead.
