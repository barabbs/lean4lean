# Group `verify-environment` — narrative and assessment

Files (all paths relative to the repository root):

| file | lines | M | I (iota) | P (trproj) |
|---|---|---|---|---|
| `Lean4Lean/Verify/Environment.lean` | 208 | 203 | 5 | 0 |
| `Lean4Lean/Verify/Environment/Basic.lean` | 619 | 197 | 398 | 24 |
| `Lean4Lean/Verify/Environment/Checker.lean` | 230 | 230 | 0 | 0 |
| `Lean4Lean/Verify/Environment/Extension.lean` | 487 | 485 | 2 | 0 |
| `Lean4Lean/Verify/Environment/Lemmas.lean` | 1178 | 254 | 308 | 616 |
| `Lean4Lean/Verify/Environment/Quot.lean` | 615 | 0 | 615 | 0 |
| `Lean4Lean/Verify/Axioms.lean` | 510 | 510 | 0 | 0 |

## 1. What this group does

This is the *environment layer* of lean4lean's verification: the bridge between a real
`Lean.Kernel.Environment` (an `SMap Name ConstantInfo` plus a quotient-initialization flag) and
the abstract `VEnv` of the thesis's type theory (a partial map to `VConstant`s, a set of
definitional equations `defeqs`, and — new on the iota branch — a set of registered pattern
reduction rules `pats`).

The central object is `TrEnv' safety C Q venv` (`Basic.lean:535`), an inductive relation with
one constructor per way the kernel can extend an environment: `empty`, `ignore` (a declaration
invisible at this `DefinitionSafety`), `axiom`, `defn`, `mutualDef`, `thm`, `opaque`, `quot`,
`induct`. `TrEnv safety env venv` (`Basic.lean:588`) instantiates it at a real environment.
Around it sit:

* **Basic.lean** — the vocabulary. `TrConstant`/`TrConstVal`/`TrDefVal` (`:21-32`) are the
  translation of one declaration and correspond to the thesis's $\tau_{\bar\ell}(c)$ and
  $v_{\bar\ell}(c)$ (`axioms.tex`, §"Definitions ($\delta$ reduction)"). `VEnv.AddConst` /
  `VEnv.AddDef` (`:55`, `:70`) are the per-safety-level step relations. `AddQuot` (`:108`) is the
  four-step witness for quotient initialization. `AddInduct` (`:272`) is the witness for an
  inductive block.
* **Lemmas.lean** — the consequences: `Aligned` (`:12`), a constants-only companion used to prove
  lookup transfer both ways; $\delta$-soundness (`TrEnv'.of_value`, `:333`); the $\iota$ interface
  (`pats_iota'` `:674`, `IotaRule` `:782`, `pats_iota_inv_shape` `:826`, `iota_rec` `:929`);
  structure-likeness (`ctor_arity` `:449`, `structure_rec` `:523`); a $\beta$-telescope calculus
  (`:959-1010`); and projection reduction (`proj_defeq` `:1021`).
* **Checker.lean / Extension.lean / Environment.lean** — the driver: per-declaration checks,
  generic extension lemmas, and `addDecl.WF` (`Environment.lean:197`), the top-level statement
  that a checked declaration addition preserves the invariant.
* **Quot.lean** — quotient initialization, in full.
* **Axioms.lean** — the trust boundary (Lean's `partial def`s, opaque `PersistentHashMap`, the
  C++-implemented `Expr` primitives).

Thesis correspondences are indirect: Carneiro's thesis specifies *the type theory*, not the
kernel's environment data structure, so this group is the refinement layer that has no thesis
counterpart of its own. Where the statements do touch the thesis they touch
`axioms.tex` §"Inductive types" / §"The recursor" (`TrIndType`, `TrRecursor`,
`AddInduct`), §"The computation rule ($\iota$ reduction)" (`pats_iota'` and friends),
§"Quotient types" (`Quot.lean`), §"Definitions ($\delta$ reduction)" (`TrEnv'.of_value`), and
`typesys.tex` §`sec:undecidable`, whose $\mathsf{inv}_x$ construction is literally the shape of
the projection expansion that `TrProjCtor` and `proj_defeq` reason about.

## 2. What the branches contributed

### 2.1 `AddInduct` (iota) — the big one

On master (`git show master:Lean4Lean/Verify/Environment/Basic.lean`, lines ~100-110):

```
/-- This definition is essentially a `sorry`: ... but it currently has no constructors, so the
`TrEnv'.induct` case below can never fire and environments containing inductives are outside
the verified `TrEnv` relation. -/
inductive AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) : Prop
  -- TODO
```

The iota branch replaced this with a real 15-field structure (`Basic.lean:272-290`) recording the
kernel data, the four model stages of `VEnv.addInduct`, the per-type-former and per-recursor
translations, freshness, and — the good idea — the *actual* kernel insertion order as a
permutation of the model's stage order (`order`, `order_perm`, `map_eq`). Nested blocks are
inserted type-by-type by `Environment.addInductive` but the model adds all type formers, then all
constructors, then all recursors; `Aligned.addInduct` (`Lemmas.lean:102`) reconciles the two with
a single `VEnv.addConst_foldlM_perm` argument. That is exactly the right factoring and the
docstring (`Lemmas.lean:97-101`) says so clearly.

From `AddInduct` the branch derives, rather than assumes, seventeen bookkeeping lemmas
(`Basic.lean:296-517`): stage recomposition, name equality with the model, distinctness of the
block's names (`names_nodup`, derived from the model's `addConst` folds succeeding), lookup
transport in both directions, and the three interface theorems `rec_find` (`:434`),
`rec_reg` (`:464`) and `ctor_find` (`:494`). Commit `d69ac5d refactor: derive AddInduct's ι
bookkeeping instead of assuming it` shows this derivation was a deliberate correction of an
earlier version that took them as fields — a good sign of self-criticism in the branch history.

The immediate payoff is `Quot.lean`. On master, `checkEqType.WF` proved `False`: `TrEnv` could
not contain the inductive `Eq`, so quotient initialization was vacuously well-formed. Once
`AddInduct` became inhabitable that argument evaporated and the branch had to prove quotient
initialization for real — 615 lines that symbolically replay the kernel's expression builder
(`AddQuotAux.L1…L5i`, `T1…T4`), evaluate the `mkForall` telescopes (`T1_eq…T4_eq`), analyse
`checkEqType` (`checkEqType_ok`, `:253`), give explicit `TrExprS` derivations for the four
quotient types (`T1_tr…T4_tr`), and assemble `addQuot.WF` (`:500`). This is honest, necessary
work of exactly the kind the project needs.

### 2.2 The $\iota$ interface (iota)

`TrEnv'.pats_iota'` (`Lemmas.lean:674`) is the forward direction: every kernel recursor rule is
registered in the model's `pats` as a `SimplePattern.iota` with the kernel's telescope split as
key and the constructor's parameter count read off its own `ctorInfo`. `TrEnv.iota_rec`
(`:929`) composes it with `IsDefEq.pat` into the form `reduceRecursor` needs. This one *is*
consumed later: `Verify/TypeChecker/WHNF.lean:119` (`inductiveReduceRecCore.WF`), which is
proved. So the iota chain reaches the kernel model — though the enclosing `reduceRecursor.WF`
(`WHNF.lean:149`) is still `sorry`, so the chain to `whnf` is not closed.

### 2.3 Structure-likeness and projections (trproj)

`TrEnv'.ctor_arity` (`Lemmas.lean:449`) and `TrEnv'.structure_rec` (`:523`, 125 lines) are the
trproj contribution to the *environment* layer. `structure_rec` takes exactly the three facts
`inferProj`/`reduceProjCore` test before accepting a projection (`all = [S]`,
`ctors = [ctorName]`, `numIndices = 0`) and returns the recursor's telescope split
(`numParams = ival.numParams`, one motive, one minor, no indices) plus the constructor with the
same parameter count. Getting there requires the four-way case analysis at `:566-640`: if only
one of $S$ and `mkRecName S` comes from the block, freshness contradicts (via
`TrRecursor.name_major`); if both do, the counts come from `VInductDecl.WF.rec_counts`/
`rec_params` and `TrIndType.all`/`numParams`/`numIndices`. The premise set is the right one.

`TrEnv'.IotaRule` (`:782`) and `pats_iota_inv_shape` (`:826`) are the *inverse* of `pats_iota'`:
given a registered $\iota$ pattern, recover the kernel rule *and* the model-side shape
(`RecShape` of the recursor type, `MinorFor`/`RuleShape` of the reduct). This is the genuinely
hard theorem of the trproj branch, and `AddInduct.rec_reg` exists to serve it.

`TrEnv.proj_defeq` (`:1021`, 138 lines) is the headline: the recursor expansion of the $i$-th
projection of a value definitionally equal to a saturated constructor spine reduces to
`fields[i]`. The proof structure (labelled (A)–(F) in the source) is clear: constructor arity,
the registered rule, the kernel's structure facts, the no-recursive-argument minor, the $\iota$
step, then two `betaN` steps through the rule template and `VExpr.fieldSelector`. Crucially the
projection rule is *derived* from the $\iota$ rule rather than postulated — this is the right
architecture and it is what makes the trproj work more than a definition dump.

## 3. Assessment

### Strengths

* **Documentation is excellent and unusually honest.** Nearly every contributed declaration has
  a docstring that says what it is for and what the reader should worry about; section headers
  (`/-! ### … -/`) organise both `Basic.lean` and `Lemmas.lean`. `Basic.lean:253-258` explains
  why a block's insertion order needs its own field; `Lemmas.lean:516-522` explains why both
  constants must be visible at `safety`; `TrProjCtor`'s docstring (`Verify/Typing/Expr.lean:84-89`)
  states its scope limitation as a *completeness* boundary, not a soundness one. This is better
  than the surrounding master code.
* **Statements are the right ones.** `structure_rec`'s hypotheses are the kernel's own tests.
  `ctor_arity`'s conclusion is the arity bridge a spine argument needs. `IotaRule` bundles
  precisely what `proj_defeq` consumes. `names_nodup` is derived, not assumed.
* **The proofs are real.** No `sorry` appears in any file of this group except
  `Environment.lean:208`. `#print axioms Lean4Lean.TrEnv.proj_defeq`
  (`Tests/ProjInhabit.lean:587-595`) is checked in CI and shows only `propext`,
  `Classical.choice`, `Quot.sound`, the three `PersistentHashMap` axioms, and one inherited
  `sorryAx` (from unique typing / `patsStrong`, not from this group).

### Weaknesses

1. **The whole edifice rests on an undischarged hypothesis.** `addDecl.WF`'s `inductDecl` case is
   `sorry` (`Environment.lean:208`) and nothing constructs an `AddInduct` from
   `Environment.addInductive`. Every theorem in §2.1–2.3 is of the form "if you hand me a witness,
   then …". That is a legitimate way to stage the work, and the docstring at
   `Environment.lean:194-196` says so, but a reviewer should be clear that the branches moved the
   `sorry` rather than removing it: from "`AddInduct` is empty" to "`AddInduct` has no producer".
   The work is not wasted — `Quot.lean` and `inductiveReduceRecCore.WF` are unconditional gains —
   but the headline theorem is no closer to proved.
2. **`proj_defeq` is orphaned.** Its only consumer is a test. `reduceProj.WF`
   (`WHNF.lean:149`) and both `inferProj.WF`s (`InferType.lean:398`, `:410`) are `sorry`, and its
   own premise `TrProjCtor` is only inhabited by hand (`Tests/ProjInhabit.lean`), since the general
   construction `inferProj.WF_struct` is also `sorry`. The trproj branch built a good theorem with
   no socket to plug into yet. (`TrExpr.mkAppList`, `Lemmas.lean:1166`, is the counter-example: a
   trproj lemma that *is* used, at `WHNF.lean:131`.)
3. **Dead and unused pieces.** `insertConsts_find?_none` (`Basic.lean:165`) is dead.
   `TrRecursor.all` (`:240`) and `TrRecursor.k` (`:245`) are never consumed — extra obligations on
   a producer that does not exist; `k` records a K-like-reduction flag for which the model has no
   rule. `TrEnv.pats_iota_inv_shape` (`Lemmas.lean:903`) is a definitional restatement of the
   primed version whose docstring claims a conversion it does not perform — `proj_defeq` does the
   conversion by hand at `:1060-1062` and `:1072-1074`.
4. **Misfiled material.** The $\beta$-telescope family (`Lemmas.lean:959-1010`) and
   `TrExpr.mkAppList` (`:1166`) are `VExpr`/`TrExpr` metatheory with no environment content; they
   live here only because `proj_defeq` needs them. `TrEnv.iota_defeq` (`:917`) is a three-line
   wrapper over `VEnv.IsDefEq.pat` that has no `TrEnv` hypothesis at all, yet is named as if it
   did.
5. **Brittleness in `Quot.lean`.** `AddQuotAux` (`:27-70`) hand-replays the binder names, binder
   infos and `withLocalDecl` order of `Lean4Lean/Quot.lean`. Nothing links the two beyond the
   proofs breaking, and the `T*_tr` derivations (`:331-392`) are 60 lines of hand-built `TrExprS`
   trees. Correct, but expensive to maintain. The repetition noted in issue 7 of the JSON
   (`:521-547`, `:584-607`) is avoidable.
6. **One undocumented design change.** `AddInduct` is `Type`-valued (no `: Prop`), so `TrEnv'`
   acquires a data-carrying constructor field and loses large elimination. Necessary, harmless for
   present consumers, but it changes the character of the project's central invariant and nowhere
   is that said.
7. **A blame caveat for the reviewer.** Some lines the per-line attribution marks as contributed
   are master code *relocated* by the refactor commits: `TrConstant.sf_mono`/`mono`,
   `TrConstVal.mono`, `TrDefVal.mono` (`Basic.lean:34-48`, from `Lemmas.lean`) and
   `insertDefs_wf` (`Lemmas.lean:211`, from `Extension.lean`). Roughly 20 of the 398 `I` lines in
   `Basic.lean` are of this kind.

### Bottom line

Within this group the iota branch is the stronger contribution: it turns a documented `sorry`
into a real structure, derives its consequences carefully, and is forced into — and delivers —
a full proof of quotient initialization that master had been getting for free from vacuity. It
also connects to the kernel model at one real point (`inductiveReduceRecCore.WF`). The trproj
contribution here is technically the more impressive single theorem (`pats_iota_inv_shape` +
`proj_defeq`) and is correctly architected — projections derived from $\iota$, not postulated —
but it is currently disconnected from the checker, and a reviewer should weigh it as a
well-built component awaiting its consumer rather than as a closed result.
