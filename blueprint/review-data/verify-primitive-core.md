# verify-primitive-core — narrative and assessment

Files (all paths relative to `/home/barabba/Documents/Research/Projects/Peregrine/lean4lean`):

| file | lines | M | I | P |
|---|---|---|---|---|
| `Lean4Lean/Verify/Primitive.lean` | 595 | 564 | 31 | 0 |
| `Lean4Lean/Verify/Environment/Primitive.lean` | 195 | 195 | 0 | 0 |
| `Lean4Lean/Verify/Environment/Primitive/Basic.lean` | 1399 | 1355 | 39 | 5 |
| `Lean4Lean/Verify/Environment/Primitive/Recursion.lean` | 1775 | 1774 | 1 | 0 |

No `sorry` occurs syntactically in any of the four files (the single hit, `Verify/Environment/Primitive.lean:8`, is the word inside a docstring).

## 1. What these files do

Lean 4's kernel does not evaluate `Nat.add` by unfolding its recursive definition; it recognises a handful of
definitions by name and shape and then computes them with GMP. That is sound only if the recognised definition
really denotes the arithmetic operation the kernel substitutes. This group is the verification of that
recognition.

The pipeline is:

1. **`Lean4Lean/Primitive.lean`** (not in this group) is the recogniser `Primitive.checkDef`. It never inspects
   the definition's identity: it opens probe variables with `withLocalDecl` and runs `isDefEq` tests on the
   definition's *value*, e.g. for `Nat.add` it checks `f x 0 ≡ x` and `f x (succ y) ≡ succ (f x y)` as **open**
   equations, the zero equation in context `[.nat]` and the successor equation in `[.nat, .nat]`.

2. **`Verify/Primitive.lean`** converts those open equations into the closed `Reflects*` statements that
   `VEnv.HasPrimitives` records. The core theorems are the five *recurrence schemas*:
   `ReflectsNatNatNat'.of_unary_step_equations` (595:273, covering `Nat.add`/`Nat.sub`),
   `.of_binary_step_equations` (:312, `Nat.mul`/`Nat.pow`),
   `.of_first_arg_step_equations` (:350, `Nat.shiftLeft`),
   `ReflectsNatNatBool'.of_constructor_cases` (:386, `Nat.beq`/`Nat.ble`) and
   `ReflectsNatNat'.of_pred_equations` (:458). Each is an induction that instantiates the open equations at
   numerals with `IsDefEqU.instN` and chains through the operator's own reflection. Crucially they are stated
   about an *opaque* `VExpr` `f` and mention no constant; the constant only enters at the end via
   `congr_head` (:475) and `toConst` (:555), using the δ-equation that `addDefEq` records
   (`isDefEqU_toDefEq`, :514; `VDefVal.addDefEq_wf`, :536).

3. **`Verify/Environment/Primitive/Basic.lean`** is the shared vocabulary: telescope combinators
   (`VExpr.appN`/`lams`/`forallEs`, :91/:117/:525) with their beta theory, culminating in
   `VExpr.lams_appN`/`lams_appN'` (:618/:654) — the bridge that lets an equation checked *under* an open
   telescope be closed off at ground arguments; the `lambdaTelescope` verification with its `Inv` bundle
   (:842, :899, :969); the ground-judgement abbreviations `HasType₀`/`IsDefEqU₀`/`WF₀`/`Closing` (:684) and
   the `VContext.Ext` extension (:706); the per-branch `Data` record (:1036) and the pre-built translation
   atoms (:1053–:1160); the top-level obligation `PrimitiveResult` (:1204) and the `mkResult*` constructors
   (:1216–:1301) that discharge it; and the `Nat.div`/`Nat.mod` fuel recursion (`goArgs` :1325,
   `natFuelRec` :1360).

4. **`Verify/Environment/Primitive/Recursion.lean`** verifies the well-founded-recursion recogniser used by
   `Nat.gcd`, `Nat.bitwise`, `Nat.div`, `Nat.mod`. `ProbeBundle` (:43) is what the recogniser hands back;
   `Done` (:176) is the caller's obligation (one unfolding, recursive calls already discharged, restricted to
   smaller measure); `NatFixUnfold` (:223) is what the checks buy; `GoConverges` (:247) and `reflects` (:279)
   are the fuel induction. `unfoldNatWellFounded.WF'` (:587) is the plumbing and `WF`/`WF₂` (:1723/:1750) the
   user-facing contract.

5. **`Verify/Environment/Primitive.lean`** is the top: `checkDef.WF` (:33) dispatches the eighteen branch
   theorems in `Clauses.lean`/`DivMod.lean`/`Gcd.lean`/`Bitwise.lean`, and is consumed by
   `Verify/Environment/Checker.lean:201`. Its second half specifies the recogniser's *inductive* clause
   (`AddsConsts` :73, `PrimitiveInductiveResult` :162, `checkInductive.WF` :174).

## 2. Relation to the thesis

There is essentially **no thesis correspondence** for the subject matter. `../lean-type-theory/*.tex` does not
model GMP-accelerated primitives at all; a grep for `GMP`, `accelerat`, `arithmetic`, `bignum` over all
1690 lines turns up nothing relevant. The only points of contact are ambient:

* `axioms.tex` §"Definitions (δ reduction)" — the constant/definition distinction, the rule
  `⊢ c_ℓ̄ ≡ v_ℓ̄(c)`, and the conservativity argument. This is exactly what `isDefEqU_toDefEq`,
  `VDefVal.addDefEq_wf`, `congr_head` and `toConst` formalise, and it is the reason the whole design
  ("prove the reflection of the *value*, then move it onto the constant") is the right one.
* `typesys.tex` §"Regularity" (`\label{thm:reg}`), §"Regularity continued", §"Weakening" (`\label{thm:weak}`)
  and §"Properties of substitution" (`\label{thm:subst}`) — the inversion, weakening and substitution lemmas
  that every proof in the group leans on.
* `unique.tex` "Unique typing" (`\label{thm:utype}`) and "Definitional inversion" (`\label{thm:1dinv}`) —
  used wherever two recorded types have to be identified (`bitwiseOperand` 595:210, `Data.mkTyEq`
  1399:1177, `VExpr.WF.app_inv'` 1399:986).

So in blueprint terms this group is an *extension* of the thesis, not a formalisation of it: it discharges
obligations Lean's real kernel incurs that Carneiro's system does not have. That is worth saying explicitly
in the blueprint, because a reader will otherwise look for the corresponding thesis section and not find it.

## 3. The contributed part: what actually changed

The honest summary is short: **this group contains no new ι or projection content.** It contains a single
mechanical adaptation, applied on the `iota` branch, plus a two-line cosmetic reflow on `trproj`.

### 3.1 The iota adaptation

Every one of the 71 non-master lines is the same edit:

* 20 theorem signatures changed `henv : env.Ordered` → `henv : env.OrderedStrong`
  (`Verify/Primitive.lean` :29,:34,:39,:47,:53,:57,:61,:65,:69,:76,:84,:96,:114,:122,:129,:134,:140,:149,:177,:229;
  `Basic.lean` :158,:163,:431,:436,:580,:603,:997);
* ~45 call sites changed `x.ordered` → `x.orderedStrong`;
* one body line changed `henv.constWF hci` → `henv.ordered.constWF hci` (`Verify/Primitive.lean:80`), because
  `OrderedStrong` is a structure whose first field is `Ordered`;
* `Recursion.lean:380` is the sole line in that 1775-line file (`TrExprS.appN c.Ewf.ordered` →
  `c.Ewf.orderedStrong`).

The reason is upstream of this group. On `master`, `VExpr.WF.app_inv`, `VExpr.WF.lam_inv` and
`HasType.const_inv` (`Theory/Typing/Strong.lean:779/:793/:798` on master) were proved from `Ordered env`
alone, and `Ordered.strong` derived the strengthening lemma unconditionally. On `iota`,
`Theory/Typing/Strong.lean:679` introduces

```
structure OrderedStrong (env : VEnv) : Prop where
  ordered : Ordered env
  strong  : OnTypes env (EnvStrong env)
  pats    : PatsStrongOn env
```

whose third field is subject reduction for the *registered ι rules*, and `VEnv.WF.strong` now takes an
explicit `PatsStrong` argument supplied by

```
theorem VEnv.WF.patsStrong {env : VEnv} (H : env.WF) : env.PatsStrong := sorry
  -- Theory/Typing/EnvLemmas.lean:334
```

The inversion lemmas moved to `OrderedStrong` accordingly, and this group was dragged along.

**Is it faithful?** Yes, in the narrow sense: no statement about primitives changed, no proof was weakened,
no hypothesis about the recogniser was added or removed. The `CoeOut (VEnv.WF env) env.OrderedStrong`
instance added at `EnvLemmas.lean:343` is why `Recursion.lean` needed only one line.

**Is it harmless?** No, and this is the one substantive review point of the group. Before the iota branch,
the GMP-primitive verification was unconditional except for `Theory/Typing/Injectivity.lean` (which
`bitwiseOperand` uses). After it, `checkDef.WF` and hence every `PrimitiveResult` transitively depend on the
admitted `VEnv.WF.patsStrong`. That is a genuine widening of the trust boundary of a body of code that has
nothing to do with ι-reduction, and it is not acknowledged anywhere — indeed the module docstring at
`Verify/Environment/Primitive.lean:6-11` still asserts that "the checker, extension, and declaration modules
introduce no additional `sorry`-backed assumptions", which is literally true but now misleads.

**Was it minimal?** No. Nine of the twenty strengthened signatures do not need the stronger hypothesis:
`natZeroT`, `natSuccT`, `natPredT`, `natLitT`, `natFstLamApp`, `natIsType`, `boolLitT`, `boolIsType`,
`appChar_inv'` use only `HasType.weak0` (`Theory/Typing/Lemmas.lean:610`, still `Ordered`) and
`IsDefEq.isType` (`ibid.:945`, still `Ordered`). Likewise `boolIsType'`/`natIsType'`
(`Basic.lean:158/:163`) only need what their `VLCtx` originals need. Keeping `Ordered` where it sufficed
would have confined the new dependency to the four lemmas that really go through `const_inv`
(`contains_nat_of_hasType` :47, `boolOfBitwise` :76, `trNat` :122, `trBool` :140) plus their transitive
users. The edit reads as a global search-and-replace rather than a considered minimisation — cheap to do,
but it makes the blast radius of `patsStrong` look larger than it has to be.

A smaller stylistic point: after the edit the file mixes three spellings of the same coercion within three
adjacent lines (`Recursion.lean:376` bare `c.Ewf` through `CoeOut`, `:380` explicit `.orderedStrong`,
`:381` explicit `.ordered`). Not wrong, but it now takes a moment to see that these are all the same object.

### 3.2 The trproj "contribution"

`git diff iota HEAD` over the four files is two hunks, both in `Basic.lean` (:431-433 and :455-456), both
purely re-wrapping lines that the iota edit had pushed past the 100-column limit. The five `P`-tagged lines
should not be counted as projection work; any summary of the trproj branch that includes them would be
overstating its footprint.

## 4. Assessment of the master code these files consist of

Since the contributed delta is thin, most of a quality judgement here is about master code, which is
relevant to the blueprint but not to the user's own review. Briefly:

* **Documentation is excellent and unusually candid.** The docstrings routinely explain *why* an interface
  has the shape it has, including what the recogniser does **not** check
  (`Recursion.lean:51-55`: "Nothing here relates `Aty` to `pack`"), why a fact cannot be exported as an
  implication (`Recursion.lean:501-520`, the eager gadget), and where obligations are still open
  (`Verify/Environment/Primitive.lean:158-161`). This is the right standard for a blueprint to inherit.
* **The statements are the right ones.** Reflections are proved about the opaque value, not the constant;
  `PrimitiveResult` quantifies over well-formed extensions so the recogniser's syntax stays out of the rest
  of the metatheory; `Done` restricts the induction hypothesis to smaller measure so the caller's obligation
  is the real termination argument.
* **Known weak points** (all master, all pre-existing): `unfoldNatWellFounded.WF'` is a single 1135-line
  tactic proof needing `maxHeartbeats 1000000` and is effectively unreviewable at that size; the
  `Expr.natBinderTypes` guard (`Basic.lean:856`) is a *hypothesis* of the theorems rather than a check the
  kernel performs, so the verified statement is conditional on a property of the caller's measure;
  roughly 120 of the 195 lines of `Verify/Environment/Primitive.lean` (`AddsConsts` and everything built on
  it) have no consumer at all; `hasPrimitives_bool`/`hasPrimitives_nat` are duplicated proofs; and the file
  is inconsistent about whether `List` helpers go to `_root_.List` or to `Lean4Lean.List`.

## 5. What the blueprint should say about this group

One paragraph of narrative plus the node set: the five recurrence schemas, the δ-transfer chain
(`congr_head` → `addDefEq_wf` → `toConst` → `mkResult*` → `checkDef.WF`), the telescope beta bridge
(`lams_appN`), and the well-founded-recursion contract (`ProbeBundle` / `Done` / `NatFixUnfold` /
`GoConverges` / `unfoldNatWellFounded.WF`). The group should be marked as **master code with a mechanical
iota adaptation**, and the dependency of the whole group on `VEnv.WF.patsStrong` should be drawn explicitly
in the blueprint's dependency graph — that edge is the single most important thing this group tells a
reviewer about the ι contribution.
