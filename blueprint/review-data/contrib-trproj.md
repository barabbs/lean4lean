# Contribution inventory — branch `trproj` (projection support / `TrProj`)

Checkout inspected: `/home/barabba/Documents/Research/Projects/Peregrine/lean4lean`, branch `trproj`
@ `20ec229` (read-only; no build run). Ranges used:

| range | files | +/− |
|---|---|---|
| `iota..trproj` (projection round proper) | 17 | +2273 / −170 |
| `master..trproj` (total footprint of both branches) | 50 | +7763 / −363 |

Per-line blame tally over the precomputed `scratchpad/blame/*.txt`: **≈2645 lines tagged `P`**
(trproj-only) in the current tree, against ≈5000 `I` (iota) and the rest `M` (upstream). The
largest `P` blocks are `Verify/Environment/Lemmas.lean` (616), `Tests/ProjInhabit.lean` (597),
`Theory/Proj.lean` (449), `Theory/VExpr.lean` (195), `Tests/ProjShape.lean` (185),
`Verify/TypeChecker/WHNF.lean` (141), `Verify/Typing/Lemmas.lean` (131),
`Theory/Typing/Pattern.lean` (77), `Verify/Typing/Expr.lean` (70).

---

## (a) Goal and design

### The problem in lean4lean's verification

`Lean4Lean.Verify` relates the executable kernel (`Lean.Expr`, `Lean.Kernel.Environment`) to the
abstract model (`VExpr`, `VEnv`) via `TrExprS`/`TrEnv`. `VExpr` has **no projection node**, so the
`.proj` case of `TrExprS` was routed through an abstract relation `TrProj`, which on `master` is

```lean
-- master:Lean4Lean/Verify/Typing/Expr.lean:68
def TrProj : ∀ (Γ : List VExpr) (structName : Name) (idx : Nat) (e : VExpr), VExpr → Prop := sorry
```

This is an *opaque definition*, not an unproven theorem: nothing can be constructed in it and
nothing refuted about it. On `master` the seven structural lemmas about it
(`weak'`, `weak'_inv`, `defeqDFC`, `wf`, `uniq`, `instN`, `instL`,
`Verify/Typing/Lemmas.lean:642,723,727,893,938,1240,1509`) are all `sorry` as well — nine `sorry`s
in total on the projection side. Consequences: no `TrEnv` witness can be built for any environment
containing Lean's prelude (`Prod.fst`, `HAdd.hAdd`, … are `.proj` bodies), and master's own
primitives layer works around the hole by restricting to projection-free terms
(`noProj` / `TrExprS.weakR`, `Verify/Environment/Primitive/Condition.lean:482` — master's own
docstring says "`noProj` only to sidestep `proj`, whose `TrProj` side condition would have to be
transported too").

### The design

A projection `.proj S i e` is modelled as an application of the **recursor the kernel generates for
`S`**:

```
P_i = S.rec (uss i) ps (λ x : S usS ps. F_i[f_j := P_j x]) (λ f₀ … f_{n−1}. f_i)
e'  = P_i e
```

with `F₀ … F_{n−1}` the constructor's field telescope instantiated at the parameters (exactly what
the kernel's `inferProj` computes), `F_i` living under the earlier fields, and the earlier
*projection functions* `P_j` (`j < i`) being the same expansions, recursively — so a dependent field
type gets the *chained* motive `λ x. F_i[f_j := P_j x]`. A per-field level list `uss : Nat → List
VLevel` is carried because the elimination level differs between fields (`Sigma.fst` needs
`Sigma.rec.{u+1,u,v}`, `Sigma.snd` `Sigma.rec.{v+1,u,v}`).

The justification for reading `Expr.proj` as a recursor application is the kernel's own rule,
already recorded in `divergences.md` by upstream: `inferProj`'s Prop gate and `toCtorWhenStruct`'s
elimination test keep a projection no more powerful than the recursor generated for the same type.

### Relation to the thesis

Verified against `../lean-type-theory/*.tex`:

- `typesys.tex:9–17` — `inv_x : acc x → ∀ y, y < x → acc y`, defined by `rec_acc` with a **specific**
  motive `λ z. y < z → acc y`. That is the precedent for the shape (a projection derived from a
  recursor with a chosen motive), cited correctly by `Theory/Proj.lean:11–13`.
- `Wtypes.tex:15,26–28,75–76,92–93` — the thesis's *soundness model* has **primitive** `π₁`/`π₂`
  with dependent typing `π₂ p : β[π₁ p/x]`, plus the η rule `(π₁ x, π₂ x) ≡ x` taken as a "modest
  strengthening". The branch reproduces the dependent typing shape but **not** η.
- `axioms.tex §2.6.3` — motive type `κ`, fresh universe variable per use of `rec_P`; this is what
  the per-field `uss` reflects.
- **Honest caveat**: the thesis never treats Lean's `Expr.proj` (`grep '\proj'` over the .tex
  sources returns nothing). The chained-motive construction is an *original extension*, not a thesis
  theorem. The commit title 811a52a "define TrProj by the thesis's dependent motive" overclaims;
  the current module docstring has been softened but still leads with "The shape is Carneiro's
  thesis's `inv_x`". The branch's own review flagged this (F44) and it is only partly fixed.

### Key declarations (verified by grep on the current checkout)

**`Lean4Lean/Theory/Proj.lean`** (new, 449 lines, 100 % `P`) — namespace `Lean4Lean.VExpr`:

| Lean name | file:line | role |
|---|---|---|
| `Lean4Lean.VExpr.fieldSelector` | Theory/Proj.lean:70 | minor premise `λ f₀…f_{n−1}. f_i` |
| `Lean4Lean.VExpr.instPis` | Theory/Proj.lean:75 | instantiate leading Π-binders (kernel's `inferProj` parameter loop) |
| `Lean4Lean.VExpr.instFields` | Theory/Proj.lean:84 | substitute the field binders, outermost first |
| `Lean4Lean.VExpr.projMotiveBodyOf` | Theory/Proj.lean:91 | motive body of field `i` given earlier `Ps` |
| `Lean4Lean.VExpr.projFnOf` | Theory/Proj.lean:96 | `P_i` given earlier `Ps` |
| `Lean4Lean.VExpr.projFns` | Theory/Proj.lean:108 | `[P₀ … P_{i−1}]` (well-founded on `i`) |
| `Lean4Lean.VExpr.projMotiveBody` | Theory/Proj.lean:114 | `F_i[f_j := P_j x]` |
| `Lean4Lean.VExpr.projFn` | Theory/Proj.lean:120 | the projection function `P_i` |
| `Lean4Lean.VExpr.projTy` | Theory/Proj.lean:127 | `inferProj`'s result type (**test-only**: 6 refs, all in Tests/docstrings) |
| `Lean4Lean.VExpr.binderArity?` | Theory/Proj.lean:136 | Π-arity of the `k`-th binder; the `minor_arity` pin |

plus ~34 commutation lemmas (`*_subst`, `*_lift'`, `*_inst`, `*_instL`) and the β-crux
`Lean4Lean.VExpr.instFields_minor_spine` (Theory/Proj.lean:428).

**`Lean4Lean/Verify/Typing/Expr.lean`**:

| Lean name | file:line | role |
|---|---|---|
| `Lean4Lean.TrProjCtor` | Verify/Typing/Expr.lean:90 | `Prop`-valued **structure**, 8 named fields: `pat`, `params_length`, `ctor`, `field_lt`, `minor_arity`, `major_ty`, `fn_ty`, `eq` |
| `Lean4Lean.TrProj` | Verify/Typing/Expr.lean:133 | `∃ ctorName usS uss params np fieldTys, TrProjCtor …` |
| `Lean4Lean.TrExprS.proj` | Verify/Typing/Expr.lean:171 | the use site (unchanged constructor, new `TrProj` signature) |

Signature change: `TrProj` gained `(env : VEnv) (U : Nat)` — it is no longer a purely syntactic
relation, because `major_ty` and `fn_ty` are `HasType` side conditions. `.proj` is the only clause
of `TrExprS` carrying a typing obligation; this is a genuine design asymmetry a maintainer may
push back on (see (e)).

**`Lean4Lean/Verify/Typing/Lemmas.lean`** — 8 lemmas, 6 proved:

| Lean name | file:line | status |
|---|---|---|
| `Lean4Lean.TrProj.weak'` | :641 | proved |
| `Lean4Lean.TrProj.weakN` | :664 | proved |
| `Lean4Lean.TrProj.weak'_inv` | :745 (`sorry` at :747) | **open** — blocked on `IsDefEqU.weakN_iff` |
| `Lean4Lean.TrProj.defeqDFC` | :749 | proved |
| `Lean4Lean.TrProj.mono` | :767 | proved (new, needed by `TrExprS.mono`) |
| `Lean4Lean.TrProj.wf` | :939 | proved |
| `Lean4Lean.TrProj.uniq` | :992 (`sorry` at :995) | **open** — needs unique typing + type-former injectivity + ι-registry functionality |
| `Lean4Lean.TrProj.instN` | :1296 | proved |
| `Lean4Lean.TrProj.instL` | :1588 | proved |

**`Lean4Lean/Verify/Environment/Lemmas.lean`** — the reduction interface:

| Lean name | file:line | role |
|---|---|---|
| `Lean4Lean.TrEnv.proj_defeq` | :1021 | **the headline theorem, fully proved** (~130 lines): `P_i d ≡ fields[i]` when `d ≡ ctor cus (params ++ fields)` |
| `Lean4Lean.TrEnv'.structure_rec` / `TrEnv.structure_rec` | :523 / :644 | kernel structure facts (`ival.all = [S]`, one ctor, no indices) → the recursor's telescope split |
| `Lean4Lean.TrEnv'.ctor_arity` / `TrEnv.ctor_arity` | :449 / :503 | kernel `numParams + numFields` = model Π-arity |
| `Lean4Lean.TrEnv'.IotaRule` (structure) + `.step` | :782 / :807 | packaged conclusion of the ι-inverse with a one-step transport lemma |
| `Lean4Lean.TrEnv'.pats_iota_inv_shape` / `TrEnv.pats_iota_inv_shape` | :826 / :903 | inverse of `pats_iota'`, with the model-side rule shape |
| `Lean4Lean.VEnv.IsDefEqU.betaN` / `.mkApps_congr` / `.beta_app`, `VEnv.HasType.mkApps_inv_head` | :994 / :980 / :970 / :959 | the β-machinery `proj_defeq` runs on |
| `Lean4Lean.Aligned.constants_pull`, `AddQuot.pull`, `AddQuot1.pull`, `pull_insert`, `mkRecName_inj` | :439, :201, :192, :184, :513 | plumbing |

**`Lean4Lean/Verify/Environment/Basic.lean`** — `TrIndType` (`:216`) gained `all`, `numParams`,
`numIndices`; `TrRecursor` (`:237`) gained `name_major` (a recursor is named after the former it
eliminates). Without these nothing identifies *which* recursor eliminates a given structure.

**`Lean4Lean/Verify/TypeChecker/InferType.lean`** — `inferProj.WF` split:
`Lean4Lean.inferProj.WF_struct` (:392, `sorry` at :398) and `Lean4Lean.inferProj.WF` (:406, `sorry`
at :410). The branch also **fixed a latent statement bug in master**: master's
`inferProj.WF` concluded `∃ ty', c.TrTyping (.proj st i e) ty e' ty'` — asserting the *struct's*
translation `e'` is the translation of the projection — and took `hasty : c.HasType e' ty'` with
`ty'` auto-bound. Now `∃ e'' ty', … e'' ty'` and `hasty : … ety'`.

**Kernel-side (executable) change** — `Lean4Lean.inductiveReduceRecCore` (Inductive/Reduce.lean:75),
extracted from `inductiveReduceRec`, with `Lean4Lean.inductiveReduceRecCore.WF`
(Verify/TypeChecker/WHNF.lean:17). I diffed the split: it is byte-for-byte the original body with
`majorIdx` recomputed as `rval.getMajorIdx` (the caller bound `majorIdx := info.getMajorIdx`), so
**behaviour-preserving** as claimed. This is ι-consumer content that happened to land on `trproj`
first (commit 6fd8a1d); the merge `20ec229` confirms `iota` carries its own copy.

**Tests** (both 100 % `P`): `Lean4Lean/Tests/ProjShape.lean` (185 lines, kernel side) and
`Lean4Lean/Tests/ProjInhabit.lean` (597 lines, model side).

---

## (b) Commit narrative

`iota..trproj` is 24 commits over 2026-08-26 → 2026-09-10, in five milestones with **two full
reworks**.

### M1 — first cut (2026-08-26 … 08-28), `f252c3c` … `b6a5a38`

- `f252c3c` merge iota into trproj (TrProj needs `env.pats` / `SimplePattern.iota` / `pats_iota'`).
- `697e094` `TrProj` defined as `S.rec params motive (λ fields. field_i) e` with a **free
  existential motive**; signature gains `(env) (U)`, ~25 dependent sites repaired; 5 of 7 lemmas
  proved, `weak'_inv` and `uniq` left as `PROJ-TODO`.
- `fee3ada` `TrEnv.proj_defeq` *stated* (proof `PROJ-TODO`), `AddInduct.ctor_find` added.
- **`7a5e96d` — first correction.** The free motive made `TrProj` non-functional: on a *neutral*
  major, well-typedness constrains the motive only on constructor-shaped inputs, so two spines
  with motives agreeing on constructors but differing on a variable both satisfied `TrProj` yet
  were not defeq — i.e. `TrProj.uniq` would have been **false**. Fix at this stage: pin the motive
  to the **constant** motive `λ _. fieldTy`. Explicitly scoped out dependent fields (Σ/Subtype).
- `18f2b21` `TrEnv.pats_iota_inv` (inverse of `pats_iota'`), backed by new `AddInduct.find?_mono`,
  `rec_reg`.
- `b6a5a38` `TrProjCtor` introduced (constructor name exposed) because the previous `proj_defeq`
  statement was **unprovable**: the ι rule's constructor and the constructor spine `d` reduces to
  were unrelated names.

### M2 — diagnosis of the dead end (2026-09-03), `7f62db2`

`docs: record corrected proj_defeq residual (rec_reg route insufficient)` — the `rec_reg` route
cannot establish that `rval` is a *structure* recursor, because the ι key records only the **sum**
`numMotives+numMinors+numIndices`. This commit is the honest write-up that motivated M3.

### M3 — principled rework (2026-09-04), `fc9fbfc` … `f7dabf1`

- `fc9fbfc` merge the corrected `iota` (derived `AddInduct` bookkeeping, real `VInductDecl.WF`).
- **`811a52a` — second correction, the design one.** The constant motive was *wrong for dependent
  fields*: it cannot type `Sigma.snd : β[π₁ p/x]`. Replaced by the **chained dependent motive**
  `λ x. F_i[f_j := P_j x]` with earlier projection functions, plus the per-field level list `uss`.
  `Theory/Proj.lean` created with the builders and their lift/inst/instL theory;
  `Tests/ProjShape.lean` added (kernel validates the builders on Prod/Sigma/PSigma/Subtype/Fin/And
  and a 3-field chain, with negative controls).
- `75ffde9` ι-side: `RuleShape.nrec` pins the reduct's recursive-argument count (pure ι content
  that landed here; the review, F20, says it should have been cherry-picked onto `iota`).
- **`83860e9` — `TrEnv.proj_defeq` becomes a theorem.** Proof: `P_i d ≡ P_i spine` (congruence),
  `pats_iota_inv_shape` names the registered rule, `IsDefEq.pat` fires it, then two `betaN` steps —
  through the rule template and through `fieldSelector`. At this point the *kernel* telescope split
  (`numMotives = 1`, `numMinors = 1`, `numIndices = 0`) was still a **hypothesis**.
- `f7dabf1` docstring tidy, unused lemmas dropped. **This is the commit the 2026-09-07 review was
  run against.**

### M4 — review response (2026-09-08), `2a901f4` … `6fd8a1d`

Eight commits, most of them direct answers to `REVIEW_2026-09-07.md` findings:

- `2a901f4` merge the *re-corrected* iota (direct-block `VInductDecl.WF`, prefix-scoped ι
  obligation, `recSplit?`/`pats_split` decoder **deleted** — review F10). `TrEnv.pats_iota` and
  `pats_iota_inv` dropped as counts-only weakenings (F09).
- `e9fefbe` `TrProjCtor` becomes a **structure** with named fields (F13: it was a
  10-existential/12-conjunct predicate destructured positionally at seven sites). Two zero-use
  wrappers (`TrProjCtor.toTrProj`, `TrProj.exists_ctorName`) deleted (F29).
- `e202975` **`proj_defeq` restated on the kernel's structure facts** instead of the recursor
  telescope split (F07: the split had no in-repo discharge path). `TrEnv.structure_rec` bridges the
  two; `TrIndType`/`TrRecursor` gain the fields that make the bridge possible.
  `pats_iota_inv_shape`'s 17-component existential packaged as `TrEnv'.IotaRule` + `.step` (F28).
- `273cd2c` `inferProj.WF` **split** into `WF_struct` (scoped, honest) and the general one whose
  docstring now says plainly it is *not provable as stated* (B3/F03 — the old docstring claimed
  "provable in principle" while the branch's own test shipped `Refl` as a negative control).
- `acd6b46` `Tests/ProjInhabit.lean`: `TrProjCtor` **inhabited** on a plain and a `Sigma`-shaped
  block declared through `VEnv.addInduct`, with `#guard_msgs in #print axioms` pins (F19: the
  docstring asserted inhabitation on the strength of a non-theorem).
- `d7ec0fa` `Theory/Proj.lean` refactored: every builder proved **once against `VExpr.subst`**
  instead of once per operator (F12: ~6–7 copy-pasted `lift'`/`inst` induction pairs). −405/+… in
  Proj.lean; generic `Lift`/`VExpr`/`List` lemmas moved next to their definitions (F32).
  `master`'s `lift'_inst_hi` is now the `m = 0` case of the new `lift'_instN_hi`.
- `de1ea39`, `d114c2d`, `ba118fd`, `b4aba6d` — docstring settling, 100-column rewrap (F43/F14),
  `Decidable` instances moved to `Tests/ShapeDecide.lean` (F34), `toParams` exercised end-to-end
  (F23).
- `6fd8a1d` `inductiveReduceRecCore` split out of the kernel's `inductiveReduceRec` and
  `inductiveReduceRecCore.WF` proved — the **first real consumer** of the ι interface (answers F09's
  "zero consumers" for the ι half; the *projection* half still has none).

### M5 — final merge (2026-09-10), `20ec229`

Trivial: `iota` had independently re-landed 6fd8a1d/b4aba6d content; the merge keeps trproj's copies
and takes only one docstring fix (`pats_iota` → `pats_iota'`). **1 line changed.**

### Reverts / rework summary

No literal `git revert` in `iota..trproj` (the revert pair cb920e1/3bbdb22 is on the `iota` series).
The rework is by replacement: the motive was changed **twice** (free → constant → chained
dependent), `proj_defeq`'s statement **three times** (ctor buried → `TrProjCtor` → kernel structure
facts), and the ι-side decoder `recSplit?` was introduced and deleted. Two merges (`fc9fbfc`,
`2a901f4`) are labelled "corrected iota", i.e. the ι branch itself was reworked twice underneath.

---

## (c) Claims made in the notes

Sources: `TRPROJ_CONTRIBUTION.md` (**stale**, 2026-08-28, describes the *constant-motive* design),
`PR_trproj.md` (2026-09-08, current), `trproj-commission.md` (2026-08-27, the brief),
`downstream-asks-commission.md` (2026-09-09, round-3 brief), `REVIEW_2026-09-07.md` (2026-09-08).

Status legend: **T** checked-true, **F** checked-false, **U** unverified (needs a build / deeper
proof reading).

| # | Claim | Source | Status | How to verify |
|---|---|---|---|---|
| 1 | `TrProj` was `sorry` on master, "and with it every lemma about it" | PR_trproj §Summary | **T** | `git grep -n -w sorry master -- Lean4Lean/Verify/Typing/Expr.lean Lean4Lean/Verify/Typing/Lemmas.lean` → def + 7 lemmas |
| 2 | `TrProj` is now a real definition; `TrProjCtor` is a structure with named fields `params_length, ctor, field_lt, minor_arity, major_ty, fn_ty, eq` | PR_trproj | **T** (but the list omits `pat`, the first field) | `sed -n '90,135p' Lean4Lean/Verify/Typing/Expr.lean` |
| 3 | `TrProj.weak'`, `.weakN`, `.mono`, `.instN`, `.instL`, `.wf`, `.defeqDFC` are proved; they were `sorry` on master | PR_trproj | **T** | grep the 9 `TrProj.*` lemmas in `Verify/Typing/Lemmas.lean`; only :747 and :995 are `sorry` |
| 4 | `TrEnv.proj_defeq` **is a theorem** (no `sorry` of its own) | PR_trproj, REVIEW §2 | **T** | `sed -n '1021,1160p' Lean4Lean/Verify/Environment/Lemmas.lean` — full tactic proof, no `sorry` |
| 5 | `proj_defeq` takes what `inferProj`/`reduceProjCore` actually check (non-mutual, single-ctor, non-indexed) rather than the recursor telescope split | PR_trproj | **T** | its hypotheses are `hall : ival.all = [S]`, `hctors : ival.ctors = [ctorName]`, `hnind : ival.numIndices = 0` (:1032) |
| 6 | "Sorry census, non-`Experimental`: ι branch 21, this branch 16. No new axioms." | PR_trproj §Validation | **T** | `git grep -n -w sorry {iota,trproj} -- 'Lean4Lean/**' \| grep -v Experimental`, minus 3 comment/docstring hits on iota and 6 on trproj → 21 / 16. master = 23. `git diff master..trproj \| grep '^+\s*axiom '` → none |
| 7 | "Closed: the `TrProj` definition and `TrProj.weak'`, `.instN`, `.instL`, `.wf`, `.defeqDFC`. New: `inferProj.WF_struct`." | PR_trproj | **T** | same grep; projection-side sorries 9 (master) → 4 (`weak'_inv`, `uniq`, `WF_struct`, `WF`) |
| 8 | The motive is pinned to make `TrProj` a **functional** relation; a free motive would make `TrProj.uniq` false | TRPROJ_CONTRIBUTION, commit 7a5e96d | **U** (argument is plausible and specific; not mechanized) | the counterexample is informal; would need two `TrProjCtor` witnesses with non-defeq motives |
| 9 | The constant motive is "correct for non-dependent structure fields … dependent fields are out of scope" | TRPROJ_CONTRIBUTION §A1 | **F, superseded** | that file describes the *abandoned* design; 811a52a replaced it with the chained dependent motive and `Tests/ProjShape.lean:120–145` exercises `Sigma.snd`/`PSigma`/`V3` |
| 10 | "15 `IOTA-TODO` markers are unchanged"; "3 `PROJ-TODO(soundness)`" | TRPROJ_CONTRIBUTION | **F, stale** | `git grep -n 'IOTA-TODO\|PROJ-TODO' Lean4Lean` → **zero** hits on trproj HEAD |
| 11 | `TrEnv.pats_iota_inv` "fully proved, sorryAx-free" | TRPROJ_CONTRIBUTION | **F, stale** | `TrEnv.pats_iota_inv` no longer exists (deleted in 2a901f4 as a counts-only weakening); its successor is `pats_iota_inv_shape` |
| 12 | `TrEnv.proj_defeq`'s prior statement "was unprovable (the two `ctorName`s were unrelated)" | TRPROJ_CONTRIBUTION | **T** | commit b6a5a38 message + the `TrProjCtor` introduction |
| 13 | "the expansion's typing is derivable from the forward rules of `IsDefEq` alone" — no structure η, no K-like, no injectivity | PR_trproj, Theory/Proj.lean:47–52 | **U-leaning-T** | the derivation is written out in `Theory/Proj.lean:38–52` and *instantiated* in `Tests/ProjInhabit.lean`; the **general** construction is the open `inferProj.WF_struct`. Verify by `lake env lean Lean4Lean/Tests/ProjInhabit.lean` |
| 14 | `TrProjCtor` is inhabited (sorry-free) for a plain and a `Sigma`-shaped dependent structure; `#print axioms` = `[propext, Quot.sound]` | PR_trproj §Validation, acd6b46 | **U** (guard_msgs present, not run) | `Lean4Lean/Tests/ProjInhabit.lean:563–580`; run `lake build Lean4Lean.Tests` — `#guard_msgs` fails the build if the profile changed |
| 15 | `TrEnv.proj_defeq`'s `sorryAx` is inherited from unique typing, Π-injectivity and `VEnv.WF.patsStrong` — not its own | PR_trproj, Tests/ProjInhabit.lean:582–595 | **U** (the `#guard_msgs` pin exists and lists `sorryAx`) | `#print axioms Lean4Lean.TrEnv.proj_defeq` in a built checkout |
| 16 | `Tests/ProjShape.lean`: the **kernel** accepts `fun ps x => projFn x` for Prod/Sigma/PSigma/Subtype/Fin/And/V3, `projTy` `isDefEq` to `inferType (.proj S i x)`, `projFn (mk ps fs)` whnfs to `fs[i]`, reflexive control fails | PR_trproj | **U** (code present and looks right) | `lake env lean Lean4Lean/Tests/ProjShape.lean`; the `run_meta` block at :121–145 |
| 17 | `minor_arity` excludes a reflexive structure, "which the `np+1+1+0` key does not" | PR_trproj, Expr.lean:110–116 | **T** | `Tests/ProjShape.lean:139–144` asserts `Refl.rec`'s minor has `binderArity? 1 = some 2` |
| 18 | `inferProj.WF` "is not provable as stated with the current `TrProj`" — `inferProj` also accepts reflexive/indexed/nested single-ctor types, e.g. `Lean.Language.SnapshotTree.element` | PR_trproj, REVIEW B3 | **U-leaning-T** | REVIEW cites mechanized probes `review-artifacts/probes/proj_gap.lean`, `core_proj.lean`, `l4l_proj*.lean`; re-run them |
| 19 | `IsDefEqU.weakN_iff` forward (Cluster 2 of the commission) was **not** closed and is a genuine research blocker (module import cycle + same-measure logical cycle) | TRPROJ_CONTRIBUTION §Cluster 2, PR_trproj | **T** (not closed) / **U** (the "genuine blocker" analysis) | `sed -n '170,178p' Lean4Lean/Theory/Typing/UniqueTyping.lean` — still `sorry`, unchanged from master |
| 20 | "No new `sorry` in Cluster 2, no renamed gap" | TRPROJ_CONTRIBUTION | **T** | `git diff master..trproj -- Lean4Lean/Theory/Typing/UniqueTyping.lean` → empty |
| 21 | `Theory/Proj.lean` proves structural lemmas "once against `VExpr.subst` instead of once per operator"; master's `lift'_inst_hi` is the `m=0` case of `lift'_instN_hi` | PR_trproj, d7ec0fa | **T** | `Theory/VExpr.lean:1014–1020`; Proj.lean shrank by 405 lines in d7ec0fa |
| 22 | `TrProj.uniq` compares two *structure names* `s₁ s₂` "because the `proj` case of `IsDefEqE` compares two projections up to the index alone" | PR_trproj | **T** (statement) / **U** (justification) | `Verify/Typing/Lemmas.lean:992–995`; REVIEW F25 disputes it ("both consumers instantiate one `s`") |
| 23 | `lake build Lean4Lean.Theory/Verify/Tests` and `Lean4Lean.Experimental` are green | PR_trproj, REVIEW §"Established facts" | **U** (explicitly not run — read-only task) | `lake build && lake build Lean4Lean.Experimental && lake build Lean4Lean.Tests` |
| 24 | "the kernel↔model bridge is unchanged / kernel unchanged" — *not literally claimed*, but PR_trproj's "Changes to existing definitions" omits `Lean4Lean/Inductive/Reduce.lean` | PR_trproj (omission) | **F** | `git diff master..trproj -- Lean4Lean/Inductive/Reduce.lean` — 34 lines, the executable kernel is refactored. Behaviour-preserving (verified by diff), but undisclosed in the trproj PR text |
| 25 | `TrEnv.proj_defeq` "is the interface the `proj` case of `TrExprS` soundness consumes" | earlier docstring (fixed) / REVIEW F38 | **F** | `grep -rn proj_defeq Lean4Lean` → only its own definition + the axiom-profile test. **Zero in-library consumers** |
| 26 | Round-3 brief: "`TrEnv.proj_defeq` — DELIVERED. No obligations remain. Do not re-open." | downstream-asks-commission.md §R4 | **T** as to proof status; **misleading** as to reach — the theorem is unused inside lean4lean and `reduceProjCore.WF` (Verify/TypeChecker/Reduce.lean:145) is still `sorry` | grep as in #25 |
| 27 | Round-3 brief: "`TrProj.uniq` · reach 44 of 63 declarations, and all four capstones" | downstream-asks-commission.md §R1 | **U** (downstream claim, unverifiable here) | needs the downstream repo |
| 28 | "no new axioms, no `native_decide`" | REVIEW §"Established facts", PR_trproj | **T** | `git diff master..trproj \| grep '^+\s*axiom '` → none; `grep -rn native_decide Lean4Lean` → none |
| 29 | "Every line this branch added past 100 columns is rewrapped" (d114c2d) | commit message | **T** | `awk 'length>100'` over all branch-touched files: the only hits are master lines (`Verify/Environment/Lemmas.lean:285,375`, `Theory/Typing/Pattern.lean:27`, `Theory/Typing/Strong.lean:253`, `Verify/TypeChecker/WHNF.lean:195`) |
| 30 | The `inductiveReduceRec` split is "behaviour-preserving: the extracted body is the original one, with `getMajorIdx` recomputed" | 6fd8a1d | **T** | `git diff master..trproj -- Lean4Lean/Inductive/Reduce.lean`; the caller bound `majorIdx := info.getMajorIdx` |
| 31 | `TrProj` is monotone under `VEnv.LE` (required by `TrExprS.mono`) | TRPROJ_CONTRIBUTION A1, commission R4 | **T** | `TrProj.mono`, `Verify/Typing/Lemmas.lean:767` |
| 32 | The design "formalizes the argument Mario himself put in `divergences.md`" | REVIEW §2 | **T** | `divergences.md` entry on `inferProj`/`toCtorWhenStruct`: "Lean4lean's rule keeps `Expr.proj` no more powerful than the recursor the kernel generates" |
| 33 | "The shape is the thesis's `inv_x` … with the dependent typing of `π₂ p : β[π₁ p/x]`" | PR_trproj, Theory/Proj.lean:11–22 | **Partly T** | `typesys.tex:11–17` and `Wtypes.tex:26–28` exist; but the thesis has **no** chained motive and never models `Expr.proj` (`grep '\proj' *.tex` → nothing). REVIEW F44 says the same |
| 34 | REVIEW: "Not upstreamable as it stands, but close in architecture" (4 blockers B1–B4) | REVIEW §1 | **Partly superseded** | B3 (`inferProj.WF` false as restated) was addressed by 273cd2c; F13/F28/F12/F09(ι half)/F19/F29/F34/F43 were addressed in M4. **B1, B2 (`VInductDecl.WF`, `patsStrong`) and B4 (does not build against current master) are ι-side and remain** |

---

## (d) Known limitations, open ends, divergences

### Open obligations introduced or left by this branch (4 of the tree's 16 `sorry`s)

1. `Lean4Lean.TrProj.weak'_inv` — `Verify/Typing/Lemmas.lean:747`. Strengthening. Blocked on
   `IsDefEqU.weakN_iff` (`Theory/Typing/UniqueTyping.lean:174`), which the commission asked for and
   the branch **declined to fake** — the write-up in `TRPROJ_CONTRIBUTION.md` §Cluster 2 argues the
   `trans` case is irreducible and both confluence routes (module import cycle; same-measure logical
   cycle) are blocked. That is the correct call, but it means Cluster 2 of the commission was not
   delivered.
2. `Lean4Lean.TrProj.uniq` — `Verify/Typing/Lemmas.lean:995`. **This is the load-bearing one**:
   `TrExprS.uniq` (:1000-ish, immediately below) inducts through it, so the entire uniqueness layer
   of the translation carries `sorryAx` because of it. Its residual: unique typing of the projection
   function, type-former injectivity (`Theory/Typing/Injectivity.lean`, a pre-existing master gap),
   and functionality of the ι registry (`pat_uniq`, an ι-branch gap).
3. `Lean4Lean.inferProj.WF_struct` — `Verify/TypeChecker/InferType.lean:398`. *New* `sorry` added by
   this branch. Needs `TrProjCtor` inhabited from an arbitrary kernel-accepted projection; only
   instances are mechanized.
4. `Lean4Lean.inferProj.WF` — `Verify/TypeChecker/InferType.lean:410`. Declared **not provable as
   stated** in its own docstring.

### Scope boundaries stated in the code

- `TrProjCtor`'s docstring (`Verify/Typing/Expr.lean:83–89`): "single-constructor types that are
  non-recursive, non-indexed and non-mutual. Projections of reflexive, indexed and nested
  single-constructor types are accepted by `inferProj` but are outside this relation — a
  **completeness boundary, not a soundness one**."
- **Structure η is not represented.** `Theory/Proj.lean:54–58` and `PR_trproj.md §Scope boundaries`.
  `IsDefEq` has no η rule for structures, so `tryEtaStructCore.WF`
  (`Verify/TypeChecker/IsDefEq.lean:227`) and `isDefEqUnitLike.WF` (:488) stay open. **Divergence
  from the thesis**: `Wtypes.tex:92–93` *does* take `(π₁ x, π₂ x) ≡ x` as an admitted η rule in the
  soundness model, precisely to avoid needing recursors for Σ. The branch takes the opposite route
  (recursors, no η), which is faithful to Lean's kernel but not to the thesis's model.
- `uss : Nat → List VLevel` is a total function, so it admits junk at indices `> i`
  (REVIEW F45, unfixed). The expansion only reads `uss 0 … uss i`, so `TrProj` is still functional
  in its observable part, but two different `uss` agreeing on `0..i` give literally equal terms and
  a proof of `uniq` must exploit that.
- `instPis`/`piBinders` are the **manifest**-binder reading; the kernel `whnf`s at each binder
  (`TrProjCtor.ctor` docstring; REVIEW F40). Non-manifest telescopes are silently out of scope.
- `TrProj` carries two `HasType` side conditions (`major_ty`, `fn_ty`). `.proj` is therefore the only
  `TrExprS` clause that is not purely syntactic.

### Divergences from Lean 4's real kernel

- The branch adds one **new** divergence-adjacent behaviour in the executable kernel only as a
  refactor (`inductiveReduceRecCore`), no semantic change. The one new `divergences.md` entry in
  `master..trproj` (`checkEqType` rejecting an `unsafe Eq`) is **ι-branch** content
  (`git diff iota..trproj -- divergences.md` is empty).
- `reduceProjCore.WF` (`Verify/TypeChecker/Reduce.lean:145`) is still `sorry`, so the branch does not
  connect `proj_defeq` to the executable projection reduction.

### Residual TODO markers

`grep -n 'IOTA-TODO\|PROJ-TODO' Lean4Lean` → **zero**; the only `TODO`s in the tree are upstream's
(`Environment.lean:63`, `Expr.lean:44,89`, `Inductive/Add.lean:279,574`,
`Theory/Typing/Meta.lean:37`). The status-memo register the review complained about (F17/F42) has
largely been cleaned out of the projection files.

---

## (e) Preliminary quality assessment

### Design soundness — **good, and visibly earned**

The core move (projection = generated-recursor application) is the *right* one for this model:
it is exactly the kernel's own justification for `Expr.proj`, already written down by upstream in
`divergences.md`, and it needs no new `IsDefEq` rule — so it cannot introduce unsoundness by
construction. Two separate corrections (free → constant → chained dependent motive) each fixed a
real defect that was *identified before* it caused a false theorem: the free motive would have made
`TrProj.uniq` false, the constant motive could not type `Sigma.snd`. Catching these is good
engineering, but note the cost: the first two designs shipped as commits with confident PR prose and
were replaced within days, and `TRPROJ_CONTRIBUTION.md` still documents the abandoned one.

Weak points a maintainer will probe:
- **Typing inside a translation relation.** `major_ty`/`fn_ty` make `TrExprS`'s `.proj` clause
  depend on `HasType`. Nothing else in `TrExprS` does. This forces every structural lemma to
  transport typing (which is why `instN` needs `CtorHeaded` stability lemmas), and it means a
  `TrExprS` derivation for a projection cannot be built before typing. The alternative — a
  projection node in `VExpr` with its own ι and η rules — is question 1 in the PR and is arguably
  the cleaner answer; the branch is honest that this is the maintainer's call.
- **The `np+1+1+0` key is a sum.** It does not pin one motive / one minor / no indices; `minor_arity`
  and the kernel-side `structure_rec` hypotheses do the real work. The design therefore leans on
  `TrIndType`/`TrRecursor` fields the branch added itself, which are only discharged where an
  `AddInduct` is constructed — and nothing constructs one yet (`Verify/Environment.lean:208` is
  still `sorry` for `inductDecl`). So `proj_defeq` is a real theorem about a hypothesis nobody has
  yet established.

### Proof hygiene — **strong**

- `TrEnv.proj_defeq` is a genuine 130-line proof with a clear six-stage structure (A–F comments),
  not a shim.
- The d7ec0fa refactor (prove once against `subst`, derive `lift'`/`inst`) removed ~400 lines of
  copy-paste and *generalised* a master lemma (`lift'_inst_hi` ← `lift'_instN_hi`). That is a
  contribution to upstream's own library, not just to the branch.
- No new axioms, no `native_decide`, no over-long lines introduced, `Decidable` instances scoped to
  `Tests/ShapeDecide.lean`.
- **Two kinds of test, both real**: `ProjShape.lean` validates the builders against the *actual Lean
  kernel* (`Environment.addDeclCore`, `Meta.whnf`, `isDefEq`) with negative controls (wrong level
  list, reflexive structure); `ProjInhabit.lean` inhabits `TrProjCtor` inside the *model* through
  `VEnv.addInduct`, sorry-free, with `#guard_msgs` axiom pins. This is better test discipline than
  the surrounding repo.
- `TrProj.uniq`'s `sorry` taints `TrExprS.uniq` and hence a large fraction of `Verify` — this is
  disclosed in PR_trproj ("Axiom cone, plainly") and is not hidden.

### Documentation — **very good content, wrong register in places**

`Theory/Proj.lean`'s module docstring (58 lines) is genuinely excellent: it states the de Bruijn
conventions, the typing derivation (a)–(c), and the η boundary. `TrProjCtor`'s per-field docstrings
are exactly what a reviewer needs. The M4 commits removed most of the status-memo prose
(`#print axioms` narration, "left to the maintainers", `IOTA-TODO` tags) the review flagged.

Remaining problems:
- **`TRPROJ_CONTRIBUTION.md` is stale and actively misleading** (constant motive, 15 IOTA-TODOs,
  `pats_iota_inv` which no longer exists, 3 PROJ-TODOs). It must not be handed to anyone.
- The thesis attribution is still slightly inflated (claims 33, above).
- `PR_trproj.md` does not disclose the executable-kernel change (claim 24).

### Churn and dead code

- Churn is high but *directed*: 24 commits, two design reversals, two upstream-branch re-merges.
  The final merge is 1 line. Since the repo squash-merges, branch history never reaches upstream,
  so the churn costs review time only.
- Dead/near-dead code remaining after the F29 cleanup: `VExpr.projTy` (used only by
  `Tests/ProjShape.lean` and docstrings — the `Verify` layer uses `projMotiveBody` instead),
  `VExpr.instFields_nil` (`@[simp]`, 1 ref), `VExpr.projMotiveBody_zero` (documents the constant-
  motive special case, otherwise unused), `VExpr.instFields_app`/`instFields_mkApps`/`projFn_eq`/
  `projFns_succ`/`projFns_length` (internal stepping stones, fine). `Pattern.RHS.Generic`
  (Theory/Typing/Pattern.lean:181) is still a `def` nothing uses — ι-side.
- **The real dead-weight issue is reach, not lines**: `TrEnv.proj_defeq`, `TrEnv.structure_rec`,
  `TrEnv.ctor_arity` and `TrEnv.pats_iota_inv_shape` have **no consumer in lean4lean** other than
  `proj_defeq` itself. `reduceProjCore.WF` was never attempted against them. That is review finding
  F09 and it is only half-answered: the branch produced an ι consumer
  (`inductiveReduceRecCore.WF`) but no *projection* consumer.

### Likely upstream reception

Optimistic-but-honest read:

- **Accept-shaped**: `Theory/Proj.lean` and its `subst`-based theory; the `TrProj`/`TrProjCtor`
  definition; the six proved structural lemmas; `TrEnv.proj_defeq`; the two test files; the
  `inferProj.WF` statement fix. These retire five `sorry`s and turn an opaque `def` into something
  refutable — a strict improvement no matter what the maintainer decides about the design.
- **Will be questioned**: the typing side conditions in `TrProj`; `uss` as a total function;
  `TrProj.uniq` quantifying over two structure names; `TrProjCtor` as a `Prop` structure with data
  parameters (the PR asks this explicitly, question 3); and the absence of any internal consumer.
- **Blocks the PR, and is not this branch's fault**: the projection work sits on top of `iota`,
  whose B1 (`VInductDecl.WF` admits inconsistent well-formed environments, mechanized in
  `review-artifacts/counterexamples/cexB.lean`) and B2 (`VEnv.WF.patsStrong` plausibly false) are
  unresolved, and B4 (neither branch builds against current master; a repair patch exists at
  `review-artifacts/merge-repair/master-into-trproj-repair.patch` but is not committed). **`trproj`
  cannot be upstreamed before `iota` is.**
- The PR's four closing questions are well-posed and show the author knows where the design
  decisions are. That register — "here is what I built, here is exactly what it does not cover, and
  here are the four calls I want from you" — is the right one for this repo.

**Bottom line for the blueprint**: the projection contribution is the more self-contained and the
more clearly-valuable of the two branches. Its headline theorem is genuinely proved, its scope
boundary is honestly drawn and mechanically tested on both sides of the kernel/model divide, and it
deleted more `sorry`s than it added. Its weaknesses are (i) no consumer, so the value is potential
rather than realised; (ii) `TrProj.uniq`, the one that actually gates `TrExprS.uniq`, is still open;
(iii) it inherits the ι branch's unresolved soundness questions wholesale.
