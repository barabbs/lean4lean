# Contribution inventory — branch `iota` (ι-reduction / inductive-block specification)

Reader-agent notes for the lean4lean blueprint. **All file:line references are against the
current `trproj` checkout** (repository root,
HEAD `20ec229`), unless a `git show <rev>:…` path is given. `iota` (`38ea0de`) is a strict
ancestor of `trproj`, and `master` (`8223d22`) is a strict ancestor of `iota`, so the branch
is up to date with upstream and the ι files are byte-identical between `iota` and `trproj`
except `Lean4Lean/Verify/Typing/Lemmas.lean` (projection work) — verified with
`git diff iota trproj`.

Scale: `git diff --stat master..iota` = **45 files, +5628 / −331**, 28 commits.

---

## (a) Goal and design

### The hole in lean4lean this fills

On `master` the abstract model (`Lean4Lean/Theory/`) has **no account of ι-reduction** at
all. Three declarations are literally `sorry`:

```
git show master:Lean4Lean/Theory/Inductive.lean            -- 8-line file
  :5  def VInductDecl.WF   (env : VEnv) (decl : VInductDecl) : Prop      := sorry
  :7  def VEnv.addInduct   (env : VEnv) (decl : VInductDecl) : Option VEnv := sorry
git show master:Lean4Lean/Theory/Typing/InductiveLemmas.lean
  :9  theorem addInduct_WF … : Ordered env'                              := sorry
```

and on the refinement side `Lean4Lean.AddInduct` was a constructor-less `Prop`
(master's own comment at `Verify/Environment/Basic.lean:101`: *"This definition is
essentially a `sorry`"*), which made `TrEnv'.induct` vacuous, which in turn made
`TrEnv'.no_inductInfo` true and master's `addQuot.WF` a **vacuous** proof
(`git show master:Lean4Lean/Verify/Environment.lean:139`:
`exact (checkEqType.WF wf).bind fun _ h => False.elim h`).

So: in upstream lean4lean, no inductive type ever enters a translated environment, no
recursor ever computes, and the type theory has β, δ (via `defeqs`), η, proof irrelevance
and the quotient rule, but not ι. The branch supplies ι.

### Design, in one paragraph

ι is modelled as a **schematic rewrite rule registry** rather than as a new `IsDefEq`
constructor specialised to recursors. `VEnv` gets a third field `pats` beside
`constants`/`defeqs`; `VEnv.addInduct` installs one entry per recursor rule; `IsDefEq`
gets one generic constructor `pat` that fires any registered entry. This re-uses two
pieces Mario already had in the tree and deliberately promotes them from prototype to
live: `Lean4Lean.Pattern` / `Lean4Lean.SimplePattern` (with the constructor
`SimplePattern.iota recursor major constr args` already present on master,
`git show master:Lean4Lean/Theory/Typing/Pattern.lean:226`) and the abstract class
`Lean4Lean.VEnv.Params` in `ChurchRosser.lean`, whose `Pat`/`pat_wf` fields were an
*assumed* pattern-reduction relation. The branch makes `env.pats` a concrete instance of
`Params.Pat` (`VEnv.toParams`) and adds the one forced new class field `pat_env`.

Relation to Carneiro's thesis (`../lean-type-theory/*.tex`):

* `VInductDecl.WF` is the thesis §2.6.1–2.6.4 specification of an inductive block
  (positivity, constructor result types, the universe bound, large elimination, recursor
  telescope, ι rules). Docstrings cite these sections by number throughout
  `Theory/Inductive.lean`.
* `IsDefEq.pat` asserts the reduct **at the redex's type with no typing premise on the
  reduct** — i.e. it takes the thesis's *regularity of ι* as a rule. The debt is repaid (or
  rather, deferred) in the strong system as `VEnv.PatsStrong`
  (`Theory/Typing/EnvLemmas.lean:130`), documented as
  "the thesis's regularity lemma for `⇝` (`typesys.tex`, 'Regularity continued';
  `unique.tex`, 'Regularity of reductions')".
* **Divergence from the thesis**: the thesis *generates* recursor types and ι rules from
  the block's specification; this branch instead **carries kernel-shaped recursor data**
  (`VRecursor`, `VRecRule`, new field `VInductDecl.recs`) and pins its shape with 20
  `VInductDecl.WF` fields. This is the single biggest architectural deviation and it
  survived the post-review rework.

### Key declarations (verified by grep on the current checkout)

Theory — the rule and its registry:

| Fully-qualified name | file:line | role |
|---|---|---|
| `Lean4Lean.VEnv.pats` (field) | `Lean4Lean/Theory/VEnv.lean:21` | registry `(p : Pattern) → p.RHS × p.Check → Prop` |
| `Lean4Lean.VEnv.addPat` | `Theory/VEnv.lean:44` | register a rule (dependent-eq encoding) |
| `Lean4Lean.VEnv.LE.pats` (field) | `Theory/VEnv.lean:50` | monotonicity of `≤` in `pats` |
| `Lean4Lean.VEnv.IsDefEq.pat` (ctor) | `Theory/Typing/Basic.lean:60` | **the ι rule** |
| `Lean4Lean.VEnv.PatTyped` | `Theory/Typing/Basic.lean:92` | `VDefEq.WF` analogue for a schematic rule |
| `Lean4Lean.VEnv.PatWF` | `Theory/Typing/Basic.lean:104` | `PatTyped ∧ RHS.TemplateHeaded` |
| `Lean4Lean.VEnv.Ordered.pat` (ctor) | `Theory/Typing/Lemmas.lean:265` | `Ordered` gains a rule-registration step |
| `Lean4Lean.VEnv.Ordered.patWF` | `Theory/Typing/Lemmas.lean:474` | every registered rule is `PatWF` |
| `Lean4Lean.VEnv.addPat_le` / `addPat_self` | `Theory/Typing/Lemmas.lean:198`/`:200` | |
| `Lean4Lean.VEnv.Params.pat_env` (field) | `Theory/Typing/ChurchRosser.lean:32` | the one new field on Mario's class |

Theory — the pattern engine extensions (`Theory/Typing/Pattern.lean`, master 232 lines →
725; 419 lines tagged `I`, 77 tagged `P` but in fact ι content, see the attribution caveat
below):

| Name | line | role |
|---|---|---|
| `Lean4Lean.Pattern.RHS.Uses` / `.Generic` | `:170` / `:181` | "the reduct's holes are exactly a context's variables"; used by `PatTyped` |
| `Lean4Lean.Pattern.Check.Realizes` | `:307` | side-conditions as **data** (avoids `IsDefEq` under `∃`) |
| `Lean4Lean.Pattern.Check.Realizes.toOK` / `Check.OK.exists_realizer` | `:318` / `:332` | equivalence with master's `Check.OK` |
| `Lean4Lean.Pattern.varN_pathOf` | `:494` | path into a spine pattern |
| `Lean4Lean.SimplePattern.iotaRHS'` / `iotaRHS` | `:569` / `:581` | **the ι reduct builder** |
| `Lean4Lean.SimplePattern.iotaRHS'_apply` | `:625` | its `apply` normal form (kernel-slicing agreement) |
| `Lean4Lean.Pattern.RHS.TemplateHeaded` | `:690` | "the reduct is a closed λ-template applied to holes" |
| `Lean4Lean.Pattern.RHS.subst_apply`, `matches_subst`, `Check.Realizes.map_subst` | `:453`,`:460`,`:473` | stability under `Subst` (needed by master's `substEq'`) |

Theory — the block specification (`Theory/Inductive.lean`, 4 lines on master → 455; 438 `I`):

| Name | line | role |
|---|---|---|
| `Lean4Lean.VExpr.CtorResult` | `:44` | §2.6.1 constructor result type |
| `Lean4Lean.VExpr.MajorApp` | `:63` | §2.6.3 major premise |
| `Lean4Lean.VExpr.ValidIndApp` / `FieldPositive` / `CtorPositive` | `:75`/`:93`/`:101` | §2.6.1 strict positivity (mirrors kernel `checkPositivity`) |
| `Lean4Lean.VExpr.MotiveShape` / `MinorHeaded` / `MinorFor` | `:121`/`:128`/`:134` | §2.6.3 motive & minor premises |
| `Lean4Lean.VExpr.RecShape` | `:143` | §2.6.3 recursor telescope |
| `Lean4Lean.VExpr.CtorShape` | `:157` | |
| `Lean4Lean.VExpr.majorFormer?` | `:161` | the type former a recursor eliminates |
| `Lean4Lean.VExpr.RuleShape` | `:174` | §2.6.4 reduct shape, incl. the `nrec` recursive-argument count |
| `Lean4Lean.VInductDecl.LargeElim` / `.LargeElimShape` | `:226` / `:237` | §2.6.2, mirrors kernel `isLargeEliminator` (`Lean4Lean/Inductive/Add.lean:258`) |
| `Lean4Lean.VEnv.addRecRule` | `:257` | installs one ι rule |
| `Lean4Lean.VInductDecl.addTypes/addCtors/addRecs/addRules` | `:280`–`:292` | the four stages |
| `Lean4Lean.VEnv.addInduct` | `:316` | **replaces master's `sorry`** |
| `Lean4Lean.VInductDecl.WF` | `:335` | **replaces master's `sorry`**; 20-field structure |
| `Lean4Lean.VRecRule` / `VRecursor` / `VRecursor.getMajorIdx` | `Theory/VDecl.lean:20`/`:35`/`:46` | kernel-mirroring recursor data; `VInductDecl.recs` field at `:57` |

Theory — extension lemmas and the `Params` instance:

| Name | file:line | status |
|---|---|---|
| `Lean4Lean.VEnv.addInduct_le` | `Theory/Typing/InductiveLemmas.lean:89` | proved |
| `Lean4Lean.VEnv.addInduct_pat` | `…InductiveLemmas.lean:136` | proved |
| `Lean4Lean.VEnv.addInduct_WF` | `…InductiveLemmas.lean:229` | **proved** (was `sorry` on master) |
| `Lean4Lean.VEnv.WF'.pats_origin` | `…InductiveParams.lean:93` | proved |
| `Lean4Lean.VEnv.PatsIota` | `…InductiveParams.lean:133` | population invariant |
| `Lean4Lean.VEnv.WF.pat_simple/.pat_uniq/.pat_app_l/.pat_app_l_uniq/.pat_app_uniq` | `…InductiveParams.lean:249/260/297/306/334` | all **proved** |
| `Lean4Lean.VEnv.DefEqsAsPats` | `…InductiveParams.lean:378` | `extra_pat` taken as a *hypothesis* |
| `Lean4Lean.VEnv.toParams` | `…InductiveParams.lean:393` | the `Params` instance |
| `Lean4Lean.VEnv.inductParams` / `IsDefEq.crDefEq_of_induct` | `…InductiveParams.lean:419`/`:426` | demo: Church–Rosser on an axiom-free one-block env |

Theory — the strong system (the deferred obligation lives here):

| Name | file:line | status |
|---|---|---|
| `Lean4Lean.VEnv.IsDefEqStrong.pat` (ctor) | `Theory/Typing/Strong.lean:89` | carries the reduct's typing |
| `Lean4Lean.VEnv.PatStrong` / `PatsStrongOn` | `Strong.lean:663` / `:672` | subject reduction of a rule / of all rules |
| `Lean4Lean.VEnv.OrderedStrong` | `Strong.lean:679` | `{ordered, strong, pats}` — **replaces master's `Ordered.strong`** |
| `Lean4Lean.VEnv.WFPrefix` | `Theory/Typing/Env.lean:57` | prefix of a `WF'` derivation |
| `Lean4Lean.VEnv.PatsStrong` | `Theory/Typing/EnvLemmas.lean:130` | the prefix-scoped obligation |
| `Lean4Lean.VEnv.WF.strong` | `EnvLemmas.lean:263` | proved **from** `PatsStrong` |
| `Lean4Lean.VEnv.WF.patsStrong` | `EnvLemmas.lean:334` | **`sorry` — the one deferred ι obligation** |
| `Lean4Lean.VEnv.WF.orderedStrong` | `EnvLemmas.lean:339` | + `instance : CoeOut (VEnv.WF env) env.OrderedStrong` at `:343` |

Verify (refinement):

| Name | file:line | role |
|---|---|---|
| `Lean4Lean.TrIndType` | `Verify/Environment/Basic.lean:216` | one type former + its constructors |
| `Lean4Lean.TrRecursor` | `…Basic.lean:237` | telescope split, `k`, rules, `TrExprS` link to the kernel rhs |
| `Lean4Lean.AddInduct` | `…Basic.lean:272` | data-carrying `structure` in `Type`; `env_eq` `:296`, `le` `:308`, `wf` `:395`, `find?_mono` `:400`, `value_find` `:422`, `rec_find` `:434`, `rec_reg` `:464`, `ctor_find` `:494` are **theorems** |
| `Lean4Lean.TrEnv'.induct` (ctor) | `…Basic.lean:582` | now non-vacuous, **at every safety level** |
| `Lean4Lean.Aligned.pat` / `.block` (ctors) | `Verify/Environment/Lemmas.lean:21` / `:28` | |
| `Lean4Lean.Aligned.addRules` / `.addInduct` | `…Lemmas.lean:88` / `:102` | both **proved** |
| `Lean4Lean.TrEnv'.pats_iota'` / `TrEnv.pats_iota'` | `…Lemmas.lean:674` / `:749` | the ι-rule lookup with the **witness named** |
| `Lean4Lean.TrEnv'.pats_iota_inv_shape` / `TrEnv.pats_iota_inv_shape` | `…Lemmas.lean:826` / `:903` | the inverse (consumed by the projection work) |
| `Lean4Lean.TrEnv.iota_defeq` | `…Lemmas.lean:917` | thin wrapper over `IsDefEq.pat` |
| `Lean4Lean.TrEnv.iota_rec` | `…Lemmas.lean:929` | the end-to-end ι step |
| `Lean4Lean.TypeChecker.Inner.inductiveReduceRecCore.WF` | `Verify/TypeChecker/WHNF.lean:17` | the ι case of recursor reduction, ~130 lines, proved |
| `Lean4Lean.addQuot.WF` | `Verify/Environment/Quot.lean:500` | **the real quotient-initialisation proof** (615-line new file, sorry-free) |
| `Lean4Lean.checkEqType` unsafe-`Eq` rejection | `Lean4Lean/Quot.lean:24` | + `divergences.md` entry |

Collateral: `Lean4Lean/Inductive/Reduce.lean:75` factors `inductiveReduceRecCore` out of
`inductiveReduceRec` so the refinement has a handle on the ι step; `Theory/VExpr.lean` gains
~29 syntactic helpers (`mkApps`, `bvarsDesc`, `piArity`/`piBody`/`piBinders`,
`lamArity`/`lamBody`, `getAppFn`/`getAppArgs`, `headConst?`, `motiveFormer?`,
`RecHeaded`/`CtorHeaded`, `instance decClosedN`) at `:1051`–`:1335`.

Tests: `Lean4Lean/Tests/IotaShape.lean` (607 lines, entirely new) and
`Lean4Lean/Tests/ShapeDecide.lean` (78 lines, the `Decidable` instances kept out of the
theory). `IotaShape` translates the *real kernel's* `RecursorVal.type`, rule `rhs` and
constructor types with `Meta.ofExpr` and **decides** the `WF` shape clauses on them;
`checkIota` builds a redex, reduces it with the executable `inductiveReduceRec`, and checks
`SimplePattern.iotaRHS … |>.apply` gives the same term. The final `run_meta` (`:454`) runs
`checkShapes`/`checkTypesHaveRec` on 10 recursors, `checkAll` (= `checkTypesHaveRec` +
`checkBlock` + `checkShapes` + `checkMore` + `checkIotaAuto` per rule) on **48** type
formers including 8 hand-built adversarial ones, `checkNested` on 9 nested blocks (asserting
they are *rejected*), plus ~20 explicit negative controls (wrong telescope split, wrong
field count, missing `Nat.zero` rule, `Prop` elimination level, minor headed by its own
binder, `nrec` off by one either way, a hand-built non-positive constructor, and the
`TwoCtorProp` block that asks for large elimination it must not get).

### Attribution caveat (important for the blueprint)

The precomputed blame files under `…/scratchpad/blame/` tag by *which branch's commit git
blame names*. Two ι commits were landed **twice** — once on `iota`, once on `trproj` — and
the merge `20ec229` kept the `trproj` side:

* `7a68882` (iota) ≡ `6fd8a1d` (trproj) — "refine recursor reduction by the registered ι
  rules": `Verify/TypeChecker/WHNF.lean` (141 lines), `Inductive/Reduce.lean` (21 lines),
  `Verify/Expr.lean` (14), and 20 lines of `Verify/Environment/Lemmas.lean`. These are
  tagged **P** in the blame files but are **ι content**.
* `3de1dcb` (iota) ≡ `b4aba6d` (trproj) — the `toParams` demo
  (`addRecRule_defeqs`/`addRules_defeqs`/`addInduct_defeqs`,
  `DefEqsAsPats.of_no_defeqs`, `inductParams`, `crDefEq_of_induct`). Also tagged **P**.
* Conversely a few `I`-tagged declarations in `Verify/Environment/Lemmas.lean`
  (`TrConstant.sf_mono`, `.mono`, `TrConstVal.mono`) are **master code that was merely
  relocated**.

`git diff master..iota` is the reliable boundary; the blame tags are a good but not exact
proxy.

---

## (b) Commit narrative

28 commits, 2026-07-21 → 2026-09-09, all authored by Alessandro Sosso. Linear, with two
upstream merges. Milestones:

**M1 — First cut of the registry (2026-07-21, 8 commits, `cb920e1`…`3c78d08`).**
`cb920e1` relocated `Pattern.lean` from `Theory/Typing/` to `Theory/` (and, incidentally,
committed `.claude/settings.json` and `.mcp.json` — agent tooling); `5a4bdda` added the
`pats` field; `a3d6076` the `IsDefEq.pat` rule and the break-fixes it forces across
`Lemmas`/`Strong`/`ChurchRosser`; `41f3fb6` a real `VEnv.addInduct` with `VRecursor`/
`VRecRule`; `e92f762` the extension lemmas and a first `Params` instance; `d0a1ae7`/`9e186e6`
the `Verify` bridge and `TrEnv.pats_iota`; `3c78d08` discharged three `Params`
side-conditions via the `PatsIota` population invariant. At this point `VInductDecl.WF` was
deliberately underspecified ("records the *checkable* conditions … positivity, the universe
constraints and large-elimination conditions are **not yet enforced**",
`PR_DESCRIPTION_formal.md`), `AddInduct` hard-coded `.safe`, and there were **12
`IOTA-TODO(soundness)` sorries**.

**M2 — Toolchain port + first revert (2026-08-06, `e68db08`, `dc01931`, `3bbdb22`).**
Merged upstream master (v4.33.0-rc2, the front-end declaration-checking work) and ported.
`3bbdb22` **reverts** `cb920e1`'s file move (`Pattern.lean` back to `Theory/Typing/`) and
removes the committed agent-tooling files — a self-correction to minimise the diff against
upstream. This commit carries a **different committer identity** (`alesosso@gmail.com` vs
`sosso@cs.au.dk`); it is the only one that does.

**M3 — Consumer-driven strengthening (2026-08-08 … 2026-08-18, `349da4b`, `1a1ebe8`,
`eddf009`).** `349da4b` trims the comments to house style (−279/+123 lines of prose).
`1a1ebe8` is the interesting one: after wiring the interface into a client of the theory
end-to-end, the author found the two exposed lemmas **did not compose** — the
opaque `∃ r` in `pats_iota` could not be instantiated at the trivial check, and nothing
related the registered model reduct to the kernel `RecursorRule.rhs`. Fix: pin the full
telescope split and a `TrExprS` link inside `AddInduct.rec_find`, expose the witness
(`pats_iota'`), and add `TrEnv.iota_rec`. `eddf009` repairs `Experimental` (adding sorried
`pat` cases — the labelling of these as "pre-existing" was later corrected, see M5/F15).

**M4 — First "principled rework" (2026-09-04, `d69ac5d`, +3715/−682).** Big consolidation:
`AddInduct` becomes a data-carrying structure whose bookkeeping is *derived* rather than
assumed (the title: "derive AddInduct's ι bookkeeping instead of assuming it"), the `.safe`
gate on `TrEnv'.induct` is dropped, `VInductDecl.WF` is fleshed out, the new
`Verify/Environment/Quot.lean` supplies the now-necessary real `addQuot.WF`, and
`Tests/IotaShape.lean` appears. `655dd3f` pins the ι reduct's recursive-argument count
(`RuleShape`'s `nrec`), cherry-picked from the `trproj` line (`75ffde9`).

**M5 — Second, deeper rework after an adversarial review (2026-09-08/09, 10 commits,
`83fc0af`…`38ea0de`).** `REVIEW_2026-09-07.md` (an 8-reviewer + 2-verifier adversarial pass
with mechanised counterexamples in `review-artifacts/`) found two blockers on the ι side:
* **B1**: `VInductDecl.WF` was a syntactic checklist that admitted *inconsistent*
  environments — mechanised as `review-artifacts/counterexamples/cexB.lean`: a `Prop` with
  two nullary constructors and a `Sort u` recursor satisfied all 14 fields, from which
  `(∀p:Prop, p→p) ≡ (∀p:Prop, p)` followed in a `VEnv.WF` environment, sorry-free.
* **B2**: `VEnv.WF.patsStrong` was not provable by the route its docstring claimed and
  plausibly false — `cexA.lean`: `WF` admitted a "recursor" over an *older* type former
  whose rule fired on an *axiom*.

The response is the substance of `4016efa` ("specify inductive blocks by positivity and
elimination": `CtorPositive`, `CtorResult`, `MajorApp`, `universes` with the `imax u ℓ ≤ ℓ`
bound and `LargeElim` mirroring the kernel's `isLargeEliminator`, `recs_over_block`,
`rec_counts`, `rules_ctor` pinning every rule to a constructor of the eliminated former) and
`f53b727` ("state ι subject reduction over well-formed prefixes": `WFPrefix`, `PatsStrong`
restated, `OrderedStrong` as a three-field structure, `WF.strong` by `WF'` induction instead
of `Ordered.induction`). Then hygiene: `18805a4` deletes the `recSplit?` decoder section and
moves decidability into the tests; `3046dff`/`4307de3` dedupe helpers and kill a 17-branch
`first` macro; `30897c0` makes `checkEqType` reject an unsafe `Eq` (replacing a caller-side
`EqSafe` obligation) and records the divergence; `be30d35` closes the four `Experimental`
`pat` cases properly (`Typing.pat_env`, `IsDefEq1.pat`); `a928c53` rewrites the status-memo
docstrings to house style; `7a68882` lands the first internal consumer
(`inductiveReduceRecCore.WF`); `3de1dcb`/`38ea0de` are doc commits.

**Sidecar branch `iota-consume`** (`ab13fac` on top of the old `349da4b`): **not** an
ancestor of `iota` or `trproj`. It is a client's own proposal — the same
three strengthenings (`rec_find` split + `TrExprS` link, `pats_iota'` with the witness
named, an `of_value` de-taint) written from the consumer side and handed back for review
(`iota-consume-review-brief.md`). Its first two edits were re-implemented on `iota` as
`1a1ebe8`; the third (`of_value` → `constMap_wf`) was dropped, the brief itself noting the
consumer "ultimately routed δ through its own `SEnvConsistent`". Treat `iota-consume` as a
dead review artefact.

Churn summary: 2 reverts/relocations (`cb920e1`/`3bbdb22`), 2 upstream merges, 2 full
reworks of the central definition (`d69ac5d`, `4016efa`), 1 statement rework of the deferred
obligation (`f53b727`), 4 doc-only commits, 1 duplicated commit pair with `trproj`.

---

## (c) Claims made in the notes

Sources: `IOTA_CONTRIBUTION.md` (**pre-rework, stale**), `PR_DESCRIPTION_formal.md`
(**oldest, 12-sorry era, stale**), `PR_DESCRIPTION.md` (current-ish prose PR),
`PR_iota.md` (current formal PR), `PR_FOLLOWUP.md`, `iota-consume-review-brief.md`,
`REVIEW_2026-09-07.md` §9 (resolution table). Status is from cheap greps only; nothing was
compiled.

| # | Claim | Source | Status | How to verify |
|---|---|---|---|---|
| 1 | master's `VInductDecl.WF` and `VEnv.addInduct` sorries are closed | PR_iota | **checked-true** | `git show master:Lean4Lean/Theory/Inductive.lean` vs `Theory/Inductive.lean:316,335` |
| 2 | `addInduct_WF` is proved | PR_iota | **checked-true** | `Theory/Typing/InductiveLemmas.lean:229`; `git grep -n sorry` in that file = none |
| 3 | The branch leaves exactly one `sorry` of its own, `VEnv.WF.patsStrong` | PR_iota, PR_DESCRIPTION | **checked-true** | `git grep -n -w sorry iota -- 'Lean4Lean/**.lean' | grep -v Experimental` → only `EnvLemmas.lean:334` is new |
| 4 | Sorry census non-`Experimental`: master 23 → iota 21 | PR_iota | **checked-true** | same grep, excluding 5 doc/comment hits on master and 3 on iota |
| 5 | No new `axiom`s | PR_iota, PR_DESCRIPTION_formal | **checked-true** | `git grep -n '^axiom' -- 'Lean4Lean/**.lean'` → only `Experimental/` |
| 6 | No `native_decide` | REVIEW §"Established facts" | **checked-true** | `git grep -n native_decide` → none |
| 7 | `lake build` green on all four targets incl. `Tests` and `Experimental` | PR_iota, REVIEW §9 | **unverified** | forbidden here; re-run `lake build Lean4Lean.Theory Lean4Lean.Verify Lean4Lean.Tests Lean4Lean.Experimental` |
| 8 | `Experimental` sorry counts equal master's (the four `pat` cases closed) | REVIEW §9 (F15) | **checked-true** | per-file counts identical, 103 = 103; `Typing.pat_env`/`IsDefEq1.pat` present at `Experimental/NormalEq.lean:97`, `Stratified.lean:71`, `StratifiedUntyped.lean:51`, `ParallelReduction.lean:857,909` |
| 9 | `TrEnv.iota_defeq` is axiom-clean (`[propext]`) | PR_DESCRIPTION, IOTA_CONTRIBUTION | **unverified** | `#print axioms Lean4Lean.TrEnv.iota_defeq`; it is a one-line `⟨A, IsDefEq.pat …⟩` at `Verify/Environment/Lemmas.lean:917`, so plausible. No `#guard_msgs` in the repo for it |
| 10 | `pats_iota'`/`iota_rec` carry `sorryAx` **only** via the pre-existing `TrProj` placeholder | PR_DESCRIPTION, PR_FOLLOWUP | **unverified, structurally plausible on `iota`** | on `iota`, `TrProj := sorry` (`git show iota:Lean4Lean/Verify/Typing/Expr.lean:68`) and `TrExprS.proj` uses it (`:104`), so every `TrEnv'`-hypothesised lemma inherits it; on `trproj` `TrProj` is defined, so the footprint differs. Check with `#print axioms` on a built `iota` worktree |
| 11 | `TrEnv'.induct` applies at **every** safety level | PR_iota, PR_DESCRIPTION | **checked-true** | `Verify/Environment/Basic.lean:582` — no `safety = .safe` premise |
| 12 | `TrEnv'.induct` is guarded to `safety = .safe`; unsafe inductives future work | IOTA_CONTRIBUTION, PR_DESCRIPTION_formal | **checked-false (stale)** | contradicted by #11 |
| 13 | "12 deferred proofs, tagged `IOTA-TODO(soundness)`" | IOTA_CONTRIBUTION, PR_DESCRIPTION_formal | **checked-false (stale)** | `git grep -n 'IOTA-TODO'` → zero hits |
| 14 | `VInductDecl.WF` records only the *checkable* conditions; positivity / universe bound / large elimination "not yet enforced" | PR_DESCRIPTION_formal | **checked-false (stale)** | `ctors_positive`, `universes`, `recs_elim` are fields at `Theory/Inductive.lean:372`, `:350`, `:359` |
| 15 | `pat_uniq`, `pat_app_uniq`, `extra_pat` are *false* against the current `WF` | IOTA_CONTRIBUTION | **checked-false for the first two (stale)**; true-in-spirit for `extra_pat` | `WF.pat_uniq` `InductiveParams.lean:260` and `WF.pat_app_uniq` `:334` are proved; `extra_pat` is not proved but *assumed* as `DefEqsAsPats` (`:378`) |
| 16 | `Aligned.addInduct` is deferred (`sorry`) | IOTA_CONTRIBUTION, PR_DESCRIPTION_formal | **checked-false (stale)** | proved at `Verify/Environment/Lemmas.lean:102` |
| 17 | "The client interface inherits **no new soundness gap**" | IOTA_CONTRIBUTION | **checked-false / misleading** | `iota-consume-review-brief.md` itself corrects this for the old state; today every strong-system consumer routes through the sorried `patsStrong` via `instance : CoeOut (VEnv.WF env) env.OrderedStrong` (`EnvLemmas.lean:343`) |
| 18 | `iotaCheck = .true`: the kernel does no parameter check at ι-reduction time | PR_DESCRIPTION | **checked-true (code-level)** | `VEnv.addRecRule` registers `…, .true` (`Theory/Inductive.lean:257`); `inductiveReduceRecCore` (`Inductive/Reduce.lean:75`) compares only `getRecRuleFor` and argument counts |
| 19 | `SimplePattern.iotaRHS` mirrors `inductiveReduceRec`'s argument slicing **exactly**, validated by `rfl` on real `Nat.rec` and by a kernel sweep | PR_iota, PR_DESCRIPTION | **checked-true as to the test's existence; the assertions need a build** | `Tests/IotaShape.lean:141` `checkIota`, `:301` `checkIotaAuto`, driver at `:454`; the `rfl`-on-`Nat.rec` phrasing is now generalised into `checkIota ``Nat.rec ``Nat.succ` |
| 20 | `VInductDecl.WF` specifies a **direct** block; nested inductives are outside it; `Tree` is the documented negative control | PR_iota, PR_DESCRIPTION | **checked-true** | `recs_over_block` `:375`, `rules_ctor` `:390`; `checkNested`/`checkBlockRejected` at `Tests/IotaShape.lean:325`/`:295`, run on 9 nested blocks at `:605` |
| 21 | `AddInduct` carries only kernel data + stage witnesses; `env_eq`/`wf`/`find?_mono`/`rec_find`/`rec_reg`/`ctor_find`/`value_find` are theorems | PR_iota, PR_DESCRIPTION | **checked-true** | `Verify/Environment/Basic.lean:272`–`:521` |
| 22 | `checkEqType` rejects an unsafe `Eq`; `Environment.EqSafe` and the `addQuot.WF`/`addDecl.WF` preconditions are gone; recorded in `divergences.md` | PR_iota, REVIEW §9 (F06) | **checked-true** | `Lean4Lean/Quot.lean:24`; `git grep -n EqSafe` → none; `divergences.md` bullet 3; `addQuot.WF` unconditional at `Verify/Environment/Quot.lean:500` |
| 23 | `Verify/Environment/Quot.lean` replaces a proof that was **vacuous** through `no_inductInfo` with a real one | PR_iota | **checked-true** | master: `Verify/Environment.lean:139` `False.elim h`; now a 615-line sorry-free file |
| 24 | "The first internal consumer landed: `inductiveReduceRecCore.WF` (ι path of recursor reduction) via `iota_rec`" | REVIEW §9 (F09) | **checked-true but hollow** | `Verify/TypeChecker/WHNF.lean:17`, calling `c.trenv.iota_rec` at `:119`. **However** `reduceRecursor.WF` is still `sorry` (`WHNF.lean:147`) and nothing references `inductiveReduceRecCore.WF` — `grep -rn inductiveReduceRecCore Lean4Lean` shows no consumer |
| 25 | `toParams` is "exercised by `inductParams` + `crDefEq_of_induct`" | REVIEW §9 (F23) | **checked-true but unconsumed** | `InductiveParams.lean:419`/`:426`; `grep -rn 'toParams\|inductParams\|crDefEq_of_induct' Lean4Lean` → **all 14 hits are inside `InductiveParams.lean`**; the whole 433-line file has no consumer in the library |
| 26 | `PatsStrong` restated over well-formed prefixes (F05 fixed) | PR_iota, REVIEW §9 | **checked-true** | `Theory/Typing/Env.lean:57` (`WFPrefix`), `EnvLemmas.lean:130`; note it still also quantifies over constant-only extensions with equal `defeqs`/`pats` |
| 27 | Master's substitution family and the primitives layer now take `OrderedStrong`; "every one of those call sites held `VEnv.WF`" | PR_iota, PR_DESCRIPTION | **checked-true** | 67 `OrderedStrong` occurrences across `Theory/Typing/Strong.lean`, `EnvLemmas.lean`, `Verify/Primitive.lean`, `Verify/Environment/Primitive/{Basic,Condition}.lean`, `Verify/Typing/{Lemmas,TrTerm}.lean`; `IsDefEq.substDF` at `Strong.lean:1282` |
| 28 | "Nothing that was previously `sorry`-free at a bare `Ordered` hypothesis loses that" | PR_iota | **checked-false as stated / misleading** | master's `Ordered.strong` (`git show master:Lean4Lean/Theory/Typing/Strong.lean:675`, a `sorry`-free theorem deriving `OnTypes env (EnvStrong env)` from `Ordered` alone) **no longer exists**; `grep -rn 'Ordered.strong' Lean4Lean` → none. Its conclusion is now a *field* of `OrderedStrong`, obtainable only via the sorried `WF.patsStrong` |
| 29 | The review's `cexB` and `cexA` are "now refuted sorry-free" | REVIEW §9 | **unverified** | the in-repo evidence stops one step short: `Tests/IotaShape.lean:446,450` prove `declB_wants_large` and `¬ declB.LargeElimShape`, **not** `¬ declB.WF ∅`; `checkBlockRejected` covers nested blocks only. Re-run `review-artifacts/counterexamples/cexB.lean`/`cexA.lean` with `lake env lean` against the reworked `WF` |
| 30 | No mention of any client project anywhere in code or docstrings | REVIEW | **checked-true** | a grep for client-project terminology over `Lean4Lean --include='*.lean'` → no hits; the few hits for generic words like "consumer" are master's own prose |
| 31 | Line-length and style conformance (≤100 columns) | REVIEW §9 (d114c2d) | **checked-true** | `awk 'length>100'` over the ι files → 2 lines total (master's tree has 49) |
| 32 | `rec_find`'s `TrExprS` link "strengthens an assumption, creating no proof obligation today" | `iota-consume-review-brief.md`, `1a1ebe8` | **checked-true** | nothing constructs an `AddInduct`: `Verify/Environment.lean:208` `| inductDecl _ _ _ _ => sorry` is the only would-be site |
| 33 | A client of the theory pins this fork and consumes the interface | the round-4 commission brief | **checked-true as a statement about the note** | the note says the client pins `20ec229`; not verifiable from this repo |

---

## (d) Known limitations, open ends, divergences

**The one deferred proof.** `Lean4Lean.VEnv.WF.patsStrong` (`Theory/Typing/EnvLemmas.lean:334`).
Its docstring is now honest: not a consequence of `Ordered` (whose `defeq` step admits
arbitrary well-typed axioms — the counterexample `List Nat ≡ List Bool` is given inline), and
open because it needs inversion of the redex's typing plus **injectivity of type formers**,
which is itself `sorry` on master (`Theory/Typing/Injectivity.lean:12,21,34`). Its blast
radius is the whole strong system: `instance : CoeOut (VEnv.WF env) env.OrderedStrong`
(`:343`) routes it into `IsDefEq.strong`, `CtxStrong.strong`, `IsDefEqStrong.substEq'`,
`IsDefEq.substDF`, `HasType.subst`, and thence master's entire primitives development.
The review (B2) judged falsity "plausible but not mechanised" against the *pre-rework* `WF`;
the rework's `rules_ctor` kills the specific counterexample, but no proof sketch is claimed.

**Not modelled, stated in-file.**
* *K-like reduction*: `addRecRule` installs only §2.6.4's constructor rule; the recorded
  `VRecursor.k` flag is unused by the theory (`Theory/VDecl.lean:35` docstring,
  `Theory/Inductive.lean:257`). The corresponding checker refinement `toCtorWhenK` is
  untouched and unproved.
* *Structure η*: absent from `IsDefEq`; `tryEtaStructCore.WF` stays `sorry`
  (`Verify/TypeChecker/IsDefEq.lean:227`), as on master.
* *Nested inductives*: outside `VInductDecl.WF` by construction (`recs_over_block` +
  `rules_ctor`). The kernel's `ElimNestedInductive` compilation is not modelled. Note the
  resulting **dead generality**: `VRecRule.ctorParams` exists precisely so an auxiliary
  recursor of a nested block can fire on a foreign constructor, yet `WF.rules_own_params`
  (`Theory/Inductive.lean:440`) proves `ctorParams = numParams` under `WF` — the field is
  needed only on the `Verify` side (`TrRecursor.rules` reads `cval.numParams` from `m₂`).
* *The kernel's `whnf` at each binder*: `CtorPositive` and the `universes` clause read the
  **manifest** Π-binders, where the kernel reduces the field type first
  (`Theory/Inductive.lean:93` docstring, and the `VInductDecl.WF` docstring's "Not modelled"
  paragraph). The review's `review-artifacts/probes/ctor_*.lean` argue `CtorShape` cannot be
  out-run by `whnf`; the analogous argument for `FieldPositive` is not made in-repo.
* *`addInduct`'s staging* re-groups the kernel's per-recursor interleaving into four global
  stages; documented as yielding the same environment, not the same order
  (`Theory/Inductive.lean:270`-ish `/-! ### The stages of addInduct` block).

**Divergences from Lean 4's real kernel.**
* `Lean4Lean.checkEqType` now rejects an `unsafe` `Eq` where `quot.cpp`'s `check_eq_type`
  does not — new entry in `divergences.md` (the only tracked-file change outside
  `Lean4Lean/`). Defensible and in the spirit of the existing prelude-check divergences,
  but it *is* a behavioural divergence introduced to make a proof go through.
* `VInductDecl.LargeElim` states a field's propositionality as a typing judgment
  (`env.HasType … F (.sort .zero)`) where the kernel tests `sortLevel!.isAlwaysZero`
  syntactically (`Lean4Lean/Inductive/Add.lean:268`). The model is therefore **more
  permissive** than the kernel here. That direction is the right one for a refinement
  (kernel-accepted ⊆ model-accepted) and is semantically the sound condition, but it means
  `VInductDecl.WF` is not a transcription of the kernel's check and the refinement
  obligation is correspondingly non-trivial.
* `VInductDecl.WF.rules_wf` is explicitly *not* a kernel check ("No kernel check performs
  it: it is the model's admissibility condition for registering the rule",
  `Theory/Inductive.lean:421`). It is the clause that `addDecl.WF`'s inductive case would
  have to discharge from kernel data; that case is still `sorry`
  (`Verify/Environment.lean:208`), so **nothing in lean4lean ever constructs an `AddInduct`
  and nothing ever establishes `VInductDecl.WF` for a real declaration**. The entire
  `Verify`-side ι interface is today usable only by a caller that *assumes* `TrEnv`.

**Divergences from the thesis.** Recursor types and ι rules are carried as data and
shape-checked, where §2.6.3–2.6.4 generates them. Consequences: `rec_counts`/`rec_shape`/
`rule_shape` are 20 hand-written syntactic pins rather than an equality with a generated
telescope; `MotiveShape` cannot pin *which* constant a non-eliminated motive ends in
(`Theory/Inductive.lean:115` docstring admits this — "the heads of the other motives of a
mutual recursor are unconstrained"); and `RuleShape` pins only the *number* of recursive
arguments, not that they are the thesis's recursive calls `rec … (u_i x)`
(`Theory/Inductive.lean:165` docstring says so explicitly: "The terms `v` are not pinned,
syntactically or through typing").

**Open `Params` residue.** `extra_pat` is not discharged; `toParams` takes `DefEqsAsPats`
as a hypothesis, which fails as soon as a `def` or a `quot` is declared
(`InductiveParams.lean:350`–`:377` explains why: registering δ rules as `SimplePattern.defn`
would need a `VEnv` to distinguish definition / constructor / recursor names, which it does
not record; and the quotient redex is not a `SimplePattern` at all). So the `Params`
instance exists only for environments built from axioms and inductives.

**Grep recipes used**: `git grep -n -w sorry -- 'Lean4Lean/**.lean'`,
`git grep -n 'IOTA-TODO\|PROJ-TODO'`, `grep -rn 'TODO' Lean4Lean`,
`grep -rn '<name>' Lean4Lean --include='*.lean'` for reference counts.

---

## (e) Preliminary quality assessment

**Design soundness — good, with one unresolved architectural bet.**
Modelling ι as a pattern-rule registry is the right call and is *Mario's own* design
promoted from prototype: `SimplePattern.iota` and `Params.Pat`/`pat_wf` were already on
master; the branch makes them live and adds exactly one field to the class (`pat_env`), in
the one place `church_rosser`'s new case needs it (it closes through master's existing
`ParRed.extra`, `ChurchRosser.lean:1393`). The `Realizes`-as-data encoding of the side
conditions, with `toOK`/`exists_realizer` proving it equivalent to master's `Check.OK`, is a
clean solution to a genuine strict-positivity obstruction. The four-stage `addInduct` mirrors
the environments the kernel checks each constant in, which is what lets `VInductDecl.WF`
be stated stage-by-stage. `Ordered.pat` and `Aligned.pat`/`.block` mirror the existing
`defeq`/`const` clauses case for case.

The unresolved bet is carrying recursor data instead of generating it (see (d)). It makes
`VInductDecl.WF` a 20-field checklist whose adequacy — that these pins imply the thesis's
admissibility — is exactly what `patsStrong` would need and is not argued. The 2026-09-07
review's own recommendation ("compute recursor types and rule templates from `types`/`ctors`
as the thesis and `Inductive/Add.lean` do and define `WF` as agreement with the computed
data") was **not** taken; the rework instead added the missing conditions to the checklist.
A maintainer may well re-raise it.

**Proof hygiene — good.** One `sorry` of its own, honestly located and honestly documented,
three of master's closed, zero new axioms, zero `native_decide`, `Experimental` restored to
master's sorry count. The `IOTA-TODO` tag convention (flagged as non-idiomatic by the
review) is gone. Proofs are real proofs: `addInduct_WF`, `addInduct_pat`, `Aligned.addInduct`,
the five `Params` side conditions, `pats_iota'`, `iota_rec`, the 615-line `addQuot.WF` and
the ~130-line `inductiveReduceRecCore.WF` are all discharged. Style is compliant (2 lines
over 100 columns across all ι files, against 49 in master's tree).

The one hygiene concern is **what the branch does to master's theorems**: deleting
`Ordered.strong` and retyping ~25 public signatures and ~115 call sites from `Ordered` to
`OrderedStrong` turns a previously unconditional development (master's substitution family
and the whole `Verify/Environment/Primitive/*` layer, ~7 000 lines) into one conditional on a
`sorry`. `PR_iota.md` discloses this in a dedicated paragraph — good practice — but its
summary sentence ("Nothing that was previously `sorry`-free at a bare `Ordered` hypothesis
loses that") is at best a lawyer's reading (claim #28). This is the item most likely to
decide the PR.

**Documentation — much improved, now occasionally over-full.** After `a928c53` the
status-memo register is gone, the thesis citations are per-field and specific, and the
"Not modelled" boundaries are stated where the definitions are. `VInductDecl.WF` now has a
15-line header plus one docstring per field — verbose by master's standard but genuinely
informative. Residual risks: the docstrings are the *only* place several
non-obvious design facts live (e.g. that `rules_wf` is not a kernel check), and the three
untracked PR/contribution notes in the repo root are mutually contradictory —
`IOTA_CONTRIBUTION.md` and `PR_DESCRIPTION_formal.md` describe a state two reworks old and
would be actively misleading if pasted into a PR (claims #12–#17).

**Churn — visible but not alarming.** 28 commits with one revert pair, two upstream merges,
two reworks of the central definition, and one commit under a second committer identity;
`cb920e1` briefly committed agent tooling (`.claude/`, `.mcp.json`), reverted in `3bbdb22`.
The repo squash-merges every PR, so branch history does not reach upstream. Two commits are
duplicated between `iota` and `trproj` (`7a68882`/`6fd8a1d`, `3de1dcb`/`b4aba6d`), which
will confuse anyone reading the merged history.

**Dead / unconsumed code — the biggest remaining soft spot.**
* `Theory/Typing/InductiveParams.lean` (433 lines: `PatsIota`, five `Params` side
  conditions, `DefEqsAsPats`, `toParams`, `inductParams`, `crDefEq_of_induct`) has **zero
  references outside itself**. It is a demonstration that the instance can exist, for a
  class of environments (axioms + inductives, no `def`, no `quot`) that no real Lean
  environment belongs to.
* `inductiveReduceRecCore.WF` — presented as "the first internal consumer" — is itself
  consumed by nothing; `reduceRecursor.WF` is still `sorry` two lines below it
  (`WHNF.lean:147`). The chain redex → ι rule → checker therefore still does not close.
* `pats_iota_inv_shape` and `ctor_arity` are consumed only by the **projection** branch's
  `proj_defeq`, not by anything ι.
* Net: of the exported ι interface, exactly one lemma (`iota_rec`) has an in-repo consumer,
  and that consumer has none.

**Likely upstream reception.** The ι architecture, the `Pattern` extensions, the four-stage
`addInduct`, the `AddInduct` rework, the real `addQuot.WF` and `Tests/IotaShape.lean` are
the kind of thing a maintainer takes. Against acceptance, in descending order: (1) the
`Ordered` → `OrderedStrong` retyping makes master's own development conditional on an open
and possibly-false statement; (2) `VInductDecl.WF` is a checklist where the thesis (and
`Inductive/Add.lean`) generate, and its adequacy is unargued; (3) the diff is ~5.6 k lines
touching 45 files including 8 of master's own modules, with no in-repo consumer proving the
interface pulls its weight; (4) four open maintainer questions are put *in the PR text*
rather than resolved (`AddInduct` in `Type` vs `Prop`; the unsafe-`Eq` divergence; δ-as-pats;
whether `toParams` should ship at all). Realistic outcome: accepted in architecture after a
round of negotiation on (1) and (2), not merged as-is.

**For the blueprint**: the honest one-line summary is *"ι-reduction is now specified, its
rules are registered and fire, and the block specification is thesis-shaped; what is not yet
established is that the rules preserve types (`patsStrong`) or that any real kernel
declaration satisfies the specification (`addDecl.WF`'s inductive case)."*
