# Upstream comparison: `digama0/lean4lean` vs the fork's `iota` / `trproj`

Network was available. Everything below was fetched live on **2026-09-14** via `curl` against
`api.github.com`, `raw.githubusercontent.com` and `codeload.github.com` (WebFetch was used once as
a cross-check and agreed). Exact URLs are listed in §6.

Fork state assumed: `master` = `8223d223ed98661882e95d9d6a7126df7097cd76`, `iota` = `38ea0de4`
(28 commits ahead of master), `trproj` = `20ec229f` (52 ahead of master, 24 ahead of `iota`;
`git merge-base --is-ancestor iota trproj` → yes).

---

## 1. Has upstream moved past `8223d22`?

**No. The fork's `master` is byte-identical to upstream `master`, and upstream has not pushed
anything since 2026-08-29 — 16 days of silence.**

| fact | value |
|---|---|
| `GET /repos/digama0/lean4lean/branches/master` → `commit.sha` | `8223d223ed98661882e95d9d6a7126df7097cd76` |
| fork `git rev-parse master` | `8223d223ed98661882e95d9d6a7126df7097cd76` |
| upstream repo `pushed_at` (any branch) | `2026-08-29T18:50:24Z` |
| upstream `open_issues_count` / `forks_count` | 22 / 36 |

Identical SHA ⇒ identical tree, so there are **zero commits since `8223d22`** and nothing to
diff. I confirmed this independently rather than relying on the SHA: I fetched all eleven files
named in the task at the upstream SHA from `raw.githubusercontent.com` and byte-compared each
against `git show master:<path>`. All eleven came back `SAME`:

```
SAME Lean4Lean/Theory/Inductive.lean          SAME Lean4Lean/Theory/Typing/Pattern.lean
SAME Lean4Lean/Theory/VEnv.lean               SAME Lean4Lean/Theory/Typing/InductiveLemmas.lean
SAME Lean4Lean/Theory/Typing/Basic.lean       SAME Lean4Lean/Theory/Typing/ChurchRosser.lean
SAME Lean4Lean/Verify/Typing/Expr.lean        SAME Lean4Lean/Theory/Typing/Strong.lean
SAME Lean4Lean/Verify/Environment/Basic.lean  SAME Lean4Lean/Theory/VDecl.lean
SAME Lean4Lean/Verify/Environment/Lemmas.lean
```

For context, the 11 most recent upstream commits (author dates; the 2026-08-28 batch was pushed
2026-08-29). All by Mario Carneiro. None touch inductives, ι, or projections:

| sha | date | summary |
|---|---|---|
| `8223d223` | 2026-08-29 | feat: close the substitution sorries with the picked substDF |
| `6ba54db4` | 2026-08-14 | Prove substDF: simultaneous substitution into (strong) defeq |
| `ac1498ae` | 2026-08-28 | feat: primitives, part 3: the clauses, and the inductive guard |
| `c195b643` | 2026-08-28 | feat: primitives, part 2: Basic, Condition, Recursion |
| `80d3dbef` | 2026-08-28 | fix: refactoring and fixing checkPrimitiveDef |
| `3468d5bf` | 2026-08-28 | feat: primitives, part 1: basic prep |
| `71128e26` | 2026-08-28 | refactor: the primitive invariant, as a table |
| `3adf6da6` | 2026-08-26 | docs: justify the projection divergence by the generated recursor |
| `7eca770c` | 2026-08-26 | fix: raise the `recDepth` bound to 50000 |
| `e0e3f6bc` | 2026-08-14 | feat(theory): coNP-hardness of level equivalence, via a reduction from SAT |
| `4b60e53d` | 2026-08-14 | fix: compute the K-target flag where the kernel does; document 3 divergences |

I also checked the **other ten upstream branches** (`cpp2026`, `cpp2025`, `logrel`,
`differential`, `arena`, `arena-v4.29.0`, `types2025`, `itp2024`, `v4.27.0-rc1`,
`bitvec_example`). Every one of them has the identical 6-line stub `Theory/Inductive.lean` with
2 `sorry`s, zero occurrences of `pats` in `Theory/VEnv.lean`, and `TrProj := sorry`. **No
upstream branch anywhere has this work.**

---

## 2. Has upstream independently implemented any of the four features?

I downloaded the full upstream tree (`codeload.github.com/.../tar.gz/8223d223…`, 112 `.lean`
files) and grepped it. Repo-wide hit counts:

| identifier | upstream hits |
|---|---|
| `VEnv.pats`, `\bpats\b`, `IsDefEq.pat`, `addPat` | **0, 0, 0, 0** |
| `addInduct` / `VInductDecl` / `AddInduct` | 14 / 5 / 13 — all stub-or-consumer sites (below) |
| `TrProj` | 19 — the `sorry` definition plus 6 `sorry` lemmas and their consumers |
| `addQuot` / `quotInit` | 26 / 18 — genuinely implemented |

### 2a. ι-reduction rules in the theory (`VEnv.pats`, `IsDefEq.pat`) — **absent upstream**

Upstream `Lean4Lean/Theory/VEnv.lean` is 44 lines. `VEnv` has exactly two fields:

```lean
@[ext] structure VEnv where
  constants : Name → Option VConstant
  defeqs : VDefEq → Prop
```

and `IsDefEq` (upstream `Theory/Typing/Basic.lean`, 76 lines) has exactly eleven constructors:
`bvar, symm, trans, sortDF, constDF, appDF, lamDF, forallEDF, defeqDF, beta, eta, proofIrrel,
extra`. There is no `pat`.

The one genuine overlap: upstream **already has the `Pattern` engine** and already anticipates
ι-shaped patterns. `Theory/Typing/Pattern.lean:226-232`:

```lean
inductive SimplePattern where
  | iota (recursor : Name) (major : Nat) (constr : Name) (args : Nat)
  | defn (head : Name)

def SimplePattern.toPattern : SimplePattern → Pattern
  | .defn c => .const c
  | .iota r m c n => .app (.varN (.const r) m) (.varN (.const c) n)
```

But upstream uses this **only inside the `Params` typeclass** of `Theory/Typing/ChurchRosser.lean`
(`pat_simple`, `pat_wf`) and in `Experimental/`. `Params` is an *assumed* interface — nothing
upstream constructs an instance of it from a real environment, and no `VEnv` carries the rules.
The fork's `iota` is precisely the step of turning that assumed interface into a live registry:
it adds the third `VEnv` field `pats`, `VEnv.addPat`, the `LE.pats` monotonicity component, the
`IsDefEq.pat` constructor, and `Theory/Typing/InductiveParams.lean` (423 lines, a file that
**does not exist upstream** — `raw.githubusercontent.com/.../InductiveParams.lean` → **404**)
which builds a `Params` instance from `env.pats`.

### 2b. Specification of inductive blocks (`VInductDecl.WF`, `addInduct`) — **absent upstream**

Upstream `Lean4Lean/Theory/Inductive.lean` is **the entire file**, seven lines:

```lean
import Lean4Lean.Theory.VDecl

namespace Lean4Lean

def VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop := sorry

def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv := sorry
```

`Theory/Typing/InductiveLemmas.lean` upstream is 10 lines: `addInduct_WF` stated, proof `sorry`.

On the Verify side, upstream `Verify/Environment/Basic.lean:101-113` is explicit that this is a
hole, in its own words:

```lean
/-- This definition is essentially a `sorry`: it should relate `addInductive`'s
effect on the constant map to `VEnv.addInduct` (which is itself a `sorry`,
see `Lean4Lean.Theory.Inductive`), but it currently has no constructors, so the
`TrEnv'.induct` case below can never fire and environments containing inductives
are outside the verified `TrEnv` relation. -/
inductive AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) : Prop
  -- TODO

nonrec theorem AddInduct.to_addInduct
    (H : AddInduct m₁ env₁ decl m₂ env₂) : env₁.addInduct decl = some env₂ :=
  nomatch H
```

`AddInduct` is an **empty inductive**; `to_addInduct` is proved by `nomatch`. Everything
that depends on `TrEnv'.induct` upstream is therefore vacuous.

### 2c. Projections (`TrProj`, `Expr.proj` in `Verify/`) — **absent upstream**

Upstream `Verify/Typing/Expr.lean:68` is a one-liner:

```lean
def TrProj : ∀ (Γ : List VExpr) (structName : Name) (idx : Nat) (e : VExpr), VExpr → Prop := sorry
```

i.e. `TrProj` is an *unspecified relation*, and `TrExprS.proj` is built on it. Six lemmas about
it in `Verify/Typing/Lemmas.lean` are `sorry` too: `TrProj.weak'` (642), `weak'_inv` (723),
`defeqDFC` (727), `wf` (893), `uniq` (938), `instN` (1240), `instL` (1509) — seven `sorry` lines.
Upstream did touch projections on 2026-08-26 (`3adf6da6` "docs: justify the projection divergence
by the generated recursor", `62441418` "perf: add lazyDeltaProjReduction"), but those are a
documentation note and a checker performance change, **not** a model of projection.

### 2d. Quotient initialization in `Verify/Environment` — **present upstream, but vacuous**

This is the one area where upstream has real machinery: `AddQuot1` / `AddQuot` /
`AddQuot.to_addQuot` / `AddQuot.le` in `Verify/Environment/Basic.lean:68-99`, `TrEnv'.quot`,
`VEnv.QuotReady`, `Theory/Quot.lean`, `Theory/Typing/QuotLemmas.lean`. But the top-level theorem
that consumes it is, again in upstream's own words (`Verify/Environment.lean`):

```lean
/-- This is currently vacuous in the non-initialized case: `TrEnv` cannot contain the
inductive `Eq` declaration until `AddInduct` is implemented. -/
theorem addQuot.WF … := by
  unfold Environment.addQuot
  split
  · exact .pure ⟨ves, wf, fun _ => VEnv.LE.rfl⟩
  · exact (checkEqType.WF wf).bind fun _ h => False.elim h
```

and `checkEqType.WF` upstream proves `fun _ => False` by appealing to `no_inductInfo` — the
environment provably contains no inductive `Eq`, because `AddInduct` is empty. The whole
non-initialized branch is discharged by `False.elim`.

The **fork's `iota` branch adds `Verify/Environment/Quot.lean` (615 new lines; does not exist
upstream)** which deletes both of those from `Verify/Environment.lean` (`+3/−30` there) and
re-proves `addQuot.WF` for real — building the four `Quot` constant telescopes (`L1`…`L6`,
`T1`…`T4`), their `LocalContext` well-formedness, and case-splitting on `env.quotInit` rather
than deriving `False`. This is a real strengthening of an upstream result that the PR description
barely advertises.

### 2e. The hole ledger

Comparing live non-`Experimental` `sorry`s (cross-checked against `sorry-grep.md`, which
classifies by `declRangeExt` + `sorryAx` taint, so prose mentions are excluded):

| upstream master hole | `iota` | `trproj` |
|---|---|---|
| `VInductDecl.WF := sorry` (`Theory/Inductive.lean:5`) | **closed** (441-line spec) | closed |
| `VEnv.addInduct := sorry` (`Theory/Inductive.lean:7`) | **closed** | closed |
| `addInduct_WF … sorry` (`InductiveLemmas.lean:10`) | **closed** (+777 lines) | closed |
| `AddInduct` = empty inductive (`Verify/Environment/Basic.lean`) | **closed** (real 15-field structure) | closed |
| `addQuot.WF` / `checkEqType.WF` vacuous | **closed** (new `Verify/Environment/Quot.lean`) | closed |
| `TrProj := sorry` (`Verify/Typing/Expr.lean:68`) | still `sorry` | **closed** (`TrProjCtor` + `TrProj`) |
| 7 `TrProj.*` `sorry` lemmas (`Verify/Typing/Lemmas.lean`) | still 7 | **5 of 7 closed**; `weak'_inv`, `uniq` remain |
| `addDecl.WF \| inductDecl => sorry` (`Verify/Environment.lean`) | **remains** | **remains** |
| `inferProj.WF` `sorry` (`InferType.lean:391`) | untouched | split into 2 `sorry`s (`WF_struct`, `WF`) |
| — new debt introduced — | `VEnv.WF.patsStrong` (`EnvLemmas.lean:334`) | same, + 3 in `Tests/ProjInhabit.lean` |

So the branches genuinely retire five upstream holes that upstream's own comments flag as the
blockers, at the cost of one new load-bearing admitted lemma (`patsStrong`) plus, on `trproj`,
four more. The single top-level boundary — `addDecl.WF`'s `inductDecl` case — is **not** closed,
which the author states plainly in his own PR comment ("`AddInduct` is still not constructed from
`Environment.addInductive` … so nothing discharges it yet").

### 2f. Interface changes the branches make to upstream code

Three signature changes upstream would have to accept, not just additions:

- `VEnv` gains a third field `pats`, so `VEnv.LE` gains a third component and every
  `⟨id, id⟩` / `⟨h2.1 ∘ h1.1, h2.2 ∘ h1.2⟩` becomes a triple. Cheap but repo-wide.
- `TrProj` changes arity: upstream `TrProj : List VExpr → Name → Nat → VExpr → VExpr → Prop`
  becomes `TrProj (env : VEnv) (U : Nat) (Γ …)`, so `TrExprS.proj` changes to
  `TrProj env Us.length Δ.toCtx s i e' e''`. This is a real API break on a definition upstream
  currently leaves opaque.
- `AddInduct` gains a leading `safety : DefinitionSafety` parameter.
- `Theory/VEnv.lean` now imports `Theory/Typing/Pattern.lean`, inverting part of the existing
  import order (`Pattern` sits under `Typing`, which conceptually sits above `VEnv`).

---

## 3. Upstream PRs and issues by the user or about inductives/projections

**The user already has an open upstream PR: `digama0/lean4lean#43, "Iota Reduction"`.**

| field | value |
|---|---|
| author / created / last updated | `barabbs` / 2026-08-08 / 2026-09-10 |
| state | **open**, not draft, `merged: false` |
| head → base | `barabbs:iota @ 38ea0de413` → `digama0:master @ 8223d223ed` |
| size | +5628 / −331 across 45 files, 28 commits |
| `mergeable` / `mergeable_state` | `true` / `unstable` |
| human review comments | **zero** |

Details that matter for judging reception:

- **All 7 inline review comments and the one review are from `copilot-pull-request-reviewer[bot]`,
  posted 2026-08-08T09:49, five minutes after opening.** They flag the `sorry` placeholders in
  `Strong.lean:275`, `Lemmas.lean:818/859/863`, `InductiveParams.lean:447`,
  `InductiveLemmas.lean:110`, `ChurchRosser.lean:1390` and a broken `insertDefs_wf` import — i.e.
  they review the *first* push, most of which the author has since moved past.
- **The only two human comments on the thread are the author's own** (2026-08-11 and 2026-08-18).
- The timeline shows `mentioned digama0` + `subscribed digama0` at **2026-08-10T07:55**. The
  maintainer has been subscribed for five weeks and has said nothing. He is not inactive: he
  commented on #26, #27, #20, #22, #33, #11 and #32 in the same window, his last being 2026-08-31.
- **CI has never been allowed to run on the fixed code.** Workflow runs on branch `iota`:
  `a01c9184` (08-08) `failure`, `349da4b6` (08-08) `failure`, `1a1ebe8b` (08-11) `failure`,
  then `eddf0090` (08-18), `a928c532` (09-08), `38ea0de4` (09-10) all **`action_required`** —
  GitHub's first-time-contributor approval gate, which no maintainer has clicked.
  `GET /commits/38ea0de4/check-runs` → `total_count: 0`; combined status → `pending`.
  So the last CI verdict upstream ever saw on this PR is **red, from 2026-08-11**, from the
  `Lean4Lean.Experimental` build break the author fixed on 08-18. That is what
  `mergeable_state: unstable` reflects.

Other upstream PRs/issues touching this territory:

- **#32** kim-em, "feat: verify primitive-model conservation through declaration checking",
  +24247/−1264 over 33 files, opened 2026-08-04, **closed unmerged 2026-08-31** as *superseded*
  by Mario's own `71128e2..8223d22` work. kim-em: *"the remaining inductive case is being handled
  separately."* This is the single most important calibration datum in this report — see §5.
- **#31** (issue, open) migrate `Verify` off the legacy `do` elaborator; **#24** (issue, open)
  Level cached-flag; **#27** (PR, open since 2026-08-02, kim-em); **#16** (issue, open)
  "Contributing proofs" by thomasahle; **#18** (issue, open) `NormLevel.subsumption_eval` false.
- **#44/#45/#46** vasnesterov, axiom audits, all opened and **closed the same day** (2026-08-23),
  unmerged, no comments.
- **#47** Kha, "Adaptations for Lean 4.35", open since 2026-09-09 — a toolchain bump that will
  touch many files and is the most likely near-term source of merge conflict.
- Nothing upstream mentions projections or `TrProj` as a PR or issue.

**Crucially, `digama0` wrote this on 2026-08-31 — three weeks after PR #43 opened, on a different
thread:**

> Still open, and unchanged by either: `addDecl.WF`'s `inductDecl` case, since `VInductDecl.WF`
> and `VEnv.addInduct` are still `sorry` in `Theory/Inductive.lean`. `checkInductive.WF` is
> stated to meet it — it delivers the declaration's shape as `AddsConsts` together with the fact
> that adding those constants preserves `HasPrimitives` — so what is missing is a constructive
> `AddInduct` whose added constants are exactly those.

The maintainer is describing **exactly** the deliverable of the `iota` branch, as still missing,
while that branch has been sitting in his PR queue. Two readings are possible and the evidence
does not settle between them: he has not looked at #43, or he has looked and does not count it as
meeting the spec. The second reading has teeth, because his sentence names an interface the fork
does **not** connect to: `git grep AddsConsts trproj` finds only the unmodified upstream
`Verify/Environment/Primitive.lean` — the fork's `AddInduct` is **not** wired to
`checkInductive.WF` / `AddsConsts`, which is precisely the handshake he says is needed.

---

## 4. PRs opened *from* `barabbs/lean4lean`

`GET /repos/barabbs/lean4lean/pulls?state=all` → **`[]`** (empty list). The fork has no PRs of
its own, `open_issues_count: 0`, `pushed_at: 2026-09-10T08:13:40Z`, parent `digama0/lean4lean`.

The user's only upstream proposal is #43, which carries **`iota` alone**. Cross-checking the PR's
45-file list against `git diff --name-status master trproj`:

- `trproj`-only files **not in any PR**: `Lean4Lean/Theory/Proj.lean` (449 lines),
  `Lean4Lean/Tests/ProjInhabit.lean` (597), `Lean4Lean/Tests/ProjShape.lean` (185), the
  `TrProj`/`TrProjCtor` definition in `Verify/Typing/Expr.lean` (+71), the `TrProj` lemma proofs
  in `Verify/Typing/Lemmas.lean` (+173 vs iota's +22), and ~455 extra lines in
  `Verify/Environment/Lemmas.lean`.

**The entire projection contribution — the larger and, by the hole ledger, the more
self-contained half — has never been shown to upstream.**

---

## 5. Assessment: what the upstream state does to the value of these branches

**Not superseded, not duplicated, and aimed at holes upstream itself documents as open.** This is
the strongest thing the evidence supports, and it is solid: upstream's `Theory/Inductive.lean` is
two `sorry`s, `AddInduct` is an empty inductive with a `-- TODO`, `TrProj` is `:= sorry`, and
`addQuot.WF` is vacuous *by its own docstring*. No upstream branch, and no other open PR, does any
of this. The work is not reinventing something that exists.

**They would merge cleanly today, in the textual sense.** GitHub reports `mergeable: true` for #43
against the current master, and since master has not moved since the branches were cut and
`iota` is an ancestor of `trproj`, `trproj` would merge textually too. That is a low bar and it
will decay: PR #47 (Lean 4.35 adaptation) is exactly the kind of change that rewrites many files.

**The risk is not conflict — it is supersession, and there is a direct precedent.** PR #32 is the
control experiment: a +24k-line verification contribution from a well-known contributor
(kim-em), on an adjacent subsystem, was **closed unmerged after four weeks** because the
maintainer had written his own version on master in the meantime. Mario's closing note is a
point-by-point argument that his version was better *because it was smaller and touched the
checker less* — "a line added there is a line that has to be believed rather than proved",
"+10,545/−627 over 30 [files]" versus "+24,247/−1,264 over 33". By that stated metric, `iota`
(+5628/−331 over 45) and `trproj` (+7762/−363 over 49) are in the size band he has already
criticized once, and they change three existing interfaces (`VEnv` arity, `TrProj` arity,
`AddInduct` arity) rather than sitting alongside. A maintainer with strong, documented design
opinions about this exact subsystem is the main threat to this work landing, not git.

**Three concrete, checkable gaps between what upstream asked for and what the branches deliver:**

1. `addDecl.WF`'s `inductDecl` case is still `sorry` on both branches. Until it is closed, the
   `AddInduct` structure is a well-specified *object* that nothing in the verified pipeline
   produces, so the end-to-end theorem is unchanged. The author says this himself.
2. The `AddInduct` ↔ `checkInductive.WF`/`AddsConsts` handshake the maintainer named on
   2026-08-31 is not made — `AddsConsts` appears nowhere in the fork's new code.
3. `VEnv.WF.patsStrong` is admitted and load-bearing for the new `IsDefEq.pat` rule. That is one
   admitted lemma standing where upstream previously had a definition-level `sorry`; whether that
   is a net improvement in trust depends on how strong `patsStrong` is, which is the census
   readers' question, not this one.

**Two process facts that probably explain the silence better than any judgment on the code.**
The PR's visible CI state is a red run from 2026-08-11, and every run since is stuck on
`action_required`. A maintainer skimming the queue sees a 5.6k-line PR from a first-time
contributor with failing CI and a bot review listing seven `sorry`s. Nothing about that presents
the work well, and all of it is fixable — asking for the CI approval, and re-stating the
2026-08-31 `AddsConsts` handshake as the thing the branch is aimed at, are cheap moves that have
not been made.

**On `trproj` specifically: its value is currently unmeasured, because nobody upstream has seen
it.** It is the half that closes the most upstream `sorry`s per line (`TrProj := sorry` plus 5 of
7 `TrProj` lemmas), and it has never been proposed. Whatever the verdict on `iota`, "we do not
know what upstream thinks of `trproj`" is a statement about the submission, not about the code.

---

## 6. Exact URLs fetched (all 2026-09-14, all HTTP 200 unless noted)

```
https://api.github.com/repos/digama0/lean4lean
https://api.github.com/repos/digama0/lean4lean/branches/master
https://api.github.com/repos/digama0/lean4lean/branches?per_page=100
https://api.github.com/repos/digama0/lean4lean/commits?per_page=50
https://api.github.com/repos/digama0/lean4lean/pulls?state=all&per_page=100
https://api.github.com/repos/digama0/lean4lean/issues?state=all&per_page=100
https://api.github.com/repos/digama0/lean4lean/issues/comments?sort=created&direction=desc&per_page=25
https://api.github.com/repos/digama0/lean4lean/pulls/43
https://api.github.com/repos/digama0/lean4lean/pulls/43/commits?per_page=100
https://api.github.com/repos/digama0/lean4lean/pulls/43/files?per_page=100
https://api.github.com/repos/digama0/lean4lean/pulls/43/comments?per_page=100
https://api.github.com/repos/digama0/lean4lean/pulls/43/reviews?per_page=100
https://api.github.com/repos/digama0/lean4lean/issues/43/comments?per_page=100
https://api.github.com/repos/digama0/lean4lean/issues/43/timeline?per_page=100
https://api.github.com/repos/digama0/lean4lean/pulls/{27,28,32,44,45,46}
https://api.github.com/repos/digama0/lean4lean/issues/{32,44,45,46}/comments?per_page=20
https://api.github.com/repos/digama0/lean4lean/commits/38ea0de4138bc7dbb5ee41c2e640fafd9ca0830a/check-runs
https://api.github.com/repos/digama0/lean4lean/commits/38ea0de4138bc7dbb5ee41c2e640fafd9ca0830a/status
https://api.github.com/repos/digama0/lean4lean/actions/workflows
https://api.github.com/repos/digama0/lean4lean/actions/runs?per_page=30
https://api.github.com/repos/digama0/lean4lean/actions/runs?branch=iota&per_page=20
https://api.github.com/repos/digama0/lean4lean/actions/runs?event=pull_request&per_page=25
https://api.github.com/repos/barabbs/lean4lean
https://api.github.com/repos/barabbs/lean4lean/pulls?state=all&per_page=50
https://codeload.github.com/digama0/lean4lean/tar.gz/8223d223ed98661882e95d9d6a7126df7097cd76
```

Raw files at `https://raw.githubusercontent.com/digama0/lean4lean/8223d223ed98661882e95d9d6a7126df7097cd76/<path>`
for `<path>` in: `Lean4Lean/Theory/Inductive.lean`, `Lean4Lean/Theory/VEnv.lean`,
`Lean4Lean/Theory/VDecl.lean`, `Lean4Lean/Theory/Typing/Basic.lean`,
`Lean4Lean/Theory/Typing/Pattern.lean`, `Lean4Lean/Theory/Typing/InductiveLemmas.lean`,
`Lean4Lean/Theory/Typing/ChurchRosser.lean`, `Lean4Lean/Theory/Typing/Strong.lean`,
`Lean4Lean/Verify/Typing/Expr.lean`, `Lean4Lean/Verify/Environment/Basic.lean`,
`Lean4Lean/Verify/Environment/Lemmas.lean` (all 200), and
`Lean4Lean/Theory/Typing/InductiveParams.lean` (**404** — fork-only file).

Per-branch probes at `https://raw.githubusercontent.com/digama0/lean4lean/<branch>/<path>` for
`<branch>` in `cpp2026, cpp2025, logrel, differential, arena, arena-v4.29.0, types2025, itp2024,
v4.27.0-rc1, bitvec_example` and `<path>` in `Lean4Lean/Theory/Inductive.lean`,
`Lean4Lean/Theory/VEnv.lean`, `Lean4Lean/Verify/Typing/Expr.lean`.

One WebFetch cross-check: `https://api.github.com/repos/digama0/lean4lean/commits?per_page=50`.
