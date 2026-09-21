# Group `verify-primitive-arith`

Files (all under the repository root):

| file | lines | M | I | P |
|---|---:|---:|---:|---:|
| `Lean4Lean/Verify/Environment/Primitive/Condition.lean` | 3117 | 3090 | 27 | 0 |
| `Lean4Lean/Verify/Environment/Primitive/DivMod.lean` | 547 | 534 | 13 | 0 |
| `Lean4Lean/Verify/Environment/Primitive/Gcd.lean` | 148 | 142 | 6 | 0 |
| `Lean4Lean/Verify/Environment/Primitive/Bitwise.lean` | 405 | 396 | 7 | 2 |
| `Lean4Lean/Verify/Environment/Primitive/Clauses.lean` | 438 | 424 | 14 | 0 |

67 iota lines, 2 trproj lines out of 4655. **This is Mario's code.** The contributed part is not new
mathematics: it is the fallout of one design decision taken on the `iota` branch, and the interesting
question for the review is whether that fallout was handled well.

## 1. What these files do

Lean's kernel does not evaluate `Nat.add` by unfolding its definition; it recognises certain declarations
by name and swaps in GMP arithmetic. That recognition is a *trusted* step, and `Lean4Lean/Primitive.lean`
re-implements it as a checker: for each recognised name, a branch that opens probe variables, runs
`isDefEq` checks against the equations the primitive is supposed to satisfy, and accepts only if they pass.
These five files are the soundness proof of that checker — one theorem per branch, each of the shape

```
theorem checkNatX.WF (wf : ves.WF env) (hname : v.name = ``Nat.X) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatX v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci'
```

i.e. *if the branch accepts, the declaration really reflects the arithmetic function the kernel will then
compute with*.

**`Condition.lean` (3117 lines)** is the shared vocabulary, and by far the most interesting file. Several
primitives (`Nat.div`, `Nat.mod`, `Nat.gcd`, `Nat.bitwise`) are defined with conditionals, so the checker
needs to know that some `ite`/`dite` in the definition really decides some predicate. A `Condition`
(`Lean4Lean/Primitive.lean:66`) packages a predicate with a decision procedure; `Condition.WF`
(`Condition.lean:150`) is its model-side reading, and `Condition.check.WF` (`Condition.lean:2765`) is the
boundary: if the check passes, the caller gets `WF_ite`/`WF_dite` (how to *build* a conditional's
translation) and `IteEval`/`DiteEval`/`DecT` (what a conditional is *worth* once the probes have been
closed off). The `Expr`-level/`VExpr`-level split between those two families is the file's central design
idea and is documented with its reason (`Condition.lean:283-297`): a caller that builds a conditional
still has an `Expr`, a caller that reached one by instantiating probe variables does not.

Underneath sits a reusable transport kit: `TrExprS.weakR` (485) adds binders on the right of a context,
`TrExprS.ofClosed` (540) removes them, and the `_nil_inv` family (664-707) identifies a closed piece read
at one binder depth with the same piece read at another. This is what lets three separate checks, run at
three different depths, be about the same `VExpr`. `noProj` (307) is the side condition that makes it
work — and note that its entire purpose is to *avoid* `Expr.proj`, precisely because a `TrProj` obligation
would then have to be transported too (485-487). That is a direct point of contact with the `trproj`
branch: the primitives layer currently excludes projections by construction.

**`Clauses.lean`** is fifteen short, individually documented theorems, one per simple clause
(`Nat.add`, `pred`, `sub`, `mul`, `pow`, `beq`, `ble`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`,
`Char.ofNat`, `String.ofList`). **`DivMod.lean`** factors `Nat.div` and `Nat.mod` through one theorem,
`checkNatFuelRec.WF` (22), about the fuel recursion they share. **`Gcd.lean`** is a single 136-line proof
for a well-founded recursion. **`Bitwise.lean`** is the hard case: `Nat.bitwise`'s operator is a free
variable of the recognizer's context, so `boolOp2_apply` (16) is needed to say what an unknown operator at
arguments that are merely *worth* boolean literals evaluates to, and the equation body is three nested
conditionals over two different `Condition`s.

## 2. Relation to the thesis

Essentially none, and that is expected. `lean-type-theory/axioms.tex` covers β, ζ, δ, ι, quotients,
propext and choice; there is no section on the kernel's GMP-accelerated `Nat`/`String` primitives at all
(`grep -ci nat axioms.tex` → 10 hits, none about literal arithmetic). These files verify a part of the
Lean 4 kernel that the thesis does not model. The only genuine correspondences are structural: the
transport lemmas instantiate Weakening (`typesys.tex \label{thm:weak}`) and Properties of substitution
(`typesys.tex \label{thm:subst}`) for the `Expr`↔`VExpr` translation relation, and `VEnv.IsDefEqU.natProj`
(881) / `Condition.check.gadget_types` (2116) are applications of the β rule
(`axioms.tex §Definitional equality`).

The one place where the thesis becomes load-bearing is the contributed change, below: it turns on
Regularity (`typesys.tex \label{thm:reg}`, "Regularity continued" at `typesys.tex:111`) and on subject
reduction for reductions (`unique.tex:121`, "Regularity of reductions").

## 3. The contributed change, precisely

**All 67 iota lines are one mechanical edit: `VEnv.Ordered` → `VEnv.OrderedStrong`.**

Six *statements* changed (all in `Condition.lean`), from `henv : env.Ordered` to `henv : env.OrderedStrong`:

- `TrExprS.boolProp` (421), `TrExprS.propBoolProp` (744), `TrExprS.boolNat3` (754),
  `TrExprS.natNatProp` (771), `TrExprS.divGoType` (786), `TrExprS.natProj` (855).

The remaining 61 lines are *proof-internal*: `c.Ewf.ordered` → `c.Ewf.orderedStrong`,
`E.wf.ordered` → `E.wf.orderedStrong`, at call sites of `VEnv.HasType.subst`, `VEnv.IsDefEqU.subst`,
`VExpr.WF.app_inv`, `VExpr.WF.lam_inv'`, `VEnv.HasType.const_inv`, `TrExprS.appN`,
`VEnv.contains_nat_of_hasType` and the `HasPrimitives.*` family. Two trproj lines
(`Bitwise.lean:203-204`) are a line re-wrap, nothing more.

**Why.** On `master`, `Ordered.strong : Ordered env → OnTypes env (EnvStrong env)` was a proved theorem,
so every inversion lemma that needed the strong system could take plain `Ordered`. The `iota` branch gives
`VEnv`'s ι-rule stage a real specification, and `Ordered`'s `defeq` step then admits definitional axioms
under which ι rules do not preserve types — the counterexample is written out at
`Lean4Lean/Theory/Typing/EnvLemmas.lean:325-333` (`List Nat ≡ List Bool` makes
`List.rec Nat m n c (List.cons Bool true tl)` well-typed with an ill-typed reduct). So `Ordered.strong`
was deleted and replaced by

```
structure OrderedStrong (env : VEnv) : Prop where
  ordered : Ordered env
  strong  : OnTypes env (EnvStrong env)
  pats    : PatsStrongOn env          -- Theory/Typing/Strong.lean:679
```

with `VEnv.WF.orderedStrong` (`EnvLemmas.lean:339`) discharging it from `VEnv.WF` — *modulo*

```
theorem VEnv.WF.patsStrong {env : VEnv} (H : env.WF) : env.PatsStrong := sorry   -- EnvLemmas.lean:334
```

The re-threading here is the knock-on consequence; the root cause is in other groups
(`Theory/Typing/Strong.lean`, `Theory/Typing/EnvLemmas.lean`, `Verify/Primitive.lean`,
`Verify/Environment/Primitive/Basic.lean`).

## 4. Assessment

**The reasoning is right.** Once ι rules are real, the strong system genuinely needs their subject
reduction; the honest thing is to name the obligation rather than to have it hidden inside a theorem that
was only provable because the ι stage was a stub (`master` had `VInductDecl.WF := sorry` and
`VEnv.addInduct := sorry` in `Theory/Inductive.lean`). Isolating it as one `sorry` with a 15-line docstring
that cites the thesis, gives a counterexample, and names what proving it would need (redex-typing inversion
plus injectivity of the block's type formers) is good practice, and it is *better* documented than most of
the surrounding code.

**The mechanical execution is fine but leaves the cost invisible.** The `CoeOut (VEnv.WF env)
env.OrderedStrong` instance (`EnvLemmas.lean:343`) means that the majority of call sites in these five
files did not even need editing; the 67 edits are the minority where the expected type was not available
for elaboration. The effect is that a reader of `Clauses.lean` or `Gcd.lean` sees
`ctx.Ewf.orderedStrong` in the middle of an otherwise ordinary proof and has no way to know that this is
where the branch's one open obligation enters. Not one of the 67 touched lines carries a comment, and
neither does any of the five files' module headers. For a contribution whose *point* is that the ι
obligation is now named and localised, not saying so where it is consumed is a missed opportunity —
`Verify/Primitive.lean` and these five files together are where every arithmetic-primitive result becomes
`sorry`-dependent.

**Local awkwardness.** `Bitwise.lean:41` binds `have hE := ctx.Ewf.orderedStrong` and then writes
`hE.ordered` at six of its eight uses (86, 150, 152, 182, 315, 362); the local name now advertises a
strength most of its uses do not want. Inside one proof, `Condition.lean:1448` writes
`VExpr.WF.lam_inv' c.Ewf.orderedStrong` while lines 1449-1450 — the same lemma, three lines later — pass
`c.Ewf` and let the coercion fire. This is what a minimal merge resolution looks like, which is defensible,
but the file now reads as if the two spellings meant different things. And after the merge
`Condition.lean` carries three different environment hypotheses with no stated rationale: `VEnv.WF`
(`ofClosed`, 540), `Ordered` (`weakR` 485, `of_nil_any` 664, `app1_nil_inv` 687) and `OrderedStrong` (the
six upgraded lemmas) — the last group only because `HasPrimitives.trNat`/`trBool`/`natIsType'` were
upgraded two files away.

**Statement quality (master's, for context).** The specifications here are unusually well chosen and
unusually well argued. `Condition.WF.propT` is applied rather than an arity, with the reason given
(`Condition.lean:155-159`); `vnil` is a field rather than a hypothesis, with the reason given (163-168);
`WF_ite` is positive rather than an elimination, with the reason given (219-238); the `natOnly` flag exists
because *nothing in the model pins `Nat`'s universe* (232-238), which is a real modelling gap honestly
declared rather than papered over. The beta-redex gadget of `Condition.check` (2242-2260) — checking
`prop`, `asBool` and `proof` against the binders of a redex so that a single `checkType` both reads them
and types them consistently — is genuinely clever and is explained. This is the standard the contributed
material sits against, and by that standard the contribution is a competent merge, not an addition.

**Defects found (all pre-existing master code except where noted):**

- `Condition.lean:26-30` — stale module docstring: it says the `Condition.check` calls for `Nat.bitwise`
  and for `unfoldNatWellFounded`'s `eager` gadget "currently sit under binders... can be hoisted".
  They have been hoisted: `Lean4Lean/Primitive.lean:409-410` and `:372` run them before the first
  `withLocalDecl`, which is why `Bitwise.lean` and `Gcd.lean` pass `hnil := rfl`.
- `Condition.lean:2438` — `Condition.fvarsIn_ite` is dead: no use anywhere in the repository
  (`fvarsIn_dite` is used once, `DivMod.lean:163`).
- `Bitwise.lean:31` — `checkNatBitwise.WF` is the only clause-level WF theorem in the group with no
  docstring, and the longest proof (375 lines).
- `Clauses.lean:225/252/280` — `checkNatLAnd.WF`, `checkNatLOr.WF`, `checkNatXor.WF` are near-duplicate
  25-30 line proofs; `checkNatBoolCases.WF` (170) right above them shows the parametrised alternative.
- `Condition.lean:744` — `TrExprS.propBoolProp` has no docstring although its five siblings do; it is also
  one of the six iota-upgraded statements.
- `Condition.lean:713-725` — `TrExprS.bvar0`..`bvar3` are four hand-rolled instances of one indexed
  statement, and are the only declarations in the file escaped to `_root_.Lean4Lean` rather than
  `Lean4Lean.Primitive`.

**No `sorry` appears in any of these five files.** Their dependence on `sorryAx` is entirely inherited,
through `VEnv.WF.orderedStrong` → `VEnv.WF.patsStrong`, on the iota/trproj branches. On `master` these
files needed only `VEnv.Ordered`.
