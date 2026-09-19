# Group `kernel-impl` — the executable Lean 4 kernel

18 files, 4040 lines. This is *the code being verified*: a Lean re-implementation of
`src/kernel/*.cpp`, written so that the `Lean4Lean/Verify/` layer can reason about it.
Of these 4040 lines, **exactly 22 are contributed**: 21 on `trproj` in
`Lean4Lean/Inductive/Reduce.lean` and 1 on `iota` in `Lean4Lean/Quot.lean`. Everything else is
Mario Carneiro's upstream code. That ratio is itself the headline finding, and it is a *good*
one: the brief the user was working under said not to change kernel code lightly, and they
didn't.

## What the files do

**The type checker** (`TypeChecker.lean`, 979 lines) is the centre. It implements the two
judgments of the thesis's §"The type system" (`axioms.tex`): algorithmic typing
`inferType'` (line 263) and algorithmic definitional equality `isDefEqCore'` (line 841), with
weak-head normalization (`whnfCore'` line 364, `whnf'` line 519) underneath. The single most
important structural decision is `Methods`/`Methods.withFuel` (lines 64, 893): the four mutually
recursive operations are passed as a record and the knot is tied at a finite depth, so nothing in
the file is `partial` and every definition has usable equations. The price is a real behavioural
divergence (`.deepRecursion`/`.deterministicTimeout` where the C++ kernel would keep going),
documented in `FuelConfig.lean` and `divergences.md`.

**Reduction of eliminators** splits in two: `Quot.lean:106` (`quotReduceRec`) for the quotient
computation rule `lift f h (mk r a) ↝ f a`, and `Inductive/Reduce.lean` for the ι rule
`rec_P C e p[b] (c b) ↝ e_c b v` (`axioms.tex` §\ref{sec:iota}) plus its two "make the major a
constructor first" preludes, K-like reduction (`toCtorWhenK`, line 29) and struct-η
(`toCtorWhenStruct`, line 58). The thesis itself describes K-like reduction as "proof irrelevance
to change the major premise into a constructor followed by the iota rule" — which is precisely the
decomposition the trproj change makes explicit in code.

**Declaration admission** is `Environment.lean:118` (`addDecl`) dispatching to per-kind checkers,
and `Inductive/Add.lean` (776 lines) for inductive blocks. `Inductive/Add.lean` is a close
transcription of the thesis's §\ref{sec:inductive}: `checkPositivity` (line 157) is the `ctor`
judgment, `isLargeEliminator`/`isKTarget` (line 258) are the `LE`/`LE-ctor` judgments including
the `y ∈ e` side condition, `mkRecInfos` (line 408) builds `κ`, `ε`, `δ`, and `mkRecRules`
(line 419) emits exactly the thesis's `e_c b v` with
`vᵢ = λ x::ξᵢ. rec_P C e πᵢ[b,x] (uᵢ x)`. `ElimNestedInductive` (line 498) has no thesis
counterpart at all and is the least trustworthy part of the kernel.

**Supporting layers**: `Level.lean` (363 lines) implements Géran's canonical form for universe
levels, deliberately *more complete* than both core Lean and the C++ kernel; `Primitive.lean`
(611 lines) closes a genuine C++ soundness gap by checking that the prelude's `Nat.add`,
`Nat.div`, … really behave as the GMP fast paths assume; `PtrEq.lean` isolates the two trusted
pointer-equality axioms; `Replay.lean` + `Main.lean` are the unverified CLI driver, whose
`checkPostponedRecursors` (line 245) is in practice the only end-to-end differential evidence that
`mkRecRules` agrees with Lean's own elaborator across whole libraries.

`divergences.md` is unusually good: fourteen entries, each naming the C++ function, the upstream
PR where relevant, and the argument for the divergence. Reviewers should treat it as part of the
deliverable.

## The contributed changes

### `Lean4Lean/Inductive/Reduce.lean:71-89` and `:115` — `inductiveReduceRecCore` (trproj)

A pure function extracted verbatim from the tail of `inductiveReduceRec`:

```
def inductiveReduceRecCore (rval : RecursorVal) (ls : List Level) (recArgs : Array Expr)
    (major : Expr) : Option Expr
```

I diffed it against `git show master:Lean4Lean/Inductive/Reduce.lean` line by line. The body is
identical; the only textual change is that the caller's `let majorIdx := info.getMajorIdx` binding
becomes `rval.getMajorIdx` at the two use sites, which is the same value. The claim in commit
`7a68882` ("behaviour-preserving; the extracted body is the original one, with `getMajorIdx`
recomputed where the caller had bound it") is accurate.

**Is it justified?** Yes, and for a good reason. `inductiveReduceRec` is monadic
(`m (Option Expr)`, with `whnf`, `inferType`, `isDefEq` in scope) because of the K-like and
struct-η preludes; the ι step itself is pure and total. Splitting it lets
`Verify/TypeChecker/WHNF.lean:17` state `inductiveReduceRecCore.WF` — the reduct translates to the
redex's own translation — about a function with no monad, no environment lookup and no
well-typedness side conditions beyond the ones passed as hypotheses. Without the split, the
theorem would have had to be stated about a monadic computation whose other branches
(`toCtorWhenK`, `toCtorWhenStruct`) genuinely have no `IsDefEq` counterpart yet. The commit is
explicit that `reduceRecursor.WF` therefore stays open — an honest scoping statement, not an
overclaim.

**Design quality**: good, with three small blemishes, all cosmetic.
1. `Lean4Lean/Inductive/Reduce.lean:75` sits inside the `section` at line 9 whose `variable`s
   (`[Monad m] (env) (whnf) (inferType) (isDefEq)`) it uses none of. Lean binds only used section
   variables so the arity is the intended 4, but the placement is misleading and a future edit
   that touches `env` would silently change the signature and break the `WF` theorem's statement.
2. The new docstring (lines 71-74) duplicates the slicing description already in the *unchanged*
   master docstring of `inductiveReduceRec` (lines 91-99). The file now documents the ι slicing
   twice, and the caller's docstring describes work it no longer does. Trimming the caller's
   docstring to the preprocessing it still performs would have completed the refactor.
3. `inductiveReduceRecCore` collapses "no rule for this constructor", "major has too few
   arguments" and "wrong number of universe arguments" into a single `none`. That is faithful to
   master, but it is why `inductiveReduceRecCore.WF` has to take saturation (`hsat`) as an
   external hypothesis rather than deriving it. The commit message says so plainly.

The extracted function is also exercised as a differential oracle by
`Lean4Lean/Tests/IotaShape.lean:151`, which compares the model's `SimplePattern.iotaRHS` reduct
against `inductiveReduceRec` on real environments — a sensible way to keep the iota specification
honest against the kernel.

### `Lean4Lean/Quot.lean:24` — `if info.isUnsafe then fail "'Eq' type is unsafe"` (iota)

One line, and the only kernel-code change on the `iota` branch. The argument (commit `30897c0`,
plus a paragraph in `divergences.md`) is: `quot.cpp`'s `check_eq_type` pins the *shape* of `Eq` but
not its safety; the four quotient constants `addQuot` inserts carry no safety flag, so they are
safe; `Quot.lift`'s type mentions `Eq`; therefore an `unsafe inductive Eq` would leave safe
constants depending on an unsafe one, and the safe-level abstract environment would have no model.

This is the right kind of kernel change for a verification project: it is in the *reject-more*
direction (never accepts something the C++ kernel rejects), it is one line, it is recorded as a
divergence, and it **pays for itself** — `Verify/Environment/Quot.lean:addQuot.WF` and
`Verify/Environment.lean:addDecl.WF` both lost the `Environment.EqSafe` hypothesis and are now
unconditional, and the assumption `Environment.EqSafe` was deleted outright. Trading a global
assumption on all callers for one computed check is a clear win.

**One caveat the commit message and `divergences.md` do not state.** `Environment.addQuot`
(`Lean4Lean/Quot.lean:40`) returns immediately when `env.quotInit` is already true, and
`Lean.Kernel.Environment.finalizeImport` (`Lean4Lean/Environment/Basic.lean:124`) sets
`quotInit := !imports.isEmpty` unconditionally. So on any *imported* environment — which is the
normal `replayFromImports` mode — neither the shape check nor the new safety check ever runs. The
new guarantee holds for environments built from scratch (`replayFromFresh`, which replays
`Init.Prelude` and so does call `addQuot`). This is a pre-existing gap in the trust story, not one
the contribution introduced, but it does bound what the removed `EqSafe` hypothesis actually buys.

### Verdict on the contributed kernel code

Both changes are small, correct, motivated by a concrete proof obligation, documented in the
commit message *and* in `divergences.md`, and neither is speculative. The `Reduce.lean` split is a
pure refactoring whose behaviour-preservation I verified against master; the `Quot.lean` line is a
deliberate, argued divergence that discharges an assumption rather than adding one. Documentation
discipline is above the repository's (already high) average. The only things I would push back on
are the duplicated docstring at `Inductive/Reduce.lean:71` vs `:91` and the section-variable
placement — both cosmetic.

## Candid notes on the surrounding (master) code, for context

These are not the user's work, but a blueprint reviewer will hit them and they bound what the
contributions can claim.

- `Verify/Environment.lean:208` — `addDecl.WF`'s `inductDecl` case is `sorry`, because the
  `AddInduct` witness must be constructed from `Environment.addInductive`
  (`Lean4Lean/Inductive/Add.lean:733`) and nobody has. Everything the iota branch proves about
  inductive blocks lives on the *model* side of that gap.
- `Lean4Lean/PtrEq.lean:17,22` — two genuine trusted axioms. They are used in only two places, but
  at `TypeChecker.lean:739` `ptrEqConstantInfo dt ds` gates a *different algorithm* (congruence
  before unfolding), not merely a shortcut, exactly as the file's own docstring warns.
- `Lean4Lean/Level.lean` — a new, complete level-normalization algorithm with no correctness
  statement anywhere in the repository; the soundness argument is the informal one in the
  `isEquiv'` docstring (line 351) plus `divergences.md`.
- `TypeChecker.lean:299, 541, 782, 845` — the `eagerReduce` marker changes defeq strategy based on
  a syntactic check for a constant in an argument. It has no thesis counterpart and is the one
  deviation in that file with no `divergences.md` entry.
- `TypeChecker.lean:946` — `etaExpand` has no call site. If it is meant to be the thesis's
  `rec`-normal-form preprocessing (`unique.tex` §\ref{sec:kappa}, the map `ē` that saturates every
  `rec` and `lift` before `κ`-reduction is even defined), that is undocumented — and it matters,
  because the saturation hypothesis `hsat` in `inductiveReduceRecCore.WF` is the executable
  counterpart of exactly that preprocessing.
- `Lean4Lean/ForEachExprV.lean` — appears to be dead code; imported but never called.
- `TypeChecker.lean:593` — `quickIsDefEq` destructures `TypeChecker.State` positionally
  (`.mk a1 … a7 (eqvManager := m)`), which breaks silently on a field addition.
- `Inductive/Add.lean:453, 469` — `isUnsafe` computed twice in `AddInductive.run`.
- `TypeChecker.lean:968-979` — a commented-out `example`/`run_tac` scratch block.

## Thesis correspondence at a glance

| Kernel definition | Thesis |
|---|---|
| `inferType'`, `isDefEqCore'` | `axioms.tex` §The type system; `typesys.tex` lemma \ref{item:alg_defn} |
| `isDefEqProofIrrel` | proof irrelevance rule; `typesys.tex` §\ref{sec:undecidable} |
| `unfoldDefinition` / `deltaValue?` | `axioms.tex` δ rule |
| `inductiveReduceRecCore` | `axioms.tex` §\ref{sec:iota} `rec_P C e p[b] (c b) ↝ e_c b v` |
| `toCtorWhenK` | `axioms.tex` §\ref{sec:iota} K-like reduction |
| `quotReduceRec`, `addQuot` | `axioms.tex` §Quotient types |
| `checkEqType` | `axioms.tex` §\ref{sec:large_elim} `eq_a := μt:α→P.(refl : t a)` |
| `checkPositivity`, `checkConstructors` | `axioms.tex` `spec`/`ctor` judgments |
| `isLargeEliminator`, `isKTarget` | `axioms.tex` §\ref{sec:large_elim} `LE`/`LE-ctor` |
| `mkRecInfos`, `mkRecRules` | `axioms.tex` §The recursor (κ, ε, δ) and §\ref{sec:iota} |
| `etaExpand` | `unique.tex` §\ref{sec:kappa} `rec`-normal form (but unused) |
| `Level.isEquiv'`, `geq'` | `axioms.tex` `ℓ ≤ ℓ' + n` (implemented *more completely*) |
| `inferProj`, `reduceProj`, `toCtorWhenStruct` | **no counterpart** — the gap the trproj branch fills |

That last row is the point worth making in the blueprint: the thesis's type theory has no
`Expr.proj` and no struct-η at all, so the trproj work is not re-formalizing something Carneiro
already did — it is extending the model to cover kernel features the thesis simply omits. The
kernel-side definitions it has to match are `TypeChecker.lean:233` (`inferProj`),
`TypeChecker.lean:343` (`reduceProjCore`) and `Inductive/Reduce.lean:58` (`toCtorWhenStruct`), and
two of those three already carry a documented divergence from the C++ kernel
(`isNeverZero` vs `!isAlwaysZero`), which narrows the class of projections any `TrProj` theorem can
be about.
