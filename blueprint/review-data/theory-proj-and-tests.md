# Group `theory-proj-and-tests`

Files: `Lean4Lean/Theory/Proj.lean` (449 lines, 100% `trproj`), `Lean4Lean/Tests/ProjInhabit.lean`
(597, 100% `trproj`), `Lean4Lean/Tests/ProjShape.lean` (185, 100% `trproj`),
`Lean4Lean/Tests/IotaShape.lean` (607: 603 `iota`, 4 `trproj`),
`Lean4Lean/Tests/ShapeDecide.lean` (78: 67 `iota`, 11 `trproj`).
No master code in this group at all: everything here is contributed.

## 1. What the files do

### `Theory/Proj.lean` — projections as recursor expansions

`VExpr` has no projection node. The trproj design decision is that `Expr.proj S i e` is modelled
by an application of the recursor the kernel generates for `S`:

    P_i e,   P_i = S.rec (uss i) ps (λ x : S ps. F_i[f_j := P_j x]) (λ f₀ … f_{n-1}. f_i)

This is literally the shape of the thesis's `inv_x` (typesys.tex §3.1, "Undecidability of
definitional equality"), which projects the argument of `intro` out of a proof of `acc x` through
`rec_acc`; and the dependent typing `P_i e : F_i[f_j := P_j e]` is the thesis's *primitive*
projection typing `π₂ p : β[π₁ p/x]` (Wtypes.tex §5.1, whose W-type system omits the recursors for
Σ in favour of projections). The per-field level list `uss j` implements the thesis's remark
(axioms.tex §2.6.3) that the motive's universe `u` in `κ = ∀a::α. P a → U_u` is a *fresh* variable
per use of `rec_P`: `Sigma.fst` needs `Sigma.rec.{u+1,u,v}`, `Sigma.snd` needs `Sigma.rec.{v+1,u,v}`.

The file is cleanly layered:

* builders — `fieldSelector` (Proj.lean:70), `instPis` (75), `instFields` (84),
  `projMotiveBodyOf` (91), `projFnOf` (96), `projFns` (108), `projMotiveBody` (114), `projFn` (120),
  `projTy` (127), `binderArity?` (136);
* four unfolding facts (140–153);
* ~30 lemmas pushing `subst` / `lift'` / `inst` / `instL` through every builder (164–384);
* five lemmas about `instFields` on variable spines (394–446), ending in
  `instFields_minor_spine`, the arithmetic core of `TrEnv.proj_defeq`.

The substitution section has an explicit and, in my judgement, correct design note (155–162):
`lift'` and `inst` are both instances of `subst`, so each builder is proved once against `Subst`
and the weakening/instantiation forms are read off. This keeps 30 lemmas honest at maybe a third of
the cost of proving each separately. The consumers are `Verify/Typing/Lemmas.lean`
(`TrProj.weak'`:641, `TrProj.instN`:1296, `TrProj.instL`:1588) and
`Verify/Environment/Lemmas.lean` (`TrEnv.proj_defeq`:1021), and the lemma set matches what they
need almost exactly — `projFn_lift'`, `projFn_inst`, `projFn_instL`, `projMotiveBody_lift'`,
`projMotiveBody_instN`, `projMotiveBody_instL`, `instPis_lift'/inst/instL`, `foldr_lam_inst`,
`instFields_bvar`, `instFields_minor_spine` are all used. The only exception is `projTy` (see §3).

The 55-line module docstring is exceptionally good documentation: it states the de Bruijn
conventions explicitly (which index each field is, what `liftN 1 i` does, why `instFields` goes
outermost-first), sketches the typing derivation in three steps (a)(b)(c), and names what the
representation does *not* carry — structure η, which the checker's `tryEtaStruct` and
`toCtorWhenStruct` have and `IsDefEq` does not.

### `Tests/ProjShape.lean` — the kernel side

`checkProj S i lvls` (ProjShape.lean:68) does four things per structure/field: reads the
constructor telescope off the kernel with `instPis`/`piBinders` exactly as `inferProj` does; has
the **real kernel** accept `fun ps (x : S ps) => P_i x : ∀ ps (x : S ps), projMotiveBody` via
`Environment.addDeclCore`; checks `isDefEq` against the kernel's own `inferType (.proj S i x)`;
and checks that `P_i (mk ps fs)` `whnf`s *syntactically* to `fs[i]` (line 119). It runs on `Prod`
0/1, `Sigma` 0/1, `PSigma` 1, `Subtype` 0/1, `Fin` 1, `And` 1, and a three-field `V3` whose last
motive mentions two earlier projections, one inside the other's motive. Two negative controls: a
single level list for every field is rejected at `Sigma.snd`, and `binderArity?` of the reflexive
`Refl.rec`'s minor is `2`, not `1`. A closing section `decide`s the exact de Bruijn form of the
`Sigma.snd` expansion (166–181).

### `Tests/ProjInhabit.lean` — the model side

Two hand-built inductive blocks declared through `VEnv.addInduct`: `Plain` (`S.mk : A → A → S`,
constant motive) and `Dependent` (`S2.mk : (a : A) → B a → S2`, dependent motive
`λ x. B (P₀ x)`). For each, `TrProjCtor` is inhabited for both fields (`inhab0`:151,
`inhab1`:164, `inhabDep0`:538, `inhabDep1`:550), with `fn_ty` derived by hand from the forward
rules of `IsDefEq`.

The interesting half is `Dependent`. To type the second selector at the minor type
`∀ a b, M₂₁ (mk a b)` one must show `B a ≡ B (P₀ (mk a b))`, i.e. that the *first* projection
computes on the generic constructor spine. That is done properly: `hmatch` (337) exhibits the
`Pattern.Matches` derivation, `hiota` (344) fires `VEnv.IsDefEq.pat` on the registered ι rule,
and `hproj0red` (485) chains it with six β steps to `P₀ (mk a b) ≡ a`. `hP1ty` (531) then
assembles `P₁ : ∀ x : S2, B (P₀ x)`. This is exactly step (b) of the docstring derivation in
`Theory/Proj.lean:45–48`, mechanized on an instance, and it is the strongest evidence in the whole
trproj contribution that the design is workable.

The file ends (562–595) with five `#guard_msgs in #print axioms` blocks. The four witnesses depend
on `[propext, Quot.sound]` only. The fifth pins `Lean4Lean.TrEnv.proj_defeq`'s axioms, which
include **`sorryAx`** — that is the "sorry" in this file: not a literal `sorry` (there is none),
but a recorded inheritance from `VEnv.WF.patsStrong` (`Theory/Typing/EnvLemmas.lean:334`), unique
typing (`UniqueTyping.lean:174`) and Π-injectivity (`Injectivity.lean:12,21,34`).

### `Tests/IotaShape.lean` and `Tests/ShapeDecide.lean` — the iota branch's specification tests

`ShapeDecide` makes every syntactic predicate of `Theory/Inductive.lean` executable, in a Tests
module so the library keeps them propositional (explicitly justified at lines 3–11). `IotaShape`
then decides all of `VInductDecl.WF` on the kernel's own data for 41 type formers plus nine nested
blocks, and compares `SimplePattern.iotaRHS` with `inductiveReduceRec`'s reduct on twelve rules.
What lifts it above the usual "run it on some examples" is the density of *negative* controls
(454–592): `RecShape` rejecting three wrong telescope splits of `Nat.rec`; `RuleShape` rejecting
wrong field counts and wrong numbers of inductive hypotheses; a reduct firing the wrong minor; a
`succ` rule with its inductive hypothesis dropped (a case-analysis reduct); a bare motive as a
minor premise; a minor headed by its own binder; a major premise over the wrong type former; a
`zero` minor targeting `motive (succ zero)`. Plus two things Lean's elaborator refuses to declare,
written as `VExpr` literals: a non-positive constructor (397–405) and a two-constructor `Prop`
whose recursor asks for large elimination (411–450) — the declaration that would collapse
definitional equality, refused by `VInductDecl.LargeElimShape` and nothing else. These are what
make `VInductDecl.WF` credible as a *tight* specification of thesis §§2.6.1–2.6.4 rather than
merely a satisfiable one.

## 2. Thesis correspondence

| Code | Thesis |
|---|---|
| `projFn`, `projFnOf`, the whole expansion | typesys.tex §3.1, `inv_x` through `rec_acc` |
| `projMotiveBody`, `projTy` | Wtypes.tex §5.1, `π₁ p : α`, `π₂ p : β[π₁ p/x]` |
| `uss : Nat → List VLevel` | axioms.tex §2.6.3, `κ = ∀a::α. P a → U_u`, `u` fresh per use of `rec_P` |
| `fieldSelector`, `binderArity?` | axioms.tex §2.6.3, minor premise `ε_c = ∀b::β.∀v::δ. C p[b] (c b)` |
| `instFields_minor_spine`, `checkIota`, `hiota` | axioms.tex §2.6.4, `rec_P C e p[b] (c b) ≡ e_c b v` |
| `CtorPositive`/`badCtorType` controls | axioms.tex §2.6.1, the two kinds of constructor argument |
| `LargeElimShape`/`TwoCtorProp` | axioms.tex §2.6.2, the two reasons for large elimination |

The deviation worth naming is deliberate and documented: the thesis's `acc` example is a
*recursive* inductive and its `inv_x` binds the inductive hypothesis, whereas `TrProjCtor`'s
`minor_arity` restricts the model to non-recursive single-constructor types. So the code borrows
the thesis's *shape* while excluding the thesis's own example (`Refl`, the reflexive structure, is
the negative control at ProjShape.lean:39). That is a completeness boundary, not a soundness one,
and `Verify/Typing/Expr.lean:85–88` says so.

## 3. Assessment of the contributed parts

**Design.** The central choice — no projection node, a projection *is* the recursor expansion —
is well argued (`divergences.md` line 15 justifies the kernel-side claim that `inferProj`'s Prop
gate keeps a projection no more powerful than the generated recursor) and it is the choice that
keeps `IsDefEq` unchanged. The two-layer split `projFnOf`/`projFn` (parameterised by the earlier
projections, vs closed) exists only to let the substitution lemmas be stated generically, and it
pays for itself. The per-field level list `uss` is genuinely necessary and is validated on the
kernel (`Sigma` 0 vs 1 at ProjShape.lean:125–126 with the negative control at 136).

Two design smells. First, `instFields` is a *second* telescope-substitution convention alongside
the master `VExpr.insts`; the section docstring (Proj.lean:195–203) argues convincingly that
neither is a special case of the other, but no lemma relates them, so the two conventions never
meet. Second, `projFns` (Proj.lean:108–111) mentions its own predecessor twice in its defining
equation, making the expansion exponential in the field index and forcing every induction over it
to apply the IH twice.

**Proof quality.** `Theory/Proj.lean` has no `sorry` and the proofs are tight — mostly structural
recursion plus `rw`, with the `Subst`-first strategy avoiding duplication. `instFields_bvar` and
`instFields_minor_spine` are the only fiddly ones and they are stated in exactly the form
`TrEnv.proj_defeq` consumes. `ProjInhabit`'s derivations are pure term-mode `IsDefEq` and are
correct but extremely verbose: 22 declarations (353–493) for a six-step β-reduction, because
`IsDefEq` has no usable `betaN` combinator at this level (`VEnv.IsDefEqU.betaN` exists in
`Verify/Environment/Lemmas.lean` but needs `VEnv.WF`, which these hand-built environments do not
have).

**Documentation.** Best-in-class for this repo. Every definition has a docstring; the module
docstrings state scope, conventions and known limitations; `Verify/Typing/Expr.lean:69–88` repeats
the model for `TrProjCtor` and names the completeness boundary. Two places over-claim slightly:
"Only forward rules of `IsDefEq` are used" (Proj.lean:52) — `symm`/`trans` are used throughout —
and `binderArity?`'s "has exactly the `nf` fields as binders" (Proj.lean:131–135), which pins only
the count.

**Are the statements the right ones?** Mostly yes, with one real gap and one real limit.

* The gap: `VExpr.projTy` (Proj.lean:127) is used nowhere outside `ProjShape.lean:178`, and the
  identity its docstring asserts — `projTy … e = (projMotiveBody … i).inst e` — is never proved
  (it is true; it follows from `instFields_subst` plus `inst_liftN`). So the definition the prose
  uses to explain `inferProj` is formally disconnected from the one `TrProjCtor.fn_ty` uses.
* The limit: `inferProj.WF_struct` (`Verify/TypeChecker/InferType.lean:398`) is `sorry`. The
  inhabitation witnesses show `TrProjCtor` is non-vacuous; they do not show that a kernel-accepted
  projection yields one. The general construction exists only as the docstring derivation. A
  reviewer should read the trproj projection work as "the model and its metatheory are in place
  and demonstrably satisfiable; the bridge from the kernel is still open", which is exactly what
  the code says of itself.

**Test value.** `ProjShape` is high-value per line: three independent kernel checks on nine
structure/field pairs. `ProjInhabit` is high-value but low-density: ~600 lines for four
`TrProjCtor` witnesses whose coverage is narrower than it looks — `np = 0`, `usS = []`, `uss`
constant, at most two fields — so the substitution lemmas `projFn_subst`/`projFn_instL` never meet
a non-trivial instance in any test. `IotaShape` is the best test in the group: its negative
controls are what give `VInductDecl.WF` its credibility.

**Dead / redundant code.** `projTy` (unused in the library); `projMotiveBody_zero` and
`instFields_nil` are `@[simp]` but never explicitly invoked; the `Plain` namespace of
`ProjInhabit` is largely subsumed by `Dependent` (~20 duplicated declarations), and untracked
near-copies of both live in `review-artifacts/inhabitation/`. Naming gaps (`T4`, `hc4` missing;
`trProj1`, `trProjDep0` missing) suggest an edited-down chain.

**Build integration.** `Theory/Proj.lean` is pulled in by `Verify/Typing/Expr.lean`, so it is in
the default targets; the four Tests modules are built by the explicit `lake build Lean4Lean.Tests`
step in CI (`.github/workflows/ci.yml`), whose comment incorrectly says `Lean4Lean.Tests` is among
`defaultTargets` (`lakefile.toml` omits it). All four test modules assert at elaboration time, so
a regression fails the build.
