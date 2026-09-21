# Group `experimental-a` — the logical-relation research modules

Files (all under the repository root):

| File | Lines | Attribution | Live `sorry` |
|---|---|---|---|
| `Lean4Lean/Experimental/ShapeLogRel.lean` | 6100 | 100% master | 0 (but 6 in a dead block comment) |
| `Lean4Lean/Experimental/ShapeLogRelAdequacy.lean` | 473 | 100% master | 1 (line 154) |
| `Lean4Lean/Experimental/LogRel.lean` | 379 | 100% master | 7 `sorry` + 5 `stop` |
| `Lean4Lean/Experimental/CoinductiveLogRel.lean` | 61 | 100% master | 0 (95% comment) |

No blame file exists for any of the four, and `git log --author="Alessandro Sosso" -- <file>` is empty for
each. Every commit touching them is by Mario Carneiro (`84f2b04 "Finished injectivity! 🎉"`,
`1772f58`, `97addd5`, plus toolchain bumps). **The user's `iota`/`trproj` contributions do not appear
in this group at all.** The user's only involvement with `Lean4Lean/Experimental/` is repair work on
*other* files in the directory (`eddf009 "fix: repair Lean4Lean.Experimental for the ι additions"`,
`be30d35 "fix(experimental): account for the ι rule in the stratified developments"`), which touched
`NormalEq.lean`, `ParallelReduction.lean`, `Stratified*.lean`, `Stronger.lean` — not these four.

---

## 1. What the group is for

The thesis (`../lean-type-theory/unique.tex`) proves **unique typing** (`\autoref{thm:unique}`, line 4)
in three steps: stratify the judgement by conversion-alternation depth `⊢ₙ` (lines 10–17), show that
"definitional inversion" (sort injectivity, Π injectivity, sort ≢ Π — lines 29–39) implies unique typing
at each level (`thm:utype`, line 40), and then prove definitional inversion at level `n+1`
(`thm:1dinv`, line 258) via a Church–Rosser theorem for a κ-reduction relation (§`sec:kappa`,
§`sec:church_rosser`) that has to be split off from proof irrelevance because CR plainly fails for the
full `≡`.

`ShapeLogRel.lean` + `ShapeLogRelAdequacy.lean` are a **complete alternative to that route**: a
finitary, syntactic *model* (a logical relation) from which definitional inversion falls out directly,
with no `⊢ₙ` stratification and no Church–Rosser theorem. The payoff is 40 lines at the very end of
`ShapeLogRelAdequacy.lean`:

- `SExpr.forallE_inv` (`ShapeLogRelAdequacy.lean:450`) — Π injectivity;
- `SExpr.sort_forallE_inv` (`:455`) — a sort is never defeq to a Π;
- `SExpr.sort_inv` (`:459`) — sort injectivity.

These are consumed by `Lean4Lean/Experimental/UniqueTyping.lean:114,128,129,148,179` to derive unique
typing, which is precisely `thm:utype`. Methodologically this is a genuine improvement on the thesis —
`StrongSound.uniq` (`ShapeLogRel.lean:4750`) proves semantic unique typing *unconditionally*, where the
thesis can only get it relative to `⊢ₙ`.

`LogRel.lean` and `CoinductiveLogRel.lean` are earlier, abandoned attempts at the same target
(`git log`: *"experimental: attempts at adapting logrel-mltt"*). Nothing imports them.

## 2. Architecture of `ShapeLogRel.lean`

Six layers, bottom to top (672 top-level declarations):

1. **Shape algebra** (lines 41–1820, ~30% of the file). `Shape n` (`:53`) is a level-stratified
   syntax of finite approximations: `⊥`, `sort r`, `forallE`, `lam`, `ctor`, `indTy`, where function
   shapes are *finite tables* `List (Shape n × Shape n)` (`ShapeFun`, `:57`). On it: an order (`:126`),
   compatibility (`:79`), lifting `lift`/`plift`/`olift` (`:284`, `:421`, `:638`), join (`:745`),
   application (`:721`), and well-formedness (`Shape.WF`, `:852`). `WShape` (`:928`) is the
   well-formed subtype; `TShape = Σ n, WShape n` (`:1819`) forgets the level.
   The key semantic idea — a shape carrying no information is identified with `⊥`, so *proofs get shape
   `⊥`* — is encoded by the `NonZero` side-conditions in `Shape.WF` (`:852`) and by the smart
   constructors `lam'`/`ctor'` (`:812`, `:817`). It is nowhere documented.
   The deepest lemma here is `WShape.join_prop` (`:1557`): compatible well-formed shapes have a
   well-formed least upper bound.
2. **Shape typing** (`:2482`–`:3280`). A decidable `Shape.hasType` (`:2486`) with inductive
   characterisation `HasTypeU` (`:2513`), monotonicity (`:2681`, `:2772`), closure under joins (`:2960`),
   and the crucial `WShape.HasType.proofIrrel` (`:3211`): anything inhabiting a `Prop`-shape is `⊥`.
   `mono_l` needs a pigeonhole lemma `find_cycle` (`:2716`) that deserves to live in `Lean4Lean/Std`.
3. **Interpretation** (`:3282`–`:4360`). `LE_Interp ρ m M` (`:3333`) — "`m` is a lower bound on the
   meaning of `M`". Closed under monotonicity (`:3397`), directed (`compat_join`, `:3936`), and
   substitution (`LE_Interp.subst`, `:4087`, a clean iff with an existentially quantified valuation).
   `Valuation.Fits` + `InterpTyped` (`:4323`, `:4330`) are the finitary shadow of
   `soundness.tex` `thm:sound2`'s `⟦Γ ⊢ e⟧ᵧ ∈ tag(⟦Γ ⊢ α⟧ᵧ)`.
4. **Soundness** (`:4361`–`:5263`). `SoundEq`/`SoundTy` (`:4607`, `:4609`) are literally the two
   bullets of `soundness.tex` `thm:sound`. `StrongSound`/`StrongSoundCore` (`:4613`) is a strengthened,
   syntax-directed typing judgement; `StrongSound.uniq` (`:4750`) is semantic unique typing. The
   headline is `LE_Interp.strongSound` (`:5054`) / `LE_Interp.sound` (`:5261`).
5. **The logical relation** (`:5265`–`:5903`). `LogRel Γ n` (`:5271`) is a *record interface* with 20
   closure obligations; `LR0` (`:5307`) is the base (sorts must weak-head reduce to the *same* sort —
   this is where sort injectivity enters), `LRS` (`:5657`) the successor step, `LR` (`:5896`) the
   recursion. Good design: `LRS` is generic in its predecessor. `LRS.TyDefEq` (`:5431`) is non-trivial
   only at `sort` and `forallE` shapes, i.e. exactly at the two definitional-inversion clauses.
6. **Substitution glue** (`:5904`–`6100`). Lifting invariance (`LR.DefEq.lift`, `:6046`) and
   `LR.SubstWF` (`:6066`). The file ends abruptly here, with both namespaces left unclosed.

`ShapeLogRelAdequacy.lean` then defines `LR.Adequate` (`:8`), proves the fundamental theorem
`LR.adequacy` (`:106`), and probes it with *minimal* shapes — `forallE ⊥ ⊥` at level 1 for
`forallE_whRed_l` (`:434`), `sort (u ≠ 0)` for `sort_inv` (`:459`) — to read the inversion results off.
That probing trick is the punchline of the whole 6600-line development and is entirely undocumented.

## 3. Candid assessment

**Design.** The core idea is strong and, as far as I can tell, novel relative to the thesis: replace the
Church–Rosser/κ-reduction machinery with a finitary approximation model in which proof irrelevance is
*absorbed* (proofs have shape `⊥`) rather than quarantined. The `LogRel` record interface (`:5271`) is
the right abstraction, and `LE_Interp.subst` (`:4087`) and `StrongSound.uniq` (`:4750`) are elegant.

The main design weakness is structural. `Shape : Nat → Type` (`:53`) is a `def` by recursion on `Nat`
with a separate `WF` predicate, so every order/lift/join/typing lemma is written **three times** — once
for `Shape`, once for `WShape`, once for `TShape`. Compare `Shape.le_sort` (`:194`) /
`WShape.le_sort` (`:1268`) / `TShape` analogues (`:1905`–`:2030`). Roughly the first 2500 lines are this
boilerplate. A well-formed-by-construction inductive family, or a single `TShape`-level API with one
transfer principle, would plausibly have halved the file. The same duality (`WShape n` level-indexed vs
`TShape` level-erased) then forces `LR.DefEq.lift`/`LR.TyDefEq.lift` to be applied by hand at nearly
every use site in `ShapeLogRelAdequacy.lean` — see `LR.Adequate.cons` (`:45`), 48 lines of which
essentially all is level bookkeeping around a one-line mathematical idea ("join the two shapes").

**Proof quality.** Correct-looking but effectively unreviewable. Six proofs exceed 100 lines as single
uncommented tactic blocks: `LE_Interp.Const.compat_join` (`ShapeLogRel.lean:3786`, 150 lines),
`LE_Interp.compat_join` (`:3936`, 140), `LE_Interp.subst` (`:4087`, 145), `LE_Interp.strongSound`
(`:5054`, 207), the `LRS` record literal (`:5657`, 240 — 20 unnamed field proofs), and `LR.adequacy`
(`ShapeLogRelAdequacy.lean:106`, 325). The `variable (ih : ...)` + `include ih` idiom used to thread
induction hypotheses through helper namespaces (`:1391`, `:2733`) is clever but makes lemmas like
`WShape.join_prop.exists_max` (`:1396`) look like standalone results with mysterious hypotheses.
`LRIsType.irrel'` in `LogRel.lean:157` leans on `grind` for two `obtain rfl` steps — brittle across
toolchain bumps.

**Honesty of the claims — the most serious finding.** Three separate holes make the headline results
conditional, and none of them is flagged anywhere in these files:

1. `LR.adequacy` has a **live `sorry` at `ShapeLogRelAdequacy.lean:154`**, in the `const` case — i.e.
   terms that are bare constants. Since every real Lean term is built from constants, this is not a
   corner case. The commit that introduced the file is titled *"Finished injectivity! 🎉"*.
2. Both `LE_Interp.strongSound` (`ShapeLogRel.lean:5055`) and `LR.adequacy`
   (`ShapeLogRelAdequacy.lean:107`) open with `replace H := H.strong`, where `SExpr.IsDefEq.strong` is
   `sorry` at `Lean4Lean/Experimental/SExpr.lean:679`. SExpr.lean carries ~20 further `sorry`s
   (substitution lemmas at `:761`–`:798`, `:886`; `extra` cases at `:957`–`:996`).
3. The δ/ι (`extra`) case is discharged with **`axiom Params.extra_pat`** (`SExpr.lean:614`) — a real
   `axiom`, not a class field; the corresponding `Params` field is commented out at `SExpr.lean:42`.
   It asserts that every environment defeq is an instance of a registered pattern rule, which is
   essentially the hard content of ι-reduction. Relatedly, `Params.pat_uniq`/`pat_wf` are assumptions
   with no instance for Lean's real environment anywhere in the repo; whether they hold for Lean's
   actual recursor rules is not addressed here.

A `grep sorry ShapeLogRel.lean` returns 8 hits, all of which are inside the block comment at
`:1665`–`:1732` (an abandoned `Shape.WF.plift` proof). So a naive count *overstates* the holes in that
file and, because of (2) and (3), *understates* the conditionality of the development. Both directions
of error are easy to make here.

**Documentation.** 13 docstrings in 6100 lines, badly distributed. None on `Shape.WF` (`:852`),
`Shape.hasType` (`:2486`), `LE_Interp` (`:3333`), `InterpTyped` (`:4330`), `SoundEq`/`StrongSound`
(`:4607`), `LogRel` (`:5271`) or `LR` (`:5896`); two of them sit on the self-evident
`Valuation.Compat`/`Valuation.join` (`:3297`, `:3301`). Documentation quality jumps markedly in the last
600 lines (`LRS.PiDefEq` `:5373`, `LRS.TyDefEq` `:5429`, `LamDefEq.mono_l` `:5534`, `LamDefEq.whr`
`:5598`), where the docstrings even explain *why* proofs work — evidence that the author's standards
rose over the project, and a good template for retrofitting the rest.

**Dead code and redundancy.**
- `CoinductiveLogRel.lean` is 95% comment sketching a `coinductive` command that does not exist in
  Lean 4; its two live declarations are unused and `Classifier Γ A u := Classifier'` discards all three
  indices. It costs a dependency on `Theory.Typing.HeadReduction` and a ~300 KB olean for nothing.
- `LogRel.lean` is a superseded branch: `fundamental` (`:353`) is unproved (`| _ => sorry` catch-all),
  `LREqTy.symm` (`:246`) — the standard hard obligation in logrel-mltt developments — was never
  discharged, and five `stop` tactics are *silent* sorries (`stop tacticSeq` macro-expands to
  `repeat sorry` in Lean core `Init/Tactics.lean`). Its one genuinely nice artefact is the hand-rolled
  eliminator `LRIsType.rec` (`:139`) with the `Subsingleton` instance (`:189`).
- Latent namespace collisions: `Lean4Lean.SExpr.LogRel` is declared three times with incompatible
  definitions (`LogRel.lean:70` inductive, `ShapeLogRel.lean:5271` structure,
  `MoreStepIndexed.lean:371` structure); ditto `Classifier'` (`LogRel.lean:8`, `StepIndexed.lean:8`)
  and `NormalType` (`LogRel.lean:58`, `StepIndexed.lean:41`). Harmless today only because no module
  imports two of them.
- `Shape.trim` (`ShapeLogRel.lean:820`) is defined and never used. The `TShape` head-discrimination
  grid (`:1928`–`:2030`) is filled in only where later proofs needed it, so omissions look accidental.
- `set_option backward.do.legacy true` at `ShapeLogRel.lean:10` is a file-wide back-compat pin
  (leanprover/lean4#13305, digama0/lean4lean#31) to keep the `plift` proofs working — a large blast
  radius for a localised problem.

**Are the statements the right ones?** Yes. `forallE_inv`, `sort_forallE_inv` and `sort_inv` are
exactly clauses 2, 3 and 1 of the thesis's "definitional inversion" definition (`unique.tex:29`–`39`),
and `sort_inv`'s conclusion `u = v` on `SLevel` — already a semantic quotient of `VLevel`
(`SExpr.lean:48`) — is the right reading of the thesis's `ℓ ≡ ℓ'`. `SoundEq`/`SoundTy` match
`soundness.tex` `thm:sound` bullet for bullet, and the `Shape`/`TShape` hierarchy is a convincing
finitary analogue of the tagged types `Tₙ`/`tag(t)` of `soundness.tex:325`. The one statement I would
question is `StrongSoundCore.const` (`ShapeLogRel.lean:4623`), whose `(F : ∀ cl, CtorBundle c cl)`
quantifies over *every* classification of a constant, which looks over-general.

**Bottom line.** The best research artefact in this group by a wide margin is the ShapeLogRel /
ShapeLogRelAdequacy pair: a real methodological advance over the thesis's route to unique typing, let
down by one unfinished case, an undisclosed axiom, an undisclosed dependence on `IsDefEq.strong`, and
documentation that assumes the reader is the author. `LogRel.lean` and `CoinductiveLogRel.lean` are
dead branches that should be deleted or explicitly labelled. Since none of it is the user's work, the
relevance to a review of the `iota`/`trproj` contributions is only as context: it shows the house style
(very large single-block proofs, sparse docstrings, `Params`-style axiomatised environments) that the
user's contributions are being measured against.
