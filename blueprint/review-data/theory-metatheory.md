# theory-metatheory — ChurchRosser, HeadReduction, UniqueTyping, Strong

Files (all under `Lean4Lean/Theory/Typing/`):

| file | lines | M | I | P |
|---|---|---|---|---|
| `ChurchRosser.lean` | 1394 | 1385 | 9 | 0 |
| `HeadReduction.lean` | 696 | 696 | 0 | 0 |
| `UniqueTyping.lean` | 279 | 279 | 0 | 0 |
| `Strong.lean` | 1308 | 1144 | 164 | 0 |

No `trproj` (projection) lines anywhere in this group.

## What the four files do, and how they line up with the thesis

These four files are the metatheory spine of `Lean4Lean/Theory`: they take the declarative
judgment `VEnv.IsDefEq` (Typing/Basic.lean) and prove about it the things the rest of the
project needs — regularity, unique typing, confluence, standardization, and a syntax-directed
reading of typing.

**`Strong.lean`** defines `IsDefEqStrong` (`Strong.lean:18`), a copy of `IsDefEq` in which
every rule carries the typing derivations its statement implicitly needs (`appDF` carries the
types of domain, codomain and instantiated codomain; `beta` carries the type of the reduct;
`extra` carries both sides of the axiom in the empty *and* the current context). Its purpose
is to make the thesis' regularity lemma (typesys.tex, Lemma `thm:reg`) structural rather than
a separate induction: `isType'` (525), `forallE_inv'` (472), `hasType'` (825) simply read the
annotations off. `HasTypeStrong` (108) is the syntax-directed typing judgment, separated from
the conversion rule by a boolean index so inversion is trivial; `HasTypeStratified` (944) is
the thesis' `⊢ₙ` (unique.tex §sec:unique). The bridge `IsDefEq.strong` (805) is where an
ordinary derivation acquires the annotations, and it is the choke point of the whole file.

**`UniqueTyping.lean`** proves `IsDefEq.uniq` (13) — unique typing, thesis Theorem
`thm:utype` — by stratifying both sides and doing a well-founded induction on the level, and
then derives the everyday toolkit (`trans_l`, `trans_r`, `transU_*`, `defeqU_*`) plus
conservativity of weakening in typed/untyped/`lift'` form.

**`ChurchRosser.lean`** is unique.tex §sec:church_rosser, essentially verbatim: `NormalEq`
(84) is the thesis' `≡ₚ`; `ParRed` (473) is `≫κ`; `CParRed` (488) is the complete reduction
`⋙κ` with its neutrality side condition; `ParRed.triangle` (766) is the Triangle lemma
`thm:tri`; `NormalEq.parRed` (1181) is `thm:gg_compat`; `ParRedS.church_rosser` (1302) is
`thm:church_rosser`; `CRDefEq` (1297) is `≡κ`; and `IsDefEq.church_rosser` (1347) is the
forward direction of `thm:ckappa`. The whole file is parameterized by a class `Params` (12)
abstracting the family of reduction rules, which is how the development avoids committing to
a particular ι-rule format.

**`HeadReduction.lean`** has no thesis counterpart for its core: it proves the standardization
theorem following Kashima (2000) (`ParRedS.standard`, 466), and uses it plus Church–Rosser to
get the two inversions that everything algorithmic needs — a term definitionally equal to a
sort/Π head-reduces to a sort/Π (470, 488) — and then the syntax-directed `InferType` (508)
with soundness (519), determinism (534) and completeness (`InferType.exists`, 633).

## The iota contribution

The iota branch adds one constructor to `IsDefEq` (in Basic.lean, another group) —
`IsDefEq.pat`, ι reduction by a rule registered in `env.pats` — and the consequences in this
group are exactly what one would want:

1. **`IsDefEqStrong.pat` (`Strong.lean:89`)**, with a docstring explaining the design. It
   mirrors `IsDefEq.pat` but adds one premise: `Γ ⊢ r.1.apply m1 m2 : A`, the typing of the
   *reduct*. This is not decoration. Four later proofs close their `pat` case only because of
   it: `forallE_inv'` (518–521, which must invert whichever side is a Π), `isType'` (548),
   `hasType'` (863), and `EqUpToLevels.defeq` (654–657). It is also exactly parallel to how
   master's `beta` carries `e.inst e'` and `extra` carries both sides. Good judgement.

2. **A `pat` case in each of the ten structural lemmas** (`weakN` 193, `defeq` 216, `mono`
   237, `EqUpToLevels.instL` 278, `instL` 362, `instN` 453, `forallE_inv'` 518, `isType'` 548,
   `EqUpToLevels.defeq` 654, `hasType'` 863, `substEq'` 1259). Each is 1–11 lines and follows
   the same recipe: commute the operation with `Pattern.RHS.apply`, transport the match
   (`Pattern.matches_*`) and the realizer (`Realizes.map_*`), then map the check triples. The
   supporting transport lemmas live in `Pattern.lean` (another group), which is the right
   place for them. This is disciplined, uniform work with no duplication.

3. **`PatStrong` / `PatsStrongOn` / `OrderedStrong` (663, 672, 679)** — the new environment
   hypothesis. `PatStrong env p r` is subject reduction for one rule, stated with exactly the
   data a proof would need (strong context, the match, the redex's strong typing, the
   realizer, the per-triple equalities). `OrderedStrong` bundles `Ordered`, `OnTypes
   (EnvStrong ·)` and `PatsStrongOn`. The docstrings at 659–682 state, correctly and without
   hedging, why subject reduction for ι cannot follow from `Ordered`: `Ordered` admits
   arbitrary well-typed definitional axioms, and under `List Nat ≡ List Bool` an ι redex can
   be well-typed with an ill-typed reduct.

4. **The refactoring of master's `Ordered.strong`** into `EnvStrong.of_hasType` (759) plus
   `OnTypes.addConst` (770) / `addDefEq` (785) / `addPat` (797), with `EnvStrong.mono` (319)
   extracted from an inline lambda. Master proved `Ordered.strong : Ordered env → OnTypes env
   (EnvStrong env)` by a single induction over the environment construction; that induction
   now has to thread a `PatsStrongOn` hypothesis through every stage, so it moved to
   `EnvLemmas.lean` (`VEnv.WF.strong`, EnvLemmas.lean:263). The decomposition is clean and
   every piece is used (all four are consumed in EnvLemmas.lean:155–320); nothing here is dead.

5. **Signature changes `Ordered env → OrderedStrong env`** in about a dozen places (885, 895,
   900, 909, 914, 923, 928, 1044, 1273, 1282, 1288, 1293, 1298, 1304, and in ChurchRosser via
   `Params.henv`). I checked several: they are *forced*, not gratuitous — e.g. `substEq'`
   needs it because its `bvar` case strengthens the substitution's component judgment at
   `Strong.lean:1052`, and the inversion lemmas need it because they go through
   `IsDefEq.strong`.

6. **In `ChurchRosser.lean`, 9 lines total**: the class field `Params.pat_env` (30–32) and the
   `pat` case of `IsDefEq.church_rosser` (1390–1394), which converts the constructor's
   `Realizes` witness to a `Check.OK` via `Realizes.toOK` and takes a single `ParRed.extra`
   step. Minimal and exactly parallel to the existing `extra` case. `pat_env` is discharged by
   `pat_env := id` in `VEnv.toParams` (InductiveParams.lean:408), so it costs the only
   instance nothing.

## Candid assessment

**Design**: good. The two central decisions — annotate the strong rule with the reduct's
typing, and isolate the resulting obligation as a per-rule predicate `PatStrong` — are the
right ones, and both are defended in docstrings that a reviewer can check. Nothing is
over-hypothesised that I could find: I looked for hypotheses that could be weakened and
found none (`PatStrong`'s five premises are all consumed at the use site, `Strong.lean:747`).
Nothing is dead: `OnTypes.addPat`, `EnvStrong.mono`, `EnvStrong.of_hasType`, `PatsStrongOn`
all have real consumers in `EnvLemmas.lean`.

**Documentation**: unusually thorough for this codebase — every new declaration has a
docstring, and they explain *why* rather than restating the statement. Two blemishes: the
`Params.pat_env` docstring (`ChurchRosser.lean:30`) justifies the field by `extra_pat`, but
the two fields are independent (`extra_pat` is about `env.defeqs`, `pat_env` about
`env.pats`); and the density of cross-references means a reader must hold four files in their
head at once.

**The cost, and it is large**: on master, `IsDefEq.strong` needed only `Ordered env`, and
`Ordered.strong` was *proved*. On the iota branch it needs `OrderedStrong env`, which is
obtainable from `VEnv.WF` only through `VEnv.WF.orderedStrong` (EnvLemmas.lean:339), whose
`patsStrong` component is `sorry` (EnvLemmas.lean:334). Consequently everything in this group
that goes through the strong system — *all* of `UniqueTyping.lean`, the inversion lemmas
`HasType.app_inv`/`lam_inv`/`const_inv`/`bvar_inv`, `substDF`, and through them essentially
all of `ChurchRosser.lean` and `HeadReduction.lean` — became sorry-dependent. Note that
`UniqueTyping.lean` is byte-identical to master yet changed status, because two `CoeOut`
instances (`Strong.lean:684`, `EnvLemmas.lean:343`) make the new hypothesis invisible at use
sites. This is honest work — the author wrote `-- Every use of the strong system is therefore
conditional on VEnv.WF.patsStrong` at EnvLemmas.lean:342 — and it is unavoidable once ι is a
rule of `IsDefEq`; but any claim about what the branch proves must be stated modulo
`patsStrong`.

**Pre-existing gaps that limit what any of this is worth today** (all master's, not the
contributor's): `NormalEq.parRed` has two `sorry`s (`ChurchRosser.lean:1193, 1212`), both in
the case where an ι/`extra` step meets a `constDF`/`appDF` normal equality — precisely the
thesis' `thm:gg_compat` — so Church–Rosser, `CRDefEq.trans`, `reduce_sort`, `reduce_forallE`
and `InferType.exists` are all unproved. `IsDefEqU.weakN_iff` (`UniqueTyping.lean:174`) is
`sorry` and is used pervasively. And the `Params` class has exactly one instance
(`VEnv.toParams`), whose `DefEqsAsPats` hypothesis fails as soon as the environment contains a
`def` or the quotient rule — so the confluence development, as instantiated today, covers only
environments built from axioms and inductives. A blueprint should say so; the information is
currently buried in a docstring at `InductiveParams.lean:351–377`.

**Statements**: I believe they are the right ones. `PatStrong` is stated per rule rather than
per environment (so it can be discharged rule by rule); `PatsStrongOn` is stated for one
environment while the EnvLemmas-side `VEnv.PatsStrong` quantifies over the prefixes and
constant-only extensions traversed by the strengthening induction — the split is deliberate
and documented (`EnvLemmas.lean:125–132`), though it does mean the deferred obligation is
heavier than "ι rules preserve types in the final environment". One minor soft spot:
`Pattern.Check.Realizes` constrains only the two term components of each check triple, leaving
the type component free, so a rule instance does not determine its `chk`; harmless, but worth
knowing.
