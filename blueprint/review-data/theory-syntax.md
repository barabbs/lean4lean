# Group `theory-syntax` — core syntax of the idealised type theory

Files: `Lean4Lean/Theory.lean`, `Theory/VLevel.lean`, `Theory/VExpr.lean`, `Theory/VDecl.lean`,
`Theory/VEnv.lean`, `Theory/Quot.lean`, `Theory/LevelSat.lean`, `Theory/Meta.lean`
(2 235 lines; 1 786 master, 254 iota, 195 trproj).

## What the files do

This group is the *object language* of the whole verification: everything else in
`Lean4Lean/Theory/` and `Lean4Lean/Verify/` is stated about the objects defined here.

**`VLevel.lean` (188 lines, untouched master).** Universe levels as
`zero | succ | max | imax | param i` — the thesis grammar of `axioms.tex §2.1`, with universe
*variables represented by de Bruijn-style indices* rather than names. `WF n` bounds the
parameter indices, `eval : List Nat → Nat` gives the semantics, and `≤`/`≈` are defined
*semantically* (pointwise over all assignments) rather than by a proof system — a deliberate
simplification over the kernel's syntactic `Level.isEquiv`, and the reason `LevelSat.lean` can
talk about the complexity of the latter. `inst`/`params` implement the thesis's
$\alpha[\bar\ell/\bar u]$, and `ofLevel` is the partial bridge from real `Lean.Level`.

**`VExpr.lean` (1 334 lines; 939 master / 200 iota / 195 trproj).** The expression syntax —
`bvar | sort | const | app | lam | forallE`, i.e. `axioms.tex §2.1` plus the constants of §2.4 —
and then, for 900 lines, the substitution calculus: `liftN`, `ClosedN`, `instL`, `inst`, `insts`,
`unliftN`/`Skips` (inverting a lift), the `Lift` renaming algebra with `lift'`, and the general
`Subst` monoid with `subst`/`Subst.comp`. Note what is *absent*: no `let` and no `proj`. Both are
eliminated at translation time by `Theory/Meta.lean` (`:12` expands projections through `casesOn`,
`:45` substitutes `let`), which is exactly why the trproj contribution has to model kernel
projections as a separate reduction relation in `Theory/Proj.lean` instead of as syntax.

**`VDecl.lean` (67 lines; 29 master / 38 iota).** Declaration payloads. The iota branch added
`VRecRule` (`:20`), `VRecursor` (`:35`), `getMajorIdx`/`getFirstIndexIdx` (`:46`, `:51`) and the
`recs` field of `VInductDecl` (`:58`) — i.e. recursors and their ι rules became *data* in the
model, mirroring `Lean.RecursorVal`/`Lean.RecursorRule` field for field.

**`VEnv.lean` (57 lines; 42 master / 15 iota).** Environments as three predicates: constants,
definitional-equality axioms, and — the iota addition — `pats`, a dependent registry of schematic
reduction rules keyed by a `Pattern` (`:21`), with `addPat` (`:44`) and the extra `VEnv.LE.pats`
clause (`:50`).

**`Quot.lean`, `Meta.lean`, `LevelSat.lean` (583 lines, all untouched master).** The quotient
axioms; the `Lean.Expr → VExpr` translator and the `vexpr(…)`/`vconst(…)`/`vdefeq(…)` macros; and
a self-contained original result with no thesis counterpart — a linear-size reduction from CNF SAT
to `VLevel` equivalence, proving `Level.isEquiv`/`Level.geq` coNP-hard
(`LevelSat.lean:331`, `:382`, size bound `:419`).

## Thesis correspondence

| Here | Thesis |
|---|---|
| `VLevel` | `axioms.tex §2.1`, level grammar |
| `VExpr` | `axioms.tex §2.1` expression grammar + §2.4 constants |
| `liftN`/`inst` algebra | `typesys.tex` Lemma `thm:weak` (Weakening), Lemma `thm:subst` (Properties of substitution) — the *syntactic substrate* of those lemmas |
| `VConstant`, `VDefEq`, `VDefVal.toDefEq` | `axioms.tex §2.4` (definitions, δ) |
| `VInductiveType`, `VInductDecl` | `axioms.tex §2.6.1` ($\mu t{:}F.\,K$) |
| `VRecursor`, `RecHeaded`, `motiveFormer?` | `axioms.tex §2.6.3` (the recursor, $\kappa$, $\varepsilon$, $\delta$) |
| `VRecRule`, `VEnv.addPat` | `axioms.tex §2.6.4` (`sec:iota`) — the constructor ι rule only |
| `Quot.lean` | `axioms.tex §2.7.1` |
| `LevelSat.lean` | **no counterpart** — original |

Two honest gaps against the thesis, both at `VDecl.lean`: `VRecursor.k` (`:41`) records the
K-like-reduction flag but the thesis's *second* ι rule is not modelled (the docstring says so);
and the quotient computation rule is still a `VDefEq` (`Quot.lean:11`) rather than a `pats` entry,
so the model now has two mechanisms for computation rules.

## Assessment of the contributed parts

### iota (254 lines here)

The iota work in this group is **specification design, and it is good**. Three judgements:

1. *`VEnv.pats` is the right abstraction.* Making reduction rules a `Prop`-valued, `Pattern`-indexed
   family (`VEnv.lean:21`) rather than a fixed clause of the reduction relation keeps environments
   extensible and monotone, and it matches exactly how master already treats `defeqs`. The
   extension of `VEnv.LE` (`:50`, `:54`, `:57`) with the third clause was done uniformly and is
   two lines of proof — the monotonicity backbone absorbs the new field without ceremony.
2. *`VRecRule.ctorParams` is a genuinely thoughtful field.* It does not exist in
   `Lean.RecursorRule`, and the docstring (`VDecl.lean:22-26`) explains precisely why it must:
   for a nested inductive the constructor a rule fires on need not have the recursor's parameter
   count (`Tree.rec_1` on `List.cons`). The current `VInductDecl.WF` only admits direct blocks
   where the two coincide, so the field is currently redundant *as data* but necessary *as
   specification* — and the docstring says so rather than pretending otherwise. This is the kind
   of thing a reviewer should count in the contribution's favour.
3. *The syntactic helpers (`VExpr.lean:1044-1334`) are well factored.* `mkApps`/`getAppFn`/
   `getAppArgs`/`piBinders`/`headConst?`/`motiveFormer?` are total functions, and the shape
   predicates `RecHeaded` (`:1219`) / `CtorHeaded` (`:1223`) are cheap existentials over spine
   heads with the one load-bearing consequence `RecHeaded.not_ctorHeaded` (`:1227`) — the lemma
   that rules out an ι redex whose head is both recursor and constructor
   (`Typing/InductiveParams.lean:147`). The `eq_mkApps_append_iff` / `eq_const_mkApps_append_iff`
   biconditionals (`:1174`, `:1319`) are exactly the right statements: quantifier-free right-hand
   sides, which is what makes the WF predicates decidable and hence testable against the real
   kernel (`Tests/ShapeDecide.lean`).

Smells: `VRecursor.getFirstIndexIdx` (`VDecl.lean:51`) is never used; `VExpr.const_mkApps_spine`
(`:1295`) bundles two facts into a conjunction only ever consumed as `.1`/`.2` and, with
`eq_const_mkApps_of_spine`, has no consumer outside the file; the section docstring at `:1046`
still claims "with their decidability" after the instances were moved to `Tests/ShapeDecide.lean`;
and `VEnv.addPat` (`VEnv.lean:44`) is total where `addConst` is partial, with no comment saying
that conflicting rules are ruled out only downstream.

### trproj (195 lines here)

The trproj work in this group is **supporting infrastructure, and it is more uneven**.

The strong part is the design statement at `VExpr.lean:963-971`: since `lift'` and `inst` are both
`subst` (`lift'_eq_subst` `:970`, master's `instN_eq`), a builder lemma need only be proved once
against `subst` and the weakening/instantiation forms read off. That is the right idea, it is
written down as a section docstring, and it pays off immediately — `mkApps_subst` (`:1059`) is one
induction from which `mkApps_lift'` and `mkApps_inst` are three-line corollaries (`:1065`, `:1069`).
`Subst.liftN_lift_l_id` (`:984`) is the lemma that makes `Lift.consN` and `Subst.liftN` line up
binder-for-binder, and `subst_instN` (`:1009`) / `lift'_instN_hi` (`:1014`) are the general forms
the projection development actually needs. `piBinders_inst_of_ctorHeaded` (`:1262`) is a nice
observation: `lift'` and `instL` cannot create new leading Π-binders but `inst` can, so the `inst`
version genuinely needs the `CtorHeaded` hypothesis.

But the block has more slack than the iota block:

* **It orphaned upstream code.** Master proved `lift'_inst_hi` at `master:VExpr.lean:903` in one
  line from `lift_r_one`. trproj moved the lemma 115 lines down (`:1018`) and re-derived it from
  the new `lift'_instN_hi`. The result: `lift_r_one` (`:919`) now has *no consumer at all*, and
  `Subst.lift_r_comm` (`:911`), `Subst.trunc` (`:908`) and `Subst.Depth.one` (`:885`) survive only
  by feeding it. Neither deleting them nor keeping master's proof was done. On a file otherwise
  shared verbatim with upstream this also maximises rebase friction.
* **Redundancy left half-resolved.** `subst_instN` (`:1009`) subsumes master's `subst_inst`
  (`:952`) at `n = 0`; `liftN_subst_liftN` (`:1032`) subsumes master's `lift_subst_lift` (`:947`)
  at `i = 0` — its own docstring says so — yet both master lemmas keep independent hand proofs.
  Contrast `lift'_inst_hi`, which *was* re-derived. Three analogous pairs, three different
  treatments.
* **Dead lemmas.** `Lift.liftVar_consN_lt` (`:753`), `Lift.liftVar_consN_succ` (`:756`) and
  (through them) `Lift.consN_fixes` (`:745`) have no consumer; of the four-lemma block at
  `744-758` only `consN_cons` is used. `VExpr.lamBinders_length` (`:1137`) fires only on itself.
  `CtorHeaded.instL` (`:1256`) and `getAppFn_instL_const` (`:1248`) are unused symmetry additions.
* **One documentation defect.** `CtorHeaded.forallE` (`:1232`) is `:= h` (definitionally trivial),
  unused, and its docstring states a *different* proposition than the lemma — it reads as the
  justification for `piArity_inst_of_ctorHeaded`, which lives 40 lines below.

### Overall

Documentation quality across both branches is well above the surrounding master code: almost every
contributed declaration carries a docstring that explains *why* the statement has the shape it has,
and several (e.g. `VDecl.lean:22-26`, `VExpr.lean:963-967`) explain a design decision rather than
restating the type. Nothing in this group is `sorry`-dependent — every contributed declaration here
is a definition or a fully proved lemma. The statements are, with the exceptions listed above, the
right ones: total readers rather than partial ones, quantifier-free biconditionals where
decidability is wanted, and general (`n`-indexed) forms where the projection development needs
them. The main criticism is hygiene: roughly ten contributed declarations in this group have no
consumer, and one trproj refactor left four upstream declarations dead without removing them.
