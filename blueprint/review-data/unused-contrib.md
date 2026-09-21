# Unused / dead-declaration census of the contributed code

> **Recovery note (this pass).** This report was regenerated from the recovered generator
> pipeline (`work/final.py` → `work/mkout.py` → `work/writemd.py`) after a `/tmp` wipe. Two
> deviations from the original run, below §1's own methodology text (which is the
> generators' original hardcoded narrative and was left untouched):
> 1. **Bug fix (not a logic change), applied to make the scripts run at all:** `mkout.py` and
>    `writemd.py` unpacked `r["other_list"]` as 3-tuples (`for a,b,_ in ...`); `final.py`
>    (as recovered) populates that field with 2-tuples `(file, line)` from the namespace-aware
>    `Resolver`. Both call sites were changed to 2-tuple unpacking; no filtering, resolution or
>    counting logic was touched.
> 2. **Count differences, larger than "small," traced to `decls.tsv`'s regenerated `kind`
>    column.** This run: **889 contributed declarations (565 iota, 324 trproj)**, of which
>    **78** have zero resolved references, vs. the original **875 (553/322)** and **31**.
>    The gap is not random noise: the regenerated `decls.tsv` records every user-written
>    `instance` (e.g. the `Decidable`/`Coe` instances in `Tests/ShapeDecide.lean`,
>    `Theory/Typing/{EnvLemmas,Strong}.lean`, `Verify/LocalContext.lean`) with `kind=def`
>    rather than `kind=instance`. `final.py`'s population filter (`kind in
>    {"ctor","instance","rec"}` → skip) therefore no longer excludes them, and since
>    typeclass-resolved instances are by construction never named at their call sites, they
>    show up as spurious zero-reference "dead" declarations. **28 of the 78** zero-reference
>    entries in §2 are such instances (all 24 in `Tests/ShapeDecide.lean`, plus
>    `instCoeOutWFOrderedStrong`, `VEnv.instCoeOutOrderedStrongOrdered`,
>    `Tests.IotaShape.instDecidableRuleShapeAt`,
>    `Lean.LocalContext.instDecidableEqFVarId_lean4Lean`) — almost certainly false positives
>    of the same kind §1's own text already flags for `@[simp]` lemmas, not genuine dead code.
>    A further **19** entries in §2 are new relative to the original 31 (small helper `def`s/
>    `inductive`s local to already-flagged-dead test clusters — `badCtorType`, `goodCtorType`,
>    `TwoCtorProp.declB`, `Tests.ProjShape.Refl`, `ProjInhabit.{Plain,Dependent}.env0?` — plus
>    six theory lemmas/defs — `VExpr.{CtorResult_iff,MajorApp_iff,ValidIndApp_iff,
>    const_mkApps_spine,headConst?_eq_some,decClosedN}` — and the six `AddQuotAux` locals
>    `ng0,L1..L5`). Per the original methodology's own §"Manual verification" step, these would
>    need individual `grep -w` confirmation before being asserted as dead; **that manual
>    re-verification was not redone in this recovery pass** (out of scope for a mechanical
>    rerun) — treat the 19 as provisional, not confirmed. The **31 original zero-reference
>    findings** (§2's `one_le_numMotives`, the seven `VInductDecl.WF` fields, `TrEnv.proj_defeq`'s
>    only-tests status in §3, etc.) all reproduce unchanged in this run. No generator filtering
>    logic was modified to compensate for the `kind` regression; per task instructions this
>    report reflects the unmodified (bug-fixed-only) generator output, with the discrepancy
>    documented here rather than silently absorbed.
>
> Everything below this note is the generator's own output, unedited.

Repo root, branch `trproj`, HEAD `20ec229`; master = `8223d22`.
Read-only analysis; no build was run. All line numbers are working-tree lines.

## 1. Method

**Population.** Every declaration in `decls.tsv` whose module file has a blame file in
`scratchpad/blame/` and whose declaration line is tagged `I` (iota) or `P` (trproj-only).
Kinds `ctor`, `instance` and `rec` are skipped per the brief. I additionally dropped
declarations Lean generates rather than the author writing them — `Foo.below_N`,
`Foo.brecOn_N`, `Foo.ctorElim` (31 of them, all in `Tests/IotaShape.lean`), and the
`decEq` functions of two `deriving instance DecidableEq` lines in `Tests/ShapeDecide.lean`.
That leaves **875 author-written contributed declarations** (553 iota, 322 trproj).

**Body ranges.** A declaration's own body runs from its doc-comment/attribute block
(walked backwards from the recorded line) to the line before the next top-level command.
Top-level commands are detected as column-0 lines outside block comments that are not
continuations (`|`, `where`, `deriving`, closing brackets, …). This matters: using
"next entry in `decls.tsv`" as the body end — the approximation the brief suggests —
swallows following `example` / `#guard` / `run_meta` blocks and produced 8 false
"dead" verdicts (e.g. `Tests.ProjShape.P₀`, used by four `example`s; `Tests.ProjShape.checkProj`,
called eleven times from a `run_meta do`).

**Reference counting.** A plain word-boundary grep on the last name component is not
sound in this repo — `Lean4Lean/Experimental/SExpr.lean` is a parallel copy of the
`VExpr` substitution theory and duplicates dozens of names (`lift_r_one`, `Subst.trunc`,
`lift'_inst_hi`, …), and short components (`wf`, `shape`, `one`, `le`, `k`, `rec_find`)
collide across namespaces. I therefore resolved references by name rather than by token:
every dotted identifier on every code line is resolved against the enclosing
`namespace` stack, the `open`s in effect, and the import closure (a reference can only
target a declaration whose file the referencing file transitively imports); every
prefix of a dotted identifier is resolved too, so `badCtorType.CtorPositive` counts as a
reference to `badCtorType` *and* to `CtorPositive`. When no exact resolution exists
— generalised field notation (`h.ctor_find`) and anonymous-constructor dots (`.trLiteral`)
— the reference is attributed by namespace proximity, which is a heuristic.
String literals and comments are masked out of the code index and counted separately.

**Manual verification.** Every candidate with zero references was checked by hand with
`grep -w` over `Lean4Lean/` and `Main.lean`; so were all 92 declarations with 1–3
references whose component is short or shared. Four automatic zeros were false
positives from the proximity heuristic and were removed (see §6), and four more were
`macro`/`notation`-generated names whose *syntax* is used. The surviving list is the
hand-verified one.

**Caveats.** (a) `@[simp]` lemmas can be used by `simp` with no textual reference; four
of the dead lemmas are `@[simp]` and are flagged. (b) Structure fields can be consumed
by anonymous-constructor syntax without naming the field; ten of the dead entries are
fields and are flagged. (c) The proximity heuristic can still credit a reference to the
wrong member of a same-named pair, so a handful of declarations counted as "used" may
not be; I checked every low-count case but cannot rule this out for high-count ones.

## 2. Contributed declarations with zero real references (78)

| # | declaration | file:line | branch | kind | docstring / statement | notes |
|---|---|---|---|---|---|---|
| 1 | `Lean4Lean.Tests.IotaShape.instDecidableRuleShapeAt` | `Lean4Lean/Tests/IotaShape.lean:63` | iota | def | `instance {ty rhs np nm nmin nf c} : Decidable (ruleShapeAt ty rhs np nm nmin nf c) := by` | in Tests/ |
| 2 | `Lean4Lean.Tests.IotaShape.matchPat_sound` | `Lean4Lean/Tests/IotaShape.lean:115` | iota | thm | `theorem matchPat_sound : ∀ {p : Pattern} {e m1 m2},` | in Tests/; mentioned in 1 comment/doc line(s) (approx) |
| 3 | `Lean4Lean.Tests.IotaShape.Dep.v` | `Lean4Lean/Tests/IotaShape.lean:365` | iota | def | `v : Fin n` | structure field, never projected; in Tests/ |
| 4 | `Lean4Lean.Tests.IotaShape.badCtorType` | `Lean4Lean/Tests/IotaShape.lean:397` | iota | def | A non-positive constructor `(Bad → False) → Bad`. | in Tests/ |
| 5 | `Lean4Lean.Tests.IotaShape.goodCtorType` | `Lean4Lean/Tests/IotaShape.lean:401` | iota | def | A strictly positive constructor of the same type former, `(Nat → Bad) → Bad`. | in Tests/ |
| 6 | `Lean4Lean.Tests.IotaShape.badCtorType_not_positive` | `Lean4Lean/Tests/IotaShape.lean:404` | iota | thm | `theorem badCtorType_not_positive : ¬ badCtorType.CtorPositive [`Bad] 0 := by decide` | in Tests/ |
| 7 | `Lean4Lean.Tests.IotaShape.goodCtorType_positive` | `Lean4Lean/Tests/IotaShape.lean:405` | iota | thm | `theorem goodCtorType_positive : goodCtorType.CtorPositive [`Bad] 0 := by decide` | in Tests/ |
| 8 | `Lean4Lean.Tests.IotaShape.TwoCtorProp.declB` | `Lean4Lean/Tests/IotaShape.lean:439` | iota | def | `def declB : VInductDecl where` | in Tests/ |
| 9 | `Lean4Lean.Tests.IotaShape.TwoCtorProp.declB_wants_large` | `Lean4Lean/Tests/IotaShape.lean:446` | iota | thm | The recursor asks for large elimination. | in Tests/ |
| 10 | `Lean4Lean.Tests.IotaShape.TwoCtorProp.declB_not_largeElimShape` | `Lean4Lean/Tests/IotaShape.lean:450` | iota | thm | The syntactic half of `VInductDecl.LargeElim` refuses it: | in Tests/ |
| 11 | `Lean4Lean.Tests.ProjInhabit.Plain.env0?` | `Lean4Lean/Tests/ProjInhabit.lean:49` | trproj | def | `def env0? : Option VEnv := VEnv.empty.addConst `A ⟨0, .sort l1⟩ \|>.bind fun e => e.addIndu` | in Tests/ |
| 12 | `Lean4Lean.Tests.ProjInhabit.Plain.trProj0` | `Lean4Lean/Tests/ProjInhabit.lean:172` | trproj | thm | `theorem trProj0 : TrProj env 0 [Sc] `S 0 (.bvar 0) (.app (.app (.app recC M0) sel0) (.bvar` | in Tests/ |
| 13 | `Lean4Lean.Tests.ProjInhabit.Dependent.env0?` | `Lean4Lean/Tests/ProjInhabit.lean:207` | trproj | def | `def env0? : Option VEnv :=` | in Tests/ |
| 14 | `Lean4Lean.Tests.ProjInhabit.Dependent.trProjDep1` | `Lean4Lean/Tests/ProjInhabit.lean:557` | trproj | thm | `theorem trProjDep1 : TrProj env 0 [S2c] `S2 1 (.bvar 0) (.app P1' (.bvar 0)) :=` | in Tests/ |
| 15 | `Lean4Lean.Tests.ProjShape.V3.h` | `Lean4Lean/Tests/ProjShape.lean:36` | trproj | thm | `h : v.val < n` | structure field, never projected; in Tests/ |
| 16 | `Lean4Lean.Tests.ProjShape.Refl` | `Lean4Lean/Tests/ProjShape.lean:39` | trproj | inductive | Reflexive: | in Tests/ |
| 17 | `Lean4Lean.Tests.ProjShape.Refl.next` | `Lean4Lean/Tests/ProjShape.lean:40` | trproj | def | `next : Nat → Refl` | structure field, never projected; in Tests/ |
| 18 | `Lean4Lean.instDecidableEqVLevel` | `Lean4Lean/Tests/ShapeDecide.lean:15` | iota | def | `deriving instance DecidableEq for VLevel` | in Tests/ |
| 19 | `Lean4Lean.instDecidableEqVExpr` | `Lean4Lean/Tests/ShapeDecide.lean:16` | iota | def | `deriving instance DecidableEq for VExpr` | in Tests/ |
| 20 | `Lean4Lean.VExpr.instDecidableExistsListEqMkAppsHAppend` | `Lean4Lean/Tests/ShapeDecide.lean:20` | iota | def | `instance {e f : VExpr} {pre : List VExpr} : Decidable (∃ rest, e = f.mkApps (pre ++ rest))` | in Tests/ |
| 21 | `Lean4Lean.VExpr.instDecidableExistsListAndEqNatMkAppsHAppend` | `Lean4Lean/Tests/ShapeDecide.lean:23` | iota | def | `instance {e f : VExpr} {pre : List VExpr} {n : Nat} :` | in Tests/ |
| 22 | `Lean4Lean.VExpr.instDecidableExistsAndEqOptionSomeOfDecidablePred` | `Lean4Lean/Tests/ShapeDecide.lean:27` | iota | def | `instance {α : Type _} {o : Option α} {P : α → Prop} [DecidablePred P] :` | in Tests/ |
| 23 | `Lean4Lean.VExpr.instDecidableExistsVLevelEqSort` | `Lean4Lean/Tests/ShapeDecide.lean:34` | trproj | def | `instance {e : VExpr} : Decidable (∃ u, e = .sort u) := decidable_of_iff _ isSort_iff` | in Tests/ |
| 24 | `Lean4Lean.VExpr.instDecidableExistsNatEqBvar` | `Lean4Lean/Tests/ShapeDecide.lean:35` | trproj | def | `instance {e : VExpr} : Decidable (∃ k, e = .bvar k) := decidable_of_iff _ isBvar_iff` | in Tests/ |
| 25 | `Lean4Lean.VExpr.instDecidableExistsNameListVLevelEqConst` | `Lean4Lean/Tests/ShapeDecide.lean:36` | trproj | def | `instance {e : VExpr} : Decidable (∃ I us, e = .const I us) := decidable_of_iff _ isConst_i` | in Tests/ |
| 26 | `Lean4Lean.VExpr.instDecidableRecHeaded` | `Lean4Lean/Tests/ShapeDecide.lean:38` | trproj | def | `instance {ty : VExpr} : Decidable ty.RecHeaded := decidable_of_iff _ isBvar_iff` | in Tests/ |
| 27 | `Lean4Lean.VExpr.instDecidableCtorHeaded` | `Lean4Lean/Tests/ShapeDecide.lean:39` | trproj | def | `instance {ty : VExpr} : Decidable ty.CtorHeaded := decidable_of_iff _ isConst_iff` | in Tests/ |
| 28 | `Lean4Lean.VExpr.instDecidableMentionsConst` | `Lean4Lean/Tests/ShapeDecide.lean:41` | iota | def | `instance {cs : List Name} {e : VExpr} : Decidable (e.MentionsConst cs) :=` | in Tests/ |
| 29 | `Lean4Lean.VExpr.instDecidableCtorResult` | `Lean4Lean/Tests/ShapeDecide.lean:44` | iota | def | `instance {ty : VExpr} {T : Name} {np nf nind : Nat} : Decidable (ty.CtorResult T np nf nin` | in Tests/ |
| 30 | `Lean4Lean.VExpr.instDecidableMajorApp` | `Lean4Lean/Tests/ShapeDecide.lean:47` | iota | def | `instance {A : VExpr} {T : Name} {np nm nmin nind : Nat} :` | in Tests/ |
| 31 | `Lean4Lean.VExpr.instDecidableValidIndApp` | `Lean4Lean/Tests/ShapeDecide.lean:50` | iota | def | `instance {fs : List Name} {np d : Nat} {e : VExpr} : Decidable (e.ValidIndApp fs np d) :=` | in Tests/ |
| 32 | `Lean4Lean.VExpr.instDecidableFieldPositive` | `Lean4Lean/Tests/ShapeDecide.lean:53` | iota | def | `instance {fs : List Name} {np d : Nat} {ty : VExpr} : Decidable (ty.FieldPositive fs np d)` | in Tests/ |
| 33 | `Lean4Lean.VExpr.instDecidableCtorPositive` | `Lean4Lean/Tests/ShapeDecide.lean:56` | iota | def | `instance {fs : List Name} {np : Nat} {ty : VExpr} : Decidable (ty.CtorPositive fs np) := b` | in Tests/ |
| 34 | `Lean4Lean.VExpr.instDecidableFieldInIndices` | `Lean4Lean/Tests/ShapeDecide.lean:59` | iota | def | `instance {ty : VExpr} {np i : Nat} : Decidable (ty.FieldInIndices np i) := by` | in Tests/ |
| 35 | `Lean4Lean.VExpr.instDecidableMotiveShape` | `Lean4Lean/Tests/ShapeDecide.lean:62` | iota | def | `instance {A : VExpr} : Decidable A.MotiveShape := by unfold MotiveShape; infer_instance` | in Tests/ |
| 36 | `Lean4Lean.VExpr.instDecidableMinorHeaded` | `Lean4Lean/Tests/ShapeDecide.lean:63` | iota | def | `instance {A : VExpr} {i nm : Nat} : Decidable (A.MinorHeaded i nm) := by` | in Tests/ |
| 37 | `Lean4Lean.VExpr.instDecidableMinorFor` | `Lean4Lean/Tests/ShapeDecide.lean:65` | iota | def | `instance {A : VExpr} {c : Name} : Decidable (A.MinorFor c) := by` | in Tests/ |
| 38 | `Lean4Lean.VExpr.instDecidableRecShape` | `Lean4Lean/Tests/ShapeDecide.lean:67` | iota | def | `instance {ty : VExpr} {np nm nmin nind : Nat} : Decidable (ty.RecShape np nm nmin nind) :=` | in Tests/ |
| 39 | `Lean4Lean.VExpr.instDecidableCtorShape` | `Lean4Lean/Tests/ShapeDecide.lean:69` | iota | def | `instance {ty : VExpr} {arity : Nat} : Decidable (ty.CtorShape arity) := by` | in Tests/ |
| 40 | `Lean4Lean.VExpr.instDecidableRuleShape` | `Lean4Lean/Tests/ShapeDecide.lean:71` | iota | def | `instance {rhs : VExpr} {np nm nmin nf nrec j : Nat} :` | in Tests/ |
| 41 | `Lean4Lean.instDecidableLargeElimShape` | `Lean4Lean/Tests/ShapeDecide.lean:77` | iota | def | `instance {decl : VInductDecl} : Decidable decl.LargeElimShape := by` | in Tests/ |
| 42 | `Lean4Lean.VExpr.CtorResult_iff` | `Lean4Lean/Theory/Inductive.lean:48` | iota | thm | `theorem CtorResult_iff {ty : VExpr} {T : Name} {np nf nind : Nat} :` |  |
| 43 | `Lean4Lean.VExpr.MajorApp_iff` | `Lean4Lean/Theory/Inductive.lean:66` | iota | thm | `theorem MajorApp_iff {A : VExpr} {T : Name} {np nm nmin nind : Nat} :` |  |
| 44 | `Lean4Lean.VExpr.ValidIndApp_iff` | `Lean4Lean/Theory/Inductive.lean:79` | iota | thm | `theorem ValidIndApp_iff {fs : List Name} {np d : Nat} {e : VExpr} :` |  |
| 45 | `Lean4Lean.VExpr.RecShape.one_le_numMotives` | `Lean4Lean/Theory/Inductive.lean:196` | iota | thm | A recursor type has at least one motive. |  |
| 46 | `Lean4Lean.VExpr.RecShape.majorFormer?_eq` | `Lean4Lean/Theory/Inductive.lean:202` | iota | thm | The type former a `RecShape` recursor eliminates: |  |
| 47 | `Lean4Lean.VInductDecl.LargeElim.shape` | `Lean4Lean/Theory/Inductive.lean:242` | iota | thm | A block whose result sort can be `Prop` eliminates largely only in the shape `LargeElimShape` allows. | mentioned in 45 comment/doc line(s) (approx) |
| 48 | `Lean4Lean.VInductDecl.WF.types_uvars` | `Lean4Lean/Theory/Inductive.lean:345` | iota | thm | Type formers share the declaration's universe parameters. | structure field, never projected |
| 49 | `Lean4Lean.VInductDecl.WF.ctors_uvars` | `Lean4Lean/Theory/Inductive.lean:347` | iota | thm | So do the constructors. | structure field, never projected |
| 50 | `Lean4Lean.VInductDecl.WF.universes` | `Lean4Lean/Theory/Inductive.lean:351` | iota | thm | §2.6.1–2.6.2: | structure field, never projected; mentioned in 6 comment/doc line(s) (approx) |
| 51 | `Lean4Lean.VInductDecl.WF.recs_elim` | `Lean4Lean/Theory/Inductive.lean:361` | iota | thm | §2.6.3, κ: | structure field, never projected; mentioned in 5 comment/doc line(s) (approx) |
| 52 | `Lean4Lean.VInductDecl.WF.ctors_params` | `Lean4Lean/Theory/Inductive.lean:367` | iota | thm | A constructor's parameter binders are its type former's. | structure field, never projected; mentioned in 2 comment/doc line(s) (approx) |
| 53 | `Lean4Lean.VInductDecl.WF.ctors_result` | `Lean4Lean/Theory/Inductive.lean:371` | iota | thm | §2.6.1: | structure field, never projected; mentioned in 2 comment/doc line(s) (approx) |
| 54 | `Lean4Lean.VInductDecl.WF.ctors_positive` | `Lean4Lean/Theory/Inductive.lean:374` | iota | thm | §2.6.1: | structure field, never projected; mentioned in 3 comment/doc line(s) (approx) |
| 55 | `Lean4Lean.VExpr.projMotiveBody_zero` | `Lean4Lean/Theory/Proj.lean:153` | trproj | thm | The motive of field `0` is the constant motive `fun _ => Fs[0]`. | @[simp] (reachable through simp sets); mentioned in 1 comment/doc line(s) (approx) |
| 56 | `Lean4Lean.VExpr.instFields_nil` | `Lean4Lean/Theory/Proj.lean:206` | trproj | thm | `` | @[simp] (reachable through simp sets) |
| 57 | `Lean4Lean.instCoeOutWFOrderedStrong` | `Lean4Lean/Theory/Typing/EnvLemmas.lean:343` | iota | def | `instance : CoeOut (VEnv.WF env) env.OrderedStrong := ⟨(·.orderedStrong)⟩` | uses sorry |
| 58 | `Lean4Lean.VEnv.WF'.pats_origin` | `Lean4Lean/Theory/Typing/InductiveParams.lean:93` | iota | thm | Origin of a registered pattern entry along a `WF'` chain: |  |
| 59 | `Lean4Lean.VEnv.IsDefEq.crDefEq_of_induct` | `Lean4Lean/Theory/Typing/InductiveParams.lean:426` | trproj | thm | Church–Rosser for such an environment: | uses sorry; mentioned in 1 comment/doc line(s) (approx) |
| 60 | `Lean4Lean.SimplePattern.iotaRHS_iotaCounts` | `Lean4Lean/Theory/Typing/Pattern.lean:675` | iota | thm | An ι reduct retains its template, the size `np + nm + nmin` of its recursor prefix and the field count `nf` — and nothing else of the telescope split. |  |
| 61 | `Lean4Lean.VEnv.instCoeOutOrderedStrongOrdered` | `Lean4Lean/Theory/Typing/Strong.lean:684` | iota | def | `instance : CoeOut (OrderedStrong env) env.Ordered := ⟨(·.ordered)⟩` |  |
| 62 | `Lean4Lean.VExpr.decClosedN` | `Lean4Lean/Theory/VExpr.lean:108` | iota | def | `instance decClosedN : ∀ (e : VExpr) (k : Nat), Decidable (e.ClosedN k)` |  |
| 63 | `Lean4Lean.Lift.liftVar_consN_lt` | `Lean4Lean/Theory/VExpr.lean:753` | trproj | thm | `theorem liftVar_consN_lt {ρ : Lift} {m i : Nat} (h : i < m) : (ρ.consN m).liftVar i = i :=` |  |
| 64 | `Lean4Lean.Lift.liftVar_consN_succ` | `Lean4Lean/Theory/VExpr.lean:756` | trproj | thm | `theorem liftVar_consN_succ (ρ : Lift) (m i : Nat) :` |  |
| 65 | `Lean4Lean.VExpr.lamBinders_length` | `Lean4Lean/Theory/VExpr.lean:1138` | trproj | thm | `\| .lam _ b => by simp [lamBinders, lamArity, lamBinders_length b]` | @[simp] (reachable through simp sets) |
| 66 | `Lean4Lean.VExpr.headConst?_eq_some` | `Lean4Lean/Theory/VExpr.lean:1289` | iota | thm | `e.headConst?` names `c` exactly when `e`'s spine head is the constant `c`. |  |
| 67 | `Lean4Lean.VExpr.const_mkApps_spine` | `Lean4Lean/Theory/VExpr.lean:1295` | iota | thm | The spine data of a constant application. |  |
| 68 | `Lean4Lean.insertConsts_find?_none` | `Lean4Lean/Verify/Environment/Basic.lean:165` | iota | thm | `theorem insertConsts_find?_none : ∀ {cis : List ConstantInfo} {C : ConstMap} {x}, C.map₂.W` |  |
| 69 | `Lean4Lean.AddInduct.mem_consts` | `Lean4Lean/Verify/Environment/Basic.lean:312` | iota | thm | Membership in the block's constants, by kind. |  |
| 70 | `Lean4Lean.AddQuotAux.ng0` | `Lean4Lean/Verify/Environment/Quot.lean:27` | iota | def | `abbrev ng0 : NameGenerator := {}` |  |
| 71 | `Lean4Lean.AddQuotAux.L1` | `Lean4Lean/Verify/Environment/Quot.lean:40` | iota | def | `abbrev L1 : LocalContext := ({} : LocalContext).mkLocalDecl x1 `α (.sort u) .implicit` |  |
| 72 | `Lean4Lean.AddQuotAux.L2'` | `Lean4Lean/Verify/Environment/Quot.lean:43` | iota | def | `abbrev L2' : LocalContext := L1.mkLocalDecl x2 `r αr .implicit` |  |
| 73 | `Lean4Lean.AddQuotAux.L3'` | `Lean4Lean/Verify/Environment/Quot.lean:44` | iota | def | `abbrev L3' : LocalContext := L2'.mkLocalDecl x3 `a (.fvar x1) .default` |  |
| 74 | `Lean4Lean.AddQuotAux.L4` | `Lean4Lean/Verify/Environment/Quot.lean:45` | iota | def | `abbrev L4 : LocalContext := L3'.mkLocalDecl x4 `β (.sort v) .implicit` |  |
| 75 | `Lean4Lean.AddQuotAux.L5` | `Lean4Lean/Verify/Environment/Quot.lean:46` | iota | def | `abbrev L5 : LocalContext := L4.mkLocalDecl x5 `f (.arrow (.fvar x1) (.fvar x4)) .default` |  |
| 76 | `Lean.Expr.getAppFn_mkAppList` | `Lean4Lean/Verify/Expr.lean:746` | trproj | thm | `\| [], _ => rfl` | @[simp] (reachable through simp sets) |
| 77 | `Lean.LocalContext.instDecidableEqFVarId_lean4Lean` | `Lean4Lean/Verify/LocalContext.lean:183` | iota | def | `instance : DecidableEq FVarId := fun ⟨a⟩ ⟨b⟩ =>` |  |
| 78 | `Lean4Lean.TypeChecker.Inner.inferProj.WF_struct` | `Lean4Lean/Verify/TypeChecker/InferType.lean:392` | trproj | thm | `inferProj.WF` for the structures the model covers (`TrProjCtor`): | uses sorry; mentioned in 1 comment/doc line(s) (approx) |

Grouping the same list by what it is:

- **Unused API lemmas in the theory (9):** `VExpr.RecShape.one_le_numMotives`,
  `VExpr.RecShape.majorFormer?_eq`, `VInductDecl.LargeElim.shape`, `VEnv.WF'.pats_origin`,
  `SimplePattern.iotaRHS_iotaCounts`, `Lift.liftVar_consN_lt`, `Lift.liftVar_consN_succ`,
  `VExpr.projMotiveBody_zero`, `VExpr.instFields_nil`. Each is proved and documented but
  nothing in the repo consumes it.
- **Unused `WF` fields (7 + 3):** seven fields of the iota `VInductDecl.WF` structure
  (`types_uvars`, `ctors_uvars`, `universes`, `recs_elim`, `ctors_params`, `ctors_result`,
  `ctors_positive`) are never projected anywhere; the last five are named only inside
  `throwError` strings and prose in `Tests/IotaShape.lean`. Plus three test-fixture
  structure fields (`Dep.v`, `V3.h`, `Refl.next`).
- **Unused infrastructure lemmas (3):** `insertConsts_find?_none`, `Lean.Expr.getAppFn_mkAppList`,
  `VExpr.lamBinders_length` — each referenced only by its own recursive proof.
- **Test assertions that nothing runs or reads (8):** `matchPat_sound`,
  `badCtorType_not_positive`, `goodCtorType_positive`, `declB_wants_large`,
  `declB_not_largeElimShape`, `trProj0`, `trProjDep1` — these are `theorem`s, so they are
  *checked* at build time (that is their point), but nothing consumes them; they are
  "dead" only in the reference sense, not useless.
- **Two open results (`sorry`):** `VEnv.IsDefEq.crDefEq_of_induct` and
  `TypeChecker.Inner.inferProj.WF_struct` are unfinished *and* unreferenced.

## 3. Contributed declarations used only from `Tests/` (6)

| declaration | file:line | branch | kind | only consumers | docstring |
|---|---|---|---|---|---|
| `Lean4Lean.VExpr.mentionsConst_iff` | `Lean4Lean/Theory/Inductive.lean:35` | iota | thm | `Lean4Lean/Tests/ShapeDecide.lean:42` |  |
| `Lean4Lean.VExpr.projTy` | `Lean4Lean/Theory/Proj.lean:127` | trproj | def | `Lean4Lean/Tests/ProjShape.lean:178`, `Lean4Lean/Tests/ProjShape.lean:179` | The type of `P_i e`, over `Γ`: |
| `Lean4Lean.VExpr.isSort_iff` | `Lean4Lean/Theory/VExpr.lean:1210` | iota | thm | `Lean4Lean/Tests/ShapeDecide.lean:34` |  |
| `Lean4Lean.VExpr.isBvar_iff` | `Lean4Lean/Theory/VExpr.lean:1211` | iota | thm | `Lean4Lean/Tests/ShapeDecide.lean:35`, `Lean4Lean/Tests/ShapeDecide.lean:38` |  |
| `Lean4Lean.VExpr.isConst_iff` | `Lean4Lean/Theory/VExpr.lean:1212` | iota | thm | `Lean4Lean/Tests/ShapeDecide.lean:36`, `Lean4Lean/Tests/ShapeDecide.lean:39` |  |
| `Lean4Lean.TrEnv.proj_defeq` | `Lean4Lean/Verify/Environment/Lemmas.lean:1021` | trproj | thm | `Lean4Lean/Tests/ProjInhabit.lean:595` | **Projection reduction.** The recursor expansion `e''` of the `i`-th projection of a structure value `d` reduces, when `d` is definitionally the satur |

Two of these are load-bearing for judging the contributions:

- `TrEnv.proj_defeq` (`Lean4Lean/Verify/Environment/Lemmas.lean:1021`) — the headline
  trproj result — has no consumer in the library at all. Its only mention outside its own
  proof is `#guard_msgs in #print axioms Lean4Lean.TrEnv.proj_defeq` in
  `Tests/ProjInhabit.lean:595`, i.e. an axiom-footprint assertion, not a use.
- `VExpr.projTy` (`Lean4Lean/Theory/Proj.lean:127`) is used only by two `example`s in
  `Tests/ProjShape.lean`; the four `*_iff` lemmas in `Theory/Inductive.lean` and
  `Theory/VExpr.lean` exist to build the `Decidable` instances in `Tests/ShapeDecide.lean`,
  which is a legitimate (if test-only) purpose.

**Referenced only from comments/docstrings.** Nine of the 31 dead declarations are
mentioned in prose but never in code: `WF.universes`, `WF.recs_elim`, `WF.ctors_params`,
`WF.ctors_result`, `WF.ctors_positive` (prose plus `throwError` strings in
`Tests/IotaShape.lean`), `matchPat_sound` (`IotaShape.lean:102`),
`VExpr.projMotiveBody_zero` (`Theory/Proj.lean:25`), `VEnv.IsDefEq.crDefEq_of_induct`
(`InductiveParams.lean:391`) and `inferProj.WF_struct` (`Tests/ProjInhabit.lean:15`,
`Verify/Typing/Expr.lean:125`, `InferType.lean:401`). The documentation therefore
advertises an interface the code never exercises.

## 4. Counts

| | iota | trproj | total |
|---|---|---|---|
| contributed declarations (author-written) | 565 | 324 | 889 |
| zero-reference | 58 | 20 | 78 |
| rate | 10.3% | 6.2% | 8.8% |

Split by location: non-`Tests/` code 37/630 (5.9%) dead;
`Tests/` code 41/259 (15.8%).

Per file (only files with contributed declarations; `dead` counts the table in §2):

| file | contributed | iota | trproj | dead |
|---|---|---|---|---|
| `Lean4Lean/Experimental/NormalEq.lean` | 1 | 1 | 0 | 0 |
| `Lean4Lean/Inductive/Reduce.lean` | 1 | 0 | 1 | 0 |
| `Lean4Lean/Std/Basic.lean` | 7 | 5 | 2 | 0 |
| `Lean4Lean/Std/SMap.lean` | 7 | 7 | 0 | 0 |
| `Lean4Lean/Tests/IotaShape.lean` | 69 | 69 | 0 | 10 |
| `Lean4Lean/Tests/ProjInhabit.lean` | 148 | 0 | 148 | 4 |
| `Lean4Lean/Tests/ProjShape.lean` | 18 | 0 | 18 | 3 |
| `Lean4Lean/Tests/ShapeDecide.lean` | 24 | 19 | 5 | 24 |
| `Lean4Lean/Theory/Inductive.lean` | 58 | 57 | 1 | 13 |
| `Lean4Lean/Theory/Proj.lean` | 48 | 0 | 48 | 2 |
| `Lean4Lean/Theory/Typing/Basic.lean` | 2 | 2 | 0 | 0 |
| `Lean4Lean/Theory/Typing/ChurchRosser.lean` | 1 | 1 | 0 | 0 |
| `Lean4Lean/Theory/Typing/Env.lean` | 2 | 2 | 0 | 0 |
| `Lean4Lean/Theory/Typing/EnvLemmas.lean` | 12 | 12 | 0 | 1 |
| `Lean4Lean/Theory/Typing/InductiveLemmas.lean` | 73 | 70 | 3 | 0 |
| `Lean4Lean/Theory/Typing/InductiveParams.lean` | 25 | 22 | 3 | 2 |
| `Lean4Lean/Theory/Typing/Lemmas.lean` | 7 | 7 | 0 | 0 |
| `Lean4Lean/Theory/Typing/Pattern.lean` | 44 | 41 | 3 | 1 |
| `Lean4Lean/Theory/Typing/QuotLemmas.lean` | 1 | 1 | 0 | 0 |
| `Lean4Lean/Theory/Typing/Strong.lean` | 14 | 14 | 0 | 1 |
| `Lean4Lean/Theory/VDecl.lean` | 17 | 17 | 0 | 0 |
| `Lean4Lean/Theory/VEnv.lean` | 4 | 4 | 0 | 0 |
| `Lean4Lean/Theory/VExpr.lean` | 67 | 33 | 34 | 6 |
| `Lean4Lean/Verify/Environment/Basic.lean` | 67 | 61 | 6 | 2 |
| `Lean4Lean/Verify/Environment/Lemmas.lean` | 37 | 10 | 27 | 0 |
| `Lean4Lean/Verify/Environment/Primitive/Basic.lean` | 2 | 2 | 0 | 0 |
| `Lean4Lean/Verify/Environment/Primitive/Condition.lean` | 1 | 1 | 0 | 0 |
| `Lean4Lean/Verify/Environment/Quot.lean` | 77 | 77 | 0 | 6 |
| `Lean4Lean/Verify/Expr.lean` | 3 | 0 | 3 | 1 |
| `Lean4Lean/Verify/LocalContext.lean` | 8 | 8 | 0 | 1 |
| `Lean4Lean/Verify/Primitive.lean` | 13 | 13 | 0 | 0 |
| `Lean4Lean/Verify/TypeChecker/InferType.lean` | 2 | 0 | 2 | 1 |
| `Lean4Lean/Verify/TypeChecker/WHNF.lean` | 1 | 0 | 1 | 0 |
| `Lean4Lean/Verify/Typing/Expr.lean` | 10 | 0 | 10 | 0 |
| `Lean4Lean/Verify/Typing/Lemmas.lean` | 17 | 8 | 9 | 0 |
| `Lean4Lean/Verify/Typing/TrTerm.lean` | 1 | 1 | 0 | 0 |

For scale, the same resolver run over the **master-side** declarations of the same tree
finds 383 of 3422 core (non-`Experimental`, non-`Tests`) declarations with no consumer
in the repo — 11.2%. Upstream lean4lean carries a much higher proportion of
consumer-less declarations than the contributions do (3.3% outside `Tests/`).

## 5. Master declarations orphaned by the branches

Method: for every master-side declaration with zero references in the working tree,
re-run the same namespace-aware resolution over a `git archive master` export and keep
those that *did* have a consumer there.

Exactly one declaration is orphaned outright, and it drags a five-declaration cluster
with it. On master, `Theory/VExpr.lean:903` proved `lift'_inst_hi` in one line from
`lift_r_one` (`:897`). trproj moved `lift'_inst_hi` 115 lines down (`:1018` in the working
tree) and re-derived it from the new `lift'_instN_hi` (`:1014`). The old chain is now
unreachable:

| declaration | worktree | master | status |
|---|---|---|---|
| `Lean4Lean.VExpr.lift_r_one` | `Theory/VExpr.lean:919` | `:897`, used at `:905` | **no consumer at all** |
| `Lean4Lean.VExpr.Subst.lift_r_comm` | `:911` | `:889` | used only inside `lift_r_one`'s proof |
| `Lean4Lean.VExpr.Subst.trunc` | `:908` | `:886` | used only by `lift_r_comm` and `lift_r_one` |
| `Lean4Lean.VExpr.Subst.Depth.one` | `:885` | `:863` | used only inside `lift_r_one`'s proof (`.one` at `:921`) |
| `Lean4Lean.VExpr.Subst.Depth.id` | `:858` | `:836` | used only by `Subst.Depth.one` |
| `Lean4Lean.VExpr.Subst.Depth` | `:796` | `:774` | used only at `:858`, `:885`, `:911` — all of the above |

So the refactor left six upstream declarations (~30 lines of `Theory/VExpr.lean`) with
no live consumer, without removing them. Note the duplicate copies of the same names in
`Lean4Lean/Experimental/SExpr.lean` are still live there and are *not* affected — a
word-boundary grep would wrongly report all six as still used.

Two further master declarations (`EquivManager.WF.empty` at `Verify/TypeChecker/Basic.lean:93`
and `InferCache.WF.empty` at `:234`) have no consumer in either tree; the apparent master
reference is a `| empty =>` case tag in `Verify/Environment/Extension.lean`, so they are
pre-existing upstream dead code, not collateral damage from the branches.

No master declaration was orphaned by the iota branch.

## 6. Automatic zeros rejected on manual inspection

Recorded so the numbers can be audited:

| declaration | why it is not dead |
|---|---|
| `Lean4Lean.AddInduct.find?_mono` | used as `h2.find?_mono` at `Verify/Environment/Lemmas.lean:563,570,733`; the resolver mis-credited a same-named `AddQuot.find?_mono` |
| `Lean4Lean.AddInduct.rec_find` | used as `hadd.rec_find` at `Lemmas.lean:735`; collides with `TrEnv'.IotaRule.rec_find` |
| `Lean4Lean.AddInduct.ctor_find` | used as `hadd.ctor_find` at `Lemmas.lean:631`; collides with `TrEnv'.IotaRule.ctor_find` |
| `Lean4Lean.VEnv.HasPrimitives.trBool` | used at `Verify/Environment/Primitive/Basic.lean:85,1116,1123`; collides with a local `def trBool` |
| `AddQuotAux.tacticQuot_simp`, `tacticQuot_mem` | `macro`-generated; the tactics `quot_simp`/`quot_mem` are used ~20 times in `Verify/Environment/Quot.lean` |
| `Tests.ProjShape.termU`, `termV` | `local notation`-generated; the notations `u`/`v` are used throughout `Tests/ProjShape.lean` |

## 7. Interpretation

The dead-code signal does **not** read as speculative over-production. 31 unreferenced
declarations out of 875 contributed (3.5%, and 3.3% outside `Tests/`) is *lower* than the
11.2% consumer-less rate of the upstream core this code sits in, and the dead set is not
a graveyard of abandoned machinery: there is no unreferenced definition, no unreferenced
inductive, no unreferenced structure — everything on the list is a leaf lemma, a
structure field, or a test assertion, and nothing on it exceeds a dozen lines. The two
largest clusters have benign readings: the seven never-projected `VInductDecl.WF` fields
are the *content* of a well-formedness specification (a field of a `WF` structure is an
obligation the definition imposes, not an API call site), and the eight unreferenced test
theorems are checked by the compiler every build, which is exactly what a test theorem is
for. What is left as genuine surplus is small and specific: nine leaf lemmas in the theory
(`one_le_numMotives`, `majorFormer?_eq`, `LargeElim.shape`, `pats_origin`,
`iotaRHS_iotaCounts`, `liftVar_consN_lt/succ`, `projMotiveBody_zero`, `instFields_nil`),
several of which are advertised in docstrings that promise a use the code never makes —
the recognisable shape of proving the lemma you expect to need next and then finding a
shorter route. Three findings do cut against the contributions, and they are about
*wiring*, not volume: trproj's headline theorem `TrEnv.proj_defeq` has no consumer in the
library and is reached only by an `#print axioms` assertion in a test, so the projection
work is not yet connected to anything that depends on it; both branches left an
unreferenced `sorry`-carrying theorem in place (`crDefEq_of_induct`, `inferProj.WF_struct`)
rather than deleting or finishing it; and trproj's `lift'_inst_hi` refactor orphaned a
six-declaration upstream cluster in `Theory/VExpr.lean` without removing it — the kind of
thing a reviewer of an upstream PR will notice, and the one place where the branches made
the host repo measurably worse rather than merely not-better.
