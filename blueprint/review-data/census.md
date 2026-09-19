# Ground-truth declaration and axiom census (compiled environment)

> **Recovery note (this pass).** Regenerated from the recovered generator chain
> `census/attrib.py` → `census/mkcensus.py` (part 1) → `census/mkcensus2.py` (part 2, appends
> §6) after a `/tmp` wipe; no generator logic was changed, only re-run against the regenerated
> `understand/decls.tsv`. The pre-recovery partial (9216 bytes, section 1 only) is preserved at
> `understand/census-partial.md`. This full version is 2297 lines / ~140KB, sections 0-6.
> Two of `mkcensus.py`'s section headings are **static strings written when the script was first
> authored** and were not recomputed against this run's data (leaving them as the generator
> produced them, per the "no logic changes" constraint): §2's title says "(638)" where the table
> beneath it now has **629** rows, and §3/§4's titles ("110" axioms, "12" opaques) do still match
> exactly (verified independently against `all-constants.tsv`). Treat the §2 heading count as
> stale; the table itself is freshly computed and authoritative. All other totals in §1 and the
> per-file breakdown in §6 are computed live from this run's `decls.tsv`/`decls-attrib.tsv`.
>
> Everything below this note is the generators' own output, unedited.

Source of truth: the **compiled `.olean`s** of the `trproj` working tree (built 2026-09-10 10:08, HEAD `20ec229`, Lean `v4.33.0-rc2`). Nothing was rebuilt.

Scripts: `../census/Census.lean` (pass A: whole project except `Lean4Lean.Experimental.*`) plus `../census/Census_<Mod>.lean`, one per Experimental module. Raw data: `decls.tsv` (7 columns: name, module, kind, line, axioms, usesSorry, private/public), `decls-attrib.tsv` (same + branch attribution + tag histogram), `all-constants.tsv` (every constant incl. compiler-generated, unfiltered).

## 0. Caveats you must read before trusting a number

- **The `Experimental/` directory cannot be imported as a whole.** `Lean4Lean.Experimental.LogRel`, `MoreStepIndexed`, `StepIndexed`, `DomainTheory` and `ShapeLogRel` all open `namespace Lean4Lean.SExpr` and redeclare the same names (e.g. `Lean4Lean.SExpr.Classifier`), so `import` of two of them fails with *environment already contains*. The census therefore ran one pass per Experimental module and merged. These modules are mutually exclusive drafts, not a library.

- **`Lean4Lean/Experimental/Thierry.lean` and `Thierry2.lean` import nothing at all** (not even `Lean`) and declare ~57 axioms **in the root namespace**: `D`, `proj`, `HasType`, `subst`, `mySorry`, `eval_cons`, … Anything importing them pollutes the global namespace.

- Three stale `.olean`s exist with no source (`Lean4Lean/Verify/Environment/Boundaries`, `Lean4Lean/Theory/Pattern`, `Lean4Lean/Std/Variable!`); they are *not* imported by anything live and are excluded from the census.

- `Lean4Lean/Verify/Environment/Basic.lean` and `Lemmas.lean` have mtimes (2026-09-14) newer than their `.olean`s (2026-09-10) but are clean w.r.t. `git status`, so content matches HEAD.

- The `kind` column reports `instance` (via `Lean.Meta.isInstance`) **in preference to** the underlying `ConstantInfo` case. One axiom is thereby hidden in the `instance` row: `Lean.Level.instLawfulBEqLevel` (`Verify/Axioms.lean:292`, `@[instance] axiom`). Axiom/opaque lists below are recomputed from `all-constants.tsv`, which keeps the raw kind.

- Internal names were filtered (numeric components, `_`-prefixed, `match_`/`proof_`/`eq_` prefixes, `.rec`/`.recOn`/`.casesOn`/`.brecOn`/`.below`/`.noConfusion`/`inj*`/`sizeOf*` suffixes). 20725 constants in `Lean4Lean.*`/`Main` reduce to 7710 user-level ones. Private declarations are **kept**, shown under their de-privatised user name, marked `private` in column 7. Mutual-inductive recursors named `X.rec_1`, `X.rec_2` (18 of them, mostly `Tests/IotaShape`) slip through the filter.

- Branch attribution comes from `../blame/*.txt`: a declaration is tagged by the majority tag over the lines from its declaration-range start to the next declaration's start. `/mixed` means the span contains more than one tag (typically a master declaration touched on a branch, or a branch declaration whose trailing span reaches into master code). `unknown(no-range)` = no `declRangeExt` entry (mostly auto-generated equation/structure-eta constants that survived the filter).


## 1. Totals per module directory

|directory|decls|sorryAx|def|thm|instance|structure|inductive|ctor|axiom|opaque|rec|private|master|iota|trproj|mixed|
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
|Theory|1573|90|331|880|0|0|50|311|0|1|0|71|971|274|88|77|
|Verify|2700|233|663|1697|0|0|63|245|32|0|0|358|2156|149|45|151|
|Experimental|2403|306|541|1128|0|0|86|580|68|0|0|103|2295|1|0|8|
|Tests|418|0|222|131|0|0|27|37|0|1|0|45|64|113|173|3|
|kernel|739|0|566|103|0|0|24|34|2|10|0|29|713|12|3|2|
|**all**|7833|629|2323|3939|0|0|250|1207|102|12|0|606|6199|549|309|241|

`kernel` = the executable kernel re-implementation and its support: `Lean4Lean/{Declaration,Environment*,EquivManager,Expr,ForEachExprV,FuelConfig,Inductive/*,Instantiate,Level,List,LocalContext,Primitive,PtrEq,Quot,Replay,Std/*,TypeChecker}.lean` plus `Main.lean`. `unknown(no-range)` rows (377 overall) are not shown in the branch columns, so branch columns need not sum to `decls`.


Per-module counts (decls / sorryAx-carrying):

| module | decls | sorryAx |
|---|---|---|
| `Lean4Lean.Experimental.CoinductiveLogRel` | 10 | 0 |
| `Lean4Lean.Experimental.DomainTheory` | 53 | 1 |
| `Lean4Lean.Experimental.LogRel` | 105 | 68 |
| `Lean4Lean.Experimental.MoreStepIndexed` | 99 | 3 |
| `Lean4Lean.Experimental.NormalEq` | 111 | 0 |
| `Lean4Lean.Experimental.ParallelReduction` | 86 | 5 |
| `Lean4Lean.Experimental.SExpr` | 447 | 58 |
| `Lean4Lean.Experimental.ShapeLogRel` | 832 | 23 |
| `Lean4Lean.Experimental.ShapeLogRelAdequacy` | 17 | 15 |
| `Lean4Lean.Experimental.StepIndexed` | 17 | 0 |
| `Lean4Lean.Experimental.Stratified` | 51 | 1 |
| `Lean4Lean.Experimental.StratifiedUntyped` | 46 | 1 |
| `Lean4Lean.Experimental.Stronger` | 121 | 1 |
| `Lean4Lean.Experimental.Thierry` | 137 | 34 |
| `Lean4Lean.Experimental.Thierry2` | 211 | 91 |
| `Lean4Lean.Experimental.UniqueTyping` | 60 | 5 |
| `Lean4Lean.Tests.DeclFVar` | 8 | 0 |
| `Lean4Lean.Tests.IotaShape` | 158 | 0 |
| `Lean4Lean.Tests.KernelHardening` | 26 | 0 |
| `Lean4Lean.Tests.Level` | 9 | 0 |
| `Lean4Lean.Tests.LevelStd` | 14 | 0 |
| `Lean4Lean.Tests.NestedInductive` | 2 | 0 |
| `Lean4Lean.Tests.ProjInhabit` | 148 | 0 |
| `Lean4Lean.Tests.ProjShape` | 22 | 0 |
| `Lean4Lean.Tests.ShapeDecide` | 26 | 0 |
| `Lean4Lean.Tests.Toolchain` | 5 | 0 |
| `Lean4Lean.Theory.Inductive` | 60 | 0 |
| `Lean4Lean.Theory.LevelSat` | 61 | 0 |
| `Lean4Lean.Theory.Meta` | 17 | 0 |
| `Lean4Lean.Theory.Proj` | 49 | 0 |
| `Lean4Lean.Theory.Quot` | 8 | 0 |
| `Lean4Lean.Theory.Typing.Basic` | 44 | 0 |
| `Lean4Lean.Theory.Typing.ChurchRosser` | 146 | 32 |
| `Lean4Lean.Theory.Typing.Env` | 22 | 0 |
| `Lean4Lean.Theory.Typing.EnvLemmas` | 23 | 3 |
| `Lean4Lean.Theory.Typing.HeadReduction` | 113 | 21 |
| `Lean4Lean.Theory.Typing.InductiveLemmas` | 76 | 0 |
| `Lean4Lean.Theory.Typing.InductiveParams` | 26 | 1 |
| `Lean4Lean.Theory.Typing.Injectivity` | 4 | 4 |
| `Lean4Lean.Theory.Typing.Lemmas` | 171 | 0 |
| `Lean4Lean.Theory.Typing.Meta` | 7 | 0 |
| `Lean4Lean.Theory.Typing.Pattern` | 133 | 0 |
| `Lean4Lean.Theory.Typing.QuotLemmas` | 8 | 0 |
| `Lean4Lean.Theory.Typing.Strong` | 148 | 0 |
| `Lean4Lean.Theory.Typing.UniqueTyping` | 31 | 29 |
| `Lean4Lean.Theory.VDecl` | 44 | 0 |
| `Lean4Lean.Theory.VEnv` | 31 | 0 |
| `Lean4Lean.Theory.VExpr` | 292 | 0 |
| `Lean4Lean.Theory.VLevel` | 59 | 0 |
| `Lean4Lean.Verify.Axioms` | 87 | 0 |
| `Lean4Lean.Verify.Environment` | 11 | 6 |
| `Lean4Lean.Verify.Environment.Basic` | 108 | 0 |
| `Lean4Lean.Verify.Environment.Checker` | 23 | 9 |
| `Lean4Lean.Verify.Environment.Extension` | 25 | 0 |
| `Lean4Lean.Verify.Environment.Lemmas` | 70 | 6 |
| `Lean4Lean.Verify.Environment.Primitive` | 24 | 1 |
| `Lean4Lean.Verify.Environment.Primitive.Basic` | 173 | 35 |
| `Lean4Lean.Verify.Environment.Primitive.Bitwise` | 5 | 3 |
| `Lean4Lean.Verify.Environment.Primitive.Clauses` | 17 | 15 |
| `Lean4Lean.Verify.Environment.Primitive.Condition` | 133 | 24 |
| `Lean4Lean.Verify.Environment.Primitive.DivMod` | 8 | 4 |
| `Lean4Lean.Verify.Environment.Primitive.Gcd` | 2 | 1 |
| `Lean4Lean.Verify.Environment.Primitive.Recursion` | 60 | 8 |
| `Lean4Lean.Verify.Environment.Quot` | 79 | 0 |
| `Lean4Lean.Verify.EquivManager` | 59 | 3 |
| `Lean4Lean.Verify.Expr` | 215 | 0 |
| `Lean4Lean.Verify.Level` | 368 | 0 |
| `Lean4Lean.Verify.LevelStd` | 54 | 0 |
| `Lean4Lean.Verify.LocalContext` | 74 | 0 |
| `Lean4Lean.Verify.Name` | 9 | 0 |
| `Lean4Lean.Verify.NameGenerator` | 10 | 0 |
| `Lean4Lean.Verify.NormLt` | 45 | 0 |
| `Lean4Lean.Verify.Primitive` | 47 | 16 |
| `Lean4Lean.Verify.QSort` | 35 | 0 |
| `Lean4Lean.Verify.TypeChecker` | 42 | 14 |
| `Lean4Lean.Verify.TypeChecker.Basic` | 227 | 9 |
| `Lean4Lean.Verify.TypeChecker.InferType` | 36 | 14 |
| `Lean4Lean.Verify.TypeChecker.IsDefEq` | 56 | 22 |
| `Lean4Lean.Verify.TypeChecker.Reduce` | 15 | 6 |
| `Lean4Lean.Verify.TypeChecker.WHNF` | 12 | 5 |
| `Lean4Lean.Verify.Typing.ConditionallyTyped` | 16 | 3 |
| `Lean4Lean.Verify.Typing.Expr` | 132 | 0 |
| `Lean4Lean.Verify.Typing.Lemmas` | 344 | 29 |
| `Lean4Lean.Verify.Typing.PrimSpec` | 13 | 0 |
| `Lean4Lean.Verify.Typing.TrTerm` | 35 | 0 |
| `Lean4Lean.Verify.VLCtx` | 31 | 0 |
| `Lean4Lean.Declaration` | 2 | 0 |
| `Lean4Lean.Environment` | 9 | 0 |
| `Lean4Lean.Environment.Basic` | 12 | 0 |
| `Lean4Lean.EquivManager` | 11 | 0 |
| `Lean4Lean.Expr` | 17 | 0 |
| `Lean4Lean.ForEachExprV` | 3 | 0 |
| `Lean4Lean.FuelConfig` | 16 | 0 |
| `Lean4Lean.Inductive.Add` | 115 | 0 |
| `Lean4Lean.Inductive.Reduce` | 8 | 0 |
| `Lean4Lean.Instantiate` | 3 | 0 |
| `Lean4Lean.Level` | 81 | 0 |
| `Lean4Lean.List` | 1 | 0 |
| `Lean4Lean.LocalContext` | 6 | 0 |
| `Lean4Lean.Primitive` | 97 | 0 |
| `Lean4Lean.PtrEq` | 8 | 0 |
| `Lean4Lean.Quot` | 6 | 0 |
| `Lean4Lean.Replay` | 44 | 0 |
| `Lean4Lean.Std.Basic` | 73 | 0 |
| `Lean4Lean.Std.Control` | 1 | 0 |
| `Lean4Lean.Std.HashMap` | 16 | 0 |
| `Lean4Lean.Std.NodupKeys` | 9 | 0 |
| `Lean4Lean.Std.Ord` | 5 | 0 |
| `Lean4Lean.Std.PersistentHashMap` | 6 | 0 |
| `Lean4Lean.Std.SMap` | 21 | 0 |
| `Lean4Lean.Std.ToExpr` | 31 | 0 |
| `Lean4Lean.Std.VariableBang` | 1 | 0 |
| `Lean4Lean.TypeChecker` | 130 | 0 |
| `Main` | 7 | 0 |

## 2. Every declaration whose axiom set contains `sorryAx` (638)

Grouped by module; `line` is the start of the declaration range (a doc-comment counts, so it can precede the `theorem` keyword). `attr` is the blame attribution.


### `Lean4Lean.Experimental.DomainTheory` (1)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.SExpr.Dom.out` | 211 | def | master |

### `Lean4Lean.Experimental.LogRel` (68)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.SExpr.LRIsType.forallE.congr_simp` | -1 | thm | master |
| `Lean4Lean.SExpr.LogRel.brecOn.eq` | -1 | thm | master |
| `Lean4Lean.SExpr.LogRel.brecOn.go` | -1 | def | master |
| `Lean4Lean.SExpr.LogRelV.brecOn.eq` | -1 | thm | master |
| `Lean4Lean.SExpr.LogRelV.brecOn.go` | -1 | def | master |
| `Lean4Lean.SExpr.Classifier.DefEq.symm` | 26 | thm | master |
| `Lean4Lean.SExpr.Classifier.defEq_self` | 31 | thm | master |
| `Lean4Lean.SExpr.Classifier.forallE` | 42 | def | master |
| `Lean4Lean.SExpr.LogRel` | 70 | inductive | master |
| `Lean4Lean.SExpr.LogRel.forallE` | 76 | ctor | master |
| `Lean4Lean.SExpr.LogRel.hasType` | 87 | thm | master |
| `Lean4Lean.SExpr.LogRel.eqTy_refl` | 91 | thm | master |
| `Lean4Lean.SExpr.LRIsType` | 98 | def | master |
| `Lean4Lean.SExpr.LREqTy` | 101 | def | master |
| `Lean4Lean.SExpr.LRDefEq` | 104 | def | master |
| `Lean4Lean.SExpr.LRIsType.hasType` | 108 | thm | master |
| `Lean4Lean.SExpr.LREqTy.defeq` | 109 | thm | master |
| `Lean4Lean.SExpr.LRDefEq.defeq` | 110 | thm | master |
| `Lean4Lean.SExpr.LRDefEq.left` | 111 | thm | master |
| `Lean4Lean.SExpr.LRIsType.cast` | 114 | def | master |
| `Lean4Lean.SExpr.LREqTy.cast` | 115 | thm | master |
| `Lean4Lean.SExpr.LRDefEq.cast` | 117 | thm | master |
| `Lean4Lean.SExpr.LRHasTy.cast` | 119 | thm | master |
| `Lean4Lean.SExpr.LRIsType.stuck` | 122 | def | master |
| `Lean4Lean.SExpr.LRIsType.sort` | 124 | def | master |
| `Lean4Lean.SExpr.LRIsType.forallE` | 127 | def | master |
| `Lean4Lean.SExpr.LRIsType.rec.inner` | 148 | def | master |
| `Lean4Lean.SExpr.LRIsType.irrel'` | 157 | thm | master |
| `Lean4Lean.SExpr.LRIsType.irrel` | 181 | thm | master |
| `Lean4Lean.SExpr.LREqTy.irrel` | 183 | thm | master |
| `Lean4Lean.SExpr.LRDefEq.irrel` | 186 | thm | master |
| `Lean4Lean.SExpr.instSubsingletonLRIsType` | 189 | thm | master |
| `Lean4Lean.SExpr.LogRel.cast` | 191 | def | master |
| `Lean4Lean.SExpr.LogRel.cast_eqTy` | 194 | thm | master |
| `Lean4Lean.SExpr.LogRel.cast_hasTy` | 198 | thm | master |
| `Lean4Lean.SExpr.LogRel.cast_defEq` | 202 | thm | master |
| `Lean4Lean.SExpr.LRIsType.weak'` | 206 | def | master |
| `Lean4Lean.SExpr.LREqTy.weak'` | 219 | thm | master |
| `Lean4Lean.SExpr.LRDefEq.weak'` | 232 | thm | master |
| `Lean4Lean.SExpr.LREqTy.defeq_r` | 243 | thm | master |
| `Lean4Lean.SExpr.LREqTy.symm` | 246 | def | master |
| `Lean4Lean.SExpr.LRDefEq.symm` | 254 | thm | master |
| `Lean4Lean.SExpr.ClassifierV.IsTy` | 263 | def | master |
| `Lean4Lean.SExpr.LogRelV` | 267 | inductive | master |
| `Lean4Lean.SExpr.LogRelV.cons` | 269 | ctor | master |
| `Lean4Lean.SExpr.LVIsCtx` | 274 | def | master |
| `Lean4Lean.SExpr.LVIsType` | 277 | def | master |
| `Lean4Lean.SExpr.LVEqSubst` | 280 | def | master |
| `Lean4Lean.SExpr.LVIsCtx.nil` | 284 | def | master |
| `Lean4Lean.SExpr.LVIsCtx.cons` | 285 | def | master |
| `Lean4Lean.SExpr.LVIsType.sort` | 287 | def | master |
| `Lean4Lean.SExpr.LVIsCtxInv` | 290 | inductive | master |
| `Lean4Lean.SExpr.LVIsCtxInv.nil` | 291 | ctor | master |
| `Lean4Lean.SExpr.LVIsCtxInv.cons` | 292 | ctor | master |
| `Lean4Lean.SExpr.LVIsCtx.inv` | 294 | thm | master |
| `Lean4Lean.SExpr.LVEqSubst.left` | 299 | thm | master |
| `Lean4Lean.SExpr.LVIsType.subst` | 301 | def | master |
| `Lean4Lean.SExpr.LVEqSubst.eqTy` | 304 | thm | master |
| `Lean4Lean.SExpr.LVIsCtx.cons_inv` | 307 | def | master |
| `Lean4Lean.SExpr.LVEqSubst.tail` | 310 | thm | master |
| `Lean4Lean.SExpr.LVEqSubst.head` | 313 | thm | master |
| `Lean4Lean.SExpr.LVIsType.lift` | 316 | def | master |
| `Lean4Lean.SExpr.LVEqTy` | 329 | def | master |
| `Lean4Lean.SExpr.LVHasType` | 333 | def | master |
| `Lean4Lean.SExpr.LVDefEq` | 345 | def | master |
| `Lean4Lean.SExpr.LVDefEq.refl` | 349 | thm | master |
| `Lean4Lean.SExpr.LVDefEq.symm` | 350 | thm | master |
| `Lean4Lean.SExpr.fundamental` | 353 | thm | master |

### `Lean4Lean.Experimental.MoreStepIndexed` (3)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.SExpr.ShapeFun.app_mono_l` | 309 | thm | master |
| `Lean4Lean.SExpr.Shape.app_mono_l` | 316 | thm | master |
| `Lean4Lean.SExpr.LogRelK.forallE` | 405 | def | master |

### `Lean4Lean.Experimental.ParallelReduction` (5)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.NormalEq.parRed` | 687 | thm | master |
| `Lean4Lean.NormalEq.parRedS` | 786 | thm | master |
| `Lean4Lean.ParRedS.church_rosser` | 799 | thm | master |
| `Lean4Lean.Typing.CRDefEq.trans` | 832 | thm | master |
| `Lean4Lean.VEnv.IsDefEqU.church_rosser` | 861 | thm | master/mixed |

### `Lean4Lean.Experimental.SExpr` (58)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.SExpr.IsDefEq.strong` | 679 | thm | master |
| `Lean4Lean.SExpr.IsDefEqStrong.defeq` | 680 | thm | master |
| `Lean4Lean.Params.ctor_ty` | 682 | thm | master |
| `Lean4Lean.SExpr.HasTypeStratifiedS.to_core` | 734 | thm | master |
| `Lean4Lean.SExpr.HasTypeStratifiedS.isType` | 737 | thm | master |
| `Lean4Lean.SExpr.Ctx.Subst.lift_r` | 760 | thm | master |
| `Lean4Lean.SExpr.Ctx.Subst.lift` | 763 | thm | master |
| `Lean4Lean.SExpr.Ctx.Subst.id` | 770 | thm | master |
| `Lean4Lean.SExpr.Ctx.Subst.one` | 771 | thm | master |
| `Lean4Lean.SExpr.Ctx.SubstEq.left` | 781 | thm | master |
| `Lean4Lean.SExpr.IsDefEq.subst` | 786 | thm | master |
| `Lean4Lean.SExpr.Ctx.SubstEq.symm` | 789 | thm | master |
| `Lean4Lean.SExpr.Ctx.SubstEq.lookup` | 794 | thm | master |
| `Lean4Lean.SExpr.Ctx.SubstEq.lift` | 797 | thm | master |
| `Lean4Lean.SExpr.IsDefEq.defeqDF_l'` | 823 | thm | master |
| `Lean4Lean.SExpr.IsDefEq.defeqDF_l` | 827 | thm | master |
| `Lean4Lean.SExpr.HasType.defeq_l` | 831 | thm | master |
| `Lean4Lean.SExpr.IsDefEqLift.subst` | 885 | thm | master |
| `Lean4Lean.SExpr.IsDefEq.defeqDFC'` | 936 | thm | master |
| `Lean4Lean.SExpr.IsDefEq.defeqDFC` | 943 | thm | master |
| `Lean4Lean.SExpr.WHRed.subst` | 953 | thm | master |
| `Lean4Lean.SExpr.WHRed.weak'` | 959 | thm | master |
| `Lean4Lean.SExpr.WHRed.weakU_inv` | 965 | thm | master |
| `Lean4Lean.SExpr.WHRed.determ` | 981 | thm | master |
| `Lean4Lean.SExpr.WHRedS.subst` | 1002 | thm | master |
| `Lean4Lean.SExpr.WHRedS.defeq` | 1008 | thm | master |
| `Lean4Lean.SExpr.WHRedS.weak'` | 1010 | thm | master |
| `Lean4Lean.SExpr.WHRedS.weakU_inv` | 1021 | thm | master |
| `Lean4Lean.SExpr.WHRedS.determ_l` | 1030 | thm | master |
| `Lean4Lean.SExpr.WHRedS.determ` | 1043 | thm | master |
| `Lean4Lean.SExpr.ParRed.weak'` | 1060 | thm | master |
| `Lean4Lean.SExpr.ParRedS.weak'` | 1074 | thm | master |
| `Lean4Lean.SExpr.InferType.hasType` | 1091 | thm | master |
| `Lean4Lean.SExpr.InferType.determ` | 1093 | thm | master |
| `Lean4Lean.SExpr.InferType.weak'` | 1106 | thm | master |
| `Lean4Lean.SExpr.InferType.weakU_inv` | 1114 | thm | master |
| `Lean4Lean.SExpr.InferType.weak'_inv` | 1140 | thm | master |
| `Lean4Lean.SExpr.InferType.subst` | 1144 | thm | master |
| `Lean4Lean.SExpr.InferType.inst` | 1161 | thm | master |
| `Lean4Lean.SExpr.InferTypeS.hasType` | 1167 | thm | master |
| `Lean4Lean.SExpr.WHRedS.inferType` | 1169 | thm | master |
| `Lean4Lean.SExpr.WHRedS.parRedS` | 1182 | thm | master |
| `Lean4Lean.SExpr.InferTypeS.determ` | 1184 | thm | master |
| `Lean4Lean.SExpr.InferTypeS.weak'` | 1190 | thm | master |
| `Lean4Lean.SExpr.InferTypeS.weakU_inv` | 1193 | thm | master |
| `Lean4Lean.SExpr.NormalEq.defeqDFC` | 1217 | thm | master |
| `Lean4Lean.SExpr.NormalEq.defeq` | 1234 | thm | master |
| `Lean4Lean.SExpr.NormalEq.symm` | 1248 | thm | master |
| `Lean4Lean.SExpr.NormalEq.weak'` | 1259 | thm | master |
| `Lean4Lean.SExpr.CRDefEq.normalEq` | 1283 | thm | master |
| `Lean4Lean.SExpr.CRDefEq.refl` | 1286 | thm | master |
| `Lean4Lean.SExpr.CRDefEq.symm` | 1291 | thm | master |
| `Lean4Lean.SExpr.CRDefEq.trans` | 1294 | thm | master |
| `Lean4Lean.SExpr.CRDefEq.weak'` | 1300 | thm | master |
| `Lean4Lean.SExpr.WHRedS.crDefEq` | 1304 | thm | master |
| `Lean4Lean.SExpr.CRDefEqLift.symm` | 1307 | thm | master |
| `Lean4Lean.SExpr.CRDefEqLift.refl` | 1313 | thm | master |
| `Lean4Lean.SExpr.InferType.whRed` | 1316 | thm | master |

### `Lean4Lean.Experimental.ShapeLogRel` (23)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.SExpr.LR.SubstWF.below.cons` | -1 | ctor | master |
| `Lean4Lean.SExpr.LR.SubstWF.below.id` | -1 | ctor | master |
| `Lean4Lean.SExpr.LE_Interp.strongSound` | 5054 | thm | master |
| `Lean4Lean.SExpr.LE_Interp.sound` | 5261 | thm | master |
| `Lean4Lean.SExpr.LR0` | 5307 | def | master |
| `Lean4Lean.SExpr.LRS.TyDefEq.symm` | 5453 | thm | master |
| `Lean4Lean.SExpr.LRS.TyDefEq.trans` | 5464 | thm | master |
| `Lean4Lean.SExpr.LRS` | 5657 | def | master |
| `Lean4Lean.SExpr.LR` | 5896 | def | master |
| `Lean4Lean.SExpr.LR_zero` | 5901 | thm | master |
| `Lean4Lean.SExpr.LR_succ` | 5902 | thm | master |
| `Lean4Lean.SExpr.LRS.PiDefEq.lift_aux` | 5904 | thm | master |
| `Lean4Lean.SExpr.LRS.LamDefEq.lift_aux` | 5949 | thm | master |
| `Lean4Lean.SExpr.LR.lift_succ_aux` | 6004 | thm | master |
| `Lean4Lean.SExpr.LR.DefEq.lift` | 6046 | thm | master |
| `Lean4Lean.SExpr.LR.TyDefEq.lift` | 6052 | thm | master |
| `Lean4Lean.SExpr.LR.Subst1` | 6061 | def | master |
| `Lean4Lean.SExpr.LR.SubstWF` | 6066 | inductive | master |
| `Lean4Lean.SExpr.LR.SubstWF.cons` | 6068 | ctor | master |
| `Lean4Lean.SExpr.LR.SubstWF.fits` | 6075 | thm | master |
| `Lean4Lean.SExpr.LR.SubstWF.toSubstEq` | 6079 | thm | master |
| `Lean4Lean.SExpr.LR.SubstWF.left` | 6083 | thm | master |
| `Lean4Lean.SExpr.LR.SubstWF.symm` | 6091 | thm | master |

### `Lean4Lean.Experimental.ShapeLogRelAdequacy` (15)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.SExpr.LR.Adequate` | 8 | def | master |
| `Lean4Lean.SExpr.LR.Adequate.bot` | 14 | thm | master |
| `Lean4Lean.SExpr.LR.Adequate.fits` | 17 | thm | master |
| `Lean4Lean.SExpr.LR.Adequate.refl` | 21 | thm | master |
| `Lean4Lean.SExpr.LR.Adequate.left` | 26 | thm | master |
| `Lean4Lean.SExpr.LR.Adequate.symm` | 29 | thm | master |
| `Lean4Lean.SExpr.LR.Adequate.trans` | 32 | thm | master |
| `Lean4Lean.SExpr.LR.Adequate.trans'` | 37 | thm | master |
| `Lean4Lean.SExpr.LR.Adequate.cons` | 45 | thm | master |
| `Lean4Lean.SExpr.LR.toValTy` | 93 | thm | master |
| `Lean4Lean.SExpr.LR.adequacy` | 105 | thm | master |
| `Lean4Lean.SExpr.forallE_whRed_l` | 434 | thm | master |
| `Lean4Lean.SExpr.forallE_inv` | 448 | thm | master |
| `Lean4Lean.SExpr.sort_forallE_inv` | 455 | thm | master |
| `Lean4Lean.SExpr.sort_inv` | 458 | thm | master |

### `Lean4Lean.Experimental.Stratified` (1)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.VEnv.IsDefEq.induction1` | 80 | thm | master/mixed |

### `Lean4Lean.Experimental.StratifiedUntyped` (1)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.VEnv.IsDefEq.inductionU1` | 60 | thm | master/mixed |

### `Lean4Lean.Experimental.Stronger` (1)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.VEnv'.IsDefEqStrong.uniqL'` | 575 | thm | master |

### `Lean4Lean.Experimental.Thierry` (34)

| declaration | line | kind | attr |
|---|---|---|---|
| `WHRed.below.app` | -1 | ctor | master |
| `WHRed.below.beta` | -1 | ctor | master |
| `WHRedTS.below.rfl` | -1 | ctor | master |
| `WHRedTS.below.tail` | -1 | ctor | master |
| `FinMut.LE.rfl` | 93 | thm | master |
| `FinMut.LE.lam` | 94 | thm | master |
| `FinMut.LE.pi` | 95 | thm | master |
| `FinHasType.mono` | 118 | thm | master |
| `FinHasType.join` | 120 | thm | master |
| `FinHasType.pi_eval` | 122 | thm | master |
| `FinHasType.lam_eval` | 123 | thm | master |
| `FinHasType.lem5` | 124 | thm | master |
| `El_iff` | 137 | thm | master |
| `El_U_iff` | 138 | thm | master |
| `El.mono` | 139 | thm | master |
| `subst` | 148 | def | master |
| `WHRed` | 166 | inductive | master |
| `WHRed.beta` | 168 | ctor | master |
| `WHRedT` | 174 | def | master |
| `WHRedTS` | 175 | inductive | master |
| `WHRedTS.tail` | 177 | ctor | master |
| `WHRedTS.uniq_pi` | 181 | axiom | master |
| `meas_apply_lt` | 190 | thm | master |
| `HasTypeF` | 194 | def | master |
| `HasTypeFamF` | 207 | def | master |
| `HasPiFamF` | 213 | def | master |
| `HasTypeFamF.def` | 222 | thm | master |
| `HasPiFamF.def` | 226 | thm | master |
| `HasPiFamF.bot` | 230 | thm | master |
| `HasTypeF.mono` | 248 | thm | master |
| `HasPiFamF.mono` | 291 | thm | master |
| `HasTypeFamF.mono` | 308 | thm | master |
| `HasTypeF.mono_r` | 321 | thm | master |
| `HasPiFamF.mono_r` | 347 | thm | master |

### `Lean4Lean.Experimental.Thierry2` (91)

| declaration | line | kind | attr |
|---|---|---|---|
| `WHRed.below.app` | -1 | ctor | master |
| `WHRed.below.beta` | -1 | ctor | master |
| `WHRedTS.below.rfl` | -1 | ctor | master |
| `WHRedTS.below.tail` | -1 | ctor | master |
| `ShapeFun.LE.bot` | 97 | thm | master |
| `Shape.Compat.def` | 132 | thm | master |
| `Shape.Join.compat` | 134 | thm | master |
| `Shape.Join.mk` | 156 | thm | master |
| `ShapeFun.Join.mk` | 158 | thm | master |
| `ShapeFun.app_mono_l` | 166 | thm | master |
| `ShapeFun.app_mono_r` | 169 | thm | master |
| `ShapeFun.Join.app` | 172 | thm | master |
| `ShapeFun.Compat.def` | 174 | thm | master |
| `ShapeFun.bot_app` | 178 | thm | master |
| `Shape.Join.app` | 184 | thm | master |
| `Shape.app_mono_l` | 186 | thm | master |
| `Shape.app_mono_r` | 192 | thm | master |
| `Shape.HasType.mono` | 240 | thm | master |
| `Shape.HasTypeLam.app` | 242 | thm | master |
| `Shape.HasTypePi.app` | 245 | thm | master |
| `Shape.HasType.maximal` | 248 | thm | master |
| `Shape.Compat.lift` | 329 | thm | master |
| `ShapeFun.Compat.lift` | 332 | thm | master |
| `Shape.lift_join` | 336 | thm | master |
| `ShapeFun.lift_join` | 339 | thm | master |
| `ShapeFun.lift_app` | 343 | thm | master |
| `Shape.lift_app` | 347 | thm | master |
| `D.above.join'` | 358 | thm | master |
| `Shape.embed` | 375 | def | master |
| `D.bot` | 387 | def | master |
| `D.bot_above` | 388 | thm | master |
| `D.LE.bot` | 392 | thm | master |
| `D.U` | 394 | def | master |
| `instCoeOutShapeD` | 402 | def | master |
| `DF.app` | 405 | def | master |
| `instCoeFunDFForallD` | 419 | def | master |
| `DF.mk'` | 421 | def | master |
| `DF.mk'_app` | 422 | axiom | master |
| `D.LE.app` | 424 | thm | master |
| `DF.comp` | 427 | def | master |
| `D.lam` | 432 | def | master |
| `D.pi` | 472 | def | master |
| `instLEDF` | 474 | def | master |
| `DF.LE.trans` | 476 | thm | master |
| `DF.bot` | 478 | def | master |
| `DF.bot_app` | 483 | thm | master |
| `D.lam_bot` | 486 | thm | master |
| `D.unlam` | 492 | def | master |
| `D.app` | 536 | def | master |
| `instCoeFunDForall` | 538 | def | master |
| `D.app_lam` | 539 | axiom | master |
| `D.LE.lam` | 541 | axiom | master |
| `D.LE.pi` | 542 | axiom | master |
| `D.LE.embed` | 544 | axiom | master |
| `DF.LE.embed` | 545 | axiom | master |
| `Shape.embed_U` | 547 | axiom | master |
| `proj_U_U` | 550 | axiom | master |
| `proj_U_pi` | 551 | axiom | master |
| `proj_pi` | 552 | axiom | master |
| `proj_le` | 555 | axiom | master |
| `proj_proj` | 556 | axiom | master |
| `El` | 558 | def | master |
| `El_iff` | 560 | thm | master |
| `El_U_iff` | 561 | thm | master |
| `El.mono` | 562 | thm | master |
| `subst` | 571 | def | master |
| `push` | 574 | def | master |
| `Expr.eval` | 578 | def | master |
| `fits` | 585 | def | master |
| `Valuation.nil` | 591 | def | master |
| `interp` | 596 | def | master |
| `WHRed` | 603 | inductive | master |
| `WHRed.beta` | 605 | ctor | master |
| `WHRedT` | 612 | def | master |
| `WHRedTS` | 613 | inductive | master |
| `WHRedTS.tail` | 615 | ctor | master |
| `WHRedTS.uniq_pi` | 619 | axiom | master |
| `DefEqPiF` | 624 | def | master |
| `DefEqLamF` | 631 | def | master |
| `DefEqF` | 640 | def | master |
| `DefEqF.U_U` | 653 | thm | master |
| `DefEqPiF.left` | 656 | thm | master |
| `DefEqLamF.left` | 661 | thm | master |
| `DefEqF.left` | 666 | thm | master |
| `DefEqF.bot` | 684 | thm | master |
| `DefEqLamF.bot` | 690 | thm | master |
| `DefEqF.mono` | 702 | thm | master |
| `DefEqLamF.mono` | 742 | thm | master |
| `DefEqPiF.mono` | 765 | thm | master |
| `DefEqF.mono_r` | 782 | thm | master |
| `DefEqLamF.mono_r` | 814 | thm | master |

### `Lean4Lean.Experimental.UniqueTyping` (5)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.SExpr.HasTypeS.uniq` | 90 | thm | master |
| `Lean4Lean.SExpr.IsDefEq.toHasTypeS` | 136 | thm | master |
| `Lean4Lean.SExpr.IsDefEq.uniq_sort` | 172 | thm | master |
| `Lean4Lean.SExpr.IsDefEq.toIsDefEq'` | 240 | thm | master |
| `Lean4Lean.SExpr.IsDefEq.iff_isDefEq'` | 260 | thm | master |

### `Lean4Lean.Theory.Typing.ChurchRosser` (32)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.VEnv.IsDefEq.apply_pat` | 59 | thm | master |
| `Lean4Lean.Pattern.Matches.hasType` | 70 | thm | master |
| `Lean4Lean.VEnv.NormalEq.defeq` | 120 | thm | master |
| `Lean4Lean.VEnv.NormalEq.symm` | 147 | thm | master |
| `Lean4Lean.VEnv.NormalEq.instN_r` | 213 | thm | master |
| `Lean4Lean.VEnv.NormalEq.weakN_inv_DFC` | 280 | thm | master |
| `Lean4Lean.VEnv.NormalEq.weakN_iff` | 385 | thm | master |
| `Lean4Lean.VEnv.NormalEq.trans` | 400 | thm | master |
| `Lean4Lean.VEnv.NormalEq.apply_pat` | 457 | thm | master |
| `Lean4Lean.VEnv.ParRed.defeq` | 549 | thm | master |
| `Lean4Lean.VEnv.ParRed.hasType` | 575 | thm | master |
| `Lean4Lean.VEnv.ParRed.defeqDFC` | 579 | thm | master |
| `Lean4Lean.VEnv.HasType.matches_inv` | 621 | thm | master |
| `Lean4Lean.VEnv.ParRed.weakN_inv` | 644 | thm | master |
| `Lean4Lean.VEnv.CParRed.exists` | 717 | thm | master |
| `Lean4Lean.VEnv.ParRed.triangle` | 766 | thm | master |
| `Lean4Lean.VEnv.ParRed.church_rosser` | 916 | thm | master |
| `Lean4Lean.VEnv.ParRedS.hasType` | 928 | thm | master |
| `Lean4Lean.VEnv.ParRedS.defeq` | 934 | thm | master |
| `Lean4Lean.VEnv.ParRedS.defeqDFC` | 940 | thm | master |
| `Lean4Lean.VEnv.ParRedS.inst` | 980 | thm | master |
| `Lean4Lean.VEnv.hasType_app_bvar0` | 1029 | thm | master |
| `Lean4Lean.VEnv.ParRedExt.parRed_beta` | 1045 | thm | master |
| `Lean4Lean.VEnv.NormalEq.parRed` | 1181 | thm | master |
| `Lean4Lean.VEnv.NormalEq.parRedS` | 1286 | thm | master |
| `Lean4Lean.VEnv.ParRedS.church_rosser` | 1302 | thm | master |
| `Lean4Lean.VEnv.CRDefEq.normalEq` | 1323 | thm | master |
| `Lean4Lean.VEnv.CRDefEq.refl` | 1327 | thm | master |
| `Lean4Lean.VEnv.CRDefEq.defeq` | 1330 | thm | master |
| `Lean4Lean.VEnv.CRDefEq.symm` | 1335 | thm | master |
| `Lean4Lean.VEnv.CRDefEq.trans` | 1339 | thm | master |
| `Lean4Lean.VEnv.IsDefEq.church_rosser` | 1347 | thm | master/mixed |

### `Lean4Lean.Theory.Typing.EnvLemmas` (3)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.VEnv.WF.patsStrong` | 323 | thm | iota |
| `Lean4Lean.VEnv.WF.orderedStrong` | 336 | thm | iota |
| `Lean4Lean.instCoeOutWFOrderedStrong` | 343 | def | iota |

### `Lean4Lean.Theory.Typing.HeadReduction` (21)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.VEnv.WHRed.weakU_inv` | 89 | thm | master |
| `Lean4Lean.VEnv.WHRed.defeq` | 115 | thm | master |
| `Lean4Lean.VEnv.WHRed.hasType` | 119 | thm | master |
| `Lean4Lean.VEnv.WHRedS.defeq` | 241 | thm | master |
| `Lean4Lean.VEnv.WHRedS.hasType` | 245 | thm | master |
| `Lean4Lean.VEnv.WHRedS.weakU_inv` | 283 | thm | master |
| `Lean4Lean.VEnv.StRed.defeqDFC` | 330 | thm | master |
| `Lean4Lean.VEnv.StRed.defeq` | 363 | thm | master |
| `Lean4Lean.VEnv.StRed.triangle` | 409 | thm | master |
| `Lean4Lean.VEnv.StRed.triangleS` | 459 | thm | master |
| `Lean4Lean.VEnv.ParRedS.standard` | 466 | thm | master |
| `Lean4Lean.VEnv.IsDefEq.reduce_sort` | 470 | thm | master |
| `Lean4Lean.VEnv.IsDefEq.reduce_forallE` | 488 | thm | master |
| `Lean4Lean.VEnv.InferType.hasType` | 519 | thm | master |
| `Lean4Lean.VEnv.InferType.weakU_inv` | 561 | thm | master |
| `Lean4Lean.VEnv.InferType.weak'_inv` | 593 | thm | master |
| `Lean4Lean.VEnv.InferType.instN` | 599 | thm | master |
| `Lean4Lean.VEnv.InferType.inst` | 627 | thm | master |
| `Lean4Lean.VEnv.InferType.exists` | 633 | thm | master |
| `Lean4Lean.VEnv.InferTypeS.hasType` | 663 | thm | master |
| `Lean4Lean.VEnv.InferTypeS.weakU_inv` | 691 | thm | master |

### `Lean4Lean.Theory.Typing.InductiveParams` (1)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.VEnv.IsDefEq.crDefEq_of_induct` | 424 | thm | trproj/mixed |

### `Lean4Lean.Theory.Typing.Injectivity` (4)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.VEnv.IsDefEqU.sort_inv` | 11 | thm | master |
| `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified` | 14 | thm | master |
| `Lean4Lean.VEnv.IsDefEqU.forallE_inv` | 23 | thm | master |
| `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv` | 33 | thm | master |

### `Lean4Lean.Theory.Typing.UniqueTyping` (29)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.VEnv.IsDefEq.uniq` | 13 | thm | master |
| `Lean4Lean.VEnv.IsDefEq.uniqU` | 113 | thm | master |
| `Lean4Lean.VEnv.isDefEq_iff` | 117 | thm | master |
| `Lean4Lean.VEnv.IsDefEq.trans_r` | 124 | thm | master |
| `Lean4Lean.VEnv.IsDefEq.trans_l` | 128 | thm | master |
| `Lean4Lean.VEnv.IsDefEq.transU_r` | 132 | thm | master |
| `Lean4Lean.VEnv.IsDefEq.transU_l` | 136 | thm | master |
| `Lean4Lean.VEnv.IsDefEqU.defeqDF` | 140 | thm | master |
| `Lean4Lean.VEnv.IsDefEqU.of_l` | 147 | thm | master |
| `Lean4Lean.VEnv.HasType.defeqU_l` | 151 | thm | master |
| `Lean4Lean.VEnv.IsType.defeqU_l` | 155 | thm | master |
| `Lean4Lean.VEnv.IsDefEqU.of_r` | 159 | thm | master |
| `Lean4Lean.VEnv.HasType.defeqU_r` | 163 | thm | master |
| `Lean4Lean.VEnv.IsDefEqU.trans` | 167 | thm | master |
| `Lean4Lean.VEnv.IsDefEqU.weakN_iff` | 172 | thm | master |
| `Lean4Lean.VExpr.WF.weakN_iff` | 177 | thm | master |
| `Lean4Lean.VEnv.IsDefEq.skips` | 180 | thm | master |
| `Lean4Lean.VEnv.IsDefEq.weakN_iff'` | 190 | thm | master |
| `Lean4Lean.OnCtx.weakN_inv` | 198 | thm | master |
| `Lean4Lean.VEnv.IsDefEq.weakN_iff` | 211 | thm | master |
| `Lean4Lean.VEnv.HasType.weakN_iff` | 216 | thm | master |
| `Lean4Lean.VEnv.IsType.weakN_iff` | 221 | thm | master |
| `Lean4Lean.VEnv.HasType.skips` | 226 | thm | master |
| `Lean4Lean.VEnv.IsDefEqU.weak'_iff` | 231 | thm | master |
| `Lean4Lean.VEnv.IsDefEq.weak'_iff` | 244 | thm | master |
| `Lean4Lean.VEnv.HasType.weak'_iff` | 257 | thm | master |
| `Lean4Lean.VEnv.IsType.weak'_iff` | 262 | thm | master |
| `Lean4Lean.VExpr.WF.weak'_iff` | 267 | thm | master |
| `Lean4Lean.OnCtx.weak'_inv` | 271 | thm | master |

### `Lean4Lean.Verify.Environment` (6)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.addAxiom.WF` | 11 | thm | master |
| `Lean4Lean.addDefinition.WF` | 28 | thm | master |
| `Lean4Lean.addTheorem.WF` | 75 | thm | master |
| `Lean4Lean.addOpaque.WF` | 91 | thm | master |
| `Lean4Lean.addMutual.WF` | 120 | thm | master |
| `Lean4Lean.addDecl.WF` | 194 | thm | master/mixed |

### `Lean4Lean.Verify.Environment.Checker` (9)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.checkConstantValBody.WF` | 53 | thm | master |
| `Lean4Lean.checkConstantValCore.WF` | 78 | thm | master |
| `Lean4Lean.checkConstantVal.WF` | 94 | thm | master |
| `Lean4Lean.checkBodyCore.WF` | 109 | thm | master |
| `Lean4Lean.checkBody.WF` | 136 | thm | master |
| `Lean4Lean.checkTheorem.WF` | 155 | thm | master |
| `Lean4Lean.checkDefinitionBody.WF` | 173 | thm | master |
| `Lean4Lean.checkDefinition.WF` | 191 | thm | master |
| `Lean4Lean.checkOpaque.WF` | 212 | thm | master |

### `Lean4Lean.Verify.Environment.Lemmas` (6)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.VEnv.HasType.mkApps_inv_head` | 958 | thm | trproj |
| `Lean4Lean.VEnv.IsDefEqU.beta_app` | 969 | thm | trproj |
| `Lean4Lean.VEnv.IsDefEqU.mkApps_congr` | 979 | thm | trproj |
| `Lean4Lean.VEnv.IsDefEqU.betaN` | 992 | thm | trproj |
| `Lean4Lean.TrEnv.proj_defeq` | 1013 | thm | trproj |
| `Lean4Lean.TrExpr.mkAppList` | 1166 | thm | trproj |

### `Lean4Lean.Verify.Environment.Primitive` (1)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.Primitive.checkDef.WF` | 27 | thm | master |

### `Lean4Lean.Verify.Environment.Primitive.Basic` (35)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.TypeChecker.M.WF.withNatProbe` | 61 | thm | master/mixed |
| `Lean4Lean.TypeChecker.M.WF.withBoolProbe` | 75 | thm | master/mixed |
| `Lean4Lean.VEnv.IsDefEqU.appN` | 444 | thm | master/mixed |
| `Lean4Lean.VEnv.IsDefEqU.appN'` | 561 | thm | master |
| `Lean4Lean.VEnv.IsDefEqU.app_arg` | 592 | thm | master |
| `Lean4Lean.VExpr.lams_appN` | 611 | thm | master/mixed |
| `Lean4Lean.VExpr.lams_appN'` | 650 | thm | master/mixed |
| `Lean4Lean.TypeChecker.VContext.Ext.natBinLitTr` | 750 | thm | master/mixed |
| `Lean4Lean.lambdaTelescope.loop.WF` | 899 | thm | master |
| `Lean4Lean.lambdaTelescope.WF` | 955 | thm | master |
| `Lean4Lean.VExpr.WF.app_inv'` | 983 | thm | master/mixed |
| `Lean4Lean.VExpr.WF.betaU` | 1002 | thm | master/mixed |
| `Lean4Lean.Primitive.hNatT` | 1070 | thm | master/mixed |
| `Lean4Lean.Primitive.trNat` | 1076 | def | master/mixed |
| `Lean4Lean.Primitive.predb` | 1080 | def | master/mixed |
| `Lean4Lean.Primitive.addb` | 1087 | def | master/mixed |
| `Lean4Lean.Primitive.divb` | 1091 | def | master/mixed |
| `Lean4Lean.Primitive.modb` | 1095 | def | master/mixed |
| `Lean4Lean.Primitive.mulb` | 1099 | def | master/mixed |
| `Lean4Lean.Primitive.natCod` | 1103 | def | master/mixed |
| `Lean4Lean.Primitive.natCod1` | 1110 | def | master/mixed |
| `Lean4Lean.Primitive.boolCod` | 1114 | def | master/mixed |
| `Lean4Lean.Primitive.trBool` | 1120 | def | master/mixed |
| `Lean4Lean.Primitive.boolOp2Ty` | 1126 | def | master |
| `Lean4Lean.Primitive.boolOp2Ty_tgt` | 1139 | thm | master |
| `Lean4Lean.Primitive.bitwiseTy` | 1142 | def | master |
| `Lean4Lean.Primitive.Data.mkTyEqBitwise` | 1162 | thm | master |
| `Lean4Lean.Primitive.Data.mkTyEq` | 1174 | thm | master/mixed |
| `Lean4Lean.Primitive.Data.mkTyEq1` | 1187 | thm | master/mixed |
| `Lean4Lean.Primitive.Data.mkResult` | 1213 | thm | master |
| `Lean4Lean.Primitive.Data.mkResult1` | 1230 | thm | master |
| `Lean4Lean.Primitive.Data.mkResultBool` | 1244 | thm | master |
| `Lean4Lean.Primitive.Data.mkResultBitwise` | 1258 | thm | master/mixed |
| `Lean4Lean.Primitive.goArgs` | 1322 | thm | master/mixed |
| `Lean4Lean.Primitive.natFuelRec` | 1353 | thm | master |

### `Lean4Lean.Verify.Environment.Primitive.Bitwise` (3)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.Primitive.boolOp2Ty.congr_simp` | -1 | thm | unknown(no-range) |
| `Lean4Lean.Primitive.boolOp2_apply` | 10 | thm | master |
| `Lean4Lean.Primitive.checkNatBitwise.WF` | 31 | thm | master/mixed |

### `Lean4Lean.Verify.Environment.Primitive.Clauses` (15)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.Primitive.checkNatAdd.WF` | 20 | thm | master/mixed |
| `Lean4Lean.Primitive.checkNatPred.WF` | 57 | thm | master |
| `Lean4Lean.Primitive.checkNatSub.WF` | 79 | thm | master/mixed |
| `Lean4Lean.Primitive.checkNatMul.WF` | 108 | thm | master/mixed |
| `Lean4Lean.Primitive.checkNatPow.WF` | 137 | thm | master/mixed |
| `Lean4Lean.Primitive.checkNatBoolCases.WF` | 168 | thm | master |
| `Lean4Lean.Primitive.checkNatBEq.WF` | 206 | thm | master |
| `Lean4Lean.Primitive.checkNatBLE.WF` | 215 | thm | master |
| `Lean4Lean.Primitive.checkNatLAnd.WF` | 223 | thm | master/mixed |
| `Lean4Lean.Primitive.checkNatLOr.WF` | 250 | thm | master/mixed |
| `Lean4Lean.Primitive.checkNatXor.WF` | 278 | thm | master/mixed |
| `Lean4Lean.Primitive.checkNatShiftLeft.WF` | 311 | thm | master/mixed |
| `Lean4Lean.Primitive.checkNatShiftRight.WF` | 339 | thm | master/mixed |
| `Lean4Lean.Primitive.checkCharOfNat.WF` | 369 | thm | master/mixed |
| `Lean4Lean.Primitive.checkStringOfList.WF` | 392 | thm | master/mixed |

### `Lean4Lean.Verify.Environment.Primitive.Condition` (24)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.Primitive.Reflection.WF.ToDecT.spine` | 76 | thm | master |
| `Lean4Lean.Primitive.TrExprS.ofClosed` | 527 | thm | master |
| `Lean4Lean.Primitive.VEnv.IsDefEqU.polyProj` | 991 | thm | master |
| `Lean4Lean.Primitive.TrExprS.reflIteType` | 1022 | thm | master |
| `Lean4Lean.Primitive.TrExprS.reflDiteType` | 1101 | thm | master |
| `Lean4Lean.Primitive.Reflection.WF.genTele` | 1219 | thm | master |
| `Lean4Lean.Primitive.Reflection.WF.genTeleT` | 1239 | thm | master/mixed |
| `Lean4Lean.Primitive.Reflection.WF.genPH` | 1259 | thm | master/mixed |
| `Lean4Lean.Primitive.Reflection.check.WF` | 1319 | thm | master |
| `Lean4Lean.Primitive.Reflection.WF.ITE_T.toDecT` | 1367 | thm | master |
| `Lean4Lean.Primitive.Reflection.checkITE.WF` | 1377 | thm | master/mixed |
| `Lean4Lean.Primitive.Reflection.WF.DITE_T.toDecT` | 1607 | thm | master |
| `Lean4Lean.Primitive.Reflection.checkNatDITE.WF` | 1614 | thm | master/mixed |
| `Lean4Lean.Primitive.Condition.WF.reflect_dite` | 1992 | thm | master/mixed |
| `Lean4Lean.Primitive.Condition.check.gadget_types` | 2108 | thm | master |
| `Lean4Lean.Primitive.Condition.check.gadget_pieces` | 2222 | thm | master |
| `Lean4Lean.Primitive.Condition.WF.natEq_args` | 2473 | thm | master |
| `Lean4Lean.Primitive.Condition.WF.natEq_iteEval` | 2492 | thm | master |
| `Lean4Lean.Primitive.Condition.WF.natEq_diteEval` | 2505 | thm | master |
| `Lean4Lean.Primitive.Condition.WF.natEq_decideTr` | 2518 | thm | master |
| `Lean4Lean.Primitive.Condition.WF.reflect_diteEval` | 2548 | thm | master |
| `Lean4Lean.Primitive.Condition.WF.reflect_iteEval` | 2619 | thm | master |
| `Lean4Lean.Primitive.Condition.WF.reflect_ite` | 2697 | thm | master/mixed |
| `Lean4Lean.Primitive.Condition.check.WF` | 2760 | thm | master/mixed |

### `Lean4Lean.Verify.Environment.Primitive.DivMod` (4)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.Primitive.natCod.congr_simp` | -1 | thm | unknown(no-range) |
| `Lean4Lean.Primitive.checkNatFuelRec.WF` | 10 | thm | master/mixed |
| `Lean4Lean.Primitive.checkNatMod.WF` | 273 | thm | master/mixed |
| `Lean4Lean.Primitive.checkNatDiv.WF` | 439 | thm | master/mixed |

### `Lean4Lean.Verify.Environment.Primitive.Gcd` (1)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.Primitive.checkNatGcd.WF` | 10 | thm | master/mixed |

### `Lean4Lean.Verify.Environment.Primitive.Recursion` (8)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.Primitive.ProbeBundle.packAty` | 105 | thm | master |
| `Lean4Lean.Primitive.ProbeBundle.GoConverges.succ` | 256 | thm | master |
| `Lean4Lean.Primitive.ProbeBundle.GoConverges.all` | 272 | thm | master |
| `Lean4Lean.Primitive.ProbeBundle.NatFixUnfold.reflects` | 278 | thm | master |
| `Lean4Lean.Primitive.ProbeBundle.probe.WF` | 319 | thm | master/mixed |
| `Lean4Lean.Primitive.unfoldNatWellFounded.WF'` | 554 | thm | master |
| `Lean4Lean.Primitive.unfoldNatWellFounded.WF` | 1707 | thm | master |
| `Lean4Lean.Primitive.unfoldNatWellFounded.WF₂` | 1744 | thm | master |

### `Lean4Lean.Verify.EquivManager` (3)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.EquivManager.RelevantEq.uniq` | 81 | thm | master |
| `Lean4Lean.EquivManager.IsDefEqE.trExpr` | 119 | thm | master |
| `Lean4Lean.EquivManager.IsDefEqE.uniq` | 163 | thm | master |

### `Lean4Lean.Verify.Primitive` (16)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.TrExprS.bitwiseOperand` | 206 | thm | master |
| `Lean4Lean.VEnv.IsDefEqU.appDF'` | 242 | thm | master |
| `Lean4Lean.VEnv.IsDefEqU.app_arg'` | 250 | thm | master |
| `Lean4Lean.VEnv.IsDefEqU.app_fun'` | 256 | thm | master |
| `Lean4Lean.VEnv.ReflectsNatNatNat'.of_unary_step_equations` | 262 | thm | master/mixed |
| `Lean4Lean.VEnv.ReflectsNatNatNat'.of_binary_step_equations` | 306 | thm | master/mixed |
| `Lean4Lean.VEnv.ReflectsNatNatNat'.of_first_arg_step_equations` | 347 | thm | master/mixed |
| `Lean4Lean.VEnv.ReflectsNatNatBool'.of_constructor_cases` | 382 | thm | master/mixed |
| `Lean4Lean.VEnv.ReflectsBoolBoolBool'.of_left_cases` | 425 | thm | master/mixed |
| `Lean4Lean.VEnv.ReflectsNatNat'.of_pred_equations` | 455 | thm | master/mixed |
| `Lean4Lean.VEnv.ReflectsNatNatNat'.congr_head` | 472 | thm | master |
| `Lean4Lean.VEnv.ReflectsNatNatBool'.congr_head` | 487 | thm | master |
| `Lean4Lean.VEnv.ReflectsNatNat'.congr_head` | 498 | thm | master |
| `Lean4Lean.VEnv.ReflectsNatNatNat'.toConst` | 548 | thm | master/mixed |
| `Lean4Lean.VEnv.ReflectsNatNatBool'.toConst` | 569 | thm | master/mixed |
| `Lean4Lean.VEnv.ReflectsNatNat'.toConst` | 582 | thm | master/mixed |

### `Lean4Lean.Verify.TypeChecker` (14)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.TypeChecker.Methods.withFuel.WF` | 48 | thm | master |
| `Lean4Lean.TypeChecker.RecM.WF.run` | 61 | thm | master |
| `Lean4Lean.TypeChecker.whnf.WF` | 184 | thm | master |
| `Lean4Lean.TypeChecker.whnfCore.WF` | 189 | thm | master |
| `Lean4Lean.TypeChecker.unfoldDefinition.WF` | 193 | thm | master |
| `Lean4Lean.TypeChecker.inferType.WF'` | 202 | thm | master |
| `Lean4Lean.TypeChecker.inferType.WF` | 210 | thm | master |
| `Lean4Lean.TypeChecker.checkType.WF` | 214 | thm | master |
| `Lean4Lean.TypeChecker.isDefEq.WF` | 218 | thm | master |
| `Lean4Lean.TypeChecker.isProp.WF` | 223 | thm | master |
| `Lean4Lean.TypeChecker.ensureSort.WF` | 227 | thm | master |
| `Lean4Lean.TypeChecker.ensureForall.WF` | 231 | thm | master |
| `Lean4Lean.TypeChecker.ensureType.WF'` | 236 | thm | master |
| `Lean4Lean.TypeChecker.ensureType.WF` | 249 | thm | master |

### `Lean4Lean.Verify.TypeChecker.Basic` (9)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.TypeChecker.RecM.WF.withLocalDecl` | 439 | thm | master |
| `Lean4Lean.TypeChecker.M.WF.withLocalDecl` | 487 | thm | master |
| `Lean4Lean.TypeChecker.RecM.WF.withLetDecl` | 537 | thm | master |
| `Lean4Lean.TypeChecker.MLCtx.WF.mkForall_tr` | 709 | thm | master |
| `Lean4Lean.TypeChecker.MLCtx.WF.mkLambda_tr` | 755 | thm | master |
| `Lean4Lean.TypeChecker.Inner.inferType.WF` | 947 | thm | master |
| `Lean4Lean.TypeChecker.Inner.inferType.WF_uniq` | 957 | thm | master |
| `Lean4Lean.TypeChecker.Inner.unfoldDefinitionCore.WF` | 983 | thm | master |
| `Lean4Lean.TypeChecker.Inner.unfoldDefinition.WF` | 1017 | thm | master |

### `Lean4Lean.Verify.TypeChecker.InferType` (14)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.TypeChecker.Inner.ensureForallCore.WF'` | 21 | thm | master |
| `Lean4Lean.TypeChecker.Inner.inferConstant.WF` | 47 | thm | master |
| `Lean4Lean.TypeChecker.Inner.inferLambda.loop.WF` | 95 | thm | master |
| `Lean4Lean.TypeChecker.Inner.inferLambda.WF` | 170 | thm | master |
| `Lean4Lean.TypeChecker.Inner.inferForall.loop.WF` | 178 | thm | master |
| `Lean4Lean.TypeChecker.Inner.inferForall.WF` | 230 | thm | master |
| `Lean4Lean.TypeChecker.Inner.inferApp.loop.WF` | 236 | thm | master |
| `Lean4Lean.TypeChecker.Inner.inferApp.WF` | 279 | thm | master |
| `Lean4Lean.TypeChecker.Inner.inferLet.loop.WF` | 291 | thm | master |
| `Lean4Lean.TypeChecker.Inner.inferLet.WF` | 379 | thm | master |
| `Lean4Lean.TypeChecker.Inner.inferProj.WF_struct` | 388 | thm | trproj |
| `Lean4Lean.TypeChecker.Inner.inferProj.WF` | 400 | thm | trproj/mixed |
| `Lean4Lean.TypeChecker.Inner.infer_literal` | 417 | thm | master |
| `Lean4Lean.TypeChecker.Inner.inferType'.WF` | 432 | thm | master/mixed |

### `Lean4Lean.Verify.TypeChecker.IsDefEq` (22)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.TypeChecker.Inner.isDefEqLambda.WF` | 9 | thm | master |
| `Lean4Lean.TypeChecker.Inner.isDefEqForall.WF` | 79 | thm | master |
| `Lean4Lean.TypeChecker.Inner.quickIsDefEq.WF` | 149 | thm | master |
| `Lean4Lean.TypeChecker.Inner.isDefEqArgs.WF` | 182 | thm | master |
| `Lean4Lean.TypeChecker.Inner.tryEtaExpansionCore.WF` | 202 | thm | master |
| `Lean4Lean.TypeChecker.Inner.tryEtaExpansion.WF` | 217 | thm | master |
| `Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF` | 225 | thm | master |
| `Lean4Lean.TypeChecker.Inner.tryEtaStruct.WF` | 229 | thm | master |
| `Lean4Lean.TypeChecker.Inner.isDefEqApp.WF` | 237 | thm | master |
| `Lean4Lean.TypeChecker.Inner.isDefEqApp.WF.loop.WF` | 247 | thm | master |
| `Lean4Lean.TypeChecker.Inner.getSortLevel.WF` | 282 | thm | master |
| `Lean4Lean.TypeChecker.Inner.isProp.WF` | 291 | thm | master |
| `Lean4Lean.TypeChecker.Inner.isDefEqProofIrrel.WF` | 297 | thm | master |
| `Lean4Lean.TypeChecker.ReductionStatus.WF.defeq` | 336 | thm | master |
| `Lean4Lean.TypeChecker.Inner.lazyDeltaReductionStep.WF` | 346 | thm | master |
| `Lean4Lean.TypeChecker.Inner.isNatZero_wf` | 403 | thm | master |
| `Lean4Lean.TypeChecker.Inner.isDefEqOffset.WF` | 424 | thm | master |
| `Lean4Lean.TypeChecker.Inner.lazyDeltaReduction.loop.WF` | 439 | thm | master |
| `Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF` | 486 | thm | master |
| `Lean4Lean.TypeChecker.Inner.lazyDeltaProjReduction.finish.WF` | 490 | thm | master |
| `Lean4Lean.TypeChecker.Inner.lazyDeltaProjReduction.loop.WF` | 505 | thm | master |
| `Lean4Lean.TypeChecker.Inner.isDefEqCore'.WF` | 528 | thm | master |

### `Lean4Lean.Verify.TypeChecker.Reduce` (6)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.TypeChecker.Inner.rawNatLitExt?.WF` | 12 | thm | master |
| `Lean4Lean.TypeChecker.Inner.reduceBinNatOpG.WF` | 28 | thm | master |
| `Lean4Lean.TypeChecker.Inner.reduceBinNatPred.WF` | 59 | thm | master |
| `Lean4Lean.TypeChecker.Inner.reduceNat.WF` | 89 | thm | master |
| `Lean4Lean.TypeChecker.Inner.reduceProjCore.WF` | 143 | thm | master |
| `Lean4Lean.TypeChecker.Inner.reduceProj.WF` | 147 | thm | master |

### `Lean4Lean.Verify.TypeChecker.WHNF` (5)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.TypeChecker.Inner.inductiveReduceRecCore.WF` | 6 | thm | trproj |
| `Lean4Lean.TypeChecker.Inner.reduceRecursor.WF` | 147 | thm | master |
| `Lean4Lean.TypeChecker.Inner.whnfFVar.WF` | 151 | thm | master |
| `Lean4Lean.TypeChecker.Inner.whnfCore'.WF` | 166 | thm | master |
| `Lean4Lean.TypeChecker.Inner.whnf'.WF` | 269 | thm | master |

### `Lean4Lean.Verify.Typing.ConditionallyTyped` (3)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.ConditionallyTyped.weakN_inv` | 18 | thm | master |
| `Lean4Lean.ConditionallyHasType.weakN_inv` | 56 | thm | master |
| `Lean4Lean.ConditionallyWHNF.weakN_inv` | 110 | thm | master |

### `Lean4Lean.Verify.Typing.Lemmas` (29)

| declaration | line | kind | attr |
|---|---|---|---|
| `Lean4Lean.VLocalDecl.weak'_iff` | 270 | thm | master |
| `Lean4Lean.VLocalDecl.weakN_iff` | 276 | thm | master |
| `Lean4Lean.VLCtx.FVLift'.wf` | 365 | thm | master |
| `Lean4Lean.VLCtx.FVLift.wf` | 438 | thm | master |
| `Lean4Lean.VLCtx.BVLift.wf` | 474 | thm | master |
| `Lean4Lean.HasType.skips` | 738 | thm | master |
| `Lean4Lean.TrProj.weak'_inv` | 742 | thm | trproj/mixed |
| `Lean4Lean.TrProj.defeqDFC` | 749 | thm | trproj/mixed |
| `Lean4Lean.TrExpr.defeq` | 967 | thm | master |
| `Lean4Lean.TrExpr.app` | 971 | thm | master |
| `Lean4Lean.TrProj.uniq` | 984 | thm | trproj/mixed |
| `Lean4Lean.TrExprS.uniq` | 998 | thm | master |
| `Lean4Lean.TrExpr.uniq` | 1034 | thm | master |
| `Lean4Lean.TrExprS.defeqDFC` | 1042 | thm | master |
| `Lean4Lean.TrExprS.defeqDFC'` | 1100 | thm | master |
| `Lean4Lean.TrExpr.lam` | 1104 | thm | master |
| `Lean4Lean.TrExpr.forallE` | 1119 | thm | master |
| `Lean4Lean.TrExpr.letE` | 1137 | thm | master |
| `Lean4Lean.TrExpr.proj` | 1162 | thm | master/mixed |
| `Lean4Lean.TrExprS.weakFV'_inv` | 1169 | thm | master |
| `Lean4Lean.TrExprS.weakFV_inv` | 1245 | thm | master |
| `Lean4Lean.TrExpr.inst` | 1352 | thm | master |
| `Lean4Lean.TrExpr.inst_let` | 1441 | thm | master |
| `Lean4Lean.TrExprS.instL` | 1676 | thm | master |
| `Lean4Lean.TrExpr.instL` | 1716 | thm | master |
| `Lean4Lean.TrExpr.beta` | 2198 | thm | master |
| `Lean4Lean.TrExpr.cheapBetaReduce` | 2224 | thm | master |
| `Lean4Lean.TrExpr.rebuild_mkAppRevList` | 2272 | thm | master |
| `Lean4Lean.TrExpr.rebuild_mkAppList` | 2282 | thm | master |

## 3. Declared `axiom` constants in the project (110)


**`Lean4Lean.Experimental.MoreStepIndexed`** (8)

- `Lean4Lean.SExpr.InferTypeN` (line 42)
- `Lean4Lean.SExpr.InferTypeN.mono` (line 43)
- `Lean4Lean.SExpr.NormalEqN` (line 44)
- `Lean4Lean.SExpr.NormalEqN.mono` (line 45)
- `Lean4Lean.SExpr.ParRedN` (line 40)
- `Lean4Lean.SExpr.ParRedN.mono` (line 41)
- `Lean4Lean.SExpr.WHRedUpToN` (line 38)
- `Lean4Lean.SExpr.WHRedUpToN.mono` (line 39)

**`Lean4Lean.Experimental.SExpr`** (1)

- `Lean4Lean.SExpr.Params.extra_pat` (line 614)

**`Lean4Lean.Experimental.StepIndexed`** (3)

- `Lean4Lean.SExpr.IsTy` (line 59)
- `Lean4Lean.SExpr.IsTy.def` (line 62)
- `Lean4Lean.SExpr.IsTyN` (line 60)

**`Lean4Lean.Experimental.Thierry`** (38)

- `D` (line 11)
- `D.LE` (line 23)
- `D.LE.antisymm` (line 28)
- `D.LE.bot` (line 43)
- `D.LE.lam` (line 46)
- `D.LE.pi` (line 47)
- `D.LE.rfl` (line 45)
- `D.LE.trans` (line 29)
- `D.U` (line 20)
- `D.app` (line 39)
- `D.app_lam` (line 41)
- `D.bot` (line 19)
- `D.lam` (line 21)
- `D.lam_bot` (line 37)
- `D.pi` (line 22)
- `DF.OK` (line 12)
- `DF.mono` (line 32)
- `FinElem.LE.unfold` (line n/a — filtered as internal)
- `FinElem.embed` (line 58)
- `FinElem.embed_U` (line 77)
- `FinElem.embed_bot` (line 75)
- `FinFun.embed` (line 59)
- `FinFun.embed_bot` (line 76)
- `FinFun.eval` (line 68)
- `FinMut.LE.cons` (line 96)
- `HasType` (line 170)
- `HasType.U` (line 171)
- `WHRedTS.uniq_pi` (line 181)
- `bot_apply` (line 99)
- `eval_cons` (line 97)
- `eval_embed` (line 98)
- `mySorry` (line 9)
- `proj` (line 126)
- `proj_U_U` (line 127)
- `proj_U_pi` (line 128)
- `proj_le` (line 132)
- `proj_pi` (line 129)
- `proj_proj` (line 133)

**`Lean4Lean.Experimental.Thierry2`** (19)

- `D.LE.embed` (line 544)
- `D.LE.lam` (line 541)
- `D.LE.pi` (line 542)
- `D.app_lam` (line 539)
- `DF.LE.embed` (line 545)
- `DF.mk'_app` (line 422)
- `DefEq` (line 607)
- `DefEq.U` (line 608)
- `DefEq.left` (line 609)
- `Shape.embed_U` (line 547)
- `ShapeFun.embed` (line 401)
- `WHRedTS.uniq_pi` (line 619)
- `mySorry` (line 9)
- `proj` (line 549)
- `proj_U_U` (line 550)
- `proj_U_pi` (line 551)
- `proj_le` (line 555)
- `proj_pi` (line 552)
- `proj_proj` (line 556)

**`Lean4Lean.PtrEq`** (2)

- `Lean4Lean.ptrEqConstantInfo_eq` (line 22)
- `Lean4Lean.ptrEqExpr_eq` (line 17)

**`Lean4Lean.Verify.Axioms`** (32)

- `Lean.Expr.abstractRange_eq` (line 466)
- `Lean.Expr.abstract_eq` (line 462)
- `Lean.Expr.equal_eq` (line 507)
- `Lean.Expr.eqv_eq` (line 504)
- `Lean.Expr.hasLooseBVar_eq` (line 484)
- `Lean.Expr.instantiate1_eq` (line 420)
- `Lean.Expr.instantiateRange_eq` (line 435)
- `Lean.Expr.instantiateRevRange_eq` (line 439)
- `Lean.Expr.instantiateRev_eq` (line 431)
- `Lean.Expr.instantiate_eq` (line 427)
- `Lean.Expr.liftLooseBVars_eq` (line 381)
- `Lean.Expr.looseBVarRange_eq` (line 358)
- `Lean.Expr.lowerLooseBVars_eq` (line 401)
- `Lean.Expr.mkAppData_eq` (line 340)
- `Lean.Expr.mkData_eq` (line 323)
- `Lean.Expr.replace_eq` (line 362)
- `Lean.Level.hasMVar_eq` (line 287)
- `Lean.Level.hasParam_eq` (line 277)
- `Lean.Level.instLawfulBEqLevel` (line 291)
- `Lean.Level.isExplicitSubsumedAux_eq` (line 193)
- `Lean.Level.mkData_eq` (line 267)
- `Lean.Level.mkLevelIMaxCore_eq` (line 302)
- `Lean.Level.mkMaxAux_eq` (line 176)
- `Lean.Level.normalize_eq` (line 255)
- `Lean.Level.skipExplicit_eq` (line 184)
- `Lean.PersistentArray.toList'_push` (line 38)
- `Lean.PersistentHashMap.WF.find?_eq` (line 77)
- `Lean.PersistentHashMap.WF.toList'_insert` (line 71)
- `Lean.PersistentHashMap.findAux_isSome` (line 82)
- `Lean.Syntax.structEq_eq` (line 113)
- `Std.TreeMap.all_eq_all_toList` (line 9)
- `Std.TreeMap.any_eq_any_toList` (line 13)

**`Lean4Lean.Verify.Expr`** (4)

- `Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7` (line n/a — filtered as internal)
- `Lean.Expr.mkAppData_looseBVarRange._native.bv_decide.ax_1_8` (line n/a — filtered as internal)
- `Lean.Expr.mkData_flags._native.bv_decide.ax_1_12` (line n/a — filtered as internal)
- `Lean.Expr.mkData_looseBVarRange._native.bv_decide.ax_1_9` (line n/a — filtered as internal)

**`Lean4Lean.Verify.Level`** (3)

- `Lean.Level.mkData_depth._native.bv_decide.ax_1_9` (line n/a — filtered as internal)
- `Lean.Level.mkData_hasMVar._native.bv_decide.ax_1_8` (line n/a — filtered as internal)
- `Lean.Level.mkData_hasParam._native.bv_decide.ax_1_8` (line n/a — filtered as internal)

## 4. `opaque` constants (12)

- `Lean4Lean.AddInductive.getElimLevel.loop` — `Lean4Lean.Inductive.Add` (line 284)
- `Lean4Lean.ElimNestedInductive.mkUniqueName.loop` — `Lean4Lean.Inductive.Add` (line 576)
- `Lean4Lean.Primitive.instToExprSyntax_lean4Lean.toExpr` — `Lean4Lean.Primitive` (line 26)
- `Lean4Lean.ptrEqConstantInfo` — `Lean4Lean.PtrEq` (line 19)
- `Lean4Lean.ptrEqConstantInfo.unsafe_impl_2` — `Lean4Lean.PtrEq` (line -1)
- `Lean4Lean.ptrEqExpr` — `Lean4Lean.PtrEq` (line 6)
- `Lean4Lean.ptrEqExpr.unsafe_impl_2` — `Lean4Lean.PtrEq` (line -1)
- `Lean4Lean.Replay.replayConstant` — `Lean4Lean.Replay` (line 161)
- `Lean4Lean.Replay.replayConstants` — `Lean4Lean.Replay` (line 224)
- `Mathlib.instToExprSyntax_lean4Lean.toExpr` — `Lean4Lean.Std.ToExpr` (line 36)
- `Lean4Lean.Tests.KernelHardening.deepNat` — `Lean4Lean.Tests.KernelHardening` (line 124)
- `Lean4Lean.Meta.ofExpr` — `Lean4Lean.Theory.Meta` (line 36)

## 5. Non-standard axioms reachable from anything in the project

Anything other than `propext`, `Classical.choice`, `Quot.sound`. Count = number of user-level declarations whose `collectAxioms` result contains it.

| axiom | #decls | where declared |
|---|---|---|
| `sorryAx` | 629 | Lean core |
| `Lean.PersistentHashMap.WF.find?_eq` | 229 | `Lean4Lean.Verify.Axioms` |
| `Lean.PersistentHashMap.WF.toList'_insert` | 229 | `Lean4Lean.Verify.Axioms` |
| `Lean.PersistentArray.toList'_push` | 154 | `Lean4Lean.Verify.Axioms` |
| `Lean.Level.instLawfulBEqLevel` | 152 | `Lean4Lean.Verify.Axioms` |
| `Lean.PersistentHashMap.findAux_isSome` | 135 | `Lean4Lean.Verify.Axioms` |
| `Lean.Expr.eqv_eq` | 120 | `Lean4Lean.Verify.Axioms` |
| `Lean.Syntax.structEq_eq` | 100 | `Lean4Lean.Verify.Axioms` |
| `Lean.Expr.mkData_eq` | 92 | `Lean4Lean.Verify.Axioms` |
| `_private.Lean4Lean.Verify.Expr.0.Lean.Expr.mkData_flags._native.bv_decide.ax_1_12` | 90 | auto-generated (`bv_decide` native LRAT certificate) |
| `Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7` | 90 | `Lean4Lean.Verify.Expr` |
| `Lean.Level.hasParam_eq` | 88 | `Lean4Lean.Verify.Axioms` |
| `Lean.Expr.mkAppData_eq` | 87 | `Lean4Lean.Verify.Axioms` |
| `Lean.Expr.instantiate_eq` | 81 | `Lean4Lean.Verify.Axioms` |
| `Lean.Level.hasMVar_eq` | 81 | `Lean4Lean.Verify.Axioms` |
| `Lean.Expr.abstractRange_eq` | 80 | `Lean4Lean.Verify.Axioms` |
| `Lean.Expr.abstract_eq` | 80 | `Lean4Lean.Verify.Axioms` |
| `Lean.Expr.hasLooseBVar_eq` | 80 | `Lean4Lean.Verify.Axioms` |
| `Lean.Expr.lowerLooseBVars_eq` | 80 | `Lean4Lean.Verify.Axioms` |
| `Lean.Expr.instantiateRev_eq` | 79 | `Lean4Lean.Verify.Axioms` |
| `Lean.Level.isExplicitSubsumedAux_eq` | 75 | `Lean4Lean.Verify.Axioms` |
| `Lean.Expr.looseBVarRange_eq` | 74 | `Lean4Lean.Verify.Axioms` |
| `Lean.Level.normalize_eq` | 74 | `Lean4Lean.Verify.Axioms` |
| `Std.TreeMap.all_eq_all_toList` | 74 | `Lean4Lean.Verify.Axioms` |
| `D` | 73 | `Lean4Lean.Experimental.Thierry` |
| `Lean.Expr.replace_eq` | 73 | `Lean4Lean.Verify.Axioms` |
| `Lean4Lean.ptrEqExpr_eq` | 65 | `Lean4Lean.PtrEq` |
| `Lean4Lean.ptrEqConstantInfo_eq` | 63 | `Lean4Lean.PtrEq` |
| `Lean.Expr.instantiate1_eq` | 62 | `Lean4Lean.Verify.Axioms` |
| `Lean.Expr.instantiateRevRange_eq` | 62 | `Lean4Lean.Verify.Axioms` |
| `Lean.Expr.instantiateRange_eq` | 61 | `Lean4Lean.Verify.Axioms` |
| `DF.OK` | 57 | `Lean4Lean.Experimental.Thierry` |
| `proj` | 52 | `Lean4Lean.Experimental.Thierry` |
| `D.LE` | 38 | `Lean4Lean.Experimental.Thierry` |
| `FinFun.eval` | 33 | `Lean4Lean.Experimental.Thierry` |
| `FinElem.embed` | 31 | `Lean4Lean.Experimental.Thierry` |
| `FinFun.embed` | 28 | `Lean4Lean.Experimental.Thierry` |
| `mySorry` | 25 | `Lean4Lean.Experimental.Thierry` |
| `D.bot` | 20 | `Lean4Lean.Experimental.Thierry` |
| `DefEq` | 20 | `Lean4Lean.Experimental.Thierry2` |
| `Std.TreeMap.any_eq_any_toList` | 19 | `Lean4Lean.Verify.Axioms` |
| `D.lam` | 18 | `Lean4Lean.Experimental.Thierry` |
| `D.U` | 18 | `Lean4Lean.Experimental.Thierry` |
| `HasType` | 18 | `Lean4Lean.Experimental.Thierry` |
| `D.pi` | 17 | `Lean4Lean.Experimental.Thierry` |
| `D.app` | 16 | `Lean4Lean.Experimental.Thierry` |
| `Lean4Lean.SExpr.Params.extra_pat` | 14 | `Lean4Lean.Experimental.SExpr` |
| `WHRedTS.uniq_pi` | 12 | `Lean4Lean.Experimental.Thierry` |
| `DefEq.left` | 9 | `Lean4Lean.Experimental.Thierry2` |
| `D.LE.bot` | 8 | `Lean4Lean.Experimental.Thierry` |
| `bot_apply` | 7 | `Lean4Lean.Experimental.Thierry` |
| `D.LE.trans` | 7 | `Lean4Lean.Experimental.Thierry` |
| `FinElem.embed_bot` | 7 | `Lean4Lean.Experimental.Thierry` |
| `FinFun.embed_bot` | 7 | `Lean4Lean.Experimental.Thierry` |
| `DefEq.U` | 6 | `Lean4Lean.Experimental.Thierry2` |
| `D.LE.embed` | 6 | `Lean4Lean.Experimental.Thierry2` |
| `DF.mono` | 6 | `Lean4Lean.Experimental.Thierry` |
| `eval_embed` | 6 | `Lean4Lean.Experimental.Thierry` |
| `HasType.U` | 6 | `Lean4Lean.Experimental.Thierry` |
| `Lean4Lean.SExpr.NormalEqN` | 6 | `Lean4Lean.Experimental.MoreStepIndexed` |
| `Lean4Lean.SExpr.ParRedN` | 6 | `Lean4Lean.Experimental.MoreStepIndexed` |
| `FinElem.LE.unfold` | 5 | `Lean4Lean.Experimental.Thierry` |
| `Lean4Lean.SExpr.InferTypeN` | 4 | `Lean4Lean.Experimental.MoreStepIndexed` |
| `Lean.Level.mkData_eq` | 4 | `Lean4Lean.Verify.Axioms` |
| `ShapeFun.embed` | 3 | `Lean4Lean.Experimental.Thierry2` |
| `Lean4Lean.SExpr.NormalEqN.mono` | 3 | `Lean4Lean.Experimental.MoreStepIndexed` |
| `Lean4Lean.SExpr.ParRedN.mono` | 3 | `Lean4Lean.Experimental.MoreStepIndexed` |
| `D.app_lam` | 2 | `Lean4Lean.Experimental.Thierry` |
| `D.LE.lam` | 2 | `Lean4Lean.Experimental.Thierry` |
| `D.LE.pi` | 2 | `Lean4Lean.Experimental.Thierry` |
| `Shape.embed_U` | 2 | `Lean4Lean.Experimental.Thierry2` |
| `FinElem.embed_U` | 2 | `Lean4Lean.Experimental.Thierry` |
| `Lean4Lean.SExpr.InferTypeN.mono` | 2 | `Lean4Lean.Experimental.MoreStepIndexed` |
| `Lean4Lean.SExpr.IsTy` | 2 | `Lean4Lean.Experimental.StepIndexed` |
| `Lean4Lean.SExpr.WHRedUpToN` | 2 | `Lean4Lean.Experimental.MoreStepIndexed` |
| `proj_le` | 2 | `Lean4Lean.Experimental.Thierry` |
| `proj_pi` | 2 | `Lean4Lean.Experimental.Thierry` |
| `proj_proj` | 2 | `Lean4Lean.Experimental.Thierry` |
| `proj_U_pi` | 2 | `Lean4Lean.Experimental.Thierry` |
| `proj_U_U` | 2 | `Lean4Lean.Experimental.Thierry` |
| `DF.LE.embed` | 1 | `Lean4Lean.Experimental.Thierry2` |
| `DF.mk'_app` | 1 | `Lean4Lean.Experimental.Thierry2` |
| `D.lam_bot` | 1 | `Lean4Lean.Experimental.Thierry` |
| `D.LE.antisymm` | 1 | `Lean4Lean.Experimental.Thierry` |
| `D.LE.rfl` | 1 | `Lean4Lean.Experimental.Thierry` |
| `eval_cons` | 1 | `Lean4Lean.Experimental.Thierry` |
| `FinMut.LE.cons` | 1 | `Lean4Lean.Experimental.Thierry` |
| `Lean4Lean.SExpr.IsTy.def` | 1 | `Lean4Lean.Experimental.StepIndexed` |
| `Lean4Lean.SExpr.IsTyN` | 1 | `Lean4Lean.Experimental.StepIndexed` |
| `Lean4Lean.SExpr.WHRedUpToN.mono` | 1 | `Lean4Lean.Experimental.MoreStepIndexed` |
| `Lean.Expr.equal_eq` | 1 | `Lean4Lean.Verify.Axioms` |
| `Lean.Expr.liftLooseBVars_eq` | 1 | `Lean4Lean.Verify.Axioms` |
| `Lean.Expr.mkAppData_looseBVarRange._native.bv_decide.ax_1_8` | 1 | `Lean4Lean.Verify.Expr` |
| `Lean.Expr.mkData_looseBVarRange._native.bv_decide.ax_1_9` | 1 | `Lean4Lean.Verify.Expr` |
| `Lean.Level.mkData_depth._native.bv_decide.ax_1_9` | 1 | `Lean4Lean.Verify.Level` |
| `Lean.Level.mkData_hasMVar._native.bv_decide.ax_1_8` | 1 | `Lean4Lean.Verify.Level` |
| `Lean.Level.mkData_hasParam._native.bv_decide.ax_1_8` | 1 | `Lean4Lean.Verify.Level` |
| `Lean.Level.mkLevelIMaxCore_eq` | 1 | `Lean4Lean.Verify.Axioms` |
| `Lean.Level.mkMaxAux_eq` | 1 | `Lean4Lean.Verify.Axioms` |
| `Lean.Level.skipExplicit_eq` | 1 | `Lean4Lean.Verify.Axioms` |

## 6. Declarations in the contributed files, with axiom footprint

Footprint codes: `std` = some subset of {`propext`, `Classical.choice`, `Quot.sound`}; `none` = axiom-free; `**SORRY**` = reaches `sorryAx`; `+`… = other named axioms (`Lean.PersistentHashMap.*`, `Lean.Expr.*_eq` etc. from `Verify/Axioms.lean`, i.e. the unproved model-vs-core-implementation bridge); `native-bv` = a `bv_decide` LRAT certificate axiom.

Line = start of the declaration range. `attr` = blame majority (`start=` tag and tag histogram are in `decls-attrib.tsv` column 9).


### `Lean4Lean/Theory/Proj.lean` — 49 declarations, 0 reach `sorryAx`

Per-line blame: trproj: 449/449 P.

| declaration | line | kind | attr | axioms |
|---|---|---|---|---|
| `Lean4Lean.VExpr.instPis.match_1.splitter` | -1 | def (private) | unknown(no-range) | std |
| `Lean4Lean.VExpr.fieldSelector` | 67 | def | trproj | none |
| `Lean4Lean.VExpr.instPis` | 73 | def | trproj | std |
| `Lean4Lean.VExpr.instFields` | 80 | def | trproj | none |
| `Lean4Lean.VExpr.projMotiveBodyOf` | 88 | def | trproj | std |
| `Lean4Lean.VExpr.projFnOf` | 94 | def | trproj | std |
| `Lean4Lean.VExpr.projFns` | 101 | def | trproj | std |
| `Lean4Lean.VExpr.projMotiveBody` | 113 | def | trproj | std |
| `Lean4Lean.VExpr.projFn` | 118 | def | trproj | std |
| `Lean4Lean.VExpr.projTy` | 125 | def | trproj | std |
| `Lean4Lean.VExpr.binderArity?` | 131 | def | trproj | std |
| `Lean4Lean.VExpr.projFn_eq` | 140 | thm | trproj | std |
| `Lean4Lean.VExpr.projFns_succ` | 143 | thm | trproj | std |
| `Lean4Lean.VExpr.projFns_length` | 146 | thm | trproj | std |
| `Lean4Lean.VExpr.projMotiveBody_zero` | 151 | thm | trproj | std |
| `Lean4Lean.VExpr.foldr_lam_subst` | 164 | thm | trproj | std |
| `Lean4Lean.VExpr.foldr_lam_inst` | 174 | thm | trproj | std |
| `Lean4Lean.VExpr.foldr_lam_instL` | 179 | thm | trproj | std |
| `Lean4Lean.VExpr.fieldSelector_subst` | 185 | thm | trproj | std |
| `Lean4Lean.VExpr.fieldSelector_instL` | 191 | thm | trproj | std |
| `Lean4Lean.VExpr.instFields_nil` | 205 | thm | trproj | none |
| `Lean4Lean.VExpr.instFields_cons` | 207 | thm | trproj | none |
| `Lean4Lean.VExpr.instFields_subst` | 210 | thm | trproj | std |
| `Lean4Lean.VExpr.instFields_instL` | 217 | thm | trproj | std |
| `Lean4Lean.VExpr.instPis_subst` | 226 | thm | trproj | std |
| `Lean4Lean.VExpr.instPis_lift'` | 235 | thm | trproj | std |
| `Lean4Lean.VExpr.instPis_inst` | 240 | thm | trproj | std |
| `Lean4Lean.VExpr.instPis_instL` | 245 | thm | trproj | std |
| `Lean4Lean.VExpr.instPis_ctorHeaded` | 254 | thm | trproj | std |
| `Lean4Lean.VExpr.instPis_piArity` | 263 | thm | trproj | std |
| `Lean4Lean.VExpr.projMotiveBodyOf_subst` | 276 | thm | trproj | std |
| `Lean4Lean.VExpr.projMotiveBodyOf_instL` | 286 | thm | trproj | std |
| `Lean4Lean.VExpr.projFnOf_subst` | 294 | thm | trproj | std |
| `Lean4Lean.VExpr.projFnOf_instL` | 304 | thm | trproj | std |
| `Lean4Lean.VExpr.projFns_subst` | 313 | thm | trproj | std |
| `Lean4Lean.VExpr.projFns_instL` | 323 | thm | trproj | std |
| `Lean4Lean.VExpr.projFn_subst` | 333 | thm | trproj | std |
| `Lean4Lean.VExpr.projFn_lift'` | 339 | thm | trproj | std |
| `Lean4Lean.VExpr.projFn_inst` | 345 | thm | trproj | std |
| `Lean4Lean.VExpr.projFn_instL` | 351 | thm | trproj | std |
| `Lean4Lean.VExpr.projMotiveBody_subst` | 357 | thm | trproj | std |
| `Lean4Lean.VExpr.projMotiveBody_lift'` | 364 | thm | trproj | std |
| `Lean4Lean.VExpr.projMotiveBody_instN` | 371 | thm | trproj | std |
| `Lean4Lean.VExpr.projMotiveBody_instL` | 379 | thm | trproj | std |
| `Lean4Lean.VExpr.instFields_app` | 394 | thm | trproj | none |
| `Lean4Lean.VExpr.instFields_mkApps` | 399 | thm | trproj | none |
| `Lean4Lean.VExpr.instFields_liftN` | 405 | thm | trproj | std |
| `Lean4Lean.VExpr.instFields_bvar` | 411 | thm | trproj | std |
| `Lean4Lean.VExpr.instFields_minor_spine` | 426 | thm | trproj | std |

### `Lean4Lean/Theory/Inductive.lean` — 60 declarations, 0 reach `sorryAx`

Per-line blame: iota: 438 I / 4 M / 2 P.

| declaration | line | kind | attr | axioms |
|---|---|---|---|---|
| `Lean4Lean.VExpr.MentionsConst.match_1.splitter` | -1 | def (private) | unknown(no-range) | none |
| `Lean4Lean.VExpr.MentionsConst` | 22 | def | iota | none |
| `Lean4Lean.VExpr.mentionsConst` | 29 | def | iota | std |
| `Lean4Lean.VExpr.mentionsConst_iff` | 35 | thm | iota | std |
| `Lean4Lean.VExpr.CtorResult` | 41 | def | iota | std |
| `Lean4Lean.VExpr.CtorResult_iff` | 48 | thm | iota | std |
| `Lean4Lean.VExpr.MajorApp` | 61 | def | iota | none |
| `Lean4Lean.VExpr.MajorApp_iff` | 66 | thm | iota | std |
| `Lean4Lean.VExpr.ValidIndApp` | 72 | def | iota | none |
| `Lean4Lean.VExpr.ValidIndApp_iff` | 79 | thm | iota | std |
| `Lean4Lean.VExpr.FieldPositive` | 88 | def | iota | std |
| `Lean4Lean.VExpr.CtorPositive` | 98 | def | iota | std |
| `Lean4Lean.VExpr.FieldInIndices` | 105 | def | iota | std |
| `Lean4Lean.VExpr.fieldCtx` | 110 | def | iota | std |
| `Lean4Lean.VExpr.MotiveShape` | 116 | def | iota | std |
| `Lean4Lean.VExpr.MinorHeaded` | 124 | def | iota | std |
| `Lean4Lean.VExpr.MinorFor` | 131 | def | iota | std |
| `Lean4Lean.VExpr.RecShape` | 137 | def | iota | std |
| `Lean4Lean.VExpr.CtorShape` | 154 | def | iota | std |
| `Lean4Lean.VExpr.majorFormer?` | 159 | def | iota | std |
| `Lean4Lean.VExpr.RuleShape` | 164 | def | iota | std |
| `Lean4Lean.VExpr.RuleShape.lam` | 181 | thm | iota | std |
| `Lean4Lean.VExpr.RecShape.recHeaded` | 190 | thm | iota | std |
| `Lean4Lean.VExpr.RecShape.one_le_numMotives` | 195 | thm | iota | std |
| `Lean4Lean.VExpr.RecShape.majorFormer?_eq` | 200 | thm | iota | std |
| `Lean4Lean.VExpr.CtorResult.ctorHeaded` | 209 | thm | iota | std |
| `Lean4Lean.VExpr.CtorResult.ctorShape` | 215 | thm | iota | std |
| `Lean4Lean.VInductDecl.LargeElim` | 221 | def | iota | std |
| `Lean4Lean.VInductDecl.LargeElimShape` | 234 | def | iota | none |
| `Lean4Lean.VInductDecl.LargeElim.shape` | 240 | thm | iota | std |
| `Lean4Lean.VEnv.addRecRule` | 251 | def | iota | std |
| `Lean4Lean.VInductDecl.addTypes` | 279 | def | iota | std |
| `Lean4Lean.VInductDecl.addCtors` | 283 | def | iota | std |
| `Lean4Lean.VInductDecl.addRecs` | 287 | def | iota | std |
| `Lean4Lean.VInductDecl.addRules` | 291 | def | iota | std |
| `Lean4Lean.VInductDecl.addTypesCtors` | 296 | def | iota | std |
| `Lean4Lean.VInductDecl.addTypesCtorsRecs` | 300 | def | iota | std |
| `Lean4Lean.VInductDecl.consts` | 304 | def | iota | none |
| `Lean4Lean.VEnv.addInduct` | 312 | def | iota | std |
| `Lean4Lean.VInductDecl.WF` | 319 | inductive | iota | std |
| `Lean4Lean.VInductDecl.WF.mk` | 335 | ctor | iota | std |
| `Lean4Lean.VInductDecl.WF.types_wf` | 337 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.ctors_wf` | 339 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.recs_wf` | 342 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.types_uvars` | 345 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.ctors_uvars` | 347 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.universes` | 351 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.recs_elim` | 361 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.ctors_params` | 367 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.ctors_result` | 371 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.ctors_positive` | 374 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.recs_over_block` | 377 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.rules_nodup` | 389 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.rules_ctor` | 392 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.types_have_rec` | 397 | thm | trproj/mixed | std |
| `Lean4Lean.VInductDecl.WF.rules_total` | 401 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.rule_shape` | 408 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.rules_wf` | 420 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.ctors_have_rules` | 428 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.rules_own_params` | 437 | thm | iota | std |

### `Lean4Lean/Theory/Typing/InductiveLemmas.lean` — 76 declarations, 0 reach `sorryAx`

Per-line blame: iota: 753 I / 8 M / 24 P.

| declaration | line | kind | attr | axioms |
|---|---|---|---|---|
| `Lean4Lean.SimplePattern.iotaRHS.congr_simp` | -1 | thm | unknown(no-range) | std |
| `Lean4Lean.SimplePattern.toPattern.match_1.splitter` | -1 | def (private) | unknown(no-range) | none |
| `Lean4Lean.VEnv.addConst.match_1.splitter` | -1 | def (private) | unknown(no-range) | none |
| `Lean4Lean.VEnv.foldlM_le` | 20 | thm | iota | std |
| `Lean4Lean.VEnv.addRecRule_le` | 31 | thm | iota | std |
| `Lean4Lean.VEnv.addRecRule_pats` | 39 | thm | iota | std |
| `Lean4Lean.VEnv.addTypes_le` | 55 | thm | iota | std |
| `Lean4Lean.VEnv.addCtors_le` | 60 | thm | iota | std |
| `Lean4Lean.VEnv.addRecs_le` | 65 | thm | iota | std |
| `Lean4Lean.VEnv.addRules_le` | 70 | thm | iota | std |
| `Lean4Lean.VEnv.addInduct_stages` | 75 | thm | iota | std |
| `Lean4Lean.VEnv.addInduct_le` | 88 | thm | iota | std |
| `Lean4Lean.VEnv.foldlM_mono_of_mem` | 94 | thm | iota | std |
| `Lean4Lean.VEnv.addRules_pat` | 111 | thm | iota | std |
| `Lean4Lean.VEnv.addInduct_pat` | 134 | thm | iota | std |
| `Lean4Lean.VEnv.foldlM_inv` | 149 | thm | iota | std |
| `Lean4Lean.VEnv.foldlM_addConst_ordered` | 160 | thm | iota | std |
| `Lean4Lean.VEnv.addTypes_ordered` | 170 | thm | iota | std |
| `Lean4Lean.VEnv.addCtors_ordered` | 176 | thm | iota | std |
| `Lean4Lean.VEnv.addRecs_ordered` | 184 | thm | iota | std |
| `Lean4Lean.VEnv.addTypesCtors_ordered` | 190 | thm | iota | std |
| `Lean4Lean.VEnv.addTypesCtorsRecs_ordered` | 197 | thm | iota | std |
| `Lean4Lean.VEnv.addRules_ordered` | 204 | thm | iota | std |
| `Lean4Lean.VEnv.addInduct_WF` | 225 | thm | iota/mixed | std |
| `Lean4Lean.VEnv.addConst_pats` | 245 | thm | iota | std |
| `Lean4Lean.VEnv.addConst_defeqs` | 252 | thm | iota | std |
| `Lean4Lean.VEnv.addDefEq_pats` | 259 | thm | iota | none |
| `Lean4Lean.VEnv.addConsts_pats` | 262 | thm | iota | std |
| `Lean4Lean.VEnv.addConsts_defeqs` | 271 | thm | iota | std |
| `Lean4Lean.VEnv.addDefEqs_pats` | 280 | thm | iota | none |
| `Lean4Lean.VEnv.addDefEqs_le` | 287 | thm | iota | none |
| `Lean4Lean.VEnv.addQuot_pats` | 294 | thm | iota | std |
| `Lean4Lean.VEnv.foldlM_pats_preserved` | 304 | thm | iota | std |
| `Lean4Lean.VEnv.foldlM_defeqs_preserved` | 313 | thm | iota | std |
| `Lean4Lean.VEnv.addConst_eq` | 323 | thm | iota | std |
| `Lean4Lean.VEnv.addConst_foldlM_fresh` | 332 | thm | iota | std |
| `Lean4Lean.VEnv.addConst_comm` | 350 | thm | iota | std |
| `Lean4Lean.VEnv.addConst_foldlM_perm` | 370 | thm | iota | std |
| `Lean4Lean.VEnv.addConst_foldlM_constants_inv` | 391 | thm | iota | std |
| `Lean4Lean.VInductDecl.addTypesCtorsRecs_eq` | 409 | thm | iota | std |
| `Lean4Lean.VEnv.addConst_foldlM_find` | 417 | thm | iota | std |
| `Lean4Lean.VEnv.addConst_foldlM_inj` | 432 | thm | iota | std |
| `Lean4Lean.VEnv.nodup_map_inj_on` | 449 | thm | iota | std |
| `Lean4Lean.VEnv.addQuot_le` | 463 | thm | iota | std |
| `Lean4Lean.VEnv.addTypes_pats` | 476 | thm | iota | std |
| `Lean4Lean.VEnv.addCtors_pats` | 481 | thm | iota | std |
| `Lean4Lean.VEnv.addRecs_pats` | 486 | thm | iota | std |
| `Lean4Lean.VEnv.addTypes_defeqs` | 491 | thm | iota | std |
| `Lean4Lean.VEnv.addCtors_defeqs` | 497 | thm | iota | std |
| `Lean4Lean.VEnv.addRecs_defeqs` | 503 | thm | iota | std |
| `Lean4Lean.VEnv.addRecRule_defeqs` | 509 | thm | trproj | std |
| `Lean4Lean.VEnv.addRules_defeqs` | 517 | thm | trproj | std |
| `Lean4Lean.VEnv.addInduct_defeqs` | 524 | thm | trproj | std |
| `Lean4Lean.VEnv.addTypes_find` | 531 | thm | iota | std |
| `Lean4Lean.VEnv.addCtors_fresh` | 537 | thm | iota | std |
| `Lean4Lean.VEnv.addCtors_find` | 544 | thm | iota | std |
| `Lean4Lean.VEnv.addRecs_fresh` | 551 | thm | iota | std |
| `Lean4Lean.VEnv.addRecs_find` | 556 | thm | iota | std |
| `Lean4Lean.VEnv.addRecs_name_inj` | 562 | thm | iota | std |
| `Lean4Lean.VEnv.addRecRule_pats_inv'` | 575 | thm | iota | std |
| `Lean4Lean.VEnv.foldlM_pats_inv_mem` | 592 | thm | iota | std |
| `Lean4Lean.VEnv.addInduct_pats_origin'` | 610 | thm | iota/mixed | std |
| `Lean4Lean.VEnv.addInduct_pats_origin` | 645 | thm | iota | std |
| `Lean4Lean.VEnv.addInduct_rec_fresh` | 659 | thm | iota | std |
| `Lean4Lean.VEnv.addInduct_rec_find` | 670 | thm | iota | std |
| `Lean4Lean.VEnv.addInduct_recs_name_inj` | 677 | thm | iota | std |
| `Lean4Lean.VInductDecl.WF.rules_ctor_shape` | 684 | thm | iota | std |
| `Lean4Lean.VEnv.addInduct_rule_ctor` | 698 | thm | iota | std |
| `Lean4Lean.VEnv.iota_toPattern_inj` | 712 | thm | iota | std |
| `Lean4Lean.VEnv.foldlM_step_success` | 724 | thm | iota | std |
| `Lean4Lean.VEnv.addRecRule_closed` | 736 | thm | iota | std |
| `Lean4Lean.VEnv.addRules_closed` | 743 | thm | iota | std |
| `Lean4Lean.VEnv.addConst_foldlM_nodup` | 752 | thm | iota | std |
| `Lean4Lean.VEnv.addTypes_nodup` | 768 | thm | iota | std |
| `Lean4Lean.VEnv.addCtors_nodup` | 773 | thm | iota | std |
| `Lean4Lean.VEnv.addRecs_nodup` | 779 | thm | iota | std |

### `Lean4Lean/Theory/Typing/InductiveParams.lean` — 26 declarations, 1 reach `sorryAx`

Per-line blame: iota: 389 I / 44 P.

| declaration | line | kind | attr | axioms |
|---|---|---|---|---|
| `Lean4Lean.VEnv.app_subpattern_iota'` | 24 | thm | iota | std |
| `Lean4Lean.VEnv.app_subpattern_iota` | 35 | thm | iota | std |
| `Lean4Lean.Pattern.inter_app_const` | 42 | thm | iota | std |
| `Lean4Lean.Pattern.inter_app_var` | 47 | thm | iota | std |
| `Lean4Lean.Pattern.inter_app_app` | 56 | thm | iota | std |
| `Lean4Lean.VDecl.WF.pats_eq_or_induct'` | 67 | thm | iota | std |
| `Lean4Lean.VDecl.WF.pats_eq_or_induct` | 81 | thm | iota | std |
| `Lean4Lean.VEnv.WF'.pats_origin` | 89 | thm | iota | std |
| `Lean4Lean.VEnv.PatsIota` | 128 | inductive | iota | std |
| `Lean4Lean.VEnv.PatsIota.mk` | 133 | ctor | iota | std |
| `Lean4Lean.VEnv.PatsIota.shape` | 134 | thm | iota | std |
| `Lean4Lean.VEnv.PatsIota.arity` | 138 | thm | iota | std |
| `Lean4Lean.VEnv.PatsIota.ctor_shape` | 141 | thm | iota | std |
| `Lean4Lean.VEnv.PatsIota.functional` | 144 | thm | iota | std |
| `Lean4Lean.VEnv.PatsIota.of_le` | 159 | thm | iota | std |
| `Lean4Lean.VEnv.WF.patsIota` | 231 | thm | iota | std |
| `Lean4Lean.VEnv.WF.pat_simple` | 248 | thm | iota | std |
| `Lean4Lean.VEnv.WF.pat_uniq` | 254 | thm | iota | std |
| `Lean4Lean.VEnv.WF.pat_app_l` | 295 | thm | iota | std |
| `Lean4Lean.VEnv.WF.pat_app_l_uniq` | 303 | thm | iota | std |
| `Lean4Lean.VEnv.WF.pat_app_uniq` | 331 | thm | iota | std |
| `Lean4Lean.VEnv.DefEqsAsPats` | 351 | def | iota/mixed | std |
| `Lean4Lean.VEnv.toParams` | 385 | def | iota/mixed | std |
| `Lean4Lean.VEnv.DefEqsAsPats.of_no_defeqs` | 412 | thm | trproj | std |
| `Lean4Lean.VEnv.inductParams` | 416 | def | trproj | std |
| `Lean4Lean.VEnv.IsDefEq.crDefEq_of_induct` | 424 | thm | trproj/mixed | **SORRY** · std |

### `Lean4Lean/Theory/Typing/Pattern.lean` — 133 declarations, 0 reach `sorryAx`

Per-line blame: mixed: 229 M / 419 I / 77 P.

| declaration | line | kind | attr | axioms |
|---|---|---|---|---|
| `Lean4Lean.Arity.below.app` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Arity.below.refl` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Arity.below.var` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Pattern.Check.OK.match_1.splitter` | -1 | def (private) | unknown(no-range) | none |
| `Lean4Lean.Pattern.Check.Realizes.match_1.splitter` | -1 | def (private) | unknown(no-range) | none |
| `Lean4Lean.Pattern.Check.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Pattern.Check.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Pattern.LE.below.app` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Pattern.LE.below.app_var` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Pattern.LE.below.refl` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Pattern.LE.below.var` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Pattern.Matches.below.app` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Pattern.Matches.below.const` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Pattern.Matches.below.var` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Pattern.Matches.match_1.splitter` | -1 | def (private) | unknown(no-range) | none |
| `Lean4Lean.Pattern.RHS.TemplateHeaded.below.app` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Pattern.RHS.TemplateHeaded.below.lam` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Pattern.RHS.apply.match_1.splitter` | -1 | def (private) | unknown(no-range) | none |
| `Lean4Lean.Pattern.RHS.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Pattern.RHS.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Pattern.RHS.fixed.congr_simp` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Pattern.RHS.spine.match_1.splitter` | -1 | def (private) | unknown(no-range) | none |
| `Lean4Lean.Pattern.RHS.spine.match_3.splitter` | -1 | def (private) | unknown(no-range) | std |
| `Lean4Lean.Pattern.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Pattern.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Pattern.inter.match_1.splitter` | -1 | def (private) | unknown(no-range) | std |
| `Lean4Lean.Pattern.varN.match_1.splitter` | -1 | def (private) | unknown(no-range) | none |
| `Lean4Lean.Pattern.varN_pathOf.congr_simp` | -1 | thm | unknown(no-range) | std |
| `Lean4Lean.SimplePattern.iotaRHS'.congr_simp` | -1 | thm | unknown(no-range) | std |
| `Lean4Lean.Subpattern.below.appL` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Subpattern.below.appR` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Subpattern.below.refl` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Subpattern.below.varL` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Pattern` | 8 | inductive | master | none |
| `Lean4Lean.Pattern.const` | 9 | ctor | master | none |
| `Lean4Lean.Pattern.app` | 10 | ctor | master | none |
| `Lean4Lean.Pattern.var` | 11 | ctor | master | none |
| `Lean4Lean.Pattern.varN` | 13 | def | master | none |
| `Lean4Lean.Subpattern` | 17 | inductive | master | none |
| `Lean4Lean.Subpattern.refl` | 18 | ctor | master | none |
| `Lean4Lean.Subpattern.appL` | 19 | ctor | master | none |
| `Lean4Lean.Subpattern.appR` | 20 | ctor | master | none |
| `Lean4Lean.Subpattern.varL` | 21 | ctor | master | none |
| `Lean4Lean.Subpattern.varN` | 23 | thm | master/mixed | none |
| `Lean4Lean.Subpattern.trans` | 27 | thm | master | none |
| `Lean4Lean.Subpattern.antisymm` | 37 | thm | master | std |
| `Lean4Lean.Arity` | 45 | inductive | master | none |
| `Lean4Lean.Arity.refl` | 46 | ctor | master | none |
| `Lean4Lean.Arity.app` | 47 | ctor | master | none |
| `Lean4Lean.Arity.var` | 48 | ctor | master | none |
| `Lean4Lean.Arity.subpattern` | 50 | thm | master | none |
| `Lean4Lean.Pattern.inter` | 55 | def | master | std |
| `Lean4Lean.Pattern.inter_self` | 63 | thm | master | std |
| `Lean4Lean.Pattern.inter_comm` | 65 | thm | iota/mixed | std |
| `Lean4Lean.Pattern.subpattern_varN_const` | 74 | thm | iota | none |
| `Lean4Lean.Pattern.not_app_subpattern_varN_const` | 89 | thm | iota | std |
| `Lean4Lean.Pattern.varN_const_inter` | 97 | thm | iota | std |
| `Lean4Lean.Pattern.varN_const_inj` | 117 | thm | iota | std |
| `Lean4Lean.Pattern.LE` | 126 | inductive | master | none |
| `Lean4Lean.Pattern.LE.refl` | 127 | ctor | master | none |
| `Lean4Lean.Pattern.LE.var` | 128 | ctor | master | none |
| `Lean4Lean.Pattern.LE.app` | 129 | ctor | master | none |
| `Lean4Lean.Pattern.LE.app_var` | 130 | ctor | master | none |
| `Lean4Lean.Pattern.Path` | 132 | def | master | none |
| `Lean4Lean.Pattern.Matches` | 137 | inductive | master | none |
| `Lean4Lean.Pattern.Matches.const` | 138 | ctor | master | none |
| `Lean4Lean.Pattern.Matches.var` | 139 | ctor | master | none |
| `Lean4Lean.Pattern.Matches.app` | 140 | ctor | master | none |
| `Lean4Lean.Pattern.Matches.uniq` | 143 | thm | master/mixed | std |
| `Lean4Lean.Pattern.OnArgs` | 150 | def | master | none |
| `Lean4Lean.Pattern.RHS` | 155 | inductive | master | none |
| `Lean4Lean.Pattern.RHS.fixed` | 156 | ctor | master | none |
| `Lean4Lean.Pattern.RHS.app` | 157 | ctor | master | none |
| `Lean4Lean.Pattern.RHS.var` | 158 | ctor | master | none |
| `Lean4Lean.Pattern.Check` | 160 | inductive | master | none |
| `Lean4Lean.Pattern.Check.true` | 161 | ctor | master | none |
| `Lean4Lean.Pattern.Check.defeq` | 162 | ctor | master | none |
| `Lean4Lean.Pattern.RHS.apply` | 164 | def | master | std |
| `Lean4Lean.Pattern.RHS.Uses` | 169 | def | iota | none |
| `Lean4Lean.Pattern.RHS.Generic` | 175 | def | iota | none |
| `Lean4Lean.Pattern.RHS.lift'_apply` | 186 | thm | master | std |
| `Lean4Lean.Pattern.RHS.liftN_apply` | 191 | thm | master | std |
| `Lean4Lean.Pattern.matches_lift'` | 195 | thm | master | std |
| `Lean4Lean.Pattern.matches_liftN` | 223 | thm | master | std |
| `Lean4Lean.Pattern.RHS.instN_apply` | 227 | thm | master | std |
| `Lean4Lean.Pattern.matches_instN` | 232 | thm | master | std |
| `Lean4Lean.Pattern.matches_inter` | 243 | thm | master | std |
| `Lean4Lean.Pattern.matches_determ` | 283 | thm | master/mixed | std |
| `Lean4Lean.Pattern.Check.OK` | 290 | def | master | std |
| `Lean4Lean.Pattern.Check.OK.map` | 295 | thm | master | std |
| `Lean4Lean.Pattern.Check.Realizes` | 302 | def | iota | std |
| `Lean4Lean.Pattern.Check.Realizes.toOK` | 315 | thm | iota | std |
| `Lean4Lean.Pattern.Check.OK.exists_realizer` | 328 | thm | iota | std |
| `Lean4Lean.Pattern.RHS.apply_closedN` | 352 | thm | iota | std |
| `Lean4Lean.Pattern.Matches.closedN` | 360 | thm | iota | none |
| `Lean4Lean.Pattern.RHS.apply_levelWF` | 369 | thm | iota | std |
| `Lean4Lean.Pattern.Matches.levelWF` | 378 | thm | iota | none |
| `Lean4Lean.Pattern.RHS.instL_apply` | 392 | thm | iota | std |
| `Lean4Lean.Pattern.matches_instL` | 401 | thm | iota | std |
| `Lean4Lean.Pattern.Check.Realizes.map_liftN` | 414 | thm | iota | std |
| `Lean4Lean.Pattern.Check.Realizes.map_instN` | 427 | thm | iota | std |
| `Lean4Lean.Pattern.Check.Realizes.map_instL` | 439 | thm | iota | std |
| `Lean4Lean.Pattern.RHS.subst_apply` | 451 | thm | iota | std |
| `Lean4Lean.Pattern.matches_subst` | 458 | thm | iota | std |
| `Lean4Lean.Pattern.Check.Realizes.map_subst` | 472 | thm | iota | std |
| `Lean4Lean.SimplePattern` | 484 | inductive | master | none |
| `Lean4Lean.SimplePattern.iota` | 485 | ctor | master | none |
| `Lean4Lean.SimplePattern.defn` | 486 | ctor | master | none |
| `Lean4Lean.SimplePattern.toPattern` | 488 | def | master/mixed | none |
| `Lean4Lean.Pattern.varN_pathOf` | 492 | def | iota | std |
| `Lean4Lean.Pattern.RHS.spine` | 509 | def | iota | std |
| `Lean4Lean.Pattern.RHS.spine_foldl_var` | 516 | thm | iota | std |
| `Lean4Lean.Pattern.RHS.iotaCounts` | 524 | def | iota | std |
| `Lean4Lean.SimplePattern.iotaPaths` | 531 | def | iota | std |
| `Lean4Lean.SimplePattern.iotaPaths_countP_isLeft` | 548 | thm | iota | std |
| `Lean4Lean.SimplePattern.iotaPaths_countP_isRight` | 556 | thm | iota | std |
| `Lean4Lean.SimplePattern.iotaRHS'` | 564 | def | iota | std |
| `Lean4Lean.SimplePattern.iotaRHS` | 573 | def | iota | std |
| `Lean4Lean.Pattern.RHS.apply_foldl_var` | 586 | thm | trproj | std |
| `Lean4Lean.Pattern.matches_varN_const` | 596 | thm | trproj | std |
| `Lean4Lean.SimplePattern.iotaRHS'_apply` | 623 | thm | trproj | std |
| `Lean4Lean.SimplePattern.iotaRHS'_spine` | 663 | thm | iota | std |
| `Lean4Lean.SimplePattern.iotaRHS'_iotaCounts` | 668 | thm | iota | std |
| `Lean4Lean.SimplePattern.iotaRHS_iotaCounts` | 673 | thm | iota | std |
| `Lean4Lean.Pattern.RHS.TemplateHeaded` | 689 | inductive | iota | none |
| `Lean4Lean.Pattern.RHS.TemplateHeaded.lam` | 691 | ctor | iota | none |
| `Lean4Lean.Pattern.RHS.TemplateHeaded.app` | 692 | ctor | iota | none |
| `Lean4Lean.Pattern.RHS.TemplateHeaded.foldl_app` | 694 | thm | iota | none |
| `Lean4Lean.Pattern.RHS.TemplateHeaded.apply_lam_or_app` | 699 | thm | iota | std |
| `Lean4Lean.Pattern.RHS.TemplateHeaded.apply_ne_forallE` | 707 | thm | iota | std |
| `Lean4Lean.Pattern.RHS.TemplateHeaded.apply_ne_sort` | 711 | thm | iota | std |
| `Lean4Lean.SimplePattern.iotaRHS'_templateHeaded` | 715 | thm | iota | std |
| `Lean4Lean.SimplePattern.iotaRHS_templateHeaded` | 721 | thm | iota | std |

### `Lean4Lean/Verify/Environment/Quot.lean` — 79 declarations, 0 reach `sorryAx`

Per-line blame: iota: 615/615 I.

| declaration | line | kind | attr | axioms |
|---|---|---|---|---|
| `Except.map.match_1.splitter` | -1 | def (private) | unknown(no-range) | none |
| `Lean4Lean.checkEqType.match_1.splitter` | -1 | def (private) | unknown(no-range) | std |
| `Lean4Lean.withLocalDecl_run` | 20 | thm | iota | std |
| `Lean4Lean.AddQuotAux.ng0` | 27 | def | iota | none |
| `Lean4Lean.AddQuotAux.x1` | 28 | def | iota | none |
| `Lean4Lean.AddQuotAux.x2` | 29 | def | iota | none |
| `Lean4Lean.AddQuotAux.x3` | 30 | def | iota | none |
| `Lean4Lean.AddQuotAux.x4` | 31 | def | iota | none |
| `Lean4Lean.AddQuotAux.x5` | 32 | def | iota | none |
| `Lean4Lean.AddQuotAux.x6` | 33 | def | iota | none |
| `Lean4Lean.AddQuotAux.u` | 35 | def | iota | none |
| `Lean4Lean.AddQuotAux.v` | 36 | def | iota | none |
| `Lean4Lean.AddQuotAux.αr` | 37 | def | iota | none |
| `Lean4Lean.AddQuotAux.quot_r` | 38 | def | iota | none |
| `Lean4Lean.AddQuotAux.L1` | 40 | def | iota | std |
| `Lean4Lean.AddQuotAux.L2` | 41 | def | iota | std |
| `Lean4Lean.AddQuotAux.L3` | 42 | def | iota | std |
| `Lean4Lean.AddQuotAux.L2'` | 43 | def | iota | std |
| `Lean4Lean.AddQuotAux.L3'` | 44 | def | iota | std |
| `Lean4Lean.AddQuotAux.L4` | 45 | def | iota | std |
| `Lean4Lean.AddQuotAux.L5` | 46 | def | iota | std |
| `Lean4Lean.AddQuotAux.L6` | 47 | def | iota | std |
| `Lean4Lean.AddQuotAux.L4i` | 48 | def | iota | std |
| `Lean4Lean.AddQuotAux.L5i` | 49 | def | iota | std |
| `Lean4Lean.AddQuotAux.T1` | 51 | def | iota | std |
| `Lean4Lean.AddQuotAux.T2` | 52 | def | iota | std |
| `Lean4Lean.AddQuotAux.sanity` | 53 | def | iota | std |
| `Lean4Lean.AddQuotAux.T3` | 56 | def | iota | std |
| `Lean4Lean.AddQuotAux.all_quot` | 58 | def | iota | std |
| `Lean4Lean.AddQuotAux.T4` | 60 | def | iota | std |
| `Lean4Lean.AddQuotAux.q1` | 63 | def | iota | std |
| `Lean4Lean.AddQuotAux.q2` | 65 | def | iota | std |
| `Lean4Lean.AddQuotAux.q3` | 67 | def | iota | std |
| `Lean4Lean.AddQuotAux.q4` | 69 | def | iota | std |
| `Lean4Lean.AddQuotAux.addQuot_eq` | 72 | thm | iota | std |
| `Lean4Lean.AddQuotAux.L1_mwf` | 92 | thm | iota | std |
| `Lean4Lean.AddQuotAux.L1_find` | 93 | thm | iota | std · +`Lean.PersistentArray.toList'_push`, `Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.L2_mwf` | 97 | thm | iota | std |
| `Lean4Lean.AddQuotAux.L2_find` | 98 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.L3_find` | 101 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.L2'_mwf` | 107 | thm | iota | std |
| `Lean4Lean.AddQuotAux.L2'_find` | 108 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.L3'_mwf` | 111 | thm | iota | std |
| `Lean4Lean.AddQuotAux.L3'_find` | 112 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.L4_mwf` | 116 | thm | iota | std |
| `Lean4Lean.AddQuotAux.L4_find` | 117 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.L5_mwf` | 121 | thm | iota | std |
| `Lean4Lean.AddQuotAux.L5_find` | 122 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.L6_find` | 127 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.L4i_mwf` | 131 | thm | iota | std |
| `Lean4Lean.AddQuotAux.L4i_find` | 132 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.L5i_find` | 136 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.tacticQuot_simp` | 144 | def | iota | none |
| `Lean4Lean.AddQuotAux.tacticQuot_mem` | 152 | def | iota | none |
| `Lean4Lean.AddQuotAux.T1_eq` | 159 | thm | iota | std · +`Lean.Expr.abstractRange_eq`, `Lean.Expr.abstract_eq`, `Lean.Expr.hasLooseBVar_eq`, `Lean.Expr.lowerLooseBVars_eq`, `Lean.PersistentArray.toList'_push`, `Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.T2_eq` | 166 | thm | iota | std · +`Lean.Expr.abstractRange_eq`, `Lean.Expr.abstract_eq`, `Lean.Expr.hasLooseBVar_eq`, `Lean.Expr.lowerLooseBVars_eq`, `Lean.PersistentArray.toList'_push`, `Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.sanity_eq` | 174 | thm | iota | std · +`Lean.Expr.abstractRange_eq`, `Lean.Expr.abstract_eq`, `Lean.Expr.hasLooseBVar_eq`, `Lean.Expr.lowerLooseBVars_eq`, `Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.T3_eq` | 182 | thm | iota | std · +`Lean.Expr.abstractRange_eq`, `Lean.Expr.abstract_eq`, `Lean.Expr.hasLooseBVar_eq`, `Lean.Expr.lowerLooseBVars_eq`, `Lean.PersistentArray.toList'_push`, `Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.all_quot_eq` | 196 | thm | iota | std · +`Lean.Expr.abstractRange_eq`, `Lean.Expr.abstract_eq`, `Lean.Expr.hasLooseBVar_eq`, `Lean.Expr.lowerLooseBVars_eq`, `Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.T4_inner_eq` | 203 | thm | iota | std · +`Lean.Expr.abstractRange_eq`, `Lean.Expr.abstract_eq`, `Lean.Expr.hasLooseBVar_eq`, `Lean.Expr.lowerLooseBVars_eq`, `Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.T4_eq` | 209 | thm | iota | std · +`Lean.Expr.abstractRange_eq`, `Lean.Expr.abstract_eq`, `Lean.Expr.hasLooseBVar_eq`, `Lean.Expr.lowerLooseBVars_eq`, `Lean.PersistentArray.toList'_push`, `Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.LE1` | 224 | def | iota | std |
| `Lean4Lean.AddQuotAux.TE` | 226 | def | iota | std |
| `Lean4Lean.AddQuotAux.LE1_find` | 229 | thm | iota | std · +`Lean.PersistentArray.toList'_push`, `Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.TE_eq` | 235 | thm | iota | std · +`Lean.Expr.abstractRange_eq`, `Lean.Expr.abstract_eq`, `Lean.Expr.hasLooseBVar_eq`, `Lean.Expr.lowerLooseBVars_eq`, `Lean.PersistentArray.toList'_push`, `Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuotAux.Environment.get_ok` | 244 | thm | iota | std |
| `Lean4Lean.AddQuotAux.checkEqType_ok` | 251 | thm | iota | std |
| `Lean4Lean.AddQuotAux.T1'` | 304 | def | iota | none |
| `Lean4Lean.AddQuotAux.T2'` | 308 | def | iota | none |
| `Lean4Lean.AddQuotAux.T3'` | 312 | def | iota | none |
| `Lean4Lean.AddQuotAux.T4'` | 322 | def | iota | none |
| `Lean4Lean.AddQuotAux.T1_tr` | 331 | thm | iota | std |
| `Lean4Lean.AddQuotAux.T2_tr` | 337 | thm | iota | std |
| `Lean4Lean.AddQuotAux.T3_tr` | 347 | thm | iota | std |
| `Lean4Lean.AddQuotAux.T4_tr` | 372 | thm | iota | std |
| `Lean4Lean.AddQuotAux.quotReady` | 396 | thm | iota | std · +`Lean.Expr.abstractRange_eq`, `Lean.Expr.abstract_eq`, `Lean.Expr.eqv_eq`, `Lean.Expr.hasLooseBVar_eq`, `Lean.Expr.lowerLooseBVars_eq`, `Lean.Level.instLawfulBEqLevel`, `Lean.PersistentArray.toList'_push`, `Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.AddQuotAux.C'` | 430 | def | iota | std |
| `Lean4Lean.AddQuotAux.exists_addQuot` | 434 | thm | iota | std · +`Lean.Expr.abstractRange_eq`, `Lean.Expr.abstract_eq`, `Lean.Expr.hasLooseBVar_eq`, `Lean.Expr.lowerLooseBVars_eq`, `Lean.PersistentArray.toList'_push`, `Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.addQuot.WF` | 496 | thm | iota | std · +`Lean.Expr.abstractRange_eq`, `Lean.Expr.abstract_eq`, `Lean.Expr.eqv_eq`, `Lean.Expr.hasLooseBVar_eq`, `Lean.Expr.lowerLooseBVars_eq`, `Lean.Level.instLawfulBEqLevel`, `Lean.PersistentArray.toList'_push`, `Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |

### `Lean4Lean/Verify/Environment/Basic.lean` — 108 declarations, 0 reach `sorryAx`

Per-line blame: mixed: 197 M / 398 I / 24 P.

| declaration | line | kind | attr | axioms |
|---|---|---|---|---|
| `Lean.ConstantInfo.value?.match_1.splitter` | -1 | def (private) | unknown(no-range) | std |
| `Lean4Lean.TrEnv'.below.axiom` | -1 | ctor | unknown(no-range) | std |
| `Lean4Lean.TrEnv'.below.defn` | -1 | ctor | unknown(no-range) | std |
| `Lean4Lean.TrEnv'.below.empty` | -1 | ctor | unknown(no-range) | std |
| `Lean4Lean.TrEnv'.below.ignore` | -1 | ctor | unknown(no-range) | std |
| `Lean4Lean.TrEnv'.below.mutualDef` | -1 | ctor | unknown(no-range) | std |
| `Lean4Lean.TrEnv'.below.opaque` | -1 | ctor | unknown(no-range) | std |
| `Lean4Lean.TrEnv'.below.quot` | -1 | ctor | unknown(no-range) | std |
| `Lean4Lean.TrEnv'.below.thm` | -1 | ctor | unknown(no-range) | std |
| `Lean4Lean.ConstantInfo.hasValue_eq` | 11 | thm | master | std |
| `Lean4Lean.ConstantInfo.value!_eq` | 14 | thm | master | std |
| `Lean.ConstantInfo.safety` | 17 | def | master | std |
| `Lean4Lean.TrConstant` | 21 | def | master | std |
| `Lean4Lean.TrConstVal` | 26 | def | master | std |
| `Lean4Lean.TrDefVal` | 30 | def | master | std |
| `Lean4Lean.TrConstant.sf_mono` | 34 | thm | iota | std |
| `Lean4Lean.TrConstant.mono` | 38 | thm | iota | std |
| `Lean4Lean.TrConstVal.mono` | 42 | thm | iota | std |
| `Lean4Lean.TrDefVal.mono` | 46 | thm | iota | std |
| `Lean4Lean.VEnv.AddConst` | 50 | def | master | std |
| `Lean4Lean.VEnv.AddConst.le` | 62 | thm | master | std |
| `Lean4Lean.VEnv.AddDef` | 68 | def | master | std |
| `Lean4Lean.VEnv.AddDef.le` | 79 | thm | master | std |
| `Lean4Lean.AddQuot1` | 86 | def | master | std |
| `Lean4Lean.AddQuot1.to_addQuot` | 95 | thm | master | std |
| `Lean4Lean.AddQuot1.le` | 102 | thm | master | std |
| `Lean4Lean.AddQuot` | 108 | def | master | std |
| `Lean4Lean.AddQuot.to_addQuot` | 114 | thm | master | std |
| `Lean4Lean.AddQuot.le` | 117 | thm | iota/mixed | std |
| `Lean4Lean.insertConsts` | 126 | def | iota | std |
| `Lean4Lean.insertConsts_cons` | 130 | thm | iota | std |
| `Lean4Lean.insertConsts_fresh_tail` | 133 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.insertConsts_wf` | 142 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.insertConsts_find?_mono` | 151 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.insertConsts_find?_mono_of_fresh` | 157 | thm | iota/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.insertConsts_find?_none` | 165 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.insertConsts_find?` | 173 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.insertConsts_find?_self` | 190 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrIndType` | 207 | inductive | trproj | std |
| `Lean4Lean.TrIndType.mk` | 216 | ctor | trproj | std |
| `Lean4Lean.TrIndType.tr` | 219 | thm | iota | std |
| `Lean4Lean.TrIndType.ctor_names` | 220 | thm | iota | std |
| `Lean4Lean.TrIndType.ctors` | 221 | thm | iota/mixed | std |
| `Lean4Lean.TrIndType.all` | 224 | thm | trproj | std |
| `Lean4Lean.TrIndType.numParams` | 226 | thm | trproj | std |
| `Lean4Lean.TrIndType.numIndices` | 228 | thm | trproj/mixed | std |
| `Lean4Lean.TrRecursor` | 230 | inductive | iota | std |
| `Lean4Lean.TrRecursor.mk` | 237 | ctor | iota | std |
| `Lean4Lean.TrRecursor.tr` | 239 | thm | iota | std |
| `Lean4Lean.TrRecursor.all` | 240 | thm | iota | std |
| `Lean4Lean.TrRecursor.numParams` | 241 | thm | iota | std |
| `Lean4Lean.TrRecursor.numMotives` | 242 | thm | iota | std |
| `Lean4Lean.TrRecursor.numMinors` | 243 | thm | iota | std |
| `Lean4Lean.TrRecursor.numIndices` | 244 | thm | iota | std |
| `Lean4Lean.TrRecursor.k` | 245 | thm | iota | std |
| `Lean4Lean.TrRecursor.rules` | 246 | thm | iota/mixed | std |
| `Lean4Lean.TrRecursor.name_major` | 251 | thm | trproj/mixed | std |
| `Lean4Lean.AddInduct.consts` | 253 | def | iota | none |
| `Lean4Lean.AddInduct` | 263 | inductive | iota | std |
| `Lean4Lean.AddInduct.mk` | 272 | ctor | iota | std |
| `Lean4Lean.AddInduct.ivals` | 274 | def | iota | std |
| `Lean4Lean.AddInduct.rvals` | 275 | def | iota | std |
| `Lean4Lean.AddInduct.envT` | 276 | def | iota | std |
| `Lean4Lean.AddInduct.envC` | 277 | def | iota | std |
| `Lean4Lean.AddInduct.envR` | 278 | def | iota | std |
| `Lean4Lean.AddInduct.stT` | 279 | thm | iota | std |
| `Lean4Lean.AddInduct.stC` | 280 | thm | iota | std |
| `Lean4Lean.AddInduct.stR` | 281 | thm | iota | std |
| `Lean4Lean.AddInduct.stP` | 282 | thm | iota | std |
| `Lean4Lean.AddInduct.types` | 283 | thm | trproj | std |
| `Lean4Lean.AddInduct.recs` | 285 | thm | iota | std |
| `Lean4Lean.AddInduct.order` | 287 | def | iota | std |
| `Lean4Lean.AddInduct.order_perm` | 288 | thm | iota | std |
| `Lean4Lean.AddInduct.fresh` | 289 | thm | iota | std |
| `Lean4Lean.AddInduct.map_eq` | 290 | thm | iota | std |
| `Lean4Lean.AddInduct.env_eq` | 296 | thm | iota | std |
| `Lean4Lean.AddInduct.addTypesCtors` | 300 | thm | iota | std |
| `Lean4Lean.AddInduct.addTypesCtorsRecs` | 304 | thm | iota | std |
| `Lean4Lean.AddInduct.le` | 308 | thm | iota | std |
| `Lean4Lean.AddInduct.leR` | 309 | thm | iota | std |
| `Lean4Lean.AddInduct.mem_consts` | 311 | thm | iota | std |
| `Lean4Lean.AddInduct.novalue` | 328 | thm | iota | std |
| `Lean4Lean.AddInduct.types_names` | 334 | thm | iota | std |
| `Lean4Lean.AddInduct.ctors_names` | 338 | thm | iota | std |
| `Lean4Lean.AddInduct.recs_names` | 343 | thm | iota | std |
| `Lean4Lean.AddInduct.consts_names` | 347 | thm | iota | std |
| `Lean4Lean.AddInduct.names_nodup` | 356 | thm | iota | std |
| `Lean4Lean.AddInduct.order_fresh` | 384 | thm | iota | std |
| `Lean4Lean.AddInduct.order_nodup` | 389 | thm | iota | std |
| `Lean4Lean.AddInduct.wf` | 394 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.AddInduct.find?_mono` | 398 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddInduct.find?` | 404 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.AddInduct.find?_self` | 414 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.AddInduct.value_find` | 420 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.AddInduct.ctor_find` | 490 | thm | iota/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.insertDefs` | 521 | def | master | std |
| `Lean4Lean.TrDefBlock` | 526 | def | master | std |
| `Lean4Lean.TrEnv'` | 535 | inductive | master | std |
| `Lean4Lean.TrEnv'.empty` | 536 | ctor | master | std |
| `Lean4Lean.TrEnv'.ignore` | 537 | ctor | master | std |
| `Lean4Lean.TrEnv'.axiom` | 541 | ctor | master | std |
| `Lean4Lean.TrEnv'.defn` | 547 | ctor | master | std |
| `Lean4Lean.TrEnv'.mutualDef` | 553 | ctor | master | std |
| `Lean4Lean.TrEnv'.thm` | 564 | ctor | master | std |
| `Lean4Lean.TrEnv'.opaque` | 571 | ctor | master | std |
| `Lean4Lean.TrEnv'.quot` | 577 | ctor | master/mixed | std |
| `Lean4Lean.TrEnv` | 588 | def | master | std |
| `Lean4Lean.TrEnv'.wf` | 591 | thm | master/mixed | std |

### `Lean4Lean/Verify/Environment/Lemmas.lean` — 70 declarations, 6 reach `sorryAx`

Per-line blame: mixed: 254 M / 308 I / 616 P.

| declaration | line | kind | attr | axioms |
|---|---|---|---|---|
| `Lean.ConstantInfo.toConstantVal.match_1.splitter` | -1 | def (private) | unknown(no-range) | none |
| `Lean4Lean.Aligned.below.block` | -1 | ctor | unknown(no-range) | std |
| `Lean4Lean.Aligned.below.const` | -1 | ctor | unknown(no-range) | std |
| `Lean4Lean.Aligned.below.defeq` | -1 | ctor | unknown(no-range) | std |
| `Lean4Lean.Aligned.below.empty` | -1 | ctor | unknown(no-range) | std |
| `Lean4Lean.Aligned.below.ignoreConst` | -1 | ctor | unknown(no-range) | std |
| `Lean4Lean.Aligned.below.pat` | -1 | ctor | unknown(no-range) | std |
| `Lean4Lean.VEnv.addConst.match_1.splitter` | -1 | def (private) | unknown(no-range) | none |
| `Lean4Lean.Aligned` | 12 | inductive | master | std |
| `Lean4Lean.Aligned.empty` | 13 | ctor | master | std |
| `Lean4Lean.Aligned.ignoreConst` | 14 | ctor | master | std |
| `Lean4Lean.Aligned.const` | 16 | ctor | master | std |
| `Lean4Lean.Aligned.defeq` | 18 | ctor | master | std |
| `Lean4Lean.Aligned.pat` | 19 | ctor | iota | std |
| `Lean4Lean.Aligned.block` | 22 | ctor | iota/mixed | std |
| `Lean4Lean.Aligned.map_wf` | 35 | thm | master/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.Aligned.find?_iff` | 43 | thm | iota/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.Aligned.addQuot1` | 75 | thm | master | std |
| `Lean4Lean.Aligned.addQuot` | 81 | thm | master | std |
| `Lean4Lean.Aligned.addRules` | 87 | thm | iota | std |
| `Lean4Lean.Aligned.addInduct` | 97 | thm | iota/mixed | std |
| `Lean4Lean.Aligned.addDefEqs` | 128 | thm | master | std |
| `Lean4Lean.Aligned.insertDefs` | 135 | thm | master | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv'.aligned` | 162 | thm | master/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv'.map_wf` | 176 | thm | trproj/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.pull_insert` | 183 | thm | trproj/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuot1.pull` | 190 | thm | trproj/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.AddQuot.pull` | 199 | thm | trproj/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.insertDefs_wf` | 209 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.Aligned.find?` | 221 | thm | master/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.Aligned.find?_uniq` | 251 | thm | master/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv.find?_iff` | 284 | thm | master | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv.find?` | 294 | thm | master | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv.find?_uniq` | 299 | thm | master | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.VEnv.addDefEqs_self` | 304 | thm | master | none |
| `Lean4Lean.insertDefs_find?` | 312 | thm | master | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv'.of_value` | 333 | thm | master/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv.of_value` | 401 | thm | iota/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.insertDefs_find?_mono` | 412 | thm | iota/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert` |
| `Lean4Lean.AddQuot1.find?_mono` | 420 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.AddQuot.find?_mono` | 426 | thm | iota/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.Aligned.constants_pull` | 437 | thm | trproj | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv'.ctor_arity` | 446 | thm | trproj | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv.ctor_arity` | 502 | thm | trproj | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.mkRecName_inj` | 513 | thm | trproj | none |
| `Lean4Lean.TrEnv'.structure_rec` | 516 | thm | trproj | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv.structure_rec` | 642 | thm | trproj/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv'.pats_iota'` | 669 | thm | iota/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv.pats_iota'` | 747 | thm | iota | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv'.IotaRule` | 771 | inductive | trproj | std |
| `Lean4Lean.TrEnv'.IotaRule.mk` | 782 | ctor | trproj | std |
| `Lean4Lean.TrEnv'.IotaRule.rule_find` | 788 | thm | trproj | std |
| `Lean4Lean.TrEnv'.IotaRule.ctor_find` | 789 | thm | trproj | std |
| `Lean4Lean.TrEnv'.IotaRule.key_split` | 790 | thm | trproj | std |
| `Lean4Lean.TrEnv'.IotaRule.key_arity` | 791 | thm | trproj | std |
| `Lean4Lean.TrEnv'.IotaRule.tr` | 792 | thm | trproj | std |
| `Lean4Lean.TrEnv'.IotaRule.rhs_eq` | 793 | thm | trproj | std |
| `Lean4Lean.TrEnv'.IotaRule.chk_eq` | 795 | thm | trproj | std |
| `Lean4Lean.TrEnv'.IotaRule.minor` | 798 | thm | trproj | std |
| `Lean4Lean.TrEnv'.IotaRule.step` | 804 | thm | trproj | std |
| `Lean4Lean.TrEnv'.pats_iota_inv_shape` | 823 | thm | trproj/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv.pats_iota_inv_shape` | 901 | thm | trproj/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrEnv.iota_defeq` | 914 | thm | iota | std |
| `Lean4Lean.TrEnv.iota_rec` | 925 | thm | iota/mixed | std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.VEnv.HasType.mkApps_inv_head` | 958 | thm | trproj | **SORRY** · std |
| `Lean4Lean.VEnv.IsDefEqU.beta_app` | 969 | thm | trproj | **SORRY** · std |
| `Lean4Lean.VEnv.IsDefEqU.mkApps_congr` | 979 | thm | trproj | **SORRY** · std |
| `Lean4Lean.VEnv.IsDefEqU.betaN` | 992 | thm | trproj | **SORRY** · std |
| `Lean4Lean.TrEnv.proj_defeq` | 1013 | thm | trproj | **SORRY** · std · +`Lean.PersistentHashMap.WF.find?_eq`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.findAux_isSome` |
| `Lean4Lean.TrExpr.mkAppList` | 1166 | thm | trproj | **SORRY** · std |

### `Lean4Lean/Tests/ProjInhabit.lean` — 148 declarations, 0 reach `sorryAx`

Per-line blame: trproj: 597/597 P.

| declaration | line | kind | attr | axioms |
|---|---|---|---|---|
| `Lean4Lean.Tests.ProjInhabit.Plain.l1` | 27 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.Ac` | 28 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.Sc` | 29 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.mkc` | 30 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.ctorTy` | 31 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.motiveTy` | 32 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.mkSpine` | 33 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.minorTy` | 34 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.recTy` | 35 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.ruleRhs` | 37 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.decl` | 40 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.env0?` | 49 | def | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.env0_isSome` | 51 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.env` | 53 | def | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hA` | 55 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hS` | 56 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hmk` | 57 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hrec` | 58 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hclosed` | 60 | thm | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.patKey` | 62 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.rhsPair` | 63 | def | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hpats` | 66 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.uss` | 70 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.recC` | 71 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.M0` | 72 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.sel0` | 73 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.sel1` | 74 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.minorTyM` | 75 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.lvl1WF` | 84 | thm | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Plain.hAt` | 89 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hSt` | 91 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hmkt` | 93 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hrect` | 95 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hM` | 98 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hspine` | 101 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hbody0` | 104 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hselnat0` | 108 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hselnat1` | 111 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hminorEq` | 115 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hsel0` | 120 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hsel1` | 122 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hstep1` | 125 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hbetax` | 130 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.htyEq` | 134 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hProjFn0` | 139 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.hProjFn1` | 143 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.inhab0` | 150 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.inhab1` | 163 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Plain.trProj0` | 172 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.l1` | 181 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.Ac` | 182 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.Bc` | 183 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.S2c` | 184 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.mk2c` | 185 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.Bx` | 186 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.BTy` | 187 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.ctorTy2` | 188 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.mk2Spine` | 189 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.motiveTy2` | 190 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.motiveTy2'` | 191 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.minorTy2` | 192 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.recTy2` | 193 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.ruleRhs2` | 195 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.decl2` | 198 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.env0?` | 207 | def | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.env0_isSome` | 211 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.env` | 213 | def | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hA` | 215 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hB` | 216 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hS2` | 217 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hmk2` | 218 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hrec2` | 219 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hclosed2` | 221 | thm | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.patKey2` | 223 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.rhsPair2` | 224 | def | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hpats2` | 227 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.uss` | 231 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.rec2C` | 232 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.M20` | 233 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.sel20` | 234 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.sel21` | 235 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.P0'` | 236 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.M21` | 237 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.P1'` | 238 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.minorTyM20` | 239 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.minorTyM21` | 240 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.T` | 248 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.bodyT` | 253 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.inner3` | 254 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.T1` | 255 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.T2` | 256 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.T3` | 257 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.T5` | 258 | def | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.lvl1WF` | 262 | thm | trproj | none |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hAt` | 267 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hBt` | 269 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hS2t` | 271 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hmk2t` | 273 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hrec2t` | 275 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hBxt` | 278 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hmk2spine` | 282 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hM20` | 288 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbody20` | 291 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hsel20nat` | 295 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hminorEq20` | 299 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hsel20M` | 304 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hstep20` | 307 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbetax20` | 312 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hP0ty` | 316 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hM21body` | 321 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hM21` | 326 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hredex` | 331 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hmatch` | 336 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hiota` | 343 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbvarC` | 353 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hCapp` | 358 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hminorTy2wf` | 364 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbvarM` | 369 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hmSpine1` | 375 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hmSpine2` | 382 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbodyT` | 387 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbeta1` | 394 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hc1` | 400 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbvarM'` | 408 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hmSpine1'` | 414 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hmSpine2'` | 420 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hinner3` | 425 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbeta2` | 431 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hc2` | 436 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hinnerT2` | 443 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbeta3` | 450 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hc3` | 456 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbeta4` | 461 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbeta5` | 468 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hc5` | 474 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbeta6` | 479 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hproj0red` | 484 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hsel21nat` | 497 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbody21` | 502 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbodyEq21` | 507 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hminorEq21` | 512 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hsel21M` | 517 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hstep21` | 520 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hbetax21` | 525 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.hP1ty` | 529 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.inhabDep0` | 537 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.inhabDep1` | 549 | thm | trproj | std |
| `Lean4Lean.Tests.ProjInhabit.Dependent.trProjDep1` | 557 | thm | trproj | std |

### `Lean4Lean/Tests/ProjShape.lean` — 22 declarations, 0 reach `sorryAx`

Per-line blame: trproj: 185/185 P.

| declaration | line | kind | attr | axioms |
|---|---|---|---|---|
| `Lean4Lean.Tests.ProjShape.Refl.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.ProjShape.Refl.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.ProjShape.V3` | 33 | inductive | trproj | none |
| `Lean4Lean.Tests.ProjShape.V3.mk` | 33 | ctor | trproj | none |
| `Lean4Lean.Tests.ProjShape.V3.n` | 34 | def | trproj | none |
| `Lean4Lean.Tests.ProjShape.V3.v` | 35 | def | trproj | none |
| `Lean4Lean.Tests.ProjShape.V3.h` | 36 | thm | trproj | none |
| `Lean4Lean.Tests.ProjShape.Refl` | 38 | inductive | trproj | none |
| `Lean4Lean.Tests.ProjShape.Refl.mk` | 39 | ctor | trproj | none |
| `Lean4Lean.Tests.ProjShape.Refl.next` | 40 | def | trproj | none |
| `Lean4Lean.Tests.ProjShape.toLevel` | 42 | def | trproj | std |
| `Lean4Lean.Tests.ProjShape.toExpr` | 51 | def | trproj | std |
| `Lean4Lean.Tests.ProjShape.binders` | 60 | def | trproj | std |
| `Lean4Lean.Tests.ProjShape.checkProj` | 65 | def | trproj | std |
| `Lean4Lean.Tests.ProjShape.termU` | 152 | def (private) | trproj | none |
| `Lean4Lean.Tests.ProjShape.termV` | 153 | def (private) | trproj | none |
| `Lean4Lean.Tests.ProjShape.usS` | 155 | def | trproj | none |
| `Lean4Lean.Tests.ProjShape.uss` | 156 | def | trproj | none |
| `Lean4Lean.Tests.ProjShape.ps` | 157 | def | trproj | none |
| `Lean4Lean.Tests.ProjShape.Fs` | 158 | def | trproj | none |
| `Lean4Lean.Tests.ProjShape.structTy` | 159 | def | trproj | none |
| `Lean4Lean.Tests.ProjShape.P₀` | 160 | def | trproj | none |

### `Lean4Lean/Tests/IotaShape.lean` — 158 declarations, 0 reach `sorryAx`

Per-line blame: iota: 603 I / 4 P.

| declaration | line | kind | attr | axioms |
|---|---|---|---|---|
| `Lean4Lean.Tests.IotaShape.Ev.below.s` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Ev.below.z` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.EvI.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.EvI.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Fn.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Fn.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Fn.brecOn_1.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Fn.brecOn_1.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Le.below.refl` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Le.below.step` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.MA.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.MA.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.MA.brecOn_1.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.MA.brecOn_1.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.MA.brecOn_2.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.MA.brecOn_2.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.MB.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.MB.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Od.below.s` | -1 | ctor | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.OdI.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.OdI.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Refl.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Refl.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T2.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T2.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T2.brecOn_1.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T2.brecOn_1.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T2.brecOn_2.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T2.brecOn_2.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T2.brecOn_3.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T2.brecOn_3.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T2.brecOn_4.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T2.brecOn_4.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T3.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T3.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T3.brecOn_1.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T3.brecOn_1.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T3.brecOn_2.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T3.brecOn_2.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T4.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T4.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T4.brecOn_1.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.T4.brecOn_1.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Tree.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Tree.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Tree.brecOn_1.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Tree.brecOn_1.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.TreeP.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.TreeP.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.TreeP.brecOn_1.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.TreeP.brecOn_1.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.TreeQ.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.TreeQ.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.TreeQ.brecOn_1.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.TreeQ.brecOn_1.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.TreeQ.brecOn_2.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.TreeQ.brecOn_2.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Vec.brecOn.eq` | -1 | thm | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.Vec.brecOn.go` | -1 | def | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.matchPat.match_1.splitter` | -1 | def (private) | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.matchPat.match_3.splitter` | -1 | def (private) | unknown(no-range) | none |
| `Lean4Lean.Tests.IotaShape.matchPat.match_5.splitter` | -1 | def (private) | unknown(no-range) | std |
| `Lean4Lean.Tests.IotaShape.matchPat.match_7.splitter` | -1 | def (private) | unknown(no-range) | std |
| `Lean4Lean.Tests.IotaShape.P2` | 39 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.P2.a` | 39 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.P2.b` | 39 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.P2.mk` | 39 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.Vec` | 41 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.Vec.nil` | 42 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.Vec.cons` | 43 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.Ev` | 46 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.Ev.z` | 47 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.Ev.s` | 48 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.Od` | 49 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.Od.s` | 50 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.Tree` | 53 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.Tree.node` | 54 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.ruleShapeAt` | 56 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.instDecidableRuleShapeAt` | 63 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.checkShapes` | 66 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.matchPat` | 102 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.matchPat_sound` | 115 | thm | iota | std |
| `Lean4Lean.Tests.IotaShape.checkIota` | 136 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.checkTypesHaveRec` | 170 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.checkMore` | 176 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.resultSort` | 195 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.largeElimClause` | 201 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.recsOf` | 222 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.blockFailures` | 233 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.checkBlock` | 288 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.checkBlockRejected` | 294 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.checkIotaAuto` | 299 | def | iota/mixed | std |
| `Lean4Lean.Tests.IotaShape.checkAll` | 312 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.checkNested` | 323 | def | iota | std |
| `Lean4Lean.Tests.IotaShape.TreeP` | 339 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.TreeP.leaf` | 340 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.TreeP.node` | 341 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.T2` | 343 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.T2.mk` | 344 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.T3` | 346 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.T3.mk` | 347 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.MA` | 350 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.MA.mk` | 350 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.MB` | 351 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.MB.mk` | 351 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.T4` | 354 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.T4.mk` | 355 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.Refl` | 357 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.Refl.mk` | 357 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.Le` | 359 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.Le.refl` | 360 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.Le.step` | 361 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.Dep` | 363 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.Dep.mk` | 363 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.Dep.n` | 364 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.Dep.v` | 365 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.Dep.h` | 366 | thm | iota | none |
| `Lean4Lean.Tests.IotaShape.TreeQ` | 368 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.TreeQ.mk` | 369 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.Fn` | 371 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.Fn.mk` | 372 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.EvI` | 375 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.EvI.z` | 376 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.EvI.s` | 377 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.OdI` | 378 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.OdI.s` | 379 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.PropLarge` | 382 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.PropLarge.mk` | 383 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.Wrap` | 385 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.Wrap.mk` | 386 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.SigmaLike` | 388 | inductive | iota | none |
| `Lean4Lean.Tests.IotaShape.SigmaLike.mk` | 389 | ctor | iota | none |
| `Lean4Lean.Tests.IotaShape.badCtorType` | 396 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.goodCtorType` | 400 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.badCtorType_not_positive` | 404 | thm | iota | std |
| `Lean4Lean.Tests.IotaShape.goodCtorType_positive` | 405 | thm | iota | std |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.Pn` | 413 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.t1n` | 414 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.t2n` | 415 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.Rn` | 416 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.Pc` | 418 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.t1c` | 419 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.t2c` | 420 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.CT` | 421 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.M1T` | 422 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.M2T` | 423 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.RT` | 424 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.rhs1` | 425 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.rhs2` | 426 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.t1V` | 428 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.t2V` | 429 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.PT` | 430 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.ru1` | 432 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.ru2` | 433 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.RV` | 434 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.declB` | 439 | def | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.declB_wants_large` | 445 | thm | iota | none |
| `Lean4Lean.Tests.IotaShape.TwoCtorProp.declB_not_largeElimShape` | 448 | thm | iota/mixed | none |

### `Lean4Lean/Tests/ShapeDecide.lean` — 26 declarations, 0 reach `sorryAx`

Per-line blame: iota: 67 I / 11 P.

| declaration | line | kind | attr | axioms |
|---|---|---|---|---|
| `Lean4Lean.instDecidableEqVLevel` | 15 | def | iota | none |
| `Lean4Lean.instDecidableEqVLevel.decEq` | 15 | def | iota | none |
| `Lean4Lean.instDecidableEqVExpr` | 16 | def | iota | std |
| `Lean4Lean.instDecidableEqVExpr.decEq` | 16 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableExistsListEqMkAppsHAppend` | 20 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableExistsListAndEqNatMkAppsHAppend` | 23 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableExistsAndEqOptionSomeOfDecidablePred` | 27 | def | iota/mixed | none |
| `Lean4Lean.VExpr.instDecidableExistsVLevelEqSort` | 34 | def | trproj | std |
| `Lean4Lean.VExpr.instDecidableExistsNatEqBvar` | 35 | def | trproj | std |
| `Lean4Lean.VExpr.instDecidableExistsNameListVLevelEqConst` | 36 | def | trproj | std |
| `Lean4Lean.VExpr.instDecidableRecHeaded` | 38 | def | trproj | std |
| `Lean4Lean.VExpr.instDecidableCtorHeaded` | 39 | def | trproj | std |
| `Lean4Lean.VExpr.instDecidableMentionsConst` | 41 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableCtorResult` | 44 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableMajorApp` | 47 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableValidIndApp` | 50 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableFieldPositive` | 53 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableCtorPositive` | 56 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableFieldInIndices` | 59 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableMotiveShape` | 62 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableMinorHeaded` | 63 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableMinorFor` | 65 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableRecShape` | 67 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableCtorShape` | 69 | def | iota | std |
| `Lean4Lean.VExpr.instDecidableRuleShape` | 71 | def | iota | std |
| `Lean4Lean.instDecidableLargeElimShape` | 77 | def | iota | none |
