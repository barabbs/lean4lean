# Issue registry — lean4lean trproj (iota + trproj contributions)

Markdown companion to `blueprint/src/chapters/status.tex` section 4 ("Issue registry"), for the
orchestrator. Same content, same grouping (severity, then branch), `file:line` in place of
`\srcloc{}{}`, bracketed `[label]` in place of `\ref{}`. No fixes are proposed anywhere below.
Every entry cites its source(s) in parentheses; see `status.tex` for the full chapter (census,
live-sorry census with reach counts, trust boundary, blueprint limitations) this registry is
extracted from.

Repo: lean4lean, branch `trproj`, HEAD `20ec229`, Lean v4.33.0-rc2. Totals: **15 High, 46
Medium, 117 Low** (178 entries), consolidated and deduplicated from the 14 module chapters' own
"Review notes" sections, `reviews/*.md`, `hygiene-review.md`, `unused-contrib.md`, and
FALSE/PARTIAL verdicts in `claims-iota.md`/`claims-trproj.md`.

## Executive summary

1. 16 genuine live `sorry`s outside `Experimental/` (one listed row of `sorry-grep.md`,
   `Tests/ProjInhabit.lean:562`, is a false positive — a doc comment, not a `sorry`): 11 master,
   4 trproj, 1 iota.
2. The single iota sorry, `VEnv.WF.patsStrong` (`EnvLemmas.lean:334`), is the most consequential
   open obligation in the branch: it reaches 343 declarations through a silent `CoeOut`,
   replacing a theorem (`Ordered.strong`) master had proved outright.
3. trproj's strongest result, `TrEnv.proj_defeq`, is orphaned (its only consumer is a
   `#print axioms` test); `inferProj.WF` is documented in-source as not provable as stated, yet
   sits on the kernel's headline soundness theorems' import path.
4. Master's oldest hole, `addDecl.WF`'s `inductDecl` case (`Verify/Environment.lean:208`), is
   still `sorry`, so the ~1000-line `AddInduct` refinement apparatus both branches build on top
   of it is currently vacuous end-to-end — not a branch defect, but it bounds every claim built
   on it.
5. Net sorry effect of both branches outside `Experimental/`: 4 sorry-carrying files fully
   closed (3 stub definitions turned into real specifications, one comment describing a
   4th uninhabited placeholder), 1 new sorry (iota), a 7-to-2 reduction in the old `TrProj`
   family (trproj), a 1-to-2 increase in `InferType.lean` (trproj fixed a latent master bug and
   added one unreferenced new sorry).
6. Census: 629 of 7833 declarations (8.0%) are `sorryAx`-tainted project-wide; contributed code
   is 549 iota + 309 trproj + 241 mixed of 7298 attributed declarations (15%), concentrated in
   `Theory/` and `Verify/`, not `Tests/` or `kernel/`.
7. Trust boundary: 110 axioms + 12 opaques beyond the 3 standard ones exist project-wide; the
   heaviest-reach are master's pre-existing `Verify/Axioms.lean` core-implementation bridge
   (up to 229 declarations each) — not anything either branch added.
8. Recurring pattern across three chapters: iota's forced `Ordered`→`OrderedStrong` retype was
   applied uniformly rather than minimally in the primitives layers, silently tainting
   master-attributed declarations with `sorryAx`, undocumented in the consuming files'
   docstrings.
9. Hygiene: two pairs of duplicated re-merged commits, one file created then reverted inside the
   branch, ~27% of the branch's own written lines written and then removed within the branch;
   `Theory/` comment density (25.3% vs master's 1.7%) is the loudest stylistic signal, though the
   content itself is substantive rather than filler.
10. Verdict signal, not a defect tally: neither branch is slop by the reviews' own standard (no
    `native_decide`/`admit`/padding-only lemmas), but both branches' own documentation
    overclaimed at least once each (patsStrong's reach, and `TrProj`'s definition/trust surface
    in now-stale contribution notes) relative to what the code and census actually show.


## High severity


### iota

- `Lean4Lean/Theory/Typing/EnvLemmas.lean:334`: `VEnv.WF.patsStrong` is `sorry`, and the paired `CoeOut (VEnv.WF E) E.OrderedStrong` instance (line 343) makes every `VEnv.WF` hypothesis silently yield the strong-system hypotheses, so the entire strong system and the whole `Verify/` typechecker-correctness layer become conditional on it; `Verify/Primitive.lean` alone gained 30 mentions of `OrderedStrong`/`orderedStrong` where it had none on master. Master's corresponding entry point, `Ordered.strong`, was a proved theorem in a sorry-free file; it no longer exists. See section [status:sec:sorries] for the full 343-declaration reach. (typing, metatheory, primitives-core, primitives-arith Review notes; hygiene-review.md section (a); claims-iota #17, #28)

- `Lean4Lean/Theory/Typing/Basic.lean:60`: `IsDefEq.pat` asserts the reduct at the redex's type with no typing premise on the reduct, i.e. it builds subject reduction for iota into the judgment itself. The author's own counterexample (`Lean4Lean/Theory/Typing/EnvLemmas.lean:327`, `List Nat List Bool`) shows the assumption is false over a merely `Ordered` environment, so every lemma of `Lemmas.lean` proved under `Ordered` may characterise a relation strictly larger than the thesis's; `IsDefEqStrong.pat` ([inductive:isdefeqstrong-pat], `Lean4Lean/Theory/Typing/Strong.lean:89`) has the correct shape. Any claim of the form "lean4lean proves X about `IsDefEq`" must be qualified by `patsStrong`. (typing Review notes)

- `Lean4Lean/Verify/Environment/Basic.lean:583`: nothing derives `VInductDecl.WF` from the kernel's own inductive checker (`Lean4Lean/Inductive/Add.lean`). `TrEnv'.induct` takes `decl.WF env` as a bare hypothesis; `Tests/IotaShape.lean` validates the record by `decide` on concrete kernel data, which is evidence, not a proof. This is better than master (where the predicate itself was `sorry`), but the contribution should be described as specified and validated, not verified. (inductive Review notes)


### trproj

- `Lean4Lean/Verify/TypeChecker/InferType.lean:400`: `inferProj.WF`'s own docstring states it is not provable as stated, because kernel-accepted projections of reflexive, indexed and nested single-constructor structures have no [def:trproj] derivation at all. Since `inferType'.WF` consumes it and `checkType.WF` has no hypothesis that its input is translatable, the top-level statements `inferType.WF'` and `checkType.WF` (part of [thm:vtc-toplevel]) are, as of this HEAD, known to be unprovable without extending the model; neither weakening the conclusion nor adding a scope hypothesis is discussed. (typechecker Review notes; trexpr Review notes)

- `Lean4Lean/Verify/Environment/Lemmas.lean:1021`: `TrEnv.proj_defeq` ([thm:tr-env-proj-defeq]), trproj's strongest result connecting the projection model to a translated environment, is orphaned: its only consumer anywhere in the repository is the `#print axioms` check at `Lean4Lean/Tests/ProjInhabit.lean:595`. Its would-be consumers (`reduceProjCore.WF`, `inferProj.WF_struct`, `inferProj.WF`) are all `sorry`, and its premise `TrProjCtor` is itself only ever inhabited by hand in tests. (trenv Review notes; claims-trproj #25)

- `Lean4Lean/Verify/Environment/Primitive/Condition.lean:1236`: the `iota` retype of this chapter's hypotheses does not only enter at the attributed lines. `Reflection.WF.genTele` is master-attributed on every line of its statement and proof, yet is newly `sorryAx`-tainted on this branch: its one call `hXY'.subst E.wf` used to coerce `VEnv.WF` to `VEnv.Ordered` (what `IsDefEqU.subst` took on master), and that lemma now takes `VEnv.OrderedStrong`, so the identical text coerces the other way. Any line-count of "what the branch touched" understates its blast radius. (primitives-arith Review notes)


### master (pre-existing)

- `Lean4Lean/Theory/Typing/Injectivity.lean:11`: the whole file is three `sorry`'d inversion principles ([thm:injectivity-open]) and nothing else. They are what a proof of `patsStrong` is said to need, so the iota branch's open obligation rests on an already-open master foundation, and [thm:foralle-inv-derived] carries two independent gaps. (typing Review notes)

- `Lean4Lean/Theory/Typing/Strong.lean:679`: [struct:orderedstrong] makes the environment hypothesis of the strong system non-derivable in the way master's `Ordered.strong` was; theorems in `Strong.lean` are themselves `sorryAx`-free because they take `OrderedStrong` as a hypothesis, but every call site that discharges it from `VEnv.WF` — all of `UniqueTyping.lean` and through it `ChurchRosser.lean`, `HeadReduction.lean` and the `Verify` layer — is newly tainted. (metatheory Review notes)

- `Lean4Lean/Theory/Typing/ChurchRosser.lean:1193`: `NormalEq.parRed` contains two sorries (1193, 1212), both in the case where a rule step meets a normal equality (the thesis's Lemma `gg_compat`); this is the load-bearing step of Church--Rosser, so `ParRedS.church_rosser`, `CRDefEq.trans`, `IsDefEq.church_rosser`, `IsDefEq.reduce_sort`, `IsDefEq.reduce_forallE` and `InferType.exists` are all unproved. (metatheory Review notes)

- `Lean4Lean/Theory/Typing/UniqueTyping.lean:174`: the forward direction of `IsDefEqU.weakN_iff` is `sorry`, consumed by `NormalEq.weakN_inv_DFC`, `ParRed.weakN_inv`, `hasType_app_bvar0`, `IsDefEq.skips`, `OnCtx.weakN_inv` and the whole `weakN_iff`/`weak'_iff` family, hence most of `ChurchRosser.lean` and `HeadReduction.lean`. (metatheory Review notes)

- `Lean4Lean/Verify/Environment.lean:208`: the `inductDecl` case of `addDecl.WF` is `sorry`, and nothing anywhere constructs an [struct:add-induct] witness from `Environment.addInductive`; the whole inductive-block apparatus of both branches ([struct:add-induct], [struct:tr-ind-type], [thm:tr-env-proj-defeq], and the 1000 lines of lemmas built on them) is correct but, end to end, currently vacuous. (trenv Review notes; hygiene-review.md section (g), "HIGH (value, not hygiene)")

- `Lean4Lean/Experimental/ShapeLogRelAdequacy.lean:154`: a live `sorry` in the `const` case of `LR.adequacy`, the fundamental theorem of the shape logical relation. [thm:expa-forallE-inv], [thm:expa-sort-forallE-inv], [thm:expa-sort-inv] and everything `UniqueTyping.lean` (Experimental) derives from them are unproved; the hole predates the commit that landed the injectivity theorems and `UniqueTyping.lean` on top of it, and no comment in the source warns of it. (experimental-logrel Review notes)

- `Lean4Lean/Experimental/SExpr.lean:679`: `IsDefEq.strong` is `sorry`; both `LE_Interp.strongSound` and `LR.adequacy` open with `replace H := H.strong`, so the entire logical-relation layer from `ShapeLogRel.lean:5054` onward is conditional on it, on top of 29 further sorry-bearing lines in the same file (30 in all). (experimental-logrel Review notes)

- `Lean4Lean/Experimental/SExpr.lean:614`: `axiom Params.extra_pat` is a genuine global axiom, not a class field (the corresponding field is commented out of `class Params` at line 42); it asserts that every environment defeq is an instance of a registered pattern rule, the hard content of iota-reduction, invisible from the files that use it. (experimental-logrel Review notes)

- `Lean4Lean/Experimental/Thierry.lean:9` and `Lean4Lean/Experimental/Thierry2.lean:9`: `axiom mySorry : ` is an inhabitant of every type, i.e. a proof of `False`, used in `DF.comp`, `DF.bot` and elsewhere; both files are scratch formalizations imported by nothing, but the axiom must be on record so nothing downstream is ever allowed to depend on them. `Thierry2.lean` additionally axiomatizes the judgment it interprets. (experimental-reduction Review notes)


## Medium severity


### iota

- `Lean4Lean/Theory/Typing/EnvLemmas.lean:130`: `VEnv.PatsStrong` is a six-hypothesis statement with both environments explicit, so every call site reads `hp _ _ hpre₀ .rfl ... rfl rfl hord (eight sites), forcing the `*_strong` lemmas to repeat the same composition three or four times; since the statement is discharged only by `sorry`, it is also unverified that it is provable in this generality. (typing Review notes; hygiene-review.md section (a))

- `Lean4Lean/Theory/Typing/Basic.lean:92`: `VEnv.PatTyped` is existential in U,Gamma,e,m_2,B and `Pattern.RHS.Generic` constrains only the holes the reduct uses, so `PatWF`/`Ordered.pat` admits a rule that typechecks only at one convenient instantiation; documented at `Lean4Lean/Theory/Typing/Pattern.lean:181`, but the name promises more than the predicate delivers. (typing Review notes; hygiene-review.md section (a))

- `Lean4Lean/Theory/Typing/Basic.lean:62`: the `Pattern.Check`/`Realizes` side-condition machinery threaded through `IsDefEq.pat` and nine induction cases is exercised only at the trivial check: the one registration point, `VEnv.addRecRule`, hard-codes `Check.true`, and K-like reduction (the rule that would need a real side condition) is not modelled. Seven supporting lemmas and one premise per induction case support a condition no registered rule yet uses. (typing Review notes)

- `Lean4Lean/Theory/Typing/EnvLemmas.lean:188`: `addQuot_strong` hand-unrolls `addQuot`'s five steps into 25 lines of explicit `.trans` chains, brittle to any change to the quotient block, because `addQuot` is an `Option` bind chain rather than a fold and so cannot reuse `foldlM_addConst_strong`. (typing Review notes)

- `Lean4Lean/Theory/Typing/ChurchRosser.lean:30`: the docstring of `Params.pat_env` justifies the field by `extra_pat`, but the two fields are logically independent (one is about `env.defeqs`, the other about `env.pats`); the comment reads as if `pat_env` were derivable. (metatheory Review notes)

- `Lean4Lean/Theory/Typing/ChurchRosser.lean:12`: the `Params` class has exactly one construction, requiring `DefEqsAsPats`, which fails as soon as an environment contains a `def` or the quotient rule; the Church--Rosser/standardization/inference development of Chapter [chap:metatheory] therefore applies today to no realistic environment. Documented in the `DefEqsAsPats` docstring but not stated in the chapters that build on it. (metatheory Review notes)

- `Lean4Lean/Theory/Typing/Strong.lean:684`: the pair of `CoeOut` instances (`OrderedStrong`->`Ordered` and `VEnv.WF`->`OrderedStrong`) makes the new sorry-backed hypothesis invisible at use sites: `UniqueTyping.lean` is byte-identical to master yet silently acquired the `patsStrong` dependency. (metatheory Review notes)

- `Lean4Lean/Theory/Typing/Strong.lean:672`: the deferred obligation is heavier than "the iota rules of the final environment preserve types": `PatsStrongOn` is stated for one environment, while `VEnv.PatsStrong` quantifies over every well-formed prefix and every constant-only extension of it traversed by the strengthening induction. (metatheory Review notes)

- `Lean4Lean/Theory/Typing/InductiveParams.lean:393`: `toParams` is a `Params` instance only for environments satisfying `DefEqsAsPats` (no `def`, `mutualDef` or `quot` at all); every realistic Lean environment fails it, so the model's own well-formed environments are still not connected to the Church--Rosser development. (inductive Review notes)

- `Lean4Lean/Theory/Inductive.lean:174`: `VExpr.RuleShape` pins only the number of arguments the reduct passes to the minor premise, not their shape (the thesis requires the reduct’s recursive arguments to follow a specific lambda-abstracted recursor-call shape); together with `rules_wf`, which only forces well-typedness, `VInductDecl.WF` accepts iota rules the kernel would never generate. (inductive Review notes)

- `Lean4Lean/Theory/Inductive.lean:257`: K-like reduction is not modelled; `addRecRule` registers only the constructor rule and `VRecursor.k` is recorded but never used, while the kernel's `toCtorWhenK` does perform it. For K-like recursors the model's reduction relation is strictly weaker than the kernel's. (inductive Review notes)

- `Lean4Lean/Theory/Inductive.lean:93`: `FieldPositive`, `CtorPositive` and `WF.universes` read the manifest Pi-binders of a field type, whereas the kernel's `checkPositivity` reduces to whnf at each step; the model is strictly stricter than the kernel, which obstructs ever discharging the previous item. (inductive Review notes)

- `Lean4Lean/Theory/Inductive.lean:335`: `recs_over_block`/`rules_ctor` require every recursor to eliminate one of the block's own type formers, excluding nested inductives, which the kernel's `Environment.addInductive` does add; `TrEnv'` can never be constructed for such a block. Documented as future work. (inductive Review notes)

- `Lean4Lean/Verify/Environment/Basic.lean:272`: `AddInduct` carries no `: Prop` ascription, so it is `Type`-valued and the `induct` constructor of `TrEnv'` quantifies over data; necessary for the derived field projections, harmless for present (all-`Prop`-eliminating) consumers, but an undocumented departure from master's `inductive AddInduct ... : Prop`. (trenv Review notes)

- `Lean4Lean/Verify/Environment/Basic.lean:240`: `TrRecursor.all` and `TrRecursor.k` (line 245) are never used anywhere; extra proof obligations on [struct:add-induct]'s producer that buy nothing, `k` in particular recording a K-like flag the model has no corresponding rule for. (trenv Review notes)

- `Lean4Lean/Verify/Environment/Basic.lean:165`: `insertConsts_find?_none` is dead code, its only occurrence besides its own statement being its own recursive call. (trenv Review notes; unused-contrib.md)

- `Lean4Lean/Verify/Environment/Lemmas.lean:903`: `TrEnv.pats_iota_inv_shape` is redundant with `TrEnv'.pats_iota_inv_shape` (the proof is literally that lemma applied), and unlike its sibling `pats_iota'` it does not convert `SMap.find?` into `Environment.find?` despite its docstring's claim; `proj_defeq` still does the conversion by hand. (trenv Review notes)

- `Lean4Lean/Verify/Environment/Lemmas.lean:959` and `Lean4Lean/Verify/Environment/Lemmas.lean:1166`: misfiled material — the beta-telescope family and `TrExpr.mkAppList` are pure `VExpr`/`TrExpr` metatheory with no environment-translation content, living in `Verify/Environment/Lemmas.lean` only because `proj_defeq` needs them there. (trenv Review notes)

- `Lean4Lean/Verify/Environment/Lemmas.lean:917`: `TrEnv.iota_defeq` is a three-line wrapper over `VEnv.IsDefEq.pat` with no `TrEnv` hypothesis at all, yet is named as if it had one. (trenv Review notes)

- `Lean4Lean/Verify/Environment/Quot.lean:27`: `AddQuotAux` hand-replays the binder names, binder infos and `withLocalDecl` order of `Lean4Lean/Quot.lean` with nothing linking the two beyond the proofs breaking if they diverge; the `T..._tr` derivations (line 331) are 60 lines of hand-built [ind:trexprs] trees. Correct, expensive to maintain. (trenv Review notes)

- `Lean4Lean/Verify/Environment/Primitive/Condition.lean:421`: all 67 iota-attributed lines of Chapter [chap:primitives-arith] are the same `Ordered`->`OrderedStrong` re-threading; every theorem there now depends on `patsStrong` where on master it depended only on `Ordered`. The declaration site documents this in a comment; none of the consuming files does, and `DivMod.lean`/`Gcd.lean`/`Bitwise.lean` have no module docstring at all, so a reviewer reading any one of them in isolation would conclude the arithmetic primitives are fully verified. (primitives-arith Review notes)

- `Lean4Lean/Verify/Primitive.lean:29`: the same retype (`Ordered`-> `OrderedStrong`) was applied uniformly across Chapter [chap:primitives-core] rather than minimally; 19 declarations there gained `sorryAx` on master's route alone, when only 4 lemmas actually need the stronger hypothesis (through `HasType.const_inv`) and the rest could have kept `Ordered`. Reads as a global search-and-replace rather than a considered minimisation. (primitives-core Review notes)

- `Lean4Lean/Verify/Environment/Primitive.lean:6`: the module docstring's claim that "the checker, extension, and declaration modules introduce no additional sorry-backed assumptions" is still literally true but now understates the layer's real hypotheses (`OrderedStrong`, produced only by the admitted `patsStrong`); not revisited when the hypotheses were strengthened. (primitives-core Review notes)

- `Lean4Lean/Verify/Environment/Primitive/Basic.lean:856`: the syntactic guard `Expr.natBinderTypes` is a hypothesis of the well-founded-recursion theorems, not a check the recogniser performs; true by `rfl` at today's call sites, but the verified statement is conditional on a caller property the kernel never tests. (primitives-core Review notes)

- `Lean4Lean/Verify/TypeChecker/WHNF.lean:17`: `inductiveReduceRecCore.WF` ([thm:vtc-iota-reduce-core]) has no consumer; `reduceRecursor.WF` two declarations below is still `sorry` and a repo-wide grep finds no other reference. The contribution proves the hard arithmetic of the iota step but connects it to no statement about the kernel. (typechecker Review notes; hygiene-review.md section (g))

- `Lean4Lean/Verify/TypeChecker/WHNF.lean:24`: `hmaj` requires the major premise, as it occurs in the recursor spine, to already be a constructor application, whereas `inductiveReduceRec` passes a major obtained by `toCtorWhenK`, `whnf`, literal conversion and `toCtorWhenStruct`; the bridging step rebuilding the spine and transporting the translation is neither provided nor mentioned. (typechecker Review notes)

- `Lean4Lean/Verify/TypeChecker/WHNF.lean:23`: `hsat` (exact saturation of the constructor application) is assumed and the docstring calls it a consequence of well-typing "left to the caller", but that consequence is proved nowhere in the repository; it also excludes over-applied constructor applications, exactly where the kernel's and the pattern's argument-slicing conventions could genuinely disagree. (typechecker Review notes)

- `Lean4Lean/Verify/TypeChecker/InferType.lean:392`: `inferProj.WF_struct` is sorry and unreferenced (0 dependants, `sorry-grep.md` section 5); its docstring advertises coverage of `TrProjCtor`, which does not occur in its actual hypotheses (kernel-side metadata facts), and even proved it would not discharge [thm:vtc-inferproj] since its listed conditions are not the ones `inferProj` checks. (typechecker Review notes; proj Review notes; hygiene-review.md section (c))

- `Lean4Lean/Verify/TypeChecker/InferType.lean:398`: the whole projection story rests on `inferProj.WF_struct`, which is sorry, with its 15-line informal proof sketch living only in a docstring and mechanised only on two hand-built `Tests/ProjInhabit.lean` instances; nothing shows a kernel-accepted projection yields a `TrProjCtor`, so [def:trproj]'s `proj` case is never inhabited from a real term. (proj Review notes)

- `Lean4Lean/Theory/Proj.lean:127`: `VExpr.projTy` has no library consumer (only an `example`), and the identity its docstring asserts, projTy ... e = (projMotiveBody ... i).inst e, is never proved; the model types a projection through [def:proj-motive-body] instead, so the two readings of "the projection's type" coexist unreconciled, visibly so in `Tests/ProjShape.lean`'s own error message, which names `projTy` while the type actually checked is built from `projMotiveBody`. (proj Review notes)

- `Lean4Lean/Tests/ProjInhabit.lean:49`: `VEnv.addInduct` checks only name clashes and closedness, never well-formedness, and neither `VInductDecl.WF` nor `env.WF` is ever proved for the two hand-built environments; the witnesses show the premises of [struct:trprojctor] are jointly satisfiable, not satisfiable in a well-formed environment, so [thm:tr-env-proj-defeq] (which needs a `TrEnv`) is not exercised end to end on them. (proj Review notes)

- `Lean4Lean/Experimental/LogRel.lean:353`: `fundamental` is unproved and `LREqTy.defeq_r`, all three branches of `LREqTy.symm`, `LVIsType.sort` and `LVIsType.lift` are `sorry` or `stop` (which macro-expands to `repeat sorry` and so is invisible to `grep`); the module is imported by nothing and superseded by `ShapeLogRel.lean`. (experimental-logrel Review notes; master)

- `Lean4Lean/Experimental/LogRel.lean:70`: `Lean4Lean.SExpr.LogRel` is declared three times in this directory with incompatible definitions (inductive here, structure in `ShapeLogRel.lean` and in `MoreStepIndexed.lean`); likewise `Classifier'` and `NormalType` twice each. Compiles only because no module imports two of them. (experimental-logrel Review notes; master)

- `Lean4Lean/Experimental/ShapeLogRel.lean:1665`: lines 1665--1732 are a block comment holding an abandoned 58-line proof of a declaration (`Shape.WF.plift`) absent from the compiled environment, containing seven `sorry`s and a `stop`; this is why a naive `grep -c sorry` reports 8 for a file with no live sorry. (experimental-logrel Review notes; master)

- `Lean4Lean/Experimental/ShapeLogRel.lean:10`: `set_option backward.do.legacy true` at file scope, on a 6100-line file, works around leanprover/lean4#13305 for one proof family; large blast radius for a localised problem. (experimental-logrel Review notes; master)

- `Lean4Lean/Experimental/CoinductiveLogRel.lean:1`: almost entirely a block comment sketching a `coinductive` command that does not exist in Lean 4; its only live content is unused, yet the file still imports `HeadReduction.lean` and produces an olean under the `Lean4Lean.Experimental` glob. (experimental-logrel Review notes; master)

- `Lean4Lean/Experimental/ShapeLogRel.lean:3430`: the pattern-matching lemmas rest on the `Params` field `pat_wf`/`pat_uniq`, and there is no `Params` instance anywhere in the repository, so nothing exhibits an environment satisfying either. (experimental-logrel Review notes; master)

- `Lean4Lean/Experimental/ParallelReduction.lean:909`: the iota case added here, plus the `Typing.pat_env` field in `NormalEq.lean`, duplicates exactly what the branch added to `ChurchRosser.lean`; both files carry an upstream `TODO: remove, this is now part of ChurchRosser.lean`, so the iota rule is maintained in two places with no cross-reference. (experimental-reduction Review notes)

- `Lean4Lean/Experimental/SExpr.lean:981`: the chapter narrative calls `WHRed` deterministic, but `WHRed.determ`'s proof is sorry in all five case splits where an `extra` step meets anything, including another `extra` step; only the beta/application fragment is actually proved deterministic. (experimental-reduction Review notes)

- `Lean4Lean/Experimental/Stratified.lean:79` and `Lean4Lean/Experimental/StratifiedUntyped.lean:59`: the hypothesis of an exported theorem was silently strengthened from `Ordered env` to `OrderedStrong env`; forced and loses no realistic instance, but neither site explains it. (experimental-reduction Review notes)

- `Lean4Lean/Experimental/SExpr.lean:609`: the `SExpr` line of work still has no iota rule in its declarative equality; the pattern-based rule is commented out and reduction enters only through `env.defeqs` plus the global `Params.extra_pat` axiom, while `WHRed`/`ParRed` in the same file do carry a `Pat`-based rule. (experimental-reduction Review notes)

- `Lean4Lean/Experimental/UniqueTyping.lean:138`: no textual `sorry`, but `IsDefEq.toHasTypeS` opens with `h.strong` and `SExpr.IsDefEq.strong` is `:= sorry`; `uniq_sort`, `toIsDefEq'` and `iff_isDefEq'` are all conditional, so a grep-based status label would mislead. (experimental-reduction Review notes)

- `Lean4Lean/Experimental/DomainTheory.lean:223`: `Dom.out` is `sorryAx`-backed through the `stop` tactic despite no literal `sorry` in the file; the same pitfall recurs at `Lean4Lean/Experimental/LogRel.lean:320` and `Lean4Lean/Experimental/ShapeLogRel.lean:1703`. (experimental-reduction Review notes)

- `Lean4Lean/Experimental/MoreStepIndexed.lean:420`: a `#exit` truncates elaboration, so `TypeEqS`/`TypeEq`, the two declarations the file exists to build, are never compiled and do not appear in the environment; the file still builds green. (experimental-reduction Review notes)


### Documentation and process (iota/trproj, hygiene)

- `Theory/` comment density: contributed code is 25.3% comment lines against master's 1.7% in the same directory (`hygiene-review.md` section (c)); extremes are a 56-line module header on the 449-line `Lean4Lean/Theory/Proj.lean:3` and a 27-line docstring on the 5-line `DefEqsAsPats` (`Lean4Lean/Theory/Typing/InductiveParams.lean:351`, the longest docstring in `Theory/`; master's own `Theory/` maximum outside `LevelSat.lean` is 11 lines). The single loudest AI-authored-looking signal in the diff, though the content itself is substantive (derivations, thesis section numbers, explicit non-coverage statements) rather than restatement. (hygiene-review.md section (c))

- History hygiene: two pairs of commits are duplicated re-merges of a rebased `iota` (`655dd3f`/`75ffde9` share a patch-id; `7a68882`/`6fd8a1d` share a subject and are, per `typechecker.tex`'s own review note, literally the same patch under two branch labels, so blame over-attributes 141 lines of `WHNF.lean` to trproj that are really iota's); a whole file, `Theory/Pattern.lean`, was created over 4 commits and then deleted again 2 commits later without ever reaching the branch tip. Roughly 27% of the branch's own written lines (net +7762/-363, gross +11439/-3399) were written and then removed inside the branch, the two largest offenders being `Verify/Environment/Lemmas.lean` (22 commits) and `Theory/Typing/InductiveParams.lean` (14 commits, over half rewritten). (hygiene-review.md section (e); typechecker Review notes)


## Low severity


### iota

- `Lean4Lean/Theory/Inductive.lean:196`, `Lean4Lean/Theory/Inductive.lean:202`, `Lean4Lean/Theory/Inductive.lean:242`: dead code. `RecShape.one_le_numMotives`, `RecShape.majorFormer?_eq` and `LargeElim.shape` have no reference anywhere in the repository. (inductive Review notes; unused-contrib.md #45,#46,#47)

- `Lean4Lean/Theory/Typing/Pattern.lean:509`: the `RHS.spine`/`iotaCounts` cluster (8 declarations, 70 lines, lines 509--678) is used only by itself, ending in `iotaRHS_iotaCounts`, which exists only to substantiate a section docstring's claim. (inductive Review notes; hygiene-review.md section (g); unused-contrib.md #60)

- `Lean4Lean/Theory/Typing/InductiveLemmas.lean:451`: placement/naming. `nodup_map_inj_on` is a pure `List` lemma declared as `Lean4Lean.VEnv.nodup_map_inj_on`; the generic `foldlM` toolkit and the `addQuot`/`addDefEqs` lemmas live in a file named `InductiveLemmas`; `Pattern.inter_app_const` and two siblings are `_root_` `Pattern` lemmas declared inside `namespace VEnv`. (inductive Review notes)

- `Lean4Lean/Theory/Inductive.lean:259`: `addRecRule` spells the major index out by hand (`numParams + numMotives + numMinors + numIndices`) instead of using `r.getMajorIdx`, which every lemma about it does use, and its own docstring claims "major at `getMajorIdx`". (inductive/syntax Review notes; hygiene-review.md section (c))

- `Lean4Lean/Theory/Inductive.lean:75`, `Lean4Lean/Theory/Inductive.lean:107`, `Lean4Lean/Theory/Inductive.lean:226`: fidelity gaps against the kernel. `ValidIndApp` drops the kernel's exact-arity check although its docstring claims to mirror `isValidIndApp?`; `FieldInIndices` searches only arguments past `nparams` where the kernel searches all of them; `LargeElim` tests a typing at `sort 0` where the kernel tests `isAlwaysZero` on the inferred level. The three agree only up to unrecorded side arguments. (inductive Review notes)

- `Lean4Lean/Theory/Inductive.lean:351`: `WF.universes` hides the purely syntactic bound `decl.nparams` `t.type.piArity` inside a clause guarded by `addTypes` succeeding, so it is unavailable if stage 0 fails; and no clause of `VInductDecl.WF` mentions `VRecursor.all`. Neither is recorded in the source. (inductive Review notes)

- `Lean4Lean/Theory/Inductive.lean:134`: `MinorFor` makes the constructor-to-minor map injective but no lemma derives that and nothing uses it; the proofs that need injectivity appeal to `rules_nodup` instead. (reviews/inductive.md)

- `Lean4Lean/Theory/VExpr.lean:919`: dead upstream code created by a refactor. Master's one-line proof of `lift'_inst_hi` was replaced by a re-derivation from a new `lift'_instN_hi`, leaving `lift_r_one` (and the chain that fed only it — `Subst.lift_r_comm`, `Subst.trunc`, `Subst.Depth.one`, `Subst.Depth`, 6 declarations) with no remaining consumer. (syntax Review notes; hygiene-review.md section (g))

- `Lean4Lean/Theory/VExpr.lean:1232`: `CtorHeaded.forallE` is unused, proved by `:= h` because definitionally trivial, and its docstring states a different proposition than the lemma. (syntax Review notes; hygiene-review.md section (a),section (c))

- `Lean4Lean/Theory/VExpr.lean:1046`: stale section docstring, still promising readers decidability instances that were relocated to `Tests/ShapeDecide.lean`. (syntax Review notes; hygiene-review.md section (c))

- `Lean4Lean/Theory/VExpr.lean:753`: `Lift.liftVar_consN_lt` and `liftVar_consN_succ` have no consumer, making `Lift.consN_fixes` dead in effect too; of the four-lemma block only `consN_cons` is used. (syntax Review notes; unused-contrib.md #63,#64)

- `Lean4Lean/Theory/VExpr.lean:1009`: redundancy left unresolved and inconsistently. `subst_instN` subsumes master's `subst_inst` at n=0 and `liftN_subst_liftN` subsumes master's `lift_subst_lift` at i=0 (the latter's own docstring says so), yet both master lemmas keep independent hand proofs while `lift'_inst_hi` in the same block *was* re-derived; also, `subst_instN`'s docstring says "under `m` binders" while the statement binds `n`. (syntax Review notes; hygiene-review.md section (c))

- `Lean4Lean/Theory/VExpr.lean:1133`: the lambda-telescope block (`lamBinders`, `lamBinders_length`, `foldr_lam_lamBinders`) has exactly one consumer, and `lamBinders_length` is reached only through `simp`, not by name; thin, but not dead. (syntax Review notes)

- `Lean4Lean/Theory/VExpr.lean:1295`: `const_mkApps_spine` bundles two independent facts into one conjunction consumed only as `.1`/`.2`, and together with `eq_const_mkApps_of_spine` has no consumer outside the file. (syntax Review notes; unused-contrib.md #67)

- `Lean4Lean/Theory/VExpr.lean:1200`: a docstring attached to `isSort` alone describes all six declarations of the block, which exists only to serve the decidability instances of the test file. (syntax Review notes)

- `Lean4Lean/Theory/VExpr.lean:108`: `decClosedN` stayed in the theory file while sibling head-shape instances moved to `Tests/ShapeDecide.lean`; it is the one such instance a *definition* (`VEnv.addRecRule`) depends on, which the module docstring does not flag as the exception. (syntax Review notes)

- `Lean4Lean/Theory/VDecl.lean:51`: `VRecursor.getFirstIndexIdx` is defined and documented but has no consumer anywhere; every other use of the concept calls Lean's own `RecursorVal` field. (syntax Review notes; hygiene-review.md section (a))

- `Lean4Lean/Theory/VDecl.lean:41`: `VRecursor.k` records the K-like flag but is, by its own docstring, unused by the theory; the structure advertises coverage the development does not have. (syntax Review notes)

- `Lean4Lean/Theory/VEnv.lean:44`: `VEnv.addPat` cannot fail — unlike `addConst` it performs no freshness or consistency check, so an `Ordered` environment may carry two conflicting reducts for one pattern until `VEnv.WF` recovers functionality downstream. (syntax Review notes; hygiene-review.md section (a))

- `Lean4Lean/Theory/Quot.lean:11`: after the iota work the model has two mechanisms for computation rules (`quotDefEq` is still a `VDefEq`, not a `pats` entry); the duplication is acknowledged nowhere in the code. (syntax Review notes)

- `Lean4Lean/Theory/Proj.lean:111`: [def:proj-fns] mentions itself twice in its own defining equation, so the unfolded expansion of field i is exponential in i and every substitution lemma applies its induction hypothesis twice. (proj Review notes)

- `Lean4Lean/Theory/Proj.lean:195`: [def:proj-inst-fields] is a second telescope-substitution convention beside master's `VExpr.insts`; no lemma relates them, so the two only ever meet through raw `inst`. (proj Review notes)

- `Lean4Lean/Theory/Proj.lean:136`: [def:proj-binder-arity] pins only the number of the minor premise's binders, not their types, yet its docstring and `TrProjCtor.minor_arity` read it as pinning the fields exactly. (proj Review notes)

- `Lean4Lean/Theory/Proj.lean:140`: [def:proj-ty] has no library consumer, and `projMotiveBody_zero`/`instFields_nil` are `@[simp]` but never invoked explicitly. (proj Review notes; hygiene-review.md section (c))

- `Lean4Lean/Theory/Proj.lean:1`: the thesis citations attached to the projection work (`inv_x`, typesys.tex; pi_2, Wtypes.tex) are individually accurate but are borrowed idioms from results that prove different things, not inherited theorems. (proj Review notes)

- `Lean4Lean/Tests/ShapeDecide.lean:20`: 22 global `Decidable` instances declared from a `Tests` module (21 in `Lean4Lean.VExpr`); safe only because nothing in the library imports the module, and the widest of them (`Lean4Lean/Tests/ShapeDecide.lean:27`) decides an existential over any `Option`/`DecidablePred` pair, not a library predicate at all. (proj Review notes; hygiene-review.md section (d))

- `Lean4Lean/Tests/IotaShape.lean:151`: the iota oracle is lean4lean's own `inductiveReduceRec`, whose iota step is the 21 trproj lines of `Inductive/Reduce.lean`, so both sides of the comparison live in this repository; a shared misreading would not be caught. (proj Review notes)

- `Lean4Lean/Tests/IotaShape.lean:86`: the `recs_elim` check assumes the recursor's extra universe parameter sits at index 0 of `levelParams`, which is how Lean generates recursors but is nowhere checked. (proj Review notes)

- `Lean4Lean/Tests/IotaShape.lean:295`: `checkBlockRejected` only asks that *some* block clause fail; which clause a nested block is expected to fail is pinned for one fixture (`Tree`) and discarded for the other eight. (proj Review notes)

- `Lean4Lean/Tests/IotaShape.lean:336`: the fixture docstring mislabels `Wrap` as small-eliminating; it is in fact subsingleton-eliminating and carries the extra universe parameter (only the wording is wrong; the fixture is exercised correctly). (proj Review notes)

- `Lean4Lean/Tests/IotaShape.lean:454`: the whole battery is one 150-line `run_meta` block, so a failure reports only the first mismatch and every later assertion, including the remaining negative controls, is never reached. (proj Review notes)


### trproj

- `Lean4Lean/Verify/Typing/Lemmas.lean:643`: [def:trproj] existentially quantifies six pieces of data, two of which are pinned by other fields (parameter count by `params_length`, field telescope by `ctor`); replacing them by definitions would remove an obligation from each of the three proofs that rebuild the record. (trexpr Review notes)

- `Lean4Lean/Verify/Typing/Expr.lean:97`: `TrProjCtor.pat` asserts only that *some* reduct is registered under the iota key; the reduct itself is not pinned and the key, a sum, does not exclude a different motive/minor/index split adding to the same total. Is the stated obstacle to [thm:trproj-uniq]. (trexpr Review notes)

- `Lean4Lean/Verify/LocalContext.lean:183`: a global `DecidableEq FVarId` instance is installed inside `namespace Lean.LocalContext`, under a section heading about the empty local context, though it has nothing to do with `LocalContext` and could have reused `instDecidableEqOfLawfulBEq` as `DefinitionSafety` does nearby. (trexpr Review notes; hygiene-review.md section (d))

- `Lean4Lean/Verify/Typing/Lemmas.lean:2349`: `TrExprS.mkAppList_inv` overlaps with the pre-existing `AppStack.build`, leaving two spine-inversion idioms in one file. (trexpr Review notes)

- `Lean4Lean/Verify/Expr.lean:745`: of the three spine lemmas added here, only `getAppArgsList_mkAppList` has an explicit consumer; `getAppArgsRevList_mkAppList` has no consumer outside its own file. (trexpr Review notes)

- `Lean4Lean/Verify/Typing/Expr.lean:84`: the scope paragraph of `TrProjCtor` makes precise prose claims about the kernel's `inferProj` that nothing in the repository formalizes; the completeness boundary is asserted, not verified. (trexpr Review notes)

- `Lean4Lean/Verify/LocalContext.lean:181`: within the iota block, `toList_empty` and `WF.empty` exist only to serve `find?_empty` three lines later. (trexpr Review notes)

- `Lean4Lean/Verify/Environment/Quot.lean:521`: mechanical repetition — `addQuot.WF` extracts four `checkName` results with four near-identical seven-line blocks and rebuilds `safePrimitives` with a 22-line hand-nested chain that a single auxiliary lemma would remove. (trenv Review notes)

- `Lean4Lean/Verify/Environment/Quot.lean:20`: `withLocalDecl_run` lands in the root namespace under a very general name; `AddQuotAux.Environment.get_ok` is a generally useful lemma buried in a private auxiliary namespace. (trenv Review notes)

- `Lean4Lean/Verify/Environment/Basic.lean:34`: some lines the per-line blame marks as contributed are master code relocated by refactor commits (`TrConstant.sf_mono`/`mono`, `TrConstVal.mono`, `TrDefVal.mono`, `insertDefs_wf`); 16 of the 398 iota lines in `Basic.lean` are of this kind, so raw line counts overstate the branch slightly. (trenv Review notes, "reviewer caveat, not a defect")

- `Lean4Lean/Verify/TypeChecker/Reduce.lean:143`: `reduceProjCore.WF` and `tryEtaStructCore.WF` are the two structure-side obligations the richer `TrProj`/`TrProjCtor` metatheory was built to support, and neither was attempted; since the branch closed 5 of master's 7 `TrProj` sorries elsewhere, leaving these untouched makes the visible contribution narrower than its supporting infrastructure. (typechecker Review notes)

- `Lean4Lean/Verify/TypeChecker/WHNF.lean:1`: the precomputed blame tags all 141 lines of this file as trproj, but `git diff iota trproj` on the file is empty and the iota/trproj commits are the same patch with the same author date; any line count of "trproj lines" over-attributes this file. (typechecker Review notes; see Documentation/process above)

- `Lean4Lean/Verify/TypeChecker.lean:21`: `VEnvs.axiom_of_choice` is a deliberately misleading name for a finite case split; documented as such, but will still surprise a grep-based audit for appeals to choice. (typechecker Review notes)

- `Lean4Lean/Tests/ProjShape.lean:136`: the `Sigma.snd` level-list negative control wraps `checkProj` in `try ... catch _ => pure false, so any unrelated failure makes the control pass vacuously. (proj Review notes)

- `Lean4Lean/Tests/ProjShape.lean:78`: `(VLevel.ofLevel lps (lvls j)).getD .zero` and `toLevel`'s `ls.getD i .anonymous` silently default a mistyped level argument instead of failing. (proj Review notes)

- `Lean4Lean/Tests/ProjShape.lean:113`: the agreement between [def:proj-motive-body] and the kernel's `inferProj` is checked with `isDefEq`, which on the kernel side may use structure eta and projection reduction the model deliberately lacks; establishes agreement up to kernel conversion, strictly weaker than anything the model reproduces. (proj Review notes)

- `Lean4Lean/Tests/ProjInhabit.lean:586`: the `#guard_msgs in #print axioms` block hardcodes a seven-element axiom list, brittle under any unrelated upstream proof change, and the prose attribution of `sorryAx` to unique typing and Pi-injectivity is a claim the guard cannot itself verify. (proj Review notes)

- `Lean4Lean/Tests/ProjInhabit.lean:179`: the `Plain` and `Dependent` namespaces duplicate about 20 near-identical declarations, `Dependent` subsuming `Plain` except for one case; untracked near-copies also sit in `review-artifacts/inhabitation/`. (proj Review notes)

- `Lean4Lean/Tests/ProjInhabit.lean:172`: asymmetric packaging — `Plain` exposes `trProj0` but no `trProj1`; `Dependent` exposes `trProjDep1` but no `trProjDep0`. (proj Review notes)

- `Lean4Lean/Tests/ProjInhabit.lean:353`: 22 declarations for a six-step reduction, because `IsDefEqU.betaN` needs `VEnv.WF`, which these hand-built environments lack; separately, 50 namespace-level one-use theorems (`hbeta5`, `hc5`, ...) are declared where upstream style would use local `have`s. (proj Review notes; hygiene-review.md section (d))

- `Lean4Lean/Tests/ProjShape.lean:155`: several top-level definitions (`usS`, `ps`, `Fs`, `structTy`, `P₀`) use maximally generic names inside an unscoped section. (hygiene-review.md section (d))

- `.github/workflows/ci.yml:25`: the comment states `Lean4Lean.Tests` is among `defaultTargets`, but `lakefile.toml:2` lists only `Lean4Lean`, `lean4lean`, `Lean4Lean.Theory` and `Lean4Lean.Verify`; the test modules are in fact built by a separate CI step, so nothing is unchecked, but the comment is wrong. (proj Review notes)

- `Lean4Lean/Experimental/StratifiedUntyped.lean:51`: the added `IsDefEqU1.pat` constructor is never eliminated; its only would-be consumer is inside a commented-out block. (experimental-reduction Review notes)

- `Lean4Lean/Experimental/Stronger.lean:28`: `pats _ _ := False` silently restricts every theorem about erased environments in the file to iota-free ones; pragmatic, since the file dead-ends in four sorries regardless. (experimental-reduction Review notes)

- `Lean4Lean/Inductive/Reduce.lean:71`: `inductiveReduceRecCore`, the 21-line ι-step extraction trproj carved out of `inductiveReduceRec`, sits inside a `section` whose `variable`s (`[Monad m], env, whnf, inferType, isDefEq`) it does not use; correct today only because Lean binds `variable`s on use, so a future reference to `env` would silently change its signature. (kernel Review notes; hygiene-review.md section (f))


### master (pre-existing)

- `Lean4Lean/Inductive/Reduce.lean:91`: after the trproj split, the unchanged master docstring of `inductiveReduceRec` still describes the iota slicing in full, now `inductiveReduceRecCore`'s job and documented there too, so the algorithm is stated twice. (kernel Review notes)

- `Lean4Lean/TypeChecker.lean:946`: `TypeChecker.etaExpand` has no call site anywhere under `Lean4Lean/`; if it realizes the thesis's rec-normal-form preprocessing, that intent is undocumented and unenforced. (kernel Review notes)

- `Lean4Lean/ForEachExprV.lean:25`: `Expr.forEachV`/`forEachV'` appear dead; the module is imported by `TypeChecker.lean` but neither function has a call site. (kernel Review notes)

- `Lean4Lean/TypeChecker.lean:593`: `quickIsDefEq` destructures `TypeChecker.State` positionally as `.mk a1 ..., a7 (eqvManager := m); reordering or adding a field would silently or confusingly change what this matches. (kernel Review notes)

- `Lean4Lean/TypeChecker.lean:299`: the `eagerReduce` marker (consulted at four sites) has no thesis counterpart and no local docstring stating what the sites jointly guarantee, though it mirrors core Lean's own gadget and is correctly absent from `divergences.md`. (kernel Review notes)

- `Lean4Lean/Inductive/Add.lean:453`: `AddInductive.run` computes its `isUnsafe` binding twice (lines 453 and 470), the second silently shadowing the first. (kernel Review notes; hygiene-review.md section (f))

- `Lean4Lean/TypeChecker.lean:493`: `reducePowMaxExp` silently declines to reduce `Nat.pow` above exponent 2^24 (matching the C++ kernel's own cap), but the incompleteness is not listed in `divergences.md`. (kernel Review notes)

- `Lean4Lean/TypeChecker.lean:845`: the `s.isConstOf "true` shortcut in `isDefEqCore'` is an asymmetric special case with neither a thesis counterpart nor a `divergences.md` entry. (kernel Review notes)

- `Lean4Lean/TypeChecker.lean:355`: `reduceProj` is written in an awkward explicit-bind style for the benefit of its own proof, and a commented-out scratch block is left at the end of the file (line 968). (kernel Review notes)

- `Main.lean:29`: `FuelConfig.toObj` uses `panic!` when the derived JSON encoding is not an object, inside a command-line argument parser. (kernel Review notes)

- `Lean4Lean/FuelConfig.lean:12`: the docstring's claim "Defaults are set so mathlib passes" has zero supporting evidence anywhere in the repository (no CI job, test or benchmark mentions mathlib). (reviews/kernel.md)

- `divergences.md:17` vs. `divergences.md:19`: internal inconsistency in the project's own divergence log. Entry 17 correctly states lean4lean does *not* recheck the constructor/recursor declarations restored after nested-inductive elimination; entry 19 asserts the opposite. Reading `Environment.addInductive` (`Lean4Lean/Inductive/Add.lean:733`) confirms entry 17: the restored declarations are inserted with a bare `.add`, no further `checkType`/`isDefEq` call. Not a blueprint issue, but confusing for the next reader of that file. (reviews/kernel.md)

- `Lean4Lean/PtrEq.lean:17`: the two pointer-equality soundness axioms are genuine trusted assumptions, honestly documented and used in only two places, but at `Lean4Lean/TypeChecker.lean:739` `ptrEqConstantInfo` gates a different algorithm rather than a shortcut. (kernel Review notes)

- `Lean4Lean/Verify/Environment.lean:208`: `addDecl.WF`'s `inductDecl` case is sorry, so everything either branch proves about inductive blocks lives on the model side of that gap; master's hole, not a contributed one, but it bounds every claim built on it. (kernel Review notes; see High severity above for the fuller framing)

- `Lean4Lean/Verify/Environment/Primitive.lean:73`: a documented-but-dead cluster (`AddsConsts`, `constants_stable`, `constants_of_mem`, `PrimitiveInductiveResult`, `checkInductive.WF`, ..., 123 of the file's 195 lines) waits on the same `addDecl.WF` case above; `AddsConsts` itself is constructed nowhere. (primitives-core Review notes)

- `Lean4Lean/Verify/Environment/Primitive.lean:121`: `AddsConsts.hasPrimitives_bool` and `.hasPrimitives_nat` are byte-for-byte the same proof script with the constant list swapped. (primitives-core Review notes)

- `Lean4Lean/Verify/Environment/Primitive/Basic.lean:318`: namespace inconsistency for `List` helpers — some declared with `_root_.`, others declared bare inside `namespace Lean4Lean` and so landing in the shadow `Lean4Lean.List`. (primitives-core Review notes)

- `Lean4Lean/Verify/Environment/Primitive/Recursion.lean:587`: `unfoldNatWellFounded.WF'` is a single 1135-line tactic proof requiring `maxHeartbeats 1000000`, not practically reviewable at that size; its `BlockQ` docstring is also stale (says two checks are recorded, the definition records four). (primitives-core Review notes)

- `Lean4Lean/Verify/Environment/Primitive/Recursion.lean:376`: three adjacent lines spell the same environment coercion three different ways after the iota merge. (primitives-core Review notes)

- `Lean4Lean/Verify/Primitive.lean:458`: small pre-existing interface asymmetries — `ReflectsNatNat'.of_pred_equations` hard-codes `Nat.pred` instead of taking it as a parameter, unlike its six siblings; `VExpr.liftN_lams` returns only an existential where `liftN_lams'` computes the lifted domains. (primitives-core Review notes)

- `Lean4Lean/Verify/Environment/Primitive/Condition.lean:26`: stale module docstring — says `Nat.bitwise`/`unfoldNatWellFounded`'s `Condition.check` calls "currently sit under binders" when the hoisting it describes as future work (`Lean4Lean/Primitive.lean:409`, `372`) has already happened, which is why `Bitwise.lean`/`Gcd.lean` can pass `rfl` for `hnil`. (primitives-arith Review notes)

- `Lean4Lean/Verify/Environment/Primitive/Condition.lean:1448`: inconsistent spelling of the same coercion within one proof (`c.Ewf.orderedStrong` vs. bare `c.Ewf` relying on `CoeOut`, at 1448--1451 and 1850--1851). (primitives-arith Review notes)

- `Lean4Lean/Verify/Environment/Primitive/Bitwise.lean:41`: the local abbreviation `hE := ctx.Ewf.orderedStrong` carries the wrong strength for 7 of its 12 uses, which immediately downgrade it with `hE.ordered`; `Gcd.lean` made the same edit without needing any downgrades. (primitives-arith Review notes)

- `Lean4Lean/Verify/Environment/Primitive/Bitwise.lean:31`: `checkNatBitwise.WF` has no docstring, unlike every other clause-level `WF` theorem in the group, and is the longest (375 lines) and most intricate declaration in the chapter. (primitives-arith Review notes)

- `Lean4Lean/Verify/Environment/Primitive/Clauses.lean:225`: `checkNatLAnd.WF`, `checkNatLOr.WF` and `checkNatXor.WF` are near-identical 25--30-line proofs; `checkNatBoolCases.WF` nearby shows the parametrised alternative. (primitives-arith Review notes)

- `Lean4Lean/Verify/Environment/Primitive/Condition.lean:2438`: `Condition.fvarsIn_ite` is dead code; its sibling `fvarsIn_dite` is used once. (primitives-arith Review notes)

- `Lean4Lean/Verify/Environment/Primitive/Condition.lean:713`: `TrExprS.bvar0` through `bvar3` are the only declarations in the file escaped with `_root_` to `Lean4Lean.TrExprS`, easily confused with the generic `TrExprS` API. (primitives-arith Review notes)

- `Lean4Lean/Verify/TypeChecker/IsDefEq.lean:211`: a commented-out `have` is left inside `tryEtaExpansionCore.WF`'s proof. (typechecker Review notes)

- `Lean4Lean/Verify/TypeChecker/Reduce.lean:21`: `reduceBinNatOpG`, an executable definition, is introduced inside a verification file as a generalisation of the kernel's own `reduceBinNatOp`, duplicating kernel code in a proof file. (typechecker Review notes)

- `Lean4Lean/Tests/Level.lean:8`: states that canonicity of `normalize'` and completeness of `isEquiv'`/`geq'` are *not* proved; all three now are (`Lean4Lean/Verify/Level.lean:3849`, `3861`, `3870`). Stale doc/code mismatch. (levels Review notes)

- `Lean4Lean/Verify/Level.lean:41`: `mkData_depth`, `mkData_hasParam` and `mkData_hasMVar` are referenced nowhere in the project and are the only consumers of the `Lean.Level.mkData_eq` axiom, needing `allowUnsafeReducibility` to elaborate. (levels Review notes)

- `Lean4Lean/Verify/EquivManager.lean:81`: `RelevantEq.uniq` and two dependent theorems reach `sorryAx` through `TrProj.uniq`, because `RelevantEq`'s `proj` case compares two projections by index alone, ignoring the structure name; this sits on the main path of the verified type checker's memo cache (`Lean4Lean/Verify/EquivManager.lean:325`), not in a corner. (levels Review notes)

- `Lean4Lean/Verify/LevelStd.lean:155`: stale doc comment naming two lemmas (`qsort_perm_toList`, `pairwise_qsort_normLt`) as unproved and nonexistent; both facts are now proved under different names. (levels Review notes)

- `Lean4Lean/Verify/Level.lean:3822`: `normalize'_eval`, `normalize'_complete`, `isEquiv'_complete`, `geq'_wf` and `geq'_complete` are used nowhere; the reconstruction layer supporting `normalize'` (roughly lines 1290--2250) supports a function the kernel never calls. (levels Review notes)

- `Lean4Lean/Verify/Level.lean:16`: a commented-out `VLevel.toLevel` definition and a `toLevel_inj := sorry` are left in the file; the only occurrence of the token `sorry` in this master-only group. (levels Review notes)

- `Lean4Lean/Verify/Level.lean:1`: no module docstring on a 3880-line file; a reader reaches line 166 before learning the file formalizes Géran's canonical form. (levels Review notes)

- `Lean4Lean/Verify/EquivManager.lean:41`: `RelevantEq.symm`, `.trans` and `M.WF.bind_le` are never used anywhere. (levels Review notes)

- `Lean4Lean/Verify/NormLt.lean:6`: the header overstates what is proved ("a strict weak order") against what is exported (asymmetry and negation-transitivity, exactly what `Array.qsort_sorted` needs). (levels Review notes)

- `Lean4Lean/Verify/QSort.lean:34`: vendored code still carrying upstream TODOs ("these attributes still need to be moved to the standard library"), commented-out attribute experiments, and global `grind`-lemma registrations that every importer inherits. (levels Review notes)

- `Lean4Lean/Verify/QSort.lean:27`: no public theorem gives `(qsort as lt lo hi)[i] = as[i]` outside `[lo,hi]`; the private lemmas exist but are not exported. Latent limitation, not a defect for the current consumer. (levels Review notes)

- `Lean4Lean/Verify/Level.lean:1222`: end-to-end theorems each thread five to seven separate side conditions about `normalize u` by hand rather than through one bundled predicate. (levels Review notes)

- `Lean4Lean/Verify/Level.lean:3177`: `Std.TreeMap` as the representation costs a whole `toList`-factoring layer (150 lines); a sorted-association-list representation would have avoided it. (levels Review notes)

- `Lean4Lean/Verify/NormLt.lean:97`: `baseCmp_swap` and `normLtAux_eq` close several goals with bare `grind`/`simp_all`, not independently checkable by reading; `QSort.lean` is `grind`-first throughout. (levels Review notes)

- `Lean4Lean/Verify/NormLt.lean:47`: `baseCmp` duplicates its `max` and `imax` arms verbatim; `getUndefParam_none` (`Lean4Lean/Verify/Level.lean:101`) is dense and hard to follow. (levels Review notes)

- `Lean4Lean/Verify/EquivManager.lean:313`: `addEquiv.WF` and `isDefEq.WF` live in `Lean4Lean.TypeChecker.Inner` rather than `EquivManager`; defensible but surprising. (levels Review notes)

- `Lean4Lean/Experimental/ShapeLogRel.lean:53`: `Shape` is a `def` by recursion on `Nat` rather than an inductive family, so essentially every order/lift/join/ typing lemma is stated three times (for `Shape`, `WShape`, `TShape`); the first 2500 lines are this boilerplate. (experimental-logrel Review notes)

- `Lean4Lean/Experimental/ShapeLogRel.lean:3333`: 13 docstrings in 6100 lines, none on the pivotal definitions (`Shape.WF`, `LE_Interp`, `LR`, ...); two sit on self-evident lemmas instead. (experimental-logrel Review notes)

- `Lean4Lean/Experimental/ShapeLogRel.lean:3936`: proof-size hygiene — several single-tactic-block proofs of 100--330 lines with no internal comments, essentially unreviewable by anyone but the author. (experimental-logrel Review notes)

- `Lean4Lean/Experimental/ShapeLogRel.lean:820`: `Shape.trim` is defined and never used. (experimental-logrel Review notes)

- `Lean4Lean/Experimental/ShapeLogRel.lean:2716`: `find_cycle`, a reusable pigeonhole lemma, is declared `private` in the middle of a shape file; belongs in `Lean4Lean/Std` or upstream. (experimental-logrel Review notes)

- `Lean4Lean/Experimental/ShapeLogRel.lean:6100`: the file ends after `LR.SubstWF.symm` without closing either open namespace and with no pointer to `ShapeLogRelAdequacy.lean`, where the development continues. (experimental-logrel Review notes)

- `Lean4Lean/Experimental/ShapeLogRel.lean:1887`: `TShape.type` has no `TShape.prop` counterpart, and the head-discrimination grid omits two of its fourteen pairs with no comment distinguishing omission from oversight. (experimental-logrel Review notes)

- `Lean4Lean/Experimental/ShapeLogRel.lean:4623`: `StrongSoundCore.const` takes a bundle for every classification of a constant, though a constant has exactly one; whether the generality is ever exercised is unchecked. (experimental-logrel Review notes)

- `Lean4Lean/Experimental/ShapeLogRel.lean:1392`: a `variable`/`include` idiom threads induction hypotheses invisibly through a 165-line namespace, making several lemmas look like standalone results with undocumented hypotheses. (experimental-logrel Review notes)

- `Lean4Lean/Experimental/LogRel.lean:157`: `LRIsType.irrel'` closes with `grind`, brittle across toolchain bumps (in dead code, but the same reliance appears in live modules). (experimental-logrel Review notes)

- `Lean4Lean/Experimental/NormalEq.lean:97`: `Typing.pat_env` has no docstring, unlike the field it mirrors in `ChurchRosser.lean`; the `Typing` structure it belongs to is never instantiated anywhere. (experimental-reduction Review notes)

- `Lean4Lean/Experimental/MoreStepIndexed.lean:63`: the `Shape`/`ShapeFun` approximation lattice exists in three near-identical copies (here, `Thierry2.lean`, `ShapeLogRel.lean`), each with its own partly admitted order laws. (experimental-reduction Review notes)

- `Lean4Lean/Experimental/StepIndexed.lean:59`: `IsTy`, `IsTyN` and `IsTy.def` are axioms positing the fixpoint the file sets out to construct; `IsTyN` is unused and 40% of the file is commented out. (experimental-reduction Review notes)

- `Lean4Lean/Experimental/NormalEq.lean:145`: several declarations here carry fully qualified names that already exist in `ChurchRosser.lean` (`Pattern.Matches.hasType`, `Check.OK.weakN`); any name-indexed tool will conflate the sorry-free copy here with the tainted one there. (experimental-reduction Review notes)

- `Lean4Lean/Experimental/Stratified.lean:160`: two thirds of this file and `StratifiedUntyped.lean` are commented-out abandoned attempts containing further sorries, making the last live declaration of each look admitted to any line-range-based analysis. (experimental-reduction Review notes)

- `Lean4Lean/Experimental/ParallelReduction.lean:699`: two pre-existing master sorries in `NormalEq.parRed` make the file's Church-Rosser corollaries conditional; the iota case the branch added extends an already-unproved theorem. (experimental-reduction Review notes)

