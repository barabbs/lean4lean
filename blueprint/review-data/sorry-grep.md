# Independent `sorry` grep census

> **Recovery note (this pass).** Regenerated unchanged from `census/mksorrygrep.py` after a
> `/tmp` wipe (ran cleanly first attempt, no path or logic fixes needed) against the
> regenerated `understand/decls-attrib.tsv` (rebuilt by `census/attrib.py` from the regenerated
> `decls.tsv`, since `sorry-grep.md`'s generator needs that file and it did not yet exist on
> disk). All numbers on this page other than one are freshly computed from this run and are
> internally consistent (**125** grep hits / **104** live / **21** comment; **1** reconciliation
> mismatch in §4, `Tests/ProjInhabit.lean:562`, which is itself a real finding — see below).
> The one stale figure is **"638"** in §4's second paragraph: it is a literal string in the
> generator (not recomputed from data) and is the same pre-`/tmp`-wipe `sorryAx`-declaration
> count already flagged as stale in `census.md`'s recovery note; this run's actual count is
> **629** (`census.md` §1/§2). It does not affect §4's substantive point (many-to-one mapping
> between grep hits and tainted declarations), only the specific number quoted.
>
> Everything below this note is the generator's own output, unedited.

- **125** lines match `sorry`; **21** are inside a comment (doc-comment prose or commented-out code) and **104** are live term-level `sorry`s.

- `master` for comparison: `git grep -cP '\bsorry\b' master` gives **131** matching lines across 27 files; the working tree has **125** across 25 files.

- Attribution is the blame tag of the `sorry` **line itself** (`M`=master/upstream, `I`=iota, `P`=trproj). Files with no blame file are byte-identical to `master`.


## 1. Live `sorry`s outside `Experimental/` (the ones that matter)

| file:line | enclosing declaration (from `declRangeExt`) | attr | source |
|---|---|---|---|
| `Lean4Lean/Tests/ProjInhabit.lean:562` | `Lean4Lean.Tests.ProjInhabit.Dependent.trProjDep1` | **trproj** | `/-! ### Both witnesses are sorry-free -/` |
| `Lean4Lean/Theory/Typing/ChurchRosser.lean:1193` | `Lean4Lean.VEnv.NormalEq.parRed` | **master** | `sorry` |
| `Lean4Lean/Theory/Typing/ChurchRosser.lean:1212` | `Lean4Lean.VEnv.NormalEq.parRed` | **master** | `sorry` |
| `Lean4Lean/Theory/Typing/EnvLemmas.lean:334` | `Lean4Lean.VEnv.WF.patsStrong` | **iota** | `theorem VEnv.WF.patsStrong {env : VEnv} (H : env.WF) : env.PatsStrong := sorry` |
| `Lean4Lean/Theory/Typing/Injectivity.lean:12` | `Lean4Lean.VEnv.IsDefEqU.sort_inv` | **master** | `(h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v := sorry` |
| `Lean4Lean/Theory/Typing/Injectivity.lean:21` | `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified` | **master** | `env.HasTypeStratified U (A'::Γ) B' (.sort u) true n' := sorry` |
| `Lean4Lean/Theory/Typing/Injectivity.lean:34` | `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv` | **master** | `¬env.IsDefEqU U Γ (.sort u) (.forallE A B) := sorry` |
| `Lean4Lean/Theory/Typing/UniqueTyping.lean:174` | `Lean4Lean.VEnv.IsDefEqU.weakN_iff` | **master** | `refine ⟨fun h => have := henv; have := hΓ; sorry, fun h => h.weakN henv W⟩` |
| `Lean4Lean/Verify/Environment.lean:208` | `Lean4Lean.addDecl.WF` | **master** | `\| inductDecl _ _ _ _ => sorry` |
| `Lean4Lean/Verify/TypeChecker/InferType.lean:398` | `Lean4Lean.TypeChecker.Inner.inferProj.WF_struct` | **trproj** | `∃ e'' ty', c.TrTyping (.proj st i e) ty e'' ty' := sorry` |
| `Lean4Lean/Verify/TypeChecker/InferType.lean:410` | `Lean4Lean.TypeChecker.Inner.inferProj.WF` | **trproj** | `∃ e'' ty', c.TrTyping (.proj st i e) ty e'' ty' := sorry` |
| `Lean4Lean/Verify/TypeChecker/IsDefEq.lean:227` | `Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF` | **master** | `RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := sorry` |
| `Lean4Lean/Verify/TypeChecker/IsDefEq.lean:488` | `Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF` | **master** | `RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := sorry` |
| `Lean4Lean/Verify/TypeChecker/Reduce.lean:145` | `Lean4Lean.TypeChecker.Inner.reduceProjCore.WF` | **master** | `∀ e₁, oe = some e₁ → c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ e' := sorry` |
| `Lean4Lean/Verify/TypeChecker/WHNF.lean:149` | `Lean4Lean.TypeChecker.Inner.reduceRecursor.WF` | **master** | `∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := sorry` |
| `Lean4Lean/Verify/Typing/Lemmas.lean:747` | `Lean4Lean.TrProj.weak'_inv` | **trproj** | `sorry` |
| `Lean4Lean/Verify/Typing/Lemmas.lean:995` | `Lean4Lean.TrProj.uniq` | **trproj** | `sorry` |

## 2. Live `sorry`s inside `Experimental/`

All `master`. Listed for completeness; these modules are not part of the default `lake build`.

| file:line | enclosing declaration | source |
|---|---|---|
| `Lean4Lean/Experimental/LogRel.lean:244` | `Lean4Lean.SExpr.LREqTy.defeq_r` | `(H : J ⊩≡ B) (H2 : J ⊩ a ≡ b) : J' ⊩ a ≡ b := sorry` |
| `Lean4Lean/Experimental/LogRel.lean:250` | `Lean4Lean.SExpr.LREqTy.symm` | `\| .stuck .. => sorry -- ⟨⟨_, .stuck _ H.1.hasType.2⟩, H.1.symm, ⟨⟩⟩` |
| `Lean4Lean/Experimental/LogRel.lean:251` | `Lean4Lean.SExpr.LREqTy.symm` | `\| .sort .. => sorry -- ⟨⟨_, _⟩, _, _⟩` |
| `Lean4Lean/Experimental/LogRel.lean:252` | `Lean4Lean.SExpr.LREqTy.symm` | `\| .forallE .. => sorry -- ⟨⟨_, _⟩, _, _⟩` |
| `Lean4Lean/Experimental/LogRel.lean:288` | `Lean4Lean.SExpr.LVIsType.sort` | `sorry -- ⟨.sort, fun _ => ⟨.sort _, fun _ _ => ⟨.sort, .rfl⟩⟩⟩` |
| `Lean4Lean/Experimental/LogRel.lean:375` | `Lean4Lean.SExpr.fundamental` | `sorry` |
| `Lean4Lean/Experimental/LogRel.lean:379` | `Lean4Lean.SExpr.fundamental` | `\| _ => sorry` |
| `Lean4Lean/Experimental/MoreStepIndexed.lean:310` | `Lean4Lean.SExpr.ShapeFun.app_mono_l` | `sorry` |
| `Lean4Lean/Experimental/ParallelReduction.lean:699` | `Lean4Lean.NormalEq.parRed` | `sorry` |
| `Lean4Lean/Experimental/ParallelReduction.lean:718` | `Lean4Lean.NormalEq.parRed` | `sorry` |
| `Lean4Lean/Experimental/SExpr.lean:679` | `Lean4Lean.SExpr.IsDefEq.strong` | `theorem IsDefEq.strong : Γ ⊢ e1 ≡ e2 : A → IsDefEqStrong Γ e1 e2 A := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:680` | `Lean4Lean.SExpr.IsDefEqStrong.defeq` | `theorem IsDefEqStrong.defeq : IsDefEqStrong Γ e1 e2 A → Γ ⊢ e1 ≡ e2 : A := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:688` | `Lean4Lean.Params.ctor_ty` | `Ts.foldr .forallE (args.foldr (fun A acc => acc.app A) (.const I ls)) : .sort u := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:735` | `Lean4Lean.SExpr.HasTypeStratifiedS.to_core` | `∃ A', Γ ⊢ e :! A' !! n := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:738` | `Lean4Lean.SExpr.HasTypeStratifiedS.isType` | `∃ u, Γ ⊢ A : .sort u !! n - 1 := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:761` | `Lean4Lean.SExpr.Ctx.Subst.lift_r` | `Ctx.Subst HasType Δ (σ.lift_r ρ) Γ := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:770` | `Lean4Lean.SExpr.Ctx.Subst.id` | `theorem Ctx.Subst.id : Ctx.Subst HasType Γ .id Γ := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:787` | `Lean4Lean.SExpr.IsDefEq.subst` | `Γ ⊢ e1 ≡ e2 : A → Γ₀ ⊢ e1.subst σ ≡ e2.subst σ' : A.subst σ := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:795` | `Lean4Lean.SExpr.Ctx.SubstEq.lookup` | `Lookup Γ i A → Γ₀ ⊢ σ i ≡ σ' i : A.subst σ := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:798` | `Lean4Lean.SExpr.Ctx.SubstEq.lift` | `Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ'.lift (A :: Γ) := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:825` | `Lean4Lean.SExpr.IsDefEq.defeqDF_l'` | `sorry` |
| `Lean4Lean/Experimental/SExpr.lean:886` | `Lean4Lean.SExpr.IsDefEqLift.subst` | `Δ ⊢ e1.subst σ ≡ e2.subst σ :↑ A.subst σ := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:957` | `Lean4Lean.SExpr.WHRed.subst` | `\| .extra h1 h2 h3 h4 => sorry` |
| `Lean4Lean/Experimental/SExpr.lean:963` | `Lean4Lean.SExpr.WHRed.weak'` | `\| .extra h1 h2 h3 h4 => sorry` |
| `Lean4Lean/Experimental/SExpr.lean:973` | `Lean4Lean.SExpr.WHRed.weakU_inv` | `\| extra => sorry` |
| `Lean4Lean/Experimental/SExpr.lean:987` | `Lean4Lean.SExpr.WHRed.determ` | `\| extra => sorry` |
| `Lean4Lean/Experimental/SExpr.lean:992` | `Lean4Lean.SExpr.WHRed.determ` | `\| extra _ r2 => sorry` |
| `Lean4Lean/Experimental/SExpr.lean:995` | `Lean4Lean.SExpr.WHRed.determ` | `\| beta => sorry` |
| `Lean4Lean/Experimental/SExpr.lean:996` | `Lean4Lean.SExpr.WHRed.determ` | `\| app => sorry` |
| `Lean4Lean/Experimental/SExpr.lean:997` | `Lean4Lean.SExpr.WHRed.determ` | `\| extra _ r2 => sorry` |
| `Lean4Lean/Experimental/SExpr.lean:1008` | `Lean4Lean.SExpr.WHRedS.defeq` | `theorem WHRedS.defeq (H : Γ ⊢ e1 ⤳* e2) (he : Γ ⊢ e1 : A) : Γ ⊢ e1 ≡ e2 : A := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:1069` | `Lean4Lean.SExpr.ParRed.weak'` | `\| .extra h1 h2 h3 h4 h5 => sorry` |
| `Lean4Lean/Experimental/SExpr.lean:1091` | `Lean4Lean.SExpr.InferType.hasType` | `theorem InferType.hasType (H : Γ ⊢ e ▷ A) : Γ ⊢ e : A := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:1167` | `Lean4Lean.SExpr.InferTypeS.hasType` | `theorem InferTypeS.hasType : Γ ⊢ e ▷* A → Γ ⊢ e : A := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:1182` | `Lean4Lean.SExpr.WHRedS.parRedS` | `theorem WHRedS.parRedS (H : Γ ⊢ e ⤳* e') : Γ ⊢ e ≫* e' := sorry` |
| `Lean4Lean/Experimental/SExpr.lean:1251` | `Lean4Lean.SExpr.NormalEq.symm` | `\| appDF h1 h2 ih1 ih2 => exact .defeqDF sorry (u := sorry) <\| .appDF ih1 ih2` |
| `Lean4Lean/Experimental/SExpr.lean:1263` | `Lean4Lean.SExpr.NormalEq.weak'` | `\| appDF h1 h2 ih1 ih2 => exact .defeqDF sorry (u := sorry) <\| .appDF (ih1 W) (ih2 W)` |
| `Lean4Lean/Experimental/SExpr.lean:1295` | `Lean4Lean.SExpr.CRDefEq.trans` | `\| ⟨l1, _, _, l3, l4, l5⟩, ⟨r1, _, _, r3, r4, r5⟩ => sorry` |
| `Lean4Lean/Experimental/SExpr.lean:1323` | `Lean4Lean.SExpr.InferType.whRed` | `exact .inst sorry b2` |
| `Lean4Lean/Experimental/SExpr.lean:1324` | `Lean4Lean.SExpr.InferType.whRed` | `\| extra => sorry` |
| `Lean4Lean/Experimental/ShapeLogRelAdequacy.lean:154` | `Lean4Lean.SExpr.LR.adequacy` | `sorry` |
| `Lean4Lean/Experimental/Stratified.lean:96` | `Lean4Lean.VEnv.IsDefEq.induction1` | `.defeq (u := u.inst ls₁) sorry <\| .const h1 h3 (h5.length_eq.symm.trans h4),` |
| `Lean4Lean/Experimental/StratifiedUntyped.lean:77` | `Lean4Lean.VEnv.IsDefEq.inductionU1` | `exact ⟨.const h1 h2 h4, .defeq sorry <\| .const h1 h3 (h5.length_eq.symm.trans h4), .constDF h5⟩` |
| `Lean4Lean/Experimental/Stronger.lean:624` | `Lean4Lean.VEnv'.IsDefEqStrong.uniqL'` | `refine ⟨?_, sorry⟩` |
| `Lean4Lean/Experimental/Stronger.lean:626` | `Lean4Lean.VEnv'.IsDefEqStrong.uniqL'` | `sorry -- looks like it needs unique typing :(` |
| `Lean4Lean/Experimental/Stronger.lean:627` | `Lean4Lean.VEnv'.IsDefEqStrong.uniqL'` | `\| _ => sorry` |
| `Lean4Lean/Experimental/Stronger.lean:628` | `Lean4Lean.VEnv'.IsDefEqStrong.uniqL'` | `\| _ => sorry` |
| `Lean4Lean/Experimental/Thierry.lean:93` | `FinMut.LE.rfl` | `@[simp] theorem FinMut.LE.rfl {x : FinMut b} : x ≤ x := sorry` |
| `Lean4Lean/Experimental/Thierry.lean:94` | `FinMut.LE.lam` | `@[simp] theorem FinMut.LE.lam {x y : FinFun} : x.lam ≤ y.lam ↔ x ≤ y := sorry` |
| `Lean4Lean/Experimental/Thierry.lean:95` | `FinMut.LE.pi` | `@[simp] theorem FinMut.LE.pi {x y : FinElem} : x.pi f ≤ y.pi g ↔ x ≤ y ∧ f ≤ g := sorry` |
| `Lean4Lean/Experimental/Thierry.lean:118` | `FinHasType.mono` | `theorem FinHasType.mono : u :ᶠ a → a ≤ b → u :ᶠ b := sorry` |
| `Lean4Lean/Experimental/Thierry.lean:120` | `FinHasType.join` | `theorem FinHasType.join (H : Join u v w) : u :ᶠ a → v :ᶠ b → w :ᶠ b := sorry` |
| `Lean4Lean/Experimental/Thierry.lean:122` | `FinHasType.pi_eval` | `theorem FinHasType.pi_eval : FinHasType f (.pi a) → u :ᶠ a → f u :ᶠ .U := sorry` |
| `Lean4Lean/Experimental/Thierry.lean:123` | `FinHasType.lam_eval` | `theorem FinHasType.lam_eval : FinHasType f (.lam a g) → u :ᶠ a → f u :ᶠ g u := sorry` |
| `Lean4Lean/Experimental/Thierry.lean:124` | `FinHasType.lem5` | `theorem FinHasType.lem5 : .lam w :ᶠ .pi b f → b ≤ a → u :ᶠ a → ∃ v, v :ᶠ b ∧ v ≤ u ∧ w u = w v := so` |
| `Lean4Lean/Experimental/Thierry.lean:137` | `El_iff` | `theorem El_iff {u a : FinElem} : El a u ↔ u :ᶠ a := sorry` |
| `Lean4Lean/Experimental/Thierry.lean:139` | `El.mono` | `theorem El.mono : v ≤ u → El a u → El a v := sorry` |
| `Lean4Lean/Experimental/Thierry.lean:148` | `subst` | `def subst : Expr → Expr → Expr := sorry` |
| `Lean4Lean/Experimental/Thierry.lean:190` | `meas_apply_lt` | `theorem meas_apply_lt (f : FinFun) (x) : meas (f x) < meas f := sorry` |
| `Lean4Lean/Experimental/Thierry.lean:224` | `HasTypeFamF.def` | `HasTypeF N B v b → HasTypeF (subst F N) .U (f v) .U := sorry` |
| `Lean4Lean/Experimental/Thierry.lean:228` | `HasPiFamF.def` | `HasTypeF N B v b → HasTypeF (.app M N) (subst F N) (m v) (f v) := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:97` | `ShapeFun.LE.bot` | `theorem ShapeFun.LE.bot : .bot ≤≤ f := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:132` | `Shape.Compat.def` | `theorem Shape.Compat.def {x y : Shape n} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:156` | `Shape.Join.mk` | `theorem Shape.Join.mk (H : x.Compat y) : Join x y (x.join y) := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:158` | `ShapeFun.Join.mk` | `theorem ShapeFun.Join.mk (H : Compat Shape.Compat x y) : Join x y (join Shape.join x y) := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:167` | `ShapeFun.app_mono_l` | `sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:170` | `ShapeFun.app_mono_r` | `sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:172` | `ShapeFun.Join.app` | `theorem ShapeFun.Join.app (H : Join x y z) : Shape.Join (x.app a) (y.app a) (z.app a) := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:176` | `ShapeFun.Compat.def` | `sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:178` | `ShapeFun.bot_app` | `@[simp] theorem ShapeFun.bot_app : (@ShapeFun.bot n).app x = .bot := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:184` | `Shape.Join.app` | `theorem Shape.Join.app (H : Join x y z) : Shape.Join (x.app a) (y.app a) (z.app a) := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:192` | `Shape.app_mono_r` | `theorem Shape.app_mono_r {f : Shape (n + 1)} (h1 : x ≤ y) : f.app x ≤ f.app y := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:240` | `Shape.HasType.mono` | `theorem Shape.HasType.mono {m a a' : Shape n} (ha : a ≤ a') : m :ᶠ a → m :ᶠ a' := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:243` | `Shape.HasTypeLam.app` | `HasType (ShapeFun.app f x) (ShapeFun.app b x) := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:246` | `Shape.HasTypePi.app` | `(ht : HasType x a) : HasType (ShapeFun.app f x) .U := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:250` | `Shape.HasType.maximal` | `∃ x, HasType x a ∧ x ≤ x' ∧ ShapeFun.app f x = ShapeFun.app f x' := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:330` | `Shape.Compat.lift` | `(x.lift : Shape m).Compat y.lift ↔ x.Compat y := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:334` | `ShapeFun.Compat.lift` | `Compat Shape.Compat x y := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:337` | `Shape.lift_join` | `((x.join y).lift : Shape m) = x.lift.join y.lift := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:341` | `ShapeFun.lift_join` | `join Shape.join (lift Shape.lift x) (lift Shape.lift y) := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:345` | `ShapeFun.lift_app` | `sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:349` | `Shape.lift_app` | `sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:421` | `DF.mk'` | `def DF.mk' (f : D → D) : DF := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:472` | `D.pi` | `def D.pi : D → DF → D := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:560` | `El_iff` | `theorem El_iff {u a : Shape n} : El a u ↔ u :ᶠ a := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:562` | `El.mono` | `theorem El.mono : v ≤ u → El a u → El a v := sorry` |
| `Lean4Lean/Experimental/Thierry2.lean:571` | `subst` | `def subst : Expr → Expr → Expr := sorry` |

## 3. Comment-only matches (not real `sorry`s)

| file:line | attr | text |
|---|---|---|
| `Lean4Lean/Experimental/MoreStepIndexed.lean:387` | master | `--       mono' := sorry }` |
| `Lean4Lean/Experimental/MoreStepIndexed.lean:473` | master | `--   mono' := sorry }` |
| `Lean4Lean/Experimental/MoreStepIndexed.lean:487` | master | `-- decreasing_by all_goals sorry` |
| `Lean4Lean/Experimental/MoreStepIndexed.lean:489` | master | `-- theorem TypeEq.mono : k ≤ k' → TypeEq k' Γ A B ≤ TypeEq k Γ A B := sorry` |
| `Lean4Lean/Experimental/ShapeLogRel.lean:1702` | master | `sorry` |
| `Lean4Lean/Experimental/ShapeLogRel.lean:1710` | master | `· sorry` |
| `Lean4Lean/Experimental/ShapeLogRel.lean:1711` | master | `· sorry` |
| `Lean4Lean/Experimental/ShapeLogRel.lean:1719` | master | `\| lam => exact ⟨⟨(go ⟨_, wf.1⟩).1, sorry⟩, fun _ h1 => ⟨(go ⟨_, wf.1⟩).2 _ h1, sorry⟩⟩` |
| `Lean4Lean/Experimental/ShapeLogRel.lean:1721` | master | `refine ⟨⟨fun _ h1 => (ih ⟨_, wf.1 _ h1⟩).1, sorry⟩, fun _ h1 => ⟨fun _ h2 => ?_, sorry⟩⟩` |
| `Lean4Lean/Experimental/ShapeLogRel.lean:1727` | master | `--   sorry` |
| `Lean4Lean/Experimental/ShapeLogRel.lean:1729` | master | `-- theorem Shape.WF.plift (h : WF (n := n) x) : WF (n := m) x.plift.1 := sorry` |
| `Lean4Lean/Experimental/ShapeLogRel.lean:1731` | master | `--     WF (n := m) Shape.WF (plift Shape.plift x).1 := sorry` |
| `Lean4Lean/Experimental/Stratified.lean:311` | master | `\| trans _ _ ih1 ih2 => sorry` |
| `Lean4Lean/Experimental/Stratified.lean:330` | master | `\| _ => sorry` |
| `Lean4Lean/Experimental/StratifiedUntyped.lean:295` | master | `\| trans _ _ ih1 ih2 => sorry` |
| `Lean4Lean/Experimental/StratifiedUntyped.lean:314` | master | `\| _ => sorry` |
| `Lean4Lean/Tests/ProjInhabit.lean:14` | trproj | `The witnesses are sorry-free; the general construction, from an arbitrary kernel-accepted` |
| `Lean4Lean/Tests/ProjInhabit.lean:582` | trproj | ``TrEnv.proj_defeq` has no `sorry` of its own: the `sorryAx` below is inherited from unique` |
| `Lean4Lean/TypeChecker.lean:970` | master | `-- example : "hi" = sorry := by` |
| `Lean4Lean/Verify/Environment/Primitive.lean:8` | master | `The checker, extension, and declaration modules introduce no additional `sorry`-backed` |
| `Lean4Lean/Verify/Level.lean:27` | master | `--     {l₁ l₂ : VLevel} (eq : l₁.toLevel ls = l₂.toLevel ls) : l₁ = l₂ := sorry` |

## 4. Cross-check against the compiled environment

The grep finds **104** live `sorry` sites; `decls.tsv` reports **638** declarations whose `collectAxioms` contains `sorryAx`. The two numbers measure different things and both are right:

- A single `sorry`-ed theorem is one grep hit but taints every declaration that depends on it, so 638 ≫ 104.

- Several grep hits sit inside one declaration (e.g. four in `Lean4Lean.VEnv'.IsDefEqStrong.uniqL'`, seven in `Lean4Lean.SExpr.WHRed.determ`), so the map is many-to-one in that direction too.


### Every grep hit reconciled with the TSV

For each live non-`Experimental` hit: does the enclosing declaration report `sorryAx` in `decls.tsv`?

| file:line | enclosing decl | `usesSorry` in TSV | verdict |
|---|---|---|---|
| `Lean4Lean/Tests/ProjInhabit.lean:562` | `Lean4Lean.Tests.ProjInhabit.Dependent.trProjDep1` | false | **MISMATCH — the nearest preceding declaration is not sorry-tainted, so the `sorry` belongs to a declaration the environment does not expose (a failed/`example`/commented decl) or the range attribution is off** |
| `Lean4Lean/Theory/Typing/ChurchRosser.lean:1193` | `Lean4Lean.VEnv.NormalEq.parRed` | true | consistent |
| `Lean4Lean/Theory/Typing/ChurchRosser.lean:1212` | `Lean4Lean.VEnv.NormalEq.parRed` | true | consistent |
| `Lean4Lean/Theory/Typing/EnvLemmas.lean:334` | `Lean4Lean.VEnv.WF.patsStrong` | true | consistent |
| `Lean4Lean/Theory/Typing/Injectivity.lean:12` | `Lean4Lean.VEnv.IsDefEqU.sort_inv` | true | consistent |
| `Lean4Lean/Theory/Typing/Injectivity.lean:21` | `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified` | true | consistent |
| `Lean4Lean/Theory/Typing/Injectivity.lean:34` | `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv` | true | consistent |
| `Lean4Lean/Theory/Typing/UniqueTyping.lean:174` | `Lean4Lean.VEnv.IsDefEqU.weakN_iff` | true | consistent |
| `Lean4Lean/Verify/Environment.lean:208` | `Lean4Lean.addDecl.WF` | true | consistent |
| `Lean4Lean/Verify/TypeChecker/InferType.lean:398` | `Lean4Lean.TypeChecker.Inner.inferProj.WF_struct` | true | consistent |
| `Lean4Lean/Verify/TypeChecker/InferType.lean:410` | `Lean4Lean.TypeChecker.Inner.inferProj.WF` | true | consistent |
| `Lean4Lean/Verify/TypeChecker/IsDefEq.lean:227` | `Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF` | true | consistent |
| `Lean4Lean/Verify/TypeChecker/IsDefEq.lean:488` | `Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF` | true | consistent |
| `Lean4Lean/Verify/TypeChecker/Reduce.lean:145` | `Lean4Lean.TypeChecker.Inner.reduceProjCore.WF` | true | consistent |
| `Lean4Lean/Verify/TypeChecker/WHNF.lean:149` | `Lean4Lean.TypeChecker.Inner.reduceRecursor.WF` | true | consistent |
| `Lean4Lean/Verify/Typing/Lemmas.lean:747` | `Lean4Lean.TrProj.weak'_inv` | true | consistent |
| `Lean4Lean/Verify/Typing/Lemmas.lean:995` | `Lean4Lean.TrProj.uniq` | true | consistent |

1 of those rows are not a clean match; see the verdict column.


## 5. The five holes the contribution is responsible for

| declaration | file:line | branch | note |
|---|---|---|---|
| `Lean4Lean.VEnv.WF.patsStrong` | `Lean4Lean/Theory/Typing/EnvLemmas.lean:334` | **iota** | subject reduction for every registered ι rule; documented at length as open; 343 constants depend on it |
| `Lean4Lean.TrProj.uniq` | `Lean4Lean/Verify/Typing/Lemmas.lean:995` | **trproj** | 138 constants depend on it |
| `Lean4Lean.TrProj.weak'_inv` | `Lean4Lean/Verify/Typing/Lemmas.lean:747` | **trproj** | 92 constants depend on it |
| `Lean4Lean.TypeChecker.Inner.inferProj.WF` | `Lean4Lean/Verify/TypeChecker/InferType.lean:410` | trproj (restated; `master` already had it `sorry`-ed at line 391) | 61 constants |
| `Lean4Lean.TypeChecker.Inner.inferProj.WF_struct` | `Lean4Lean/Verify/TypeChecker/InferType.lean:398` | **trproj** | **0 constants — declared, documented, `sorry`-ed, and used by nothing** |

Against that, the branches *deleted* five `master` `sorry`s that were on **definitions** (`VInductDecl.WF`, `VEnv.addInduct`, `TrProj`) plus two lemma stubs — see `census.md` §7.3.

