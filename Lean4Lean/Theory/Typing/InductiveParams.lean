import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.InductiveLemmas

namespace Lean4Lean
namespace VEnv

open VExpr

/-!
# A concrete `Params` instance from `env.pats`

`VEnv.toParams` instantiates `ChurchRosser`'s abstract pattern-reduction relation
`Params.Pat` with the environment's own registered ι rules `env.pats`. Its engine is
the population invariant `VEnv.PatsIota`: every registered pattern is a
`SimplePattern.iota` redex whose recursor head is a registered `RecHeaded` constant
(`shape`) of a spine arity fixed by the recursor name (`arity`), whose constructor is
a registered `CtorHeaded` constant (`ctor_shape`), and whose reduct is determined by
the pattern (`functional`). The invariant is established from the staged
`VInductDecl.WF` (`rec_shape`, `rules_ctor`, `rules_nodup`) and the stage lemmas of
`addInduct`; from it, `pat_simple`, `pat_uniq`, `pat_app_l`, `pat_app_l_uniq` and
`pat_app_uniq` are proved; `pat_env` is the identity. The remaining side condition
`extra_pat` (every `defeqs` entry realised by a registered pattern) is `VEnv.DefEqsAsPats`,
which `toParams` takes as a hypothesis.

The section "Recoverability of the recursor data" records what a registered entry lets
one recover of the recursor it came from: the full `VRecursor` from the `WF'` witness
(`WF'.pats_origin`), the telescope split with the shapes of the registered constants
(`WF.pats_split`), and a total decoder over the data a bare `VEnv` retains
(`VEnv.recSplit?`), with its honest limit.
-/

/-! ### Combinatorics of ι redexes -/

/-- The only application subpattern of an ι redex is its top-level one: the recursor
spine applied to the constructor spine. -/
theorem app_subpattern_iota' {r m c n a b}
    (hs : Subpattern (.app a b) ((SimplePattern.iota r m c n).toPattern)) :
    a = (Pattern.const r).varN m ∧ b = (Pattern.const c).varN n := by
  simp only [SimplePattern.toPattern] at hs
  cases hs with
  | refl => exact ⟨rfl, rfl⟩
  | appL h => exact absurd h Pattern.not_app_subpattern_varN_const
  | appR h => exact absurd h Pattern.not_app_subpattern_varN_const

/-- The only application subpattern of an ι redex is its top-level one, whose left
factor is the recursor spine. -/
theorem app_subpattern_iota {r m c n a b}
    (hs : Subpattern (.app a b) ((SimplePattern.iota r m c n).toPattern)) :
    a = (Pattern.const r).varN m :=
  (app_subpattern_iota' hs).1

/-- An application pattern does not intersect a constant. -/
theorem _root_.Lean4Lean.Pattern.inter_app_const {f a : Pattern} {c : Name} :
    (Pattern.app f a).inter (.const c) = none := by
  simp [Pattern.inter]

/-- An application pattern intersects a variable pattern only through its function
part. -/
theorem _root_.Lean4Lean.Pattern.inter_app_var {f a f' q : Pattern}
    (h : (Pattern.app f a).inter (.var f') = some q) :
    ∃ g, f.inter f' = some g ∧ q = .app g a := by
  cases hf : f.inter f' with
  | none => simp [Pattern.inter, hf] at h
  | some g => simp [Pattern.inter, hf] at h; exact ⟨g, rfl, h.symm⟩

/-- Two application patterns intersect componentwise. -/
theorem _root_.Lean4Lean.Pattern.inter_app_app {f a f' a' q : Pattern}
    (h : (Pattern.app f a).inter (.app f' a') = some q) :
    ∃ g b, f.inter f' = some g ∧ a.inter a' = some b ∧ q = .app g b := by
  cases hf : f.inter f' with
  | none => simp [Pattern.inter, hf] at h
  | some g =>
    cases ha : a.inter a' with
    | none => simp [Pattern.inter, hf, ha] at h
    | some b => simp [Pattern.inter, hf, ha] at h; exact ⟨g, b, rfl, rfl, h.symm⟩

/-- Each `VDecl.WF` step either leaves `pats` unchanged (`axiom`/`def`/`opaque`/
`example`/`quot`) or is the `addInduct` of a well-formed declaration `d = .induct decl`. -/
theorem _root_.Lean4Lean.VDecl.WF.pats_eq_or_induct' {env d env'} (h : VDecl.WF env d env') :
    env'.pats = env.pats ∨
      ∃ decl, d = .induct decl ∧ decl.WF env ∧ env.addInduct decl = some env' := by
  cases h with
  | «axiom» _ h2 => exact .inl (addConst_pats h2)
  | «def» _ h2 => exact .inl (by rw [addDefEq_pats]; exact addConst_pats h2)
  | mutualDef _ h2 _ => exact .inl (by rw [addDefEqs_pats]; exact addConsts_pats h2)
  | «opaque» _ h2 => exact .inl (addConst_pats h2)
  | «example» _ => exact .inl rfl
  | quot _ h2 => exact .inl (addQuot_pats h2)
  | induct h1 h2 => exact .inr ⟨_, rfl, h1, h2⟩

/-- Each `VDecl.WF` step either leaves `pats` unchanged (`axiom`/`def`/`opaque`/
`example`/`quot`) or is an `addInduct` of a well-formed declaration. -/
theorem _root_.Lean4Lean.VDecl.WF.pats_eq_or_induct {env d env'} (h : VDecl.WF env d env') :
    env'.pats = env.pats ∨ ∃ decl, decl.WF env ∧ env.addInduct decl = some env' := by
  rcases h.pats_eq_or_induct' with heq | ⟨decl, -, hdecl, hind⟩
  · exact .inl heq
  · exact .inr ⟨decl, hdecl, hind⟩

/-- Every `VDecl.WF` step only grows the environment. -/
theorem _root_.Lean4Lean.VDecl.WF.le {env d env'} (h : VDecl.WF env d env') : env ≤ env' := by
  cases h with
  | «axiom» _ h2 => exact addConst_le h2
  | «def» _ h2 => exact (addConst_le h2).trans addDefEq_le
  | mutualDef _ h2 _ => exact (VEnv.addConsts_le h2).trans addDefEqs_le
  | «opaque» _ h2 => exact addConst_le h2
  | «example» _ => exact .rfl
  | quot _ h2 => exact addQuot_le h2
  | induct _ h2 => exact addInduct_le h2

/-! ### Recoverability of the recursor data

`env.pats` retains of an ι rule only its key `SimplePattern.iota recN M cN N` and its
reduct `SimplePattern.iotaRHS`: the recursor name and summed major index `M`, the
constructor name and spine arity `N`, and (`Pattern.RHS.iotaCounts`) the template and
the two hole counts. The `VRecursor` it was registered from is recoverable by three
routes:

* (R1) `WF'.pats_origin`: from the `WF'` witness, the full `VInductDecl`, `VRecursor`
  and `VRecRule` — the declaration list `ds` is the source of truth for declaration-level
  data, as it already is for def-versus-axiom.
* (R2) `TrEnv.pats_iota_inv'` (`Verify/Environment/Lemmas.lean`): in a translated
  environment, the kernel `RecursorVal` and `ConstructorVal`, hence the full kernel
  telescope split.
* (R3) `VEnv.recSplit?`: a total decoder over the data a bare `VEnv` retains — the
  entry's hole counts and the registered recursor type — exact (`recSplit?_eq`, and the
  last clause of `WF.pats_split`) when the rule's constructor has the recursor's
  parameters, `cnp = np`: every rule of a non-nested block and every rule of a nested
  block's main recursors (`VInductDecl.WF.rules_own_params`).

Honest limit of (R3): for a rule of an auxiliary recursor of a nested block
(`Tree.rec_1` on `List.cons`: `cnp = 1 ≠ np = 0`) the parameter count is not determined
by `N = cnp + nf` and the hole counts — the major's type is a restored nested occurrence
such as `List Tree` — so `recSplit?` reads `cnp` as `np` and misplaces the motive/minor
boundary accordingly (`Tests/IotaShape.lean` exhibits this); (R1)/(R2) cover these rules.
Independently of the decoder, `WF.pats_split` gives `M = np+nm+nmin+nind`, `N = cnp+nf`,
`1 ≤ nm`, `1 ≤ nmin`, the reduct as `iotaRHS` at that split, and the `RecShape`/
`CtorShape` of the registered recursor and constructor types and the `RuleShape` of the
template at some minor `j`; a consumer that knows `np` and `nind = 0` (a structure's
recursor, `M = np + 2`) gets `(nm, nmin) = (1, 1)` by `omega`. -/

/-- (R1) Origin of a registered pattern entry along a `WF'` chain: some `ds` step is the
`addInduct` of a well-formed `decl` (`VDecl.induct decl :: ds₀` a suffix of `ds`, `ds₀`
the declarations before it), and the entry is exactly the ι entry of one rule `ru` of one
recursor `rec` of `decl` — key `SimplePattern.iota` and reduct `SimplePattern.iotaRHS`,
both read off `rec`/`ru`, with `rec`'s full telescope split. -/
theorem WF'.pats_origin {ds : List VDecl} {env : VEnv} (H : env.WF' ds) {p rr}
    (hp : env.pats p rr) :
    ∃ (decl : VInductDecl) (ds₀ : List VDecl) (env₀ env₁ : VEnv),
      (VDecl.induct decl :: ds₀) <:+ ds ∧ env₀.WF' ds₀ ∧ decl.WF env₀ ∧
      env₀.addInduct decl = some env₁ ∧ env₁ ≤ env ∧
      ∃ rec ∈ decl.recs, ∃ ru ∈ rec.rules, ∃ (hc : ru.rhs.Closed)
        (e : p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
          (ru.ctorParams + ru.nfields)).toPattern),
        e ▸ rr = (SimplePattern.iotaRHS rec.name ru.ctor
          rec.numParams rec.numMotives rec.numMinors rec.numIndices ru.ctorParams ru.nfields
          ru.rhs hc, .true) := by
  induction H with
  | empty => exact (hp : False).elim
  | @decl d env' ds env hd H ih =>
    suffices key : env.pats p rr ∨ ∃ decl, d = .induct decl ∧ decl.WF env ∧
        env.addInduct decl = some env' ∧
        ∃ rec ∈ decl.recs, ∃ ru ∈ rec.rules, ∃ (hc : ru.rhs.Closed)
          (e : p = (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
            (ru.ctorParams + ru.nfields)).toPattern),
          e ▸ rr = (SimplePattern.iotaRHS rec.name ru.ctor
            rec.numParams rec.numMotives rec.numMinors rec.numIndices ru.ctorParams ru.nfields
            ru.rhs hc, .true) by
      rcases key with hold | ⟨decl, rfl, hdecl, hind, rest⟩
      · obtain ⟨decl, ds₀, env₀, env₁, hsuf, hwf', hdecl, hadd, hle, rest⟩ := ih hold
        exact ⟨decl, ds₀, env₀, env₁, hsuf.trans (List.suffix_cons _ _), hwf', hdecl, hadd,
          hle.trans hd.le, rest⟩
      · exact ⟨decl, ds, env, env', List.suffix_refl _, H, hdecl, hind, .rfl, rest⟩
    rcases hd.pats_eq_or_induct' with heq | ⟨decl, hd_eq, hdecl, hind⟩
    · exact .inl (heq ▸ hp)
    · rcases addInduct_pats_origin' hind hp with hold | rest
      · exact .inl hold
      · exact .inr ⟨decl, hd_eq, hdecl, hind, rest⟩

/-- (R3) Decode a recursor's telescope split `(np, nm, nmin, nind)` from the data a bare
`VEnv` retains of an ι entry `iota recN M cN N ↦ R` together with the registered recursor
type `recTy`: `nf` and `k = np + nm + nmin` are the entry's constructor- and
recursor-side hole counts (`Pattern.RHS.iotaCounts`), `np := N - nf` (exact iff the
constructor has the recursor's parameters, `cnp = np`), `nind := M - k`, and the
motive/minor boundary is read off the recursor type: `nm` is the number of binders among
positions `[np, k)` whose Π-body is a sort (`VExpr.RecShape`: motive binders end in a
sort, minor binders in a motive application), `nmin` the rest. Total; `recSplit?_eq`
states its exactness. -/
def recSplit? (recTy : VExpr) {recN M cN N} (R : (SimplePattern.iota recN M cN N).toPattern.RHS) :
    Option (Nat × Nat × Nat × Nat) := do
  let (_, k, nf) ← R.iotaCounts
  let np := N - nf
  let nm := (List.range (k - np)).countP fun i =>
    (recTy.piBinders[np + i]?).any fun A => A.piBody.isSort
  some (np, nm, k - np - nm, M - k)

/-- Exactness of `recSplit?`: on the ι entry of a rule whose constructor has the
recursor's parameters (`cnp = np`), over a recursor type of the matching `RecShape`, the
decoder returns the true split. The hypotheses are the corresponding clauses of
`WF.pats_split`. -/
theorem recSplit?_eq {recN M cN N} {R : (SimplePattern.iota recN M cN N).toPattern.RHS}
    {recTy : VExpr} {np nm nmin nind cnp nf : Nat} {rhs : VExpr} {hc : rhs.Closed}
    (hM : M = np + nm + nmin + nind) (hN : N = cnp + nf)
    (hR : HEq R (SimplePattern.iotaRHS recN cN np nm nmin nind cnp nf rhs hc))
    (hshape : recTy.RecShape np nm nmin nind) (hown : cnp = np) :
    recSplit? recTy R = some (np, nm, nmin, nind) := by
  subst hM hN; subst cnp
  obtain rfl := eq_of_heq hR
  have hcount : (List.range (nm + nmin)).countP
      (fun i => (recTy.piBinders[np + i]?).any fun A => A.piBody.isSort) = nm := by
    rw [List.range_add, List.countP_append, List.countP_map, List.countP_eq_length.2,
      List.countP_eq_zero.2, List.length_range, Nat.add_zero]
    · intro i hi
      obtain ⟨A, hA, k', -, hk'⟩ := hshape.2.2.1 i (List.mem_range.1 hi)
      simp only [Function.comp, ← Nat.add_assoc, hA, Option.any_some]
      intro h
      obtain ⟨u, hu⟩ := isSort_iff.1 h
      rw [hu] at hk'; cases hk'
    · intro i hi
      obtain ⟨A, hA, ⟨u, hu⟩, -⟩ := hshape.2.1 i (List.mem_range.1 hi)
      simp [hA, hu, isSort]
  have h1 : np + nf - nf = np := by omega
  have h2 : np + nm + nmin - np = nm + nmin := by omega
  have h3 : nm + nmin - nm = nmin := by omega
  have h4 : np + nm + nmin + nind - (np + nm + nmin) = nind := by omega
  simp only [recSplit?, SimplePattern.iotaRHS_iotaCounts, Option.bind_eq_bind, Option.bind_some,
    h1, h2, hcount, h3, h4]

/-- The telescope split behind a registered ι entry of a well-formed environment: the
summed major index splits as `M = np + nm + nmin + nind` with at least one motive and one
minor, the constructor spine as `N = cnp + nf`, the reduct is `iotaRHS` at that split
(componentwise: `HEq` on the `RHS`, `.true` check), the recursor and the constructor are
registered with types of the matching `RecShape`/`CtorShape`, the template has the
matching `RuleShape` at some minor `j` — the minor `MinorFor cN`, with the reduct's
recursive-argument count its binders beyond the fields — and `recSplit?` decodes the split
exactly when
`cnp = np`. From `WF'.pats_origin` and `VInductDecl.WF` (`rec_shape`, `rules_ctor`,
`rule_shape`). -/
theorem WF.pats_split {env : VEnv} (H : env.WF) {recN M cN N rr}
    (hp : env.pats (SimplePattern.iota recN M cN N).toPattern rr) :
    ∃ (np nm nmin nind cnp nf : Nat) (rhs : VExpr) (hc : rhs.Closed) (ci cci : VConstant),
      M = np + nm + nmin + nind ∧ N = cnp + nf ∧ 1 ≤ nm ∧ 1 ≤ nmin ∧
      HEq rr.1 (SimplePattern.iotaRHS recN cN np nm nmin nind cnp nf rhs hc) ∧ rr.2 = .true ∧
      env.constants recN = some ci ∧ ci.type.RecShape np nm nmin nind ∧
      env.constants cN = some cci ∧ cci.type.CtorShape (cnp + nf) ∧
      (∃ j < nmin, ∃ A, ci.type.piBinders[np + nm + j]? = some A ∧ A.MinorFor cN ∧
        nf ≤ A.piArity ∧ rhs.RuleShape np nm nmin nf (A.piArity - nf) j) ∧
      (cnp = np → recSplit? ci.type rr.1 = some (np, nm, nmin, nind)) := by
  obtain ⟨ds, H⟩ := H
  obtain ⟨decl, ds₀, env₀, env₁, -, -, hdecl, hind, hle, rec, hrec, ru, hru, hc, e, he⟩ :=
    H.pats_origin hp
  obtain ⟨rfl, rfl, rfl, rfl⟩ := iota_toPattern_inj e
  have he' : rr = (SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives
    rec.numMinors rec.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true) := he
  obtain ⟨cci, hcci, hcs⟩ := addInduct_rule_ctor hdecl hind hrec hru
  have hrs := hdecl.rec_shape rec hrec
  obtain ⟨j', hj', A, hA, hAm, hle', hru_s⟩ := hdecl.rule_shape rec hrec ru hru
  obtain ⟨-, -, -, j, hj, -⟩ := id hrs
  have hR : HEq rr.1 (SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives
    rec.numMinors rec.numIndices ru.ctorParams ru.nfields ru.rhs hc) := by rw [he']; exact HEq.rfl
  exact ⟨rec.numParams, rec.numMotives, rec.numMinors, rec.numIndices, ru.ctorParams, ru.nfields,
    ru.rhs, hc, _, cci, rfl, rfl, by omega, by omega, hR, by rw [he'],
    hle.constants (addInduct_rec_find hind hrec), hrs, hle.constants hcci, hcs,
    ⟨j', hj', A, hA, hAm, hle', hru_s⟩,
    fun hown => recSplit?_eq rfl rfl hR hrs hown⟩

/-! ### The population invariant -/

/-- The pattern-registry invariant of a well-formed environment: every registered
pattern is a `SimplePattern.iota` redex whose recursor head is a registered constant
with a `RecHeaded` type (`shape`), the recursor name determines the spine arity `M`
(`arity`), the constructor is a registered constant with a `CtorHeaded` type
(`ctor_shape`), and a pattern determines its reduct (`functional`). -/
structure PatsIota (env : VEnv) : Prop where
  shape : ∀ {p rr}, env.pats p rr →
    ∃ recN M ctorN N c,
      p = (SimplePattern.iota recN M ctorN N).toPattern ∧ env.constants recN = some c ∧
      c.type.RecHeaded
  arity : ∀ {recN M₁ c₁ N₁ rr₁ M₂ c₂ N₂ rr₂},
    env.pats (SimplePattern.iota recN M₁ c₁ N₁).toPattern rr₁ →
    env.pats (SimplePattern.iota recN M₂ c₂ N₂).toPattern rr₂ → M₁ = M₂
  ctor_shape : ∀ {recN M ctorN N rr},
    env.pats (SimplePattern.iota recN M ctorN N).toPattern rr →
    ∃ ci, env.constants ctorN = some ci ∧ ci.type.CtorHeaded
  functional : ∀ {p rr rr'}, env.pats p rr → env.pats p rr' → rr = rr'

/-- A recursor head of one ι redex is never the constructor of another (or the same)
ι redex: the constant would have to be both `RecHeaded` and `CtorHeaded`. -/
theorem PatsIota.rec_ne_ctor {env : VEnv} (H : env.PatsIota)
    {R M C N r₁ R₂ M₂ C₂ N₂ r₂}
    (h1 : env.pats (SimplePattern.iota R M C N).toPattern r₁)
    (h2 : env.pats (SimplePattern.iota R₂ M₂ C₂ N₂).toPattern r₂) : R ≠ C₂ := by
  intro heq
  obtain ⟨recN, M', ctorN, N', c, hf, hc, hrec⟩ := H.shape h1
  obtain ⟨rfl, -, -, -⟩ := iota_toPattern_inj hf
  obtain ⟨ci, hci, hctor⟩ := H.ctor_shape h2
  subst heq; rw [hc] at hci; cases hci
  exact hrec.not_ctorHeaded hctor

/-- `PatsIota` is preserved by any step that leaves `pats` unchanged and only grows
`constants` (the non-`induct` `VDecl.WF` steps). -/
theorem PatsIota.of_le {env env' : VEnv} (H : env.PatsIota)
    (hpats : env'.pats = env.pats) (hle : env ≤ env') : env'.PatsIota := by
  constructor
  · intro p rr hp; rw [hpats] at hp
    obtain ⟨recN, M, ctorN, N, c, hform, hc, hrec⟩ := H.shape hp
    exact ⟨recN, M, ctorN, N, c, hform, hle.constants hc, hrec⟩
  · intro recN M₁ c₁ N₁ rr₁ M₂ c₂ N₂ rr₂ h1 h2
    rw [hpats] at h1 h2; exact H.arity h1 h2
  · intro recN M ctorN N rr hp; rw [hpats] at hp
    obtain ⟨ci, hci, hctor⟩ := H.ctor_shape hp
    exact ⟨ci, hle.constants hci, hctor⟩
  · intro p rr rr' h1 h2
    rw [hpats] at h1 h2; exact H.functional h1 h2

/-- `PatsIota` is preserved by `addInduct` of a well-formed declaration: freshly
registered ι entries are keyed by a new `RecHeaded` recursor constant
(`rec_shape`) firing on a registered `CtorHeaded` constructor (`rules_ctor`); old and
new recursor names cannot collide (`addInduct_rec_fresh`); and two new entries with
the same key come from the same recursor (`addInduct_recs_name_inj`) and the same
rule (`rules_nodup`), hence coincide. -/
theorem PatsIota.induct {env env' : VEnv} {decl : VInductDecl} (H : env.PatsIota)
    (hwf : decl.WF env) (h : env.addInduct decl = some env') : env'.PatsIota := by
  have hle := addInduct_le h
  -- an old pattern's recursor is not a recursor of `decl`
  have hold_fresh : ∀ {recN M ctorN N rr},
      env.pats (SimplePattern.iota recN M ctorN N).toPattern rr →
      ∀ rec ∈ decl.recs, recN ≠ rec.name := by
    intro recN M ctorN N rr hp rec hrec heq
    obtain ⟨recN', M', ctorN', N', c, hf, hc, -⟩ := H.shape hp
    obtain ⟨rfl, -, -, -⟩ := iota_toPattern_inj hf
    subst heq
    have := addInduct_rec_fresh h hrec; rw [hc] at this; cases this
  constructor
  · intro p rr hp
    rcases addInduct_pats_origin h hp with hold | ⟨rec, hrec, ru, hru, hform⟩
    · obtain ⟨recN, M, ctorN, N, c, hf, hc, hrec⟩ := H.shape hold
      exact ⟨recN, M, ctorN, N, c, hf, hle.constants hc, hrec⟩
    · exact ⟨rec.name, rec.getMajorIdx, ru.ctor, ru.ctorParams + ru.nfields, _, hform,
        addInduct_rec_find h hrec, (hwf.rec_shape rec hrec).recHeaded⟩
  · intro recN M₁ c₁ N₁ rr₁ M₂ c₂ N₂ rr₂ h1 h2
    rcases addInduct_pats_origin h h1 with hold1 | ⟨ra, hra, rua, hrua, hfa⟩ <;>
      rcases addInduct_pats_origin h h2 with hold2 | ⟨rb, hrb, rub, hrub, hfb⟩
    · exact H.arity hold1 hold2
    · obtain ⟨hrn, -, -, -⟩ := iota_toPattern_inj hfb
      exact absurd hrn (hold_fresh hold1 rb hrb)
    · obtain ⟨hrn, -, -, -⟩ := iota_toPattern_inj hfa
      exact absurd hrn (hold_fresh hold2 ra hra)
    · obtain ⟨hrn_a, hm_a, -, -⟩ := iota_toPattern_inj hfa
      obtain ⟨hrn_b, hm_b, -, -⟩ := iota_toPattern_inj hfb
      have hab : ra = rb := addInduct_recs_name_inj h hra hrb (by rw [← hrn_a, ← hrn_b])
      rw [hm_a, hm_b, hab]
  · intro recN M ctorN N rr hp
    rcases addInduct_pats_origin h hp with hold | ⟨rec, hrec, ru, hru, hform⟩
    · obtain ⟨ci, hci, hctor⟩ := H.ctor_shape hold
      exact ⟨ci, hle.constants hci, hctor⟩
    · obtain ⟨-, -, rfl, -⟩ := iota_toPattern_inj hform
      obtain ⟨ci, hci, hcs⟩ := addInduct_rule_ctor hwf h hrec hru
      exact ⟨ci, hci, hcs.2⟩
  · intro p rr rr' hp hp'
    rcases addInduct_pats_origin' h hp with hold | ⟨ra, hra, rua, hrua, hca, ea, hea⟩ <;>
      rcases addInduct_pats_origin' h hp' with hold' | ⟨rb, hrb, rub, hrub, hcb, eb, heb⟩
    · exact H.functional hold hold'
    · subst eb; exact absurd rfl (hold_fresh hold rb hrb)
    · subst ea; exact absurd rfl (hold_fresh hold' ra hra)
    · obtain ⟨hname, -, hctor, -⟩ := iota_toPattern_inj (ea.symm.trans eb)
      obtain rfl : ra = rb := addInduct_recs_name_inj h hra hrb hname
      obtain rfl : rua = rub := nodup_map_inj_on (hwf.rules_nodup ra hra) rua hrua rub hrub hctor
      subst ea; cases eb
      exact hea.trans heb.symm

/-- Every well-formed environment satisfies the pattern population invariant. -/
theorem WF.patsIota {env : VEnv} (H : env.WF) : env.PatsIota := by
  obtain ⟨ds, H⟩ := H
  induction H with
  | empty =>
    constructor
    · intro p rr h; exact (h : False).elim
    · intro _ _ _ _ _ _ _ _ _ h1 _; exact (h1 : False).elim
    · intro _ _ _ _ _ h; exact (h : False).elim
    · intro _ _ _ h _; exact (h : False).elim
  | decl hd _ ih =>
    rcases hd.pats_eq_or_induct with heq | ⟨decl, hwf, hind⟩
    · exact ih.of_le heq hd.le
    · exact ih.induct hwf hind

/-! ### The discharged `Params` side conditions -/

/-- `Params.pat_simple` for `env.pats`: every registered pattern is a `SimplePattern`. -/
theorem WF.pat_simple {env : VEnv} (H : env.WF) {p rr} (hp : env.pats p rr) :
    ∃ sp : SimplePattern, p = sp.toPattern := by
  obtain ⟨recN, M, ctorN, N, _, hform, _⟩ := H.patsIota.shape hp
  exact ⟨.iota recN M ctorN N, hform⟩

/-- `Params.pat_uniq` for `env.pats`: if a subpattern `p₃` of a registered redex `p₁`
intersects a registered redex `p₂`, then `p₁ = p₂ = p₃` and the reducts agree. The
intersection forces the recursor spines to agree: at the top (`refl`) both spines
match and `functional` closes; inside the recursor spine (`appL`) the arity would drop
below `arity`; inside the constructor spine (`appR`) a recursor would be a
constructor (`rec_ne_ctor`). -/
theorem WF.pat_uniq {env : VEnv} (H : env.WF) {p₁ p₂ p₃ p₄ : Pattern}
    {r : p₁.RHS × p₁.Check} {r' : p₂.RHS × p₂.Check}
    (h1 : env.pats p₁ r) (h2 : env.pats p₂ r') (hs : Subpattern p₃ p₁)
    (hi : p₂.inter p₃ = some p₄) : p₁ = p₂ ∧ p₂ = p₃ ∧ HEq r r' := by
  have HI := H.patsIota
  obtain ⟨R₁, M₁, C₁, N₁, c₁, rfl, -, -⟩ := HI.shape h1
  obtain ⟨R₂, M₂, C₂, N₂, c₂, rfl, -, -⟩ := HI.shape h2
  simp only [SimplePattern.toPattern] at hs
  cases hs with
  | refl =>
    simp only [SimplePattern.toPattern] at hi
    obtain ⟨g, b, hg, hb, -⟩ := Pattern.inter_app_app hi
    obtain ⟨rfl, rfl, -⟩ := Pattern.varN_const_inter hg
    obtain ⟨rfl, rfl, -⟩ := Pattern.varN_const_inter hb
    exact ⟨rfl, rfl, heq_of_eq (HI.functional h1 h2)⟩
  | appL hs' =>
    obtain ⟨i, hi', rfl⟩ := Pattern.subpattern_varN_const hs'
    cases i with
    | zero => simp [SimplePattern.toPattern, Pattern.varN, Pattern.inter_app_const] at hi
    | succ i =>
      simp only [SimplePattern.toPattern, Pattern.varN] at hi
      obtain ⟨g, hg, -⟩ := Pattern.inter_app_var hi
      obtain ⟨rfl, rfl, -⟩ := Pattern.varN_const_inter hg
      have := HI.arity h1 h2
      omega
  | appR hs' =>
    obtain ⟨i, hi', rfl⟩ := Pattern.subpattern_varN_const hs'
    cases i with
    | zero => simp [SimplePattern.toPattern, Pattern.varN, Pattern.inter_app_const] at hi
    | succ i =>
      simp only [SimplePattern.toPattern, Pattern.varN] at hi
      obtain ⟨g, hg, -⟩ := Pattern.inter_app_var hi
      obtain ⟨rfl, -, -⟩ := Pattern.varN_const_inter hg
      exact absurd rfl (HI.rec_ne_ctor h2 h1)

/-- `Params.pat_app_l` for `env.pats`: the left factor of an ι redex's application
subpattern (the recursor spine) has no application subpattern of its own. -/
theorem WF.pat_app_l {env : VEnv} (H : env.WF) {p p₁ p₂ p₃ p₄ rr} (hp : env.pats p rr)
    (hs : Subpattern (.app p₁ p₂) p) : ¬ Subpattern (.app p₃ p₄) p₁ := by
  obtain ⟨recN, M, ctorN, N, _, rfl, _⟩ := H.patsIota.shape hp
  rw [app_subpattern_iota hs]
  exact Pattern.not_app_subpattern_varN_const

/-- `Params.pat_app_l_uniq` for `env.pats`: a variable-argument slot of one ι redex's
recursor spine never intersects another ι redex's recursor spine, since the recursor
name fixes the spine arity (`PatsIota.arity`). -/
theorem WF.pat_app_l_uniq {env : VEnv} (H : env.WF) {p r p' r' p₁ p₂ p₁' p₂' p₃}
    (hp : env.pats p r) (hp' : env.pats p' r')
    (hs : Subpattern (.app p₁ p₂) p) (hs' : Subpattern (.app p₁' p₂') p')
    (hv : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  have HI := H.patsIota
  obtain ⟨recN, M, ctorN, N, c, rfl, hc⟩ := HI.shape hp
  obtain ⟨recN', M', ctorN', N', c', rfl, hc'⟩ := HI.shape hp'
  have e1 : p₁ = (Pattern.const recN).varN M := app_subpattern_iota hs
  have e1' : p₁' = (Pattern.const recN').varN M' := app_subpattern_iota hs'
  subst e1 e1'
  obtain ⟨k, hk, hkk⟩ := Pattern.subpattern_varN_const hv
  cases k with
  | zero => simp [Pattern.varN] at hkk
  | succ i =>
    simp only [Pattern.varN] at hkk
    injection hkk with hkk; subst hkk
    cases hinter : ((Pattern.const recN').varN M').inter ((Pattern.const recN).varN i) with
    | none => rfl
    | some r₄ =>
      exfalso
      obtain ⟨hrr, hMi, _⟩ := Pattern.varN_const_inter hinter
      subst hrr
      have hMM : M = M' := HI.arity hp hp'
      omega

/-- `Params.pat_app_uniq` for `env.pats`: a subpattern of one ι redex's recursor spine
never intersects a subpattern of another ι redex's constructor spine, since a recursor
is never a constructor (`PatsIota.rec_ne_ctor`). -/
theorem WF.pat_app_uniq {env : VEnv} (H : env.WF) {p r p' r' p₁ p₂ p₁' p₂' p₃ p₃'}
    (hp : env.pats p r) (hp' : env.pats p' r')
    (hs : Subpattern (.app p₁ p₂) p) (hs' : Subpattern (.app p₁' p₂') p')
    (h3 : Subpattern p₃ p₁) (h3' : Subpattern p₃' p₂') : p₃.inter p₃' = none := by
  have HI := H.patsIota
  obtain ⟨R, M, C, N, c, rfl, -, -⟩ := HI.shape hp
  obtain ⟨R', M', C', N', c', rfl, -, -⟩ := HI.shape hp'
  obtain ⟨rfl, -⟩ := app_subpattern_iota' hs
  obtain ⟨-, rfl⟩ := app_subpattern_iota' hs'
  obtain ⟨i, -, rfl⟩ := Pattern.subpattern_varN_const h3
  obtain ⟨j, -, rfl⟩ := Pattern.subpattern_varN_const h3'
  cases hinter : ((Pattern.const R).varN i).inter ((Pattern.const C').varN j) with
  | none => rfl
  | some q =>
    obtain ⟨rfl, -, -⟩ := Pattern.varN_const_inter hinter
    exact absurd rfl (HI.rec_ne_ctor hp hp')

/-- Every registered definitional equation is realised by a registered pattern: the
content of `Params.extra_pat`, stated verbatim for `env.pats` (in particular the level
bound `uvars` of the instantiating levels is arbitrary there, as in the class field).

This is a **design hypothesis** of `toParams`, inherited from `Params`, not a deferred proof.
`ChurchRosser`'s `Params` reads every `defeqs` entry as realised by a `Pat` rule, while in
this model the δ rules of definitions (`VDecl.WF.def`/`mutualDef`) and the quotient rule
(`VDecl.WF.quot`) are definitional axioms in `defeqs` and are not registered as `pats`:
`pats` holds the ι rules, whose reducts have the computational shape `VEnv.PatWF` asks of a
reduction rule, whereas a δ reduct is the definition's closed body, of arbitrary shape, and
the quotient rule's redex `Quot.lift f h (Quot.mk r a)` is written under binders that no
`SimplePattern` matches (`SimplePattern.defn` is unused). `DefEqsAsPats` therefore holds of
an environment built from axioms and inductives only and fails for any environment containing
a `def` or `quot`; `toParams` is a `Params` instance exactly for the environments that satisfy
it, and discharging `extra_pat` for the δ/quot rules is the pre-existing gap between `Params`
and `VDecl.WF`, left to the maintainers. -/
def DefEqsAsPats (env : VEnv) (U : Nat) : Prop :=
  ∀ {df : VDefEq} {ls : List VLevel} {uvars : Nat} {Γ : List VExpr},
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    ∃ (p : Pattern) (r : p.RHS × p.Check) (m1 : List VLevel) (m2 : p.Path → VExpr),
      env.pats p r ∧ p.Matches (df.lhs.instL ls) m1 m2 ∧
      r.2.OK (env.IsDefEqU U Γ) m1 m2 ∧ df.rhs.instL ls = r.1.apply m1 m2

/-- The `Params` structure induced by a well-formed environment `env`, taking the
abstract reduction relation `Pat` to be `env.pats`. Five side conditions are
discharged from `VEnv.PatsIota`; `pat_wf` is `IsDefEq.pat` (recovering a `Realizes`
witness from `Check.OK`); `pat_env` is the identity; `extra_pat` is the design hypothesis
`hδ : env.DefEqsAsPats U` (see `DefEqsAsPats`). -/
@[reducible] def toParams (env : VEnv) (henv : env.WF) (U : Nat) (hδ : env.DefEqsAsPats U) :
    Params where
  env := env
  henv := henv
  univs := U
  Pat := env.pats
  pat_simple := fun hp => henv.pat_simple hp
  pat_uniq := fun h1 h2 hs hi => henv.pat_uniq h1 h2 hs hi
  pat_wf := fun {_ _ _ _ _ Γ A} hpat hmatch hty hok =>
    let ⟨_, hr, hall⟩ := hok.exists_realizer (rel := fun a b t => IsDefEq env U Γ a b t)
    ⟨A, IsDefEq.pat hpat hmatch hty hr hall⟩
  pat_app_l := fun hp hs => henv.pat_app_l hp hs
  pat_app_l_uniq := fun hp hp' hs hs' hv => henv.pat_app_l_uniq hp hp' hs hs' hv
  pat_app_uniq := fun hp hp' hs hs' h3 h3' => henv.pat_app_uniq hp hp' hs hs' h3 h3'
  extra_pat := fun h1 h2 h3 => hδ h1 h2 h3
  pat_env := id

end VEnv
end Lean4Lean
