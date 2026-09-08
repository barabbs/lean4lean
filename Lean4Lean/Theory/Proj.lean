import Lean4Lean.Theory.VExpr

/-!
# Structure projections as recursor expansions

`VExpr` has no projection node. A projection `.proj S i e` of a structure value `e : S ps` is
modelled by an application of the recursor the kernel generates for `S`. That is the kernel's
own reading of `Expr.proj`: `inferProj`'s Prop gate and `toCtorWhenStruct`'s elimination test
keep a projection no more powerful than that recursor (`divergences.md`), so nothing is lost by
spelling one out. The shape is Carneiro's thesis's `inv_x` (typesys.tex §"Undecidability of
definitional equality"), which projects the argument of `intro` out of a proof of `acc x`
through `rec_acc`:

    P_i e,   P_i = S.rec (uss i) ps (λ x : S ps. F_i[f_j := P_j x]) (λ f₀ … f_{n-1}. f_i)

where `F₀ … F_{n-1}` is the constructor's field telescope instantiated at the parameters `ps`
(`VExpr.instPis`/`VExpr.piBinders`, what the kernel's `inferProj` computes), `F_i` lives
under the earlier fields `f₀ … f_{i-1}`, and the earlier projection *functions* `P_j`, `j < i`,
are the same expansions (`VExpr.projFns`, well-founded on `i`). The motive of field `i` is
the field's type with the earlier fields replaced by their projections of the bound major,
so that `P_i e : F_i[f_j := P_j e]` (`VExpr.projTy`) — the kernel's `inferProj` result with
`.proj S j e ↦ P_j e`, and the dependent typing shape of the thesis's *primitive* projections
`π₂ p : β[π₁ p/x]` (Wtypes.tex, whose W-type system omits the recursors for `Σ` in favour of
projections). For field `0` and for every field whose type does not mention earlier
fields this is the constant motive `λ _. F_i` (`projMotiveBody_zero`). The elimination level
of `P_j` is the sort of `F_j`, which differs between fields (`Sigma.fst` uses
`Sigma.rec.{u+1,u,v}`, `Sigma.snd` `Sigma.rec.{v+1,u,v}`), hence a level list `uss j` per
field — the thesis's motive type `κ = ∀ a::α. P a → U_u` for a large-eliminating type (`→ P`
otherwise), with `u` a *fresh* universe variable per use of `rec_P` (axioms.tex §2.6.3).

De Bruijn conventions. Contexts are listed outermost first, `bvar 0` is innermost. Over
`Γ, f₀ … f_{n-1}` field `j` is `bvar (n-1-j)` (`fieldSelector`); `F_i` lives over
`Γ, f₀ … f_{i-1}`. `instFields F Ps` substitutes `f_j := Ps[j]` outermost first: `f₀ =
bvar (m-1)` is hit first by `inst _ (m-1)`, which lifts `Ps[0]` under the `m-1` remaining
binders. `projMotiveBodyOf` first moves `F_i` under the motive's binder `x` (`liftN 1 i`
shifts the `Γ`-variables past `x`), then substitutes `f_j := P_j x` with `P_j` lifted past `x`.

Typing of the expansion (derivation, thesis §2.6.3–4, mechanized on instances in
`Tests/ProjInhabit.lean`): for a non-recursive structure with the kernel's recursor
`∀ ps (C : S ps → Sort ℓ) (m : ∀ f::Fs, C (mk ps f)) (t : S ps), C t`, ι rule
`rec ps C m (mk ps f) ≡ m f`, and `ℓ_i` the sort of `F_i`, by strong induction on `i` with
`uss i = ℓ_i :: usS`:
(a) `Γ, x ⊢ projMotiveBody i : sort ℓ_i` — substitute the fields of `F_i` by the typed
`P_j x` (`IsDefEq.instN`, using (c) for `j < i` weakened past `x`);
(b) `Γ ⊢ ∀ f::Fs, F_i⁺ ≡ ∀ f::Fs, projMotive i (mk ps f)` — `beta` under the field
binders, then `IsDefEq.pat` for each used `P_j (mk ps f)` on the *generic* constructor spine
(typed by (c) and the constructor's type), whose reduct β-reduces through the rule template
and `fieldSelector Fs j` to `f_j`, then `IsDefEq.instDF`;
(c) `Γ ⊢ projFn i : ∀ x : S ps, projMotiveBody i` — `constDF` at `S.rec (uss i)`, `appDF` on
the parameters, the motive (a) and the selector (b, `defeqDF`), then `forallEDF`/`beta` with
`instN_bvar0`.
Only forward rules of `IsDefEq` are used: no structure-η, no K-like reduction, no injectivity.

Structure η is the one thing the representation does not carry: the checker's `tryEtaStruct`
and `toCtorWhenStruct` equate a value with its expansion `S.mk ps (p₁ t) … (pₙ t)`, and
`IsDefEq` has no such rule (`tryEtaStructCore.WF` is the open obligation). Nothing here blocks
adding a per-structure η rule; the expansion simply does not provide one.
-/

namespace Lean4Lean
open Lean

namespace VExpr

/-! ### Builders -/

/-- The λ-telescope over field types `Fs` that selects its `i`-th binder:
`fun (f₀ : Fs[0]) … (f_{n-1} : Fs[n-1]) => fᵢ`; field `i` (numbered from the outside) is
`bvar (Fs.length - 1 - i)`. The minor premise of a structure's recursor that reads out field `i`. -/
def fieldSelector (Fs : List VExpr) (i : Nat) : VExpr :=
  Fs.foldr .lam (.bvar (Fs.length - 1 - i))

/-- Instantiate the leading Π-binders of `ty` with `args`, outermost first (the parameter loop
of the kernel's `inferProj`); `none` if `ty` has fewer manifest binders. -/
def instPis : VExpr → List VExpr → Option VExpr
  | e, [] => some e
  | .forallE _ B, a :: as => instPis (B.inst a) as
  | _, _ :: _ => none

/-- `instFields F Ps`: `F` lives under the `Ps.length` innermost binders `f₀ … f_{m-1}`
(outermost first, `f_j = bvar (m-1-j)`), each `Ps[j]` lives outside them; substitute
`f_j := Ps[j]` outermost first (`f₀ = bvar (m-1)` is hit first, `inst _ (m-1)` lifting `Ps[0]`
under the `m-1` remaining binders). Substituting for an unused binder is the identity. -/
def instFields : VExpr → List VExpr → VExpr
  | F, [] => F
  | F, P :: Ps => instFields (F.inst P Ps.length) Ps

/-- The body, over `Γ, x`, of the motive of projection `i`: `Fs[i]` (over `Γ, f₀ … f_{i-1}`)
moved under the new binder `x` (`liftN 1 i` shifts the `Γ`-variables past `x`), then
`f_j := Ps[j] x` for the earlier projection *functions* `Ps` (over `Γ`). -/
def projMotiveBodyOf (Fs : List VExpr) (i : Nat) (Ps : List VExpr) : VExpr :=
  instFields ((Fs.getD i default).liftN 1 i) (Ps.map fun P => .app P.lift (.bvar 0))

/-- The projection function of field `i` given the earlier projection functions `Ps`:
`S.rec (uss i) ps (λ x : S usS ps. Fs[i][f := Ps x]) (fieldSelector Fs i)`. -/
def projFnOf (S : Name) (usS : List VLevel) (uss : Nat → List VLevel) (ps Fs : List VExpr)
    (i : Nat) (Ps : List VExpr) : VExpr :=
  (const (mkRecName S) (uss i)).mkApps
    (ps ++ [.lam ((const S usS).mkApps ps) (projMotiveBodyOf Fs i Ps), fieldSelector Fs i])

/-- The first `i` projection functions `[P₀, …, P_{i-1}]` of the structure `S usS ps` with field
telescope `Fs`, over `Γ`:
`P_j = S.rec (uss j) ps (λ x : S usS ps. Fs[j][f := P x]) (fieldSelector Fs j)`.
`uss j` is the recursor's level list for field `j` — the field's own elimination level
consed onto `usS` for a large-eliminating recursor (`Sigma.fst` uses `Sigma.rec.{u+1,u,v}`,
`Sigma.snd` `Sigma.rec.{v+1,u,v}`), `usS` itself for a small-eliminating one. Thesis
§2.6.3: `u` is a *fresh* universe variable per use of `rec_P`. -/
def projFns (S : Name) (usS : List VLevel) (uss : Nat → List VLevel) (ps Fs : List VExpr) :
    Nat → List VExpr
  | 0 => []
  | i+1 => projFns S usS uss ps Fs i ++ [projFnOf S usS uss ps Fs i (projFns S usS uss ps Fs i)]

/-- Motive body of projection `i`, over `Γ, x`: `Fs[i][f_j := P_j x]`. -/
def projMotiveBody (S : Name) (usS : List VLevel) (uss : Nat → List VLevel) (ps Fs : List VExpr)
    (i : Nat) : VExpr :=
  projMotiveBodyOf Fs i (projFns S usS uss ps Fs i)

/-- The projection *function* `P_i : ∀ x : S usS ps, projMotiveBody … i` (thesis `inv_x`):
`S.rec (uss i) ps (λ x. Fs[i][f_j := P_j x]) (λ f. f_i)`. -/
def projFn (S : Name) (usS : List VLevel) (uss : Nat → List VLevel) (ps Fs : List VExpr)
    (i : Nat) : VExpr :=
  (const (mkRecName S) (uss i)).mkApps
    (ps ++ [.lam ((const S usS).mkApps ps) (projMotiveBody S usS uss ps Fs i), fieldSelector Fs i])

/-- The type of `P_i e`, over `Γ`: `Fs[i][f_j := P_j e]` — the kernel's `inferProj` result with
`.proj S j struct ↦ P_j struct'` (`(projMotiveBody … i).inst e`). -/
def projTy (S : Name) (usS : List VLevel) (uss : Nat → List VLevel) (ps Fs : List VExpr)
    (i : Nat) (e : VExpr) : VExpr :=
  instFields (Fs.getD i default) ((projFns S usS uss ps Fs i).map fun P => .app P e)

/-- The Π-arity of the `k`-th binder of the Π-telescope `ty`, `none` if there is no such
binder. `ty.binderArity? (np+1) = some nf` says that the minor premise of a structure's
recursor (binder `np+1`, after the parameters and the motive) has exactly the `nf` fields
as binders — no inductive-hypothesis binder: the constructor is non-recursive, and the
ι reduct applies the minor to the fields alone (`VInductDecl.WF.rule_shape`'s count). -/
def binderArity? (ty : VExpr) (k : Nat) : Option Nat := ty.piBinders[k]?.map piArity

/-! ### Unfolding facts -/

theorem projFn_eq :
    projFn S usS uss ps Fs i = projFnOf S usS uss ps Fs i (projFns S usS uss ps Fs i) := rfl

theorem projFns_succ :
    projFns S usS uss ps Fs (i+1) = projFns S usS uss ps Fs i ++ [projFn S usS uss ps Fs i] := rfl

@[simp] theorem projFns_length : (projFns S usS uss ps Fs i).length = i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [projFns_succ, ih]

/-- The motive of field `0` is the constant motive `fun _ => Fs[0]`. -/
@[simp] theorem projMotiveBody_zero :
    projMotiveBody S usS uss ps Fs 0 = (Fs.getD 0 default).lift := rfl

/-! ### The builders under substitution

`VExpr.lift'` and `VExpr.inst` are both instances of `VExpr.subst` (`lift'_eq_subst`,
`instN_eq`), and every builder below shifts its pieces by one binder per field. So each is
proved once against `subst`, with `σ.liftN j` for the piece standing under `j` binders, and
the weakening and instantiation forms are read off: `Lift.consN j` for the first, `Subst.liftN`
at `k + j` for the second. Level instantiation substitutes levels, not terms, so the `instL`
family keeps its own proofs. -/

theorem foldr_lam_subst : ∀ (Fs : List VExpr) (base : VExpr) (σ : Subst),
    (List.foldr lam base Fs).subst σ =
      List.foldr lam (base.subst (σ.liftN Fs.length))
        (Fs.mapIdx fun j F => F.subst (σ.liftN j))
  | [], _, _ => rfl
  | F :: Fs, base, σ => by
    simp only [List.foldr_cons, subst, List.mapIdx_cons, List.length_cons,
      foldr_lam_subst Fs base σ.lift, Subst.lift_liftN]
    rfl

theorem foldr_lam_inst {Fs : List VExpr} {base e₀ : VExpr} {k : Nat} :
    (List.foldr lam base Fs).inst e₀ k =
      List.foldr lam (base.inst e₀ (k + Fs.length)) (Fs.mapIdx fun j F => F.inst e₀ (k + j)) := by
  simp only [instN_eq, foldr_lam_subst, Subst.liftN_liftN]

theorem foldr_lam_instL {Fs : List VExpr} {base : VExpr} {ls : List VLevel} :
    (List.foldr lam base Fs).instL ls = List.foldr lam (base.instL ls) (Fs.map (·.instL ls)) := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih => simp [List.foldr, instL, ih]

theorem fieldSelector_subst {Fs : List VExpr} {σ : Subst} {i : Nat} (hi : i < Fs.length) :
    (fieldSelector Fs i).subst σ =
      fieldSelector (Fs.mapIdx fun j F => F.subst (σ.liftN j)) i := by
  rw [fieldSelector, fieldSelector, List.length_mapIdx, foldr_lam_subst, subst_bvar,
    Subst.Fixes.liftN _ _ (show Fs.length - 1 - i < Fs.length by omega)]

theorem fieldSelector_instL {Fs : List VExpr} {ls : List VLevel} {i : Nat} :
    (fieldSelector Fs i).instL ls = fieldSelector (Fs.map (·.instL ls)) i := by
  rw [fieldSelector, fieldSelector, foldr_lam_instL]; simp [instL, List.length_map]

/-! ### `instFields` under substitution and level instantiation

`instFields` and `VExpr.insts` are the two conventions for substituting a telescope, and both
are kept. `insts` is the β-chain convention: it substitutes at index `0` once per binder, so
its `j`-th argument must live under the binders still standing when its turn comes.
`instFields` substitutes at the descending indices `m-1, …, 0`, so all of its arguments live
over `Γ` alone. The two therefore differ by a relifting of each argument past the binders
`insts` has not yet consumed, and neither is a special case of the other; the projection
builders take their `P_j` over `Γ`, so they use `instFields`. -/

@[simp] theorem instFields_nil (F : VExpr) : instFields F [] = F := rfl

theorem instFields_cons (F P : VExpr) (Ps : List VExpr) :
    instFields F (P :: Ps) = instFields (F.inst P Ps.length) Ps := rfl

theorem instFields_subst : ∀ (Ps : List VExpr) (F : VExpr) (σ : Subst),
    (instFields F Ps).subst σ = instFields (F.subst (σ.liftN Ps.length)) (Ps.map (·.subst σ))
  | [], _, _ => rfl
  | P :: Ps, F, σ => by
    simp only [instFields_cons, List.map_cons, List.length_cons, List.length_map]
    rw [instFields_subst Ps, subst_instN]

theorem instFields_instL : ∀ (Ps : List VExpr) (F : VExpr) (ls : List VLevel),
    (instFields F Ps).instL ls = instFields (F.instL ls) (Ps.map (·.instL ls))
  | [], _, _ => rfl
  | P :: Ps, F, ls => by
    simp only [instFields_cons, List.map_cons, List.length_map]
    rw [instFields_instL Ps, instL_instN]

/-! ### `instPis` under weakening / instantiation / level instantiation -/

theorem instPis_subst : ∀ (T : VExpr) (ps : List VExpr) {cty : VExpr} (σ : Subst),
    T.instPis ps = some cty → (T.subst σ).instPis (ps.map (·.subst σ)) = some (cty.subst σ)
  | _, [], _, _, h => by cases h; rfl
  | .forallE _ B, a :: as, _, σ, h => by
    simp only [instPis] at h; simp only [subst, List.map_cons, instPis]
    rw [← subst_inst]; exact instPis_subst _ _ σ h
  | .bvar _, _ :: _, _, _, h | .sort _, _ :: _, _, _, h | .const .., _ :: _, _, _, h
  | .app .., _ :: _, _, _, h | .lam .., _ :: _, _, _, h => nomatch h

theorem instPis_lift' (T : VExpr) (ps : List VExpr) {cty : VExpr} (ρ : Lift)
    (h : T.instPis ps = some cty) :
    (T.lift' ρ).instPis (ps.map (·.lift' ρ)) = some (cty.lift' ρ) := by
  simpa only [lift'_eq_subst] using instPis_subst T ps _ h

theorem instPis_inst (T : VExpr) (ps : List VExpr) {cty : VExpr} (e₀ : VExpr) (k : Nat)
    (h : T.instPis ps = some cty) :
    (T.inst e₀ k).instPis (ps.map (·.inst e₀ k)) = some (cty.inst e₀ k) := by
  simpa only [instN_eq] using instPis_subst T ps _ h

theorem instPis_instL : ∀ (T : VExpr) (ps : List VExpr) {cty : VExpr} (ls : List VLevel),
    T.instPis ps = some cty → (T.instL ls).instPis (ps.map (·.instL ls)) = some (cty.instL ls)
  | _, [], _, _, h => by cases h; rfl
  | .forallE _ B, a :: as, _, ls, h => by
    simp only [instPis] at h; simp only [instL, List.map_cons, instPis]
    rw [← instL_instN]; exact instPis_instL _ _ ls h
  | .bvar _, _ :: _, _, _, h | .sort _, _ :: _, _, _, h | .const .., _ :: _, _, _, h
  | .app .., _ :: _, _, _, h | .lam .., _ :: _, _, _, h => nomatch h

theorem instPis_ctorHeaded : ∀ (T : VExpr) (ps : List VExpr) {cty : VExpr},
    T.CtorHeaded → T.instPis ps = some cty → cty.CtorHeaded
  | _, [], _, hT, h => by cases h; exact hT
  | .forallE _ B, a :: as, _, hT, h => by
    simp only [instPis] at h
    exact instPis_ctorHeaded _ _ (CtorHeaded.inst (T := B) hT a 0) h
  | .bvar _, _ :: _, _, _, h | .sort _, _ :: _, _, _, h | .const .., _ :: _, _, _, h
  | .app .., _ :: _, _, _, h | .lam .., _ :: _, _, _, h => nomatch h

/-- `instPis` consumes exactly `ps.length` of the Π-binders of a `CtorHeaded` type. -/
theorem instPis_piArity : ∀ (T : VExpr) (ps : List VExpr) {cty : VExpr},
    T.CtorHeaded → T.instPis ps = some cty → cty.piArity + ps.length = T.piArity
  | _, [], _, _, h => by cases h; rfl
  | .forallE _ B, a :: as, _, hT, h => by
    simp only [instPis] at h
    have := instPis_piArity _ _ (CtorHeaded.inst (T := B) hT a 0) h
    simp only [piArity, List.length_cons, piArity_inst_of_ctorHeaded (T := B) hT] at this ⊢; omega
  | .bvar _, _ :: _, _, _, h | .sort _, _ :: _, _, _, h | .const .., _ :: _, _, _, h
  | .app .., _ :: _, _, _, h | .lam .., _ :: _, _, _, h => nomatch h

/-! ### The projection builders under substitution and level instantiation -/

theorem projMotiveBodyOf_subst {Fs : List VExpr} {i : Nat} {Ps : List VExpr} (σ : Subst)
    (hPs : Ps.length = i) :
    (projMotiveBodyOf Fs i Ps).subst σ.lift =
      projMotiveBodyOf (Fs.mapIdx fun j F => F.subst (σ.liftN j)) i (Ps.map (·.subst σ)) := by
  unfold projMotiveBodyOf
  rw [instFields_subst, List.length_map, hPs, Subst.lift_liftN, liftN_subst_liftN,
    List.getD_mapIdx (α := VExpr) (β := VExpr) (fun _ => rfl)]
  congr 1
  simp only [List.map_map, Function.comp_def, subst_app, subst_bvar, Subst.lift, lift_subst_lift]

theorem projMotiveBodyOf_instL {Fs : List VExpr} {i : Nat} {Ps : List VExpr} (ls : List VLevel) :
    (projMotiveBodyOf Fs i Ps).instL ls =
      projMotiveBodyOf (Fs.map (·.instL ls)) i (Ps.map (·.instL ls)) := by
  unfold projMotiveBodyOf
  rw [instFields_instL, List.getD_map (α := VExpr) (β := VExpr) rfl, instL_liftN]
  congr 1
  simp only [List.map_map, Function.comp_def, instL, instL_liftN]

theorem projFnOf_subst {S usS uss ps Fs i Ps} (σ : Subst) (hi : i < Fs.length)
    (hPs : Ps.length = i) :
    (projFnOf S usS uss ps Fs i Ps).subst σ =
      projFnOf S usS uss (ps.map (·.subst σ)) (Fs.mapIdx fun j F => F.subst (σ.liftN j)) i
        (Ps.map (·.subst σ)) := by
  unfold projFnOf
  rw [mkApps_subst]
  simp only [List.map_append, List.map_cons, List.map_nil, subst, mkApps_subst,
    projMotiveBodyOf_subst σ hPs, fieldSelector_subst hi]

theorem projFnOf_instL {S usS uss ps Fs i Ps} (ls : List VLevel) :
    (projFnOf S usS uss ps Fs i Ps).instL ls =
      projFnOf S (usS.map (VLevel.inst ls)) (fun j => (uss j).map (VLevel.inst ls))
        (ps.map (·.instL ls)) (Fs.map (·.instL ls)) i (Ps.map (·.instL ls)) := by
  unfold projFnOf
  rw [mkApps_instL]
  simp only [List.map_append, List.map_cons, List.map_nil, instL, mkApps_instL,
    projMotiveBodyOf_instL ls, fieldSelector_instL]

theorem projFns_subst {S usS uss ps Fs} (σ : Subst) : ∀ {i : Nat}, i ≤ Fs.length →
    (projFns S usS uss ps Fs i).map (·.subst σ) =
      projFns S usS uss (ps.map (·.subst σ)) (Fs.mapIdx fun j F => F.subst (σ.liftN j)) i
  | 0, _ => rfl
  | i+1, hi => by
    rw [projFns_succ, List.map_append, projFns_subst σ (Nat.le_of_succ_le hi), projFn_eq,
      List.map_cons, List.map_nil, projFnOf_subst σ hi projFns_length,
      projFns_subst σ (Nat.le_of_succ_le hi)]
    rfl

theorem projFns_instL {S usS uss ps Fs} (ls : List VLevel) : ∀ {i : Nat},
    (projFns S usS uss ps Fs i).map (·.instL ls) =
      projFns S (usS.map (VLevel.inst ls)) (fun j => (uss j).map (VLevel.inst ls))
        (ps.map (·.instL ls)) (Fs.map (·.instL ls)) i
  | 0 => rfl
  | i+1 => by
    rw [projFns_succ, List.map_append, projFns_instL ls, projFn_eq,
      List.map_cons, List.map_nil, projFnOf_instL ls, projFns_instL ls]
    rfl

theorem projFn_subst {S usS uss ps Fs i} (σ : Subst) (hi : i < Fs.length) :
    (projFn S usS uss ps Fs i).subst σ =
      projFn S usS uss (ps.map (·.subst σ)) (Fs.mapIdx fun j F => F.subst (σ.liftN j)) i := by
  rw [projFn_eq, projFn_eq, projFnOf_subst σ hi projFns_length,
    projFns_subst σ (Nat.le_of_lt hi)]

theorem projFn_lift' {S usS uss ps Fs i} (ρ : Lift) (hi : i < Fs.length) :
    (projFn S usS uss ps Fs i).lift' ρ =
      projFn S usS uss (ps.map (·.lift' ρ)) (Fs.mapIdx fun j F => F.lift' (ρ.consN j)) i := by
  rw [lift'_eq_subst, projFn_subst _ hi]
  simp only [lift'_eq_subst, Subst.liftN_lift_l_id]

theorem projFn_inst {S usS uss ps Fs i} (e₀ : VExpr) (k : Nat) (hi : i < Fs.length) :
    (projFn S usS uss ps Fs i).inst e₀ k =
      projFn S usS uss (ps.map (·.inst e₀ k)) (Fs.mapIdx fun j F => F.inst e₀ (k + j)) i := by
  rw [instN_eq, projFn_subst _ hi]
  simp only [instN_eq, Subst.liftN_liftN]

theorem projFn_instL {S usS uss ps Fs i} (ls : List VLevel) :
    (projFn S usS uss ps Fs i).instL ls =
      projFn S (usS.map (VLevel.inst ls)) (fun j => (uss j).map (VLevel.inst ls))
        (ps.map (·.instL ls)) (Fs.map (·.instL ls)) i := by
  rw [projFn_eq, projFn_eq, projFnOf_instL ls, projFns_instL ls]

theorem projMotiveBody_subst {S usS uss ps Fs i} (σ : Subst) (hi : i ≤ Fs.length) :
    (projMotiveBody S usS uss ps Fs i).subst σ.lift =
      projMotiveBody S usS uss (ps.map (·.subst σ))
        (Fs.mapIdx fun j F => F.subst (σ.liftN j)) i := by
  unfold projMotiveBody
  rw [projMotiveBodyOf_subst σ projFns_length, projFns_subst σ hi]

theorem projMotiveBody_lift' {S usS uss ps Fs i} (ρ : Lift) (hi : i ≤ Fs.length) :
    (projMotiveBody S usS uss ps Fs i).lift' ρ.cons =
      projMotiveBody S usS uss (ps.map (·.lift' ρ))
        (Fs.mapIdx fun j F => F.lift' (ρ.consN j)) i := by
  rw [lift'_eq_subst, ← Subst.lift_lift_l_id, projMotiveBody_subst _ hi]
  simp only [lift'_eq_subst, Subst.liftN_lift_l_id]

theorem projMotiveBody_instN {S usS uss ps Fs i} (e₀ : VExpr) (k : Nat) (hi : i ≤ Fs.length) :
    (projMotiveBody S usS uss ps Fs i).inst e₀ (k+1) =
      projMotiveBody S usS uss (ps.map (·.inst e₀ k))
        (Fs.mapIdx fun j F => F.inst e₀ (k + j)) i := by
  rw [instN_eq, show Subst.liftN (.one e₀) (k+1) = (Subst.liftN (.one e₀) k).lift from rfl,
    projMotiveBody_subst _ hi]
  simp only [instN_eq, Subst.liftN_liftN]

theorem projMotiveBody_instL {S usS uss ps Fs i} (ls : List VLevel) :
    (projMotiveBody S usS uss ps Fs i).instL ls =
      projMotiveBody S (usS.map (VLevel.inst ls)) (fun j => (uss j).map (VLevel.inst ls))
        (ps.map (·.instL ls)) (Fs.map (·.instL ls)) i := by
  unfold projMotiveBody
  rw [projMotiveBodyOf_instL ls, projFns_instL ls]

/-! ### λ-telescopes and `instFields` on variable spines

The ι reduct of a structure's rule is the template `λ params motive minor fields, minor
fields` applied to the redex's arguments; `betaN`-style reduction of a λ-telescope
saturated by its arguments substitutes them outermost first (`instFields`), and on the
variable spine `minor fields` this selects the minor and the fields
(`instFields_minor_spine`). -/

theorem instFields_app : ∀ (Ps : List VExpr) (f a : VExpr),
    instFields (.app f a) Ps = .app (instFields f Ps) (instFields a Ps)
  | [], _, _ => rfl
  | _ :: Ps, f, a => by simp only [instFields_cons, inst]; exact instFields_app Ps _ _

theorem instFields_mkApps (Ps : List VExpr) (f : VExpr) : ∀ l : List VExpr,
    instFields (f.mkApps l) Ps = (instFields f Ps).mkApps (l.map (instFields · Ps))
  | [] => rfl
  | a :: l => by
    rw [mkApps_cons, instFields_mkApps Ps _ l, instFields_app, List.map_cons, mkApps_cons]

theorem instFields_liftN : ∀ (Ps : List VExpr) (e : VExpr), instFields (e.liftN Ps.length) Ps = e
  | [], e => by simp
  | _ :: Ps, e => by
    simp only [instFields_cons, List.length_cons]
    rw [Nat.add_comm, ← liftN'_liftN_lo, inst_liftN, instFields_liftN Ps]

/-- Substituting the variable spine's binders: variable `j` (of `Ps.length`, innermost
first) becomes `Ps[Ps.length - 1 - j]`. -/
theorem instFields_bvar : ∀ (Ps : List VExpr) (j : Nat), j < Ps.length →
    instFields (.bvar j) Ps = Ps.getD (Ps.length - 1 - j) default
  | P :: Ps, j, h => by
    simp only [instFields_cons, inst, instVar, List.length_cons]
    split
    · rename_i hj
      rw [instFields_bvar Ps j hj, show Ps.length + 1 - 1 - j = (Ps.length - 1 - j) + 1 by omega,
        List.getD_cons_succ]
    · split
      · rename_i hj; subst hj
        rw [instFields_liftN, Nat.add_sub_cancel, Nat.sub_self, List.getD_cons_zero]
      · simp only [List.length_cons] at h; omega

/-- The reduct of a structure's ι rule, `λ params motive minor fields, minor fields`, on the
arguments `pre ++ s :: fs` (with `s` the minor's argument): `s fs`. -/
theorem instFields_minor_spine (pre : List VExpr) (s : VExpr) (fs : List VExpr) :
    instFields ((bvar fs.length).mkApps (bvarsDesc 0 fs.length)) (pre ++ s :: fs) =
      s.mkApps fs := by
  rw [instFields_mkApps, instFields_bvar _ _ (by simp; omega)]
  have hlen : (pre ++ s :: fs).length - 1 - fs.length = pre.length := by simp
  rw [hlen, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]
  congr 1
  apply List.ext_getElem
  · simp
  · intro t h1 h2
    simp only [List.getElem_map] at h1 ⊢
    rw [getElem_bvarsDesc _ _ _ (by simpa using h1),
      instFields_bvar _ _ (by simp <;> omega),
      show (pre ++ s :: fs).length - 1 - (0 + (fs.length - 1 - t)) = pre.length + (t + 1) by
        simp <;> omega,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.getElem?_eq_getElem h2,
      Option.getD_some]

end VExpr
end Lean4Lean
