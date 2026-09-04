import Lean4Lean.Theory.VExpr

/-!
# Structure projections as recursor expansions

`VExpr` has no projection node. A projection `.proj S i e` of a structure value `e : S ps` is
modelled by a recursor expansion in the style of Carneiro's thesis's `inv_x` (typesys.tex
§"Undecidability of definitional equality"), which projects the argument of `intro` out of a
proof of `acc x` through `rec_acc`:

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

Typing of the expansion (derivation, thesis §2.6.3–4; not a theorem here): for a
non-recursive structure with the kernel's recursor `∀ ps (C : S ps → Sort ℓ)
(m : ∀ f::Fs, C (mk ps f)) (t : S ps), C t`, ι rule `rec ps C m (mk ps f) ≡ m f`, and
`ℓ_i` the sort of `F_i`, by strong induction on `i` with `uss i = ℓ_i :: usS`:
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

theorem projFn_eq : projFn S usS uss ps Fs i = projFnOf S usS uss ps Fs i (projFns S usS uss ps Fs i) :=
  rfl

theorem projFns_succ :
    projFns S usS uss ps Fs (i+1) = projFns S usS uss ps Fs i ++ [projFn S usS uss ps Fs i] := rfl

@[simp] theorem projFns_length : (projFns S usS uss ps Fs i).length = i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [projFns_succ, ih]

/-- The motive of field `0` is the constant motive `fun _ => Fs[0]`. -/
@[simp] theorem projMotiveBody_zero :
    projMotiveBody S usS uss ps Fs 0 = (Fs.getD 0 default).lift := rfl

/-! ### Structural lemmas for `mkApps` and `fieldSelector`

Weakening / instantiation / level-instantiation distribute over `mkApps` (a left fold of
`.app`) and over `fieldSelector` (a right fold of `.lam` selecting a bound variable). -/

theorem mkApps_lift' {f : VExpr} {args : List VExpr} {ρ : Lift} :
    (f.mkApps args).lift' ρ = (f.lift' ρ).mkApps (args.map (·.lift' ρ)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => simp [VExpr.mkApps, List.foldl] at *; rw [ih]; rfl

theorem mkApps_inst {f : VExpr} {args : List VExpr} {e₀ : VExpr} {k : Nat} :
    (f.mkApps args).inst e₀ k = (f.inst e₀ k).mkApps (args.map (·.inst e₀ k)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => simp [VExpr.mkApps, List.foldl] at *; rw [ih]; rfl

theorem mkApps_instL {f : VExpr} {args : List VExpr} {ls : List VLevel} :
    (f.mkApps args).instL ls = (f.instL ls).mkApps (args.map (·.instL ls)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => simp [VExpr.mkApps, List.foldl] at *; rw [ih]; rfl

theorem consN_fixes : ∀ (m : Nat) (ρ : Lift), (ρ.consN m).Fixes m
  | 0, _ => trivial
  | m+1, ρ => consN_fixes m ρ

theorem foldr_lam_lift'_aux : ∀ (Fs : List VExpr) (base : VExpr) (ρ : Lift) (d : Nat),
    (List.foldr lam base Fs).lift' (ρ.consN d) =
      List.foldr lam (base.lift' (ρ.consN (d + Fs.length)))
        (Fs.mapIdx fun j F => F.lift' (ρ.consN (d + j))) := by
  intro Fs; induction Fs with
  | nil => intro base ρ d; simp
  | cons F Fs ih =>
    intro base ρ d
    simp only [List.foldr_cons, lift', List.mapIdx_cons, List.length_cons, Nat.add_zero]
    rw [show (ρ.consN d).cons = ρ.consN (d+1) from rfl, ih base ρ (d+1)]
    have e1 : d + 1 + Fs.length = d + (Fs.length + 1) := by omega
    have e2 : (fun (j : Nat) (F : VExpr) => F.lift' (ρ.consN (d + 1 + j)))
            = (fun (j : Nat) (F : VExpr) => F.lift' (ρ.consN (d + (j + 1)))) := by
      funext j F; rw [show d + 1 + j = d + (j + 1) from by omega]
    rw [e1, e2]

theorem foldr_lam_lift' (Fs : List VExpr) (base : VExpr) (ρ : Lift) :
    (List.foldr lam base Fs).lift' ρ =
      List.foldr lam (base.lift' (ρ.consN Fs.length)) (Fs.mapIdx fun j F => F.lift' (ρ.consN j)) := by
  have := foldr_lam_lift'_aux Fs base ρ 0; simpa using this

theorem fieldSelector_lift' {Fs : List VExpr} {ρ : Lift} {i : Nat} (hi : i < Fs.length) :
    (fieldSelector Fs i).lift' ρ = fieldSelector (Fs.mapIdx fun j F => F.lift' (ρ.consN j)) i := by
  rw [fieldSelector, fieldSelector, foldr_lam_lift', List.length_mapIdx, lift',
      (consN_fixes _ _).liftVar_eq (show Fs.length - 1 - i < Fs.length by omega)]

theorem foldr_lam_inst_aux : ∀ (Fs : List VExpr) (base e₀ : VExpr) (k : Nat),
    (List.foldr lam base Fs).inst e₀ k =
      List.foldr lam (base.inst e₀ (k + Fs.length)) (Fs.mapIdx fun j F => F.inst e₀ (k + j)) := by
  intro Fs; induction Fs with
  | nil => intro base e₀ k; simp
  | cons F Fs ih =>
    intro base e₀ k
    simp only [List.foldr_cons, inst, List.mapIdx_cons, List.length_cons, Nat.add_zero]
    rw [ih base e₀ (k+1)]
    have e1 : k + 1 + Fs.length = k + (Fs.length + 1) := by omega
    have e2 : (fun (j : Nat) (F : VExpr) => F.inst e₀ (k + 1 + j))
            = (fun (j : Nat) (F : VExpr) => F.inst e₀ (k + (j + 1))) := by
      funext j F; rw [show k + 1 + j = k + (j + 1) from by omega]
    rw [e1, e2]

theorem fieldSelector_inst {Fs : List VExpr} {e₀ : VExpr} {k i : Nat} (hi : i < Fs.length) :
    (fieldSelector Fs i).inst e₀ k = fieldSelector (Fs.mapIdx fun j F => F.inst e₀ (k + j)) i := by
  rw [fieldSelector, fieldSelector, foldr_lam_inst_aux, List.length_mapIdx]
  have : (bvar (Fs.length - 1 - i)).inst e₀ (k + Fs.length) = bvar (Fs.length - 1 - i) := by
    simp only [inst, instVar]; rw [if_pos (by omega)]
  rw [this]

theorem foldr_lam_instL {Fs : List VExpr} {base : VExpr} {ls : List VLevel} :
    (List.foldr lam base Fs).instL ls = List.foldr lam (base.instL ls) (Fs.map (·.instL ls)) := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih => simp [List.foldr, instL, ih]

theorem fieldSelector_instL {Fs : List VExpr} {ls : List VLevel} {i : Nat} :
    (fieldSelector Fs i).instL ls = fieldSelector (Fs.map (·.instL ls)) i := by
  rw [fieldSelector, fieldSelector, foldr_lam_instL]; simp [instL, List.length_map]

/-- Weakening / instantiation commute with the `.lift` sitting under one extra binder. -/
theorem lift_lift'_cons {b : VExpr} {ρ : Lift} :
    (b.lift).lift' ρ.cons = (b.lift' ρ).lift := by
  rw [lift_eq_lift', lift_eq_lift', ← lift'_comp, ← lift'_comp]
  simp [Lift.comp, Lift.refl_comp]

theorem lift_inst_cons {b e₀ : VExpr} {k : Nat} :
    (b.lift).inst e₀ (k+1) = (b.inst e₀ k).lift := (lift_instN_lo ..).symm

/-! ### Weakening under `k` binders commutes with instantiation -/

theorem _root_.Lean4Lean.Lift.consN_cons (ρ : Lift) : ∀ j : Nat, (Lift.cons ρ).consN j = ρ.consN (j+1)
  | 0 => rfl
  | j+1 => by rw [Lift.consN, Lift.consN_cons ρ j]; rfl

theorem _root_.Lean4Lean.Lift.liftVar_consN_lt {ρ : Lift} {m i : Nat} (h : i < m) :
    (ρ.consN m).liftVar i = i :=
  (consN_fixes m ρ).liftVar_eq h

theorem _root_.Lean4Lean.Lift.liftVar_consN_succ (ρ : Lift) (m i : Nat) :
    (ρ.consN (m+1)).liftVar (i+1) = (ρ.consN m).liftVar i + 1 := rfl

/-- `lift'` under `m` binders commutes with `inst` at index `m`; the `m = 0` case is
`lift'_inst_hi`. -/
theorem lift'_instN_hi (e1 e2 : VExpr) (ρ : Lift) (m : Nat) :
    (e1.inst e2 m).lift' (ρ.consN m) = (e1.lift' (ρ.consN (m+1))).inst (e2.lift' ρ) m := by
  induction e1 generalizing m with
  | bvar i =>
    simp only [inst, lift']
    rcases Nat.lt_trichotomy i m with h | rfl | h
    · rw [Lift.liftVar_consN_lt (Nat.lt_succ_of_lt h)]
      simp only [instVar, if_pos h, lift', Lift.liftVar_consN_lt h]
    · rw [Lift.liftVar_consN_lt (Nat.lt_succ_self i)]
      simp only [instVar, Nat.lt_irrefl, ite_true, ite_false]
      rw [← lift'_consN_skipN (n := i) (k := 0) (e := e2),
        ← lift'_consN_skipN (n := i) (k := 0) (e := e2.lift' ρ)]
      show (e2.lift' (Lift.skipN .refl i)).lift' (ρ.consN i) = (e2.lift' ρ).lift' (Lift.skipN .refl i)
      rw [← lift'_comp, ← lift'_comp, Lift.skipN_comp_consN, Lift.comp_skipN, Lift.refl_comp]
      rfl
    · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [Lift.liftVar_consN_succ]
      have hle : m ≤ (ρ.consN m).liftVar i := Nat.le_trans (Nat.le_of_lt_succ h) Lift.le_liftVar
      simp only [instVar]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
  | sort _ => rfl
  | const _ _ => rfl
  | app f a ihf iha => simp only [inst, lift', ihf, iha]
  | lam A b ihA ihb => simp only [inst, lift', ihA]; exact congrArg _ (ihb (m+1))
  | forallE A b ihA ihb => simp only [inst, lift', ihA]; exact congrArg _ (ihb (m+1))

/-- `liftN 1 _ i` (inserting a binder at depth `i`) commutes with `lift'` past it; generalises
`lift_lift'_cons`. -/
theorem liftN_lift'_consN (e : VExpr) (ρ : Lift) (i : Nat) :
    (e.liftN 1 i).lift' (ρ.consN (i+1)) = (e.lift' (ρ.consN i)).liftN 1 i := by
  rw [← lift'_consN_skipN, ← lift'_consN_skipN, ← lift'_comp, ← lift'_comp,
    ← Lift.consN_cons, ← Lift.consN_comp, ← Lift.consN_comp]
  simp [Lift.comp]

/-! ### `instFields` under weakening / instantiation / level instantiation -/

@[simp] theorem instFields_nil (F : VExpr) : instFields F [] = F := rfl

theorem instFields_cons (F P : VExpr) (Ps : List VExpr) :
    instFields F (P :: Ps) = instFields (F.inst P Ps.length) Ps := rfl

theorem instFields_inst : ∀ (Ps : List VExpr) (F e₀ : VExpr) (k : Nat),
    (instFields F Ps).inst e₀ k = instFields (F.inst e₀ (k + Ps.length)) (Ps.map (·.inst e₀ k))
  | [], _, _, _ => rfl
  | P :: Ps, F, e₀, k => by
    simp only [instFields_cons, List.map_cons, List.length_cons, List.length_map]
    rw [instFields_inst Ps, inst_inst_hi, Nat.add_assoc]

theorem instFields_lift' : ∀ (Ps : List VExpr) (F : VExpr) (ρ : Lift),
    (instFields F Ps).lift' ρ = instFields (F.lift' (ρ.consN Ps.length)) (Ps.map (·.lift' ρ))
  | [], _, _ => rfl
  | P :: Ps, F, ρ => by
    simp only [instFields_cons, List.map_cons, List.length_cons, List.length_map]
    rw [instFields_lift' Ps, lift'_instN_hi]

theorem instFields_instL : ∀ (Ps : List VExpr) (F : VExpr) (ls : List VLevel),
    (instFields F Ps).instL ls = instFields (F.instL ls) (Ps.map (·.instL ls))
  | [], _, _ => rfl
  | P :: Ps, F, ls => by
    simp only [instFields_cons, List.map_cons, List.length_map]
    rw [instFields_instL Ps, instL_instN]

/-! ### `piBinders`, `piArity` and `instPis` under weakening / instantiation -/

theorem piBinders_lift' : ∀ (T : VExpr) (ρ : Lift),
    (T.lift' ρ).piBinders = T.piBinders.mapIdx fun j A => A.lift' (ρ.consN j)
  | .forallE A B, ρ => by
    simp only [lift', piBinders, List.mapIdx_cons, piBinders_lift' B, Lift.consN_cons]; rfl
  | .bvar _, _ | .sort _, _ | .const .., _ | .app .., _ | .lam .., _ => rfl

/-- A `CtorHeaded` type is not a Π-telescope ending in a variable, so instantiation cannot
create new leading binders. -/
theorem CtorHeaded.forallE {A B : VExpr} (h : (VExpr.forallE A B).CtorHeaded) : B.CtorHeaded := h

theorem getAppFn_inst_const : ∀ {f : VExpr} {I : Name} {us : List VLevel},
    f.getAppFn = .const I us → ∀ (e₀ : VExpr) (k : Nat), (f.inst e₀ k).getAppFn = .const I us
  | .app f _, _, _, h, e₀, k => getAppFn_inst_const (f := f) h e₀ k
  | .const .., _, _, h, _, _ => h
  | .bvar _, _, _, h, _, _ | .sort _, _, _, h, _, _ | .lam .., _, _, h, _, _
  | .forallE .., _, _, h, _, _ => nomatch h

theorem CtorHeaded.inst : ∀ {T : VExpr}, T.CtorHeaded → ∀ (e₀ : VExpr) (k : Nat),
    (T.inst e₀ k).CtorHeaded
  | .forallE _ B, h, e₀, k => CtorHeaded.inst (T := B) h e₀ (k+1)
  | .const .., ⟨I, us, h⟩, _, _ => ⟨I, us, h⟩
  | .app .., ⟨I, us, h⟩, e₀, k => ⟨I, us, getAppFn_inst_const h e₀ k⟩
  | .bvar _, ⟨_, _, h⟩, _, _ | .sort _, ⟨_, _, h⟩, _, _ | .lam .., ⟨_, _, h⟩, _, _ => nomatch h

theorem getAppFn_instL_const : ∀ {f : VExpr} {I : Name} {us : List VLevel},
    f.getAppFn = .const I us → ∀ ls : List VLevel,
      (f.instL ls).getAppFn = .const I (us.map (VLevel.inst ls))
  | .app f _, _, _, h, ls => getAppFn_instL_const (f := f) h ls
  | .const .., _, _, h, _ => by cases h; rfl
  | .bvar _, _, _, h, _ | .sort _, _, _, h, _ | .lam .., _, _, h, _
  | .forallE .., _, _, h, _ => nomatch h

theorem CtorHeaded.instL : ∀ {T : VExpr}, T.CtorHeaded → ∀ ls : List VLevel, (T.instL ls).CtorHeaded
  | .forallE _ B, h, ls => CtorHeaded.instL (T := B) h ls
  | .const .., _, _ => ⟨_, _, rfl⟩
  | .app .., ⟨_, _, h⟩, ls => ⟨_, _, getAppFn_instL_const h ls⟩
  | .bvar _, ⟨_, _, h⟩, _ | .sort _, ⟨_, _, h⟩, _ | .lam .., ⟨_, _, h⟩, _ => nomatch h

theorem piBinders_inst_of_ctorHeaded : ∀ {T : VExpr}, T.CtorHeaded → ∀ (e₀ : VExpr) (k : Nat),
    (T.inst e₀ k).piBinders = T.piBinders.mapIdx fun j A => A.inst e₀ (k + j)
  | .forallE A B, h, e₀, k => by
    simp only [inst, piBinders, List.mapIdx_cons, piBinders_inst_of_ctorHeaded (T := B) h,
      Nat.add_zero]
    have e : (fun (j : Nat) (A : VExpr) => A.inst e₀ (k + 1 + j))
        = fun j A => A.inst e₀ (k + (j + 1)) := by
      funext j A; rw [Nat.add_right_comm]; rfl
    rw [e]
  | .bvar _, ⟨_, _, h⟩, _, _ => nomatch h
  | .sort _, _, _, _ | .const .., _, _, _ | .app .., _, _, _ | .lam .., _, _, _ => rfl

theorem piBinders_instL : ∀ (T : VExpr) (ls : List VLevel),
    (T.instL ls).piBinders = T.piBinders.map (·.instL ls)
  | .forallE A B, ls => by simp only [instL, piBinders, List.map_cons, piBinders_instL B]
  | .bvar _, _ | .sort _, _ | .const .., _ | .app .., _ | .lam .., _ => rfl

theorem piArity_inst_of_ctorHeaded {T : VExpr} (h : T.CtorHeaded) (e₀ : VExpr) (k : Nat) :
    (T.inst e₀ k).piArity = T.piArity := by
  rw [← piBinders_length, piBinders_inst_of_ctorHeaded h, List.length_mapIdx, piBinders_length]

theorem piArity_instL (T : VExpr) (ls : List VLevel) : (T.instL ls).piArity = T.piArity := by
  rw [← piBinders_length, piBinders_instL, List.length_map, piBinders_length]

theorem instPis_lift' : ∀ (T : VExpr) (ps : List VExpr) {cty : VExpr} (ρ : Lift),
    T.instPis ps = some cty → (T.lift' ρ).instPis (ps.map (·.lift' ρ)) = some (cty.lift' ρ)
  | _, [], _, _, h => by cases h; rfl
  | .forallE _ B, a :: as, _, ρ, h => by
    simp only [instPis] at h; simp only [lift', List.map_cons, instPis]
    rw [← lift'_inst_hi]; exact instPis_lift' _ _ ρ h
  | .bvar _, _ :: _, _, _, h | .sort _, _ :: _, _, _, h | .const .., _ :: _, _, _, h
  | .app .., _ :: _, _, _, h | .lam .., _ :: _, _, _, h => nomatch h

theorem instPis_inst : ∀ (T : VExpr) (ps : List VExpr) {cty : VExpr} (e₀ : VExpr) (k : Nat),
    T.instPis ps = some cty → (T.inst e₀ k).instPis (ps.map (·.inst e₀ k)) = some (cty.inst e₀ k)
  | _, [], _, _, _, h => by cases h; rfl
  | .forallE _ B, a :: as, _, e₀, k, h => by
    simp only [instPis] at h; simp only [inst, List.map_cons, instPis]
    rw [← inst0_inst_hi]; exact instPis_inst _ _ e₀ k h
  | .bvar _, _ :: _, _, _, _, h | .sort _, _ :: _, _, _, _, h | .const .., _ :: _, _, _, _, h
  | .app .., _ :: _, _, _, _, h | .lam .., _ :: _, _, _, _, h => nomatch h

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

/-! ### The projection builders under weakening / instantiation / level instantiation -/

theorem getD_mapIdx {f : Nat → VExpr → VExpr} (hf : ∀ i, f i default = default)
    (Fs : List VExpr) (i : Nat) : (Fs.mapIdx f).getD i default = f i (Fs.getD i default) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  cases Fs[i]? <;> simp [hf]

theorem getD_map {f : VExpr → VExpr} (hf : f default = default) (Fs : List VExpr) (i : Nat) :
    (Fs.map f).getD i default = f (Fs.getD i default) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases Fs[i]? <;> simp [hf]

theorem projMotiveBodyOf_lift' {Fs : List VExpr} {i : Nat} {Ps : List VExpr} (ρ : Lift)
    (hPs : Ps.length = i) :
    (projMotiveBodyOf Fs i Ps).lift' ρ.cons =
      projMotiveBodyOf (Fs.mapIdx fun j F => F.lift' (ρ.consN j)) i (Ps.map (·.lift' ρ)) := by
  unfold projMotiveBodyOf
  rw [instFields_lift', List.length_map, hPs, Lift.consN_cons, liftN_lift'_consN,
    getD_mapIdx (fun _ => rfl)]
  congr 1
  simp only [List.map_map, Function.comp_def, lift', lift_lift'_cons, Lift.liftVar]

theorem projMotiveBodyOf_inst {Fs : List VExpr} {i : Nat} {Ps : List VExpr} (e₀ : VExpr) (k : Nat)
    (hPs : Ps.length = i) :
    (projMotiveBodyOf Fs i Ps).inst e₀ (k+1) =
      projMotiveBodyOf (Fs.mapIdx fun j F => F.inst e₀ (k + j)) i (Ps.map (·.inst e₀ k)) := by
  unfold projMotiveBodyOf
  rw [instFields_inst, List.length_map, hPs, getD_mapIdx (fun _ => rfl),
    show k + 1 + i = 1 + (k + i) by omega, ← liftN_instN_lo _ _ _ _ _ (Nat.le_add_left i k)]
  congr 1
  simp only [List.map_map, Function.comp_def, inst, lift_inst_cons, instVar_lower]

theorem projMotiveBodyOf_instL {Fs : List VExpr} {i : Nat} {Ps : List VExpr} (ls : List VLevel) :
    (projMotiveBodyOf Fs i Ps).instL ls =
      projMotiveBodyOf (Fs.map (·.instL ls)) i (Ps.map (·.instL ls)) := by
  unfold projMotiveBodyOf
  rw [instFields_instL, getD_map rfl, instL_liftN]
  congr 1
  simp only [List.map_map, Function.comp_def, instL, instL_liftN]

theorem projFnOf_lift' {S usS uss ps Fs i Ps} (ρ : Lift) (hi : i < Fs.length) (hPs : Ps.length = i) :
    (projFnOf S usS uss ps Fs i Ps).lift' ρ =
      projFnOf S usS uss (ps.map (·.lift' ρ)) (Fs.mapIdx fun j F => F.lift' (ρ.consN j)) i
        (Ps.map (·.lift' ρ)) := by
  unfold projFnOf
  rw [mkApps_lift']
  simp only [List.map_append, List.map_cons, List.map_nil, lift', mkApps_lift',
    projMotiveBodyOf_lift' ρ hPs, fieldSelector_lift' hi]

theorem projFnOf_inst {S usS uss ps Fs i Ps} (e₀ : VExpr) (k : Nat) (hi : i < Fs.length)
    (hPs : Ps.length = i) :
    (projFnOf S usS uss ps Fs i Ps).inst e₀ k =
      projFnOf S usS uss (ps.map (·.inst e₀ k)) (Fs.mapIdx fun j F => F.inst e₀ (k + j)) i
        (Ps.map (·.inst e₀ k)) := by
  unfold projFnOf
  rw [mkApps_inst]
  simp only [List.map_append, List.map_cons, List.map_nil, inst, mkApps_inst,
    projMotiveBodyOf_inst e₀ k hPs, fieldSelector_inst hi]

theorem projFnOf_instL {S usS uss ps Fs i Ps} (ls : List VLevel) :
    (projFnOf S usS uss ps Fs i Ps).instL ls =
      projFnOf S (usS.map (VLevel.inst ls)) (fun j => (uss j).map (VLevel.inst ls))
        (ps.map (·.instL ls)) (Fs.map (·.instL ls)) i (Ps.map (·.instL ls)) := by
  unfold projFnOf
  rw [mkApps_instL]
  simp only [List.map_append, List.map_cons, List.map_nil, instL, mkApps_instL,
    projMotiveBodyOf_instL ls, fieldSelector_instL]

theorem projFns_lift' {S usS uss ps Fs} (ρ : Lift) : ∀ {i : Nat}, i ≤ Fs.length →
    (projFns S usS uss ps Fs i).map (·.lift' ρ) =
      projFns S usS uss (ps.map (·.lift' ρ)) (Fs.mapIdx fun j F => F.lift' (ρ.consN j)) i
  | 0, _ => rfl
  | i+1, hi => by
    rw [projFns_succ, List.map_append, projFns_lift' ρ (Nat.le_of_succ_le hi), projFn_eq,
      List.map_cons, List.map_nil, projFnOf_lift' ρ hi projFns_length,
      projFns_lift' ρ (Nat.le_of_succ_le hi)]
    rfl

theorem projFns_inst {S usS uss ps Fs} (e₀ : VExpr) (k : Nat) : ∀ {i : Nat}, i ≤ Fs.length →
    (projFns S usS uss ps Fs i).map (·.inst e₀ k) =
      projFns S usS uss (ps.map (·.inst e₀ k)) (Fs.mapIdx fun j F => F.inst e₀ (k + j)) i
  | 0, _ => rfl
  | i+1, hi => by
    rw [projFns_succ, List.map_append, projFns_inst e₀ k (Nat.le_of_succ_le hi), projFn_eq,
      List.map_cons, List.map_nil, projFnOf_inst e₀ k hi projFns_length,
      projFns_inst e₀ k (Nat.le_of_succ_le hi)]
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

theorem projFn_lift' {S usS uss ps Fs i} (ρ : Lift) (hi : i < Fs.length) :
    (projFn S usS uss ps Fs i).lift' ρ =
      projFn S usS uss (ps.map (·.lift' ρ)) (Fs.mapIdx fun j F => F.lift' (ρ.consN j)) i := by
  rw [projFn_eq, projFn_eq, projFnOf_lift' ρ hi projFns_length, projFns_lift' ρ (Nat.le_of_lt hi)]

theorem projFn_inst {S usS uss ps Fs i} (e₀ : VExpr) (k : Nat) (hi : i < Fs.length) :
    (projFn S usS uss ps Fs i).inst e₀ k =
      projFn S usS uss (ps.map (·.inst e₀ k)) (Fs.mapIdx fun j F => F.inst e₀ (k + j)) i := by
  rw [projFn_eq, projFn_eq, projFnOf_inst e₀ k hi projFns_length,
    projFns_inst e₀ k (Nat.le_of_lt hi)]

theorem projFn_instL {S usS uss ps Fs i} (ls : List VLevel) :
    (projFn S usS uss ps Fs i).instL ls =
      projFn S (usS.map (VLevel.inst ls)) (fun j => (uss j).map (VLevel.inst ls))
        (ps.map (·.instL ls)) (Fs.map (·.instL ls)) i := by
  rw [projFn_eq, projFn_eq, projFnOf_instL ls, projFns_instL ls]

theorem projMotiveBody_lift' {S usS uss ps Fs i} (ρ : Lift) (hi : i ≤ Fs.length) :
    (projMotiveBody S usS uss ps Fs i).lift' ρ.cons =
      projMotiveBody S usS uss (ps.map (·.lift' ρ)) (Fs.mapIdx fun j F => F.lift' (ρ.consN j)) i := by
  unfold projMotiveBody
  rw [projMotiveBodyOf_lift' ρ projFns_length, projFns_lift' ρ hi]

theorem projMotiveBody_instN {S usS uss ps Fs i} (e₀ : VExpr) (k : Nat) (hi : i ≤ Fs.length) :
    (projMotiveBody S usS uss ps Fs i).inst e₀ (k+1) =
      projMotiveBody S usS uss (ps.map (·.inst e₀ k)) (Fs.mapIdx fun j F => F.inst e₀ (k + j)) i := by
  unfold projMotiveBody
  rw [projMotiveBodyOf_inst e₀ k projFns_length, projFns_inst e₀ k hi]

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

/-- The leading λ-binder types, outermost first. -/
def lamBinders : VExpr → List VExpr
  | .lam A b => A :: b.lamBinders
  | _ => []

@[simp] theorem lamBinders_length : ∀ e : VExpr, e.lamBinders.length = e.lamArity
  | .lam _ b => by simp [lamBinders, lamArity, lamBinders_length b]
  | .bvar _ | .sort _ | .const .. | .app .. | .forallE .. => rfl

theorem foldr_lam_lamBinders : ∀ e : VExpr, e.lamBinders.foldr lam e.lamBody = e
  | .lam _ b => by simp [lamBinders, lamBody, foldr_lam_lamBinders b]
  | .bvar _ | .sort _ | .const .. | .app .. | .forallE .. => rfl

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

theorem getElem_bvarsDesc (lo n t : Nat) (h : t < n) :
    (bvarsDesc lo n)[t]'(by simp [h]) = .bvar (lo + (n - 1 - t)) := by
  simp [bvarsDesc, List.getElem_reverse]

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
    simp only [List.getElem_map, bvarsDesc_length] at h1 ⊢
    rw [getElem_bvarsDesc _ _ _ (by simpa using h1),
      instFields_bvar _ _ (by simp <;> omega),
      show (pre ++ s :: fs).length - 1 - (0 + (fs.length - 1 - t)) = pre.length + (t + 1) by
        simp <;> omega,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.getElem?_eq_getElem h2,
      Option.getD_some]

end VExpr
end Lean4Lean
