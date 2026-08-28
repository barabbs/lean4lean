import Lean4Lean.Std.SMap
import Lean4Lean.Declaration
import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Theory.Typing.InductiveParams

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem TrConstant.sf_mono (hsf : safety ≤ safety')
    (H : TrConstant safety' env ci ci') : TrConstant safety env ci ci' :=
  ⟨safety.le_trans hsf H.1, H.2⟩

theorem TrConstant.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstant safety env ci ci') : TrConstant safety env' ci ci' :=
  ⟨H.1, H.2.1, H.2.2.mono henv⟩

theorem TrConstVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstVal safety env ci ci') : TrConstVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2⟩

theorem TrDefVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrDefVal safety env ci ci') : TrDefVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2.mono henv⟩

variable (safety : DefinitionSafety) in
inductive Aligned : ConstMap → VEnv → Prop where
  | empty : Aligned {} .empty
  | ignoreConst : Aligned C venv → C.find? n = none → ¬safety ≤ ci.safety →
    ci.name = n → Aligned (C.insert n ci) venv
  | const : Aligned C venv → C.find? n = none → TrConstant safety venv ci ci' →
    venv.addConst n ci' = some venv' → ci.name = n → Aligned (C.insert n ci) venv'
  | defeq : Aligned C venv → Aligned C (venv.addDefEq df)

theorem Aligned.map_wf (H : Aligned safety C venv) : C.WF := by
  induction H with
  | empty => exact .empty
  | ignoreConst _ h1 _ _ ih
  | const _ h1 _ _ _ ih => exact ih.insert _ _ h1
  | defeq _ ih => exact ih

theorem Aligned.find?_iff (H : Aligned safety C venv) :
    (∃ ci, C.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  induction H with
  | empty => simp [SMap.find?, VEnv.empty]
  | ignoreConst H _ h2 _ ih =>
    simp [H.map_wf.find?_insert]; split <;> [skip; assumption]
    rename_i eq1 eq2; subst eq2; simp [← ih, *]
  | const H h1 h2 eq _ ih =>
    simp [H.map_wf.find?_insert]
    simp [VEnv.addConst] at eq; split at eq <;> cases eq
    split <;> simp_all; exact h2.1
  | defeq _ ih => exact ih

theorem Aligned.addQuot1 {Q : Prop}
    (H1 : ∀ c env, Aligned safety c env → P c env → Q)
    (C env) (wf : Aligned safety C env) (H2 : AddQuot1 n k ci P C env) : Q := by
  let ⟨_, _, _, h1, h2, h3, h4⟩ := H2
  exact H1 _ _ (wf.const h2 (h1.sf_mono DefinitionSafety.le_safe) h3 rfl) h4

nonrec theorem Aligned.addQuot (H : AddQuot C₁ C₂ venv₁ venv₂)
    (wf : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  dsimp [AddQuot] at H
  refine (addQuot1 <| addQuot1 <| addQuot1 <| addQuot1 ?_) _ _ wf H
  rintro _ _ h ⟨rfl, rfl⟩; exact h.defeq

theorem Aligned.addInduct (H : AddInduct C₁ venv₁ decl C₂ venv₂)
    (h : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  -- IOTA-TODO(soundness): `Aligned` has no constructor for `addInduct`'s final
  -- `addPat` stage, and records no per-step `addConst` witnesses, so the batch
  -- `AddInduct` cannot rebuild an `Aligned`. `pats_iota` bypasses this (via
  -- `TrEnv'.constMap_wf`); only the `Aligned`-routed `find?`/`of_value` family is
  -- tainted.
  sorry

theorem Aligned.addDefEqs {C : ConstMap} : ∀ {cis' : List VDefVal} {venv},
    Aligned safety C venv → Aligned safety C (venv.addDefEqs cis')
  | [], _, H => H
  | ci :: cis, venv, H => by
    show Aligned safety C (VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis)
    exact Aligned.addDefEqs H.defeq

theorem Aligned.insertDefs : ∀ {cis : List DefinitionVal} {cis' : List VDefVal} {C venv venv'},
    Aligned safety C venv → (cis.map (·.name)).Nodup →
    (∀ ci ∈ cis, C.find? ci.name = none) →
    List.Forall₂ (fun ci ci' => TrConstVal safety venv (.defnInfo ci) ci'.toVConstVal) cis cis' →
    venv.addConsts cis' = some venv' → Aligned safety (insertDefs C cis) venv'
  | [], _, _, _, _, H, _, _, hblk, e => by
    cases hblk; simp [VEnv.addConsts] at e; cases e; exact H
  | ci :: cis, _, C, venv, _, H, hnd, hfr, hblk, e => by
    cases hblk with | @cons _ ci' _ _ htr hblk => ?_
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨venv₁, h1, h2⟩ := e
    have hname := htr.2
    simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hname
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have h1' : venv.addConst ci.name ci'.toVConstant = some venv₁ := by rw [hname]; exact h1
    show Aligned safety
      (_root_.Lean4Lean.insertDefs (SMap.insert C ci.name (.defnInfo ci)) cis) _
    refine Aligned.insertDefs (H.const (hfr _ (.head _)) htr.1 h1' rfl) hnd.2
      (fun c hc => ?_) (Lean4Lean.List.Forall₂.imp
        (fun _ _ h => h.mono (VEnv.addConst_le h1')) hblk) h2
    rw [H.map_wf.find?_insert]
    have : ¬ (ci.name == c.name) = true := by
      simp only [beq_iff_eq]; intro h
      exact hnd.1 ⟨c, hc, h.symm⟩
    simp [this]
    exact hfr c (.tail _ hc)

theorem TrEnv'.aligned (H : TrEnv' safety C Q venv) : Aligned safety C venv := by
  induction H with
  | empty => exact .empty
  | ignore h1 h2 _ ih => exact ih.ignoreConst h1 h2 rfl
  | «axiom» h1 h2 _ h _ ih => exact ih.const h2 h1 h rfl
  | thm h1 h2 _ _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | «opaque» h1 h2 _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | defn h1 h2 _ h _ ih => exact (ih.const h2 h1.1.1 h rfl).defeq
  | mutualDef hblk hnd hfr _ hadd _ _ ih =>
    exact Aligned.addDefEqs <| ih.insertDefs hnd hfr
      (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) hblk) hadd
  | quot _ h _ ih => exact ih.addQuot h
  | induct _ _ h _ ih => exact ih.addInduct h

theorem TrEnv'.map_wf (H : TrEnv' safety C Q venv) : C.WF := H.aligned.map_wf

/-! ### Constant-map well-formedness and recursor lookup, independent of `Aligned`

`pats_iota` (below) needs `SMap.WF` at every `TrEnv'` step and a way to pull a
`recInfo` lookup back across `quot`, both supplied here without routing through
`Aligned` (whose `addInduct` case is still an `IOTA-TODO`). -/

/-- Pull a `recInfo` lookup back across one fresh non-`recInfo` insertion: since
the inserted value is not a `recInfo`, a `recInfo` resolved in the extended map
was already resolved before the insertion. -/
theorem pull_recInfo {m : ConstMap} {name recName : Name} {q : ConstantInfo}
    {rval : RecursorVal} (wf : m.WF) (hq : ∀ v, q ≠ .recInfo v)
    (h : (m.insert name q).find? recName = some (.recInfo rval)) :
    m.find? recName = some (.recInfo rval) := by
  rw [wf.find?_insert] at h; split at h
  · exact absurd (Option.some.inj h) (hq rval)
  · exact h

/-- WF-preservation combinator for one `AddQuot1` step: the fresh insertion keeps
the map `SMap.WF`, so a property of the extended WF map transfers. -/
theorem AddQuot1.wf {P : ConstMap → VEnv → Prop} {Q : Prop} {name kind ci'}
    (H1 : ∀ m env, m.WF → P m env → Q)
    (m env) (wf : m.WF) (H2 : AddQuot1 name kind ci' P m env) : Q := by
  let ⟨_, _, _, _, h2, _, h4⟩ := H2
  exact H1 _ _ (wf.insert _ _ h2) h4

/-- Adding the quotient constants preserves constant-map well-formedness. -/
theorem AddQuot.wf (H : AddQuot C₁ C₂ env₁ env₂) (wf : C₁.WF) : C₂.WF := by
  dsimp [AddQuot] at H
  refine (AddQuot1.wf <| AddQuot1.wf <| AddQuot1.wf <| AddQuot1.wf ?_) _ _ wf H
  rintro m env hwf ⟨rfl, _⟩; exact hwf

/-- Pull-back combinator for one `AddQuot1` step: the inserted quotient constant
is a `quotInfo`, so a `recInfo` lookup passes through it. -/
theorem AddQuot1.pull {P : ConstMap → VEnv → Prop} {name kind ci' recName rval}
    (H1 : ∀ m env, m.WF → P m env → m.find? recName = some (.recInfo rval))
    (m env) (wf : m.WF) (H2 : AddQuot1 name kind ci' P m env) :
    m.find? recName = some (.recInfo rval) := by
  let ⟨_, _, _, _, h2, _, h4⟩ := H2
  exact pull_recInfo wf (fun _ => by nofun) (H1 _ _ (wf.insert _ _ h2) h4)

/-- A `recInfo` resolvable after adding the quotient constants was already
resolvable before: `addQuot` only registers `quotInfo` constants. -/
theorem AddQuot.pull {recName rval} (H : AddQuot C₁ C₂ env₁ env₂) (wf : C₁.WF)
    (hfind : C₂.find? recName = some (.recInfo rval)) :
    C₁.find? recName = some (.recInfo rval) := by
  dsimp [AddQuot] at H
  refine (AddQuot1.pull <| AddQuot1.pull <| AddQuot1.pull <| AddQuot1.pull ?_) _ _ wf H
  rintro m env hwf ⟨rfl, _⟩; exact hfind

/-- Inserting a whole block of definitions preserves constant-map well-formedness,
provided every name is fresh and the block has no duplicate names. -/
theorem insertDefs_wf : ∀ {cis : List DefinitionVal} {C : ConstMap}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup → (insertDefs C cis).WF
  | [], _, hC, _, _ => hC
  | d :: ds, C, hC, hfr, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    refine insertDefs_wf (cis := ds) (hC.insert _ _ (hfr _ (.head _))) (fun e he => ?_) hnd.2
    rw [hC.find?_insert, if_neg]; · exact hfr e (.tail _ he)
    simp only [beq_iff_eq]; intro hh
    exact hnd.1 (List.mem_map.2 ⟨e, he, hh.symm⟩)

/-- Constant-map well-formedness of a translated environment, by induction on
`TrEnv'`. Unlike `TrEnv'.map_wf`, it does not route through `Aligned`, so it avoids
the `Aligned.addInduct` placeholder. -/
theorem TrEnv'.constMap_wf (H : TrEnv' safety C Q venv) : C.WF := by
  induction H with
  | empty => exact .empty
  | ignore h1 _ _ ih => exact ih.insert _ _ h1
  | «axiom» _ h2 _ _ _ ih => exact ih.insert _ _ h2
  | defn _ h2 _ _ _ ih => exact ih.insert _ _ h2
  | mutualDef _ hnd hfr _ _ _ _ ih => exact insertDefs_wf ih hfr hnd
  | thm _ h2 _ _ _ _ ih => exact ih.insert _ _ h2
  | «opaque» _ h2 _ _ _ ih => exact ih.insert _ _ h2
  | quot _ h2 _ ih => exact h2.wf ih
  | induct _ _ h2 _ ih => exact h2.wf ih

theorem Aligned.find? (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' := by
  have mono {env₁ env₂} (H : env₁.LE env₂) :
      (∃ ci', env₁.constants name = some ci' ∧ TrConstant safety env₁ ci ci') →
      (∃ ci', env₂.constants name = some ci' ∧ TrConstant safety env₂ ci ci')
    | ⟨_, h1, h2⟩ => ⟨_, H.constants h1, h2.mono H⟩
  induction H with
  | empty => simp [SMap.find?] at h
  | ignoreConst h1 _ _ _ ih =>
    rw [h1.map_wf.find?_insert] at h; split at h
    · cases h; contradiction
    · exact ih h
  | const h1 _ h2 h3 _ ih =>
    have := VEnv.addConst_le h3
    rw [h1.map_wf.find?_insert] at h; split at h
    · rename_i h'; cases h; simp at h'; subst h'
      simp [VEnv.addConst] at h3; split at h3 <;> cases h3
      simp; rename_i h'; refine h2.mono this
    · let ⟨_, h1, h2⟩ := ih h; exact ⟨_, this.constants h1, h2.mono this⟩
  | defeq h1 ih => let ⟨_, h1, h2⟩ := ih h; exact ⟨_, h1, h2.mono VEnv.addDefEq_le⟩

theorem Aligned.find?_uniq (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' := by
  induction H with
  | empty => simp [SMap.find?] at h
  | ignoreConst H h2 h3 _ ih =>
    simp [H.map_wf.find?_insert] at h; split at h
    · rename_i n ci _ h'; subst n h'
      simpa [h2, hs] using H.find?_iff (name := ci.name)
    · exact ih h hs
  | const h1 h5 h2 h3 h4 ih =>
    have := VEnv.addConst_le h3
    simp [VEnv.addConst] at h3; split at h3 <;> cases h3
    simp [h1.map_wf.find?_insert] at h hs; revert h hs; split
    · rintro ⟨⟩ ⟨⟩; rename_i n _ _ _; subst n; exact ⟨h4, h2.mono this⟩
    · intro hs h; let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono this⟩
  | defeq h1 ih => let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono VEnv.addDefEq_le⟩

theorem TrEnv.find?_iff (H : TrEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  conv => enter [1,1,_,1,1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

-- theorem TrEnv.contains_iff (H : TrEnv safety env venv) :
--     env.contains name ↔ ∃ oci, venv.constants name = some oci := by
--   simp [← H.find?_iff, Kernel.Environment.find?, H.map_wf.find?'_eq_find?,
--     ← Option.isSome_iff_exists, ← SMap.find?_isSome, Kernel.Environment.contains]

theorem TrEnv.find? (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem TrEnv.find?_uniq (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

-- `VEnv.addDefEqs_le` is provided by the `Theory.Typing.InductiveParams` import
-- (identical statement); the former local duplicate here would clash with it.

theorem VEnv.addDefEqs_self : ∀ {cis' : List VDefVal} {venv : VEnv} {ci'}, ci' ∈ cis' →
    (venv.addDefEqs cis').defeqs ci'.toDefEq
  | ci :: cis, venv, _, hc => by
    show (VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis).defeqs _
    cases hc with
    | head => exact VEnv.addDefEqs_le.defeqs VEnv.addDefEq_self
    | tail _ hc => exact VEnv.addDefEqs_self hc

theorem insertDefs_find? : ∀ {cis : List DefinitionVal} {C : ConstMap} {name ci}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    (insertDefs C cis).find? name = some ci →
    C.find? name = some ci ∨ ∃ d ∈ cis, d.name = name ∧ ConstantInfo.defnInfo d = ci
  | [], _, _, _, _, _, _, h => .inl h
  | d :: ds, C, name, ci, hC, hfr, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hfr' : ∀ e ∈ ds, (SMap.insert C d.name (.defnInfo d)).find? e.name = none := by
      intro e he
      rw [hC.find?_insert]
      have : ¬ (d.name == e.name) = true := by
        simp only [beq_iff_eq]; intro hh; exact hnd.1 ⟨e, he, hh.symm⟩
      simp [this]; exact hfr e (.tail _ he)
    have h : (insertDefs (SMap.insert C d.name (.defnInfo d)) ds).find? name = some ci := h
    rcases insertDefs_find? (hC.insert _ _ (hfr _ (.head _))) hfr' hnd.2 h with h | ⟨e, he, h1, h2⟩
    · rw [hC.find?_insert] at h; split at h
      · rename_i hb; cases h
        exact .inr ⟨d, .head _, by simpa using hb, rfl⟩
      · exact .inl h
    · exact .inr ⟨e, .tail _ he, h1, h2⟩

theorem TrEnv'.of_value (H : TrEnv' safety C Q venv) (h : C.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) := by
  have {C n ci'} (hC : C.WF) :
      (SMap.insert C n ci').find? name = some ci →
      C.find? name = some ci ∨ n = name ∧ ci' = ci := by
    rw [hC.find?_insert]; simp; split <;> simp +contextual [*]
  induction H with
  | empty => simp [SMap.find?] at h
  | ignore h1 h2 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact ih h
    · exact (h2 hs).elim
  | «axiom» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | defn h2 h3 h4 h1 H ih =>
    have' le := (VEnv.addConst_le h1).trans VEnv.addDefEq_le
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      have := VEnv.IsDefEq.extra0 VEnv.addDefEq_self <|
        (H.defn h2 h3 h4 h1).wf.ordered.defEqWF VEnv.addDefEq_self
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ⟨_, this.symm⟩⟩
  | mutualDef hblk hnd hfr _ hadd _ H ih =>
    have' le := (VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le
    rcases insertDefs_find? H.map_wf hfr hnd h with h | ⟨d, hd, rfl, rfl⟩
    · exact (ih h).mono le
    · obtain ⟨d', hd', htr, hval⟩ := Lean4Lean.List.Forall₂.forall_exists_l hblk _ hd
      cases hv
      have hdefeq := VEnv.IsDefEq.extra0 (VEnv.addDefEqs_self hd')
        ((H.mutualDef hblk hnd hfr ‹_› hadd ‹_›).wf.ordered.defEqWF (VEnv.addDefEqs_self hd'))
      let ⟨⟨b1, b2, b3⟩, b4⟩ := htr
      exact ⟨_, hval.mono VEnv.addDefEqs_le, b2.symm ▸ b4.symm ▸ ⟨_, hdefeq.symm⟩⟩
  | thm h2 h3 h4 h5 h1 H ih =>
    have' le := VEnv.addConst_le h1
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      dsimp only [ConstantInfo.name, ConstantInfo.levelParams, ConstantInfo.toConstantVal] at b2 b4 ⊢
      have hp := h5.mono le
      have hb := h4.mono le
      have hc := VEnv.HasType.const0 (VEnv.addConst_self h1) ⟨_, hp⟩
      rw [b4] at hc
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ?_⟩
      exact ⟨_, .proofIrrel hp hb hc⟩
  | «opaque» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | quot _ h1 H ih =>
    suffices ∀ {n k ci' P}, (∀ C env, Aligned safety C env → P C env → C.find? name = some ci) →
        ∀ C env, Aligned safety C env → AddQuot1 n k ci' P C env → C.find? name = some ci by
      refine (ih <| this (this <| this <| this ?_) _ _ H.aligned h1).mono h1.le
      rintro _ _ _ ⟨rfl, rfl⟩; exact h
    rintro n k ci' P ih C env wf ⟨_, h1, _, h2, h3, h4, h5⟩
    have wf' := wf.const h3 ⟨by cases safety <;> rfl, h2.2⟩ h4 rfl
    obtain h | ⟨rfl, rfl⟩ := this wf.map_wf (ih _ _ wf' h5)
    · exact h
    · contradiction
  | induct _ _ hadd H ih =>
    -- The registered constants carry no delta-value, so `hv` forces `name` to have
    -- been present already in `C` (`AddInduct.value_find`); then `ih` applies.
    exact (ih (hadd.value_find h hv)).mono hadd.le

nonrec theorem TrEnv.of_value (H : TrEnv safety env venv) (h : env.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) :=
  H.of_value (by rwa [← H.map_wf.find?'_eq_find?]) hs hv

/-! ### Forward (`small ⇒ large`) constant-map monotonicity

The `pats_iota'` family threads a `recInfo` lookup *down* the `TrEnv'` induction
(splitting `find?_insert`); the *inverse* `pats_iota_inv` threads it *up*, so it
needs the opposite monotonicity: a binding present before a fresh insertion (or a
block of them) survives it. -/

/-- A binding survives a single fresh insertion at a different key. -/
theorem find?_insert_mono {C : ConstMap} {k x : Name} {v cx : ConstantInfo}
    (wf : C.WF) (hfresh : C.find? k = none) (h : C.find? x = some cx) :
    (C.insert k v).find? x = some cx := by
  rw [wf.find?_insert]; split
  · rename_i hkx; rw [beq_iff_eq] at hkx; subst hkx; simp [hfresh] at h
  · exact h

/-- A binding survives a whole block of fresh, distinctly-named insertions. -/
theorem insertDefs_find?_mono : ∀ {cis : List DefinitionVal} {C : ConstMap} {name ci}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    C.find? name = some ci → (insertDefs C cis).find? name = some ci
  | [], _, _, _, _, _, _, h => h
  | d :: ds, C, name, ci, hC, hfr, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hfresh_d : C.find? d.name = none := hfr _ (.head _)
    refine insertDefs_find?_mono (cis := ds) (hC.insert d.name (.defnInfo d) hfresh_d)
      (fun e he => ?_) hnd.2 (find?_insert_mono (v := .defnInfo d) hC hfresh_d h)
    rw [hC.find?_insert]; split
    · rename_i hb; rw [beq_iff_eq] at hb
      exact absurd (List.mem_map.2 ⟨e, he, hb.symm⟩) hnd.1
    · exact hfr e (.tail _ he)

/-- Push-forward combinator for one `AddQuot1` step: a binding at `recName ≠` the
fresh quotient name survives the step's insertion. -/
theorem AddQuot1.push {P : ConstMap → VEnv → Prop} {Q : Prop} {name kind ci' recName ci}
    (H1 : ∀ m env, m.WF → m.find? recName = some ci → P m env → Q)
    (m env) (wf : m.WF) (hf : m.find? recName = some ci)
    (H2 : AddQuot1 name kind ci' P m env) : Q := by
  obtain ⟨_, _, _, _, hnone, _, hP⟩ := H2
  exact H1 _ _ (wf.insert _ _ hnone) (find?_insert_mono wf hnone hf) hP

/-- A binding present before the quotient constants are added survives: `addQuot`
only inserts the four fresh `Quot*` names. -/
theorem AddQuot.push {recName ci} (H : AddQuot C₁ C₂ env₁ env₂) (wf : C₁.WF)
    (hf : C₁.find? recName = some ci) : C₂.find? recName = some ci := by
  dsimp [AddQuot] at H
  refine (AddQuot1.push <| AddQuot1.push <| AddQuot1.push <| AddQuot1.push ?_) _ _ wf hf H
  rintro m env _ hf' ⟨rfl, _⟩; exact hf'

/-! ### The ι-reduction interface -/

/-- `TrEnv'`-level ι-rule lookup with the registered witness named: the reduct is
`iotaRHS` at the recursor's telescope split over a template `rhs` translating the kernel
rule's reduct, and the check is trivial (so `iota_defeq` runs with `chk := []`). -/
theorem TrEnv'.pats_iota' {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule}
    (H : TrEnv' safety C Q venv)
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hrec : C.find? recName = some (.recInfo rval))
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety) :
    ∃ (rhs : VExpr) (hc : rhs.Closed),
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.pats
        (SimplePattern.iota recName
          (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
          (rval.numParams + rule.nfields)).toPattern
        (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives rval.numMinors
          rval.numIndices rule.nfields rhs hc, .true) := by
  induction H with
  | empty => simp [SMap.find?] at hrec
  | ignore h1 h2 h3 ih =>
    rw [h3.constMap_wf.find?_insert] at hrec; split at hrec
    · injection hrec with hrec; subst hrec; exact absurd hsafe h2
    · exact ih hrec
  | thm _ _ _ _ h5 h6 ih =>
    rw [h6.constMap_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · have le := VEnv.addConst_le h5
      obtain ⟨rhs, hc, htr, hp⟩ := ih hrec; exact ⟨rhs, hc, htr.mono le, le.pats hp⟩
  | mutualDef _ hnd hfr _ hadd _ h7 ih =>
    rcases insertDefs_find? h7.constMap_wf hfr hnd hrec with hrec' | ⟨d, _, _, hd⟩
    · obtain ⟨rhs, hc, htr, hp⟩ := ih hrec'
      exact ⟨rhs, hc, htr.mono ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le),
        ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le).pats hp⟩
    · exact absurd hd (by nofun)
  | «axiom» _ _ _ h4 h5 ih =>
    rw [h5.constMap_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · have le := VEnv.addConst_le h4
      obtain ⟨rhs, hc, htr, hp⟩ := ih hrec; exact ⟨rhs, hc, htr.mono le, le.pats hp⟩
  | defn _ _ _ h4 h5 ih =>
    rw [h5.constMap_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · obtain ⟨rhs, hc, htr, hp⟩ := ih hrec
      exact ⟨rhs, hc, htr.mono ((VEnv.addConst_le h4).trans VEnv.addDefEq_le),
        ((VEnv.addConst_le h4).trans VEnv.addDefEq_le).pats hp⟩
  | «opaque» _ _ _ h4 h5 ih =>
    rw [h5.constMap_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · have le := VEnv.addConst_le h4
      obtain ⟨rhs, hc, htr, hp⟩ := ih hrec; exact ⟨rhs, hc, htr.mono le, le.pats hp⟩
  | quot _ h2 h3 ih =>
    obtain ⟨rhs, hc, htr, hp⟩ := ih (h2.pull h3.constMap_wf hrec)
    exact ⟨rhs, hc, htr.mono h2.le, h2.le.pats hp⟩
  | induct _ _ hadd h3 ih =>
    rcases hadd.rec_find hrec with hC | ⟨r, hr, hname, _, hpar, hmot, hmin, hind, hrules⟩
    · obtain ⟨rhs, hc, htr, hp⟩ := ih hC
      exact ⟨rhs, hc, htr.mono hadd.le, hadd.le.pats hp⟩
    · obtain ⟨hctor, hmem⟩ : rule.ctor = cName ∧ rule ∈ rval.rules :=
        ⟨by simpa using List.find?_some hrule, List.mem_of_find?_eq_some hrule⟩
      obtain ⟨ru, hru, hructor, hrunf, hclosed, hrutr⟩ := hrules rule hmem
      refine ⟨ru.rhs, hclosed, hrutr, ?_⟩
      rw [← hname, ← hpar, ← hmot, ← hmin, ← hind, ← hrunf, ← hctor, ← hructor]
      exact VEnv.addInduct_pat hr hru hclosed hadd.env_eq

/-- `TrEnv'`-level ι-rule lookup, stated against the constant map's own `find?`.
The recursor is registered by one `induct` step (where `VEnv.addInduct_pat` supplies
the `pat`) and carried forward by `.pats`-monotonicity. -/
theorem TrEnv'.pats_iota {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule}
    (H : TrEnv' safety C Q venv)
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hrec : C.find? recName = some (.recInfo rval))
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety) :
    ∃ r, venv.pats
      (SimplePattern.iota recName rval.getMajorIdx cName
        (rval.numParams + rule.nfields)).toPattern r := by
  obtain ⟨_, _, _, hp⟩ := H.pats_iota' hrule hrec hsafe
  exact ⟨_, hp⟩

/-- `TrEnv.pats_iota` with the registered witness named; see `TrEnv'.pats_iota'`. -/
theorem TrEnv.pats_iota' {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule}
    (H : TrEnv safety env venv)
    (hrec : env.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety) :
    ∃ (rhs : VExpr) (hc : rhs.Closed),
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.pats
        (SimplePattern.iota recName
          (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
          (rval.numParams + rule.nfields)).toPattern
        (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives rval.numMinors
          rval.numIndices rule.nfields rhs hc, .true) := by
  refine TrEnv'.pats_iota' H hrule ?_ hsafe
  have h : env.constants.find?' recName = some (.recInfo rval) := hrec
  rwa [(TrEnv'.constMap_wf H).find?'_eq_find?] at h

/-- The ι-reduction rule of a recursor rule resolvable in `env` is registered in the
translated environment's `pats`, with pattern counts mirroring `VEnv.addInduct_pat`. -/
theorem TrEnv.pats_iota {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule}
    (H : TrEnv safety env venv)
    (hrec : env.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety) :
    ∃ r, venv.pats
      (SimplePattern.iota recName rval.getMajorIdx cName
        (rval.numParams + rule.nfields)).toPattern r := by
  obtain ⟨_, _, _, hp⟩ := H.pats_iota' hrec hrule hsafe
  exact ⟨_, hp⟩

/-- **Inverse of `pats_iota'`, at the `TrEnv'` level.** Any registered ι pattern of
shape `SimplePattern.iota recName n cName k` was installed by an `induct` step; that
step's `AddInduct.rec_reg` recovers the kernel recursor `rval` (found under `recName`)
and the rule (found by `cName`) whose telescope/field counts reproduce `n` and `k`.
Non-`induct` steps leave `pats` untouched (`*_pats`) and only add fresh constants, so
the lookup is threaded up by the forward monotonicity lemmas above. -/
theorem TrEnv'.pats_iota_inv {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {recName cName : Name} {n k : Nat}
    {r : (SimplePattern.iota recName n cName k).toPattern.RHS ×
         (SimplePattern.iota recName n cName k).toPattern.Check}
    (H : TrEnv' safety C Q venv)
    (hp : venv.pats (SimplePattern.iota recName n cName k).toPattern r) :
    ∃ (rval : RecursorVal) (rule : RecursorRule),
      C.find? recName = some (.recInfo rval) ∧
      rval.rules.find? (·.ctor == cName) = some rule ∧
      n = rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices ∧
      k = rval.numParams + rule.nfields := by
  induction H with
  | empty => exact (hp : False).elim
  | ignore h1 _ Hprev ih =>
    obtain ⟨rval, rule, hrec, hru, hn, hk⟩ := ih hp
    exact ⟨rval, rule, find?_insert_mono Hprev.constMap_wf h1 hrec, hru, hn, hk⟩
  | «axiom» _ h2 _ h4 Hprev ih =>
    rw [VEnv.addConst_pats h4] at hp
    obtain ⟨rval, rule, hrec, hru, hn, hk⟩ := ih hp
    exact ⟨rval, rule, find?_insert_mono Hprev.constMap_wf h2 hrec, hru, hn, hk⟩
  | defn _ h2 _ h4 Hprev ih =>
    rw [VEnv.addDefEq_pats, VEnv.addConst_pats h4] at hp
    obtain ⟨rval, rule, hrec, hru, hn, hk⟩ := ih hp
    exact ⟨rval, rule, find?_insert_mono Hprev.constMap_wf h2 hrec, hru, hn, hk⟩
  | mutualDef _ hnd hfr _ hadd _ Hprev ih =>
    rw [VEnv.addDefEqs_pats, VEnv.addConsts_pats hadd] at hp
    obtain ⟨rval, rule, hrec, hru, hn, hk⟩ := ih hp
    exact ⟨rval, rule, insertDefs_find?_mono Hprev.constMap_wf hfr hnd hrec, hru, hn, hk⟩
  | thm _ h2 _ _ h5 Hprev ih =>
    rw [VEnv.addConst_pats h5] at hp
    obtain ⟨rval, rule, hrec, hru, hn, hk⟩ := ih hp
    exact ⟨rval, rule, find?_insert_mono Hprev.constMap_wf h2 hrec, hru, hn, hk⟩
  | «opaque» _ h2 _ h4 Hprev ih =>
    rw [VEnv.addConst_pats h4] at hp
    obtain ⟨rval, rule, hrec, hru, hn, hk⟩ := ih hp
    exact ⟨rval, rule, find?_insert_mono Hprev.constMap_wf h2 hrec, hru, hn, hk⟩
  | quot _ h2 Hprev ih =>
    rw [VEnv.addQuot_pats h2.to_addQuot] at hp
    obtain ⟨rval, rule, hrec, hru, hn, hk⟩ := ih hp
    exact ⟨rval, rule, h2.push Hprev.constMap_wf hrec, hru, hn, hk⟩
  | induct _ _ hadd Hprev ih =>
    rcases VEnv.addInduct_pats_origin hadd.env_eq hp with hold | ⟨rec, hrec, ru, hru, hform⟩
    · obtain ⟨rval, rule, hrecC, hru', hn, hk⟩ := ih hold
      exact ⟨rval, rule, hadd.find?_mono hrecC, hru', hn, hk⟩
    · obtain ⟨hrn, hm, hc, hkk⟩ := VEnv.iota_toPattern_inj hform
      subst hrn hm hc hkk
      obtain ⟨rval, hrfind, hmaj, hpar, hrules⟩ := hadd.rec_reg hrec
      obtain ⟨rule, hfind, hnf⟩ := hrules hru
      exact ⟨rval, rule, hrfind, hfind, hmaj, by rw [hpar, hnf]⟩

/-- **Inverse of `pats_iota'`.** From a registered ι pattern
`SimplePattern.iota recName n cName k`, recover the kernel recursor `rval` (resolvable
in `env` under `recName`) and its rule for `cName`, with the telescope counts pinning
`n` and `k`. Genuinely converse to `pats_iota'` (which goes recursor ⇒ pattern);
supplied by inverting the `TrEnv'` induction (`pats_iota_inv` at the `TrEnv'` level). -/
theorem TrEnv.pats_iota_inv {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {recName cName : Name} {n k : Nat}
    {r : (SimplePattern.iota recName n cName k).toPattern.RHS ×
         (SimplePattern.iota recName n cName k).toPattern.Check}
    (H : TrEnv safety env venv)
    (hp : venv.pats (SimplePattern.iota recName n cName k).toPattern r) :
    ∃ (rval : RecursorVal) (rule : RecursorRule),
      env.find? recName = some (.recInfo rval) ∧
      rval.rules.find? (·.ctor == cName) = some rule ∧
      n = rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices ∧
      k = rval.numParams + rule.nfields := by
  obtain ⟨rval, rule, hrec, hru, hn, hk⟩ := TrEnv'.pats_iota_inv H hp
  refine ⟨rval, rule, ?_, hru, hn, hk⟩
  rw [← (TrEnv'.constMap_wf H).find?'_eq_find? recName] at hrec
  exact hrec

/-- A registered ι rule, matched against a well-typed redex with its `Realizes` side
conditions discharged, gives a definitional equality between redex and reduct. Thin
wrapper over `VEnv.IsDefEq.pat`. -/
theorem TrEnv.iota_defeq {venv : VEnv} {U : Nat} {Γ : List VExpr}
    {p : Pattern} {r : p.RHS × p.Check} {e A : VExpr} {m1 m2 chk}
    (hpat : venv.pats p r) (hm : p.Matches e m1 m2)
    (hty : venv.HasType U Γ e A) (hR : r.2.Realizes m1 m2 chk)
    (hall : ∀ t ∈ chk, venv.IsDefEq U Γ t.1 t.2.1 t.2.2) :
    venv.IsDefEqU U Γ e (r.1.apply m1 m2) :=
  ⟨A, VEnv.IsDefEq.pat hpat hm hty hR hall⟩

/-- A well-typed redex matching a recursor's ι pattern is definitionally equal to the
`iotaRHS` reduct, over a template `rhs` translating the kernel rule's reduct. Composes
`pats_iota'` with `iota_defeq` at the trivial check. -/
theorem TrEnv.iota_rec {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule}
    {U : Nat} {Γ : List VExpr} {e A : VExpr} {m1 m2}
    (H : TrEnv safety env venv)
    (hrec : env.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety)
    (hm : (SimplePattern.iota recName
        (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
        (rval.numParams + rule.nfields)).toPattern.Matches e m1 m2)
    (hty : venv.HasType U Γ e A) :
    ∃ (rhs : VExpr) (hc : rhs.Closed),
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.IsDefEqU U Γ e ((SimplePattern.iotaRHS recName cName rval.numParams
        rval.numMotives rval.numMinors rval.numIndices rule.nfields rhs hc).apply m1 m2) := by
  obtain ⟨rhs, hc, htr, hp⟩ := H.pats_iota' hrec hrule hsafe
  exact ⟨rhs, hc, htr, TrEnv.iota_defeq hp hm hty (chk := []) trivial nofun⟩

/-- **Projection reduction.** If `e''` is the recursor expansion of the `i`-th
projection of a structure value `d` (`TrProj`), and `d` is definitionally equal to
a constructor spine `ctorName cus (params ++ fields)`, then `e''` is definitionally
equal to the named field `fields[i]`. This is the interface the `proj` case of
`TrExprS` soundness consumes: firing the structure's ι rule on the rewritten
constructor spine, whose reduct (η-long minor application `fun … minor fields =>
minor fields`) β-reduces through the `fieldSelector` telescope to `fields[i]`.

Proof route (see the PROJ-TODO): from `hp`, `e'' = recName us params motive
(fieldSelector fieldTys i) d` with a registered ι rule `venv.pats (iota recName
(np+1+1+0) ctorName …) r`; rewrite `d` by `hd` to the constructor spine so the ι
rule fires (`iota_defeq`/`IsDefEq.pat`), then β-reduce the structure reduct. -/
theorem TrEnv.proj_defeq {safety : DefinitionSafety} {kenv : Lean.Kernel.Environment}
    {venv : VEnv} {U : Nat} {Γ : List VExpr} {S ctorName : Name} {i np nf : Nat}
    {us cus : List VLevel} {params fields : List VExpr} {d e'' A : VExpr}
    (H : TrEnv safety kenv venv)
    (hp : TrProj venv U Γ S i d e'')
    (hd : venv.IsDefEqU U Γ d ((VExpr.const ctorName cus).mkApps (params ++ fields)))
    (hty : venv.HasType U Γ d A)
    (hlen : params.length = np) (hflen : fields.length = nf) (hi : i < nf) :
    venv.IsDefEqU U Γ e'' (fields[i]'(hflen ▸ hi)) := by
  sorry -- PROJ-TODO(soundness): structure recursor rhs is the η-long minor application; β-reduces to fields[i]
