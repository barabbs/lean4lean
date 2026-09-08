import Lean4Lean.Std.SMap
import Lean4Lean.Declaration
import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Theory.Typing.InductiveParams

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel

variable (safety : DefinitionSafety) in
inductive Aligned : ConstMap → VEnv → Prop where
  | empty : Aligned {} .empty
  | ignoreConst : Aligned C venv → C.find? n = none → ¬safety ≤ ci.safety →
    ci.name = n → Aligned (C.insert n ci) venv
  | const : Aligned C venv → C.find? n = none → TrConstant safety venv ci ci' →
    venv.addConst n ci' = some venv' → ci.name = n → Aligned (C.insert n ci) venv'
  | defeq : Aligned C venv → Aligned C (venv.addDefEq df)
  /-- Registering a pattern-reduction rule (an ι rule) changes neither the constant
  map nor the model's constants. -/
  | pat : Aligned C venv → Aligned C (venv.addPat p r)
  /-- An inductive block, inserted as a whole: the map gets the block's constants `cis`
  (fresh, with distinct names, in the order the kernel inserts them), the model the
  matching constants `l`, and each constant translates in the model environment holding
  the whole block — the types of a block's recursors mention all of its type formers and
  constructors, so a nested mutual block, which the kernel inserts type by type, cannot
  be aligned one constant at a time. -/
  | block {cis : List ConstantInfo} {l : List (Name × VConstant)} :
    Aligned C venv →
    (∀ ci ∈ cis, C.find? ci.name = none) → (cis.map (·.name)).Nodup →
    List.Forall₂ (fun ci b => TrConstant safety venv' ci b.2 ∧ ci.name = b.1) cis l →
    l.foldlM (fun (e : VEnv) b => e.addConst b.1 b.2) venv = some venv' →
    Aligned (insertConsts C cis) venv'

theorem Aligned.map_wf (H : Aligned safety C venv) : C.WF := by
  induction H with
  | empty => exact .empty
  | ignoreConst _ h1 _ _ ih
  | const _ h1 _ _ _ ih => exact ih.insert _ _ h1
  | defeq _ ih | pat _ ih => exact ih
  | block _ hfr hnd _ _ ih => exact insertConsts_wf ih hfr hnd

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
  | defeq _ ih | pat _ ih => exact ih
  | block H hfr hnd hblk hfold ih =>
    constructor
    · rintro ⟨ci, hci, hs⟩
      rcases insertConsts_find? H.map_wf hfr hnd hci with h | ⟨hmem, hn⟩
      · obtain ⟨ci', hci'⟩ := ih.1 ⟨ci, h, hs⟩
        exact ⟨ci', (VEnv.foldlM_le (fun hh => VEnv.addConst_le hh) hfold).constants hci'⟩
      · obtain ⟨b, hb, -, hbn⟩ := hblk.forall_exists_l ci hmem
        refine ⟨b.2, ?_⟩
        rw [← hn, hbn]
        exact VEnv.addConst_foldlM_find (nm := Prod.fst) (ci := Prod.snd) hfold b hb
    · rintro ⟨ci', hci'⟩
      rcases VEnv.addConst_foldlM_constants_inv (nm := Prod.fst) (ci := Prod.snd) hfold hci'
        with h | ⟨b, hb, hbn, -⟩
      · obtain ⟨ci, hci, hs⟩ := ih.2 ⟨ci', h⟩
        refine ⟨ci, insertConsts_find?_mono H.map_wf.map₂ (fun d hd e => ?_) hci, hs⟩
        have := hfr d hd; rw [e, hci] at this; cases this
      · obtain ⟨ci, hci, htr, hcn⟩ := hblk.forall_exists_r b hb
        refine ⟨ci, ?_, htr.1⟩
        rw [← hbn, ← hcn]; exact insertConsts_find?_self H.map_wf hfr hnd ci hci

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

/-- Registering the ι rules of a declaration keeps `Aligned`: every step is an `addPat`. -/
theorem Aligned.addRules {decl : VInductDecl} (h : Aligned safety C venv)
    (hP : decl.addRules venv = some venv') : Aligned safety C venv' := by
  unfold VInductDecl.addRules at hP
  refine VEnv.foldlM_inv (P := Aligned safety C) (fun r _ _ _ hA hfold => ?_) h hP
  refine VEnv.foldlM_inv (P := Aligned safety C) (fun ru _ _ _ hA' hstep => ?_) hA hfold
  unfold VEnv.addRecRule at hstep; split at hstep
  · cases hstep; exact hA'.pat
  · cases hstep

/-- Adding an inductive block keeps `Aligned`: the constant stages form one `Aligned.block`
step — the kernel inserts the block's constants in `H.order`, the model in stage order
(`VInductDecl.consts`, which `addTypesCtorsRecs` folds over), and an `addConst` fold does
not depend on its order (`VEnv.addConst_foldlM_perm`); each constant translates in the
environment holding the whole block (`H.envR`). The ι-rule stage is `Aligned.addRules`. -/
theorem Aligned.addInduct (H : AddInduct safety C₁ venv₁ decl C₂ venv₂)
    (h : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  have leT : H.envT ≤ H.envR := (VEnv.addCtors_le H.stC).trans (VEnv.addRecs_le H.stR)
  -- the block's constants, kernel side and model side, matched by kind
  have hpair : List.Forall₂ (fun ci (b : Name × VConstant) =>
      TrConstant safety H.envR ci b.2 ∧ ci.name = b.1)
      (AddInduct.consts H.ivals H.rvals) decl.consts := by
    unfold AddInduct.consts VInductDecl.consts
    refine List.Forall₂.append (List.Forall₂.append ?_ ?_) ?_
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact H.types.imp fun _ _ ht =>
        ⟨ht.tr.1.mono ((VEnv.addTypes_le H.stT).trans leT), ht.tr.2⟩
    · rw [← List.map_flatMap, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact (List.Forall₂.flatMap (fun _ _ ht => ht.ctors) H.types).imp fun _ _ hc =>
        ⟨hc.1.1.mono leT, hc.1.2⟩
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact H.recs.imp fun _ _ hr => ⟨hr.tr.1.mono (VEnv.addRecs_le H.stR), hr.tr.2⟩
  -- the same matching, in the kernel's insertion order
  obtain ⟨l', hl', hpair'⟩ := List.Forall₂.perm_left H.order_perm hpair
  have hfold : l'.foldlM (fun (e : VEnv) b => e.addConst b.1 b.2) venv₁ = some H.envR := by
    have := H.addTypesCtorsRecs
    rw [VInductDecl.addTypesCtorsRecs_eq] at this
    exact VEnv.addConst_foldlM_perm (nm := Prod.fst) (ci := Prod.snd) hl'.symm this
  rw [H.map_eq]
  exact (h.block H.order_fresh H.order_nodup hpair' hfold).addRules H.stP

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
  | induct _ h _ ih => exact ih.addInduct h

theorem TrEnv'.map_wf (H : TrEnv' safety C Q venv) : C.WF := H.aligned.map_wf

/-! ### Recursor lookup across the quotient constants

`pats_iota` (below) pulls a `recInfo` lookup back across a `quot` step: `addQuot`
registers only `quotInfo` constants. -/

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
  | pat h1 ih => let ⟨_, h1, h2⟩ := ih h; exact ⟨_, h1, h2.mono VEnv.addPat_le⟩
  | block H hfr hnd hblk hfold ih =>
    rcases insertConsts_find? H.map_wf hfr hnd h with h' | ⟨hmem, hn⟩
    · exact mono (VEnv.foldlM_le (fun hh => VEnv.addConst_le hh) hfold) (ih h')
    · obtain ⟨b, hb, htr, hbn⟩ := hblk.forall_exists_l ci hmem
      refine ⟨b.2, ?_, htr⟩
      rw [← hn, hbn]
      exact VEnv.addConst_foldlM_find (nm := Prod.fst) (ci := Prod.snd) hfold b hb

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
  | pat h1 ih => let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono VEnv.addPat_le⟩
  | block H hfr hnd hblk hfold ih =>
    rcases insertConsts_find? H.map_wf hfr hnd h with h' | ⟨hmem, hn⟩
    · rcases VEnv.addConst_foldlM_constants_inv (nm := Prod.fst) (ci := Prod.snd) hfold hs
        with hs' | ⟨b, hb, hbn, -⟩
      · obtain ⟨h1, h2⟩ := ih h' hs'
        exact ⟨h1, h2.mono (VEnv.foldlM_le (fun hh => VEnv.addConst_le hh) hfold)⟩
      · exfalso
        obtain ⟨d, hd, -, hdn⟩ := hblk.forall_exists_r b hb
        have := hfr d hd; rw [hdn, hbn, h'] at this; cases this
    · obtain ⟨b, hb, htr, hbn⟩ := hblk.forall_exists_l ci hmem
      have := VEnv.addConst_foldlM_find (nm := Prod.fst) (ci := Prod.snd) hfold b hb
      rw [← hbn, hn, hs] at this
      cases this
      exact ⟨hn, htr⟩

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
  | induct _ hadd H ih =>
    -- The registered constants carry no delta-value, so `hv` forces `name` to have
    -- been present already in `C` (`AddInduct.value_find`); then `ih` applies.
    exact (ih (hadd.value_find H.map_wf h hv)).mono hadd.le

nonrec theorem TrEnv.of_value (H : TrEnv safety env venv) (h : env.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) :=
  H.of_value (by rwa [← H.map_wf.find?'_eq_find?]) hs hv

/-! ### Forward `find?` transport across fresh insertions

A constant already resolvable stays resolvable, to the same value, across insertions of
names it does not carry (`SMap.find?_insert_of_fresh`, `SMap.insertList_find?_mono`,
`AddInduct.find?_mono` in `Basic.lean`); here for `insertDefs` and `AddQuot`. -/

theorem insertDefs_find?_mono {cis : List DefinitionVal} {C : ConstMap} {x v} (wf : C.WF)
    (hfr : ∀ d ∈ cis, C.find? d.name = none) (h : C.find? x = some v) :
    (insertDefs C cis).find? x = some v := by
  unfold insertDefs
  refine SMap.insertList_find?_mono (nm := (·.name)) (val := (.defnInfo ·)) wf.map₂
    (fun d hd hx => ?_) h
  have := hfr d hd; rw [hx, h] at this; cases this

theorem AddQuot1.find?_mono {P : ConstMap → VEnv → Prop} {Q : Prop} {name kind ci' x v}
    (H1 : ∀ m env, m.WF → m.find? x = some v → P m env → Q)
    (m env) (wf : m.WF) (h : m.find? x = some v) (H2 : AddQuot1 name kind ci' P m env) : Q := by
  let ⟨_, _, _, _, h2, _, h4⟩ := H2
  exact H1 _ _ (wf.insert _ _ h2) (SMap.find?_insert_of_fresh wf.map₂ h2 h) h4

/-- A constant resolvable before adding the quotient constants is still resolvable, to
the same value, afterwards. -/
theorem AddQuot.find?_mono {x v} (H : AddQuot C₁ C₂ env₁ env₂) (wf : C₁.WF)
    (h : C₁.find? x = some v) : C₂.find? x = some v := by
  dsimp [AddQuot] at H
  refine (AddQuot1.find?_mono <| AddQuot1.find?_mono <| AddQuot1.find?_mono <|
    AddQuot1.find?_mono ?_) _ _ wf h H
  rintro m env _ h ⟨rfl, _⟩; exact h

/-! ### Constructor lookups across the quotient constants, and pulling a model constant back -/

theorem pull_ctorInfo {m : ConstMap} {name c : Name} {q : ConstantInfo}
    {cval : ConstructorVal} (wf : m.WF) (hq : ∀ v, q ≠ .ctorInfo v)
    (h : (m.insert name q).find? c = some (.ctorInfo cval)) :
    m.find? c = some (.ctorInfo cval) := by
  rw [wf.find?_insert] at h; split at h
  · exact absurd (Option.some.inj h) (hq cval)
  · exact h

theorem AddQuot1.pull_ctor {P : ConstMap → VEnv → Prop} {name kind ci' c cval}
    (H1 : ∀ m env, m.WF → P m env → m.find? c = some (.ctorInfo cval))
    (m env) (wf : m.WF) (H2 : AddQuot1 name kind ci' P m env) :
    m.find? c = some (.ctorInfo cval) := by
  let ⟨_, _, _, _, h2, _, h4⟩ := H2
  exact pull_ctorInfo wf (fun _ => by nofun) (H1 _ _ (wf.insert _ _ h2) h4)

/-- A `ctorInfo` resolvable after adding the quotient constants was already resolvable
before. -/
theorem AddQuot.pull_ctor {c cval} (H : AddQuot C₁ C₂ env₁ env₂) (wf : C₁.WF)
    (hfind : C₂.find? c = some (.ctorInfo cval)) : C₁.find? c = some (.ctorInfo cval) := by
  dsimp [AddQuot] at H
  refine (AddQuot1.pull_ctor <| AddQuot1.pull_ctor <| AddQuot1.pull_ctor <|
    AddQuot1.pull_ctor ?_) _ _ wf H
  rintro m env hwf ⟨rfl, _⟩; exact hfind

/-- A model constant of an extension `env ≤ env'` whose name was already registered (at a
visible safety) was already the model constant of `env`: constants are never overwritten. -/
theorem Aligned.constants_pull {env env' : VEnv} (H : Aligned safety C env) (hle : env ≤ env')
    {c : Name} {ci₀ : ConstantInfo} {ci : VConstant}
    (hfind : C.find? c = some ci₀) (hs : safety ≤ ci₀.safety) (h : env'.constants c = some ci) :
    env.constants c = some ci := by
  obtain ⟨ci', h'⟩ := H.find?_iff.1 ⟨ci₀, hfind, hs⟩
  have := hle.constants h'; rw [h] at this; cases this; exact h'

/-- The Π-arity of the model type of a kernel constructor is its `numParams + numFields`
(`TrIndType.ctors`, carried through the later steps since constants are never overwritten).
The arity link between a translated constructor spine and the model's field telescope. -/
theorem TrEnv'.ctor_arity {safety : DefinitionSafety} {C : ConstMap} {Q : Bool} {venv : VEnv}
    {c : Name} {cval : ConstructorVal} {ci : VConstant}
    (H : TrEnv' safety C Q venv) (hk : C.find? c = some (.ctorInfo cval))
    (hv : venv.constants c = some ci) : ci.type.piArity = cval.numParams + cval.numFields := by
  have hs : safety ≤ (ConstantInfo.ctorInfo cval).safety := by
    obtain ⟨ci₁, h1, h2⟩ := H.aligned.find?_iff.2 ⟨ci, hv⟩
    rw [hk] at h1; cases h1; exact h2
  induction H with
  | empty => simp [SMap.find?] at hk
  | ignore h1 _ Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at hk; split at hk
    · rename_i heq; simp only [beq_iff_eq] at heq; subst heq
      obtain ⟨_, h1', -⟩ := Hprev.aligned.find?_iff.2 ⟨ci, hv⟩
      rw [h1] at h1'; cases h1'
    · exact ih hk hv
  | «axiom» _ _ _ h4 Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at hk; split at hk
    · cases hk
    · exact ih hk (Hprev.aligned.constants_pull (VEnv.addConst_le h4) hk hs hv)
  | defn _ _ _ h4 Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at hk; split at hk
    · cases hk
    · exact ih hk (Hprev.aligned.constants_pull ((VEnv.addConst_le h4).trans VEnv.addDefEq_le) hk hs hv)
  | mutualDef _ hnd hfr _ hadd _ Hprev ih =>
    rcases insertDefs_find? Hprev.map_wf hfr hnd hk with hk' | ⟨_, _, _, hd⟩
    · exact ih hk' (Hprev.aligned.constants_pull
        ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le) hk' hs hv)
    · cases hd
  | thm _ _ _ _ h5 Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at hk; split at hk
    · cases hk
    · exact ih hk (Hprev.aligned.constants_pull (VEnv.addConst_le h5) hk hs hv)
  | «opaque» _ _ _ h4 Hprev ih =>
    rw [Hprev.map_wf.find?_insert] at hk; split at hk
    · cases hk
    · exact ih hk (Hprev.aligned.constants_pull (VEnv.addConst_le h4) hk hs hv)
  | quot _ h2 Hprev ih =>
    have hk' := h2.pull_ctor Hprev.map_wf hk
    exact ih hk' (Hprev.aligned.constants_pull h2.le hk' hs hv)
  | induct _ hadd Hprev ih =>
    rcases hadd.find? Hprev.map_wf hk with hk' | ⟨hmem, hname⟩
    · exact ih hk' (Hprev.aligned.constants_pull hadd.le hk' hs hv)
    · rcases AddInduct.mem_consts.1 hmem with ⟨_, _, h'⟩ | ⟨iv, hiv, _, hcv, h'⟩ | ⟨_, _, h'⟩ <;>
        cases h'
      obtain ⟨t, ht, htr⟩ := hadd.types.forall_exists_l iv hiv
      obtain ⟨c', hc', hctr, harity⟩ := htr.ctors.forall_exists_l _ hcv
      have hcn : c'.name = c := hctr.2.symm.trans hname
      have hfind := VEnv.addCtors_find hadd.stC t ht c' hc'
      have := ((VEnv.addRecs_le hadd.stR).trans (VEnv.addRules_le hadd.stP)).constants hfind
      rw [hcn, hv] at this; cases this
      exact harity.symm

/-- `TrEnv'.ctor_arity` against the kernel environment. -/
theorem TrEnv.ctor_arity {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {c : Name} {cval : ConstructorVal} {ci : VConstant}
    (H : TrEnv safety env venv) (hk : env.find? c = some (.ctorInfo cval))
    (hv : venv.constants c = some ci) : ci.type.piArity = cval.numParams + cval.numFields := by
  have h : env.constants.find?' c = some (.ctorInfo cval) := hk
  rw [(TrEnv'.map_wf H).find?'_eq_find?] at h
  exact TrEnv'.ctor_arity H h hv

/-! ### The ι-reduction interface -/

/-- `TrEnv'`-level ι-rule lookup with the registered witness named: the reduct is
`iotaRHS` at the recursor's telescope split and the constructor's parameter count
(`cval.numParams`, read off the constructor's own `ctorInfo`), over a template `rhs`
translating the kernel rule's reduct; the check is trivial (so `iota_defeq` runs with
`chk := []`). -/
theorem TrEnv'.pats_iota' {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule}
    (H : TrEnv' safety C Q venv)
    (hrec : C.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety) :
    ∃ (cval : ConstructorVal) (rhs : VExpr) (hc : rhs.Closed),
      C.find? cName = some (.ctorInfo cval) ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.pats
        (SimplePattern.iota recName
          (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
          (cval.numParams + rule.nfields)).toPattern
        (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives rval.numMinors
          rval.numIndices cval.numParams rule.nfields rhs hc, .true) := by
  induction H with
  | empty => simp [SMap.find?] at hrec
  | ignore h1 h2 h3 ih =>
    rw [h3.map_wf.find?_insert] at hrec; split at hrec
    · injection hrec with hrec; subst hrec; exact absurd hsafe h2
    · obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h3.map_wf.map₂ h1 hct, htr, hp⟩
  | thm _ h2 _ _ h5 h6 ih =>
    rw [h6.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · have le := VEnv.addConst_le h5
      obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h6.map_wf.map₂ h2 hct,
        htr.mono le, le.pats hp⟩
  | mutualDef _ hnd hfr _ hadd _ h7 ih =>
    rcases insertDefs_find? h7.map_wf hfr hnd hrec with hrec' | ⟨d, _, _, hd⟩
    · obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec'
      exact ⟨cval, rhs, hc, insertDefs_find?_mono h7.map_wf hfr hct,
        htr.mono ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le),
        ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le).pats hp⟩
    · exact absurd hd (by nofun)
  | «axiom» _ h2 _ h4 h5 ih =>
    rw [h5.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · have le := VEnv.addConst_le h4
      obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h5.map_wf.map₂ h2 hct,
        htr.mono le, le.pats hp⟩
  | defn _ h2 _ h4 h5 ih =>
    rw [h5.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h5.map_wf.map₂ h2 hct,
        htr.mono ((VEnv.addConst_le h4).trans VEnv.addDefEq_le),
        ((VEnv.addConst_le h4).trans VEnv.addDefEq_le).pats hp⟩
  | «opaque» _ h2 _ h4 h5 ih =>
    rw [h5.map_wf.find?_insert] at hrec; split at hrec
    · exact absurd hrec (by nofun)
    · have le := VEnv.addConst_le h4
      obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hrec
      exact ⟨cval, rhs, hc, SMap.find?_insert_of_fresh h5.map_wf.map₂ h2 hct,
        htr.mono le, le.pats hp⟩
  | quot _ h2 h3 ih =>
    obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih (h2.pull h3.map_wf hrec)
    exact ⟨cval, rhs, hc, h2.find?_mono h3.map_wf hct, htr.mono h2.le, h2.le.pats hp⟩
  | induct _ hadd h3 ih =>
    rcases hadd.rec_find h3.map_wf hrec with
      hC | ⟨r, hr, hname, _, hpar, hmot, hmin, hind, hrules⟩
    · obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := ih hC
      exact ⟨cval, rhs, hc, hadd.find?_mono h3.map_wf hct, htr.mono hadd.le,
        hadd.le.pats hp⟩
    · obtain ⟨hctor, hmem⟩ : rule.ctor = cName ∧ rule ∈ rval.rules :=
        ⟨by simpa using List.find?_some hrule, List.mem_of_find?_eq_some hrule⟩
      obtain ⟨ru, hru, hructor, hrunf, ⟨cval, hcfind, hcnp⟩, hclosed, hrutr⟩ := hrules rule hmem
      refine ⟨cval, ru.rhs, hclosed, by rw [← hctor]; exact hcfind, hrutr, ?_⟩
      rw [← hname, ← hpar, ← hmot, ← hmin, ← hind, ← hrunf, ← hctor, ← hructor, ← hcnp]
      exact VEnv.addInduct_pat hr hru hclosed hadd.env_eq

/-- `TrEnv'.pats_iota'` against the environment's own `find?`: the ι rule of a recursor
rule resolvable in `env` is registered in the translated environment's `pats`. -/
theorem TrEnv.pats_iota' {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule}
    (H : TrEnv safety env venv)
    (hrec : env.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety) :
    ∃ (cval : ConstructorVal) (rhs : VExpr) (hc : rhs.Closed),
      env.find? cName = some (.ctorInfo cval) ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.pats
        (SimplePattern.iota recName
          (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
          (cval.numParams + rule.nfields)).toPattern
        (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives rval.numMinors
          rval.numIndices cval.numParams rule.nfields rhs hc, .true) := by
  have h : env.constants.find?' recName = some (.recInfo rval) := hrec
  rw [(TrEnv'.map_wf H).find?'_eq_find?] at h
  obtain ⟨cval, rhs, hc, hct, htr, hp⟩ := TrEnv'.pats_iota' H h hrule hsafe
  refine ⟨cval, rhs, hc, ?_, htr, hp⟩
  show env.constants.find?' cName = _
  rw [(TrEnv'.map_wf H).find?'_eq_find?]; exact hct

/-- Inverse of `pats_iota'`, at the `TrEnv'` level, with the model-side shape of the rule:
every registered ι pattern `SimplePattern.iota recName M cName N` comes from a kernel
recursor `rval` (resolvable in `C` under `recName`) and its rule for `cName` (found by
constructor, uniquely by `VInductDecl.WF.rules_nodup`), whose constructor `cval` is
resolvable in `C`; `M` and `N` are the kernel telescope split and
`cval.numParams + rule.nfields`, and the registered entry is `iotaRHS` at those counts over
a translation of the kernel reduct, with the trivial check (the reduct component is stated
with `HEq` because its type mentions `M` and `N`). On the model side, the recursor is a
registered constant whose type has `RecShape` at the kernel split
(`VInductDecl.WF.rec_shape` through `TrRecursor`), and the reduct has `RuleShape` at the
rule's minor `j` — a minor `MinorFor cName` with `rule.nfields` binders followed by exactly
as many as the reduct applies it to beyond the fields (`VInductDecl.WF.rule_shape`). -/
theorem TrEnv'.pats_iota_inv_shape {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {recName cName : Name} {M N : Nat}
    {r : (SimplePattern.iota recName M cName N).toPattern.RHS ×
      (SimplePattern.iota recName M cName N).toPattern.Check}
    (H : TrEnv' safety C Q venv)
    (hp : venv.pats (SimplePattern.iota recName M cName N).toPattern r) :
    ∃ (rval : RecursorVal) (rule : RecursorRule) (cval : ConstructorVal) (rhs : VExpr)
      (hc : rhs.Closed) (rci : VConstant),
      C.find? recName = some (.recInfo rval) ∧
      rval.rules.find? (·.ctor == cName) = some rule ∧
      C.find? cName = some (.ctorInfo cval) ∧
      M = rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices ∧
      N = cval.numParams + rule.nfields ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      HEq r.1 (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives
        rval.numMinors rval.numIndices cval.numParams rule.nfields rhs hc) ∧
      r.2 = .true ∧
      venv.constants recName = some rci ∧
      rci.type.RecShape rval.numParams rval.numMotives rval.numMinors rval.numIndices ∧
      ∃ j < rval.numMinors, ∃ A,
        rci.type.piBinders[rval.numParams + rval.numMotives + j]? = some A ∧ A.MinorFor cName ∧
        rule.nfields ≤ A.piArity ∧
        rhs.RuleShape rval.numParams rval.numMotives rval.numMinors rule.nfields
          (A.piArity - rule.nfields) j := by
  induction H with
  | empty => exact (hp : False).elim
  | ignore h1 _ Hprev ih =>
    obtain ⟨rval, rule, cval, rhs, hc, rci, hrec, hru, hct, hM, hN, htr, hh1, hh2, hrci, hrs, hj⟩ :=
      ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, rci, SMap.find?_insert_of_fresh wf h1 hrec, hru,
      SMap.find?_insert_of_fresh wf h1 hct, hM, hN, htr, hh1, hh2, hrci, hrs, hj⟩
  | «axiom» _ h2 _ h4 Hprev ih =>
    rw [VEnv.addConst_pats h4] at hp
    obtain ⟨rval, rule, cval, rhs, hc, rci, hrec, hru, hct, hM, hN, htr, hh1, hh2, hrci, hrs, hj⟩ :=
      ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, rci, SMap.find?_insert_of_fresh wf h2 hrec, hru,
      SMap.find?_insert_of_fresh wf h2 hct, hM, hN, htr.mono (VEnv.addConst_le h4), hh1, hh2,
      (VEnv.addConst_le h4).constants hrci, hrs, hj⟩
  | defn _ h2 _ h4 Hprev ih =>
    rw [VEnv.addDefEq_pats, VEnv.addConst_pats h4] at hp
    obtain ⟨rval, rule, cval, rhs, hc, rci, hrec, hru, hct, hM, hN, htr, hh1, hh2, hrci, hrs, hj⟩ :=
      ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, rci, SMap.find?_insert_of_fresh wf h2 hrec, hru,
      SMap.find?_insert_of_fresh wf h2 hct, hM, hN,
      htr.mono ((VEnv.addConst_le h4).trans VEnv.addDefEq_le), hh1, hh2,
      ((VEnv.addConst_le h4).trans VEnv.addDefEq_le).constants hrci, hrs, hj⟩
  | mutualDef _ hnd hfr _ hadd _ Hprev ih =>
    rw [VEnv.addDefEqs_pats, VEnv.addConsts_pats hadd] at hp
    obtain ⟨rval, rule, cval, rhs, hc, rci, hrec, hru, hct, hM, hN, htr, hh1, hh2, hrci, hrs, hj⟩ :=
      ih hp
    have wf := Hprev.map_wf
    exact ⟨rval, rule, cval, rhs, hc, rci, insertDefs_find?_mono wf hfr hrec, hru,
      insertDefs_find?_mono wf hfr hct, hM, hN,
      htr.mono ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le), hh1, hh2,
      ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le).constants hrci, hrs, hj⟩
  | thm _ h2 _ _ h5 Hprev ih =>
    rw [VEnv.addConst_pats h5] at hp
    obtain ⟨rval, rule, cval, rhs, hc, rci, hrec, hru, hct, hM, hN, htr, hh1, hh2, hrci, hrs, hj⟩ :=
      ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, rci, SMap.find?_insert_of_fresh wf h2 hrec, hru,
      SMap.find?_insert_of_fresh wf h2 hct, hM, hN, htr.mono (VEnv.addConst_le h5), hh1, hh2,
      (VEnv.addConst_le h5).constants hrci, hrs, hj⟩
  | «opaque» _ h2 _ h4 Hprev ih =>
    rw [VEnv.addConst_pats h4] at hp
    obtain ⟨rval, rule, cval, rhs, hc, rci, hrec, hru, hct, hM, hN, htr, hh1, hh2, hrci, hrs, hj⟩ :=
      ih hp
    have wf := Hprev.map_wf.map₂
    exact ⟨rval, rule, cval, rhs, hc, rci, SMap.find?_insert_of_fresh wf h2 hrec, hru,
      SMap.find?_insert_of_fresh wf h2 hct, hM, hN, htr.mono (VEnv.addConst_le h4), hh1, hh2,
      (VEnv.addConst_le h4).constants hrci, hrs, hj⟩
  | quot _ h2 Hprev ih =>
    rw [VEnv.addQuot_pats h2.to_addQuot] at hp
    obtain ⟨rval, rule, cval, rhs, hc, rci, hrec, hru, hct, hM, hN, htr, hh1, hh2, hrci, hrs, hj⟩ :=
      ih hp
    have wf := Hprev.map_wf
    exact ⟨rval, rule, cval, rhs, hc, rci, h2.find?_mono wf hrec, hru, h2.find?_mono wf hct, hM, hN,
      htr.mono h2.le, hh1, hh2, h2.le.constants hrci, hrs, hj⟩
  | induct hwf hadd Hprev ih =>
    have wf := Hprev.map_wf
    rcases VEnv.addInduct_pats_origin' hadd.env_eq hp with
      hold | ⟨rec, hrec, ru, hru, hc, e, he⟩
    · obtain ⟨rval, rule, cval, rhs, hc, rci, hrec, hru, hct, hM, hN, htr, hh1, hh2, hrci, hrs, hj⟩ :=
        ih hold
      exact ⟨rval, rule, cval, rhs, hc, rci, hadd.find?_mono wf hrec, hru, hadd.find?_mono wf hct,
        hM, hN, htr.mono hadd.le, hh1, hh2, hadd.le.constants hrci, hrs, hj⟩
    · obtain ⟨hrn, hm, hcn, hkk⟩ := VEnv.iota_toPattern_inj e
      subst hrn hm hcn hkk
      cases e
      obtain ⟨rval, hrfind, hmaj, hpar, hmot, hmin, hind, hrules⟩ := hadd.rec_reg wf hwf hrec
      obtain ⟨rule, hfind, hnf, ⟨cval, hcfind, hcnp⟩, htr⟩ := hrules ru hru
      have hrs := hwf.rec_shape rec hrec
      obtain ⟨j, hj, A, hA, hAm, hAle, hru_s⟩ := hwf.rule_shape rec hrec ru hru
      refine ⟨rval, rule, cval, ru.rhs, hc, rec.toVConstVal.toVConstant, hrfind, hfind, hcfind, ?_,
        by rw [← hcnp, ← hnf], htr, ?_, ?_, VEnv.addInduct_rec_find hadd.env_eq hrec, ?_, ?_⟩
      · rw [hmaj]; rfl
      · rw [← hpar, ← hmot, ← hmin, ← hind, ← hcnp, ← hnf]
        exact heq_of_eq (congrArg Prod.fst he)
      · exact congrArg Prod.snd he
      · rw [← hpar, ← hmot, ← hmin, ← hind]; exact hrs
      · refine ⟨j, by rw [← hmin]; exact hj, A, ?_, hAm, by rw [← hnf]; exact hAle, ?_⟩
        · rw [← hpar, ← hmot]; exact hA
        · rw [← hpar, ← hmot, ← hmin, ← hnf]; exact hru_s

/-- Inverse of `pats_iota'`, at the `TrEnv'` level: the kernel-side half of
`TrEnv'.pats_iota_inv_shape`. -/
theorem TrEnv'.pats_iota_inv' {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} {recName cName : Name} {M N : Nat}
    {r : (SimplePattern.iota recName M cName N).toPattern.RHS ×
      (SimplePattern.iota recName M cName N).toPattern.Check}
    (H : TrEnv' safety C Q venv)
    (hp : venv.pats (SimplePattern.iota recName M cName N).toPattern r) :
    ∃ (rval : RecursorVal) (rule : RecursorRule) (cval : ConstructorVal) (rhs : VExpr)
      (hc : rhs.Closed),
      C.find? recName = some (.recInfo rval) ∧
      rval.rules.find? (·.ctor == cName) = some rule ∧
      C.find? cName = some (.ctorInfo cval) ∧
      M = rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices ∧
      N = cval.numParams + rule.nfields ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      HEq r.1 (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives
        rval.numMinors rval.numIndices cval.numParams rule.nfields rhs hc) ∧
      r.2 = .true := by
  obtain ⟨rval, rule, cval, rhs, hc, -, hrec, hru, hct, hM, hN, htr, hh1, hh2, -, -, -⟩ :=
    H.pats_iota_inv_shape hp
  exact ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩

/-- `TrEnv'.pats_iota_inv_shape` against the kernel environment. -/
theorem TrEnv.pats_iota_inv_shape {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {recName cName : Name} {M N : Nat}
    {r : (SimplePattern.iota recName M cName N).toPattern.RHS ×
      (SimplePattern.iota recName M cName N).toPattern.Check}
    (H : TrEnv safety env venv)
    (hp : venv.pats (SimplePattern.iota recName M cName N).toPattern r) :
    ∃ (rval : RecursorVal) (rule : RecursorRule) (cval : ConstructorVal) (rhs : VExpr)
      (hc : rhs.Closed) (rci : VConstant),
      env.find? recName = some (.recInfo rval) ∧
      rval.rules.find? (·.ctor == cName) = some rule ∧
      env.find? cName = some (.ctorInfo cval) ∧
      M = rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices ∧
      N = cval.numParams + rule.nfields ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      HEq r.1 (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives
        rval.numMinors rval.numIndices cval.numParams rule.nfields rhs hc) ∧
      r.2 = .true ∧
      venv.constants recName = some rci ∧
      rci.type.RecShape rval.numParams rval.numMotives rval.numMinors rval.numIndices ∧
      ∃ j < rval.numMinors, ∃ A,
        rci.type.piBinders[rval.numParams + rval.numMotives + j]? = some A ∧ A.MinorFor cName ∧
        rule.nfields ≤ A.piArity ∧
        rhs.RuleShape rval.numParams rval.numMotives rval.numMinors rule.nfields
          (A.piArity - rule.nfields) j := by
  obtain ⟨rval, rule, cval, rhs, hc, rci, hrec, hru, hct, hM, hN, htr, hh1, hh2, hrci, hrs, hj⟩ :=
    TrEnv'.pats_iota_inv_shape H hp
  have wf := TrEnv'.map_wf H
  refine ⟨rval, rule, cval, rhs, hc, rci, ?_, hru, ?_, hM, hN, htr, hh1, hh2, hrci, hrs, hj⟩
  · show env.constants.find?' recName = _; rw [wf.find?'_eq_find?]; exact hrec
  · show env.constants.find?' cName = _; rw [wf.find?'_eq_find?]; exact hct

/-- Inverse of `pats_iota'`; see `TrEnv'.pats_iota_inv'`. From a registered ι pattern,
recover the kernel recursor and its rule for the constructor, the constructor itself, the
full kernel telescope split behind `M`, the split of `N` into the constructor's parameter
and field counts, and the registered reduct. -/
theorem TrEnv.pats_iota_inv' {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {recName cName : Name} {M N : Nat}
    {r : (SimplePattern.iota recName M cName N).toPattern.RHS ×
      (SimplePattern.iota recName M cName N).toPattern.Check}
    (H : TrEnv safety env venv)
    (hp : venv.pats (SimplePattern.iota recName M cName N).toPattern r) :
    ∃ (rval : RecursorVal) (rule : RecursorRule) (cval : ConstructorVal) (rhs : VExpr)
      (hc : rhs.Closed),
      env.find? recName = some (.recInfo rval) ∧
      rval.rules.find? (·.ctor == cName) = some rule ∧
      env.find? cName = some (.ctorInfo cval) ∧
      M = rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices ∧
      N = cval.numParams + rule.nfields ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      HEq r.1 (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives
        rval.numMinors rval.numIndices cval.numParams rule.nfields rhs hc) ∧
      r.2 = .true := by
  obtain ⟨rval, rule, cval, rhs, hc, hrec, hru, hct, hM, hN, htr, hh1, hh2⟩ :=
    TrEnv'.pats_iota_inv' H hp
  have wf := TrEnv'.map_wf H
  refine ⟨rval, rule, cval, rhs, hc, ?_, hru, ?_, hM, hN, htr, hh1, hh2⟩
  · show env.constants.find?' recName = _; rw [wf.find?'_eq_find?]; exact hrec
  · show env.constants.find?' cName = _; rw [wf.find?'_eq_find?]; exact hct

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

/-- The ι reduction step of a translated environment, as `reduceRecursor.WF` needs it: a
well-typed redex matching a recursor's ι pattern (over the constructor `cval` resolved in
`env`) is definitionally equal to the `iotaRHS` reduct, over a template `rhs` translating
the kernel rule's reduct. Composes `pats_iota'` with `iota_defeq` at the trivial check. -/
theorem TrEnv.iota_rec {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule} {cval : ConstructorVal}
    {U : Nat} {Γ : List VExpr} {e A : VExpr} {m1 m2}
    (H : TrEnv safety env venv)
    (hrec : env.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety)
    (hctor : env.find? cName = some (.ctorInfo cval))
    (hm : (SimplePattern.iota recName
        (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
        (cval.numParams + rule.nfields)).toPattern.Matches e m1 m2)
    (hty : venv.HasType U Γ e A) :
    ∃ (rhs : VExpr) (hc : rhs.Closed),
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.IsDefEqU U Γ e ((SimplePattern.iotaRHS recName cName rval.numParams
        rval.numMotives rval.numMinors rval.numIndices cval.numParams rule.nfields rhs hc).apply
          m1 m2) := by
  obtain ⟨cval', rhs, hc, hct, htr, hp⟩ := H.pats_iota' hrec hrule hsafe
  rw [hctor] at hct; cases hct
  exact ⟨rhs, hc, htr, TrEnv.iota_defeq hp hm hty (chk := []) trivial nofun⟩

/-! ### β-reduction of a saturated λ-telescope

`(λ x₁:A₁ … x_m:A_m. b) a₁ … a_m ≡ b[x := a]`, for a well-typed application spine. Each step
inverts the application and the abstraction (`HasType.app_inv`, `HasType.lam_inv`) to type
the redex for `IsDefEq.beta`, and unique typing (`IsDefEqU.of_l`) carries the definitional
equality of the heads along the spine. The substitution is `VExpr.instFields`, outermost
argument first. -/

/-- The head of a well-typed application spine is well-typed. -/
theorem VEnv.HasType.mkApps_inv_head {env : VEnv} {U : Nat} {Γ : List VExpr}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {as : List VExpr} {f V : VExpr}, env.HasType U Γ (f.mkApps as) V → ∃ W, env.HasType U Γ f W
  | [], _, V, H => ⟨V, H⟩
  | a :: as, f, _, H => by
    rw [VExpr.mkApps_cons] at H
    obtain ⟨_, H'⟩ := mkApps_inv_head henv hΓ (as := as) (f := f.app a) H
    obtain ⟨_, _, hf, -⟩ := H'.app_inv henv hΓ
    exact ⟨_, hf⟩

/-- β at the head of a well-typed application. -/
theorem VEnv.IsDefEqU.beta_app {env : VEnv} {U : Nat} {Γ : List VExpr} {A b a V : VExpr}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasType U Γ ((VExpr.lam A b).app a) V) :
    env.IsDefEqU U Γ ((VExpr.lam A b).app a) (b.inst a) := by
  obtain ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ
  obtain ⟨⟨_, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨_, Ae⟩, -⟩ := (hf.uniqU henv hΓ (hA.lam hb)).forallE_inv henv hΓ
  exact ⟨_, hb.beta (Ae.defeq ha)⟩

/-- A definitional equality of heads extends along a well-typed application spine. -/
theorem VEnv.IsDefEqU.mkApps_congr {env : VEnv} {U : Nat} {Γ : List VExpr}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {as : List VExpr} {f f' V : VExpr}, env.IsDefEqU U Γ f f' →
      env.HasType U Γ (f.mkApps as) V → env.IsDefEqU U Γ (f.mkApps as) (f'.mkApps as)
  | [], _, _, _, hf, _ => hf
  | a :: as, f, f', _, hf, H => by
    rw [VExpr.mkApps_cons] at H ⊢
    obtain ⟨_, H'⟩ := H.mkApps_inv_head henv hΓ
    obtain ⟨_, _, hfA, ha⟩ := H'.app_inv henv hΓ
    have hfa : env.IsDefEqU U Γ (f.app a) (f'.app a) := ⟨_, (hf.of_l henv hΓ hfA).appDF ha⟩
    exact mkApps_congr henv hΓ (as := as) hfa H

/-- β-reduction of a λ-telescope saturated by a well-typed spine of exactly its arity:
`(λ x₁:A₁ … x_m:A_m. b) a₁ … a_m ≡ instFields b [a₁, …, a_m]`. -/
theorem VEnv.IsDefEqU.betaN {env : VEnv} {U : Nat} {Γ : List VExpr}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {As as : List VExpr} {b V : VExpr}, as.length = As.length →
      env.HasType U Γ ((As.foldr VExpr.lam b).mkApps as) V →
      env.IsDefEqU U Γ ((As.foldr VExpr.lam b).mkApps as) (VExpr.instFields b as)
  | [], [], _, V, _, H => ⟨V, H⟩
  | _ :: As, a :: as, b, _, hlen, H => by
    have hl : as.length = As.length := by simpa using hlen
    simp only [List.foldr_cons, VExpr.mkApps_cons] at H ⊢
    obtain ⟨_, H'⟩ := H.mkApps_inv_head henv hΓ
    have h2 := IsDefEqU.mkApps_congr henv hΓ (IsDefEqU.beta_app henv hΓ H') H
    rw [VExpr.foldr_lam_inst_aux] at h2
    simp only [Nat.zero_add] at h2
    obtain ⟨_, H2⟩ := h2
    have h3 := betaN henv hΓ (by simpa using hl) H2.hasType.2
    rw [VExpr.instFields_cons, hl]
    exact IsDefEqU.trans henv hΓ ⟨_, H2⟩ h3
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => nomatch h

/-- **Projection reduction.** The recursor expansion `e''` of the `i`-th projection of a
structure value `d` (`TrProjCtor`, with the constructor `ctorName` named) reduces, when `d`
is definitionally a saturated spine `ctorName cus (params ++ fields)` of the kernel's
constructor `cval`, to the field `fields[i]`.

The kernel side supplies what the model's `VEnv` cannot express: the constructor's arity
(`hlen`/`hflen`, against `cval` — `TrEnv.ctor_arity` ties it to the model telescope), and
the segmentation of `S.rec`'s telescope (`hnp`/`hnm`/`hnmin`/`hnind`: the recursor of a
structure with `cval.numParams` parameters, one motive, one minor, no indices — the
`np+1+1+0` key of `TrProjCtor` retains only their sum, and a `VEnv` cannot tell a parameter
binder from a motive binder). This is the interface the `proj` case of `TrExprS` soundness
consumes.

Proof: `d ≡ spine` at the structure type (unique typing), so `P_i d ≡ P_i spine`; the
registered ι rule of `S.rec` on `ctorName` (`pats_iota_inv_shape`) fires on `P_i spine`
(`IsDefEq.pat`, trivial check); its reduct is the rule template — by `rule_shape` and the
minor's arity pin, `λ params motive minor fields, minor fields` with no recursive arguments —
applied to the redex's arguments, which β-reduces (`IsDefEqU.betaN`) to
`fieldSelector fieldTys i fields`, and once more to `fields[i]`.

No `sorry` of its own: the `sorryAx` in its `#print axioms` is inherited only from the
pre-existing unique-typing / Π-injectivity sorries (`Injectivity.lean`'s `IsDefEqU.sort_inv`,
`IsDefEqU.forallE_inv_stratified`; `UniqueTyping.lean`) and from `VEnv.WF.patsStrong`. -/
theorem TrEnv.proj_defeq {safety : DefinitionSafety} {kenv : Lean.Kernel.Environment}
    {venv : VEnv} {U : Nat} {Γ : List VExpr} {S ctorName : Name} {i : Nat}
    {rval : RecursorVal} {cval : ConstructorVal}
    {usS : List VLevel} {uss : Nat → List VLevel} {params' : List VExpr} {np : Nat}
    {fieldTys : List VExpr}
    {cus : List VLevel} {params fields : List VExpr} {d e'' : VExpr}
    (H : TrEnv safety kenv venv) (hΓ : OnCtx Γ (venv.IsType U))
    (hp : TrProjCtor venv U Γ S i d e'' ctorName usS uss params' np fieldTys)
    (hrec : kenv.find? (mkRecName S) = some (.recInfo rval))
    (hctor : kenv.find? ctorName = some (.ctorInfo cval))
    (hnp : rval.numParams = cval.numParams) (hnm : rval.numMotives = 1)
    (hnmin : rval.numMinors = 1) (hnind : rval.numIndices = 0)
    (hd : venv.IsDefEqU U Γ d ((VExpr.const ctorName cus).mkApps (params ++ fields)))
    (hlen : params.length = cval.numParams) (hflen : fields.length = cval.numFields)
    (hi : i < cval.numFields) :
    venv.IsDefEqU U Γ e'' (fields[i]'(hflen ▸ hi)) := by
  have henv : venv.WF := H.wf
  obtain ⟨ci, hci, hch, cty, hcty, hF⟩ := hp.ctor
  obtain ⟨rci, hrci, harity⟩ := hp.minor_arity
  have hi' := hp.field_lt
  have hnp' := hp.params_length
  have hE := hp.major_ty
  have hPF := hp.fn_ty
  obtain rfl := hp.eq
  -- (A) the constructor's arity: the spine `params ++ fields` is saturated
  have hnf : np + fieldTys.length = params.length + fields.length := by
    have := VExpr.instPis_piArity _ _ (hch.instL usS) hcty
    rw [VExpr.piArity_instL, H.ctor_arity hctor hci] at this
    rw [hF, VExpr.piBinders_length]; omega
  -- (B) the registered rule: the kernel recursor and its rule, with the model-side shape
  obtain ⟨r, hpat⟩ := hp.pat
  revert r hpat
  generalize hM : np + 1 + 1 + 0 = M
  generalize hN : np + fieldTys.length = N
  intro r hpat
  obtain ⟨rval', rule, cval', rhs, hc, rci', hrec', hrule, hctor', rfl, rfl, -, hR, hchk, hrci',
    -, j, hj, A, hA, -, hAle, hla, recArgs, hrl, hlb⟩ := H.pats_iota_inv_shape hpat
  rw [hrec] at hrec'; cases hrec'
  rw [hctor] at hctor'; cases hctor'
  rw [hrci] at hrci'; cases hrci'
  obtain ⟨R, chk⟩ := r
  cases eq_of_heq hR; cases hchk
  have hnpeq : rval.numParams = np := by omega
  have hnfeq : rule.nfields = fieldTys.length := by omega
  have hfl : fields.length = fieldTys.length := by omega
  have hplen : params.length = np := by omega
  -- (C) the minor: exactly the fields as binders, so the reduct has no recursive arguments
  have hj0 : j = 0 := by omega
  subst hj0
  rw [show rval.numParams + rval.numMotives + 0 = np + 1 by omega] at hA
  rw [VExpr.binderArity?, hA, Option.map_some] at harity
  have hA' : A.piArity = fieldTys.length := Option.some.inj harity
  obtain rfl : recArgs = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [List.append_nil, hnfeq, show fieldTys.length + (rval.numMinors - 1 - 0) = fieldTys.length by
    omega] at hlb
  -- (D) `P_i d ≡ P_i spine`, then ι on `P_i spine`
  have hde := hd.of_l henv hΓ hE
  have h1 : venv.IsDefEqU U Γ (.app (VExpr.projFn S usS uss params' fieldTys i) d)
      (.app (VExpr.projFn S usS uss params' fieldTys i) ((VExpr.const ctorName cus).mkApps
        (params ++ fields))) := ⟨_, hPF.appDF hde⟩
  have hredex := hPF.app hde.hasType.2
  obtain ⟨g1, hm1, hg1⟩ := Pattern.matches_varN_const (c := mkRecName S) (ls := uss i)
    (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices)
    (params' ++ [.lam ((VExpr.const S usS).mkApps params')
      (VExpr.projMotiveBody S usS uss params' fieldTys i), VExpr.fieldSelector fieldTys i])
    (by simp; omega)
  obtain ⟨g2, hm2, hg2⟩ := Pattern.matches_varN_const (c := ctorName) (ls := cus)
    (cval.numParams + rule.nfields) (params ++ fields) (by simp; omega)
  have hm : (SimplePattern.iota (mkRecName S)
      (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) ctorName
      (cval.numParams + rule.nfields)).toPattern.Matches
      (.app (VExpr.projFn S usS uss params' fieldTys i)
        ((VExpr.const ctorName cus).mkApps (params ++ fields))) (uss i) (Sum.elim g1 g2) :=
    .app hm1 hm2
  have hι := VEnv.IsDefEq.pat hpat hm hredex (chk := []) trivial nofun
  replace hι : venv.IsDefEq U Γ (.app (VExpr.projFn S usS uss params' fieldTys i)
      ((VExpr.const ctorName cus).mkApps (params ++ fields)))
      (Pattern.RHS.apply (p := (SimplePattern.iota (mkRecName S)
          (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) ctorName
          (cval.numParams + rule.nfields)).toPattern) (uss i) (Sum.elim g1 g2)
        (SimplePattern.iotaRHS' (mkRecName S) ctorName
          (rval.numParams + rval.numMotives + rval.numMinors) rval.numIndices cval.numParams
          rule.nfields rhs hc))
      ((VExpr.projMotiveBody S usS uss params' fieldTys i).inst
        ((VExpr.const ctorName cus).mkApps (params ++ fields))) := hι
  rw [SimplePattern.iotaRHS'_apply _ _ _ _ _ _ _ _ _ (Sum.elim g1 g2)
    (by simp; omega) (by simp; omega) hg1 hg2,
    List.take_of_length_le (by simp; omega), show cval.numParams = params.length from hlen.symm,
    List.drop_left] at hι
  -- (E) β through the template, then through `fieldSelector`
  have hβ1 := VEnv.IsDefEqU.betaN henv hΓ (As := rhs.lamBinders.map (VExpr.instL (uss i)))
    (as := params' ++ [.lam ((VExpr.const S usS).mkApps params')
      (VExpr.projMotiveBody S usS uss params' fieldTys i), VExpr.fieldSelector fieldTys i] ++ fields)
    (b := rhs.lamBody.instL (uss i)) (by simp [hla]; omega)
    (by rw [← VExpr.foldr_lam_instL, VExpr.foldr_lam_lamBinders]; exact hι.hasType.2)
  rw [← VExpr.foldr_lam_instL, VExpr.foldr_lam_lamBinders] at hβ1
  rw [hlb, VExpr.mkApps_instL, VExpr.instL,
    show (VExpr.bvarsDesc 0 fieldTys.length).map (VExpr.instL (uss i)) =
      VExpr.bvarsDesc 0 fieldTys.length by simp [VExpr.bvarsDesc, VExpr.instL],
    ← hfl] at hβ1
  have e : VExpr.instFields ((VExpr.bvar fields.length).mkApps (VExpr.bvarsDesc 0 fields.length))
      (params' ++ [VExpr.lam ((VExpr.const S usS).mkApps params')
        (VExpr.projMotiveBody S usS uss params' fieldTys i), VExpr.fieldSelector fieldTys i] ++
        fields) = (VExpr.fieldSelector fieldTys i).mkApps fields := by
    rw [show params' ++ [VExpr.lam ((VExpr.const S usS).mkApps params')
        (VExpr.projMotiveBody S usS uss params' fieldTys i), VExpr.fieldSelector fieldTys i] ++ fields
      = (params' ++ [VExpr.lam ((VExpr.const S usS).mkApps params')
        (VExpr.projMotiveBody S usS uss params' fieldTys i)]) ++
        VExpr.fieldSelector fieldTys i :: fields by simp]
    exact VExpr.instFields_minor_spine _ _ _
  rw [e] at hβ1
  obtain ⟨_, Hβ1⟩ := hβ1
  have hβ2 := VEnv.IsDefEqU.betaN henv hΓ (As := fieldTys) (as := fields)
    (b := .bvar (fieldTys.length - 1 - i)) hfl Hβ1.hasType.2
  rw [VExpr.instFields_bvar _ _ (by omega), show fields.length - 1 - (fieldTys.length - 1 - i) = i by
    omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hflen ▸ hi), Option.getD_some] at hβ2
  exact (h1.trans henv hΓ ⟨_, hι⟩).trans henv hΓ (VEnv.IsDefEqU.trans henv hΓ ⟨_, Hβ1⟩ hβ2)
