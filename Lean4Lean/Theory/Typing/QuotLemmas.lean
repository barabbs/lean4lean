import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.Meta

namespace Lean4Lean
namespace VEnv

theorem addQuot_WF (henv : Ordered env) (hq : QuotReady env) :
    addQuot env = some env' → Ordered env' := by
  refine with_addConst (cis := [.const _ eqConst]) (hcis := ⟨hq, ⟨⟩⟩) henv
    (fun _ => ⟨_, by type_tac⟩) fun henv => ?_
  refine with_addConst henv (fun ⟨quot, _⟩ => ⟨_, by type_tac⟩) fun henv => ?_
  refine with_addConst henv (fun ⟨_, quot, eq, _⟩ => ⟨_, by type_tac⟩) fun henv => ?_
  refine with_addConst henv (fun ⟨_, _, quot, _⟩ => ⟨_, by type_tac⟩) fun henv => ?_
  rintro ⟨_, _, _, _, eq, _⟩ ⟨⟩; exact .defeq henv ⟨by type_tac, by type_tac⟩

/-- `addQuot` as the chain it is: four `addConst` steps and one `addDefEq`, with the typing
of each constant in the environment it is added to and of the quotient rule in the
environment it is registered in. -/
theorem addQuot_chain {env env' : VEnv} (hq : QuotReady env) (h : addQuot env = some env') :
    ∃ e1 e2 e3 e4,
      quotConst.WF env ∧ env.addConst ``Quot quotConst = some e1 ∧
      quotMkConst.WF e1 ∧ e1.addConst ``Quot.mk quotMkConst = some e2 ∧
      quotLiftConst.WF e2 ∧ e2.addConst ``Quot.lift quotLiftConst = some e3 ∧
      quotIndConst.WF e3 ∧ e3.addConst ``Quot.ind quotIndConst = some e4 ∧
      quotDefEq.WF e4 ∧ env' = e4.addDefEq quotDefEq := by
  rw [VEnv.addQuot] at h
  obtain ⟨e1, s1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e2, s2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e3, s3, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e4, s4, h⟩ := Option.bind_eq_some_iff.1 h
  injection h with h
  have o1 := HasObjects.const (ls := [.const ``Eq eqConst]) ⟨hq, ⟨⟩⟩ s1
  have o2 := HasObjects.const o1 s2
  have o3 := HasObjects.const o2 s3
  have o4 := HasObjects.const o3 s4
  obtain ⟨_, _, _⟩ := o1
  obtain ⟨_, _, _, _⟩ := o2
  obtain ⟨_, _, _, _, _⟩ := o3
  obtain ⟨_, _, _, _, _, _⟩ := o4
  exact ⟨e1, e2, e3, e4, ⟨_, by type_tac⟩, s1, ⟨_, by type_tac⟩, s2, ⟨_, by type_tac⟩, s3,
    ⟨_, by type_tac⟩, s4, ⟨by type_tac, by type_tac⟩, h.symm⟩

section
variable (henv : addQuot env = some env') include henv

theorem addQuot_objs : env'.HasObjects [.defeq quotDefEq, .const `Quot.ind quotIndConst,
    .const `Quot.lift quotLiftConst, .const `Quot.mk quotMkConst, .const `Quot quotConst] := by
  let ⟨env, h, henv⟩ := HasObjects.bind_const (ls := []) trivial henv
  let ⟨env, h, henv⟩ := HasObjects.bind_const h henv
  let ⟨env, h, henv⟩ := HasObjects.bind_const h henv
  obtain ⟨env, h, ⟨⟩⟩ := HasObjects.bind_const h henv
  exact HasObjects.defeq (df := quotDefEq) h

theorem addQuot_quot : env'.constants ``Quot = quotConst := (addQuot_objs henv).2.2.2.2.1
theorem addQuot_quotMk : env'.constants ``Quot.mk = quotMkConst := (addQuot_objs henv).2.2.2.1
theorem addQuot_quotLift : env'.constants ``Quot.lift = quotLiftConst := (addQuot_objs henv).2.2.1
theorem addQuot_quotInd : env'.constants ``Quot.ind = quotIndConst := (addQuot_objs henv).2.1
theorem addQuot_defeq : env'.defeqs quotDefEq := (addQuot_objs henv).1

end
