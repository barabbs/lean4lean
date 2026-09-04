import Lean4Lean.Theory.Typing.InductiveParams
import Lean4Lean.Theory.Meta

/-!
Validation of the recursor / constructor / ι-rule shape predicates (`VExpr.RecShape`,
`VExpr.CtorShape`, `VExpr.RuleShape` with its `VExpr.MinorFor` tie to the minor premise)
and of the ι reduct builder `SimplePattern.iotaRHS` against the kernel's own data.

For each recursor we translate (`Meta.ofExpr`) the kernel's `RecursorVal.type`, each
rule's `rhs`, and each rule constructor's type, and *decide* the shape predicates on the
results (their `Decidable` instances make them executable). For ι we build a redex
`rec params motives minors indices (ctor cparams fields)` over free variables, reduce it
with the executable kernel (`inductiveReduceRec`), and check that `iotaRHS … |>.apply` on
the pattern match gives the very same term. Finally we run the telescope decoder
`VEnv.recSplit?` on the reduct and the recursor's type: it must recover the kernel's
`(numParams, numMotives, numMinors, numIndices)` whenever the rule's constructor has the
recursor's parameters, and must *not* for the auxiliary recursor of a nested block (its
documented limit).

The declarations cover the cases `VInductDecl.WF` must be inhabitable for: a plain
recursive type (`Nat`), a parametrised one (`List`), a structure (`P2`), an indexed family
(`Vec`), a mutual block (`Ev`/`Od`), a nested block with its auxiliary recursor
(`Tree.rec`/`Tree.rec_1`, whose rules fire on `List.nil`/`List.cons` with
`ctorParams = 1 ≠ numParams = 0`), a K-like type (`Eq`), a recursor with λ-abstracted
recursive arguments (`Acc`), and an empty type (`False`); then (`checkAll`) every clause
on a further set of adversarial shapes and on a sweep of the library's inductive types.
-/

namespace Lean4Lean.Tests.IotaShape

open Lean Meta Lean4Lean

universe u

structure P2 where (a b : Nat)

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

mutual
inductive Ev : Nat → Prop where
  | z : Ev 0
  | s : Od n → Ev (n+1)
inductive Od : Nat → Prop where
  | s : Ev n → Od (n+1)
end

inductive Tree where
  | node : List Tree → Tree

/-- `VInductDecl.WF.rule_shape` for one rule: the reduct has `RuleShape` at some minor
`j`, the minor premise for the rule's constructor, applied to the `nf` fields and to as
many further arguments as the minor has binders after them. -/
def ruleShapeAt (ty rhs : VExpr) (np nm nmin nf : Nat) (c : Name) : Prop :=
  ∃ j < nmin, ∃ A, ty.piBinders[np + nm + j]? = some A ∧ A.MinorFor c ∧ nf ≤ A.piArity ∧
    rhs.RuleShape np nm nmin nf (A.piArity - nf) j

instance {ty rhs np nm nmin nf c} : Decidable (ruleShapeAt ty rhs np nm nmin nf c) := by
  unfold ruleShapeAt; infer_instance

/-- Decide the shape predicates on the kernel's data for recursor `n`, and check that each
rule's `nfields` is its constructor's `numFields`. Also decides the `recs_elim` clause of
`VInductDecl.WF` (the motives eliminate into `Sort (param 0)` iff the recursor has one
universe parameter more than its inductive, else into `Prop`) and its `rules_total` clause
(one rule per constructor of the major premise's type former — here also for the auxiliary
recursor of a nested block, whose major is over an older type former). -/
def checkShapes (n : Name) : MetaM Unit := do
  let .recInfo r ← getConstInfo n | throwError "{n} is not a recursor"
  let ty ← Meta.ofExpr r.levelParams {} r.type
  unless ty.RecShape r.numParams r.numMotives r.numMinors r.numIndices do
    throwError "RecShape fails for {n}"
  unless ty.RecHeaded do throwError "RecHeaded fails for {n}"
  if ty.CtorHeaded then throwError "CtorHeaded holds for the recursor {n}"
  let some I := ty.majorFormer? r.getMajorIdx | throwError "majorFormer? fails for {n}"
  let .inductInfo ival ← getConstInfo I | throwError "{I} is not an inductive type"
  -- the block's universe parameters (`VInductDecl.uvars`): those of its first type former,
  -- which for the auxiliary recursor of a nested block differ from the major's (`List`)
  let some I0 := r.all.head? | throwError "{n} has an empty block"
  let .inductInfo ival0 ← getConstInfo I0 | throwError "{I0} is not an inductive type"
  let duvars := ival0.levelParams.length
  unless (r.levelParams.length = duvars ∨ r.levelParams.length = duvars + 1) ∧
      ∀ i < r.numMotives, ∃ A, ty.piBinders[r.numParams + i]? = some A ∧
        A.piBody = .sort (if r.levelParams.length = duvars + 1 then .param 0 else .zero) do
    throwError "recs_elim fails for {n}"
  unless ∀ c ∈ ival.ctors, ∃ ru ∈ r.rules, ru.ctor = c do throwError "rules_total fails for {n}"
  for ru in r.rules do
    let .ctorInfo c ← getConstInfo ru.ctor | throwError "{ru.ctor} is not a constructor"
    let rhs ← Meta.ofExpr r.levelParams {} ru.rhs
    unless ruleShapeAt ty rhs r.numParams r.numMotives r.numMinors ru.nfields ru.ctor do
      throwError "RuleShape/MinorFor fails for {n}/{ru.ctor}"
    let cty ← Meta.ofExpr c.levelParams {} c.type
    unless cty.CtorShape (c.numParams + ru.nfields) do
      throwError "CtorShape fails for {ru.ctor}"
    if cty.RecHeaded then throwError "RecHeaded holds for the constructor {ru.ctor}"
    unless c.numFields = ru.nfields do throwError "nfields mismatch for {n}/{ru.ctor}"

/-- Executable pattern matcher; `matchPat_sound` relates it to `Pattern.Matches`. -/
def matchPat : (p : Pattern) → VExpr → Option (List VLevel × (p.Path → VExpr))
  | .const c, .const c' ls => if c = c' then some (ls, nofun) else none
  | .var f, .app f' a' =>
    match matchPat f f' with
    | some (m1, g) => some (m1, fun x => x.elim a' g)
    | none => none
  | .app f a, .app f' a' =>
    match matchPat f f', matchPat a a' with
    | some (m1, g1), some (_, g2) => some (m1, Sum.elim g1 g2)
    | _, _ => none
  | _, _ => none

theorem matchPat_sound : ∀ {p : Pattern} {e m1 m2},
    matchPat p e = some (m1, m2) → p.Matches e m1 m2
  | .const c, .const c' ls, m1, m2, h => by
    simp only [matchPat] at h; split at h
    · simp at h; obtain ⟨rfl, rfl⟩ := h; subst ‹c = c'›; exact .const
    · cases h
  | .var f, .app f' a', m1, m2, h => by
    simp only [matchPat] at h; split at h
    · rename_i hm; cases h; exact .var (matchPat_sound hm)
    · cases h
  | .app f a, .app f' a', m1, m2, h => by
    simp only [matchPat] at h; split at h
    · rename_i hf ha; cases h; exact .app (matchPat_sound hf) (matchPat_sound ha)
    · cases h
  | .const _, .bvar _, _, _, h | .const _, .sort _, _, _, h | .const _, .app .., _, _, h
  | .const _, .lam .., _, _, h | .const _, .forallE .., _, _, h
  | .var _, .bvar _, _, _, h | .var _, .sort _, _, _, h | .var _, .const .., _, _, h
  | .var _, .lam .., _, _, h | .var _, .forallE .., _, _, h
  | .app .., .bvar _, _, _, h | .app .., .sort _, _, _, h | .app .., .const .., _, _, h
  | .app .., .lam .., _, _, h | .app .., .forallE .., _, _, h => by simp [matchPat] at h

/-- Compare the `iotaRHS` reduct with the executable kernel's `inductiveReduceRec` on the
redex `recName params motives minors indices (ctorName cparams fields)`, all arguments
free variables. `cus` are the constructor's universe levels and `ctorParams` builds its
parameters from the recursor's arguments (the auxiliary recursor of a nested block fires
on a constructor whose parameters are not the recursor's). -/
def checkIota (recName ctorName : Name) (cus : List Level)
    (ctorParams : Array Expr → Array Expr) : MetaM Unit := do
  let kenv := (← getEnv).toKernelEnv
  let .recInfo r ← getConstInfo recName | throwError "{recName} is not a recursor"
  let .ctorInfo c ← getConstInfo ctorName | throwError "{ctorName} is not a constructor"
  let us := r.levelParams.map Level.param
  forallBoundedTelescope r.type (some r.getMajorIdx) fun xs _ => do
    let ctorHead := mkAppN (mkConst ctorName cus) (ctorParams xs)
    forallTelescope (← inferType ctorHead) fun fs _ => do
      let e := mkAppN (mkConst recName us) (xs.push (mkAppN ctorHead fs))
      let some red ← inductiveReduceRec kenv e Meta.whnf Meta.inferType Meta.isDefEq
        | throwError "the kernel does not reduce {e}"
      let all := xs ++ fs
      let fv : FVarIdMap Nat := all.zipIdx.foldl (init := {}) fun m (x, i) =>
        m.insert x.fvarId! (all.size - 1 - i)
      let ev ← Meta.ofExpr r.levelParams fv e
      let redv ← Meta.ofExpr r.levelParams fv red
      let some rule := r.rules.find? (·.ctor == ctorName)
        | throwError "{recName} has no rule for {ctorName}"
      let rhs ← Meta.ofExpr r.levelParams {} rule.rhs
      if hc : rhs.Closed then
        let p := (SimplePattern.iota recName r.getMajorIdx ctorName
          (c.numParams + rule.nfields)).toPattern
        let some (m1, m2) := matchPat p ev | throwError "no ι match for {recName}/{ctorName}"
        let R := SimplePattern.iotaRHS recName ctorName r.numParams r.numMotives r.numMinors
          r.numIndices c.numParams rule.nfields rhs hc
        unless R.apply m1 m2 = redv do throwError "ι reduct mismatch for {recName}/{ctorName}"
        -- (R3) `VEnv.recSplit?` decodes the kernel's telescope split from the entry and the
        -- recursor's type exactly when the rule's constructor has the recursor's parameters;
        -- for the auxiliary recursor of a nested block it reads `cnp` as `np` instead.
        let ty ← Meta.ofExpr r.levelParams {} r.type
        let split := VEnv.recSplit? ty R
        let truth := some (r.numParams, r.numMotives, r.numMinors, r.numIndices)
        if c.numParams = r.numParams then
          unless split = truth do
            throwError "recSplit? mismatch for {recName}/{ctorName}: {repr split}"
        else if split = truth then
          throwError "recSplit? unexpectedly exact for the nested rule {recName}/{ctorName}"
      else throwError "the reduct template of {recName}/{ctorName} is not closed"

/-- `types_have_rec`: the recursor of inductive type `I` eliminates `I`. -/
def checkTypesHaveRec (I : Name) : MetaM Unit := do
  let .recInfo r ← getConstInfo (mkRecName I) | throwError "{I} has no recursor"
  let ty ← Meta.ofExpr r.levelParams {} r.type
  unless ty.majorFormer? r.getMajorIdx = some I do throwError "types_have_rec fails for {I}"

/-- The `VInductDecl.WF` clauses not decided by `checkShapes`: `rec_params`,
`rules_own_params`, `rules_nodup`, `rules_ctor` (with the constructor's own `numParams`),
and closedness of the reducts. -/
def checkMore (n : Name) : MetaM Unit := do
  let .recInfo r ← getConstInfo n | throwError "{n} is not a recursor"
  let some I0 := r.all.head? | throwError "{n} has an empty block"
  let .inductInfo ival0 ← getConstInfo I0 | throwError "{I0} is not an inductive type"
  unless r.numParams = ival0.numParams do throwError "rec_params fails for {n}"
  unless (r.rules.map (·.ctor)).Nodup do throwError "rules_nodup fails for {n}"
  let own : List Name ← r.all.flatMapM fun t => do
    let .inductInfo iv ← getConstInfo t | throwError "{t} is not an inductive type"
    pure iv.ctors
  for ru in r.rules do
    let .ctorInfo c ← getConstInfo ru.ctor | throwError "{ru.ctor} is not a constructor"
    if ru.ctor ∈ own then
      unless c.numParams = r.numParams do throwError "rules_own_params fails for {n}/{ru.ctor}"
    let cty ← Meta.ofExpr c.levelParams {} c.type
    unless cty.CtorShape (c.numParams + ru.nfields) do throwError "rules_ctor fails for {n}/{ru.ctor}"
    let rhs ← Meta.ofExpr r.levelParams {} ru.rhs
    unless rhs.Closed do throwError "the reduct of {n}/{ru.ctor} is not closed"

/-- `checkIota` with the constructor's levels and parameters read off the recursor's major
premise, so that the auxiliary recursors of nested blocks are covered generically. -/
def checkIotaAuto (recName ctorName : Name) : MetaM Unit := do
  let .recInfo r ← getConstInfo recName | throwError "{recName} is not a recursor"
  let .ctorInfo c ← getConstInfo ctorName | throwError "{ctorName} is not a constructor"
  let (cus, absParams) ← forallBoundedTelescope r.type (some r.getMajorIdx) fun xs body => do
    let .forallE _ majorTy _ _ := body | throwError "{recName} has no major premise"
    let .const _ us := majorTy.getAppFn | throwError "the major premise of {recName} is not a constant application"
    let args := (majorTy.getAppArgs.toList.take c.numParams).toArray
    pure (us, args.map (·.abstract xs))
  checkIota recName ctorName cus (fun xs => absParams.map (·.instantiateRev xs))

/-- The recursors of the block of `I`: `I.rec` and the auxiliary `I.rec_1`, `I.rec_2`, … of
a nested block. -/
def recsOf (I : Name) : MetaM (List Name) := do
  let env ← getEnv
  let mut out := [mkRecName I]
  let mut i := 1
  while env.contains ((mkRecName I).appendIndexAfter i) do
    out := out ++ [(mkRecName I).appendIndexAfter i]
    i := i + 1
  pure out

/-- Every check on every recursor of the block of `I` and every rule of each. -/
def checkAll (I : Name) : MetaM Unit := do
  checkTypesHaveRec I
  for rn in ← recsOf I do
    checkShapes rn
    checkMore rn
    let .recInfo r ← getConstInfo rn | throwError "{rn} is not a recursor"
    for ru in r.rules do
      checkIotaAuto rn ru.ctor

/-! Further shapes: nested through several type formers (`TreeP`, `T2`, `T3`, `TreeQ`),
mutual and nested at once (`MA`/`MB`), nested through an indexed family (`T4`), reflexive
(`Refl`, `Fn`: minors with an inductive-hypothesis binder after the fields, rules with a
λ-abstracted recursive argument), an indexed `Prop` family (`Le`), a dependent structure
(`Dep`), a mutual indexed `Type` block (`EvI`/`OdI`), and small-eliminating `Prop`
inductives (`PropLarge`, `Wrap`, `SigmaLike`). -/

inductive TreeP (α : Type u) where
  | leaf : α → TreeP α
  | node : List (TreeP α) → TreeP α

inductive T2 where
  | mk : Option T2 → (Nat × T2) → Array T2 → T2

inductive T3 where
  | mk : List (List T3) → T3

mutual
inductive MA where | mk : List MB → MA
inductive MB where | mk : List MA → Nat → MB
end

inductive T4 where
  | mk : Vec T4 2 → T4

inductive Refl where | mk : (Nat → Refl) → Refl

inductive Le : Nat → Nat → Prop where
  | refl : Le n n
  | step : Le n m → Le n (m+1)

structure Dep where
  n : Nat
  v : Fin n
  h : n > 0

inductive TreeQ (α : Type) (β : Type) where
  | mk : List (α × TreeQ α β) → β → TreeQ α β

inductive Fn (α : Type u) : Type u where
  | mk : (α → Fn α) → List (Fn α) → Fn α

mutual
inductive EvI : Nat → Type where
  | z : EvI 0
  | s : OdI n → EvI (n+1)
inductive OdI : Nat → Type where
  | s : EvI n → OdI (n+1)
end

inductive PropLarge : Prop where
  | mk : Nat → PropLarge

inductive Wrap (p : Prop) : Prop where
  | mk : p → Wrap p

inductive SigmaLike : Prop where
  | mk (n : Nat) (h : n = n) : SigmaLike

run_meta do
  for n in [``Nat.rec, ``List.rec, ``P2.rec, ``Vec.rec, ``Ev.rec, ``Od.rec, ``Tree.rec,
      ``Tree.rec_1, ``Eq.rec, ``Acc.rec, ``False.rec] do
    checkShapes n
  for I in [``Nat, ``List, ``P2, ``Vec, ``Ev, ``Od, ``Tree, ``Eq, ``Acc, ``False] do
    checkTypesHaveRec I

  -- Negative controls: `RecShape` rejects a wrong telescope split, `RuleShape` a wrong
  -- field count, `CtorShape` a wrong arity.
  let .recInfo natRec ← getConstInfo ``Nat.rec | throwError "Nat.rec"
  let ty ← Meta.ofExpr natRec.levelParams {} natRec.type
  if ty.RecShape 0 1 1 1 then throwError "RecShape accepts (0,1,1,1) for Nat.rec"
  if ty.RecShape 1 1 1 0 then throwError "RecShape accepts (1,1,1,0) for Nat.rec"
  if ty.RecShape 0 2 1 0 then throwError "RecShape accepts (0,2,1,0) for Nat.rec"
  let some succRule := natRec.rules.find? (·.ctor == ``Nat.succ) | throwError "Nat.succ rule"
  let rhs ← Meta.ofExpr natRec.levelParams {} succRule.rhs
  if ∃ j < (2 : Nat), rhs.RuleShape 0 1 2 0 2 j then
    throwError "RuleShape accepts nf = 0 for Nat.rec/Nat.succ"
  if ∃ j < (1 : Nat), rhs.RuleShape 0 1 1 1 1 j then
    throwError "RuleShape accepts nmin = 1 for Nat.rec/Nat.succ"
  -- The recursive-argument count: the `succ` rule `λ motive z s n, s n (Nat.rec motive z s n)`
  -- applies the minor to its field and to exactly one inductive hypothesis.
  unless rhs.RuleShape 0 1 2 1 1 1 do throwError "RuleShape rejects nrec = 1 for Nat.rec/Nat.succ"
  if rhs.RuleShape 0 1 2 1 0 1 then throwError "RuleShape accepts nrec = 0 for Nat.rec/Nat.succ"
  if rhs.RuleShape 0 1 2 1 2 1 then throwError "RuleShape accepts nrec = 2 for Nat.rec/Nat.succ"
  let .ctorInfo cons ← getConstInfo ``List.cons | throwError "List.cons"
  let cty ← Meta.ofExpr cons.levelParams {} cons.type
  if cty.CtorShape 2 then throwError "CtorShape accepts arity 2 for List.cons"
  -- `rules_total` rejects a recursor over `Nat` lacking the rule for one of its constructors
  -- (the stuck `R : ∀ m (f : ∀ n, m (n+1)) t, m t` with only a `succ` rule).
  let .inductInfo natVal ← getConstInfo ``Nat | throwError "Nat"
  let succOnly := natRec.rules.filter (·.ctor != ``Nat.zero)
  if ∀ c ∈ natVal.ctors, ∃ ru ∈ succOnly, ru.ctor = c then
    throwError "rules_total accepts a recursor over Nat without a rule for Nat.zero"
  -- `recs_elim` rejects a `Prop`-eliminating level for `Nat.rec` and an extra universe
  -- parameter for `Ev.rec`.
  if ∀ i < natRec.numMotives, ∃ A, ty.piBinders[natRec.numParams + i]? = some A ∧
      A.piBody = .sort .zero then
    throwError "recs_elim accepts Prop as the elimination level of Nat.rec"
  let .recInfo evRec ← getConstInfo ``Ev.rec | throwError "Ev.rec"
  let evTy ← Meta.ofExpr evRec.levelParams {} evRec.type
  if ∀ i < evRec.numMotives, ∃ A, evTy.piBinders[evRec.numParams + i]? = some A ∧
      A.piBody = .sort (.param 0) then
    throwError "recs_elim accepts Sort (param 0) as the elimination level of Ev.rec"

  -- Negative controls for the §2.6.3 pins. The `Nat.succ` rule reducing to the *zero* minor
  -- (`λ motive z s n, z n`) has `RuleShape` at `j = 0`, but minor 0 of `Nat.rec` is not the
  -- minor premise for `Nat.succ`; and as a rule for `Nat.zero` with one field it applies
  -- the zero minor (no binders) to a field — rejected by the count (`nf ≤ piArity(minor)`).
  -- A reduct whose recursive-call slot holds a well-typed non-recursive term is not rejected
  -- by the shapes (only its number is pinned; the terms are not).
  let bogusSuccRhs : VExpr :=
    .lam (.sort .zero) (.lam (.sort .zero) (.lam (.sort .zero) (.lam (.sort .zero)
      ((VExpr.bvar 2).mkApps [.bvar 0]))))
  if ruleShapeAt ty bogusSuccRhs 0 1 2 1 ``Nat.succ then
    throwError "rule_shape accepts the zero minor for Nat.rec/Nat.succ"
  if ruleShapeAt ty bogusSuccRhs 0 1 2 1 ``Nat.zero then
    throwError "rule_shape accepts a field applied to the zero minor for Nat.rec/Nat.zero"
  -- The kernel's zero rule `λ motive z s, z` is shape-correct for `Nat.zero` with no fields.
  let zeroRhs : VExpr := .lam (.sort .zero) (.lam (.sort .zero) (.lam (.sort .zero) (.bvar 1)))
  unless ruleShapeAt ty zeroRhs 0 1 2 0 ``Nat.zero do
    throwError "rule_shape rejects the zero rule for Nat.rec/Nat.zero"
  -- The `succ` rule with its inductive hypothesis dropped (`λ motive z s n, s n`, a
  -- case-analysis reduct) applies the `succ` minor to one argument short of its binders.
  let succNoIH : VExpr :=
    .lam (.sort .zero) (.lam (.sort .zero) (.lam (.sort .zero) (.lam (.sort .zero)
      ((VExpr.bvar 1).mkApps [.bvar 0]))))
  if ruleShapeAt ty succNoIH 0 1 2 1 ``Nat.succ then
    throwError "rule_shape accepts the succ rule without its inductive hypothesis"
  -- A minor premise that is a bare motive (`m : motive`) is not the minor for any constructor.
  if (VExpr.bvar 0).MinorFor ``Nat.zero then throwError "MinorFor accepts a bare motive"
  -- `Nat.rec`'s telescope with the major premise `Bool` (motive over `Nat`, major over
  -- `Bool`), and with the zero minor targeting `motive (Nat.succ Nat.zero)`.
  let natRecTy (majorTy zeroTarget : VExpr) : VExpr :=
    .forallE (.forallE (.const ``Nat []) (.sort (.param 0)))
      (.forallE zeroTarget
        (.forallE (.forallE (.const ``Nat []) (.forallE ((VExpr.bvar 2).app (.bvar 0))
            ((VExpr.bvar 3).app ((VExpr.const ``Nat.succ []).app (.bvar 1)))))
          (.forallE majorTy ((VExpr.bvar 3).app (.bvar 0)))))
  let zeroTarget : VExpr := (VExpr.bvar 0).app (.const ``Nat.zero [])
  unless (natRecTy (.const ``Nat []) zeroTarget).RecShape 0 1 2 0 do
    throwError "RecShape rejects the hand-built Nat.rec type"
  if (natRecTy (.const ``Bool []) zeroTarget).RecShape 0 1 2 0 then
    throwError "RecShape accepts a major premise over the wrong type former"
  let swappedZero : VExpr := (VExpr.bvar 0).app ((VExpr.const ``Nat.succ []).app (.const ``Nat.zero []))
  if swappedZero.MinorFor ``Nat.zero then
    throwError "MinorFor accepts `motive (Nat.succ Nat.zero)` as the minor for Nat.zero"
  -- The head of a minor premise is one of the motives (`MinorHeaded`): a succ minor
  -- `∀ n (g : Nat → Sort u), g (Nat.succ n)`, headed by its own binder `g`, is rejected.
  let selfHeadedSucc : VExpr :=
    .forallE (.const ``Nat []) (.forallE (.forallE (.const ``Nat []) (.sort (.param 0)))
      ((VExpr.bvar 0).app ((VExpr.const ``Nat.succ []).app (.bvar 1))))
  let selfHeadedTy : VExpr :=
    .forallE (.forallE (.const ``Nat []) (.sort (.param 0)))
      (.forallE zeroTarget (.forallE selfHeadedSucc
        (.forallE (.const ``Nat []) ((VExpr.bvar 3).app (.bvar 0)))))
  if selfHeadedTy.RecShape 0 1 2 0 then
    throwError "RecShape accepts a minor premise headed by its own binder"

  -- `iotaRHS` reproduces the kernel's ι reduct, including for the auxiliary recursor of a
  -- nested block (`Tree.rec_1` on `List.cons`, `ctorParams = 1`, `nfields = 2`).
  checkIota ``Nat.rec ``Nat.zero [] (fun _ => #[])
  checkIota ``Nat.rec ``Nat.succ [] (fun _ => #[])
  checkIota ``List.rec ``List.cons [.param `u] (fun xs => #[xs[0]!])
  checkIota ``P2.rec ``P2.mk [] (fun _ => #[])
  checkIota ``Vec.rec ``Vec.cons [] (fun xs => #[xs[0]!])
  checkIota ``Ev.rec ``Ev.s [] (fun _ => #[])
  checkIota ``Od.rec ``Od.s [] (fun _ => #[])
  checkIota ``Tree.rec ``Tree.node [] (fun _ => #[])
  checkIota ``Tree.rec_1 ``List.nil [.zero] (fun _ => #[mkConst ``Tree])
  checkIota ``Tree.rec_1 ``List.cons [.zero] (fun _ => #[mkConst ``Tree])
  checkIota ``Eq.rec ``Eq.refl [.param `u_1] (fun xs => #[xs[0]!, xs[1]!])
  checkIota ``Acc.rec ``Acc.intro [.param `u] (fun xs => #[xs[0]!, xs[1]!])

  -- Every check, on the shapes above and on a sweep of the library's inductive types.
  for I in [``TreeP, ``T2, ``T3, ``MA, ``MB, ``T4, ``Refl, ``Le, ``Dep, ``TreeQ, ``Fn,
      ``EvI, ``OdI, ``PropLarge, ``Wrap, ``SigmaLike,
      ``Nat, ``List, ``Bool, ``Option, ``Sum, ``Prod, ``PProd, ``PSum, ``PSigma, ``Sigma,
      ``Subtype, ``And, ``Or, ``Exists, ``Nonempty, ``Decidable, ``Fin, ``Char, ``String,
      ``Array, ``Except, ``ULift, ``PLift, ``HEq, ``Iff, ``WellFounded, ``Acc, ``Eq, ``PUnit,
      ``True, ``False, ``Empty, ``PEmpty, ``Lean.Syntax, ``Lean.Json, ``Lean.Expr,
      ``Lean.Name, ``Lean.Level, ``Lean.LocalDecl, ``Lean.Elab.Term.MatchAltView,
      ``Lean.Meta.Simp.Step, ``Std.Format, ``Lean.MessageData, ``Lean.Elab.Info,
      ``Lean.Elab.InfoTree] do
    checkAll I

end Lean4Lean.Tests.IotaShape
