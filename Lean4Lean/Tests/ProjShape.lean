import Lean4Lean.Tests.ShapeDecide
import Lean4Lean.Theory.Proj
import Lean4Lean.Theory.Meta

/-!
Validation of the projection builders of `Theory/Proj.lean` (`VExpr.instPis`, `VExpr.projFn`,
`VExpr.projMotiveBody`, `VExpr.projTy`) against the kernel.

For each structure `S` and field `i` we read the constructor's telescope off the kernel's
constructor type with `instPis`/`piBinders` (as `inferProj` does), build the projection
function `projFn` over the parameter variables, translate it back to an `Expr` and have the
**kernel** accept `fun ps (x : S ps) => projFn x : ∀ ps (x : S ps), projMotiveBody` as a
definition (`Environment.addDeclCore`, synchronous); then we check that `projTy` is
`isDefEq` to the kernel's own `inferType (.proj S i x)`, and that `projFn (mk ps fs)`
ι+β-reduces (`Meta.whnf`) to the field `fs[i]`; and that the recursor's minor premise has
exactly the fields as binders (`VExpr.binderArity?`, the pin of `TrProjCtor`), which a
reflexive structure fails. The cases cover the constant motive
(`Prod`), the dependent motives of `Sigma`/`PSigma` at two distinct universes (a single
level list is rejected by the kernel there), `Subtype`/`Fin`/`And` (small elimination in
the second field), and a three-field chain `V3` whose last motive mentions two earlier
projections, one of them inside the other's motive.

`decide` pins the de Bruijn form of the builders on the hand-written expansions of
`Sigma.snd` (the motive `λ p. β[π₁ p/x]` realising the thesis's `π₂ p : β[π₁ p/x]`).
-/

namespace Lean4Lean.Tests.ProjShape

open Lean Meta Lean4Lean

structure V3 where
  n : Nat
  v : Fin n
  h : v.val < n

/-- Reflexive: the key `np+1+1+0` holds, the minor has an inductive-hypothesis binder. -/
structure Refl where
  next : Nat → Refl

/-- `VLevel` back to `Level` over the universe names `ls` (`VLevel.param i` is `ls[i]`,
inverting `VLevel.ofLevel`). -/
def toLevel (ls : List Name) : VLevel → Level
  | .zero => .zero
  | .succ l => .succ (toLevel ls l)
  | .max a b => .max (toLevel ls a) (toLevel ls b)
  | .imax a b => .imax (toLevel ls a) (toLevel ls b)
  | .param i => .param (ls.getD i .anonymous)

/-- `VExpr` back to `Expr`; binder names are irrelevant to the kernel. -/
def toExpr (ls : List Name) : VExpr → Expr
  | .bvar i => .bvar i
  | .sort u => .sort (toLevel ls u)
  | .const c us => .const c (us.map (toLevel ls))
  | .app f a => .app (toExpr ls f) (toExpr ls a)
  | .lam t b => .lam `x (toExpr ls t) (toExpr ls b) .default
  | .forallE t b => .forallE `x (toExpr ls t) (toExpr ls b) .default

/-- The leading `n` binders of a kernel type, outermost first. -/
def binders : Expr → Nat → List (Name × Expr)
  | .forallE n d b _, k+1 => (n, d) :: binders b k
  | _, _ => []

/-- Kernel-check the expansion of projection `i` of the structure `S`; `lvls j` is the
elimination level of field `j` (over the structure's universe names), consed onto its
levels when its recursor is large-eliminating. -/
def checkProj (S : Name) (i : Nat) (lvls : Nat → Level) : MetaM Unit := do
  let ival ← getConstInfoInduct S
  let [c] := ival.ctors | throwError "{S} is not a structure"
  let cinfo ← getConstInfoCtor c
  let rinfo ← getConstInfoRec (mkRecName S)
  let lps := ival.levelParams
  let usS : List VLevel := (List.range lps.length).map VLevel.param
  let usL := lps.map Level.param
  let large := rinfo.levelParams.length == lps.length + 1
  let uss : Nat → List VLevel := fun j =>
    if large then (VLevel.ofLevel lps (lvls j)).getD .zero :: usS else usS
  let np := ival.numParams
  -- the parameters as variables: under `p₀ … p_{np-1}`, parameter `j` is `bvar (np-1-j)`
  let ps := (List.range np).map fun j => VExpr.bvar (np - 1 - j)
  let cty0 ← Meta.ofExpr lps {} cinfo.type
  unless cty0.CtorHeaded do throwError "CtorHeaded fails for {c}"
  let some cty := (cty0.instL usS).instPis ps | throwError "instPis fails for {c}"
  let Fs := cty.piBinders
  unless Fs.length = cinfo.numFields do throwError "field count mismatch for {c}"
  unless i < Fs.length do throwError "no field {i} in {S}"
  -- the minor premise of the structure's recursor has exactly the fields as binders
  let rty ← Meta.ofExpr rinfo.levelParams {} rinfo.type
  unless rty.binderArity? (np + 1) = some cinfo.numFields do
    throwError "binderArity? of the minor of {S}.rec is not the field count"
  let structTy := (VExpr.const S usS).mkApps ps
  let pf := VExpr.projFn S usS uss ps Fs i
  let body := VExpr.projMotiveBody S usS uss ps Fs i
  -- `fun ps (x : S ps) => P_i x : ∀ ps (x : S ps), body`
  let val0 := toExpr lps (.lam structTy (.app pf.lift (.bvar 0)))
  let ty0 := toExpr lps (.forallE structTy body)
  let bs := binders ival.type np
  let val := bs.foldr (fun (n, d) v => Expr.lam n d v .default) val0
  let ty := bs.foldr (fun (n, d) v => Expr.forallE n d v .default) ty0
  let name := S ++ (s!"projExpansion_{i}").toName
  let cv : ConstantVal := { name, levelParams := lps, type := ty }
  let dv : DefinitionVal := { toConstantVal := cv, value := val, hints := .abbrev, safety := .safe }
  match (← getEnv).addDeclCore 0 512 (.defnDecl dv) none with
  | .ok _ => pure ()
  | .error e => throwError "the kernel rejects the expansion of {S}.{i}: {e.toMessageData {}}"
  -- `projTy` is the kernel's `inferProj` type, and the expansion computes the field
  forallBoundedTelescope ival.type np fun pfv _ => do
    let sTy := mkAppN (mkConst S usL) pfv
    withLocalDeclD `x sTy fun x => do
      let tProj ← inferType (.proj S i x)
      let tExp ← instantiateForall ty (pfv.push x)
      unless ← isDefEq tProj tExp do
        throwError "projTy of {S}.{i} is not the kernel's: {tExp} vs {tProj}"
    let ctorTy ← instantiateForall cinfo.type pfv
    forallBoundedTelescope ctorTy cinfo.numFields fun fs _ => do
      let mk := mkAppN (mkConst c usL) (pfv ++ fs)
      let red ← whnf (.app ((toExpr lps pf).instantiateRev pfv) mk)
      unless red == fs[i]! do throwError "projFn {S}.{i} (mk ps fs) reduces to {red}, not fs[{i}]"

run_meta do
  let u := Level.param `u; let v := Level.param `v
  checkProj ``Prod 0 (fun _ => .succ u)
  checkProj ``Prod 1 (fun j => if j == 0 then .succ u else .succ v)
  checkProj ``Sigma 0 (fun _ => .succ u)
  checkProj ``Sigma 1 (fun j => if j == 0 then .succ u else .succ v)
  checkProj ``PSigma 1 (fun j => if j == 0 then u else v)
  checkProj ``Subtype 0 (fun _ => u)
  checkProj ``Subtype 1 (fun j => if j == 0 then u else .zero)
  checkProj ``Fin 1 (fun j => if j == 0 then .succ .zero else .zero)
  checkProj ``And 1 (fun _ => .zero)
  checkProj ``V3 1 (fun _ => .succ .zero)
  checkProj ``V3 2 (fun j => if j == 2 then .zero else .succ .zero)
  -- Negative control: a single level list for every field is rejected by the kernel at
  -- `Sigma.snd` (`Sigma.rec.{u+1,u,v}` for a motive into `Type v`).
  let ok ← try checkProj ``Sigma 1 (fun _ => .succ u); pure true catch _ => pure false
  if ok then throwError "the kernel accepts Sigma.snd with the level list of Sigma.fst"
  -- Negative control: the minor premise of a reflexive structure's recursor has an
  -- inductive-hypothesis binder after its field (`binderArity?` is `2`, not `1`).
  let rinfo ← getConstInfoRec ``Refl.rec
  let rty ← Meta.ofExpr rinfo.levelParams {} rinfo.type
  if rty.binderArity? 1 = some 1 then
    throwError "binderArity? accepts the reflexive Refl.rec minor as field-only"
  unless rty.binderArity? 1 = some 2 do throwError "binderArity? of Refl.rec's minor is not 2"

/-! The hand-written expansion of `Sigma.snd` (thesis `π₂ p : β[π₁ p/x]` for `p : Σ x:α. β`), over
`Γ ⊢ A : Type u, B : A → Type v` as `bvar 1`, `bvar 0`: field telescope
`Fs = [A, B f₀]`, `P₀ = Sigma.rec.{u+1,u,v} A B (λ _. A) (λ a b. a)`, and the motive of the
second projection `λ p. B (P₀ p)`. -/
section SigmaSnd

local notation "u" => VLevel.param 0
local notation "v" => VLevel.param 1

def usS : List VLevel := [u, v]
def uss : Nat → List VLevel := fun j => if j = 0 then [.succ u, u, v] else [.succ v, u, v]
def ps : List VExpr := [.bvar 1, .bvar 0]
def Fs : List VExpr := [.bvar 1, .app (.bvar 1) (.bvar 0)]
def structTy : VExpr := (VExpr.const ``Sigma [u, v]).mkApps [.bvar 1, .bvar 0]
def P₀ : VExpr := (VExpr.const ``Sigma.rec [.succ u, u, v]).mkApps
  [.bvar 1, .bvar 0, .lam structTy (.bvar 2), .lam (.bvar 1) (.lam (.app (.bvar 1) (.bvar 0)) (.bvar 1))]

example : ((VExpr.const ``Sigma.mk [u, v]).mkApps ps).instPis ps = none := by decide

example : VExpr.projFn ``Sigma usS uss ps Fs 0 = P₀ := by decide

example : VExpr.projMotiveBody ``Sigma usS uss ps Fs 1 = .app (.bvar 1) (.app P₀.lift (.bvar 0)) := by
  decide

example : VExpr.projFn ``Sigma usS uss ps Fs 1 = (VExpr.const ``Sigma.rec [.succ v, u, v]).mkApps
    [.bvar 1, .bvar 0, .lam structTy (.app (.bvar 1) (.app P₀.lift (.bvar 0))),
      .lam (.bvar 1) (.lam (.app (.bvar 1) (.bvar 0)) (.bvar 0))] := by decide

/-- `P₁ e : B (P₀ e)`, the kernel's `β x.1`. -/
example (e : VExpr) : VExpr.projTy ``Sigma usS uss ps Fs 1 e = .app (.bvar 0) (.app P₀ e) := by
  simp [VExpr.projTy, VExpr.projFns, VExpr.projFnOf, VExpr.instFields, Fs, VExpr.inst, VExpr.instVar,
    VExpr.projMotiveBodyOf, VExpr.fieldSelector, ps, P₀, structTy, usS, uss, VExpr.mkApps,
    mkRecName, VExpr.liftN, liftVar]

end SigmaSnd

end Lean4Lean.Tests.ProjShape
