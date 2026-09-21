import Lean4Lean.Environment
import Lean4Lean.Tests.IotaShape
import Lean4Lean.Tests.ProjShape
import Lean4Lean.Tests.Programs

/-!
The checks for `Lean4Lean/Tests/Programs.lean`.

Building that module only says that *Lean's* kernel accepted it. This one re-establishes the
same facts with lean4lean's, and adds the two things a build cannot say by itself.

1. **The declarations type check.** Each definition and theorem of the module is re-checked by
   `Lean4Lean.checkDefinitionBody`, which is the body of `Lean4Lean.addDecl`: infer the type of
   the value with lean4lean's `TypeChecker` and `isDefEq` it against the declared type. For a
   `theorem _ : f xs = ys := rfl` that is exactly the reduction the suite is about. A
   deliberately corrupted declaration is run through the same path to show it can reject.

2. **The programs compute the right values.** `checkValue` reduces a closed term with
   lean4lean's own `whnf` — recursively, since one `whnf` only exposes the outermost
   constructor — and compares the normal form with the expected value syntactically, which is
   stronger than asking `isDefEq` (that could hold by some other route); `isDefEq` is asked as
   well. `checkDistinct` demands the opposite verdict on a pair that must not be equal, so a
   harness that accepted everything would fail here.

3. **The ι and projection builders of `Theory/` describe these types.** `IotaShape.checkAll`
   decides the `VInductDecl.WF` clauses on the kernel's own recursor data and checks that the
   reduct `SimplePattern.iotaRHS` builds is the one `inductiveReduceRec` produces;
   `ProjShape.checkProj` has *Lean's* kernel accept the projection expansion `VExpr.projFn`
   builds and checks it reduces to the field (that file predates this one and drives
   `Environment.addDeclCore`, not lean4lean's `TypeChecker`). Both are run here on the *program* types rather than on
   the hand-picked prelude types of their own files.

`lake exe lean4lean Lean4Lean.Tests.Programs` is the fourth check and the only end-to-end one:
it replays the whole module, inductive declarations and recursors included, through
`Lean4Lean.addDecl` into an environment built from the module's imports.
-/

namespace Lean4Lean.Tests.ProgramsCheck

open Lean Lean4Lean
open Lean.Meta (mkAppM mkListLit)
open Lean4Lean.Tests.IotaShape (checkAll checkNested)
open Lean4Lean.Tests.ProjShape (checkProj)

/-! ### Re-checking the declarations with lean4lean's type checker -/

/-- The declarations `checkDefinitionBody` can take: a definition, or a theorem viewed as one
(the kernel checks a theorem's value against its type the same way). `partial` and `unsafe`
definitions are skipped, as `Lean4Lean.Replay` skips them (`Replay.lean`, `replayConstant`); the
equation compiler emits a `partial` `_unsafe_rec` companion for several of the programs, and it
carries no logical content. -/
private def defnOf : ConstantInfo → Option DefinitionVal
  | .defnInfo v => if v.safety matches .safe then some v else none
  | .thmInfo v =>
    some { toConstantVal := v.toConstantVal, value := v.value, hints := .opaque, safety := .safe }
  | _ => none

private def kernelMsg (e : Kernel.Exception) : MetaM String := (e.toMessageData {}).toString

/-- Infer the type of `v`'s value with lean4lean and `isDefEq` it against the declared type,
in the `.safe` context `Lean4Lean.addDefinition` uses for a safe definition. -/
private def recheck (env : Kernel.Environment) (v : DefinitionVal) :
    Except Kernel.Exception Unit :=
  TypeChecker.M.run env (lparams := v.levelParams) (x := checkDefinitionBody env v)

-- Every definition and theorem of `Lean4Lean.Tests.Programs`, re-checked. The module's
-- auxiliary declarations (`brecOn`, the match auxiliaries, the `DecidableEq` instances) are
-- included: they are what the programs actually reduce through.
run_meta do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Lean4Lean.Tests.Programs
    | throwError "Lean4Lean.Tests.Programs is not imported"
  let kenv := env.toKernelEnv
  let mut n : Nat := 0
  let mut sawProgram := false
  for ci in env.header.moduleData[idx]!.constants do
    if ci.name == ``Programs.NatArith.fib_ex then sawProgram := true
    if let some v := defnOf ci then
      match recheck kenv v with
      | .ok _ => n := n + 1
      | .error e => throwError "lean4lean rejected {ci.name}: {← kernelMsg e}"
  -- the module index is looked up by name, so pin that the constants iterated are the
  -- program suite's and not some other module's
  unless sawProgram do throwError "the re-checked module does not contain the programs"
  if n < 50 then throwError "only {n} declarations were re-checked; the module looks truncated"

-- The negative control for the check above: the same path on a declaration whose stated type
-- is wrong must reject. Without it, a `recheck` that returned `.ok` unconditionally would pass.
run_meta do
  let some v := defnOf (← getConstInfo ``Programs.NatArith.fib_ex)
    | throwError "fib_ex has no value"
  let corrupted := { v with type := .const ``Bool [] }
  match recheck (← getEnv).toKernelEnv corrupted with
  | .error _ => pure ()
  | .ok _ => throwError "lean4lean accepted a declaration whose stated type is `Bool`"

/-! ### Reducing the programs with lean4lean's `whnf` -/

/-- `TypeChecker.whnf` exposes the head constructor and stops, so the arguments of the result
are still redexes; `deepWhnf` walks into them. Built on lean4lean's `whnf` alone — using
Lean's `Meta.whnf` anywhere here would measure the wrong kernel. -/
private partial def deepWhnf (env : Kernel.Environment) (e : Expr) :
    Except Kernel.Exception Expr := do
  let e ← TypeChecker.M.run env (x := TypeChecker.whnf e)
  let args := e.getAppArgs
  if args.isEmpty then return e
  return mkAppN e.getAppFn (← args.mapM (deepWhnf env))

private def nf (env : Kernel.Environment) (label : String) (e : Expr) : MetaM Expr := do
  match deepWhnf env e with
  | .ok e => return e
  | .error err => throwError "lean4lean failed to reduce {label} ({e}): {← kernelMsg err}"

private def defeq (env : Kernel.Environment) (label : String) (a b : Expr) : MetaM Bool := do
  match TypeChecker.M.run env (x := TypeChecker.isDefEq a b) with
  | .ok r => return r
  | .error err => throwError "lean4lean failed on isDefEq for {label}: {← kernelMsg err}"

/-- `actual` reduces to `expected` and the two are `isDefEq`, both according to lean4lean. -/
private def checkValue (env : Kernel.Environment) (label : String) (actual expected : Expr) :
    MetaM Unit := do
  let actualNF ← nf env label actual
  let expectedNF ← nf env s!"{label} (expected side)" expected
  unless actualNF == expectedNF do
    throwError "{label}: lean4lean reduces {actual}\n  to {actualNF}\n  not to {expectedNF}"
  unless ← defeq env label actual expected do
    throwError "{label}: lean4lean reduces both sides to {actualNF} but isDefEq is false"

/-- The mirror: a pair that must not be equal. Guards against a vacuous `checkValue`. -/
private def checkDistinct (env : Kernel.Environment) (label : String) (actual expected : Expr) :
    MetaM Unit := do
  let actualNF ← nf env label actual
  let expectedNF ← nf env s!"{label} (expected side)" expected
  if actualNF == expectedNF && (← defeq env label actual expected) then
    throwError "{label}: lean4lean equates {actual} with {expected}, which must not be equal"

private def natList (ns : List Nat) : MetaM Expr := mkListLit (mkConst ``Nat) (ns.map mkNatLit)

open Programs in
run_meta do
  let env := (← getEnv).toKernelEnv
  let input ← natList [5, 3, 8, 1, 9, 2, 7, 4, 10, 6]
  let sorted ← natList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

  -- ι on `List.rec` and `Nat.rec`, through three different sorts
  checkValue env "isort" (← mkAppM ``Sorting.isort #[input]) sorted
  checkValue env "mergeSort" (← mkAppM ``Sorting.mergeSort #[mkNatLit 10, input]) sorted
  checkValue env "qsort" (← mkAppM ``Sorting.qsort #[mkNatLit 10, input]) sorted
  checkValue env "insert"
    (← mkAppM ``Sorting.insert #[mkNatLit 4, ← natList [1, 3, 5]]) (← natList [1, 3, 4, 5])
  checkValue env "isort []" (← mkAppM ``Sorting.isort #[← natList []]) (← natList [])

  -- ι on a user recursor, a nested block's auxiliary recursor, and a mutual block
  checkValue env "BST.inorder"
    (← mkAppM ``Trees.BST.inorder #[← mkAppM ``Trees.build #[input]]) sorted
  checkValue env "sumRose"
    (← mkAppM ``Trees.sumRose #[mkConst ``Trees.sampleRose]) (mkNatLit 15)
  checkValue env "sumTree"
    (← mkAppM ``Trees.sumTree #[mkConst ``Trees.sampleTree]) (mkNatLit 10)

  -- ι on `Nat.rec` against a literal major premise, and on a mutual `Nat` block
  checkValue env "fib" (← mkAppM ``NatArith.fib #[mkNatLit 15]) (mkNatLit 610)
  checkValue env "sumRange" (← mkAppM ``NatArith.sumRange #[mkNatLit 100]) (mkNatLit 5050)
  checkValue env "isEven" (← mkAppM ``Parity.isEven #[mkNatLit 20]) (mkConst ``Bool.true)

  -- the ι branches the equation compiler never produces: arguments after the major premise,
  -- a structure-like major, a string literal major, and an indexed family
  checkValue env "addFromRec"
    (← mkAppM ``Special.addFromRec #[mkNatLit 3, mkNatLit 10]) (mkNatLit 13)
  checkValue env "sumPair"
    (← mkAppM ``Special.sumPair #[← mkAppM ``Prod.mk #[mkNatLit 3, mkNatLit 4]]) (mkNatLit 7)
  checkValue env "byteSize" (← mkAppM ``Special.byteSize #[mkStrLit "abc"]) (mkNatLit 3)
  checkValue env "Vec.sum" (← mkAppM ``Special.Vec.sum #[mkConst ``Special.v3]) (mkNatLit 6)

  -- projections, written as `Expr.proj` so that `Inner.inferProj`/`reduceProj` are what runs;
  -- the structure being projected is the result of a recursion, so ι has to fire first
  let rle ← mkAppM ``Records.encode #[← natList [1, 1, 1, 2, 2, 3, 3, 3, 3, 1]]
  let firstRun ← mkAppM ``Records.firstRun #[rle]
  checkValue env "Run.val" (.proj ``Records.Run 0 firstRun) (mkNatLit 1)
  checkValue env "Run.count" (.proj ``Records.Run 1 firstRun) (mkNatLit 3)
  let tally ← mkAppM ``Records.summarize #[← natList [1, 2, 3, 4, 5]]
  checkValue env "Tally.sum" (.proj ``Records.Tally 0 tally) (mkNatLit 15)
  checkValue env "Tally.count" (.proj ``Records.Tally 1 tally) (mkNatLit 5)
  let basket ← mkAppM ``Records.buildBasket #[← natList [1, 2, 3, 4, 5]]
  checkValue env "Basket.items" (.proj ``Records.Basket 0 basket) (← natList [1, 2, 3, 4, 5])
  -- a projection out of a projection
  let rect := mkConst ``Records.sampleRect
  checkValue env "Rect.bottomRight.x"
    (.proj ``Records.Point 0 (.proj ``Records.Rect 1 rect)) (mkNatLit 5)

  -- the harness is not vacuous
  checkDistinct env "2 + 2 ≠ 5" (← mkAppM ``Nat.add #[mkNatLit 2, mkNatLit 2]) (mkNatLit 5)
  checkDistinct env "isort [2,1] ≠ [2,1]"
    (← mkAppM ``Sorting.isort #[← natList [2, 1]]) (← natList [2, 1])
  checkDistinct env "Run.count ≠ Run.val"
    (.proj ``Records.Run 1 firstRun) (.proj ``Records.Run 0 firstRun)

/-! ### The `Theory/` builders on the program types -/

/-- `act` must fail, and its message must mention `pat`: a negative control that only demands
*some* failure keeps passing when the failure drifts to an unrelated cause. -/
private def expectFailure (label pat : String) (act : MetaM Unit) : MetaM Unit := do
  let msg? ← try act; pure none catch e => pure (some (← e.toMessageData.toString))
  match msg? with
  | none => throwError "{label} was expected to fail"
  | some msg =>
    unless (msg.splitOn pat).length > 1 do
      throwError "{label} failed for the wrong reason: {msg}"

-- `VInductDecl.WF` and the ι reduct builder, on the types the programs are written over.
run_meta do
  checkAll ``Programs.Trees.BST
  checkAll ``Programs.Trees.Tree
  checkAll ``Programs.Trees.Forest
  checkAll ``Programs.Records.Color
  checkAll ``Programs.Records.Run
  checkAll ``Programs.Records.Point
  checkAll ``Programs.Records.Tally
  checkAll ``Programs.Records.Rect
  checkAll ``Programs.Records.Basket
  checkAll ``Programs.Records.Pair
  -- an indexed family and a large-eliminating `Prop`, the two block shapes the programs above
  -- do not have
  checkAll ``Programs.Special.Vec
  checkAll ``Programs.Special.Boxed
  -- `Rose` is nested through `List`, which `VInductDecl.WF` describes no more than it
  -- describes the nested blocks of `IotaShape`: the block clauses reject it, while its ι
  -- rules -- `Rose.rec`'s and those of the auxiliary recursor over `List Rose` -- still agree
  -- with the kernel's.
  checkNested ``Programs.Trees.Rose
  expectFailure "checkAll on the nested Rose" "ctors_positive" (checkAll ``Programs.Trees.Rose)

-- The projection expansion, on the program records. Each call has the kernel accept
-- `fun ps x => projFn x` as a definition, checks `projTy` against the kernel's `inferProj`, and
-- checks that the expansion applied to a constructor reduces to the field. The level argument is
-- the elimination level of each field: `.succ .zero` for a field in `Type`.
run_meta do
  let type : Nat → Level := fun _ => .succ .zero
  checkProj ``Programs.Records.Run 0 type
  checkProj ``Programs.Records.Run 1 type
  checkProj ``Programs.Records.Point 0 type
  checkProj ``Programs.Records.Point 1 type
  checkProj ``Programs.Records.Rect 0 type
  checkProj ``Programs.Records.Rect 1 type
  checkProj ``Programs.Records.Basket 0 type
  checkProj ``Programs.Records.Basket 1 type
  checkProj ``Programs.Records.Tally 0 type
  checkProj ``Programs.Records.Tally 1 type
  checkProj ``Programs.Records.Pair 0 type
  checkProj ``Programs.Records.Pair 1 type
  -- The level argument is not idle: `Prop` elimination does not type the expansion of a field
  -- in `Type`.
  expectFailure "checkProj Point 0 at the Prop level" "the kernel rejects the expansion"
    (checkProj ``Programs.Records.Point 0 (fun _ => .zero))

end Lean4Lean.Tests.ProgramsCheck
