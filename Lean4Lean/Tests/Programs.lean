/-!
Ordinary Lean programs, run through the kernel.

Every other file in `Lean4Lean/Tests` checks the kernel on data assembled by hand: a
`Declaration` literal, a `VExpr`, a recursor read out of the environment. This one checks it
the way a user does — write a sorting function, state what it returns, and make the kernel
decide the equation. The proofs are `rfl` and `by decide`, so each of them is a reduction
task: to accept the declaration the kernel has to fire the ι rules of the types below and
project the fields of the structures below until the two sides meet.

The file is checked twice, by two kernels that are supposed to agree. `lake build` runs
Lean's own, at elaboration time. `lake exe lean4lean Lean4Lean.Tests.Programs` replays the
same declarations through lean4lean's `Lean4Lean.addDecl`, which is the point: the ι step is
`Lean4Lean.inductiveReduceRec` — the major-premise conversions, then the rule firing in the
extracted `inductiveReduceRecCore` — the projection step is `TypeChecker.Inner.inferProj` /
`reduceProj`, and `Lean4Lean/Tests/ProgramsCheck.lean` then re-runs the same reductions a
third way, through lean4lean's `whnf` and `isDefEq` directly, and validates the ι and
projection *builders* of `Theory/` against these types.

Two rules shape what can be written here.

* No `import`, so that the replay is standalone and drags in neither `batteries` nor `Lean`
  (a module importing `Lean` cannot be replayed with `--fresh`, digama0/lean4lean#17).
* No well-founded recursion. `termination_by` compiles the function to `WellFounded.fix` and
  tags the *generated definition* `@[irreducible]` (`WellFounded.fix` itself is an ordinary
  definition), so it does not reduce in either kernel — a `rfl` on such a definition fails to
  elaborate rather than exercising anything. Recursion here is therefore structural, or
  driven by an explicit `Nat` fuel argument that bounds it from above; a helper consuming two
  arguments at once (`merge`) takes its own fuel. `List.attach`, which the equation compiler
  inserts when recursing under a `List`, drags in the same `WellFounded.fix`, so a nested
  inductive is folded through an explicit mutual helper (`Trees.sumRoseList`) instead.

Sizes are chosen so that the whole file elaborates in well under a second; the reductions are
meant to be real, not large.
-/

namespace Lean4Lean.Tests.Programs

/-! ## Sorting

`List.rec` and `Nat.rec` under composition: `isort` fires the `cons` rule once per element and
`insert`'s rule once per element scanned past, and the two fuelled sorts fire `Nat.rec`'s
`succ` rule once per recursive step on top of that. -/

namespace Sorting

/-- Insert into a sorted list; structural on the list. -/
def insert : Nat → List Nat → List Nat
  | x, [] => [x]
  | x, y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

/-- Insertion sort; structural on the list. -/
def isort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (isort xs)

theorem isort_ex : isort [5, 3, 8, 1, 9, 2, 7, 4, 10, 6] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := rfl

/-- The same reduction under `Decidable.decide` and the `List Nat` equality instance, which is
itself a `List.rec`/`Nat.rec` computation. -/
theorem isort_ne_ex : isort [2, 1] ≠ [2, 1] := by decide

/-- Deal a list into two halves; the `let`-pattern on the result fires `Prod.rec`. -/
def split : List Nat → List Nat × List Nat
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
    let (a, b) := split rest
    (x :: a, y :: b)

/-- Merge two sorted lists; structural on the fuel, which the caller sets to the combined
length, so it never runs out. -/
def merge : Nat → List Nat → List Nat → List Nat
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
    if x ≤ y then x :: merge fuel xs (y :: ys) else y :: merge fuel (x :: xs) ys

/-- Merge sort; structural on the fuel, which bounds the number of halvings. -/
def mergeSort : Nat → List Nat → List Nat
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | fuel + 1, l =>
    let (a, b) := split l
    merge (a.length + b.length) (mergeSort fuel a) (mergeSort fuel b)

theorem mergeSort_ex :
    mergeSort 10 [5, 3, 8, 1, 9, 2, 7, 4, 10, 6] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := rfl

/-- Quicksort; structural on the fuel, which bounds the recursion depth by the list length.
`List.filter` runs a `Decidable` instance per element, so one call reduces three recursors. -/
def qsort : Nat → List Nat → List Nat
  | 0, l => l
  | _ + 1, [] => []
  | fuel + 1, x :: xs =>
    qsort fuel (xs.filter (· < x)) ++ x :: qsort fuel (xs.filter (fun y => ¬ y < x))

theorem qsort_ex : qsort 10 [5, 3, 8, 1, 9, 2, 7, 4, 10, 6] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :=
  rfl

/-- The three sorts agree on the same input, decided by the kernel rather than by a proof. -/
theorem sorts_agree_ex :
    isort [5, 3, 8, 1, 9, 2] = mergeSort 6 [5, 3, 8, 1, 9, 2] ∧
      isort [5, 3, 8, 1, 9, 2] = qsort 6 [5, 3, 8, 1, 9, 2] := by decide

end Sorting

/-! ## Trees

Three shapes of inductive declaration, so that the ι rules being fired are not all of the
same kind: a plain recursive type (`BST`), a *nested* one (`Rose`, recursive under `List`,
whose block gets the auxiliary recursor `Rose.rec_1` over `List Rose`), and a genuinely
mutual one (`Tree`/`Forest`, whose recursors fire on each other's constructors). -/

namespace Trees

inductive BST where
  | leaf : BST
  | node : BST → Nat → BST → BST

/-- Structural on the tree; fires `BST.rec`'s `node` rule once per node on the search path. -/
def BST.insert : BST → Nat → BST
  | .leaf, x => .node .leaf x .leaf
  | .node l y r, x =>
    if x < y then .node (l.insert x) y r
    else if y < x then .node l y (r.insert x)
    else .node l y r

def BST.member : BST → Nat → Bool
  | .leaf, _ => false
  | .node l y r, x => if x = y then true else if x < y then l.member x else r.member x

def BST.inorder : BST → List Nat
  | .leaf => []
  | .node l x r => l.inorder ++ x :: r.inorder

def build (l : List Nat) : BST := l.foldl BST.insert .leaf

theorem inorder_ex :
    (build [5, 3, 8, 1, 9, 2, 7, 4, 10, 6]).inorder = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := rfl

theorem member_pos_ex : (build [5, 3, 8, 1, 9, 2, 7, 4, 10, 6]).member 7 = true := rfl
theorem member_neg_ex : (build [5, 3, 8, 1, 9, 2, 7, 4, 10, 6]).member 11 = false := rfl

/-- A BST built from a list sorts it, decided by the kernel. -/
theorem bst_sorts_ex : (build [5, 3, 8, 1, 9, 2]).inorder = Sorting.isort [5, 3, 8, 1, 9, 2] := by
  decide

/-- Nested: the constructor mentions `Rose` under `List`, so the block carries an auxiliary
recursor over `List Rose` beside `Rose.rec`. -/
inductive Rose where
  | node : Nat → List Rose → Rose

-- Folded through an explicit mutual helper rather than by recursing under `List`, which would
-- go through `List.attach` and hence `WellFounded.fix`.
mutual
def sumRose : Rose → Nat
  | .node v cs => v + sumRoseList cs
def sumRoseList : List Rose → Nat
  | [] => 0
  | t :: ts => sumRose t + sumRoseList ts
end

def sampleRose : Rose := .node 1 [.node 2 [], .node 3 [.node 4 [], .node 5 []]]

theorem sumRose_ex : sumRose sampleRose = 15 := rfl

-- A mutual block: `Tree.rec`'s `node` rule and `Forest.rec`'s `cons` rule fire alternately.
mutual
inductive Tree where
  | node : Nat → Forest → Tree
inductive Forest where
  | nil : Forest
  | cons : Tree → Forest → Forest
end

mutual
def sumTree : Tree → Nat
  | .node v f => v + sumForest f
def sumForest : Forest → Nat
  | .nil => 0
  | .cons t f => sumTree t + sumForest f
end

def sampleTree : Tree :=
  .node 1 (.cons (.node 2 .nil) (.cons (.node 3 (.cons (.node 4 .nil) .nil)) .nil))

theorem sumTree_ex : sumTree sampleTree = 10 := rfl

end Trees

/-! ## List utilities

Eight one-line structural recursions, so that a failure in the `cons` rule shows up as a
short, isolated reduction rather than only inside a sort. -/

namespace ListUtils

def myAppend : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: myAppend xs ys

def myReverse : List Nat → List Nat
  | [] => []
  | x :: xs => myReverse xs ++ [x]

def myMap (f : Nat → Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => f x :: myMap f xs

/-- Fires `List.rec`'s `cons` rule and a `Bool` case split on the predicate. -/
def myFilter (p : Nat → Bool) : List Nat → List Nat
  | [] => []
  | x :: xs => if p x then x :: myFilter p xs else myFilter p xs

def myFoldl (f : Nat → Nat → Nat) : Nat → List Nat → Nat
  | i, [] => i
  | i, x :: xs => myFoldl f (f i x) xs

def myZip : List Nat → List Nat → List (Nat × Nat)
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x, y) :: myZip xs ys

def myTake : Nat → List Nat → List Nat
  | 0, _ => []
  | _, [] => []
  | n + 1, x :: xs => x :: myTake n xs

def myDrop : Nat → List Nat → List Nat
  | 0, l => l
  | _, [] => []
  | n + 1, _ :: xs => myDrop n xs

theorem append_ex : myAppend [1, 2, 3] [4, 5, 6] = [1, 2, 3, 4, 5, 6] := rfl
theorem reverse_ex : myReverse [1, 2, 3, 4, 5] = [5, 4, 3, 2, 1] := rfl
theorem map_ex : myMap (· + 1) [1, 2, 3, 4, 5] = [2, 3, 4, 5, 6] := rfl
theorem filter_ex : myFilter (fun n => decide (n % 2 = 0)) [1, 2, 3, 4, 5, 6] = [2, 4, 6] := rfl
theorem foldl_ex : myFoldl (· + ·) 0 [1, 2, 3, 4, 5] = 15 := rfl
theorem zip_ex : myZip [1, 2, 3] [4, 5, 6] = [(1, 4), (2, 5), (3, 6)] := rfl
theorem take_ex : myTake 3 [1, 2, 3, 4, 5] = [1, 2, 3] := rfl
theorem drop_ex : myDrop 3 [1, 2, 3, 4, 5] = [4, 5] := rfl

theorem map_ne_ex : myMap (· + 1) [1, 2, 3] ≠ [1, 2, 4] := by decide

end ListUtils

/-! ## Nat arithmetic

`Nat.rec`'s `succ` rule against a literal major premise: the kernel first converts the
literal with `Expr.natLitToConstructor` (`Lean4Lean.inductiveReduceRec`) and then fires the
rule, once per unit of input. -/

namespace NatArith

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

def gcdFuel : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | _ + 1, a, 0 => a
  | fuel + 1, a, b + 1 => gcdFuel fuel (b + 1) (a % (b + 1))

def power : Nat → Nat → Nat
  | _, 0 => 1
  | b, n + 1 => b * power b n

def sumRange : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumRange n

theorem fib_ex : fib 15 = 610 := rfl
theorem gcd_ex : gcdFuel 50 48 18 = 6 := rfl
theorem pow_ex : power 3 10 = 59049 := rfl
theorem sumRange_ex : sumRange 100 = 5050 := rfl
theorem fib_ne_ex : fib 15 ≠ 611 := by decide

/-- A 1000-step literal-to-constructor conversion followed by a single rule firing. -/
def isZero : Nat → Bool
  | 0 => true
  | _ + 1 => false

theorem isZero_ex : isZero 1000 = false := rfl

end NatArith

/-! ## Mutual recursion on `Nat`

The equation compiler fuses the block into one `Nat.brecOn` whose motive is a product, so the
same `succ` rule drives both functions; the three theorems pin both branches of it. -/

namespace Parity

mutual
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

theorem even_ex : isEven 20 = true := rfl
theorem odd_ex : isOdd 20 = false := rfl
theorem even_odd_ex : isEven 21 = false := rfl
theorem odd_ne_ex : isOdd 20 ≠ true := by decide

end Parity

/-! ## Records

The projection half. Every field is non-dependent: the `TrProj` of `Theory/Proj.lean` pins the
motive to the constant motive, which is the fragment these structures stay inside. The
interesting cases are the ones where the projected structure is not already a constructor
application — it is the result of a recursive function, and the kernel must fire the ι rules
first and only then project. -/

namespace Records

/-- A run-length code. A real `structure`, not `Prod`, so the projections are this type's own. -/
structure Run where
  val : Nat
  count : Nat
deriving DecidableEq

def encode : List Nat → List Run
  | [] => []
  | x :: xs =>
    match encode xs with
    | [] => [⟨x, 1⟩]
    | ⟨v, c⟩ :: rest => if x = v then ⟨v, c + 1⟩ :: rest else ⟨x, 1⟩ :: ⟨v, c⟩ :: rest

def decode : List Run → List Nat
  | [] => []
  | ⟨v, c⟩ :: rest => List.replicate c v ++ decode rest

def firstRun : List Run → Run
  | [] => ⟨0, 0⟩
  | r :: _ => r

theorem encode_ex : encode [1, 1, 1, 2, 2, 3, 3, 3, 3, 1] = [⟨1, 3⟩, ⟨2, 2⟩, ⟨3, 4⟩, ⟨1, 1⟩] := rfl

theorem roundtrip_ex :
    decode (encode [1, 1, 1, 2, 2, 3, 3, 3, 3, 1]) = [1, 1, 1, 2, 2, 3, 3, 3, 3, 1] := rfl

/-- The structure being projected exists only after `encode` has been reduced: ι first, then
the projection. -/
theorem encode_first_count_ex : (firstRun (encode [1, 1, 1, 2, 2, 3, 3, 3, 3, 1])).count = 3 := rfl
theorem encode_first_val_ex : (firstRun (encode [1, 1, 1, 2, 2, 3, 3, 3, 3, 1])).val = 1 := rfl

/-- A record-typed field: `r.bottomRight.x` is two projections, and the inner one is not the
head constructor of `r`. -/
structure Point where
  x : Nat
  y : Nat
deriving DecidableEq

structure Rect where
  topLeft : Point
  bottomRight : Point
deriving DecidableEq

def Rect.width (r : Rect) : Nat := r.bottomRight.x - r.topLeft.x
def Rect.height (r : Rect) : Nat := r.bottomRight.y - r.topLeft.y
def Rect.area (r : Rect) : Nat := r.width * r.height

def sampleRect : Rect := ⟨⟨1, 1⟩, ⟨5, 9⟩⟩

theorem width_ex : sampleRect.width = 4 := rfl
theorem height_ex : sampleRect.height = 8 := rfl
theorem area_ex : sampleRect.area = 32 := rfl

/-- Explicit constructor/projection round trip. -/
def Point.rebuild (p : Point) : Point := ⟨p.x, p.y⟩

theorem rebuild_ex : Point.rebuild ⟨3, 4⟩ = ⟨3, 4⟩ := rfl

/-- Structure eta, not ι: `p` is a variable, so there is no constructor to reduce, and the two
sides meet only by the kernel's single-constructor eta rule (`TypeChecker.Inner.tryEtaStruct`).
-/
theorem point_eta_ex (p : Point) : p = (⟨p.x, p.y⟩ : Point) := rfl

theorem point_ne_dec : (⟨3, 4⟩ : Point) ≠ ⟨4, 3⟩ := by decide

/-- A `List`-typed field, built by a recursion that projects its own recursive call. -/
structure Basket where
  items : List Nat
  total : Nat
deriving DecidableEq

def buildBasket : List Nat → Basket
  | [] => ⟨[], 0⟩
  | x :: xs =>
    let rest := buildBasket xs
    ⟨x :: rest.items, x + rest.total⟩

theorem buildBasket_ex : buildBasket [1, 2, 3, 4, 5] = ⟨[1, 2, 3, 4, 5], 15⟩ := rfl
theorem buildBasket_items_ex : (buildBasket [1, 2, 3, 4, 5]).items = [1, 2, 3, 4, 5] := rfl
theorem buildBasket_total_ex : (buildBasket [1, 2, 3, 4, 5]).total = 15 := rfl

/-- A parametrised record, projected at two different instantiations. -/
structure Pair (α β : Type) where
  fst : α
  snd : β
deriving DecidableEq

def Pair.swap (p : Pair α β) : Pair β α := ⟨p.snd, p.fst⟩

def natBool : Pair Nat Bool := ⟨3, true⟩
def boolList : Pair Bool (List Nat) := ⟨false, [1, 2, 3]⟩

theorem swap_natBool_ex : natBool.swap = (⟨true, 3⟩ : Pair Bool Nat) := rfl
theorem swap_boolList_ex : boolList.swap = (⟨[1, 2, 3], false⟩ : Pair (List Nat) Bool) := rfl
theorem swap_swap_ex : natBool.swap.swap = natBool := rfl

/-- An accumulator projected out of `List.foldl`, i.e. out of a recursion this file did not
write. -/
structure Tally where
  sum : Nat
  count : Nat
deriving DecidableEq

def step (a : Tally) (x : Nat) : Tally := ⟨a.sum + x, a.count + 1⟩

def summarize (l : List Nat) : Tally := l.foldl step ⟨0, 0⟩

theorem summarize_ex : summarize [1, 2, 3, 4, 5] = ⟨15, 5⟩ := rfl
theorem summarize_sum_ex : (summarize [1, 2, 3, 4, 5]).sum = 15 := rfl
theorem summarize_mean_ex : (summarize [2, 4, 6, 8]).sum / (summarize [2, 4, 6, 8]).count = 5 := rfl

/-- An enumeration: three constructors, no fields, so its ι rules are the degenerate ones. -/
inductive Color where
  | red | green | blue
deriving DecidableEq

def Color.code : Color → Nat
  | .red => 0
  | .green => 1
  | .blue => 2

def Color.cycle : Color → Color
  | .red => .green
  | .green => .blue
  | .blue => .red

theorem color_ex : (Color.red.cycle.cycle.cycle).code = 0 := rfl
theorem color_ne_ex : Color.red ≠ Color.blue := by decide

end Records

/-! ## The other reduction paths of the ι step

`Lean4Lean.inductiveReduceRec` converts a non-constructor major premise before firing a rule:
a `Nat` literal (covered above), a `String` literal, a K-like type, a structure. Each of the
four is a separate branch, as are the arguments after the major premise and the split at the
indices; none of them is reachable through the equation compiler, so the recursors here are
applied by hand. `Quot.lift` is the one computation rule that is not ι at all. -/

namespace Special

/-- `Expr.strLitToConstructor` (`Lean4Lean/Expr.lean`): the major premise is a string literal,
which the kernel replaces by `String.ofList` applied to a `List Char` — and unfolds further,
since as of v4.33 `String` is a `ByteArray` and a validity proof — before `String.rec` can
fire. The recursor is applied by hand because `String.length` and `String.toList` go through
`Expr.proj` instead, which is the other literal case (`Inner.reduceProjCore`). `noncomputable`
only because the compiler refuses to generate code for `String.rec`; the kernel is unaffected.
-/
noncomputable def byteSize : String → Nat :=
  @String.rec (fun _ => Nat) fun bytes _ => bytes.size

theorem byteSize_ex : byteSize "abc" = 3 := rfl

/-- The same literal through `Expr.proj`: `String.toByteArray` is a projection, so this reduces
by `Inner.reduceProjCore`, whose own literal case expands the string. -/
def firstChar : String → Char
  | s => s.toList.headD 'z'

theorem str_length_ex : "abc".length = 3 := rfl
theorem str_first_ex : firstChar "abc" = 'a' := rfl

/-- `toCtorWhenK`: `Eq` is a K-like type, so `Eq.rec` fires on a proof that is only a variable,
never a constructor application. -/
theorem eq_rec_k_ex (h : (2 : Nat) = 2) : @Eq.rec Nat 2 (fun _ _ => Nat) 7 2 h = 7 := rfl

/-- `toCtorWhenStruct`: the major premise of a structure's recursor is eta-expanded into a
constructor application even when it is a variable. `Prod.fst`/`Prod.snd` do not exercise this
— they are `Expr.proj`, which reduces by `reduceProjCore` without ever reaching
`inductiveReduceRec` — so the recursor is applied by hand, to a variable. -/
noncomputable def sumPair (p : Nat × Nat) : Nat :=
  @Prod.rec Nat Nat (fun _ => Nat) (fun a b => a + b) p

theorem sumPair_eta_ex (p : Nat × Nat) : sumPair p = p.1 + p.2 := rfl
theorem sumPair_ex : sumPair (3, 4) = 7 := rfl

/-- The arguments after the major premise, which `inductiveReduceRecCore` re-applies to the
reduct. The equation compiler never builds such a redex — it threads later arguments through
the motive — so this one is written directly: `Nat.rec` here takes a fifth argument past its
major premise. -/
def addFromRec (n m : Nat) : Nat :=
  @Nat.rec (fun _ => Nat → Nat) (fun m => m) (fun _ ih m => Nat.succ (ih m)) n m

theorem addFromRec_ex : addFromRec 3 10 = 13 := rfl

/-- An indexed family, so that the split `inductiveReduceRecCore` makes between the
parameters/motives/minors and the indices is not always at the same place. The values stay
non-dependent. -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

def Vec.sum : Vec Nat n → Nat
  | .nil => 0
  | .cons x xs => x + xs.sum

def v3 : Vec Nat 3 := .cons 1 (.cons 2 (.cons 3 .nil))

theorem vec_sum_ex : v3.sum = 6 := rfl

/-- A `Prop` with one constructor whose field is a proposition: it eliminates large, which is
the clause of `VInductDecl.LargeElim` that the program types above never reach. -/
inductive Boxed (p : Prop) : Prop where
  | mk : p → Boxed p

def Boxed.run {p : Prop} {α : Sort u} (f : p → α) : Boxed p → α
  | .mk h => f h

theorem boxed_ex : Boxed.run (p := (2 : Nat) = 2) (fun _ => 7) (.mk rfl) = 7 := rfl

/-- Quotient computation: `Quot.lift f h (Quot.mk r a) ≡ f a`, which is not an ι rule; the
kernel handles it in `Inner.whnfCore'`, and `Lean4Lean/Quot.lean` is what admits the quotient
constants in the first place. -/
def SameParity (a b : Nat) : Prop := a % 2 = b % 2

theorem quot_ex :
    Quot.lift (fun n => n % 2) (fun _ _ (h : SameParity _ _) => h) (Quot.mk SameParity 7) = 1 :=
  rfl

end Special

end Lean4Lean.Tests.Programs
