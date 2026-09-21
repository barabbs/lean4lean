# Group `verify-level-and-utils`

Files (all relative to the repository root):

| file | lines | attribution |
|---|---|---|
| `Lean4Lean/Verify/Level.lean` | 3880 | 100% master |
| `Lean4Lean/Verify/NormLt.lean` | 364 | 100% master |
| `Lean4Lean/Verify/QSort.lean` | 392 | 100% master (vendored from leanprover/lean4#14658) |
| `Lean4Lean/Verify/EquivManager.lean` | 331 | 100% master |

**None of these files carries a blame file**, i.e. none of the user's `iota` or `trproj` work
touches them. Everything below is a review of upstream (Mario Carneiro's, plus one vendored Lean FRO)
code, included in the blueprint for completeness of coverage. There is **no active `sorry`** in the
group; the single occurrence of the token is inside a dead comment block at `Verify/Level.lean:27`.

---

## 1. What the files do

### 1.1 `Verify/Level.lean` — the universe-level canonical form

This is the largest single file in the project and it verifies something the thesis does *not*
contain. The thesis (`axioms.tex:42-58`) specifies level equality `ℓ ≡ ℓ'` via an algorithmic
inequality judgement `ℓ ≤ ℓ' + n` given by ten inference rules, and (`soundness.tex:22-33`) gives
the semantics `⟦ℓ⟧_v ∈ ℕ` with `⟦imax(ℓ,ℓ')⟧ = 0` when `⟦ℓ'⟧ = 0`. It says nothing about how to
*decide* the judgement. lean4lean's `Lean4Lean/Level.lean` implements a decision procedure based on
an external paper (Yoan Géran, *A Canonical Form for Universe Levels in Impredicative Type Theory*),
and `Verify/Level.lean` proves it correct. So this file is a genuine extension beyond the thesis,
not a formalisation of it.

The algorithm represents a level as a `NormLevel = Std.TreeMap (List Name) Node`: a key is a
*condition set* (the set of parameters that must be nonzero, i.e. the guards of an `imax` chain) and
the node at that key bundles a constant `C(p, c)` and a list of variable sublevels `V(p, x+k)`. The
verification has six phases:

1. **Preliminaries** (1–165). Unrelated facts about core `Level`: `getOffset'` (:29),
   the bit-packed `Level.Data` accessors (:41–:87), `getUndefParam_none` (:101, used by
   `Verify/TypeChecker/InferType.lean:31`), and `substParams'` (:138, used by `Verify/Expr.lean:1128`).
2. **Accumulation and semantics** (166–660). `evalParam`/`evalPath`/`Node.eval`/`NormLevel.eval`
   (:234–:282) interpret the canonical form; `NormLevel.WF` (:390) is the accumulation invariant;
   `normalizeAux_eval` (:575) is the semantic correctness of the traversal.
3. **Subsumption** (660–1290). `subsumeBy`/`subsume`/`minimize` remove dominated sublevels;
   `subsumption_eval` (:1157) shows this is value-preserving, giving `normalize_eval` (:1214), and
   `NormLevel.le_eval` (:1237) is Géran's Theorem 39 (soundness of the inequality test).
4. **Reconstruction** (1290–2250). A `NormLevel` must be turned back into a `Lean.Level`, which means
   choosing an `imax` chain per key. The subtlety, stated beautifully in the docstring at
   `Lean4Lean/Level.lean:183-205`, is that a chain is not free: each edge itself contributes a
   sublevel `V(S', vᵢ, 0)`, so only *admissible* orders (`Dom`/`Feas`/`Adm`, :1616–:1867) may be used,
   and the choice must depend only on the sublevels — hence the lexicographically least admissible
   chain (`lexChain_spec`, :1836). `toTree_eval` (:2217) and `Tree.reify_eval` (:1404) close the loop.
5. **Completeness** (2250–3180). `NormLevel.separation` (:2674) is the converse of Theorem 39: from a
   semantic bound, build a separating valuation and read off a *syntactic* dominator. With
   `subsumption_reduced` (:3542) and `eq_of_hasSub_iff` (:3662) this yields canonicity,
   `normalize_complete` (:3721).
6. **Flat fast path** (2940–3800). 99.8% of real levels contain no essential `imax`; `flatAux` skips
   the map entirely, and `normalize'_eq` (:3793) proves the fast path is transparent.

The end-to-end theorems are `isEquiv'_wf` (:3808), `normalize'_eval` (:3822), `geq'_wf` (:3828),
`isEquivList_wf` (:3837), `normalize'_complete` (:3849), `isEquiv'_complete` (:3861),
`geq'_complete` (:3870).

### 1.2 `Verify/NormLt.lean`

Core Lean's `Level.normalize` sorts the arguments of a `max` with `Array.qsort normLt`. To use the
qsort specification one must know `normLt` is a strict weak order. The file reformulates `normLt` as
an `Ordering`-valued `normCmp` (:65) that compares base then offset, proves the bridge
`normLtAux_eq` (:264) / `normLt_eq` (:345), and derives `normLt_asymm` (:350),
`normLt_le_trans` (:354), `normLt_same_base` (:359). Transitivity goes through `Lean4Lean.Rot`, the
lexicographic-product device shared with `Name.cmp` — a nice reuse, since `normCmp`'s structural
component returns `.eq` on unrelated constructors and so is *not* itself transitive, which is exactly
the case `Rot.then'` was designed for (`Lean4Lean/Std/Ord.lean:25-31`).

### 1.3 `Verify/QSort.lean`

Vendored from an upstream Lean PR. Proves `size_qsort` (:110), `qsort_perm` (:137) and the
sortedness theorems (:348–:390) under `lt_asymm` and `le_trans` hypotheses. Almost entirely
`grind`-driven; the only hand-written argument is `qsort_sort_spec` (:264), which is well commented.

### 1.4 `Verify/EquivManager.lean`

The kernel memoises structural equality with a union-find keyed by `ExprMap` lookup, i.e. by
`Expr`'s `BEq`, which ignores binder names, `mdata` payloads and `proj` structure names. `RelevantEq`
(:10) names that quotient and `RelevantEq.uniq` (:81) proves it is semantically harmless. `M.WF`
(:181) is a small Hoare logic for the state monad; `isEquiv.WF` (:262) is the soundness of the cache;
`isDefEq.WF` (:325) is the entry point consumed all over `Verify/TypeChecker/`.

---

## 2. Assessment

### What is good

- **The documentation in `Verify/Level.lean` is exemplary.** Nearly every nontrivial definition and
  theorem has a docstring that explains *why*, not just *what* — `NormLevel.WF` (:386-:389),
  the reconstruction section header (:1603-:1611), `separation` (:2665-:2673), the flat-path header
  (:2940-:2944), and the `TreeMap`-shape caveats (:3173-:3176, :3736-:3739). This is far above the
  norm for verification code and makes a 3.9k-line file genuinely readable.
- **The statements are the right ones.** `normalize_eval` (:1214) and `normalize_complete` (:3721)
  are stated against the *semantic* `VLevel.eval`, i.e. against the thesis' `⟦ℓ⟧_v`, not against
  some syntactic notion. The soundness/completeness pair for `NormLevel.le` (:1237, :2886) is the
  correct reading of Géran's Theorem 39 plus its converse. `isEquiv.WF` in `EquivManager` proves only
  soundness, which is the right asymmetry for a kernel cache.
- **`separation` (:2674) is a real theorem, proved well.** The separating-valuation construction
  (set the condition set to 1, the sublevel's own variable to a value exceeding every constant and
  offset in the other map, everything else to 0) is the mathematical core of canonicity and is
  written out in ~90 lines with no automation black boxes.
- **The test files earn their keep.** `Tests/Level.lean:20-38` document three real bugs the
  canonicity requirement exposed, including one ("picking the chain by parent pointers into the key
  set") that needs four parameters and size-10 levels to reproduce, and one that made lean4lean reject
  an inductive Lean accepts.

### What is weak

- **Dead code.** `mkData_depth`/`mkData_hasParam`/`mkData_hasMVar` (`Verify/Level.lean:41,58,73`) are
  referenced nowhere; they are also the only consumers of the `Lean.Level.mkData_eq` axiom and
  require a global `allowUnsafeReducibility` hack (:38-39) to elaborate. In `EquivManager`,
  `RelevantEq.symm` (:41), `RelevantEq.trans` (:58) and `M.WF.bind_le` (:205) are unused.
- **A large verified component nothing consumes.** `normalize'` is not called by the kernel at all
  (only by `Tests/Level.lean`). The entire reconstruction layer — `Tree`, `reify`, `lexChain`,
  `Dom`/`Feas`/`Adm`, roughly lines 1290–2250, i.e. a quarter of the file — supports it, as do
  `normalize'_eval` (:3822) and `normalize'_complete` (:3849). Likewise `geq'_wf` (:3828) and
  `geq'_complete` (:3870) are unused even though `geq'` is called at `Inductive/Add.lean:226` (that
  code path simply has no verification yet), and `isEquiv'_complete` (:3861) is unused. Only
  `isEquivList_wf` (:3837) actually reaches the verified type checker. None of this is *wrong* — it
  is forward-looking work — but a reviewer should know that roughly half the file's value is
  currently potential rather than realised.
- **Doc/code mismatches.** `Tests/Level.lean:8-10` still asserts that canonicity of `normalize'` and
  completeness of `isEquiv'`/`geq'` are "*not* proved" — all three are (`:3849`, `:3861`, `:3870`).
  `Verify/LevelStd.lean:155-157` still says the two qsort facts are "currently unproved because
  `Array.qsort` has no specification in the standard library", and names two lemmas
  (`qsort_perm_toList`, `pairwise_qsort_normLt`) that do not exist; the real ones are at
  `Verify/LevelStd.lean:228` and `:234`, resting on `Verify/QSort.lean`.
- **Axiom surface.** Every main theorem of `Verify/Level.lean` factors through two axioms,
  `Std.TreeMap.all_eq_all_toList` and `any_eq_any_toList` (`Verify/Axioms.lean:10,14`), because
  `NormLevel.le`, `NormLevel.addable` and `BEq NormLevel` are all defined via `TreeMap.all`/`any`.
  They are honestly flagged with an upstream issue link, but they are load-bearing for the level
  comparison the kernel performs. `EquivManager` similarly depends on `Lean4Lean.ptrEqExpr_eq`
  (`Lean4Lean/PtrEq.lean:17`), which is unavoidable given the kernel's use of pointer equality.
- **Invariant sprawl.** The end-to-end theorems thread five to seven separate hypotheses about
  `normalize u` by hand (`normalize_sortedVars`, `normalize_nonempty`, `normalize_sorted`,
  `normalize_vars`, `normalize_keys`, `normalize_feas`, `normalize_reduced` — :1222–:1229, :2413,
  :2443, :2524, :1807, :3600). `geq'_complete` (:3870) takes six of them in a single `refine`. A
  bundled invariant would read much better and would make the results easier to reuse.
- **`Std.TreeMap` as the representation costs a whole layer.** Because two maps with the same entries
  need not be the same tree, everything that follows has to be shown to factor through `toList`
  (`normalizeAux_congr` :3204, `subsumption_congr` :3236, `addable_congr` :3753, `feasible_congr`
  :3768, `lexChain_congr` :3772, `toTree_congr` :3785). This is a design consequence, honestly
  documented, but a sorted-association-list representation would have avoided ~150 lines of pure
  bookkeeping and the `BEq NormLevel` awkwardness at :3741.
- **Automation opacity in the two smaller files.** `NormLt.lean`'s `baseCmp_swap` (:97) and
  `normLtAux_eq` (:264) end several cases in bare `grind`/`simp_all`, and `QSort.lean` is
  `grind`-first throughout. This is fine for maintenance but means a human reviewer cannot check the
  argument by reading; it also makes these files brittle against `grind` changes.
- **Namespace hygiene in `QSort.lean`.** It declares four lemmas at `_root_` into `List`/`Array`/
  `Vector` (:58–:103) and registers them plus several core lemmas as global `grind` lemmas (:40–:55,
  :105–:106). Any file importing `Verify/QSort.lean` inherits those `grind` patterns. It also carries
  upstream TODOs ("These attributes still need to be moved to the standard library", :34) into this
  repository, and is the only file in the project using the Lean 4 module system
  (`module`/`public import`/`import all`).
- **Minor overstatement.** `NormLt.lean`'s header says it "shows [`normLt`] is a strict weak order";
  what is exported is asymmetry and transitivity of the negation — exactly what `qsort` needs, but
  not a packaged strict-weak-order statement.

### Relation to the thesis

- `def:lvl-normlevel-eval` (`evalParam`/`evalPath`/`Node.eval`/`NormLevel.eval`, :234–:282)
  interprets normal forms into the thesis' `⟦ℓ⟧_v` (`soundness.tex:22-33`); `evalPath` is precisely
  the `imax` clause generalised to a set of guards.
- `Sub.le` (:2548) and `NormLevel.le_eval`/`le_complete` (:1237, :2886) decide the thesis'
  algorithmic inequality `ℓ ≤ ℓ'` (`axioms.tex:42-58`); `normalize_complete` (:3721) decides
  `ℓ ≡ ℓ'` (`axioms.tex:43`). The `imax` distribution identities used in `normalizeAux_eval` (:575)
  — `imax_max` (:330), `imax_imax` (:334) — are the value-level counterparts of the thesis'
  `imax`-rewriting rules (`axioms.tex:54-57`).
- Nothing in `NormLt.lean`, `QSort.lean` or `EquivManager.lean` corresponds to the thesis; they are
  implementation-fidelity obligations arising from Lean's actual kernel (sorting inside
  `Level.normalize`, and the `isDefEq` memo cache), not from the type theory.

### Verdict on quality

Upstream work, uniformly of high quality. `Verify/Level.lean` is the strongest single artefact in
this group: the right statements, a real mathematical theorem at its centre (`separation`), and
documentation that explains the design choices rather than restating the code. Its weaknesses are
the ordinary ones of a large research-quality file — some dead lemmas, a stale test-file docstring,
hypothesis sprawl, and a substantial verified component (reconstruction/canonicity) that nothing in
the kernel yet uses. `EquivManager.lean` is compact and correctly scoped. `NormLt.lean` is a clean
small file. `QSort.lean` is vendored and should ideally be replaced by a standard-library
specification when one lands.
