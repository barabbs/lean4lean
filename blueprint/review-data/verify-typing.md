# Group `verify-typing` — the Lean.Expr → VExpr translation layer

## What these files are

This group is the bridge between the *real* Lean kernel data structures (`Lean.Expr`,
`Lean.LocalContext`, `Lean.NameGenerator`, `Lean.Name`) and the *model* syntax `VExpr`/`VEnv`
that Carneiro's thesis axiomatises. Nothing here is a thesis theorem; the thesis's judgment
`Γ ⊢ e : α` is `VEnv.HasType` (Theory/), and this group's job is to say, precisely, *which*
real expressions denote which model terms, and to prove that this correspondence survives every
operation the checker performs on a context (weakening, instantiation, abstraction, universe
substitution, environment growth, definitional equality of contexts).

The layering is:

* `Verify/Expr.lean` (1219 lines) — real `Lean.Expr` facts: the packed header bits
  (`hasFVar`, `hasExprMVar`, `looseBVarRange`, …) agree with structural traversal
  (`Verify/Expr.lean:385-549`); application spines are characterised as lists
  (`:641-805`); the lift/instantiate/abstract calculus (`:807-1108`); `LawfulBEq`/`EquivBEq`
  instances so hash tables and `==` are trustworthy (`:13-199`, `:1170-1219`).
* `Verify/Name.lean`, `Verify/NameGenerator.lean` — order properties of `Name.quickCmp` (which
  compares hashes first, so transitivity is non-trivial), and the freshness discipline
  `NameGenerator.Reserves`.
* `Verify/VLCtx.lean` (116 lines) — the translation context. A `VLCtx` is a list of
  `(Option (FVarId × deps), VLocalDecl)`; `VLocalDecl.depth` is 1 for a binder and 0 for a let,
  which is how `let` occupies a source slot but vanishes from the model context `toCtx`.
  `find?` (`Verify/VLCtx.lean:62`) resolves either kind of source variable, lifting as it walks out.
* `Verify/Typing/Expr.lean` (463 lines) — the definitions: `Closed`, `FVarsIn`, `VLCtx.WF`,
  **`TrProjCtor`/`TrProj`**, `TrExprS`/`TrExpr`, the model spellings of the literals, and the
  primitive invariant `VEnv.HasPrimitives` as a name-keyed table `primSpecs` of seven
  `PrimSpec` shapes.
* `Verify/Typing/Lemmas.lean` (2357 lines) — essentially all the metatheory of the translation.
* `Verify/Typing/TrTerm.lean`, `ConditionallyTyped.lean`, `PrimSpec.lean` — three consumers:
  a bundled builder used by the primitive proofs, the conditional invariants the checker's
  monadic specs are stated with, and the single environment-extension theorem for `HasPrimitives`.

Where the thesis does speak, it speaks about the *model*: `Closed`/`FVarsIn` and
`TrExprS.closed`/`fvarsIn` are the syntactic side of Regularity (typesys.tex, `thm:reg`);
the `FVLift'`/`BVLift` families and `TrExprS.weakFV`/`weakBV` are Weakening (`thm:weak`), including
its strengthening direction (item 3) which is exactly where the remaining holes sit; `InstN`/`InstLet`
and `TrExprS.instN`/`instN_let` are Substitution (`thm:subst`); `TrExprS.uniq` is the translation-level
shadow of Unique typing (unique.tex, `thm:utype`).

## The contributed parts

### trproj: `TrProjCtor` / `TrProj` and their transport lemmas

This is the substantial contribution in this group, and it is a real one. On `master`,
`Verify/Typing/Expr.lean` contained

```lean
def TrProj : ∀ (Γ : List VExpr) (structName : Name) (idx : Nat) (e : VExpr), VExpr → Prop := sorry
```

and `Verify/Typing/Lemmas.lean` contained **seven** `sorry` lemmas about it (`weak'`,
`weak'_inv`, `defeqDFC`, `wf`, `uniq`, `instN`, `instL`). The branch replaces the stub by a real
definition (`Verify/Typing/Expr.lean:69-135`) and proves **five** of the seven, leaving
`weak'_inv` (`Lemmas.lean:745`) and `uniq` (`:992`) open but now *documented* with precise
statements of what is missing.

The definition is the right idea. `VExpr` has no projection node, so a source `.proj S i e` is
translated to the application `P_i e` of the recursor expansion

```
P_i = S.rec (uss i) params (fun x : S usS params => F_i[f_j := P_j x]) (fun f => f_i)
```

which is literally the thesis's `inv_x` construction (typesys.tex §"Undecidability of
definitional equality") generalised from `Acc` to an arbitrary single-constructor structure; the
builders live in `Theory/Proj.lean` (`projFn`, `projMotiveBody`, `projFns`, `fieldSelector`).
The nine fields of `TrProjCtor` are each documented with the kernel fact they stand in for, and
the docstring states the scope honestly: single-constructor, non-recursive, non-indexed,
non-mutual, with reflexive/indexed/nested structures declared a *completeness* boundary rather
than a soundness one. That framing is correct and is echoed at the consumer
(`Verify/TypeChecker/InferType.lean:400-407`, where `inferProj.WF` is labelled "not provable as
stated").

Proof quality of the four transport lemmas (`weak'` `:641`, `defeqDFC` `:749`, `mono` `:767`,
`instN` `:1296`, `instL` `:1588`) is good: each is a single `refine` over a record literal, with
the observation — reused four times — that the key, the parameter count, the field index and the
minor arity depend on `fieldTys` only through its *length*, so `List.length_mapIdx` /
`List.length_map` discharge them. `instN` is the one that needed real theory support: the
`CtorHeaded` field exists precisely so that `piBinders_inst_of_ctorHeaded` applies, i.e. so that
substituting inside the telescope cannot create binders. `wf` (`:939`) is *stronger* than the
master stub — it drops the `VExpr.WF env U Γ e` hypothesis, because the major's typing is now a
field — and the corresponding case of `TrExprS.wf` shrinks from `h2.wf (ih hΔ)` to `h2.wf`. That
is a good sign: the definition was chosen so that later proofs get simpler, not harder.

`TrProj.mono` (`:767`) is a genuinely new obligation created by the design: because `TrProj`
now mentions `env`, `TrExprS.mono`'s projection case is no longer trivial. It is discharged
using the iota branch's new `VEnv.LE.pats` field (`Theory/VEnv.lean:50`), which is a nice
cross-branch fit — the projection model depends on the ι registry being monotone, which is
exactly what the ι work added.

Criticisms, in order of weight:

1. **`uniq` is open and its sketch has a gap.** The 8-line docstring at `Lemmas.lean:984-991`
   lists unique typing, type-former injectivity and "functionality of the ι registry" as what is
   needed, and explicitly notes that the key `np+1+1+0` does not exclude reading a two-minor
   recursor as `(np+1)+1+1+0`. But it does not address the per-field level list `uss`: two
   `TrProjCtor` witnesses for the same projection may pick different `uss`, in which case the two
   expansions are different recursor constants at different universe instances, and
   `IsDefEqU` between them is not obviously available. Either the sketch is incomplete or
   `TrProjCtor` needs another field pinning `uss i` to the sort of `F_i`.
2. **`pat` pins a key, not a rule.** `∃ r, env.pats (…).toPattern r` says only that *some*
   reduct is registered. The relation therefore does not determine reduction behaviour on its
   own; `TrEnv.proj_defeq` (`Verify/Environment/Lemmas.lean:1021`, proved) supplies the missing
   kernel-side structure facts. This is acknowledged in the docstring, but a reader should not
   mistake `TrProj` for a complete specification of a projection.
3. **Two redundant existentials.** `np` is `params.length` and `fieldTys` is determined by
   `(ctorName, usS, params)`; keeping both as existentials adds an obligation to every transport
   proof (`params_length := by simpa`, `field_lt := by rw [hlen]`, …).
4. **`weak'_inv` still open**, but for an honest reason: it needs `IsDefEqU.weakN_iff`, which is
   itself `sorry` on master (`Theory/Typing/UniqueTyping.lean:174`). The cost is that
   `TrExprS.weakFV'_inv` (`Lemmas.lean:1169`) and the three `Conditionally*.weakN_inv` lemmas
   stay sorry-dependent — but they were on master too, so this is not a regression.
5. The scope claims about `inferProj`'s Prop gate (`Verify/Typing/Expr.lean:84-89`) are prose
   only; nothing machine-checks them, and both `inferProj.WF_struct` and `inferProj.WF` are
   `sorry`. So `TrProjCtor` is currently a specification with witnesses on hand-built examples
   (`Tests/ProjInhabit.lean`, sorry-free modulo inherited axioms) but no general inhabitation
   theorem.

Two small trproj additions elsewhere are well judged: `Verify/Expr.lean:745-757`
(`getAppFn_mkAppList`, `getAppArgsRevList_mkAppList`, `getAppArgsList_mkAppList`) fills a real
gap in master's spine API — master had only the `mkAppList_getAppArgsList` direction — and both
of the latter two are used at `Verify/TypeChecker/WHNF.lean:50,52`. `TrExprS.mkAppList_inv`
(`Lemmas.lean:2349`) is a clean 8-line inversion used five times in the same WHNF proof; it does
partly duplicate `AppStack.build` twelve lines above it, but in the `List.Forall₂` shape the
caller needs.

### iota: `LocalContext` lookup lemmas, and an `Ordered → OrderedStrong` sweep

The iota-attributed lines in this group are of two kinds.

The first is a self-contained block in `Verify/LocalContext.lean:181-222`: `WF.empty`,
`toList_empty`, `find?_empty`, `empty_map_wf`, `map_wf_mkLocalDecl`, `find?_mkLocalDecl`,
`mkForall_eq_fold`, plus a `DecidableEq FVarId` instance. The design point is stated in the
docstring and is correct: `find?_mkLocalDecl` needs only the *map's* well-formedness, not
freshness, so a chain of six `mkLocalDecl`s can be resolved without six freshness side
conditions. All seven are used, heavily, in `Verify/Environment/Quot.lean` (the `Quot` axiom
shapes). `mkForall_eq_fold` is a one-line corollary of master's `mkBindingList_eq_fold` and is
used nine times. Two placement nits: the `DecidableEq FVarId` instance is a global instance
about `FVarId`, not about `LocalContext`, sitting under a heading about the empty context (and
could have been `instDecidableEqOfLawfulBEq`, as done for `DefinitionSafety` at
`Verify/Expr.lean:51`); and `toList_empty`/`WF.empty` exist only to serve `find?_empty` three
lines later.

The second is purely mechanical: ten lemma signatures in `Typing/Lemmas.lean:1856-1986` and two
in `TrTerm.lean:104,111` changed from `env.Ordered` to `env.OrderedStrong`, with
`wf.constWF` becoming `wf.ordered.constWF`. This is forced — on the iota branch
`HasType.const_inv` and `forallE_inv` (`Theory/Typing/Strong.lean:909-928`) require the strong
environment, because `Ordered.strong` no longer suffices once ι rules can be registered
(`OrderedStrong` bundles `PatsStrongOn`). Nothing is wrong with the propagation itself, but two
things follow. (a) `TrExprS.ofConst`'s docstring (`TrTerm.lean:98-103`) was not updated and
still reads as if ordering alone were needed. (b) Every *use* of these literal lemmas
(`Verify/TypeChecker/Reduce.lean:16`, `IsDefEq.lean:406`, `InferType.lean:420`) now discharges
`OrderedStrong` via `VEnv.WF.orderedStrong`, which calls the admitted `VEnv.WF.patsStrong`
(`Theory/Typing/EnvLemmas.lean:334`). So a hypothesis strengthening in this group quietly
imports a new admission into the checker's literal handling. That is a cost worth stating
explicitly in the write-up, even though the root cause is in the theory group.

## Overall assessment of the contributed parts

**Design.** The `TrProjCtor` choice — model a projection as the recursor expansion, carry the
expansion's typing as a field rather than deriving it, and quantify the expansion data
existentially — is the right one given that `VExpr` has no projection node, and it is the same
device the thesis uses for `Acc`. Carrying typing in the relation is consistent with how master
already treats `app`/`lam`/`forallE`. The choice makes the five transport lemmas easy and makes
`wf` unconditional; it makes `uniq` hard, and the branch is candid about that.

**Proofs.** Short, structured, no tactic soup; each of the four transport proofs reuses the same
`length_mapIdx` observation, which reads as deliberate rather than accidental. Five sorries
closed, two left with precise, honest explanations. No proof in this group is longer than it
needs to be.

**Documentation.** Unusually good — better than master's in the same files. Per-field docstrings
on `TrProjCtor`, scope paragraphs, and "open, and here is exactly what is missing" notes on both
remaining holes. The one doc/code mismatch found is the stale `ofConst` docstring.

**Redundancy / dead code.** Minor: two redundant existentials in `TrProj`; `mkAppList_inv` vs
`AppStack.build`; `toList_empty`/`WF.empty` used once each. Nothing is unused —
every contributed declaration in this group has at least one consumer.

**Are the statements the right ones?** For the five proved lemmas, yes: they are exactly the
master stubs' statements (modulo the two new parameters and the dropped hypothesis in `wf`), so
the consumers did not have to change. For `uniq`, the statement is master's and is probably
right, but the definition may not yet support it (see criticism 1). The real gap is not in this
group at all: `TrProjCtor` has no general inhabitation theorem
(`inferProj.WF_struct` is `sorry`), so the projection model is currently specified and
transported but not yet connected to what the kernel actually accepts.
