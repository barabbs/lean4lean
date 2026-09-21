# Review material extracted from the chapters
Extracted mechanically before the chapters were refurbished into a standalone, schematic blueprint.
The chapters no longer carry review notes, per-chapter "Review notes" and "Contribution summary"
sections, or the issue registry of the status chapter; this file preserves them verbatim (LaTeX source),
keyed by chapter and node label. See also `ISSUES.md` and the per-topic files in this directory.

## syntax.tex

### Node review notes (19)
- `inst:dec-closedn`: The sibling head-shape decidability instances were moved out of this file to \texttt{Lean4Lean/Tests/ShapeDecide.lean} (commit \texttt{ba118fd}, ``file the head-shape decidability instances with the tests'') while this one stayed. That file's module docstring does give the general rationale -- the shape predicates are used as propositions in the theory and only the tests run them -- but says nothing about why \texttt{decClosedN} is the exception, and the exception is the interesting part, since it is the one closedness test a \emph{definition} needs.
- `fam:lift-consn`: Of this four-lemma block only \texttt{consN\_cons} has a consumer (in \texttt{piBinders\_lift'}, \ref{fam:pibinders-stability}). \texttt{liftVar\_consN\_lt} and \texttt{liftVar\_consN\_succ} are unused anywhere in the repository, which makes \texttt{consN\_fixes} dead in effect as well.
- `fam:subst-trunc-orphans`: The \texttt{trproj} branch re-derived \texttt{lift'\_inst\_hi} from \ref{thm:lift-instn-hi} and left this block behind. \texttt{lift\_r\_one} (\srcloc{Lean4Lean/Theory/VExpr.lean}{919}) now has no consumer at all, and the whole chain that fed it died with it: \texttt{Subst.lift\_r\_comm} (911), \texttt{Subst.trunc} (908), \texttt{Subst.Depth.one} (885), \texttt{Subst.Depth.id} (858) and \texttt{Subst.Depth} itself (796) are now mentioned only inside this block -- six declarations. \texttt{Subst.tail\_eq\_lift\_l} was already unused on master. Only \texttt{Subst.lift\_r\_tail} is still used, from \srcloc{Lean4Lean/Theory/Typing/Lemmas.lean}{1005}. All six survive verbatim in \texttt{Experimental/SExpr.lean}, where the same API is proved out and \texttt{lift\_r\_one} is still consumed.
- `thm:subst-instn`: Master already proves \texttt{subst\_inst} (\srcloc{Lean4Lean/Theory/VExpr.lean}{952}), which is exactly the case $n = 0$, and keeps its independent hand proof; the contribution did not fold it in. The docstring says ``under \texttt{m} binders'' while the statement binds $n$.
- `thm:lift-instn-hi`: \texttt{lift'\_inst\_hi} already existed on master at line 903 with a one-line proof from \texttt{lift\_r\_one}. Moving it 115 lines down and re-deriving it is arguably cleaner, but it creates merge-conflict surface on a file otherwise shared verbatim with upstream and orphans the block at \ref{fam:subst-trunc-orphans}. The general form \texttt{lift'\_instN\_hi} has no consumer outside this pair.
- `thm:liftn-subst-liftn`: The docstring correctly identifies the case $i = 0$ as master's \texttt{lift\_subst\_lift} (\srcloc{Lean4Lean/Theory/VExpr.lean}{947}) but does not re-derive it, so that specialisation keeps a separate hand proof; the lemma itself has one consumer, in \texttt{Theory/Proj.lean}.
- `def:lam-telescope`: The consumer of all three \texttt{trproj} additions is a single proof in the verification layer, \srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{1128}: it builds the $\beta$-redex of an $\iota$ rule out of \texttt{rhs.lamBinders} and closes the reconstruction with \texttt{foldr\_lam\_lamBinders} (lines 1133 and 1134). \texttt{lamBinders\_length} is named nowhere, but it is \texttt{@[simp]} and the arity side condition at line 1132 (\texttt{simp [hla]} against \texttt{hla : rhs.lamArity = ...}) is exactly what it discharges, so it should not be called dead. This is the one \texttt{lamBinders} consumer in the repository; nothing in \texttt{Theory/Proj.lean} uses these three.
- `def:head-tests`: The only consumers are the \texttt{Decidable} instances in \texttt{Lean4Lean/Tests/ShapeDecide.lean}, so this is test-support machinery living in a theory file. Also, the docstring ``Head-constructor tests, with their reflections into existentials'' is attached to \texttt{isSort} alone while describing all six declarations.
- `thm:ctorheaded-forallE`: The lemma has no consumer anywhere in the repository, and its docstring states a different proposition than the statement: ``a \texttt{CtorHeaded} type is not a $\Pi$-telescope ending in a variable, so instantiation cannot create new leading binders'' is the motivation for \texttt{piArity\_inst\_of\_ctorHeaded}, which lives some forty lines below.
- `fam:ctorheaded-stability`: \texttt{getAppFn\_instL\_const} (\srcloc{Lean4Lean/Theory/VExpr.lean}{1248}) and \texttt{CtorHeaded.instL} (\srcloc{Lean4Lean/Theory/VExpr.lean}{1256}) are dead: nothing outside this file mentions them. They read as symmetry-driven additions to the \texttt{inst} pair rather than lemmas the projection development needs.
- `fam:const-spine`: \texttt{const\_mkApps\_spine} bundles two independent facts into one conjunction and is only ever consumed as \texttt{.1}/\texttt{.2}; two lemmas would read better. Neither it nor \texttt{eq\_const\_mkApps\_of\_spine} is used outside \texttt{VExpr.lean}.
- `struct:venv`: The dependent type of \texttt{pats} is heavier than that of the other two fields and is what forces the transport in \ref{def:venv-addpat}.
- `def:venv-addpat`: Unlike \texttt{addConst}, \texttt{addPat} cannot fail: there is no freshness or consistency check, so two conflicting reducts for the same pattern are admissible at this layer. That burden is pushed entirely onto block well-formedness and \texttt{VEnv.PatWF} later, and the asymmetry with \texttt{addConst} deserves a comment here. The idiom $\exists\,h : p' = p,\; h \triangleright r' = r$ is correct but unusual; a heterogeneous equality would read more conventionally.
- `struct:vrecrule`: The docstring justifies the extra field carefully: for a nested inductive the constructor a rule fires on need not have the recursor's parameter count (\texttt{Tree.rec\_1} fires on \texttt{List.cons}), and it is honest that the current well-formedness predicate admits only direct blocks, where the two coincide. The field is therefore redundant as data but necessary as specification, and the code says so.
- `struct:vrecursor`: \texttt{k} is recorded but, as its own docstring admits, unused by the theory: the thesis's second $\iota$ rule (K-like reduction on a subsingleton eliminator) is outside the model. The honesty is in the docstring, but the structure still advertises coverage the development does not have.
- `def:getmajoridx`: \texttt{VRecursor.getFirstIndexIdx} has no consumer anywhere. The \texttt{getFirstIndexIdx} occurrences elsewhere in the repository are all Lean's own \texttt{RecursorVal} field on a kernel \texttt{rval} (\srcloc{Lean4Lean/Inductive/Reduce.lean}{84} and \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{29}), plus one mention in a comment in \texttt{Theory/Typing/Pattern.lean}. And \texttt{VEnv.addRecRule} (\srcloc{Lean4Lean/Theory/Inductive.lean}{260}) spells the major index $\texttt{numParams}+\texttt{numMotives}+\texttt{numMinors}+\texttt{numIndices}$ out by hand instead of calling \texttt{getMajorIdx}, although its docstring says ``major at \texttt{getMajorIdx}''.
- `def:meta-ofexpr`: This is the context for the \texttt{trproj} work: the model's syntax has no projection node, and this translator removes projections by \texttt{casesOn} expansion, so projections must be modelled as a reduction relation elsewhere. Defensible, but it means \texttt{VExpr} and \texttt{Lean.Expr} diverge on exactly the construct being verified.
- `def:quot-consts`: Taking the types from real Lean rather than writing them out is economical, but it makes the model's fidelity depend on the ambient Lean version.
- `def:venv-addquot`: The quotient computation rule is registered as a \texttt{VDefEq}, not through the \texttt{pats} registry of \ref{struct:venv}, so after the \texttt{iota} work the model carries two mechanisms for computation rules. This is a follow-up rather than a defect, but nothing in the code says so: \texttt{Theory/Quot.lean} has no docstrings at all, and neither \texttt{VEnv.addPat} nor \texttt{Theory/Typing/Pattern.lean} mentions the quotient rule.

### Section "Contribution summary"

```latex
\section{Contribution summary}

The \texttt{iota} branch contributed 254 lines here, and they are specification design
rather than proof. Three pieces matter. First, the \texttt{pats} field of
\ref{struct:venv} with \ref{def:venv-addpat} and the third clause of
\ref{struct:venv-le}: reduction rules become \texttt{Prop}-valued, pattern-indexed
environment data instead of a fixed clause of the reduction relation, which keeps
environments extensible and monotone; in the monotonicity backbone it costs one new
field (\srcloc{Lean4Lean/Theory/VEnv.lean}{50}) and two rewritten proof terms, the
pairs of \texttt{LE.rfl} and \texttt{LE.trans} becoming triples.
Second, \ref{struct:vrecrule}, \ref{struct:vrecursor}, \ref{def:getmajoridx} and the
\texttt{recs} field of \ref{struct:vinductdecl}: recursors and their computation rules
become data in the model, mirroring \texttt{Lean.RecursorVal} and
\texttt{Lean.RecursorRule} field for field, with the deliberate addition of
\texttt{ctorParams}. Third, the syntactic toolkit at the end of \texttt{VExpr.lean}
(\ref{def:mkapps} to \ref{fam:const-spine}): total telescope and spine readers, plus
biconditionals trading existentials over expression lists for prefix and length tests,
which is what lets the shape predicates of
chapter \ref{chap:inductive} be decidable and therefore testable against the real kernel.
The one load-bearing lemma of that block is the disjointness in \ref{def:ctorheaded}.

The \texttt{trproj} branch contributed 195 lines, all in \texttt{VExpr.lean}, and they
are supporting infrastructure for the projection development of chapter
\ref{chap:proj}. The organising idea is \ref{thm:lift-eq-subst}: since weakening and
instantiation are both substitutions, a builder lemma need only be proved once against
\texttt{subst}. That idea is written down as a section docstring and pays off
immediately in \ref{fam:mkapps-stability}, where one induction yields three corollaries.
What is actually consumed later splits in two. \texttt{Theory/Proj.lean} takes
\ref{thm:lift-eq-subst}, all five lemmas of \ref{fam:subst-liftn-algebra},
\ref{thm:subst-instn}, \ref{thm:liftn-subst-liftn}, the \texttt{subst}, \texttt{inst} and
\texttt{instL} halves of \ref{fam:mkapps-stability}, \texttt{getElem\_bvarsDesc}, and
\texttt{CtorHeaded.inst} and \texttt{piArity\_inst\_of\_ctorHeaded} from
\ref{fam:ctorheaded-stability}. The \emph{verification} layer, not
\texttt{Theory/Proj.lean}, is what consumes \ref{fam:pibinders-stability}
(\srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{652},
\srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{1598},
\srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{1051}),
\texttt{piBinders\_inst\_of\_ctorHeaded}, \texttt{mkApps\_lift'}, and the
$\lambda$-telescope readers of \ref{def:lam-telescope}.
\ref{thm:lift-instn-hi} is consumed only through its $m=0$ case, which
\texttt{Theory/Typing/HeadReduction.lean} already used before the refactor.

What remains open at this layer. The K-like reduction flag of \ref{struct:vrecursor} is
recorded but not modelled, so the thesis's second $\iota$ rule is out of scope. The
quotient computation rule (\ref{def:venv-addquot}) still lives in \texttt{defeqs} rather
than in \texttt{pats}, leaving two mechanisms for computation rules. \texttt{ctorParams}
is redundant as data until nested blocks are admitted. And seven contributed
declarations in this chapter are dead. Five are mentioned nowhere outside their own
statement: \texttt{Lift.liftVar\_consN\_lt}, \texttt{Lift.liftVar\_consN\_succ},
\texttt{VExpr.CtorHeaded.forallE}, \texttt{VExpr.CtorHeaded.instL} and
\texttt{VRecursor.getFirstIndexIdx}. Two more, \texttt{Lift.consN\_fixes} and
\texttt{VExpr.getAppFn\_instL\_const}, survive only by feeding one of those five. The
review notes below list them with line numbers.
```

### Section "Review notes"

```latex
\section{Review notes}

\begin{itemize}
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/VExpr.lean}{919}: dead upstream code
created by the \texttt{trproj} refactor. Master proved \texttt{lift'\_inst\_hi} at
\texttt{master:VExpr.lean:903} with the one-line
\texttt{simp [subst\_lift', lift'\_subst, lift\_r\_one, inst\_eq]}; the branch moved the
lemma to line 1018 and re-derived it from the new \texttt{lift'\_instN\_hi}.
\texttt{lift\_r\_one} now has no consumer anywhere, and with it the whole chain that
existed to feed it: \texttt{Subst.lift\_r\_comm} (911), \texttt{Subst.trunc} (908),
\texttt{Subst.Depth.one} (885), \texttt{Subst.Depth.id} (858) and \texttt{Subst.Depth}
(796) are now mentioned only inside that block. Six declarations. Either keeping
master's proof or deleting the orphaned block would be consistent; leaving both
maximises merge-conflict surface on a file otherwise shared verbatim with upstream
(\ref{fam:subst-trunc-orphans}, \ref{thm:lift-instn-hi}).
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/VExpr.lean}{1232}:
\texttt{VExpr.CtorHeaded.forallE} is unused anywhere in the repository, is proved by
\texttt{:= h} because it is definitionally trivial, and its docstring states a different
proposition than the lemma. The docstring text is the motivation for
\texttt{piArity\_inst\_of\_ctorHeaded}, not for this statement
(\ref{thm:ctorheaded-forallE}).
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/VExpr.lean}{1046}: stale section docstring.
It promises telescope and spine readers ``with their decidability'', but the decidability
instances were relocated to \texttt{Lean4Lean/Tests/ShapeDecide.lean}, so the section
contains no decidability at all.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/VExpr.lean}{753}:
\texttt{Lift.liftVar\_consN\_lt} and \texttt{Lift.liftVar\_consN\_succ} (line 756) have no
consumer, which makes \texttt{Lift.consN\_fixes} (line 745) dead in effect as well. Of
the four-lemma block at lines 744 to 758 only \texttt{consN\_cons} is used
(\ref{fam:lift-consn}).
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/VExpr.lean}{1256}:
\texttt{VExpr.CtorHeaded.instL} and its helper \texttt{getAppFn\_instL\_const} (line 1248)
are dead; nothing outside \texttt{VExpr.lean} mentions them. They look like
symmetry-driven additions to the \texttt{inst} pair rather than lemmas the projection
development needs (\ref{fam:ctorheaded-stability}).
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/VExpr.lean}{1009}: redundancy left
unresolved, and inconsistently. \texttt{subst\_instN} subsumes master's
\texttt{subst\_inst} (line 952) at $n = 0$, and \texttt{liftN\_subst\_liftN} (line 1032)
subsumes master's \texttt{lift\_subst\_lift} (line 947) at $i = 0$ -- its own docstring
says so -- yet both master lemmas keep independent hand proofs, whereas
\texttt{lift'\_inst\_hi} in the same block \emph{was} re-derived. Three analogous pairs,
three different treatments. Additionally \texttt{subst\_instN}'s docstring says ``under
\texttt{m} binders'' while the statement binds $n$
(\ref{thm:subst-instn}, \ref{thm:liftn-subst-liftn}).
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/VExpr.lean}{1133}: the whole
$\lambda$-telescope block -- \texttt{lamBinders}, \texttt{lamBinders\_length},
\texttt{foldr\_lam\_lamBinders} -- has exactly one consumer, a single proof at
\srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{1128}, and
\texttt{lamBinders\_length} is reached only through \texttt{simp} rather than by name.
That is thin, but it is not dead code: the claim that it is should not be made
(\ref{def:lam-telescope}).
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/VExpr.lean}{1295}:
\texttt{const\_mkApps\_spine} bundles two independent facts into one conjunction and is
only ever consumed as \texttt{.1}/\texttt{.2}; together with
\texttt{eq\_const\_mkApps\_of\_spine} it has no consumer outside \texttt{VExpr.lean}
(\ref{fam:const-spine}).
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/VExpr.lean}{1200}: the docstring
``Head-constructor tests, with their reflections into existentials'' is attached to
\texttt{isSort} alone while describing all six declarations; and the whole block exists
only for the decidability instances in the test file (\ref{def:head-tests}).
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/VExpr.lean}{108}: \texttt{decClosedN} stayed
in the theory file while the sibling head-shape instances moved to
\texttt{Lean4Lean/Tests/ShapeDecide.lean} (commit \texttt{ba118fd}). That file's module
docstring explains the general policy but not this exception, which is the part a reader
needs: \texttt{decClosedN} is the one such instance a \emph{definition} depends on, via
the \texttt{if h : ru.rhs.Closed} of \texttt{VEnv.addRecRule}
(\srcloc{Lean4Lean/Theory/Inductive.lean}{258}) (\ref{inst:dec-closedn}).
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/VDecl.lean}{51}:
\texttt{VRecursor.getFirstIndexIdx} is defined and documented but has no consumer
anywhere; every other \texttt{getFirstIndexIdx} in the repository is Lean's own
\texttt{RecursorVal} field on a kernel \texttt{rval}
(\srcloc{Lean4Lean/Inductive/Reduce.lean}{84},
\srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{29} and following), plus one comment in
\texttt{Theory/Typing/Pattern.lean}. Relatedly,
\texttt{VEnv.addRecRule} (\srcloc{Lean4Lean/Theory/Inductive.lean}{260}) spells
\texttt{numParams + numMotives + numMinors + numIndices} out by hand instead of calling
\texttt{VRecursor.getMajorIdx}, though its docstring says ``major at
\texttt{getMajorIdx}'' (\ref{def:getmajoridx}).
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/VDecl.lean}{41}: \texttt{VRecursor.k} records
the K-like-reduction flag but, as its own docstring admits, is unused by the theory; the
thesis's second $\iota$ rule is outside the model. Honest, but the structure advertises
coverage the development does not have, and a reader auditing ``does this model Lean's
$\iota$?'' has to read the docstring to find out (\ref{struct:vrecursor}).
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/VEnv.lean}{44}: \texttt{VEnv.addPat} cannot
fail. Unlike \texttt{addConst} it performs no freshness or consistency check, so
conflicting reducts for the same pattern are admissible at this layer; the invariant is
enforced only later. The asymmetry with \texttt{addConst} deserves a comment here
(\ref{def:venv-addpat}).
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Quot.lean}{11}: after the \texttt{iota} work
the model has two mechanisms for computation rules, since \texttt{quotDefEq} is still a
\texttt{VDefEq} rather than a \texttt{pats} entry. The duplication is nowhere
acknowledged in the code -- \texttt{Theory/Quot.lean} carries no docstrings, and neither
\texttt{VEnv.addPat} nor \texttt{Theory/Typing/Pattern.lean} mentions the quotient rule
(\ref{def:venv-addquot}).
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Quot.lean}{6}: the quotient signatures are
obtained by elaborating the real Lean constants, so the model's fidelity at this point
depends on the ambient Lean version rather than on anything written in the repository
(\ref{def:quot-consts}).
\item \textbf{Low (context, not a defect).} \srcloc{Lean4Lean/Theory/Meta.lean}{12}:
\texttt{ofExpr} rejects \texttt{.proj} (line 46) and \texttt{expandProj} eliminates
projections through \texttt{casesOn} beforehand. \texttt{VExpr} and \texttt{Lean.Expr}
therefore diverge on exactly the construct the \texttt{trproj} branch verifies, which is
why projections are modelled as a reduction relation in chapter \ref{chap:proj} instead
of as syntax (\ref{def:meta-ofexpr}).
\end{itemize}
```

## typing.tex

### Node review notes (10)
- `rule:isdefeq-pat`: The rule builds subject reduction for ι into the judgment. It is false over a merely \texttt{Ordered} environment (see \ref{thm:wf-patsstrong}), so every lemma of \texttt{Lemmas.lean} proved under \texttt{Ordered} describes a relation that may be strictly larger than the thesis's. The debt is discharged only by \texttt{VEnv.WF.patsStrong}, which is \texttt{sorry}. Honestly documented at \srcloc{Lean4Lean/Theory/Typing/Basic.lean}{57}.
- `def:pattyped`: The predicate is existential in $U$, $\Gamma$, $e$, $m_2$ and $B$, and \texttt{Generic} constrains only the holes the reduct \emph{uses}; the index arguments and the constructor's copy of the parameters may be arbitrary terms over $\Gamma$. So a rule can be ``typed'' at one convenient instantiation. The \texttt{Generic} docstring (\srcloc{Lean4Lean/Theory/Typing/Pattern.lean}{181}) says so, but the name \texttt{PatWF} promises more than the predicate delivers.
- `def:ordered`: \texttt{Ordered} no longer implies that \texttt{IsDefEq} is a sensible relation: \texttt{Ordered.defeq} admits arbitrary well-typed definitional axioms, under which a registered ι rule can take a well-typed redex to an ill-typed reduct, while \ref{rule:isdefeq-pat} forces the reduct to be typed anyway.
- `def:ontypes`: \texttt{OnTypes} deliberately says nothing about \texttt{pats}. This is the structural reason the iota branch could not thread its ι obligation through \ref{thm:ordered-induction} and had to rebuild the bootstrap of \ref{thm:wf-strong}.
- `thm:addquot-wf`: The quotient computation rule is modelled as a \texttt{VDefEq}, that is as a $\delta$ rule on closed terms, not as a \texttt{pats} entry, although the thesis calls it an ι rule. This asymmetry with the inductive ι rules is exactly what a proof of \ref{thm:wf-patsstrong} would have to handle.
- `thm:addquot-chain`: This re-derives, through the same \texttt{type\_tac} invocations, the four constant typings that \ref{thm:addquot-wf} already establishes; \texttt{addQuot\_WF} could be a short corollary of this lemma instead.
- `def:patsstrong`: Six positional hypotheses with $E_1$ and $E_0$ explicit, so every call site reads \texttt{hp \_ \_ hpre₀ .rfl \dots rfl rfl hord} (\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{279}; eight such call sites, at lines 279, 282, 291, 293, 305, 308, 316 and 319). Packaging ``$E_0$ is a constant-only extension of a well-formed prefix of $E$'' as one named relation with implicit environments would remove most of the plumbing in lines 137--321. Since the statement is only ever discharged by a \texttt{sorry}, nobody has checked that it is provable in this generality: $E_1$ ranges over prefixes that already contain $\delta$ rules and the quotient rule, so a proof must handle the ι/$\delta$ interaction.
- `thm:addquot-strong`: Hand-unrolled into about 25 lines of \texttt{l1--l5 / d1--d4 / p1--p4 / O1--O4 / I1--I4} with explicit \texttt{.trans} chains: correct, but a sixth quotient constant would require editing every chain. It cannot reuse \ref{thm:foldlm-addconst-strong} only because \texttt{addQuot} is an \texttt{Option} bind chain rather than a fold.
- `thm:wf-patsstrong`: This is the branch's only new \texttt{sorry} and it is load-bearing: through \ref{thm:wf-orderedstrong} and its \texttt{CoeOut} instance, the whole strong system and every result in \texttt{Verify/} that takes a \texttt{VEnv.WF} hypothesis becomes conditional on it (343 constants depend on it, the widest reach of any hole in the non-experimental project). Master's corresponding entry point was proved.
- `thm:wf-orderedstrong`: The coercion is the delivery mechanism for the gap: a reader supplying \texttt{henv : E.WF} where \texttt{OrderedStrong} is expected inherits the \texttt{sorry} with no visible cue, and the file marks this with a bare comment at \srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{342} rather than a docstring on the instance. In practice this is not hypothetical: \texttt{Verify/Primitive.lean} was rewritten from \texttt{Ordered} to \texttt{OrderedStrong} in 31 places on this branch (it had none on master), and \texttt{Verify/Environment/Primitive/*} uses \texttt{ctx.Ewf.orderedStrong} throughout.

### Section "Contribution summary"

```latex
\section{Contribution summary}

Everything contributed in this group belongs to the \texttt{iota} branch (381 lines);
\texttt{trproj} does not touch it. The contribution has three layers.

\emph{The rule and its admissibility condition.} \ref{rule:isdefeq-pat} adds the schematic
ι rule to the judgment, and \ref{def:pattyped} and \ref{def:patwf} say when a rule may be
registered, with \ref{def:ordered} gaining the corresponding \texttt{pat} constructor. The
split into a typing condition and a shape condition is the good idea here: because
\texttt{TemplateHeaded} is monotone (\ref{fam:patwf-mono}) and is recovered from the
environment by \ref{thm:ordered-patwf}, the sort and $\Pi$ inversion lemmas
(\ref{thm:isdefeq-sort-inv}, \ref{thm:isdefeq-foralle-inv}) survive the new rule with a
one-line case each, instead of requiring the open $\Pi$-injectivity of
\ref{thm:injectivity-open}.

\emph{The induction cases.} Nine inductions over \texttt{IsDefEq} gained a \texttt{pat} case
(\ref{thm:isdefeq-closedn}, \ref{thm:isdefeq-mono}, \ref{thm:isdefeq-levelwf},
\ref{thm:isdefeq-weakn}, \ref{thm:isdefeq-instl}, \ref{thm:isdefeq-instn},
\ref{thm:isdefeq-foralle-inv}, \ref{thm:isdefeq-sort-inv} and \ref{thm:isdefeq-istype}), and
three inductions over \texttt{Ordered} gained a one-line one (\ref{thm:ordered-induction} and
the two lemmas of \ref{fam:ordered-entrywf}). They are uniform, one to six lines each, and no
master lemma gained a hypothesis. Each rests on a transport lemma for patterns
(\texttt{liftN\_apply}, \texttt{instN\_apply}, \texttt{instL\_apply} and the
\texttt{Check.Realizes.map\_*} family) proved in Chapter \ref{chap:inductive}.

\emph{The bootstrap.} \ref{def:wfprefix}, \ref{thm:wfprefix-trans}, \ref{thm:vdecl-wf-le},
\ref{def:patsstrong} and the five \texttt{*\_strong} lemmas
(\ref{thm:foldlm-addconst-strong}, \ref{thm:adddefeqs-strong}, \ref{thm:addrules-strong},
\ref{thm:addquot-strong}, \ref{thm:addinduct-strong}) rebuild the entry point into the strong
system of Chapter \ref{chap:metatheory} from \texttt{VEnv.WF} rather than from
\texttt{Ordered}, ending at \ref{thm:wf-strong} and \ref{thm:wf-orderedstrong}.
\ref{thm:addquot-chain} exists to serve \ref{thm:addquot-strong}. The rewrite costs about
200 lines where master needed twelve, and the cost is intrinsic: \texttt{PatsStrong} is not a
property \ref{thm:ordered-induction} can carry, because \texttt{OnTypes}
(\ref{def:ontypes}) says nothing about registered rules.

What remains open is one statement, \ref{thm:wf-patsstrong}, and it is the statement the
thesis calls easy. Until it is proved, every theorem in this repository that assumes
\texttt{VEnv.WF} and uses the strong system is conditional on it. The honest framing is that
master had left the inductive layer unspecified (\texttt{VInductDecl.WF} and
\texttt{VEnv.addInduct} were \texttt{sorry}-ed definitions and \texttt{addInduct\_WF} a
\texttt{sorry}-ed theorem), and the branch trades those for a real specification plus one
open lemma; that is a good trade, but the resulting hole is wider than any it replaced.
```

### Section "Review notes"

```latex
\section{Review notes}

\begin{itemize}
\item \textbf{High.} \srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{334}:
\texttt{VEnv.WF.patsStrong} is \texttt{sorry}. Combined with the
\texttt{CoeOut (VEnv.WF E) E.OrderedStrong} instance at line 343, every \texttt{VEnv.WF}
hypothesis silently yields the strong-system hypotheses, so the entire strong system and the
whole \texttt{Verify/} typechecker-correctness layer become conditional on it
(\texttt{Verify/Primitive.lean} alone mentions \texttt{OrderedStrong} or
\texttt{orderedStrong} in 30 places added on this branch; it had none on master). On master
the corresponding entry point, \texttt{Ordered.strong}, was a proved theorem in a
\texttt{sorry}-free file.
\item \textbf{High.} \srcloc{Lean4Lean/Theory/Typing/Basic.lean}{60}: \texttt{IsDefEq.pat}
asserts the reduct at the redex's type with no typing premise on the reduct, that is, it
builds subject reduction for ι into the judgment. The author's own counterexample
(\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{327}) shows the assumption is false over a
merely \texttt{Ordered} environment, so every lemma of \texttt{Lemmas.lean} proved under
\texttt{Ordered} characterises a relation that may be strictly larger than the thesis's. The
strong system's \texttt{IsDefEqStrong.pat}
(\srcloc{Lean4Lean/Theory/Typing/Strong.lean}{89}) has the correct shape. Any claim of the
form ``lean4lean proves $X$ about \texttt{IsDefEq}'' must be qualified by
\texttt{VEnv.WF.patsStrong}.
\item \textbf{High (pre-existing, master).}
\srcloc{Lean4Lean/Theory/Typing/Injectivity.lean}{11}: the three inversion principles of
\ref{thm:injectivity-open} are \texttt{sorry} and the whole file is nothing else. They are
what a proof of \texttt{patsStrong} is said to need, so the iota branch's open obligation
rests on an already open foundation, and \ref{thm:foralle-inv-derived} now carries two
independent gaps.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Typing/Basic.lean}{92}:
\texttt{VEnv.PatTyped} is existential in $U$, $\Gamma$, $e$, $m_2$ and $B$, and
\texttt{Pattern.RHS.Generic} constrains only the holes the reduct \emph{uses}; the index
arguments and the constructor's copy of the parameters are arbitrary terms over $\Gamma$. So
\texttt{PatWF}, and hence \texttt{Ordered.pat}, admits a rule that typechecks only at one
convenient instantiation. The weakness is documented at
\srcloc{Lean4Lean/Theory/Typing/Pattern.lean}{181}, but the name promises more than the
predicate delivers.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Typing/Basic.lean}{62}: the
\texttt{Pattern.Check}/\texttt{Realizes} side-condition machinery threaded through
\texttt{IsDefEq.pat} and nine induction cases is exercised only at the trivial check. The one
registration point, \texttt{VEnv.addRecRule} (\srcloc{Lean4Lean/Theory/Inductive.lean}{257}),
hard-codes \texttt{Check.true} (line 264), and every lemma about it repeats that constant
(\srcloc{Lean4Lean/Theory/Typing/InductiveParams.lean}{103},
\srcloc{Lean4Lean/Theory/Typing/InductiveLemmas.lean}{630},
\srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{688}); K-like reduction, the rule that
would need a definitional side condition, is explicitly not modelled
(\srcloc{Lean4Lean/Theory/Inductive.lean}{332}). Seven lemmas around
\texttt{Check.OK}/\texttt{Check.Realizes} (\texttt{OK.map}, \texttt{Realizes.toOK},
\texttt{OK.exists\_realizer}, \texttt{map\_liftN}, \texttt{map\_instN}, \texttt{map\_instL},
\texttt{map\_subst}) and one premise per induction case support a side condition that no
registered rule yet uses.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{130}:
\texttt{VEnv.PatsStrong} is a six-hypothesis statement with both environments explicit,
making all eight call sites read \texttt{hp \_ \_ hpre₀ .rfl \dots rfl rfl hord} (lines 279,
282, 291, 293, 305, 308, 316, 319) and forcing the \texttt{*\_strong} lemmas to repeat the same
$\le$/\texttt{defeqs}/\texttt{pats} composition three or four times. A single named relation
with implicit environments would materially shorten lines 137--321. Since the statement is
only ever discharged by \texttt{sorry}, it is also unverified that it is provable in this
generality.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{188}:
\texttt{addQuot\_strong} hand-unrolls \texttt{addQuot}'s five steps into about 25 lines of
explicit \texttt{.trans} chains. Correct but brittle: any change to the quotient block
requires editing every chain. It cannot reuse \texttt{foldlM\_addConst\_strong} only because
\texttt{addQuot} is written as an \texttt{Option} bind chain rather than a fold.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Typing/QuotLemmas.lean}{19}:
\texttt{addQuot\_chain} re-derives, through the same \texttt{type\_tac} invocations, the four
quotient-constant typings that \texttt{addQuot\_WF} (line 7) already establishes. The two
proofs duplicate each other; \texttt{addQuot\_WF} could be a short corollary of
\texttt{addQuot\_chain}.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Typing/Basic.lean}{58}: the docstring of
\texttt{IsDefEq.pat} cites \texttt{Params.pat\_wf} unqualified and forward. The intended
declaration is the class field \texttt{Lean4Lean.VEnv.Params.pat\_wf}
(\srcloc{Lean4Lean/Theory/Typing/ChurchRosser.lean}{20}), in a module that imports
\texttt{Basic.lean} and so is not in scope there, and an unrelated
\texttt{Lean4Lean.Params.pat\_wf} exists in \srcloc{Lean4Lean/Experimental/SExpr.lean}{30}.
Minor, but this docstring is the main explanation of the branch's central design decision.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Typing/QuotLemmas.lean}{7}: the quotient
computation rule is registered as a \texttt{VDefEq} (a $\delta$ rule on closed terms) rather
than as a \texttt{pats} entry, although the thesis classifies it as an ι rule. The
asymmetry is invisible in this chapter but is part of what a proof of
\ref{thm:wf-patsstrong} must handle, since a well-formed prefix carries it.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Typing/Lemmas.lean}{267}: \texttt{OnTypes} says
nothing about \texttt{pats}, so \ref{thm:ordered-induction} propagates nothing about
registered rules. This is not a defect but it is the structural cause of the 200-line
rewrite in \texttt{EnvLemmas.lean}, and it is worth recording that a \texttt{pats}-aware
\texttt{OnTypes} was not attempted.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{323}: the route a proof
of \texttt{patsStrong} would take should be checked for circularity before it is attempted.
\texttt{ChurchRosser.Params} requires \texttt{VEnv.WF} and
\texttt{InductiveParams.toParams} builds it from \texttt{VEnv.WF.pat\_*} facts; as of this
branch \texttt{ChurchRosser.lean} does not mention \texttt{OrderedStrong}, so the route looks
open rather than circular, but nothing records that check.
\item \textbf{Low (master).} \srcloc{Lean4Lean/Theory/Typing/Meta.lean}{37}:
\texttt{type\_tac} is a brute-force \texttt{first} chain carrying its own TODO (``write an
actual tactic''). Master ran it on the five closed terms of the quotient block; the branch
made it markedly more load-bearing, adding six call sites in \ref{thm:addquot-chain} (which
re-runs it over the goals \ref{thm:addquot-wf} already closes) and a hundred in the
contributed \srcloc{Lean4Lean/Verify/Environment/Quot.lean}{1}, where it builds the
\texttt{TrExprS} derivations for the four quotient constant types.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Typing/Injectivity.lean}{23}:
\texttt{IsDefEqU.forallE\_inv} is byte-identical to master (the whole file is), yet it now
carries a second, independent \texttt{sorry} source. Its proof calls
\texttt{IsDefEq.strong}, whose environment hypothesis the branch changed from
\texttt{Ordered} to \texttt{OrderedStrong}
(\srcloc{Lean4Lean/Theory/Typing/Strong.lean}{805}); the \texttt{CoeOut} instance supplies
the difference from \ref{thm:wf-patsstrong} without a visible change at the call site. This
is the propagation mechanism of the first item, observed on an unmodified master proof.
\end{itemize}
```

## metatheory.tex

### Node review notes (13)
- `inductive:isdefeqstrong-pat`: the check list is specified by \texttt{Pattern.Check.Realizes}, which constrains only the two term components of each triple and leaves the type component free; the rule then asks for a typed equality at that free type. Sound, but $chk$ is not determined by $(p, r, m_1, m_2)$, so two derivations of the same rule instance may carry different $chk$.
- `def:equptolevels`: only \texttt{EqUpToLevels.instL} was touched on the \texttt{iota} branch, by a one-line \texttt{pat} case at 278 taking the left components of the two induction hypotheses.
- `thm:equptolevels-defeq`: the \texttt{pat} case rebuilds the same rule instance rather than transporting it. That is correct here because only the two endpoints move, but it does rely on the rule's own components being untouched by the level change.
- `struct:orderedstrong`: this replaces master's situation, where \texttt{Ordered.strong : Ordered env} $\to$ \texttt{OnTypes env (EnvStrong env)} was a proved theorem and \texttt{IsDefEq.strong} needed only \texttt{Ordered env}. Here \texttt{OrderedStrong} is reachable from \texttt{VEnv.WF} only through \texttt{VEnv.WF.orderedStrong} (\ref{thm:wf-orderedstrong}), whose \texttt{patsStrong} component is admitted (\ref{thm:wf-patsstrong}). The change is forced by adding $\iota$ to \texttt{IsDefEq} and it is documented, but it is the single largest liability of the contribution.
- `instance:coeout-orderedstrong`: combined with the sibling instance \texttt{CoeOut (VEnv.WF env) env.OrderedStrong} (\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{343}) this makes the new, admitted hypothesis invisible at use sites: \texttt{UniqueTyping.lean} is byte-identical to master yet changed from \texttt{Ordered}-dependent to \texttt{patsStrong}-dependent. Convenient, but it hides a proof obligation.
- `def:hastypestratified`: no \texttt{pat} handling is needed here: \texttt{HasTypeStratified} mirrors the rules of \texttt{HasTypeStrong}, none of which is an $\iota$ rule, and its \texttt{defeq} premise carries an \texttt{IsDefEq} derivation that is never analysed.
- `thm:unique-typing`: textually untouched by the branches, but its \texttt{henv : VEnv.WF} is now coerced to \texttt{OrderedStrong}, so it silently acquired the \texttt{patsStrong} dependency; on master it was \texttt{Ordered}-dependent only.
- `class:cr-params`: the class has exactly one construction, \texttt{VEnv.toParams} (\srcloc{Lean4Lean/Theory/Typing/InductiveParams.lean}{393}), and its specialisation \texttt{inductParams} (line 420); both are \texttt{@[reducible] def}s rather than \texttt{instance}s, so a \texttt{Params} has to be supplied by hand at every use. \texttt{toParams} takes its \texttt{extra\_pat} as the hypothesis \texttt{DefEqsAsPats}; that hypothesis fails as soon as the environment contains a \texttt{def} or the quotient rule, because those live in \texttt{defeqs} and not in \texttt{pats}. So the whole Church--Rosser development, and with it the standardization and inference results of the next section, currently applies only to environments built from axioms and inductives.
- `axiom:cr-params-pat-env`: the docstring at \srcloc{Lean4Lean/Theory/Typing/ChurchRosser.lean}{30} justifies the field by \texttt{extra\_pat} (``as every definitional axiom is realised by one''), but the two fields are logically independent: \texttt{extra\_pat} is about \texttt{env.defeqs}, \texttt{pat\_env} about \texttt{env.pats}, and neither implies the other. The comment reads as if \texttt{pat\_env} were derivable.
- `thm:normaleq-trans`: \texttt{meas}, \texttt{meas\_liftN} and \texttt{meas\_lift} are \texttt{private} (line 389), so the measure cannot be reused from outside the file.
- `thm:cparred-exists`: the case split uses \texttt{Classical.byCases}; harmless, but it makes the confluence development classical.
- `def:parredext`: not in the thesis; a Lean-specific device for handling the $\eta$ rules inside the confluence proof.
- `fam:hr-pattern-shape`: both are declared inside \texttt{namespace Lean4Lean.VEnv}. That is right for \texttt{Params.simple\_app}, since \texttt{Params} is \texttt{Lean4Lean.VEnv.Params}, but not for the first: \texttt{Subpattern} lives at \texttt{Lean4Lean.Subpattern} while the lemma is \texttt{Lean4Lean.VEnv.Subpattern.varN\_const}, so dot notation on a \texttt{Subpattern} hypothesis will not find it.

### Section "Contribution summary"

```latex
\section{Contribution summary}

The \texttt{iota} branch touches two of the four files of this chapter, adding 164 lines to
\texttt{Strong.lean} and 9 to \texttt{ChurchRosser.lean}; \texttt{UniqueTyping.lean} and
\texttt{HeadReduction.lean} are byte-identical to master. The work is the follow-on half of
the new \texttt{IsDefEq.pat} rule (\ref{rule:isdefeq-pat}): once $\iota$ reduction is a rule of
the declarative judgment, the metatheory spine has to be re-proved with it.

What was added, in four pieces. First, the strong rule \ref{inductive:isdefeqstrong-pat},
which mirrors \ref{rule:isdefeq-pat} and adds one premise, the typing of the reduct. This is a
design decision, not bookkeeping: it puts subject reduction for the rule into the derivation
instead of deriving it afterwards, and it is the reason the \texttt{pat} cases of
\ref{thm:strong-foralle-inv}, \ref{thm:strong-hastype-prime}, \ref{def:equptolevels},
\ref{thm:equptolevels-defeq} and \ref{thm:strong-substeq} close at all, each in one to four
lines: those are the five proofs that need an induction hypothesis for the right-hand side.
\ref{thm:strong-istype}, by contrast, reads its \texttt{pat} case off the redex annotation
alone. It is exactly parallel to
the annotations master already carries on \texttt{beta} and \texttt{extra}
(\ref{def:isdefeqstrong}). Second, a \texttt{pat} case in each of the eleven structural
inductions over the strong judgment: \ref{thm:strong-weakn}, \ref{thm:strong-defeq},
\ref{thm:strong-mono}, \ref{def:equptolevels}, \ref{thm:strong-instl},
\ref{thm:strong-instn}, \ref{thm:strong-foralle-inv}, \ref{thm:strong-istype},
\ref{thm:equptolevels-defeq}, \ref{thm:strong-hastype-prime} and \ref{thm:strong-substeq}.
Each follows one recipe, commute the operation with \texttt{Pattern.RHS.apply}, transport the
match and the realizer, map the check triples, and each rests on the transport lemmas
\ref{family:pattern-transport-iota}, which live in \texttt{Pattern.lean} where they belong.
Third, the new environment hypothesis \ref{def:patstrong}, \ref{def:patsstrongon} and
\ref{struct:orderedstrong}, stated per rule so that the obligation can be discharged rule by
rule, with the coercion \ref{instance:coeout-orderedstrong} to keep call sites unchanged; and
with it the decomposition of master's \texttt{Ordered.strong} into \ref{thm:envstrong-mono},
\ref{thm:envstrong-of-hastype}, \ref{thm:ontypes-addconst}, \ref{thm:ontypes-adddefeq} and
\ref{thm:ontypes-addpat}, so that the induction over the environment construction can move to
\texttt{EnvLemmas.lean} (\ref{thm:wf-strong}), where \texttt{pats} is under control. All five
pieces have consumers there; none is dead. Fourth, in \texttt{ChurchRosser.lean}, the class
field \ref{axiom:cr-params-pat-env} and the five-line \texttt{pat} case of
\ref{thm:isdefeq-church-rosser}, which takes one \texttt{ParRed.extra} step after converting
the rule's \texttt{Realizes} witness to a \texttt{Check.OK}.

How it connects. The choke point is \ref{thm:isdefeq-strong}: on master it needed
\texttt{Ordered env}, a proved consequence of well-formedness, and on this branch it needs
\ref{struct:orderedstrong}, which reaches \texttt{VEnv.WF} only through
\ref{thm:wf-orderedstrong}. Everything in this chapter that routes through the strong system
inherits that hypothesis: all of \ref{thm:unique-typing} and its corollaries, the inversion
lemmas \ref{fam:strong-inversions}, the substitution results
\ref{thm:strong-substeq} and \ref{thm:isdefeq-substdf}, and through those most of
\texttt{ChurchRosser.lean} and \texttt{HeadReduction.lean}.

What remains open. The \texttt{patsStrong} component of \ref{thm:wf-orderedstrong} is
\texttt{sorry} (\ref{thm:wf-patsstrong}), so every consequence of \ref{thm:isdefeq-strong} is
conditional; this is real mathematics, subject reduction for $\iota$, and it cannot be avoided
once \ref{rule:isdefeq-pat} exists. \ref{axiom:cr-params-pat-env} is discharged only by the
single \texttt{Params} instance \ref{def:indparams-toparams}, which exists only for
environments with no \texttt{def} and no quotient rule, so the $\iota$ case of
\ref{thm:isdefeq-church-rosser} is today exercised on no realistic environment. And
independently of the branch, the two \texttt{sorry}s in \ref{thm:normaleq-parred} and the one
in \ref{thm:isdefequ-weakn-iff} are master's, and they leave Church--Rosser, standardization
and \ref{thm:infertype-exists} unproved.
```

### Section "Review notes"

```latex
\section{Review notes}
\label{sec:metatheory-review}

\begin{itemize}
\item \textbf{High.} \srcloc{Lean4Lean/Theory/Typing/Strong.lean}{679}:
\ref{struct:orderedstrong} makes the environment hypothesis of the strong system
non-derivable. Master proved \texttt{Ordered.strong : Ordered env} $\to$
\texttt{OnTypes env (EnvStrong env)} outright; \texttt{OrderedStrong} additionally demands
\texttt{PatsStrongOn} and is obtained from \texttt{VEnv.WF} only through
\texttt{VEnv.WF.orderedStrong} (\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{339}), whose
\texttt{patsStrong} component is \texttt{sorry}
(\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{334}). The theorems of \texttt{Strong.lean}
are themselves still free of \texttt{sorryAx}, because they take \texttt{OrderedStrong} as a
hypothesis; the taint appears at every call site that discharges it from \texttt{VEnv.WF},
which is all of \texttt{UniqueTyping.lean} and through it \texttt{ChurchRosser.lean},
\texttt{HeadReduction.lean} and the \texttt{Verify} layer. Several of those were already
\texttt{sorry}-dependent through \texttt{Injectivity.lean} on master; what is new is a second,
independent dependency. The gap is documented and is unavoidable once \texttt{IsDefEq.pat}
exists, but it must be stated in every claim about what this chapter proves.
\item \textbf{High.} \srcloc{Lean4Lean/Theory/Typing/ChurchRosser.lean}{1193}:
\texttt{NormalEq.parRed} contains two \texttt{sorry}s (lines 1193 and 1212), both in the case
where a rule step (\texttt{ParRed.extra}, that is $\iota$ or $\delta$) meets a
\texttt{constDF} respectively an \texttt{appDF} normal equality. This is the thesis' Lemma
\texttt{thm:gg\_compat} and the load-bearing step of Church--Rosser, so
\texttt{ParRedS.church\_rosser}, \texttt{CRDefEq.trans}, \texttt{IsDefEq.church\_rosser},
\texttt{IsDefEq.reduce\_sort}, \texttt{IsDefEq.reduce\_forallE} and \texttt{InferType.exists}
are all unproved. The \texttt{sorry}s are master's, but the \texttt{iota} \texttt{pat} rule
routes more content through them.
\item \textbf{High.} \srcloc{Lean4Lean/Theory/Typing/UniqueTyping.lean}{174}: the forward
direction of \texttt{IsDefEqU.weakN\_iff} is \texttt{sorry} (master). It is used by
\texttt{NormalEq.weakN\_inv\_DFC}, \texttt{ParRed.weakN\_inv}, \texttt{hasType\_app\_bvar0},
\texttt{IsDefEq.skips}, \texttt{OnCtx.weakN\_inv} and the whole
\texttt{weakN\_iff}/\texttt{weak'\_iff} family, hence by most of \texttt{ChurchRosser.lean}
and \texttt{HeadReduction.lean}.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Typing/ChurchRosser.lean}{30}: the docstring
of \texttt{Params.pat\_env} justifies the field by \texttt{extra\_pat} (``as every
definitional axiom is realised by one''), but the two fields are logically independent:
\texttt{extra\_pat} speaks about \texttt{env.defeqs}, \texttt{pat\_env} about
\texttt{env.pats}, and neither implies the other. The comment reads as if \texttt{pat\_env}
were derivable.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Typing/ChurchRosser.lean}{12}: the
\texttt{Params} class has exactly one construction, \texttt{VEnv.toParams}
(\srcloc{Lean4Lean/Theory/Typing/InductiveParams.lean}{393}) with its specialisation
\texttt{inductParams} (line 420), and it requires
\texttt{DefEqsAsPats} and therefore exists only for environments with no \texttt{def} and no
quotient rule. The Church--Rosser development, and with it the standardization and inference
results of \texttt{HeadReduction.lean}, currently applies to no realistic environment. This
belongs in the blueprint and not only in the \texttt{DefEqsAsPats} docstring.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Typing/Strong.lean}{684}: the
\texttt{CoeOut (OrderedStrong env) env.Ordered} instance together with its sibling
\texttt{CoeOut (VEnv.WF env) env.OrderedStrong}
(\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{343}) makes the new,
\texttt{sorry}-backed hypothesis invisible at use sites: \texttt{UniqueTyping.lean} is
byte-identical to master yet changed from \texttt{Ordered}-dependent to
\texttt{patsStrong}-dependent. Convenient, but it hides a proof obligation.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Typing/Strong.lean}{672}: the deferred
obligation is heavier than ``the $\iota$ rules of the final environment preserve types''.
\texttt{PatsStrongOn} is stated for one environment, while the \texttt{EnvLemmas} side
\texttt{VEnv.PatsStrong} (\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{130}) quantifies
over every well-formed prefix and every constant-only extension of it traversed by the
strengthening induction. The split is deliberate and documented, but a future proof of
\texttt{VEnv.WF.patsStrong} has to establish the quantified form.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Typing/Strong.lean}{89}: the check list of
\texttt{IsDefEqStrong.pat} is specified by \texttt{Pattern.Check.Realizes}, which constrains
only the two term components of each triple and leaves the type component arbitrary; the rule
then demands a typed equality at that arbitrary type. Sound, but $chk$ is only partially
determined by $(p, r, m_1, m_2)$, so two derivations of the same rule instance can carry
different check lists.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Typing/HeadReduction.lean}{29}:
\texttt{Subpattern.varN\_const} is declared inside \texttt{namespace Lean4Lean.VEnv}, so its
full name is \texttt{Lean4Lean.VEnv.Subpattern.varN\_const} even though \texttt{Subpattern}
lives at \texttt{Lean4Lean.Subpattern}; dot notation on a \texttt{Subpattern} hypothesis will
not find the lemma (master). Its neighbour \texttt{Params.simple\_app} is unaffected, since
\texttt{Params} does live in that namespace.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Typing/ChurchRosser.lean}{22}: the
\texttt{Params} field \texttt{pat\_app\_l} is never consumed. No proof in
\texttt{ChurchRosser.lean} or \texttt{HeadReduction.lean} mentions it; its only occurrences
outside the class are the obligation \texttt{VEnv.WF.pat\_app\_l}
(\srcloc{Lean4Lean/Theory/Typing/InductiveParams.lean}{297}) and the line of
\texttt{toParams} that discharges it. The field is master's, but the \texttt{iota} branch pays
for it, since the instance has to prove it for \texttt{env.pats}.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Typing/ChurchRosser.lean}{632}: a ten-line
commented-out \texttt{IsDefEqU.applyL} draft (lines 632 to 641) is left in the file (master).
\item \textbf{Low, documentation.} \srcloc{Lean4Lean/Theory/Typing/Strong.lean}{659}: the new
declarations are documented unusually well for this codebase, and the docstrings explain why
rather than restating the statement, but their density of cross-references means a reader has
to hold \texttt{Strong.lean}, \texttt{EnvLemmas.lean}, \texttt{Pattern.lean} and
\texttt{InductiveParams.lean} in view at once to check a single claim.
\end{itemize}
```

## inductive.tex

### Node review notes (41)
- `def:ind-mentions-const`: It mirrors the kernel's \texttt{hasIndOcc} (\srcloc{Lean4Lean/Inductive/Add.lean}{118}), which searches the whole term, so the two agree. The Boolean copy exists only so that \texttt{Tests/ShapeDecide.lean} can \texttt{decide} the shape predicates; the \texttt{Decidable} instance built from \texttt{mentionsConst\_iff} lives there, not beside the definition, a placement the test file's header states and defends.
- `def:ind-ctor-result`: The thesis has one argument sequence where the model fixes the first \texttt{nparams} arguments to be the parameter variables. This is a deliberate move towards the kernel and is documented as such.
- `def:ind-valid-ind-app`: The kernel's \texttt{isValidIndAppIdx} (\srcloc{Lean4Lean/Inductive/Add.lean}{157}) additionally checks the exact arity \texttt{args.size == nparams + nindices[i]}. The model drops it and so accepts a former over-applied in its index positions. Such a field would be rejected later by \texttt{WF.universes}, so this is imprecision rather than a hole, but the docstring advertises the predicate as mirroring \texttt{isValidIndApp?} and it does not.
- `def:ind-field-positive`: Two deviations. The kernel reduces the field type and each binder domain to weak head normal form (\texttt{checkPositivity}, \srcloc{Lean4Lean/Inductive/Add.lean}{184}) whereas the model reads manifest binders only, so the model is strictly \emph{stricter} than the kernel. Conversely the thesis forbids a recursive argument from being referred to by later arguments and the model, like the kernel, does not.
- `def:ind-field-in-indices`: The kernel's \texttt{isLargeEliminator} (\srcloc{Lean4Lean/Inductive/Add.lean}{275}) searches all result arguments, not only those past \texttt{nparams}. The two agree because \texttt{CtorResult} pins the first $np$ arguments to be \texttt{bvarsDesc nf np}, whose entries are all $\ge nf$, while the field variable sought here is $\mathsf{bvar}\,(nf-1-i) < nf$; that argument is what makes the \texttt{drop np} sound and it is recorded nowhere in the source.
- `def:ind-motive-shape`: A deliberately weak approximation of $\kappa$: the telescope is not required to be $indices \to P\;a \to \mathsf{Sort}$. Its ``ends in a sort'' clause is subsumed by \texttt{VInductDecl.WF.recs\_elim}, which pins the exact sort, so it is also mildly redundant.
- `def:ind-minor-headed`: Nothing ties minor $i$ to the motive of the type former its constructor belongs to, only to \emph{some} motive.
- `def:ind-minor-for`: Two distinct constructors cannot satisfy \texttt{MinorFor} for the same minor (\texttt{getLast?} and \texttt{headConst?} are functions), so the constructor-to-minor map \texttt{rule\_shape} chooses is injective, but no lemma in the repository derives that and nothing uses it; \texttt{rules\_nodup} is what the proofs actually appeal to.
- `def:ind-rec-shape`: Parameter and index binder types are unconstrained, as are the heads of the non-eliminated motives of a mutual recursor: a documented weakening of $\kappa$ and $\varepsilon$. The de Bruijn arithmetic of the body head is machine-checked against the kernel by \texttt{checkShapes} in \texttt{Tests/IotaShape.lean}, which decides \texttt{RecShape} on the translated \texttt{RecursorVal.type} of some fifty recursors (\texttt{Nat}, \texttt{Eq}, \texttt{Acc}, \texttt{Vec}, the \texttt{Ev}/\texttt{Od} mutual block, \texttt{False}, and a list of \texttt{Init}/\texttt{Std} inductives).
- `def:ind-ctor-shape`: Its two halves are consumed separately and neither by the same client: \texttt{PatsIota.ctor\_shape} keeps only the \texttt{CtorHeaded} half, and the front end (\srcloc{Lean4Lean/Verify/Environment/Basic.lean}{514}) only the arity half.
- `def:ind-rule-shape`: This is the main weakening of \S2.6.4 in the file, flagged at length in its own docstring: the recursive calls $v_i = \lambda x{::}\xi_i.\;\mathrm{rec}_P\;C\;e\;\pi_i[b,x]\;(u_i\;x)$ are pinned only in number, not in shape, and \texttt{WF.rules\_wf} only forces them to be well-typed. \texttt{VInductDecl.WF} therefore accepts $\iota$ rules Lean would never generate.
- `family:ind-shape-corollaries`: \texttt{RuleShape.lam} (used by \texttt{addRules\_ordered}), \texttt{RecShape.recHeaded} (used by \texttt{PatsIota.induct}) and \texttt{CtorResult.ctorShape} (used by \texttt{rules\_ctor\_shape}) are load-bearing. \texttt{RecShape.one\_le\_numMotives} (\srcloc{Lean4Lean/Theory/Inductive.lean}{196}) and \texttt{RecShape.majorFormer?\_eq} (\srcloc{Lean4Lean/Theory/Inductive.lean}{202}) are referenced nowhere in the repository.
- `def:ind-large-elim`: It matches the kernel's \texttt{isLargeEliminator} (\srcloc{Lean4Lean/Inductive/Add.lean}{258}) clause for clause, including the zero-constructor case, and the thesis's separate rule for recursive arguments is subsumed. But the kernel tests \texttt{isAlwaysZero} on the inferred level where the model demands a typing at $\mathsf{sort}\;0$; these agree only up to level defeq and uniqueness of typing, neither of which is proved here. Because the propositionality clause is a typing judgment, \texttt{LargeElim} is undecidable.
- `def:ind-large-elim-shape`: \texttt{LargeElimShape} carries a \texttt{Decidable} instance and is used by the tests; \texttt{LargeElim.shape}, the lemma that justifies calling it the syntactic half, is used nowhere.
- `inductive:pattern-core`: \texttt{Pattern.LE} is declared and used nowhere in the repository, and \texttt{Arity}/\texttt{Arity.subpattern} only in the experimental logical-relations development (\srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{3436} and \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{3620}), never in the verified one. This is pre-existing \texttt{master} code, not the contributor's.
- `inductive:pattern-matches`: In the \texttt{app} case the argument side's level list is discarded, so an $\iota$ redex constrains the recursor's universes but not the constructor's. That is what makes \texttt{iotaRHS}'s use of the recursor's levels correct. \texttt{Matches.uniq} (line 143) and \texttt{matches\_determ} (line 283) are the same statement proved twice.
- `inductive:simple-pattern`: \texttt{SimplePattern.defn} is never registered by anything; \texttt{InductiveParams} explains why, namely that $\delta$ rules stay in \texttt{defeqs}.
- `def:pattern-rhs-generic`: This is the modelling idea behind \texttt{VEnv.PatTyped}: the thesis's schematic rule, stated in the context $\Gamma, C{:}\kappa, e{::}\varepsilon, b{::}\beta$, becomes one typing obligation over a context of exactly the used holes. The docstring is candid that an $\iota$ rule's index arguments and constructor parameters are tied to nothing by it.
- `def:pattern-check-realizes`: A good design move: \texttt{Check.OK} mentions the definitional-equality relation and so cannot occur positively in the \texttt{IsDefEq} inductive, whereas \texttt{Realizes} is a pure predicate, which is what makes the new \texttt{IsDefEq.pat} constructor legal.
- `def:pattern-iota-paths`: The two \texttt{pmap}s with their \texttt{omega} side proofs are heavy for what they say, but correct.
- `def:pattern-iota-rhs`: Splitting the shape reduction sees (\texttt{iotaRHS'}) from the typed split (\texttt{iotaRHS}) is a good separation, and the $cnp$ versus $np$ distinction anticipates the auxiliary recursors of nested inductives even though \texttt{VInductDecl.WF} currently excludes them.
- `thm:pattern-apply-foldl-var`: The line blame tags this \texttt{trproj}, but the code is byte-identical on \texttt{iota} (ported as commit \texttt{3de1dcb}); it belongs to the $\iota$ story, not the projection story.
- `family:pattern-iota-counts`: None of these eight declarations is referenced outside \texttt{Pattern.lean}, and inside it they are used only by each other: about seventy lines of purely documentary material, better expressed as a doc comment plus one \texttt{example}.
- `inductive:pattern-template-headed`: This is what separates a registered reduction rule from a definitional axiom: it is used in \texttt{Theory/Typing/Lemmas.lean} to show a registered rule cannot rewrite a sort or a $\Pi$-type, which the inversion lemmas of the type system need. A well-judged invariant.
- `def:ind-add-rec-rule`: Only the constructor rule of \S2.6.4 is registered. K-like reduction, the section's second rule, which the kernel does perform (\texttt{toCtorWhenK}, \srcloc{Lean4Lean/Inductive/Reduce.lean}{29}, called from \srcloc{Lean4Lean/Inductive/Reduce.lean}{110}), is not modelled, and \texttt{VRecursor.k} is recorded but unused. Style nit: the major index is spelled out here as \texttt{r.numParams + r.numMotives + r.numMinors + r.numIndices} while every lemma about it uses \texttt{r.getMajorIdx}.
- `family:ind-add-stages`: The staging exists precisely so that \texttt{VInductDecl.WF} can type each kind of constant in the environment the kernel checks it in, and the docstring is honest that the kernel interleaves recursors with their rules, so only the resulting environment agrees, not the order.
- `def:ind-add-induct`: On \texttt{master} this was \texttt{def VEnv.addInduct := sorry}, an opaque \texttt{Option VEnv}, so no statement mentioning it could be proved or refuted.
- `structure:ind-wf`: This replaces \texttt{master}'s \texttt{def VInductDecl.WF := sorry} and is the centrepiece of the contribution. Four limitations are stated in the structure's own docstring: nested inductives are excluded; K-like reduction and structure $\eta$ are not modelled; and positivity and \texttt{universes} read manifest binders where the kernel \texttt{whnf}s. \texttt{rule\_shape}'s field docstring adds a fifth, that the recursive arguments are pinned in number only. Two further ones are documented nowhere: \texttt{universes} bundles the purely syntactic bound \texttt{decl.nparams} $\le$ \texttt{t.type.piArity} into a clause guarded by stage 0 succeeding, so that arity fact is unavailable if stage 0 fails; and no clause mentions \texttt{VRecursor.all}, which is pinned to the kernel's only consumer, by \texttt{TrRecursor.all} (\srcloc{Lean4Lean/Verify/Environment/Basic.lean}{240}). Above all, and also undocumented, no theorem derives this record from the kernel's own checker.
- `family:indlem-foldlm`: These are generic over an arbitrary element type and have nothing to do with inductives, yet they live in namespace \texttt{Lean4Lean.VEnv} inside a file called \texttt{InductiveLemmas}.
- `thm:indlem-add-induct-wf`: This is the headline result of the branch for this file: \texttt{master} declared exactly this statement with \texttt{sorry}. It is proved only relative to the new \texttt{VInductDecl.WF}, which is itself part of the contribution and remains an assumption on the front-end side.
- `family:indlem-pats-defeqs-preserved`: \texttt{addQuot\_le}, \texttt{addQuot\_pats} and the \texttt{addDefEqs} lemmas are about other declaration kinds and sit oddly in a file called \texttt{InductiveLemmas}; the three \texttt{defeqs} lemmas for rules are tagged \texttt{trproj} by the blame but exist identically on \texttt{iota}.
- `family:indlem-addconst-spec`: \texttt{nodup\_map\_inj\_on} is a pure \texttt{List} lemma declared as \texttt{Lean4Lean.VEnv.nodup\_map\_inj\_on}.
- `family:indlem-pats-origin`: The dependent-equality formulation is heavy, but it is what pins the reduct and not only the key; the primed and unprimed pair is a sensible interface split.
- `family:indparams-inter`: Three \texttt{Pattern} lemmas declared with \texttt{\_root\_} inside \texttt{namespace VEnv}; they belong next to \texttt{Pattern.inter} in \texttt{Pattern.lean}.
- `thm:indparams-wf-pats-origin`: Its own docstring calls it the first step of the deferred $\iota$ subject-reduction proof (\texttt{VEnv.WF.patsStrong}, \srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{334}, still \texttt{sorry}). Nothing uses it yet, so its value is entirely as groundwork for that open obligation.
- `structure:indparams-patsiota`: Well chosen: exactly strong enough to discharge the five structural \texttt{Params} conditions and weak enough to be preserved by \texttt{addInduct}. The \texttt{arity} field is the non-obvious one.
- `thm:indparams-patsiota-rec-ne-ctor`: The separation rests on the type shapes of the constants, not on any tagging in \texttt{VEnv.constants}, which is precisely why the same trick does not extend to $\delta$ rules.
- `def:indparams-defeqs-as-pats`: The 27-line docstring (\srcloc{Lean4Lean/Theory/Typing/InductiveParams.lean}{351}) is the most useful documentation in the group. It explains that $\delta$ rules and the quotient rule live in \texttt{defeqs}, why registering \texttt{SimplePattern.defn} would require a new environment invariant separating definition names from recursor and constructor names, and why the quotient redex is not a \texttt{SimplePattern} at all. The consequence, stated plainly, is that \texttt{DefEqsAsPats} fails for any environment containing a single \texttt{def} or \texttt{quot}. Two thirds of it (lines 355, 362--377) is tagged \texttt{trproj} by the blame and is, unlike every other \texttt{trproj}-tagged block in this group, genuinely absent from \texttt{iota}, where the hypothesis is called a ``design hypothesis'' and the $\delta$ analysis is missing.
- `def:indparams-toparams`: This is the point of the file: the abstract development had no instance at all before. Its value is limited by \texttt{DefEqsAsPats}, which as it stands restricts \texttt{toParams} to environments with no definitional axiom whatsoever.
- `def:indparams-induct-params`: The only witness that \texttt{Params} is inhabitable at all, which is genuinely useful as a sanity check, but the environment is a toy: one inductive block and nothing else. The line blame tags it \texttt{trproj}; identical on \texttt{iota}.
- `thm:indparams-cr-defeq-of-induct`: The statement reads as a finished result and is not one. \texttt{IsDefEq.church\_rosser} routes through \texttt{NormalEq.parRed}, which still contains two \texttt{sorry}s, so the conclusion is conditional on them; the docstring says nothing about that. Nothing consumes the theorem.

### Section "Contribution summary"

```latex
\section{Contribution summary}

The $\iota$ contribution to this group does four things. First, it replaces two
\texttt{sorry}-definitions by a real specification: \ref{def:ind-add-induct} stages the
environment extension into type formers, constructors, recursors and rules, and
\ref{structure:ind-wf} states in twenty clauses what the kernel checks, each clause typed in
the environment the kernel checks it in and each documented with its thesis reference. The
syntactic half of that record is \ref{def:ind-ctor-result} to \ref{def:ind-rule-shape}, whose
de Bruijn arithmetic is correct and is exercised against real kernel declarations by
\texttt{Tests/IotaShape.lean}. Second, it makes the $\iota$ rule a first-class reduction rule:
\ref{def:pattern-rhs-generic} turns the thesis's ``all substitution instances'' parenthesis
into one typing obligation, \ref{def:pattern-check-realizes} makes the side conditions a
positive predicate so that the new \texttt{IsDefEq.pat} constructor is legal,
\ref{inductive:pattern-template-headed} records that a registered rule computes, and
\ref{def:pattern-iota-rhs} with \ref{thm:pattern-iota-rhs-apply} identify the model's reduct
with the kernel's \texttt{inductiveReduceRecCore} reduct argument slice for argument slice.
Third, \ref{thm:indlem-add-induct-wf} proves that adding a well-formed block preserves
orderedness, with \ref{family:indlem-pat-registration} and \ref{family:indlem-pats-origin}
giving both directions of ``\texttt{pats} holds exactly the block's $\iota$ rules''. Fourth,
\ref{structure:indparams-patsiota} to \ref{def:indparams-toparams} build the first concrete
instance of the parameter record the Church-Rosser development is stated over.

What remains open. Nothing derives \ref{structure:ind-wf} from
\texttt{Lean4Lean/Inductive/Add.lean}, the repository's own re-implementation of the kernel's
inductive checker, so \texttt{TrEnv'.induct} still takes it as a hypothesis; two of the
model's deliberate deviations, manifest binders in positivity and the exclusion of nested
inductives, actively obstruct closing that gap. \ref{def:indparams-toparams} applies only to
environments with no definitional axiom, so the only instance built,
\ref{def:indparams-induct-params}, is a toy. \ref{thm:indparams-wf-pats-origin} is groundwork
for \texttt{VEnv.WF.patsStrong}, which is still \texttt{sorry}. And K-like reduction is not
modelled at all, so for subsingleton eliminators the model's reduction relation is strictly
weaker than the kernel's.
```

### Section "Review notes"

```latex
\section{Review notes}
\label{sec:ind-review}

\begin{itemize}
\item \textbf{High.} \srcloc{Lean4Lean/Verify/Environment/Basic.lean}{583}: nothing derives
\texttt{VInductDecl.WF} from the kernel's own inductive checker. \texttt{TrEnv'.induct} takes
\texttt{decl.WF env} as a hypothesis and \texttt{Lean4Lean/Inductive/Add.lean} is never
related to it, so the refinement chain still has an assumption at the hardest declaration
kind. This is better than \texttt{master}, where the predicate was \texttt{sorry} and the
assumption was uninformative, and \texttt{Tests/IotaShape.lean} validates the record by
\texttt{decide} on concrete kernel data, but that is evidence, not a proof. The contribution
should be described as specified and validated, not verified.
\item \textbf{High.} \srcloc{Lean4Lean/Theory/Typing/InductiveParams.lean}{426}:
\texttt{IsDefEq.crDefEq\_of\_induct} is presented as Church-Rosser for such an environment,
but \texttt{IsDefEq.church\_rosser} depends on the two \texttt{sorry}s in
\texttt{NormalEq.parRed} (\srcloc{Lean4Lean/Theory/Typing/ChurchRosser.lean}{1193} and
\srcloc{Lean4Lean/Theory/Typing/ChurchRosser.lean}{1212}). The docstring gives no hint that
the conclusion is conditional, and no other declaration uses the theorem.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Typing/InductiveParams.lean}{393}:
\texttt{toParams} is a \texttt{Params} instance only for environments satisfying
\texttt{DefEqsAsPats}, that is, containing no \texttt{def}, \texttt{mutualDef} or
\texttt{quot} at all. Every realistic Lean environment fails it, so the Church-Rosser
development is still not connected to the model's own well-formed environments. Documented at
length in the \texttt{DefEqsAsPats} docstring, but it is the main limitation of the file.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Inductive.lean}{174}:
\texttt{VExpr.RuleShape} pins only the number of arguments the reduct passes to the minor
premise after the fields, not their shape, where the thesis requires
$v_i = \lambda x{::}\xi_i.\;\mathrm{rec}_P\;C\;e\;\pi_i[b,x]\;(u_i\;x)$. Together with
\texttt{rules\_wf}, which only forces them to be well-typed, \texttt{VInductDecl.WF} accepts
$\iota$ rules the kernel would never generate. Flagged in the docstring, but it caps what any
soundness theorem proved against this model can mean.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Inductive.lean}{257}: K-like reduction is not
modelled. \texttt{addRecRule} registers only the constructor rule and \texttt{VRecursor.k} is
recorded but never used, while the kernel does perform it (\texttt{toCtorWhenK},
\srcloc{Lean4Lean/Inductive/Reduce.lean}{29}, called from
\srcloc{Lean4Lean/Inductive/Reduce.lean}{110}). For K-like recursors the model's reduction
relation is strictly weaker than the kernel's and the verified WHNF cannot be shown complete
for them.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Inductive.lean}{93}:
\texttt{FieldPositive}, \texttt{CtorPositive} and \texttt{WF.universes} read the manifest
$\Pi$-binders of a field type, whereas the kernel reduces to weak head normal form at each
step of \texttt{checkPositivity} (\srcloc{Lean4Lean/Inductive/Add.lean}{189}). The model is
therefore strictly stricter than the kernel: a declaration whose field type is a reducible
definition unfolding to a $\Pi$ passes the kernel and fails \texttt{VInductDecl.WF}.
Documented, but it is an obstacle to ever discharging the first item above.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Inductive.lean}{335}:
\texttt{recs\_over\_block} and \texttt{rules\_ctor} require every recursor to eliminate one of
the block's own type formers, which excludes nested inductives. \texttt{Environment.addInductive}
does add such blocks, so \texttt{TrEnv'} can never be constructed for an environment containing
one. Documented as future work, namely modelling the kernel's \texttt{ElimNestedInductive} pass.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Inductive.lean}{196}: dead code.
\texttt{VExpr.RecShape.one\_le\_numMotives} (line 196),
\texttt{VExpr.RecShape.majorFormer?\_eq} (line 202) and
\texttt{VInductDecl.LargeElim.shape} (line 242) are referenced nowhere in the repository, and
so is the whole \texttt{Pattern.RHS.spine} and \texttt{iotaCounts} cluster at
\srcloc{Lean4Lean/Theory/Typing/Pattern.lean}{509} to 678, eight declarations and about
seventy lines used only by each other.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Typing/InductiveLemmas.lean}{451}: placement and
naming. \texttt{nodup\_map\_inj\_on} is a pure \texttt{List} lemma declared as
\texttt{Lean4Lean.VEnv.nodup\_map\_inj\_on}; the generic \texttt{foldlM} and
\texttt{addConst\_foldlM} toolkit and the \texttt{addQuot} and \texttt{addDefEqs} lemmas,
which are about quotients and definitions, all live in a file named \texttt{InductiveLemmas};
and \texttt{VEnv.addRecRule} (\srcloc{Lean4Lean/Theory/Inductive.lean}{259}) spells the major
index out instead of using \texttt{r.getMajorIdx}, which every lemma about it does use.
Similarly \texttt{Pattern.inter\_app\_const} and its two siblings are \texttt{\_root\_}
\texttt{Pattern} lemmas declared inside \texttt{namespace VEnv}.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Typing/Pattern.lean}{283}: redundancy.
\texttt{Pattern.Matches.uniq} (line 143) and \texttt{Pattern.matches\_determ} (line 283) are
the same statement proved twice; both are pre-existing \texttt{master} code that the branches
left untouched (\texttt{git diff master} on this file is 493 insertions and no deletions), so
the duplication is inherited rather than introduced.
Similarly \texttt{MotiveShape}'s ``ends in a sort'' clause is
subsumed by \texttt{VInductDecl.WF.recs\_elim}, which pins the exact sort, and
\texttt{WF.universes} bundles the purely syntactic bound
\texttt{decl.nparams} $\le$ \texttt{t.type.piArity} into a clause guarded by stage 0
succeeding.
\item \textbf{Low, fidelity.} \srcloc{Lean4Lean/Theory/Inductive.lean}{75}:
\texttt{ValidIndApp} drops the kernel's exact-arity check on the occurrence's arguments,
\texttt{args.size == params.size + nindices[i]}
(\srcloc{Lean4Lean/Inductive/Add.lean}{159}), although its docstring claims to mirror
\texttt{isValidIndApp?}; \texttt{FieldInIndices}
(\srcloc{Lean4Lean/Theory/Inductive.lean}{107}) searches only the arguments past
\texttt{nparams} where the kernel searches all of them
(\srcloc{Lean4Lean/Inductive/Add.lean}{275}), the two agreeing only by an argument about
\texttt{CtorResult} that is recorded nowhere; and \texttt{LargeElim} demands a typing at
$\mathsf{sort}\;0$ where the kernel tests \texttt{isAlwaysZero} on the inferred level
(\srcloc{Lean4Lean/Inductive/Add.lean}{271}), which agree only up to level defeq and
uniqueness of typing.
\item \textbf{Low, undocumented limitations.}
\srcloc{Lean4Lean/Theory/Inductive.lean}{351}: \texttt{WF.universes} hides the purely
syntactic bound \texttt{decl.nparams} $\le$ \texttt{t.type.piArity} inside a clause guarded
by \texttt{addTypes} succeeding, so the arity fact is unavailable when stage 0 fails; and no
clause of \texttt{VInductDecl.WF} mentions \texttt{VRecursor.all}, which the model's own
well-formedness therefore never uses (the refinement pins it to the kernel's separately,
\srcloc{Lean4Lean/Verify/Environment/Basic.lean}{240}). Unlike the nested-inductive, K-like,
$\eta$, \texttt{whnf} and \texttt{rule\_shape} limitations, neither is recorded in the
source.
\end{itemize}
```

## proj.tex

### Node review notes (38)
- `def:proj-field-selector`: The \texttt{Nat} subtraction $|Fs|-1-i$ is unguarded: for $i\ge|Fs|$ it truncates to $0$ and silently selects the innermost binder instead of being undefined. Callers are expected to carry \texttt{TrProjCtor.field\_lt}.
- `def:proj-inst-pis`: Manifest binders only. The kernel \texttt{whnf}s at each binder, so a constructor type whose telescope hides behind a definition makes this \texttt{none}; that is a documented completeness boundary of \texttt{TrProjCtor.ctor}, not a soundness gap.
- `def:proj-inst-fields`: This is a \emph{second} telescope-substitution convention next to the master \texttt{VExpr.insts}, which substitutes at index $0$ once per binder. The section docstring (lines 195--203) argues convincingly that neither is a special case of the other, but no lemma relates them, so the two conventions only ever meet through raw \texttt{inst}.
- `def:proj-motive-body-of`: Out-of-range $i$ falls back to $\mathrm{default}=\mathrm{sort}\;\mathrm{zero}$ through \texttt{List.getD}, so the definition is total but meaningless above the field count.
- `def:proj-fns`: The defining equation mentions $\mathrm{projFns}\dots i$ twice, so the unfolded expansion of field $i$ is exponential in $i$ (each motive embeds every earlier projection function in full) and every induction over it must apply the induction hypothesis twice. An accumulating fold returning the list built so far would be linear.
- `def:proj-ty`: Dead in the library: its only use anywhere is the example at \srcloc{Lean4Lean/Tests/ProjShape.lean}{178}, and the model types a projection through \ref{def:proj-motive-body} instead. The identity its docstring asserts, $\mathrm{projTy}\dots e = (\mathrm{projMotiveBody}\dots i).\mathrm{inst}\;e$, is never proved (it should follow from \texttt{instFields\_subst} and \texttt{inst\_liftN}), so the definition the prose uses to explain \texttt{inferProj} is formally disconnected from the one the model uses. \texttt{Tests/ProjShape.lean} nevertheless names \texttt{projTy} in its module docstring and in the error message at \srcloc{Lean4Lean/Tests/ProjShape.lean}{114} for a check whose type is built from \ref{def:proj-motive-body}.
- `def:proj-binder-arity`: It pins only the \emph{number} of binders, not their types: a recursor whose minor bound $n_f$ unrelated things would pass. In \ref{thm:tr-env-proj-defeq} the gap is closed by the kernel-side structure facts, so it is contained, but the docstring's wording ``has exactly the \texttt{nf} fields as binders'' over-reads what is checked.
- `fam:proj-unfolding`: \texttt{projMotiveBody\_zero} is marked \texttt{@[simp]} but is never invoked explicitly anywhere, as is \texttt{instFields\_nil}; both are cheap, so this is noise rather than a defect.
- `fam:proj-fieldselector-subst`: Used only inside this file, by \ref{fam:proj-fnof-subst}.
- `fam:shapedecide-deceq`: The two declarations are elaborator-generated (\texttt{Lean4Lean.instDecidableEqVLevel}, \texttt{Lean4Lean.instDecidableEqVExpr}) and are referenced nowhere in the sources by name.
- `fam:shapedecide-existential`: Only the \texttt{some} branch (lines 31--32) is \texttt{trproj}-attributed; the rest of the node is \texttt{iota}-branch work.
- `fam:shapedecide-head`: This is the \texttt{trproj} addition to an otherwise \texttt{iota}-branch file: \texttt{CtorHeaded} is what \texttt{TrProjCtor.ctor} and the kernel test of \ref{def:projshape-checkproj} need to decide.
- `fam:shapedecide-shapes`: All twenty-two instances of this file are \emph{global}: twenty-one in the \texttt{Lean4Lean.VExpr} namespace and one on \texttt{VInductDecl.LargeElimShape}, all declared from a \texttt{Tests} module. That is safe today only because nothing in the library imports the module; any future library import would silently expose typeclass resolution to these potentially expensive decision procedures, the more so for the one instance that is not about a library predicate at all, $\exists a,\;o=\mathrm{some}\;a\wedge P\,a$ for \emph{any} \texttt{Option} and any decidable $P$ (\srcloc{Lean4Lean/Tests/ShapeDecide.lean}{27}). The module docstring explains the placement but not this risk.
- `def:iotashape-checkshapes`: The \texttt{recs\_elim} check spells the extra universe as $\mathrm{param}\;0$, that is, it assumes the fresh universe sits at index $0$ of the recursor's \texttt{levelParams}. That is how Lean generates recursors, but nothing here checks it.
- `thm:iotashape-matchpat-sound`: Completeness is not proved, which is the right asymmetry for a test: a failed match raises an error rather than passing silently.
- `def:iotashape-checkiota`: The oracle is lean4lean's own \texttt{inductiveReduceRec} (\srcloc{Lean4Lean/Inductive/Reduce.lean}{100}), not Lean's C++ kernel, so both sides of the comparison live in this repository and a shared misreading of the kernel's argument slicing would not be caught. The constant-application guard on the major premise (\srcloc{Lean4Lean/Tests/IotaShape.lean}{306}) is one of the two \texttt{trproj} edits here.
- `def:iotashape-largeelim`: Honest about the boundary between the syntactic and the typing halves of \ref{def:ind-large-elim}; the expected answers, open fields included, are pinned in \ref{test:iotashape-run}.
- `def:iotashape-blockfailures`: Returning failing clause \emph{names} rather than a Boolean makes the negative controls informative, but \texttt{checkBlockRejected} only asks that \emph{some} clause fail, so the docstring's expectation that a nested block fails \texttt{ctors\_positive} and \texttt{recs\_over\_block} in particular is pinned by no test. For \texttt{Tree} the two underlying predicates are pinned separately (\srcloc{Lean4Lean/Tests/IotaShape.lean}{584}); for the other eight nested blocks of \ref{test:iotashape-run} nothing records which clause failed.
- `def:iotashape-fixtures-nested`: The module docstring (\srcloc{Lean4Lean/Tests/IotaShape.lean}{336}) groups all three as ``small-eliminating \texttt{Prop} inductives''. \texttt{Wrap.rec} in fact eliminates into $\mathrm{Sort}\;u$; only the wording is wrong, and the fixture is the one of the three that supplies the large-eliminating case.
- `thm:iotashape-twoctorprop`: The sharpest test in the group: it isolates which clause of \ref{structure:ind-wf} is load-bearing for consistency and shows the specification catches the unsound declaration. Only the syntactic half is exercised; \texttt{VInductDecl.LargeElim} itself is a typing judgment and is decided nowhere.
- `test:iotashape-run`: Nearly every assertion comes with a matching negative control, which is what makes \ref{structure:ind-wf} credible as a \emph{tight} specification rather than merely a satisfiable one. Two caveats: it is one \texttt{run\_meta} block, so a failure reports only the first mismatch and the remaining assertions are never reached; and this node carries no \texttt{\textbackslash lean} link because a \texttt{run\_meta} block declares no constant. The control at \srcloc{Lean4Lean/Tests/IotaShape.lean}{538} is the second \texttt{trproj} line pair in the file.
- `fam:projshape-back-translation`: The \texttt{param} case of \texttt{toLevel} uses \texttt{ls.getD i .anonymous}, so a level index the structure's universe names do not support silently becomes the anonymous universe rather than an error.
- `def:projshape-checkproj`: Three caveats. The second check uses \texttt{isDefEq} (as the module docstring says), so it is agreement up to \emph{kernel} conversion, which may use structure eta and projection reduction that the model's \texttt{IsDefEq} deliberately lacks. The type it compares is built from \ref{def:proj-motive-body}, but the docstring and the error message call it \texttt{projTy}, a different definition (\ref{def:proj-ty}) that no lemma relates to it. And \texttt{uss} is built with \texttt{(VLevel.ofLevel lps (lvls j)).getD .zero} (\srcloc{Lean4Lean/Tests/ProjShape.lean}{78}), silently defaulting a mistyped level argument to zero.
- `test:projshape-run`: The \texttt{Sigma.snd} control (\srcloc{Lean4Lean/Tests/ProjShape.lean}{136}) wraps the call in \texttt{try \dots catch \_ => pure false}, so \emph{any} failure inside \texttt{checkProj} makes it pass vacuously. Also, this node has no \texttt{\textbackslash lean} link because a \texttt{run\_meta} block declares no constant.
- `test:projshape-sigmasnd`: This is the only use of \ref{def:proj-ty} anywhere. The top-level names \texttt{ps}, \texttt{Fs}, \texttt{uss}, \texttt{usS} and \texttt{structTy} sit in the test namespace but are very broad for globally visible definitions.
- `def:projinhabit-plain-block`: \texttt{VEnv.addInduct} (\srcloc{Lean4Lean/Theory/Inductive.lean}{316}) checks only name clashes and closedness of the rule reducts, never well-formedness, and neither $\mathtt{VInductDecl.WF}\;\mathit{decl}\;\mathit{env}$ nor $\mathit{env}.\mathtt{WF}$ is ever proved here. The witnesses below therefore establish that the premises of \ref{struct:trprojctor} are simultaneously satisfiable, not that they are satisfiable in a well-formed environment.
- `def:projinhabit-plain-expansion`: $\mathit{uss}$ is the constant function $\lambda \_.\,[l_1]$, so the per-field level list, the whole reason \ref{def:proj-fn} takes $uss$ as a function at all, is not exercised on the model side anywhere in this file.
- `fam:projinhabit-plain-typing`: Readable and well factored, but every lemma is indexed by $\Gamma$ and re-proved from scratch rather than weakened from a fixed context: eighteen declarations for one structure.
- `thm:projinhabit-plain-inhab0`: This is the real content of the file: it shows \texttt{TrProjCtor} is not vacuous. It does \emph{not} show that a kernel-accepted projection yields one; that is the \texttt{sorry}-ed \ref{thm:vtc-inferproj-struct}.
- `thm:projinhabit-plain-inhab1`: Asymmetric with the \texttt{Dependent} namespace, which packages \texttt{trProjDep1} but not \texttt{trProjDep0}; neither \texttt{trProj1} nor \texttt{trProjDep0} exists.
- `def:projinhabit-dep-block`: Near-verbatim duplication of the \texttt{Plain} namespace: the same block construction re-declared, mostly with a \texttt{2} suffix. Untracked near-copies of both namespaces also live in \texttt{review-artifacts/inhabitation/}.
- `def:projinhabit-dep-template`: The numbering skips $T_4$ and there is no \texttt{hc4}, but neither is a gap: only the $\lambda$-headed intermediates get a name, and the reduct of $\beta_4$ is the application $\mathit{sel}_{20}\,a\,b$; \texttt{hbeta4} and \texttt{hbeta6} are stated on the full spine already, so they need no congruence wrapper.
- `thm:projinhabit-dep-hmatch`: A good concrete illustration of the pattern machinery; the closing \texttt{rfl} is a nontrivial kernel computation over the reduct's \texttt{RHS.apply}.
- `thm:projinhabit-dep-hiota`: This is the one place in the whole group where the model's $\iota$ rule is actually fired; everything else is $\beta$ and conversion.
- `fam:projinhabit-dep-beta-chain`: Very verbose, twenty-two declarations for six $\beta$ steps, because \texttt{IsDefEq} has no \texttt{betaN} or \texttt{whnf} combinator usable here: \texttt{VEnv.IsDefEqU.betaN} exists (\srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{994}, added on the same branch) but needs \texttt{VEnv.WF}, which these hand-built environments do not have.
- `thm:projinhabit-dep-hp1ty`: This is the technical heart of the projection design: it mechanises, on an instance, the claim that the dependent motive is typable using only $\beta$ and the registered $\iota$ rule --- no structure eta, no K-like reduction, no injectivity.
- `thm:projinhabit-dep-inhab`: Together with \ref{thm:projinhabit-plain-inhab0} and \ref{thm:projinhabit-plain-inhab1} these are the only evidence that \texttt{TrProjCtor} is satisfiable. They cover a constant and a dependent motive, but not: parameters ($np=0$ in both), a non-trivial $usS$, a per-field $uss$, or more than two fields, so \ref{fam:proj-fn-subst} never meets a non-trivial instance in any test.
- `test:projinhabit-axioms`: Hardcoding the full seven-element axiom list makes the guard brittle: any unrelated upstream proof that gains or loses an axiom forces an edit here. And the prose attribution of the \texttt{sorryAx} to unique typing, $\Pi$-injectivity and \texttt{VEnv.WF.patsStrong} is a claim the guard cannot check; the axiom census traces the dependency only through \texttt{VEnv.WF.orderedStrong} to \texttt{VEnv.WF.patsStrong}, the one literal \texttt{sorry} involved. This node carries no \texttt{\textbackslash lean} link because a \texttt{\#guard\_msgs} block declares no constant; the theorem the fifth block pins belongs to Chapter~\ref{chap:trenv} (\ref{thm:tr-env-proj-defeq}).

### Section "Contribution summary"

```latex
\section{Contribution summary}

Two contributions meet in this group, and the whole of it is contributed. The \texttt{trproj}
branch adds \texttt{Lean4Lean/Theory/Proj.lean} in full. Its content is one design decision and
its consequences: a kernel projection is not a new node of \texttt{VExpr} (\ref{ind:vexpr}) but an
application of the recursor the kernel already generates for the structure. That buys a great
deal. \texttt{IsDefEq} (\ref{def:isdefeq}) gains no rule, so no metatheory has to be redone, and a
projection computes because the structure's $\iota$ rule computes, not because a projection rule
was added. The expansion is spelled out by \ref{def:proj-field-selector} through
\ref{def:proj-fn}, its type by \ref{def:proj-motive-body} and \ref{def:proj-ty}, and the
de Bruijn metatheory those builders need by \ref{fam:proj-foldr-lam} through
\ref{fam:proj-motivebody-subst}, all stated once against \texttt{Subst} (\ref{def:subst}) and
specialised to weakening and instantiation afterwards.

It connects to later work at three points. \texttt{TrProjCtor} (\ref{struct:trprojctor}) in
Chapter~\ref{chap:trexpr} is the consumer: its \texttt{eq} clause is \ref{def:proj-fn}, its
\texttt{fn\_ty} clause is \ref{def:proj-motive-body}, its \texttt{ctor} clause is
\ref{def:proj-inst-pis} and its \texttt{minor\_arity} clause is \ref{def:proj-binder-arity}. The
four forms of \ref{fam:proj-fn-subst} are exactly what \texttt{TrProj.weak'},
\texttt{TrProj.instN} and \texttt{TrProj.instL} consume. And
\ref{thm:proj-instfields-minor-spine}, with \ref{thm:proj-instfields-bvar} beneath it, is the
arithmetic \texttt{TrEnv.proj\_defeq} (\ref{thm:tr-env-proj-defeq}) needs to compute the $\iota$
reduct of a structure's rule. The same branch adds the three modules that make the design
falsifiable: \ref{def:projshape-checkproj} confronts the expansion with the real Lean kernel on
eleven structure-and-field pairs, and \ref{thm:projinhabit-plain-inhab0},
\ref{thm:projinhabit-plain-inhab1} and \ref{thm:projinhabit-dep-inhab} inhabit
\texttt{TrProjCtor}, the last of these resting on \ref{thm:projinhabit-dep-hp1ty}, which
mechanises on an instance the claim that the dependent motive is typable using only $\beta$ and a
registered $\iota$ rule.

The \texttt{iota} branch contributes the two specification tests.
\ref{fam:shapedecide-deceq} through \ref{fam:shapedecide-shapes} make every syntactic predicate of
Chapter~\ref{chap:inductive} executable without moving it out of \texttt{Prop} in the library, and
\ref{def:iotashape-ruleshapeat} through \ref{test:iotashape-run} decide every \emph{syntactic}
clause of \ref{structure:ind-wf} on the kernel's own data, compare the model's $\iota$ reduct with the
executable kernel's on twelve rules (\ref{def:iotashape-checkiota}, sound by
\ref{thm:iotashape-matchpat-sound}), and supply the negative controls
(\ref{thm:iotashape-positivity}, \ref{thm:iotashape-twoctorprop}) that make the specification look
tight rather than merely satisfiable. The \texttt{trproj} contribution to those two files is
fifteen lines: eleven in \texttt{Tests/ShapeDecide.lean} (the head-constructor tests of
\ref{fam:shapedecide-head}, which \texttt{TrProjCtor.ctor} needs, and the \texttt{some} branch of
the option instance), and four in \texttt{Tests/IotaShape.lean} (the constant-application guard
inside \texttt{checkIotaAuto} and one minor-premise control in \ref{test:iotashape-run}).

What remains open is the bridge from the kernel. \texttt{inferProj.WF\_struct}
(\ref{thm:vtc-inferproj-struct}) is \texttt{sorry}, so nothing yet shows that a kernel-accepted
projection yields a \texttt{TrProjCtor}; the general construction exists as a fifteen-line
informal derivation in the module docstring of \texttt{Theory/Proj.lean} and is mechanised only on
the two hand-built instances of \ref{def:projinhabit-plain-block} and
\ref{def:projinhabit-dep-block}, whose environments are never shown well formed. \ref{def:proj-ty}
is not connected to \ref{def:proj-motive-body} by any lemma. The witnesses cover neither
parameters nor a non-trivial per-field level list, so \ref{fam:proj-fn-subst} is never exercised
on a non-trivial instance. Structure eta is outside what this representation can express, and the
docstring says so. On the \texttt{iota} side, nothing derives \ref{structure:ind-wf} from the
repository's own inductive checker, so \ref{test:iotashape-run} remains evidence about the
specification rather than a proof about it.
```

### Section "Review notes"

```latex
\section{Review notes}
\label{sec:proj-review}

\begin{itemize}
\item \textbf{Medium.} \srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{398}: the whole
projection story rests on \texttt{inferProj.WF\_struct} (\ref{thm:vtc-inferproj-struct}), which is
\texttt{sorry}. Its proof exists as a fifteen-line informal derivation in the module docstring of
\srcloc{Lean4Lean/Theory/Proj.lean}{38} and is mechanised only on the two instances of
\texttt{Tests/ProjInhabit.lean}. Nothing in the development shows that a kernel-accepted
projection yields a \texttt{TrProjCtor}, so \texttt{TrExprS.proj} is never inhabited from a real
term.
\item \textbf{Medium.} \srcloc{Lean4Lean/Theory/Proj.lean}{127}: \texttt{VExpr.projTy}
(\ref{def:proj-ty}) has no consumer in the library, only
\srcloc{Lean4Lean/Tests/ProjShape.lean}{178}, and the identity its docstring asserts,
$\mathrm{projTy}\dots e=(\mathrm{projMotiveBody}\dots i).\mathrm{inst}\;e$, is never proved. The
model types a projection through \ref{def:proj-motive-body}, so the definition the prose uses to
explain \texttt{inferProj} is formally disconnected from the one \texttt{TrProjCtor.fn\_ty} uses.
The confusion is visible in the test: the module docstring and the error message at
\srcloc{Lean4Lean/Tests/ProjShape.lean}{114} say the kernel comparison checks \texttt{projTy},
while the type actually handed to the kernel is built from \texttt{projMotiveBody}.
\item \textbf{Medium.} \srcloc{Lean4Lean/Tests/ProjInhabit.lean}{49}: \texttt{VEnv.addInduct}
(\srcloc{Lean4Lean/Theory/Inductive.lean}{316}) checks only name clashes and closedness of the
rule reducts, never well-formedness, and neither
$\mathtt{VInductDecl.WF}\;\mathit{decl}\;\mathit{env}$ nor $\mathit{env}.\mathtt{WF}$ is ever
proved for the two hand-built environments. The witnesses therefore establish that the premises of
\ref{struct:trprojctor} are simultaneously satisfiable, not that they are satisfiable in a
well-formed environment; in particular \ref{thm:tr-env-proj-defeq}, which needs a \texttt{TrEnv},
is not exercised end to end on them.
\item \textbf{Low.} \srcloc{Lean4Lean/Tests/ProjInhabit.lean}{70}: both blocks set
$\mathit{uss}$ to the constant $\lambda\_.\,[l_1]$ and both have no parameters
($np=0$, $usS=[]$). The per-field level list, which is the reason \ref{def:proj-fn} and
\ref{def:proj-fns} take $uss$ as a function at all and the case the module docstring highlights
($\mathrm{Sigma.fst}$ at $u+1$ against $\mathrm{Sigma.snd}$ at $v+1$), is exercised only on the
kernel side (\srcloc{Lean4Lean/Tests/ProjShape.lean}{126}). So \ref{fam:proj-fn-subst} never meets
a non-trivial instance in any test.
\item \textbf{Low.} \srcloc{Lean4Lean/Tests/ProjShape.lean}{136}: the \texttt{Sigma.snd}
level-list negative control wraps \texttt{checkProj} in \texttt{try \dots catch \_ => pure false},
so \emph{any} failure inside \texttt{checkProj} (a renamed constant, a \texttt{CtorHeaded}
failure, a field-count mismatch) makes the control pass vacuously.
\item \textbf{Low.} \srcloc{Lean4Lean/Tests/ProjShape.lean}{78}:
\texttt{(VLevel.ofLevel lps (lvls j)).getD .zero} silently substitutes the zero level when the
caller passes a level the structure's universe names do not support, so a mistyped test argument
degrades into a different, possibly still passing, test rather than an error.
\texttt{toLevel}'s \texttt{ls.getD i .anonymous} (\srcloc{Lean4Lean/Tests/ProjShape.lean}{49}) has
the same shape.
\item \textbf{Low.} \srcloc{Lean4Lean/Tests/ProjShape.lean}{113}: the agreement between
\ref{def:proj-motive-body} and the kernel's \texttt{inferProj} is checked with \texttt{isDefEq},
which on the kernel side may use structure eta and projection reduction that the model's
\texttt{IsDefEq} deliberately lacks. The check is the right one, since the kernel's type mentions
\texttt{.proj} nodes the model cannot spell, and the module docstring does say \texttt{isDefEq};
but what it establishes is agreement up to \emph{kernel} conversion, which is strictly weaker than
anything the model can reproduce.
\item \textbf{Low.} \srcloc{Lean4Lean/Tests/ProjInhabit.lean}{586}: the
\texttt{\#guard\_msgs in \#print axioms} block for \texttt{TrEnv.proj\_defeq} hardcodes a
seven-element axiom list including \texttt{sorryAx} and three
\texttt{Lean.PersistentHashMap} axioms. It is brittle, since any unrelated upstream proof change
forces an edit here, and the prose attribution of the \texttt{sorryAx} to unique typing,
$\Pi$-injectivity and \texttt{VEnv.WF.patsStrong} is a claim the guard cannot verify.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Proj.lean}{111}: \ref{def:proj-fns} mentions
$\mathrm{projFns}\dots i$ twice in its own defining equation, so the expansion of field $i$ is
exponential in $i$, every motive embedding all earlier projection functions in full, and every
substitution lemma about it must apply its induction hypothesis twice. An accumulating fold would
be linear.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Proj.lean}{195}: \ref{def:proj-inst-fields} is a
\emph{second} telescope-substitution convention alongside the master \texttt{VExpr.insts}, which
substitutes at index $0$ once per binder. The section docstring argues convincingly that neither
is a special case of the other, but no lemma relates them, so the two conventions only ever meet
through raw \texttt{inst}.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Proj.lean}{136}: \ref{def:proj-binder-arity} pins
only the \emph{number} of binders of the recursor's minor premise, not their types, yet its
docstring and \texttt{TrProjCtor.minor\_arity} read it as ``has exactly the \texttt{nf} fields as
binders''. The gap is closed in \ref{thm:tr-env-proj-defeq} by the kernel-side structure facts,
but the documentation overstates what the predicate checks.
\item \textbf{Low.} \srcloc{Lean4Lean/Tests/ProjInhabit.lean}{179}: the \texttt{Plain} and
\texttt{Dependent} namespaces duplicate about twenty near-identical declarations, and
\texttt{Dependent} subsumes \texttt{Plain} except for the two-fields-of-the-same-type case.
Untracked near-copies of both live in \texttt{review-artifacts/inhabitation/}.
\item \textbf{Low.} \srcloc{Lean4Lean/Tests/ProjInhabit.lean}{172}: the packaging is asymmetric.
\texttt{Plain} exposes \texttt{trProj0} but no \texttt{trProj1}, while \texttt{Dependent} exposes
\texttt{trProjDep1} but no \texttt{trProjDep0}, so neither namespace packages both of its fields
as a \texttt{TrProj}. (The gaps at $T_4$ and \texttt{hc4} in the $\beta$ chain are not defects:
see \ref{def:projinhabit-dep-template}.)
\item \textbf{Low.} \srcloc{Lean4Lean/Tests/ProjInhabit.lean}{353}: the derivations are correct
but extremely verbose, twenty-two declarations for a six-step $\beta$-reduction
(\ref{fam:projinhabit-dep-beta-chain}), because \texttt{IsDefEq} has no \texttt{betaN} combinator
usable at this level: \texttt{VEnv.IsDefEqU.betaN} needs \texttt{VEnv.WF}, which these hand-built
environments do not have.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Proj.lean}{140}: dead or unused code.
\ref{def:proj-ty} has no library consumer, and \texttt{projMotiveBody\_zero} and
\texttt{instFields\_nil} are marked \texttt{@[simp]} but are never invoked explicitly anywhere.
\item \textbf{Low.} \srcloc{Lean4Lean/Tests/ShapeDecide.lean}{20}: all twenty-two instances of the
file are \emph{global} \texttt{Decidable} instances, twenty-one of them in the
\texttt{Lean4Lean.VExpr} namespace and one on \texttt{VInductDecl.LargeElimShape}, declared from a
\texttt{Tests} module. That is safe today only because nothing in the library imports the module;
any future library import would silently expose typeclass resolution to these potentially
expensive decision procedures. The widest of them is not about a library predicate at all:
\srcloc{Lean4Lean/Tests/ShapeDecide.lean}{27} decides $\exists a,\;o=\mathrm{some}\;a\wedge P\,a$
for any \texttt{Option} and any decidable $P$. The module docstring explains the placement but not
this risk.
\item \textbf{Low.} \srcloc{Lean4Lean/Tests/IotaShape.lean}{151}: \ref{def:iotashape-checkiota}
compares \texttt{SimplePattern.iotaRHS} against lean4lean's own \texttt{inductiveReduceRec}
(\srcloc{Lean4Lean/Inductive/Reduce.lean}{100}), not against Lean's C++ kernel. Both sides of the
oracle live in this repository, so a shared misreading of the kernel's argument slicing would not
be detected; the $\iota$ step itself, \texttt{inductiveReduceRecCore}
(\srcloc{Lean4Lean/Inductive/Reduce.lean}{75}), is the twenty-one lines of that file written on
\texttt{trproj}.
\item \textbf{Low.} \srcloc{Lean4Lean/Tests/IotaShape.lean}{86}: the \texttt{recs\_elim} check of
\ref{def:iotashape-checkshapes} assumes the recursor's extra universe parameter is at index $0$ of
its \texttt{levelParams}, which is how Lean generates recursors but is nowhere checked.
\item \textbf{Low.} \srcloc{Lean4Lean/Tests/IotaShape.lean}{295}: \texttt{checkBlockRejected}
(\ref{def:iotashape-blockfailures}) only asks that \emph{some} block clause fail. Which clauses a
nested block is expected to fail, \texttt{ctors\_positive} and \texttt{recs\_over\_block}, is
asserted in the docstring and pinned in no test. For \texttt{Tree} the two predicates are checked
directly (\srcloc{Lean4Lean/Tests/IotaShape.lean}{584}); for the other eight nested blocks the
returned clause names are discarded.
\item \textbf{Low.} \srcloc{Lean4Lean/Tests/IotaShape.lean}{336}: the fixture docstring calls
\texttt{PropLarge}, \texttt{Wrap} and \texttt{SigmaLike} ``small-eliminating \texttt{Prop}
inductives''. \texttt{Wrap p}, whose single field is a proof of \texttt{p}, is
subsingleton-eliminating: \texttt{Wrap.rec} eliminates into $\mathrm{Sort}\;u$ and carries the
extra universe parameter. Only the wording is wrong; the fixture is in fact the large-eliminating
case of the three, and is covered by \texttt{checkAll}.
\item \textbf{Low.} \srcloc{Lean4Lean/Tests/IotaShape.lean}{454}: \ref{test:iotashape-run} is one
\texttt{run\_meta} block of about 150 lines, so a failure reports only the first mismatch and the
remaining assertions, including all the negative controls after it, are never reached.
\item \textbf{Low.} \srcloc{.github/workflows/ci.yml}{25}: the comment states that
\texttt{Lean4Lean.Tests} is among the \texttt{defaultTargets}, but
\srcloc{lakefile.toml}{2} lists only \texttt{Lean4Lean}, \texttt{lean4lean},
\texttt{Lean4Lean.Theory} and \texttt{Lean4Lean.Verify}. The test modules of this chapter are in
fact built by the separate \texttt{lake build Lean4Lean.Tests} step, so nothing is unchecked, but
the comment is wrong.
\item \textbf{Low.} \srcloc{Lean4Lean/Theory/Proj.lean}{1}: the thesis citations attached to the
projection work are individually accurate but are borrowed idioms rather than inherited results.
The thesis's $\mathrm{inv}_x$ (typesys.tex \S3.1) is introduced to prove conversion
\emph{undecidable}, and the $\pi_2$ rule (Wtypes.tex \S5.1) belongs to the W-type system that
\emph{replaces} general inductives, which lean4lean does not formalise. Neither is a statement
this development inherits.
\end{itemize}
```

## kernel.tex

### Node review notes (50)
- `def:kernel-reducibility-lt`: The single marker \texttt{-- lean4\#2750} is the only record that the C++ hint comparison is known to differ subtly from this one.
- `def:kernel-expr-replace`: \texttt{replaceM} is itself \texttt{partial} even though \texttt{replaceNoCacheT} is not, so it has no equation lemmas, and the cached implementation is trusted. A \texttt{TODO} at \srcloc{Lean4Lean/Expr.lean}{44} acknowledges this.
- `def:kernel-cheap-beta`: The $x_i$ branch is guarded by \texttt{assert! n < i} at \srcloc{Lean4Lean/Instantiate.lean}{24}; the invariant is not established here.
- `def:kernel-foreach-exprv`: The module is imported by \texttt{TypeChecker.lean} but neither \texttt{forEachV} nor \texttt{forEachV'} has a call site anywhere under \texttt{Lean4Lean/}; this looks like dead code left from an earlier version of the expression scope check.
- `def:kernel-level-normalize`: Substantial new algorithmic content, but its correctness is not established in this chapter's scope: Chapter \ref{chap:levels} proves it, in full and sorry-free, as \texttt{Lean.Level.Normalize.normalize\_complete} and \texttt{Lean.Level.isEquiv'\_complete} ($\texttt{isEquiv'}\;u\;v \leftrightarrow u \approx v$ against the semantic model \texttt{VLevel}), so this is not the unverified new component it might appear to be in isolation.
- `def:kernel-level-le`: Cited in this docstring only as ``Theorem 39 of the paper'', with no formal bibliography entry, though the paper itself (Yoan G\'eran, ``A Canonical Form for Universe Levels in Impredicative Type Theory'') is named with a working URL earlier in the same file, at \srcloc{Lean4Lean/Level.lean}{27}. In any case the claim is not merely cited on trust: Chapter \ref{chap:levels} reproves it from scratch in Lean, sorry-free, as \texttt{Lean.Level.Normalize.NormLevel.le\_complete} and \texttt{Lean.Level.geq'\_complete}.
- `def:kernel-level-isequiv`: The docstring quotes a measurement (261k comparisons over Lean, Std and Batteries; roughly 20 times cheaper than normalizing) that no script in the repository reproduces.
- `def:kernel-is-nonrec-structure`: The thesis's type theory has neither projections nor structure $\eta$, so this predicate delimits precisely the extension the \texttt{trproj} model work has to cover (Chapter \ref{chap:proj}).
- `def:kernel-env-empty-import`: \srcloc{Lean4Lean/Environment/Basic.lean}{124} sets \texttt{quotInit := !imports.isEmpty} unconditionally, that is, it \emph{assumes} any non-empty import set has already initialized quotients. \texttt{Replay.checkQuotInit} is the compensating check, but an imported environment is never re-checked, so \texttt{checkEqType} never runs on one.
- `axiom:kernel-ptr-eq`: These are two of the project's genuine trusted axioms, used in only two places (\srcloc{Lean4Lean/Verify/EquivManager.lean}{264} and \srcloc{Lean4Lean/Verify/TypeChecker/IsDefEq.lean}{384}), so the trusted surface is small. But at \srcloc{Lean4Lean/TypeChecker.lean}{739} \texttt{ptrEqConstantInfo dt ds} gates a \emph{different algorithm} (congruence on arguments before unfolding), not merely a shortcut, which is exactly what the file's own docstring warns about.
- `structure:kernel-fuel-config`: Every field's docstring names the loop it bounds, which is exemplary; the docstring's claim that ``defaults are set so mathlib passes'' is backed by nothing in the repository.
- `def:kernel-equiv-manager`: Since \texttt{addEquiv} records pairs equated by the \emph{algorithmic} relation, and that relation is not transitive, the union-find's transitive closure can claim equalities the algorithm would not decide. This matches the C++ kernel, but it means \texttt{isEquiv} is not a conservative optimization and the verification layer has to account for it.
- `def:kernel-check-eq-type`: The guarantee is narrower than the commit message suggests. \texttt{Environment.addQuot} returns immediately when \texttt{env.quotInit} is already true, and \texttt{finalizeImport} sets \texttt{quotInit} for any non-empty import set, so on an imported environment neither the shape check nor the new safety check ever runs. The new property holds only for environments built from scratch, where \texttt{Init.Prelude} is replayed. This is a pre-existing gap, not one the contribution introduced, but it bounds what removing \texttt{EqSafe} buys.
- `def:kernel-quot-reduce-rec`: The positions 5/4 and 3/3 are magic numbers justified only by the type signatures quoted in the surrounding docstring. Unlike the inductive $\iota$ rule, nothing here checks that the eliminator is saturated: a partially applied \texttt{Quot.lift} simply fails to match.
- `def:kernel-to-ctor-when-k`: The thesis describes this step as ``proof irrelevance to change the major premise into a constructor, followed by the iota rule'', which is exactly the factoring the \texttt{trproj} branch made explicit in code. \texttt{reduceRecursor.WF} remains open precisely because this step has no \texttt{IsDefEq} counterpart in the model yet.
- `def:kernel-to-ctor-when-struct`: Second site of the documented \texttt{isNeverZero} versus \texttt{!isAlwaysZero} divergence from the C++ kernel; it narrows the class of projections any \texttt{TrProj} theorem can be about.
- `def:kernel-iota-core`: Three cosmetic blemishes. (a) The definition sits inside the \texttt{section} opened at \srcloc{Lean4Lean/Inductive/Reduce.lean}{9} whose variables (\texttt{[Monad m]}, \texttt{env}, \texttt{whnf}, \texttt{inferType}, \texttt{isDefEq}) it uses none of; Lean binds only used section variables so the arity is the intended four, but a later edit that touches \texttt{env} would silently change the signature and break the \texttt{WF} statement. (b) The new docstring duplicates the slicing description in the unchanged caller docstring. (c) It collapses ``no rule for this constructor'', ``major has too few arguments'' and ``wrong number of universe arguments'' into one \texttt{none}, which is why the \texttt{WF} theorem must take saturation as an external hypothesis rather than deriving it; the commit message says so plainly.
- `def:kernel-inductive-reduce-rec`: The master docstring at \srcloc{Lean4Lean/Inductive/Reduce.lean}{91} was left untouched and still describes the $\iota$ slicing in full, work that is now done in \texttt{inductiveReduceRecCore} and documented there too. Trimming it to the preprocessing the caller still performs would have completed the refactor.
- `structure:kernel-tc-monad`: Keeping \texttt{lparams} fixed for the whole run is one of the documented divergences: the C++ kernel sets and unsets level parameters around \texttt{check}, so its \texttt{ensure\_sort} runs without them.
- `structure:kernel-methods-fuel`: Central design decision of the project, and the source of a real behavioural divergence: a declaration the C++ kernel accepts can be rejected here with \texttt{.deepRecursion}.
- `def:kernel-reduce-recursor`: \texttt{reduceRecursor.WF} is explicitly still open in the verification layer, since the K-like and structure-$\eta$ paths have no \texttt{IsDefEq} counterpart; the \texttt{trproj} contribution verifies only the pure $\iota$ core beneath it.
- `def:kernel-reduce-proj`: The comment at \srcloc{Lean4Lean/TypeChecker.lean}{356} states that the explicit \texttt{>>=} is written that way because \texttt{reduceProj.WF} ``cannot see through'' the \texttt{do}-elaborator's bind lifting. That is the implementation being bent to suit its proof; defensible in a verification-first project, but worth naming.
- `def:kernel-reduce-nat`: This is the one place where the checker's answers depend on the prelude really defining \texttt{Nat.add} and friends correctly, which is why Definition \ref{def:kernel-primitive-checkdef} exists. The exponent cap is a silent incompleteness (a legitimate \texttt{Nat.pow} simply fails to reduce) and is not listed in \texttt{divergences.md}, though the C++ kernel has the same cap.
- `def:kernel-whnf-core`: The docstring records that the C++ companion flag \texttt{cheap\_rec} is omitted because nothing has set it since lean4\#9275, and the comment at \srcloc{Lean4Lean/TypeChecker.lean}{404} justifies the re-decomposition branch. Both are the kind of invariant note the proofs need.
- `def:kernel-infer-constant`: The safety discipline \texttt{.safe}/\texttt{.partial}/\texttt{.unsafe} is outside the thesis's system; it is the extra structure that the safety-indexed abstract environments of the verification layer exist to model.
- `def:kernel-infer-binders`: \texttt{inferApp} is the \texttt{inferOnly := true} fast path and is correct only on already well-typed terms; the precondition is recorded in the \texttt{isDefEqCore} docstring at \srcloc{Lean4Lean/TypeChecker.lean}{172} rather than on \texttt{inferApp} itself.
- `def:kernel-infer-proj`: A documented divergence: lean4lean tests \texttt{isNeverZero} where the C++ kernel tests \texttt{!isAlwaysZero}, deliberately keeping \texttt{proj} no stronger than the recursor the kernel generates for the same type. This directly bounds the scope of the \texttt{trproj} \texttt{inferProj.WF} and \texttt{TrProj} results.
- `def:kernel-infer-type`: The \texttt{eagerReduce} escape hatch at \srcloc{Lean4Lean/TypeChecker.lean}{299} changes definitional-equality behaviour on a \emph{syntactic} test for core Lean's \texttt{eagerReduce} marker in an argument, and is consulted again at lines 541, 782 and 845. It mirrors upstream Lean, so it is rightly not a divergence, but it has no thesis counterpart and no local documentation of what the four sites jointly guarantee.
- `def:kernel-quick-isdefeq`: The \texttt{modifyGet} at \srcloc{Lean4Lean/TypeChecker.lean}{593} destructures \texttt{TypeChecker.State} positionally as \texttt{.mk a1 \dots a7 (eqvManager := m)}; adding or reordering a field silently changes what this matches. A named \texttt{modifyGet} would be equivalent and robust.
- `family:kernel-isdefeq-aux`: \texttt{isDefEqUnitLike} is not derivable from the thesis's rules; it is an extra definitional equality the C++ kernel has, and the model has to account for it. Two entries of \texttt{divergences.md} cover this family (argument-count-before-head, and the \texttt{whnf} removed from \texttt{tryStringLitExpansionCore}).
- `def:kernel-eta-rules`: The comment at \srcloc{Lean4Lean/TypeChecker.lean}{654} documents that both symmetric calls in \texttt{tryEtaStruct} redo work \texttt{isDefEqApp} already did, and that the C++ kernel has the same redundancy. Matching the kernel rather than optimizing is the right call here.
- `def:kernel-proof-irrel`: \texttt{isProp} tests \texttt{isAlwaysZero} while \texttt{inferProj} and \texttt{toCtorWhenStruct} test \texttt{isNeverZero} for the opposite question. The asymmetry is deliberate and explained in \texttt{divergences.md}, but the two spellings sitting in one file invite confusion.
- `def:kernel-lazy-delta`: \texttt{ptrEqConstantInfo} is used here as a \emph{semantic} test, not an optimization: two different addresses for the same \texttt{ConstantInfo} select a different branch. That is precisely what the \texttt{PtrEq} docstring warns about and why \texttt{ptrEqConstantInfo\_eq} must be an axiom.
- `def:kernel-isdefeq-core`: This is the function whose correctness is the entire point of the verification. The \texttt{s.isConstOf ``true} shortcut at \srcloc{Lean4Lean/TypeChecker.lean}{845} is an asymmetric special case for \texttt{Decidable} instances with neither a thesis counterpart nor a \texttt{divergences.md} entry.
- `family:kernel-tc-entrypoints`: A commented-out \texttt{example}/\texttt{run\_tac} block at \srcloc{Lean4Lean/TypeChecker.lean}{968} is leftover scratch code that should be either a real test or deleted.
- `def:kernel-eta-expand`: This function has no call site anywhere under \texttt{Lean4Lean/}. If it is meant to realize the thesis's $\mathrm{rec}$-normal-form preprocessing, which saturates every $\mathrm{rec}$ and $\mathrm{lift}$ before $\kappa$-reduction is even defined, that intent is undocumented, and the executable kernel never enforces $\mathrm{rec}$-normal form. This matters: the saturation hypothesis of \texttt{inductiveReduceRecCore.WF} is the executable counterpart of exactly that preprocessing.
- `def:kernel-check-positivity`: The model-side counterpart on the \texttt{iota} branch is the positivity specification in \texttt{Theory/Inductive.lean} (Chapter \ref{chap:inductive}); the two should be cross-checked on nested and reflexive cases, which the kernel handles in \texttt{ElimNestedInductive} rather than in this judgment.
- `def:kernel-mk-rec-infos`: A tower of continuation-passing loops with hand-written \texttt{termination\_by}, split into standalone functions because they would not compile together as \texttt{let rec}s. It is readable only against the thesis's notation, and there is no docstring pointing at \S2.6.3.
- `def:kernel-mk-rec-rules`: This is the producer side of the contract whose consumer side \texttt{inductiveReduceRecCore.WF} verifies, and the \texttt{iota} branch's model of the $\iota$ rule is a model of exactly these rules; it is the right place to look when judging whether that specification is faithful.
- `def:kernel-addinductive-run`: The binding \texttt{isUnsafe}, read from the context safety, is computed twice, at \srcloc{Lean4Lean/Inductive/Add.lean}{453} and again at \srcloc{Lean4Lean/Inductive/Add.lean}{470}, the second shadowing the first. The recursor type is built with \texttt{type.inferImplicit 1000 false}, a magic constant whose accompanying comment notes that the flag's polarity is inverted relative to C++.
- `def:kernel-elim-nested`: Fully unverified and the largest source of \texttt{unreachable!}/\texttt{assert!} in the kernel. Three \texttt{divergences.md} entries concern it, one of which admits an actual hole: \texttt{restoreCtorName}'s \texttt{unreachable!} would continue with a default value, and a restored rule constructor \emph{name} is covered by no later re-check, since lean4lean also skips lean4\#14621's recheck of restored declarations.
- `def:kernel-add-inductive`: This is the function for which \texttt{addDecl.WF}'s \texttt{inductDecl} case is \texttt{sorry} at \srcloc{Lean4Lean/Verify/Environment.lean}{208}: the \texttt{AddInduct} witness the model needs has to be constructed from here, and nobody has. Everything the \texttt{iota} branch proves about inductive blocks sits on the model side of that gap.
- `family:kernel-primitive-dsl`: \texttt{deriving instance ToExpr} for \texttt{Syntax}, \texttt{KVMap} and \texttt{Expr} ties this file to the exact shape of core's \texttt{Expr} and \texttt{Syntax}. Acceptable for a recognizer, but it is compile-time-only machinery living inside the trusted kernel library.
- `def:kernel-primitive-checkdef`: A genuine soundness gap in the C++ kernel that lean4lean closes, and the \texttt{run\_meta} self-test at the end of the file gives real assurance that it accepts the actual prelude. But the property it establishes is stated nowhere here; the connection to \texttt{reduceNat} is made only in \texttt{Verify/Environment/Primitive/} (Chapters \ref{chap:primitives-core} and \ref{chap:primitives-arith}), and a build-time test is not a proof.
- `family:kernel-add-decls`: Three \texttt{divergences.md} entries live here. The comment at \srcloc{Lean4Lean/Environment.lean}{53} explains why \texttt{Primitive.checkDef} runs after the body check (so that its \texttt{isDefEq} calls see terms already known well-typed); that is an ordering invariant the proofs depend on and it is easy to break.
- `def:kernel-add-decl`: \texttt{addDecl.WF} is proved for every case except \texttt{inductDecl}, which is \texttt{sorry} at \srcloc{Lean4Lean/Verify/Environment.lean}{208}. The \texttt{quotDecl} case is unconditional thanks to the \texttt{iota} change to \texttt{checkEqType}.
- `family:kernel-replay-core`: The \texttt{--compare} path times lean4lean against Lean's own kernel, which is useful but makes the driver depend on core's \texttt{Environment.addDecl} as well.
- `family:kernel-replay-postponed`: This is the real value of replay as a test: a differential check of \texttt{AddInductive.mkRecRules} against Lean's own elaborator across whole libraries, and in practice the only end-to-end evidence that the kernel's rule generation agrees with Lean's. It is worth pointing at when judging the \texttt{iota} branch's $\iota$-rule specification.
- `def:kernel-replay-entrypoints`: \texttt{replayFromFresh} passes \texttt{checkQuot := false} (\srcloc{Lean4Lean/Replay.lean}{319}), so the quotient-initialization check is skipped exactly in the mode that builds an environment from scratch. In that mode \texttt{Init.Prelude} is replayed and so \texttt{addQuot} does run, but the ordering is the opposite of what one would want.
- `family:kernel-fuelconfig-cli`: \texttt{toObj} calls \texttt{panic!} if the derived encoding is not a JSON object. Unreachable, but a panic inside a command line argument parser. The node map named these two helpers \texttt{toJsonObj} and \texttt{fields}; the declarations are actually called \texttt{toObj} and \texttt{fieldNames}, and both are \texttt{private} to \texttt{Main}.

### Section "Contribution summary"

```latex
\section{Contribution summary}

The two branches together changed 22 of the 4040 lines in this chapter's scope, and both changes
were made to unblock a specific proof obligation rather than to improve the kernel for its own
sake.

On \texttt{trproj}, the $\iota$ step of \texttt{inductiveReduceRec} was extracted verbatim into the
pure function \texttt{inductiveReduceRecCore} (Definition \ref{def:kernel-iota-core}), and
\texttt{inductiveReduceRec} (Definition \ref{def:kernel-inductive-reduce-rec}) now ends by calling
it. The reason is that \texttt{inductiveReduceRec} is monadic only because of its K-like
(Definition \ref{def:kernel-to-ctor-when-k}) and structure-$\eta$
(Definition \ref{def:kernel-to-ctor-when-struct}) preludes, whereas the $\iota$ step itself is
pure and total; after the split, \texttt{inductiveReduceRecCore.WF} can be stated about a function
with no monad, no environment lookup and no well-typedness side conditions beyond its hypotheses.
The commit is explicit that \texttt{reduceRecursor.WF}
(Definition \ref{def:kernel-reduce-recursor}) stays open, because the two preludes still have no
\texttt{IsDefEq} counterpart in the model. The split is behaviour-preserving; the extracted body
was diffed against master line by line and differs only in recomputing \texttt{rval.getMajorIdx}
where the caller had bound it.

On \texttt{iota}, \texttt{checkEqType} (Definition \ref{def:kernel-check-eq-type}) gained one line
rejecting an \texttt{unsafe} \texttt{Eq}. This is a reject-more divergence from \texttt{quot.cpp},
recorded in \texttt{divergences.md}, and it discharges rather than adds an assumption: both
\texttt{addQuot.WF} and \texttt{addDecl.WF} (Definition \ref{def:kernel-add-decl}) lost their
\texttt{Environment.EqSafe} hypothesis, and the assumption itself was deleted.

What remains open on the kernel side is unchanged by either branch and bounds what they can claim:
\texttt{addDecl.WF}'s \texttt{inductDecl} case is still \texttt{sorry} because the model witness
must be built from \texttt{Environment.addInductive}
(Definition \ref{def:kernel-add-inductive}); \texttt{reduceRecursor.WF} is open; the projection
rules (Definitions \ref{def:kernel-infer-proj} and \ref{def:kernel-reduce-proj}) carry a documented
\texttt{isNeverZero} divergence that narrows every \texttt{TrProj} statement; and
\texttt{etaExpand} (Definition \ref{def:kernel-eta-expand}), the only plausible executable
counterpart of the thesis's $\mathrm{rec}$-normal-form preprocessing, is never called, so the
saturation hypothesis of \texttt{inductiveReduceRecCore.WF} is not enforced anywhere in the kernel.
```

### Section "Review notes"

```latex
\section{Review notes}

\begin{itemize}
\item \textbf{Medium.} \srcloc{Lean4Lean/Quot.lean}{24}: the \texttt{iota} safety check is well
justified and net positive, but the guarantee is narrower than the commit message suggests.
\texttt{Environment.addQuot} returns early when \texttt{env.quotInit} is already true, and
\texttt{Kernel.Environment.finalizeImport} (\srcloc{Lean4Lean/Environment/Basic.lean}{124}) sets
\texttt{quotInit := !imports.isEmpty} unconditionally, so on any imported environment neither the
shape check nor the new safety check ever runs. The model-side claim holds only for environments
replayed from scratch.
\item \textbf{Low.} \srcloc{Lean4Lean/Inductive/Reduce.lean}{71}:
\texttt{inductiveReduceRecCore} is declared inside the \texttt{section} opened at line 9 with
variables \texttt{[Monad m]}, \texttt{env}, \texttt{whnf}, \texttt{inferType},
\texttt{isDefEq}, none of which it uses. Lean binds only used section variables, so the signature
is the intended four-argument one, but a reader (or a later edit that adds a use of \texttt{env})
can be misled about its arity. Placing it outside the section would be clearer.
\item \textbf{Low.} \srcloc{Lean4Lean/Inductive/Reduce.lean}{91}: after the split, the unchanged
master docstring of \texttt{inductiveReduceRec} still describes the $\iota$ slicing in full, which
is now \texttt{inductiveReduceRecCore}'s job and is documented there too. The file states the same
algorithm twice; the caller's docstring should have been trimmed to the K-like, structure-$\eta$
and literal preprocessing it still performs.
\item \textbf{Low.} \srcloc{Lean4Lean/Inductive/Reduce.lean}{75}:
\texttt{inductiveReduceRecCore} collapses ``no rule for this constructor'', ``major has too few
arguments'' and ``wrong number of universe arguments'' into a single \texttt{none}. This is
faithful to master, but it is why \texttt{inductiveReduceRecCore.WF} must take saturation as an
external hypothesis instead of deriving it.
\item \textbf{Low.} \srcloc{Lean4Lean/TypeChecker.lean}{946}: \texttt{TypeChecker.etaExpand} has
no call site anywhere under \texttt{Lean4Lean/}. If it is meant to realize the thesis's
$\mathrm{rec}$-normal-form preprocessing (unique.tex \S4, sec:kappa), that intent is undocumented,
and the executable kernel never enforces $\mathrm{rec}$-normal form.
\item \textbf{Low.} \srcloc{Lean4Lean/ForEachExprV.lean}{25}: \texttt{Expr.forEachV} and
\texttt{forEachV'} appear to be dead code; the module is imported by \texttt{TypeChecker.lean} but
neither function has a call site in the kernel files.
\item \textbf{Low.} \srcloc{Lean4Lean/TypeChecker.lean}{593}: \texttt{quickIsDefEq} destructures
\texttt{TypeChecker.State} positionally as \texttt{.mk a1 a2 a3 a4 a5 a6 a7 (eqvManager := m)}.
Adding or reordering a field silently changes what this matches, or fails to compile confusingly;
a \texttt{modifyGet} on the named field would be equivalent and robust.
\item \textbf{Low.} \srcloc{Lean4Lean/TypeChecker.lean}{299}: the \texttt{eagerReduce} marker (a
syntactic \texttt{isAppOfArity} test that switches the definitional-equality strategy, consulted
again at lines 541, 782 and 845) mirrors core Lean's own gadget, so it is correctly absent from
\texttt{divergences.md}. It is nevertheless the one reduction knob in the file with no thesis
counterpart and no local docstring stating what the four sites jointly guarantee.
\item \textbf{Low.} \srcloc{Lean4Lean/Inductive/Add.lean}{470}: \texttt{AddInductive.run} computes
its \texttt{isUnsafe} binding twice (lines 453 and 470), the second shadowing
the first; dead duplication.
\item \textbf{Low.} \srcloc{Lean4Lean/TypeChecker.lean}{493}: \texttt{reducePowMaxExp} silently
declines to reduce \texttt{Nat.pow} at exponents above $2^{24}$. The C++ kernel has the same cap,
but the incompleteness is not listed in \texttt{divergences.md}.
\item \textbf{Low.} \srcloc{Lean4Lean/TypeChecker.lean}{845}: the \texttt{s.isConstOf ``true}
shortcut in \texttt{isDefEqCore'} is an asymmetric special case with neither a thesis counterpart
nor a \texttt{divergences.md} entry.
\item \textbf{Low.} \srcloc{Lean4Lean/TypeChecker.lean}{355} and
\srcloc{Lean4Lean/TypeChecker.lean}{968}: \texttt{reduceProj} is written in an awkward explicit
bind style for the benefit of its proof, and a commented-out \texttt{example}/\texttt{run\_tac}
scratch block is left at the end of the file.
\item \textbf{Low.} \srcloc{Main.lean}{29}: \texttt{FuelConfig.toObj} uses \texttt{panic!} when the
derived JSON encoding is not an object, inside a command line argument parser.
\item \textbf{Informational.} \srcloc{Lean4Lean/PtrEq.lean}{17}: the two pointer-equality
soundness axioms are genuine trusted assumptions of the project. They are honestly documented and
used in only two places, but at \srcloc{Lean4Lean/TypeChecker.lean}{739}
\texttt{ptrEqConstantInfo} gates a different algorithm rather than a shortcut.
\item \textbf{Informational.} \srcloc{Lean4Lean/Verify/Environment.lean}{208}:
\texttt{addDecl.WF}'s \texttt{inductDecl} case is \texttt{sorry}, so everything the \texttt{iota}
branch proves about inductive blocks lives on the model side of that gap. This is master's hole,
not a contributed one, but it bounds what the branch can claim.
\end{itemize}
```

## trexpr.tex

### Section "Contribution summary"

```latex
\section{Contribution summary}

The \texttt{trproj} branch contributed the projection translation. Where
\srcloc{Lean4Lean/Verify/Typing/Expr.lean}{69} to 136 now stands, master held the single line
\texttt{def TrProj : ... := sorry}, and \srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{641} held seven
\texttt{sorry} lemmas about it, so the \texttt{proj} rule of \texttt{TrExprS}
(Definition \ref{ind:trexprs}) related a source projection to an arbitrary model term and the whole
translation relation was, in that case, vacuous. The branch replaced the stub by
\texttt{TrProjCtor} (Definition \ref{struct:trprojctor}) and its existential closure
\texttt{TrProj} (Definition \ref{def:trproj}): since \texttt{VExpr} has no projection node, the
target is required to be the recursor expansion applied to the major premise, which is the
thesis's \texttt{inv\_x} construction generalised from \texttt{Acc} to an arbitrary
single-constructor structure, built from the \texttt{Theory/Proj.lean} vocabulary of
Chapter \ref{chap:proj}. Two design decisions carry the section: the expansion's typing is a
\emph{field} of the relation rather than something to be derived, and the expansion data
(constructor name, level lists, parameters, field telescope) is hidden existentially so that the
consumers' statements do not change.

Five of master's seven stubs are now proved: Theorems \ref{thm:trproj-weak},
\ref{thm:trproj-defeqdfc}, \ref{thm:trproj-wf}, \ref{thm:trproj-instn} and
\ref{thm:trproj-instl}. Three of them, \ref{thm:trproj-weak}, \ref{thm:trproj-instn} and
\ref{thm:trproj-instl}, are a single \texttt{refine} over a record literal built on one observation
reused three times, that the pattern key, the field index and the minor arity mention the field
telescope only through its length; \ref{thm:trproj-defeqdfc} reuses the old record with
\texttt{\{H with \ldots\}} and \ref{thm:trproj-wf} is two lines. Theorem \ref{thm:trproj-wf} is
strictly stronger than master's stub, the hypothesis on the major premise being now a field; as a
result the projection case of Theorem \ref{thm:trexprs-wf} shrinks rather than grows. The new
parameters on \texttt{TrProj} create one obligation that master did not have,
Theorem \ref{thm:trproj-mono}, which is discharged using the \texttt{iota} branch's monotonicity
of the pattern registry. Two of the five proved forms also carry hypotheses master's stubs did not:
\texttt{Ordered env} on \ref{thm:trproj-weak} and, on \ref{thm:trproj-instn}, that plus a typing
for the substituted term; each is available at the single call site. Outside the projection section
the branch also added the three spine lemmas of Theorem \ref{thm:mkapplist-spine}, one of which is
used at \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{50}, and the inversion
Theorem \ref{thm:trexprs-mkapplist-inv}, used five times at \texttt{WHNF.lean:87} to \texttt{:93},
both in the projection and $\iota$ proof. Later, the projection relation is what
\ref{thm:tr-env-proj-defeq} in Chapter \ref{chap:trenv} supplies the kernel-side reduction facts
for, and what \texttt{inferProj} in Chapter \ref{chap:typechecker} is meant to produce.

The \texttt{iota} branch contributed two unrelated things here. The first is the self-contained
block of Lemma \ref{family:lctx-empty-decl} and Theorem \ref{thm:mkforall-eq-fold}: lookups in a
chain of \texttt{mkLocalDecl} steps over the empty context, with the freshness side condition
deliberately dropped so that a six-step chain does not generate six obligations, five of its
eight declarations being consumed by the hand-built \texttt{Quot} axiom shapes in
\srcloc{Lean4Lean/Verify/Environment/Quot.lean}{1} and the rest serving them locally. The second is not a contribution of content
but a propagation: eight lemma signatures in the literal family
(Lemma \ref{family:trexprs-literals}) and two in Theorem \ref{thm:trexprs-ofconst} were
strengthened from \texttt{Ordered} to \texttt{OrderedStrong}, forced by the new signature of
\texttt{HasType.const\_inv} on that branch.

What remains open. Theorem \ref{thm:trproj-weak-inv} and Theorem \ref{thm:trproj-uniq} are still
\texttt{sorry}. The first is blocked on a master admission, \texttt{VEnv.IsDefEqU.weakN\_iff}, and
keeps Theorem \ref{thm:trexprs-weakfv-inv} and the three \texttt{weakN\_inv} lemmas of
Definitions \ref{def:conditionallytyped}, \ref{def:conditionallyhastype} and
\ref{def:conditionallywhnf} sorry-dependent, exactly as on master. The second is blocked on
facts about the relation itself, and keeps Theorem \ref{thm:trexprs-uniq},
Lemma \ref{family:trexpr-builders} and everything built on them sorry-dependent; its docstring
does not address how the per-field level list is pinned, which may mean the relation is
under-constrained rather than the proof merely unwritten. Beyond this chapter, nothing constructs
a \texttt{TrProjCtor} witness in general: \texttt{inferProj.WF\_struct} is \texttt{sorry}, so the
relation is inhabited only by the hand-built examples of Chapter \ref{chap:proj}.
```

### Section "Review notes"

```latex
\section{Review notes}

\begin{itemize}
\item \textbf{Medium.} \texttt{TrProj.uniq} is still \texttt{sorry}
(\srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{992}). Its docstring lists what a proof needs, unique
typing of the projection function, type-former injectivity for the structure's level list, its
parameters and the head names, and functionality of the $\iota$ registry for the parameter count
and the field count, but it does not say how the per-field level list \texttt{uss} is pinned. Two
\texttt{TrProjCtor} witnesses for the same projection may choose different \texttt{uss}, in which
case the two expansions are syntactically different recursor applications at different universe
instances and a definitional equality between them is not obviously available. Either the sketch
is incomplete or \texttt{TrProjCtor} is under-constrained. \ref{thm:trexprs-uniq} and the
\texttt{proj} builder of \ref{family:trexpr-builders} depend on this hole.
\item \textbf{Medium.} \texttt{TrProj.weak'\_inv} is still \texttt{sorry}
(\srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{745}). The docstring correctly traces it to the
admitted master lemma \texttt{IsDefEqU.weakN\_iff}
(\srcloc{Lean4Lean/Theory/Typing/UniqueTyping.lean}{172}), but the consequence is that
\ref{thm:trexprs-weakfv-inv} and all three \texttt{Conditionally} strengthening lemmas
(\ref{def:conditionallytyped}, \ref{def:conditionallyhastype}, \ref{def:conditionallywhnf}) remain
sorry-dependent, and those are a large part of the checker's specification.
\item \textbf{Medium.} \texttt{TrProjCtor.pat} (\srcloc{Lean4Lean/Verify/Typing/Expr.lean}{97})
asserts only that \emph{some} reduct is registered under the $\iota$ key; the reduct itself is not
pinned, so \ref{def:trproj} alone does not determine reduction behaviour, and the key, being a
sum, does not exclude a different motive/minor/index split adding up to the same number. The
docstring acknowledges this and defers to \ref{thm:tr-env-proj-defeq} for the kernel-side facts,
but the relation is weaker than it looks, and this is the stated obstacle to
\ref{thm:trproj-uniq}.
\item \textbf{Low.} \texttt{TrProj} (\srcloc{Lean4Lean/Verify/Typing/Expr.lean}{133})
existentially quantifies six pieces of data, two of which are pinned by other fields: the
parameter count is the length of the parameter list by \texttt{params\_length}, and the field
telescope is determined by the constructor name, the level list and the parameters by
\texttt{ctor}. Replacing them by definitions would shrink the relation and remove an obligation
from each of the three proofs that rebuild the record (\texttt{weak'}, \texttt{instN},
\texttt{instL}), where they reappear as \texttt{by simpa} and \texttt{by rw [hlen]}.
\item \textbf{Low.} The \texttt{iota} block installs a global \texttt{DecidableEq FVarId} instance
inside \texttt{namespace Lean.LocalContext}
(\srcloc{Lean4Lean/Verify/LocalContext.lean}{183}), under a section heading about the empty local
context. The instance has nothing to do with \texttt{LocalContext}, and given the project's own
\texttt{LawfulBEq FVarId} (\srcloc{Lean4Lean/Verify/Expr.lean}{12}) it could have been
\texttt{instDecidableEqOfLawfulBEq}, as is already done for \texttt{DefinitionSafety} at
\srcloc{Lean4Lean/Verify/Expr.lean}{51}. No conflict exists today, since Lean core has no such
instance, but the placement invites one.
\item \textbf{Low.} \texttt{TrExprS.mkAppList\_inv}
(\srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{2349}) overlaps with the pre-existing
\texttt{AppStack.build} (\srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{2344}): both invert a
translated application spine. The pointwise-list shape is what the WHNF proof wants, so the
duplication is defensible, but it leaves two spine-inversion idioms in one file.
\item \textbf{Low.} Of the three spine lemmas the \texttt{trproj} branch added to
\srcloc{Lean4Lean/Verify/Expr.lean}{745}, only \texttt{getAppArgsList\_mkAppList} has an explicit
consumer (\srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{50});
\texttt{getAppFn\_mkAppList} is reached only as a \texttt{@[simp]} lemma, and
\texttt{getAppArgsRevList\_mkAppList} (\srcloc{Lean4Lean/Verify/Expr.lean}{749}) has no consumer
outside its own file, existing only to prove the forward form.
\item \textbf{Low.} The \texttt{iota} branch strengthened eight master lemma signatures in
\srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{1856} and two in
\srcloc{Lean4Lean/Verify/Typing/TrTerm.lean}{104} from \texttt{env.Ordered} to
\texttt{env.OrderedStrong}, forced by the new signature of \texttt{HasType.const\_inv}. Since
\texttt{OrderedStrong} is obtained only through \texttt{VEnv.WF.orderedStrong}, which invokes the
admitted \texttt{VEnv.WF.patsStrong} (\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{334}), every
later use of the literal lemmas (\srcloc{Lean4Lean/Verify/TypeChecker/Reduce.lean}{16},
\srcloc{Lean4Lean/Verify/TypeChecker/IsDefEq.lean}{406},
\srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{420}) now depends on that admission.
\item \textbf{Low.} The scope paragraph of \texttt{TrProjCtor}
(\srcloc{Lean4Lean/Verify/Typing/Expr.lean}{84}) makes precise claims about the kernel's
\texttt{inferProj}, which structures it accepts and when its \texttt{Prop} gate fires, that are
prose only: nothing in the repository formalizes them, and both \texttt{inferProj.WF\_struct} and
\texttt{inferProj.WF} (\srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{392},
\srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{407}) are \texttt{sorry}. The completeness
boundary is therefore asserted, not verified.
\item \textbf{Low.} Within the \texttt{iota} block of
\srcloc{Lean4Lean/Verify/LocalContext.lean}{181}, \texttt{toList\_empty} and \texttt{WF.empty}
exist only to serve \texttt{find?\_empty} three lines later, and have no other consumer.
\end{itemize}
```

## trenv.tex

### Node review notes (16)
- `family:insert-consts-lemmas`: \texttt{insertConsts\_find?\_none} (\srcloc{Lean4Lean/Verify/Environment/Basic.lean}{165}) is dead code: apart from its own statement, its only occurrence is its own recursive call.
- `struct:tr-recursor`: The fields \texttt{all} (\srcloc{Lean4Lean/Verify/Environment/Basic.lean}{240}) and \texttt{k} (\srcloc{Lean4Lean/Verify/Environment/Basic.lean}{245}) are never used anywhere in the repository; \texttt{k} in particular records a flag for which the model has no rule. Looking up the constructor in $m_2$ rather than in the block, by contrast, is a deliberate and documented choice for nested blocks, whose auxiliary recursors fire on older constructors.
- `thm:add-induct-rec-find`: The conclusion is a long existential conjunction rather than a named structure, unlike the dual \ref{thm:add-induct-rec-reg} which feeds \ref{struct:iota-rule}. The asymmetry in style makes the two halves of the $\iota$ interface harder to compare than they need to be.
- `thm:tr-env-structure-rec`: Two caveats. The conclusion does not assert that the returned $cval$ is visible at $safety$, so a caller that needs a \texttt{TrConstant} for it must re-derive visibility. And the argument relies on the naming convention $\mathtt{mkRecName}\ S$ rather than on a structural link, through the \texttt{TrRecursor.name\_major} field: a syntactic assumption about the kernel's \texttt{AddInductive} that is asserted, not proved.
- `thm:tr-env-pats-iota`: The prime in \texttt{pats\_iota'} is a leftover of an earlier unprimed version that no longer exists.
- `struct:iota-rule`: The \texttt{HEq} field is forced by the dependent \texttt{Pattern.RHS} type and is honestly documented, but it makes the structure awkward to consume: the only consumer, \ref{thm:tr-env-proj-defeq}, has to \texttt{cases eq\_of\_heq} it, and uses nine of the eleven fields (all but \texttt{tr} and \texttt{rec\_shape}).
- `thm:tr-env-pats-iota-inv-shape`: Near-redundant. Unlike its sibling \ref{thm:tr-env-pats-iota}, it does not convert the \texttt{SMap.find?} lookups of \texttt{IotaRule} into \texttt{Environment.find?}, so it adds nothing over the primed version, and \ref{thm:tr-env-proj-defeq} still performs those conversions by hand (\srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{1060} and \srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{1072}). Its docstring claims the conversion it does not perform.
- `thm:tr-env-iota-defeq`: The name \texttt{TrEnv.iota\_defeq} places the lemma in the \texttt{TrEnv} namespace although no \texttt{TrEnv} hypothesis appears in it; it is pure theory-layer material and belongs next to \texttt{VEnv.IsDefEq.pat}.
- `family:beta-telescope`: This family is generic \texttt{VExpr} metatheory with no environment-translation content; it sits in \texttt{Verify/Environment/Lemmas.lean} only because \ref{thm:tr-env-proj-defeq} needs it, and belongs in the theory layer. It is also where the projection work picks up \texttt{sorryAx}, but not, as one might expect, only through unique typing: \texttt{mkApps\_inv\_head} uses nothing but \texttt{HasType.app\_inv}, whose \texttt{OrderedStrong} argument is supplied by the \texttt{VEnv.WF} coercion \texttt{VEnv.WF.orderedStrong}, and that is defined from the \texttt{sorry} \texttt{VEnv.WF.patsStrong} (\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{334}). Every lemma of the family is tainted for that reason, whether or not it also uses \texttt{IsDefEqU.of\_l}.
- `thm:tr-env-proj-defeq`: Technically the strongest result of this group, and correctly architected: the projection computation rule is derived from the registered $\iota$ rule rather than postulated. But it is orphaned. No non-test declaration uses it. The places that would use it are \texttt{reduceProjCore.WF} (\srcloc{Lean4Lean/Verify/TypeChecker/Reduce.lean}{143}, \texttt{sorry} at line 145; note that \texttt{reduceProj.WF} one line below it \emph{is} proved, by delegating to \texttt{reduceProjCore.WF}), \texttt{inferProj.WF\_struct} (\srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{392}, \texttt{sorry} at line 398) and \texttt{inferProj.WF} (\srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{407}, \texttt{sorry} at line 410). Its premise \texttt{TrProjCtor} is only ever inhabited by hand in \texttt{Tests/ProjInhabit.lean}, the general construction \texttt{inferProj.WF\_struct} being itself \texttt{sorry}. The parameter name \texttt{kenv} also deviates from the \texttt{env} used by every neighbouring lemma.
- `thm:with-local-decl-run`: Used once, inside \ref{thm:check-eq-type-ok}, but declared outside the \texttt{AddQuotAux} namespace, so a very general name lands in the \texttt{Lean4Lean} root namespace.
- `def:quot-telescope-data`: These abbreviations mirror \texttt{Lean4Lean/Quot.lean} line by line, which is the only way to compute with a monadic expression builder, but nothing links the two beyond the proofs breaking: any change to a binder name, a binder info or the order of the \texttt{withLocalDecl} calls silently invalidates \ref{thm:add-quot-eq}.
- `thm:environment-get-ok`: Declared inside \texttt{AddQuotAux}, so this generally useful lemma has the full name \texttt{Lean4Lean.AddQuotAux.Environment.get\_ok} and is hidden in an auxiliary namespace.
- `family:quot-type-tr`: Sixty lines of hand-built derivation trees: correct, but unreadable and fragile. A \texttt{TrExprS}-building tactic would collapse them, as the \texttt{type\_tac} macro they rely on already notes for its own case.
- `thm:add-quot-wf`: Two smells in the assembly: the four \texttt{checkName} results are extracted by four near-identical seven-line blocks (\srcloc{Lean4Lean/Verify/Environment/Quot.lean}{521}), and the \texttt{safePrimitives} field is rebuilt by a 22-line hand-nested chain of \texttt{Environment.find?\_add\_of\_ne} (\srcloc{Lean4Lean/Verify/Environment/Quot.lean}{584}); a single auxiliary lemma would remove both. Note also that \texttt{Quot.sound}, the only genuine axiom among the quotient constants in the thesis, is not added here (Lean declares it in core), so this theorem covers the four kernel-builtin constants plus the computation rule.
- `family:expr-axioms`: This is the largest single trust assumption of the project: every kernel-level theorem about \texttt{Expr} manipulation rests on it. The identifications are shallow and syntactic, but nothing in the repository checks them beyond inspection.

### Section "Contribution summary"

```latex
\section{Contribution summary}

The \texttt{iota} branch contributed the inductive-block half of this layer. On master
\texttt{AddInduct} was a \texttt{Prop} with no constructors, documented as ``essentially a
\texttt{sorry}'': the \texttt{induct} step of \ref{ind:tr-env} could never fire, so every
environment containing an inductive type lay outside the verified relation, and every consequence
of $\mathtt{TrEnv}'$ was silently restricted to inductive-free environments. The branch replaced it
with a real witness (\ref{struct:add-induct}) recording the kernel data, the four stages of
\texttt{VEnv.addInduct}, a \ref{struct:tr-ind-type} per type former and a \ref{struct:tr-recursor}
per recursor, freshness of every inserted name, and the kernel's actual insertion order as a
permutation of the model's stage order (\ref{def:add-induct-consts}). Supporting it is the
\texttt{insertConsts} map calculus (\ref{def:insert-consts}, \ref{family:insert-consts-lemmas}).
From the witness the branch \emph{derives} the block's bookkeeping instead of assuming it as
further fields: stage recomposition (\ref{family:add-induct-stages}), membership by kind and
absence of $\delta$-values (\ref{family:add-induct-membership}), agreement of the kernel names with
the model's together with their distinctness (\ref{family:add-induct-names}), map well-formedness
(\ref{thm:add-induct-wf}) and two-way lookup transport (\ref{family:add-induct-find}).

The three interface theorems \ref{thm:add-induct-rec-find}, \ref{thm:add-induct-rec-reg} and
\ref{thm:add-induct-ctor-find} are what the rest of the chapter consumes. They feed, on the
alignment side, \ref{thm:aligned-add-rules} and \ref{thm:aligned-add-induct}, which replace
master's one-line \texttt{nomatch} for the \texttt{induct} case and isolate the whole
kernel-order-versus-model-order difficulty in a single permutation argument; and, on the reduction
side, \ref{thm:tr-env-pats-iota}, which says every kernel recursor rule is a registered $\iota$
pattern of the model, and its composition \ref{thm:tr-env-iota-rec} with
\ref{thm:tr-env-iota-defeq}. A second, unplanned consequence is the whole of
\srcloc{Lean4Lean/Verify/Environment/Quot.lean}{1}: on master \texttt{checkEqType.WF} proved
\texttt{False}, because a \texttt{TrEnv} could not contain the inductive \texttt{Eq}, so quotient
initialization was well-formed by vacuity. Once \texttt{AddInduct} became inhabitable that argument
evaporated and the branch had to prove it for real, which is \ref{thm:with-local-decl-run} through
\ref{thm:add-quot-wf}: a symbolic replay of the kernel's expression builder
(\ref{def:quot-telescope-data}, \ref{family:quot-telescope-find}, \ref{def:quot-tactics}), the
evaluation of the four \texttt{mkForall} telescopes (\ref{family:quot-type-eqs},
\ref{thm:add-quot-eq}), the analysis of \texttt{checkEqType} (\ref{def:check-eq-type-shape},
\ref{thm:environment-get-ok}, \ref{thm:check-eq-type-ok}), explicit translations of the four
quotient types (\ref{family:quot-type-tr}, \ref{thm:quot-ready}), and the assembly
\ref{thm:exists-add-quot}, \ref{thm:add-quot-wf}. That last theorem discharges the
\texttt{quotDecl} case of \ref{thm:add-decl-wf} for real.

The \texttt{trproj} branch contributed the structure-likeness and projection half. Its additions to
the inductive-block vocabulary are the parameters and the \texttt{all}, \texttt{numParams},
\texttt{numIndices} and arity fields of \ref{struct:tr-ind-type} and the \texttt{name\_major} field
of \ref{struct:tr-recursor}. On them rest \ref{thm:aligned-constants-pull},
\ref{thm:tr-env-ctor-arity} (a constructor's model type has $\Pi$-arity
$numParams + numFields$) and \ref{thm:tr-env-structure-rec}, which takes exactly the three tests
the kernel's \texttt{inferProj} and \texttt{reduceProjCore} perform before accepting a projection
and returns the recursor's telescope split and the constructor's parameter count. The branch then
built the inverse of the $\iota$ interface: \ref{struct:iota-rule} bundles the kernel data behind
one registered pattern together with its model-side shape, \ref{thm:iota-rule-step} transports it
along the non-\texttt{induct} steps, and \ref{thm:pats-iota-inv-shape} (restated at the kernel
environment level as \ref{thm:tr-env-pats-iota-inv-shape}) recovers a kernel rule from a registered
pattern. With the $\beta$-telescope calculus \ref{family:beta-telescope} these combine into
\ref{thm:tr-env-proj-defeq}: the recursor expansion of the $i$-th projection of a value
definitionally equal to a saturated constructor spine is definitionally equal to the $i$-th field.
The architecture is the right one, in that the projection computation rule is derived from the
registered $\iota$ rule rather than postulated alongside it.

Connection to the rest of the blueprint. The $\iota$ interface reaches the kernel model at exactly
one point, \ref{thm:vtc-iota-reduce-core}, which has no \texttt{sorry} of its own; the projection work reaches it at one
point through \ref{thm:tr-expr-mk-app-list}, and otherwise not at all. Upstream, the two branches
depend on the inductive-specification lemmas of Chapter~\ref{chap:inductive} and on the projection
translation \ref{struct:trprojctor} of Chapter~\ref{chap:trexpr}; later, the intended
consumers are \ref{thm:vtc-reduceprojcore} and \ref{thm:vtc-inferproj-struct} in
Chapter~\ref{chap:typechecker}.

What remains open. Nothing in the repository constructs an \texttt{AddInduct} witness from
\texttt{Environment.addInductive}, and the \texttt{inductDecl} case of \ref{thm:add-decl-wf} is
still \texttt{sorry}, so every theorem above is conditional on a hypothesis that is never
discharged: the branches moved the \texttt{sorry} from ``\texttt{AddInduct} is empty'' to
``\texttt{AddInduct} has no producer''. \ref{thm:tr-env-proj-defeq} has no consumer outside
\ref{test:projinhabit-axioms}, because \ref{thm:vtc-reduceprojcore}, \ref{thm:vtc-inferproj-struct}
and \ref{thm:vtc-inferproj} are \texttt{sorry} (\ref{thm:vtc-reduceproj}, which delegates to the
first of these, is itself proved) and its premise \texttt{TrProjCtor} is so far inhabited
only by hand in the tests. Finally both \ref{family:beta-telescope} and
\ref{thm:tr-env-proj-defeq} inherit \texttt{sorryAx} through unique typing
(\texttt{VEnv.WF.orderedStrong}, \texttt{VEnv.WF.patsStrong}), which is outside this group but on
the critical path of its headline result.
```

### Section "Review notes"

```latex
\section{Review notes}

\begin{itemize}
\item \textbf{High.} The \texttt{inductDecl} case of \texttt{addDecl.WF} is still \texttt{sorry}
(\srcloc{Lean4Lean/Verify/Environment.lean}{208}) and nothing anywhere constructs an
\texttt{AddInduct} witness from \texttt{Environment.addInductive}. The entire inductive-block
apparatus of both branches (\ref{struct:add-induct}, \ref{struct:tr-ind-type},
\ref{struct:tr-recursor}, \ref{thm:aligned-add-induct}, \ref{thm:tr-env-pats-iota},
\ref{thm:pats-iota-inv-shape}) is conditional on that hypothesis. The theorems are correct but in
the end-to-end sense currently vacuous.
\item \textbf{High.} \texttt{TrEnv.proj\_defeq} is orphaned
(\srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{1021}): its only consumer in the repository is
the \texttt{\#print axioms} check at \srcloc{Lean4Lean/Tests/ProjInhabit.lean}{595}.
\texttt{reduceProjCore.WF} (\srcloc{Lean4Lean/Verify/TypeChecker/Reduce.lean}{143}),
\texttt{inferProj.WF\_struct} (\srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{392}) and
\texttt{inferProj.WF} (\srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{407}) remain
\texttt{sorry}, so the strongest \texttt{trproj} theorem does not yet connect to the kernel
model. Its premise \texttt{TrProjCtor}
is likewise only ever inhabited by hand in tests, the general construction
\texttt{inferProj.WF\_struct} being itself \texttt{sorry}.
\item \textbf{Medium.} \texttt{TrEnv.pats\_iota\_inv\_shape}
(\srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{903}) is redundant: its proof is literally
\texttt{TrEnv'.pats\_iota\_inv\_shape H hp}, the two statements being definitionally equal, and
unlike its sibling \texttt{TrEnv.pats\_iota'} it does not convert \texttt{SMap.find?} into
\texttt{Environment.find?}. Its docstring claims otherwise, and \texttt{proj\_defeq} still performs
the conversions by hand at \srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{1060} and
\srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{1072}.
\item \textbf{Medium.} \texttt{TrRecursor.all}
(\srcloc{Lean4Lean/Verify/Environment/Basic.lean}{240}) and \texttt{TrRecursor.k}
(\srcloc{Lean4Lean/Verify/Environment/Basic.lean}{245}) are never used anywhere in the repository.
They are extra proof obligations on a producer of \texttt{AddInduct} that buy nothing; \texttt{k}
in particular records the K-like reduction flag, for which the model has no corresponding rule.
\item \textbf{Medium.} \texttt{insertConsts\_find?\_none}
(\srcloc{Lean4Lean/Verify/Environment/Basic.lean}{165}) is dead code: apart from its own statement,
its only occurrence is its own recursive call.
\item \textbf{Medium.} \texttt{AddInduct} is declared without a \texttt{: Prop} ascription
(\srcloc{Lean4Lean/Verify/Environment/Basic.lean}{272}), so it is a \texttt{Type}-valued structure
and the \texttt{induct} constructor of $\mathtt{TrEnv}'$ carries data. This is necessary, since the
derived lemmas project the fields \texttt{ivals}, \texttt{envR} and \texttt{order}, and harmless
for the present consumers, which all eliminate into \texttt{Prop}; but it is a real change to the
shape of the project's central invariant relative to master's
\texttt{inductive AddInduct ... : Prop} and it is nowhere documented. (It does not, as one might
read it, cost $\mathtt{TrEnv}'$ large elimination: with nine constructors it never had any.)
\item \textbf{Medium.} Misfiled material. The $\beta$-telescope family
(\srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{959}) is pure \texttt{VExpr} metatheory with no
environment-translation content and belongs in \texttt{Theory/Typing/Lemmas.lean}; the same holds
for \texttt{TrExpr.mkAppList} (\srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{1166}), which is
\texttt{TrExpr} rebuilding rather than environment bookkeeping. Both live here only because
\texttt{proj\_defeq} needs them.
\item \textbf{Medium.} \texttt{TrEnv.iota\_defeq}
(\srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{917}) is a three-line wrapper over
\texttt{VEnv.IsDefEq.pat} with no \texttt{TrEnv} hypothesis at all, yet is named as if it had one.
\item \textbf{Medium.} Brittleness in \texttt{Quot.lean}: \texttt{AddQuotAux}
(\srcloc{Lean4Lean/Verify/Environment/Quot.lean}{27}) hand-replays the binder names, binder infos
and \texttt{withLocalDecl} order of \texttt{Lean4Lean/Quot.lean}, with nothing linking the two
beyond the proofs breaking, and the \texttt{T\ldots\_tr} derivations
(\srcloc{Lean4Lean/Verify/Environment/Quot.lean}{331}) are sixty lines of hand-built
\texttt{TrExprS} trees. Correct, but expensive to maintain.
\item \textbf{Low.} \texttt{addQuot.WF} extracts the four \texttt{checkName} results with four
near-identical seven-line blocks (\srcloc{Lean4Lean/Verify/Environment/Quot.lean}{521}) and
rebuilds the \texttt{safePrimitives} field with a 22-line hand-nested chain of
\texttt{Environment.find?\_add\_of\_ne} (\srcloc{Lean4Lean/Verify/Environment/Quot.lean}{584});
both are mechanical repetition that a single auxiliary lemma would remove. Also
\texttt{Lean4Lean.withLocalDecl\_run} (\srcloc{Lean4Lean/Verify/Environment/Quot.lean}{20}) and
\texttt{Lean4Lean.AddQuotAux.Environment.get\_ok}
(\srcloc{Lean4Lean/Verify/Environment/Quot.lean}{244}) are generally useful lemmas placed in,
respectively, the root namespace and a private auxiliary namespace.
\item \textbf{Low (reviewer caveat, not a defect).} Some lines the per-line attribution marks as
contributed are master code relocated by the refactor commits:
\texttt{TrConstant.sf\_mono}/\texttt{mono}, \texttt{TrConstVal.mono} and \texttt{TrDefVal.mono}
(\srcloc{Lean4Lean/Verify/Environment/Basic.lean}{34}, moved from \texttt{Lemmas.lean}) and
\texttt{insertDefs\_wf} (\srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{211}, moved from
\texttt{Extension.lean}). Sixteen of the 398 \texttt{iota} lines in \texttt{Basic.lean} are of
this kind, so the raw line counts overstate the branch slightly.
\end{itemize}
```

## primitives-core.tex

### Section "Contribution summary"

```latex
\section{Contribution summary}
\label{sec:vpc-contribution}

Twenty-seven of the seventy-six nodes of this chapter carry a contribution badge, and all of them
carry it for the same reason. No statement about primitives was added, removed or changed on
either branch: the entire delta is one mechanical adaptation of a hypothesis. Counted on the
\texttt{iota} branch itself, twenty-seven declarations changed an \texttt{henv : env.Ordered}
hypothesis to \texttt{henv : env.OrderedStrong} (twenty-five \texttt{theorem} lines, one
\texttt{variable!} line covering \texttt{VExpr.WF.appN\_inv}, and one continuation line of
\texttt{TrExprS.appChar\_inv'}), forty-five call sites changed \texttt{x.ordered} to
\texttt{x.orderedStrong}, and one body line at \srcloc{Lean4Lean/Verify/Primitive.lean}{80} became
\texttt{henv.ordered.constWF} because \texttt{OrderedStrong} is a structure whose first field is
\texttt{Ordered}. That is 73 lines on the branch, of which 71 still carry \texttt{iota} blame at
\texttt{HEAD}; one of them is the single line in
\srcloc{Lean4Lean/Verify/Environment/Primitive/Recursion.lean}{380}. The 5 lines blamed on
\texttt{trproj} are the two hunks of \texttt{git diff iota HEAD} over these files: a three-line
re-wrap of the signature of \ref{vpc:thm:wf-app-inv2} (431--433) and a two-line re-wrap of a call
site inside the proof of \ref{vpc:thm:wf-appn-inv} (455--456), both pushed past 100 columns by the
\texttt{iota} edit. There is no projection content anywhere in this chapter.

The reason for the adaptation is upstream of this chapter. On \texttt{master} the inversion
lemmas this layer lives on, \texttt{VExpr.WF.app\_inv}, \texttt{VExpr.WF.lam\_inv} and
\texttt{HasType.const\_inv}, were provable from \texttt{Ordered} alone. On \texttt{iota} they were
restated over \ref{struct:orderedstrong}, whose third field is subject reduction for the
registered $\iota$ rules (\ref{def:patsstrongon}), and every consumer was dragged along. Within
this chapter the genuine consumers are \ref{vpc:thm:prim-contains-nat} and
\ref{vpc:thm:prim-trnat-trbool}, which go through \texttt{const\_inv}, and
\ref{vpc:thm:wf-appn-inv}, \ref{vpc:thm:wf-inv-prime}, \ref{vpc:thm:lams-ctx},
\ref{vpc:thm:lams-appn}, \ref{vpc:thm:trexprs-appn} and \ref{vpc:thm:goargs}, which go through
\texttt{app\_inv} or \texttt{lam\_inv}. Everything else inherits the hypothesis from those,
mostly through \ref{vpc:thm:prim-nat-bool-typing} and \ref{vpc:def:prim-atoms}.

How it connects. The strengthened hypothesis is carried from the reflection schemas onto the
constant by \ref{vpc:thm:reflects-toconst}, packaged into the recogniser's obligation by
\ref{vpc:thm:data-mkresult} and \ref{vpc:thm:data-mkresultbitwise}, and surfaces at the
verification boundary \ref{vpc:thm:checkdef-wf}, which the declaration checker consumes at
\srcloc{Lean4Lean/Verify/Environment/Checker.lean}{201}. Since \texttt{OrderedStrong} is obtained
from \texttt{VEnv.WF} only through \ref{thm:wf-orderedstrong}, and that rests on the admitted
\ref{thm:wf-patsstrong}, the guarantee the primitive layer offers the kernel is now conditional on
the $\iota$ contribution's one open obligation. That obligation is a \emph{new} source, not the
first: before the branch this layer already reached the \texttt{sorry}s of
\texttt{Theory/Typing/Injectivity.lean} and \texttt{Theory/Typing/UniqueTyping.lean}, through
\ref{vpc:thm:prim-bitwise-operand} and through every node that chains two definitional equalities
(\ref{vpc:lem:prim-isdefequ-app-congr}), and the \texttt{sorry} at \texttt{TrProj.weak'\_inv}
through the typechecker monad's \texttt{M.WF.withLocalDecl}. What is new is that nineteen
declarations in these four files which were \texttt{sorryAx}-free on \texttt{master} are not any
more; they are listed in Section~\ref{sec:vpc-review}.

What remains open on the contributed side is exactly \ref{thm:wf-patsstrong}; nothing in this
chapter can discharge it, and nothing in this chapter is made harder or easier by it. What remains
open as a matter of hygiene is the scope of the edit: it was applied uniformly rather than to the
lemmas that need it, so the blast radius of \ref{thm:wf-patsstrong} in this layer is larger than
the proofs require, and it is what turned nineteen previously unconditional declarations into
conditional ones. Both points are recorded in Section~\ref{sec:vpc-review}.
```

### Section "Review notes"

```latex
\section{Review notes}
\label{sec:vpc-review}

\begin{itemize}
\item \textbf{High.} \srcloc{Lean4Lean/Verify/Primitive.lean}{29}: the \texttt{iota} branch
replaced \texttt{env.Ordered} by \texttt{env.OrderedStrong} in every hypothesis of this layer.
\texttt{OrderedStrong} is derivable from \texttt{VEnv.WF} only through
\texttt{VEnv.WF.orderedStrong}, which is built on
\texttt{VEnv.WF.patsStrong := sorry} (\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{334}). On
\texttt{master} the inversion lemmas this layer uses (\texttt{VExpr.WF.app\_inv},
\texttt{VExpr.WF.lam\_inv}, \texttt{HasType.const\_inv}) were provable from \texttt{Ordered}
alone, and \texttt{Theory/Typing/Strong.lean} contained no \texttt{sorry} at all. After the
change, \texttt{checkDef.WF} and every \texttt{PrimitiveResult} transitively depend on an admitted
subject-reduction lemma for the new generic $\iota$-rule mechanism. Concretely, nineteen
declarations in these four files carried no \texttt{sorryAx} on \texttt{master} and carry one
now, the \emph{only} route being a \texttt{.orderedStrong} coercion the edit inserted:
\texttt{ReflectsBoolBoolBool'.of\_left\_cases} (\srcloc{Lean4Lean/Verify/Primitive.lean}{429}),
\texttt{ReflectsNatNat'.of\_pred\_equations} (\srcloc{Lean4Lean/Verify/Primitive.lean}{458}), the
fourteen shared translation atoms \texttt{hNatT}, \texttt{trNat}, \texttt{predb}, \texttt{addb},
\texttt{divb}, \texttt{modb}, \texttt{mulb}, \texttt{natCod}, \texttt{natCod1}, \texttt{boolCod},
\texttt{trBool}, \texttt{boolOp2Ty}, \texttt{boolOp2Ty\_tgt} and \texttt{bitwiseTy}
(\srcloc{Lean4Lean/Verify/Environment/Primitive/Basic.lean}{1071}), and the three type-pinning
theorems \texttt{Data.mkTyEq}, \texttt{Data.mkTyEq1} and \texttt{Data.mkTyEqBitwise}
(\srcloc{Lean4Lean/Verify/Environment/Primitive/Basic.lean}{1163}). Everything the eighteen
branches of Chapter~\ref{chap:primitives-arith} build on those atoms follows. This is a real
widening of the trust boundary of code that is not part of the $\iota$ contribution, and it is
stated nowhere in the source.
\item \textbf{Medium.} \srcloc{Lean4Lean/Verify/Primitive.lean}{84}: the edit was applied
uniformly rather than minimally. \texttt{natZeroT} (29), \texttt{natSuccT} (34),
\texttt{natPredT} (39), \texttt{natLitT} (84), \texttt{natFstLamApp} (96), \texttt{natIsType}
(114), \texttt{boolLitT} (129), \texttt{boolIsType} (134) and \texttt{appChar\_inv'} (177) invoke
only \texttt{HasType.weak0} (\srcloc{Lean4Lean/Theory/Typing/Lemmas.lean}{610}) and
\texttt{IsDefEq.isType} (\srcloc{Lean4Lean/Theory/Typing/Lemmas.lean}{945}), both of which still
take \texttt{Ordered}; so do \texttt{boolIsType'} and \texttt{natIsType'}
(\srcloc{Lean4Lean/Verify/Environment/Primitive/Basic.lean}{158}). Only
\texttt{contains\_nat\_of\_hasType} (47), \texttt{boolOfBitwise} (76), \texttt{trNat} (122) and
\texttt{trBool} (140) need the stronger hypothesis directly, through
\texttt{HasType.const\_inv}; the five \texttt{natOf*} wrappers and
\texttt{natArrow1}/\texttt{natArrow2} inherit it from those four and are not gratuitous. Keeping
the weaker hypothesis where it suffices would have confined the new \texttt{sorry} dependency to
four lemmas and their transitive users instead of the whole file. The edit reads as a global
search-and-replace, not a considered minimisation.
\item \textbf{Medium.} \srcloc{Lean4Lean/Verify/Environment/Primitive.lean}{6}: the module
docstring claims that ``the checker, extension, and declaration modules introduce no additional
\texttt{sorry}-backed assumptions. The imported type-checker and theory layers retain their own
explicit verification gaps.'' This is still literally true but now reads as a stronger trust
statement than the code supports, since this layer's hypotheses are \texttt{OrderedStrong} and
their only producer is the admitted \texttt{VEnv.WF.patsStrong}. The docstring was not revisited
when the hypotheses were strengthened.
\item \textbf{Medium.} \srcloc{Lean4Lean/Verify/Primitive.lean}{210}: pre-existing on
\texttt{master}, and unchanged by either branch, this chapter was never unconditional.
\texttt{bitwiseOperand} uses \texttt{IsDefEqU.forallE\_inv}
(\srcloc{Lean4Lean/Theory/Typing/Injectivity.lean}{23}) and
\texttt{IsDefEqU.of\_l} (\srcloc{Lean4Lean/Verify/Primitive.lean}{244}) goes through
\texttt{IsDefEq.uniq} (\srcloc{Lean4Lean/Theory/Typing/UniqueTyping.lean}{13}), both
\texttt{sorry}-backed. Every node below that chains two definitional equalities or inverts a
$\Pi$ inherits that taint. A third, also pre-existing, reaches every theorem of this chapter that
runs in the typechecker monad: \texttt{TypeChecker.M.WF.withLocalDecl}
(\srcloc{Lean4Lean/Verify/TypeChecker/Basic.lean}{489}) restores its caches with
\texttt{ConditionallyHasType.weakN\_inv} and \texttt{ConditionallyWHNF.weakN\_inv}
(\srcloc{Lean4Lean/Verify/Typing/ConditionallyTyped.lean}{18}), which go through
\texttt{TrExprS.weakFV\_inv} to the \texttt{sorry} at \texttt{TrProj.weak'\_inv}
(\srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{747}); that \texttt{sorry} is on \texttt{master}
too, at line 723 of the same file, so this route is pre-existing even though the line now carries
\texttt{trproj} blame. The footprints in this chapter therefore name three independent
pre-existing \texttt{sorry} sources plus the contributed one, not one.
\item \textbf{Medium.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Basic.lean}{856}: the
syntactic guard \texttt{Expr.natBinderTypes}, that every leading binder type of the measure is
literally the constant \texttt{Nat}, is a \emph{hypothesis} of the well-founded-recursion
theorems, not a check the recogniser performs. The docstring argues it holds by \texttt{rfl} at
the call sites because the caller writes the measure, which is true today; the verified statement
is nonetheless conditional on a property of the caller's measure that the kernel never tests.
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive.lean}{73}: dead code,
documented but dead. \texttt{AddsConsts}, \texttt{constants\_stable},
\texttt{constants\_of\_mem}, \texttt{holds\_of\_ne}, \texttt{boolConsts}, \texttt{natConsts},
\texttt{hasPrimitives\_bool}, \texttt{hasPrimitives\_nat}, \texttt{PrimitiveInductiveResult} and
\texttt{checkInductive.WF} form a closed cluster: they use each other and nothing else in the
repository uses any of them, \texttt{AddsConsts} in particular being constructed nowhere. Lines
73--195, 123 of this file's 195, are this pre-staged half, waiting on the \texttt{inductDecl} case
of \texttt{addDecl.WF} (\srcloc{Lean4Lean/Verify/Environment.lean}{208}).
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive.lean}{121}:
\texttt{AddsConsts.hasPrimitives\_bool} (121) and \texttt{AddsConsts.hasPrimitives\_nat} (137)
are byte-for-byte the same proof script with \texttt{boolConsts} and \texttt{natConsts} swapped. A
single lemma parameterised by the three-element constant list would remove the duplication.
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Basic.lean}{431}: the only
\texttt{trproj}-attributed lines in this chapter, 431--433 and 455--456, are a pure line re-wrap;
\texttt{git diff iota HEAD} over these four files is exactly two hunks re-flowing lines the
\texttt{iota} edit had pushed past 100 columns. Any summary of the \texttt{trproj} branch that
counts them as projection work overstates its footprint.
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Basic.lean}{318}: namespace
inconsistency for the \texttt{List} helpers. \texttt{List.Forall2.map\_right'} (222) and
\texttt{List.Forall2.forall\_left} (229) are declared with \texttt{\_root\_.}, while
\texttt{List.Forall2.append\_inv} (318), \texttt{List.forall\_mem\_pair} (333),
\texttt{List.Forall2.snoc} (336), \texttt{List.Forall2.rev} (342),
\texttt{List.Forall2.fvars\_uniq} (357) and \texttt{List.mapIdx\_replicate\_nat} (141) are written
bare inside \texttt{namespace Lean4Lean} and therefore land in \texttt{Lean4Lean.List}, shadowing
the real \texttt{List} namespace inside the project.
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Recursion.lean}{587}:
\texttt{unfoldNatWellFounded.WF'} is a single tactic proof of 1135 lines (587 to 1721) requiring
\texttt{set\_option maxHeartbeats 1000000}. It is the largest obligation in the chapter and, at
that size, not practically reviewable; the surrounding design notes are good but do not substitute
for decomposition. Its \texttt{BlockQ} docstring
(\srcloc{Lean4Lean/Verify/Environment/Primitive/Recursion.lean}{527}) is also stale: it says only
the first two checks are recorded so far, whereas the definition records all four.
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Recursion.lean}{376}: after the
\texttt{iota} edit three adjacent lines spell the same coercion three ways, line 376 passing
\texttt{c.Ewf} bare through the \texttt{CoeOut} instance, line 380 writing
\texttt{.orderedStrong} explicitly and line 381 keeping \texttt{.ordered}. Not wrong, but it takes
a moment to see that these are the same object.
\item \textbf{Low.} Small interface asymmetries, all \texttt{master} and all noted in the node
remarks above: \texttt{ReflectsNatNat'.of\_pred\_equations}
(\srcloc{Lean4Lean/Verify/Primitive.lean}{458}) hard-codes the meta-level \texttt{Nat.pred}
instead of taking it as a parameter, unlike the six sibling schemas, which all take the
meta-level function as a parameter;
\texttt{ReflectsBoolBoolBool'.of\_closed\_cases} (\srcloc{Lean4Lean/Verify/Primitive.lean}{450})
is a repackaging of its own hypotheses; \texttt{VContext.natBinLitBool}
(\srcloc{Lean4Lean/Verify/Environment/Primitive/Basic.lean}{52}) inlines the proof of
\texttt{ReflectsNatNatNat.applyLit} (\srcloc{Lean4Lean/Verify/Environment/Primitive/Basic.lean}{35})
rather than reusing a \texttt{Bool}-valued analogue; and
\texttt{VExpr.liftN\_lams} (\srcloc{Lean4Lean/Verify/Environment/Primitive/Basic.lean}{195})
returns only an existential for the lifted domains where \texttt{liftN\_lams'} (128) computes
them.
\end{itemize}
```

## primitives-arith.tex

### Node review notes (36)
- `prim-cond:struct:condition-wf`: \texttt{ConditionImpl.WF} and \texttt{ReflectNatNat.WF} are the only two declarations in this block with no docstring. The structure lives in \texttt{Type} and is consumed under an existential in \ref{prim-cond:thm:condition-check-wf}, so no consumer can project its data out except through a \texttt{Prop}-valued continuation; that is deliberate and consistent, but it is nowhere said.
- `prim-cond:def:noproj`: \texttt{noProj} exists precisely to sidestep transporting a \texttt{TrProj} obligation (the docstring of \ref{prim-cond:thm:trexprs-weakr} says so). The primitives layer therefore excludes projections by construction rather than supporting them, which is the one direct point of contact between this chapter and the \texttt{trproj} work in chapter~\ref{chap:trexpr}; nothing in either place records the connection.
- `prim-cond:family:vlctx-append`: These are generic \texttt{VLCtx} lemmas declared as \texttt{Lean4Lean.Primitive.VLCtx.*} rather than next to the rest of the \texttt{VLCtx} API in \texttt{Lean4Lean/Verify/Typing/}; the qualified names are easy to mistake for \texttt{Lean4Lean.VLCtx.*}.
- `prim-cond:thm:trexprs-weakr`: After the \texttt{iota} merge this still takes \texttt{env.Ordered}, unlike the six neighbouring lemmas that were raised to \texttt{OrderedStrong}; nothing in the file says which lemmas need which strength.
- `prim-cond:thm:trexprs-ofclosed`: This takes the full \texttt{VEnv.WF} where its immediate neighbours take \texttt{Ordered} or \texttt{OrderedStrong}; that is master's choice, but together with the \texttt{iota} upgrade it leaves the file with three different environment hypotheses and no stated rationale for any of them.
- `prim-cond:family:trexprs-bvars`: Four hand-rolled instances of what one indexed lemma would state, and the only declarations in the file escaped with \texttt{\_root\_} to \texttt{Lean4Lean.TrExprS} rather than \texttt{Lean4Lean.Primitive.TrExprS}.
- `prim-cond:thm:trexprs-boolprop`: Changed on \texttt{iota}: the hypothesis was \texttt{henv : env.Ordered} on master and is \texttt{henv : env.OrderedStrong} here. The statement is therefore strictly weaker than master's, and every instantiation of it is now \texttt{sorry}-dependent; no comment on the line says so.
- `prim-cond:thm:trexprs-propboolprop`: Changed on \texttt{iota} (\texttt{Ordered} to \texttt{OrderedStrong}). It is also the only one of the six upgraded lemmas with no docstring at all, although its five siblings have one.
- `prim-cond:thm:trexprs-boolnat3`: Changed on \texttt{iota} (\texttt{Ordered} to \texttt{OrderedStrong}).
- `prim-cond:thm:trexprs-natnatprop`: Changed on \texttt{iota} (\texttt{Ordered} to \texttt{OrderedStrong}).
- `prim-cond:thm:trexprs-divgotype`: Changed on \texttt{iota} (\texttt{Ordered} to \texttt{OrderedStrong}).
- `prim-cond:thm:trexprs-natproj`: Changed on \texttt{iota} (\texttt{Ordered} to \texttt{OrderedStrong}).
- `prim-cond:thm:reflection-gentele`: Not one character of this proof was changed on either branch, and it is \texttt{sorry}-dependent now where on \texttt{master} it was not. The single call \texttt{hXY'.subst E.wf} at \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{1236} used to coerce \texttt{VEnv.WF} to \texttt{VEnv.Ordered}, which is what \texttt{VEnv.IsDefEqU.subst} took on \texttt{master}; the same text now coerces to \texttt{VEnv.OrderedStrong} and so routes through \ref{thm:wf-patsstrong}. Line-level attribution understates how far the change reaches.
- `prim-cond:thm:reflection-gentelet`: Changed on \texttt{iota} in the proof only (\srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{1256}): \texttt{hX'.subst E.wf.ordered} became \texttt{hX'.subst E.wf.orderedStrong}, because \texttt{VEnv.HasType.subst} now requires the strong environment. The statement is unchanged, so the only visible effect is that the theorem became \texttt{sorry}-dependent.
- `prim-cond:thm:reflection-genph`: Changed on \texttt{iota} in the proof only (\srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{1299}), from \texttt{.subst E.wf.ordered} to \texttt{.subst E.wf.orderedStrong}.
- `prim-cond:thm:reflection-checkite-wf`: Changed on \texttt{iota} in the proof only. At \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{1448} the merge writes \texttt{c.Ewf.orderedStrong} while lines 1449 and 1450, two further calls to the same lemma, still pass \texttt{c.Ewf} and let the \texttt{CoeOut} instance fire. The resolution is minimal, which is defensible, but the file now reads as if the two spellings meant different things.
- `prim-cond:thm:reflection-checknatdite-wf`: Changed on \texttt{iota} in the proof only (lines 1792 and 1850). At 374 lines (1617--1990) this is the second-longest declaration in the chapter, one line shorter than \ref{prim-bitwise:thm:checknatbitwise-wf}; it is broken up by comments, but its internal \texttt{have} names follow no documented scheme.
- `prim-cond:thm:condition-reflect-dite`: Changed on \texttt{iota} in the proof only: seven \texttt{.ordered} to \texttt{.orderedStrong}, at lines 2037, 2066, 2088--2091 and 2095.
- `prim-cond:family:condition-fvarsin`: \texttt{Condition.fvarsIn\_ite} is dead: a full-repository grep finds no use of it. Its sibling \texttt{fvarsIn\_dite} is used once, at \srcloc{Lean4Lean/Verify/Environment/Primitive/DivMod.lean}{163}.
- `prim-cond:thm:condition-reflect-ite`: Changed on \texttt{iota} in the proof only: seven \texttt{.ordered} to \texttt{.orderedStrong} at lines 2733 and 2747--2757.
- `prim-cond:thm:condition-check-wf`: Changed on \texttt{iota} in the proof only (\srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{2913}). It is the boundary every conditional-driven clause consumes -- \texttt{Nat.div}, \texttt{Nat.mod}, \texttt{Nat.gcd} and \texttt{Nat.bitwise}, at \srcloc{Lean4Lean/Verify/Environment/Primitive/DivMod.lean}{98}, \srcloc{Lean4Lean/Verify/Environment/Primitive/Gcd.lean}{29} and \srcloc{Lean4Lean/Verify/Environment/Primitive/Bitwise.lean}{46} -- though not the fifteen simple clauses, which reach \texttt{sorryAx} by other routes. Nothing at that line or in the module docstring says a \texttt{sorry} enters here.
- `prim-clauses:thm:checknatadd-wf`: Changed on \texttt{iota} in the proof only (\srcloc{Lean4Lean/Verify/Environment/Primitive/Clauses.lean}{53}, lines 53 and 54): the two \texttt{HasPrimitives} typing accessors are now passed \texttt{ctx.Ewf.orderedStrong}.
- `prim-clauses:thm:checknatsub-wf`: Changed on \texttt{iota} in the proof only (lines 89 and 105).
- `prim-clauses:thm:checknatmul-wf`: Changed on \texttt{iota} in the proof only (line 118).
- `prim-clauses:thm:checknatpow-wf`: Changed on \texttt{iota} in the proof only (line 148).
- `prim-clauses:family:checknat-bitwise-ops`: Changed on \texttt{iota} in the proofs only (lines 233, 260 and 288), each the \texttt{boolOfBitwise} call. The three proofs are otherwise near-duplicates of about 25 lines each, differing in the boolean operation and in whether a probe is opened; \ref{prim-clauses:thm:checknatboolcases-wf} directly above them shows the parametrised alternative that would have removed the repetition.
- `prim-clauses:family:checknat-shifts`: Changed on \texttt{iota} in the proofs only (lines 321 and 349), each the \texttt{natOfMul}/\texttt{natOfDiv} call that recovers \texttt{Nat} from the guard.
- `prim-clauses:thm:checkcharofnat-wf`: Changed on \texttt{iota} in the proof only (line 389), the \texttt{trNat} call.
- `prim-clauses:thm:checkstringoflist-wf`: Changed on \texttt{iota} in the proof only (lines 404 and 405), the two \texttt{appChar\_inv'} calls.
- `prim-divmod:thm:checknatfuelrec-wf`: Changed on \texttt{iota} in the proof only (lines 230 and 232): the two \texttt{subst} calls that close the five binders now take \texttt{c.Ewf.orderedStrong}.
- `prim-divmod:thm:checknatfuelrec-wf`: The interface is twenty-one explicit hypotheses over a forty-nine-line statement (\srcloc{Lean4Lean/Verify/Environment/Primitive/DivMod.lean}{22}, lines 22--70) and leaks a good deal of the checker's internal structure: \texttt{lhs}, \texttt{H}, \texttt{els} and \texttt{top} are \texttt{Expr} builders supplied by the caller, \texttt{goName} the name of the auxiliary it recurses through. The parameter groups are commented and factoring the two clauses through one theorem is clearly right; the cost is that the statement cannot be read without the recognizer beside it.
- `prim-divmod:thm:checknatmod-wf`: Changed on \texttt{iota} in the proof only (lines 290, 294, 296, 308, 390 and 392).
- `prim-divmod:thm:checknatdiv-wf`: Changed on \texttt{iota} in the proof only (lines 452, 456, 462, 519 and 521). The proof is noticeably shorter than \ref{prim-divmod:thm:checknatmod-wf}'s because \texttt{Nat.div} has no separate base equation, which is evidence that the shared lemma is factored at the right place.
- `prim-gcd:thm:checknatgcd-wf`: Changed on \texttt{iota} at line 24, where the local abbreviation \texttt{hE := ctx.Ewf.orderedStrong} replaced \texttt{ctx.Ewf.ordered}, and at lines 95--100, five \texttt{subst} calls now taking \texttt{E.wf.orderedStrong}.
- `prim-bitwise:thm:checknatbitwise-wf`: Changed on \texttt{iota} in the proof only (lines 41, 86, 150, 152, 182, 315, 362). The two \texttt{trproj} lines in this chapter are here as well (\srcloc{Lean4Lean/Verify/Environment/Primitive/Bitwise.lean}{203}): that commit is a pure re-wrap (``style: wrap the lines over the column limit''), and the \texttt{hE.ordered} the wrapped line carries was already \texttt{iota}'s.
- `prim-bitwise:thm:checknatbitwise-wf`: The local abbreviation \texttt{hE := ctx.Ewf.orderedStrong} introduced at line 41 is immediately downgraded by \texttt{hE.ordered} at seven of its twelve uses (86, 150, 152, 182, 204, 315, 362), so the name advertises a strength most of its uses do not want. At 375 lines this is also the longest declaration of the chapter and the only clause-level \texttt{WF} theorem in the group without a docstring.

### Section "Contribution summary"

```latex
\section{Contribution summary}
\label{sec:prim-arith-contribution}

Twenty-six of the fifty-eight nodes of this chapter carry a contribution badge, and every one of
them carries it for the same reason. No declaration was added to these five files and none was
removed; the diff against \texttt{master} is 69 insertions against 68 deletions, the extra line
being the \texttt{trproj} re-wrap. Of 4655 lines, 67 are attributed to \texttt{iota} and 2 to
\texttt{trproj}, and all 67 re-thread one hypothesis between \texttt{VEnv.Ordered} and
\ref{struct:orderedstrong}: 61 raise it, and 6 -- the \texttt{Bitwise.lean} uses of the one
local abbreviation that was raised -- lower it again. Six theorem
\emph{statements} changed (\ref{prim-cond:thm:trexprs-boolprop},
\ref{prim-cond:thm:trexprs-propboolprop}, \ref{prim-cond:thm:trexprs-boolnat3},
\ref{prim-cond:thm:trexprs-natnatprop}, \ref{prim-cond:thm:trexprs-divgotype},
\ref{prim-cond:thm:trexprs-natproj}), and they changed only because the
\texttt{HasPrimitives} accessors they call were strengthened two files away
(\ref{vpc:thm:prim-trnat-trbool}, \ref{vpc:thm:prim-nat-bool-typing},
\ref{vpc:thm:prim-istype-prime}); of the other 61 lines, 55 write \texttt{c.Ewf.orderedStrong}
or \texttt{E.wf.orderedStrong} where master wrote \texttt{.ordered} and 6 write
\texttt{hE.ordered} where master wrote \texttt{hE}. The 2 \texttt{trproj} lines
(\srcloc{Lean4Lean/Verify/Environment/Primitive/Bitwise.lean}{203}) re-wrap one over-long line
inside \ref{prim-bitwise:thm:checknatbitwise-wf}; the content they carry is \texttt{iota}'s.

Why the edit was necessary is settled in other chapters, and the reasoning is sound. On
\texttt{master} the strong system was reached from \texttt{Ordered} by a proved theorem, which was
available only because the $\iota$ stage of \texttt{Ordered} was a stub. Once $\iota$ rules have a
real specification, an environment can be \texttt{Ordered} and still admit $\iota$ rules that do
not preserve types, so the theorem is false as stated and the honest replacement carries subject
reduction for the registered rules as a third field of \ref{struct:orderedstrong}. Two of that
structure's three fields are then discharged from \texttt{VEnv.WF} only through
\ref{thm:wf-patsstrong}: \ref{thm:wf-orderedstrong} builds its \texttt{strong} field as
\texttt{H.strong H.patsStrong} and its \texttt{pats} field from \texttt{H.patsStrong} directly
(\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{339}).

How it connects. Every result in this chapter discharges the recognizer's obligation
\texttt{PrimitiveResult} (\ref{vpc:struct:primitiveresult}) for the declaration checker of
chapter~\ref{chap:primitives-core}. The four conditional-driven clauses reach it through
\ref{prim-cond:thm:condition-check-wf}; the fifteen simple clauses of \texttt{Clauses.lean} use
no \texttt{Condition} and reach \texttt{sorryAx} through the probe and \texttt{HasPrimitives}
lemmas instead. Either way the branch's single open obligation is now a hypothesis of
every arithmetic primitive: \ref{prim-clauses:thm:checknatadd-wf} through
\ref{prim-clauses:thm:checkstringoflist-wf}, \ref{prim-divmod:thm:checknatdiv-wf},
\ref{prim-divmod:thm:checknatmod-wf}, \ref{prim-gcd:thm:checknatgcd-wf} and
\ref{prim-bitwise:thm:checknatbitwise-wf} all depend on \ref{thm:wf-patsstrong}, where on
\texttt{master} they depended only on \texttt{VEnv.Ordered}. The two clause nodes whose own
text escaped the edit, \ref{prim-clauses:thm:checknatpred-wf} and
\ref{prim-clauses:thm:checknatboolcases-wf} (four declarations in all), are no exception: the lemmas they call --
\ref{vpc:thm:withprobe}, \ref{vpc:thm:reflects-pred-eqns}, \ref{vpc:thm:reflects-ctor-cases} --
were strengthened in chapter~\ref{chap:primitives-core}, and the \texttt{CoeOut} coercion inserts
the rest, which is precisely what makes the change invisible in the source.

What remains open on the contributed side is exactly \ref{thm:wf-patsstrong}; nothing in these
five files can discharge it, and nothing in them is made harder or easier by it. What remains open
as a matter of hygiene is that the change is nowhere declared where it is consumed: no touched
line records that \texttt{orderedStrong} is where a \texttt{sorry} enters, three of the five
files have no module docstring at all, and the file left with three different environment
hypotheses (\texttt{VEnv.WF}, \texttt{Ordered}, \texttt{OrderedStrong}) gives no rationale for
any of them. The line counts above should also not be read as the extent of the change: because
the \texttt{CoeOut} instance's target moved, master proofs that neither branch edited became
\texttt{sorry}-dependent too, \ref{prim-cond:thm:reflection-gentele} being the clearest case.
Both points are recorded in Section~\ref{sec:prim-arith-review}. One further loose end is
\ref{prim-cond:def:noproj}: the primitives layer excludes \texttt{Expr.proj} by construction
precisely to avoid transporting a \texttt{TrProj} obligation, which is the one place where this
chapter touches the \texttt{trproj} work of chapter~\ref{chap:trexpr}, and neither side records
the connection.
```

### Section "Review notes"

```latex
\section{Review notes}
\label{sec:prim-arith-review}

\begin{itemize}
\item \textbf{High.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{421}: all 67
\texttt{iota}-attributed lines in these five files are the
\texttt{VEnv.Ordered}~$\rightsquigarrow$~\texttt{VEnv.OrderedStrong} re-threading, and
\texttt{OrderedStrong} is obtained from \texttt{VEnv.WF} only through
\texttt{VEnv.WF.orderedStrong}, two of whose three fields rest on
\texttt{VEnv.WF.patsStrong := sorry} (\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{334}). Every
theorem in this chapter therefore now depends on that open obligation, where on \texttt{master}
they depended only on \texttt{Ordered}. The declaration site says so, in a comment at
\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{342}; none of the consuming files does. The
\texttt{CoeOut} instance at \srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{343} hides most of
the coercions: not one of the roughly seventy touched call sites carries a comment saying that
\texttt{ctx.Ewf.orderedStrong} is where a \texttt{sorry} enters, \texttt{Clauses.lean}'s and
\texttt{Condition.lean}'s module docstrings do not say so, and \texttt{DivMod.lean},
\texttt{Gcd.lean} and \texttt{Bitwise.lean} have no module docstring at all. A reviewer
reading \texttt{Clauses.lean} or \texttt{Gcd.lean} alone would conclude that the arithmetic
primitives are fully verified.
\item \textbf{High.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{1236}: the
\texttt{sorry} does not enter only at the attributed lines. \texttt{Reflection.WF.genTele}
(\ref{prim-cond:thm:reflection-gentele}) is master-attributed on every line of its statement and
proof, and is \texttt{sorry}-tainted on this branch and was not on \texttt{master}: its one call
\texttt{hXY'.subst E.wf} used to coerce \texttt{VEnv.WF} to \texttt{VEnv.Ordered}, which is what
\texttt{VEnv.IsDefEqU.subst} took on \texttt{master}; that lemma now takes
\texttt{VEnv.OrderedStrong} (\srcloc{Lean4Lean/Theory/Typing/Strong.lean}{1299}), so the same
text coerces the other way. Any count of ``lines the branch
changed'' therefore understates the blast radius, in this chapter and elsewhere.
\item \textbf{Medium.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{26}: stale
module docstring. Lines 26--30 say that \texttt{Nat.mod} and \texttt{Nat.div} call
\texttt{Condition.check} before their first \texttt{withLocalDecl} but that the calls in
\texttt{Nat.bitwise} and in \texttt{unfoldNatWellFounded}'s \texttt{eager} gadget ``currently sit
under binders \ldots\ so both can be hoisted''. The hoisting has already happened:
\srcloc{Lean4Lean/Primitive.lean}{409} runs both \texttt{Condition.check} calls for
\texttt{Nat.bitwise} before the operator binder and \srcloc{Lean4Lean/Primitive.lean}{372} does
the same for \texttt{Nat.gcd}, which is why \texttt{Bitwise.lean} (lines 46--47) and
\texttt{Gcd.lean} (line 29) can pass \texttt{rfl} for \texttt{hnil}. The paragraph describes a
state of the code that no longer exists.
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{485}: the file
now carries three different environment hypotheses with no stated rationale: \texttt{VEnv.WF} at
\ref{prim-cond:thm:trexprs-ofclosed} (540), \texttt{VEnv.Ordered} at
\ref{prim-cond:thm:trexprs-weakr} (485) and the \texttt{\_nil\_inv} family (664, 668, 676, 687),
and \texttt{VEnv.OrderedStrong} at the six lemmas of 421, 744, 754, 771, 786 and 855. The last
group was raised only because \texttt{HasPrimitives.trNat} and \texttt{trBool} in
\texttt{Lean4Lean/Verify/Primitive.lean} (lines 122 and 140) and \texttt{natIsType'} in
\texttt{Lean4Lean/Verify/Environment/Primitive/Basic.lean} (line 163) were raised; nothing in
this file records that, so the distinction looks arbitrary.
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{1448}:
inconsistent spelling of the environment hypothesis inside a single proof. Line 1448 writes
\texttt{VExpr.WF.lam\_inv' c.Ewf.orderedStrong} while lines 1449 and 1450, two further calls
to the same lemma, pass \texttt{c.Ewf} and let the \texttt{CoeOut} instance insert the coercion;
the same mix appears at 1850--1851, where \texttt{TrExprS.appN c.Ewf.orderedStrong} is followed by
\texttt{TrExprS.of\_nil\_any c.Ewf.ordered}. The merge resolution was minimal, which is
defensible, but a reader cannot now tell which occurrences are load-bearing.
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Bitwise.lean}{41}: after the
merge the local abbreviation \texttt{have hE := ctx.Ewf.orderedStrong} carries the wrong strength
for most of its uses: seven of its twelve occurrences immediately downgrade it with
\texttt{hE.ordered} (lines 86, 150, 152, 182, 204, 315, 362). Keeping \texttt{hE : Ordered} and
writing \texttt{ctx.Ewf.orderedStrong} at the sites that need it would read better; as it stands
the local name suggests every use needs the strong environment. \texttt{Gcd.lean} made the same
edit at \srcloc{Lean4Lean/Verify/Environment/Primitive/Gcd.lean}{24} and needed no such
downgrades, so the two files now spell the same idiom differently.
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Bitwise.lean}{31}:
\texttt{checkNatBitwise.WF} (\ref{prim-bitwise:thm:checknatbitwise-wf}) has no docstring, unlike
every other clause-level \texttt{WF} theorem in the group -- \texttt{Clauses.lean} documents all
fifteen of its theorems, and \texttt{Gcd.lean} and \texttt{DivMod.lean} document theirs. It is
also the longest declaration here (375 lines) and the one with the most intricate structure: two
conditions, three nested conditionals and a free operator variable.
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Clauses.lean}{225}:
\texttt{checkNatLAnd.WF}, \texttt{checkNatLOr.WF} and \texttt{checkNatXor.WF}
(\ref{prim-clauses:family:checknat-bitwise-ops}) are near-identical proofs of 25 to 30 lines,
differing only in the boolean operation and in whether the probes are needed.
\texttt{checkNatBoolCases.WF} (\ref{prim-clauses:thm:checknatboolcases-wf}) directly above them
shows the alternative: one parametrised theorem whose two instances are two-line proof terms.
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{2438}:
\texttt{Condition.fvarsIn\_ite} (\ref{prim-cond:family:condition-fvarsin}) is dead code. A
full-repository grep finds no use of it anywhere; its sibling \texttt{fvarsIn\_dite} is used once,
at \srcloc{Lean4Lean/Verify/Environment/Primitive/DivMod.lean}{163}. Either a consumer was removed
or it was written speculatively alongside the \texttt{dite} version.
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{744}:
\texttt{TrExprS.propBoolProp} (\ref{prim-cond:thm:trexprs-propboolprop}) has no docstring although
its five siblings in the same block do, and it is one of the six statements the \texttt{iota}
branch weakened.
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{713}:
\texttt{TrExprS.bvar0} through \texttt{bvar3} (\ref{prim-cond:family:trexprs-bvars}) are four
hand-rolled instances of one indexed statement, and are the only declarations in the file escaped
with \texttt{\_root\_} to \texttt{Lean4Lean.TrExprS} rather than declared in
\texttt{Lean4Lean.Primitive}; the qualified names are easy to confuse with the generic
\texttt{TrExprS} API.
\item \textbf{Low.} \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{307}:
\texttt{noProj} (\ref{prim-cond:def:noproj}) exists to keep \texttt{Expr.proj} out of this layer
so that no \texttt{TrProj} obligation has to be transported, as the docstring of
\ref{prim-cond:thm:trexprs-weakr} states. That is the single point of contact between this chapter
and the \texttt{trproj} contribution of chapter~\ref{chap:trexpr}, and it is recorded in neither
place.
\item \textbf{Informational.} No \texttt{sorry} occurs in any of the five files of this chapter,
and none of them declares an axiom. Every \texttt{sorryAx} in the axiom footprints above is
inherited: through \ref{thm:wf-orderedstrong} and \ref{thm:wf-patsstrong} on the branches, and
through the typechecker correctness theorems and the uniqueness-of-typing lemmas already on
\texttt{master}. The \texttt{Verify/Axioms.lean} bridge axioms relating the model to Lean's own
\texttt{Expr} implementation are likewise inherited from the typechecker layer.
\end{itemize}
```

## typechecker.tex

### Node review notes (8)
- `def:vtc-vstate-wf`: The cache clauses are what make the kernel's memoisation sound and they are the least thesis-like part of the development; Carneiro's text has no counterpart.
- `thm:vtc-iota-reduce-core`: The proof script itself is complete and free of \texttt{sorry}, but four things qualify the result: it has no consumer (\ref{thm:vtc-reducerecursor} is still open); the hypothesis on the major premise is stronger than the kernel's call site, which passes a \texttt{major} obtained by K-conversion, \texttt{whnf}, literal conversion and structure eta; the saturation hypothesis is a second deferred obligation, proved nowhere in the repository and genuinely excluding over-applied constructor applications; and the lemma is not unconditional, since \texttt{\#print axioms} reports \texttt{sorryAx}. See the review notes.
- `thm:vtc-inferproj-struct`: The docstring advertises the lemma as \texttt{inferProj.WF} ``for the structures the model covers (\texttt{TrProjCtor})'', but \texttt{TrProjCtor} does not occur in the statement: the hypotheses are kernel-side metadata, and the implication from them to \texttt{TrProjCtor} is precisely the unproved content. The census also records that nothing in the project depends on this declaration, so as code it is dead.
- `thm:vtc-inferproj`: The \texttt{trproj} edit is a real fix. Master had \texttt{hasty : c.HasType e' ty'} with \texttt{ty'} an auto-bound implicit unrelated to the \texttt{ty'} of the conclusion, so the hypothesis said only that \texttt{e'} has some type, and master's conclusion asserted \texttt{TrTyping (.proj st i e) ty e' ty'}, that is that the \emph{projection} translates to \texttt{e'}, which is the translation of its \emph{subterm}. The new signature is exactly what the caller supplies at \srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{479} and the conclusion now existentially quantifies the projection's own translation. But the lemma is on the import path of \ref{thm:vtc-infertype-prime}, so the project's headline soundness statement now visibly rests on a lemma its own documentation says is false for a class of terms the kernel accepts. Alternatives such as weakening \ref{thm:vtc-infertype-prime}'s conclusion or adding a scope hypothesis are not discussed.
- `thm:vtc-infertype-prime`: This is the theorem the file exists for, and it is only partially proved: its projection case is \ref{thm:vtc-inferproj}, which is not merely open but documented as unprovable without extending the model. Since \texttt{checkType.WF} (\ref{thm:vtc-toplevel}) carries no hypothesis that its input is translatable, the gap is reached by every dependent \texttt{Verify/Environment} result.
- `thm:vtc-tryetaexpansion`: Line 211 carries a commented-out \texttt{have}; dead text left in master.
- `def:vtc-venvs`: A reader grepping the project for uses of choice will be misled by the name, even though the docstring is explicit.
- `thm:vtc-toplevel`: \texttt{checkType.WF} takes only \texttt{e.FVarsIn (· ∈ c.vlctx.fvars)}, with no hypothesis that \texttt{e} is translatable. That is the right statement to want, and it is also why the gap recorded at \ref{thm:vtc-inferproj} propagates to every caller.

### Section "Contribution summary"

```latex
\section{Contribution summary}

The two branches added 163 lines to this group, in two disjoint places.

\textbf{\texttt{iota}.} Upstream, \texttt{inductiveReduceRec} was one monolithic kernel
function. The branch split out the pure $\iota$ step as \texttt{inductiveReduceRecCore}
(\ref{def:kernel-iota-core}) and proved \ref{thm:vtc-iota-reduce-core} about it, 129 lines of
tactic script. The decomposition is the right one: the K-like conversion, the
literal-to-constructor conversion and the structure-eta of the major premise are monadic and
belong in the caller, whereas the $\iota$ step itself is pure and is the only part that has to
be matched against the model's registered rules (\ref{thm:tr-env-iota-rec}). The proof is a
genuinely fiddly index-arithmetic argument, carried out by slicing both spines and matching them
against the pattern machinery of \ref{thm:pattern-matches-varn-const} and
\ref{thm:pattern-iota-rhs-apply}; it is well commented, contains no \texttt{sorry}, and its
docstring is accurate about the saturation caveat. What it does not do is connect to anything:
\ref{thm:vtc-reducerecursor} is still open, no other declaration in the repository mentions the
lemma, and the hypothesis that the major premise is already a constructor application is
stronger than what the kernel's call site provides. The value of the contribution is therefore
prospective, and the missing bridging lemma is exactly the step that would make it a statement
about a kernel step rather than about a syntactic redex.

\textbf{\texttt{trproj}.} Twenty-two lines in the projection case of type inference. The
signature of \ref{thm:vtc-inferproj} was repaired, and the repair is real: master's version had
an auto-bound implicit standing where the caller's type should be, and asserted that the
projection translates to the translation of its own subterm. \ref{thm:vtc-inferproj-struct} was
added as the same statement scoped to the structures \texttt{TrProjCtor}
(\ref{struct:trprojctor}) covers. The substantive contribution, however, is the documentation:
it records that the general statement is not provable as stated and why, and lists the four
model extensions that would be needed to close it. That is an honest and correct diagnosis of a
pre-existing hole in the project's headline soundness theorem. Against it: all three
declarations remain \texttt{sorry}, \ref{thm:vtc-inferproj-struct} has no consumer at all, its
hypotheses are kernel metadata rather than \texttt{TrProjCtor}, and the two obligations that the
new \texttt{TrProj} metatheory was built to support and that sit in this very group,
\ref{thm:vtc-reduceprojcore} and \ref{thm:vtc-tryetastruct}, were not attempted.
```

### Section "Review notes"

```latex
\section{Review notes}

\begin{itemize}
  \item \textbf{High.} \srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{400}: the
    \texttt{trproj} docstring states that \ref{thm:vtc-inferproj} is not provable as stated,
    because kernel-accepted projections of reflexive, indexed and nested single-constructor
    structures have no \texttt{TrExprS} derivation at all. Since
    \ref{thm:vtc-infertype-prime} consumes it and \texttt{checkType.WF} has no hypothesis that
    its input is translatable, the top-level statements \texttt{inferType.WF'} and
    \texttt{checkType.WF} (\srcloc{Lean4Lean/Verify/TypeChecker.lean}{204},
    \srcloc{Lean4Lean/Verify/TypeChecker.lean}{215}) are, as of \texttt{trproj}, known to be
    unprovable without extending the model. The observation is correct and valuable, but it
    leaves an admitted-false lemma on the build path of the project's headline theorem, and the
    alternatives (weakening the conclusion, or adding a scope hypothesis) are not discussed.
  \item \textbf{Medium.} \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{17}:
    \ref{thm:vtc-iota-reduce-core} has no consumer. \ref{thm:vtc-reducerecursor}, two
    declarations below, is still \texttt{sorry}, and a repository-wide grep finds no other
    reference. The contribution proves the hard arithmetic of the $\iota$ step but does not
    connect it to any statement about the kernel.
  \item \textbf{Medium.} \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{24}: the hypothesis
    \texttt{hmaj} requires the major premise \emph{as it occurs in the recursor spine} to
    already be a constructor application, whereas \texttt{inductiveReduceRec}
    (\srcloc{Lean4Lean/Inductive/Reduce.lean}{105}) passes a major obtained from
    \texttt{recArgs[majorIdx]!} by \texttt{toCtorWhenK}, \texttt{whnf}, literal-to-constructor
    conversion and \texttt{toCtorWhenStruct}. A consumer must first rebuild the spine with the
    converted major and transport the translation across the resulting \texttt{IsDefEqU}; that
    bridging step is neither provided nor mentioned in the docstring, which flags only the
    saturation caveat.
  \item \textbf{Medium.} \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{23}: \texttt{hsat},
    exact saturation of the constructor application, is assumed. The docstring says it ``is a
    consequence of the redex being well-typed, and is left to the caller'', but that
    consequence is proved nowhere in the repository, so it is a second deferred obligation of
    unquantified difficulty. It also excludes over-applied constructor applications, which is
    exactly the case where the kernel's ``last \texttt{nfields} arguments'' slicing and the
    pattern's ``arguments past \texttt{numParams}'' slicing genuinely disagree, so the
    hypothesis is doing real work rather than being a convenience.
  \item \textbf{Medium.} \srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{392}:
    \ref{thm:vtc-inferproj-struct} is \texttt{sorry} and unused, referenced only from
    docstrings (\srcloc{Lean4Lean/Tests/ProjInhabit.lean}{15},
    \srcloc{Lean4Lean/Verify/Typing/Expr.lean}{125}); the census records zero dependants. It
    functions as a written-down specification of future work rather than as a result. Its
    docstring advertises it as covering ``the structures the model covers
    (\texttt{TrProjCtor})'' but \texttt{TrProjCtor} does not occur in the statement: the
    hypotheses are kernel-side metadata facts whose implication of \texttt{TrProjCtor} is
    itself the unproved content. The listed conditions are also not the ones \texttt{inferProj}
    checks, so even once proved the lemma could not discharge \ref{thm:vtc-inferproj}.
  \item \textbf{Low.} \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{17}:
    \texttt{\#print axioms} on \ref{thm:vtc-iota-reduce-core} reports \texttt{sorryAx}. The
    proof script itself is complete; the dependency comes through \texttt{TrExprS.instL} and
    \texttt{TrExpr.proj} to the still-open \texttt{TrProj.uniq}
    (\srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{995}) (checked by BFS over the constant
    dependency graph: the declaration does not reach the other open \texttt{TrProj} lemma,
    \texttt{TrProj.weak'\_inv}). Not the contribution's doing, but the lemma should not be
    advertised as unconditional.
  \item \textbf{Low.} \srcloc{Lean4Lean/Verify/TypeChecker/Reduce.lean}{143}:
    \ref{thm:vtc-reduceprojcore} and \ref{thm:vtc-tryetastruct}
    (\srcloc{Lean4Lean/Verify/TypeChecker/IsDefEq.lean}{227}) are the two structure-side
    obligations that the much richer \texttt{TrProj}/\texttt{TrProjCtor} metatheory was built
    to support, and neither was attempted on \texttt{trproj}. Given that the branch closed five
    of master's seven \texttt{TrProj} \texttt{sorry}s in
    \srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{1}, leaving these untouched makes the
    contribution visible in this group look narrower than its supporting infrastructure.
  \item \textbf{Low.} \srcloc{Lean4Lean/Verify/TypeChecker/Reduce.lean}{21}:
    \texttt{reduceBinNatOpG} is an executable definition introduced inside a verification file
    as a generalisation of the kernel's \texttt{reduceBinNatOp}; the kernel function itself is
    only reached indirectly, through \ref{thm:vtc-reducenat}. Duplicating kernel code in a
    proof file is a small maintenance hazard. Master, not contributed.
  \item \textbf{Low (attribution).} \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{1}: the
    precomputed per-line blame tags all 141 new lines in this file as \texttt{trproj}, but
    \texttt{git diff iota trproj} on the file is empty and commits \texttt{7a68882} (iota) and
    \texttt{6fd8a1d} (trproj) are the same patch with the same author date. The lines are the
    \texttt{iota} contribution; \texttt{trproj} carries a duplicate of the commit and then
    merges \texttt{iota} on top in \texttt{20ec229}. Any count of ``trproj lines'' taken from
    the blame files over-attributes this file by 141 lines.
  \item \textbf{Low.} \srcloc{Lean4Lean/Verify/TypeChecker/IsDefEq.lean}{211}: a commented-out
    \texttt{have} is left inside \ref{thm:vtc-tryetaexpansion}. Dead text in master.
  \item \textbf{Low.} \srcloc{Lean4Lean/Verify/TypeChecker.lean}{21}:
    \texttt{VEnvs.axiom\_of\_choice} is a deliberately misleading name for a finite case split.
    The docstring says so, but a reader auditing the project for appeals to choice will still
    be surprised by the grep hit.
  \item \textbf{Context.} Six \texttt{sorry}s remain in the group. Four are master's:
    \ref{thm:vtc-reduceprojcore}, \ref{thm:vtc-reducerecursor}, \ref{thm:vtc-tryetastruct} and
    \ref{thm:vtc-isdefequnitlike}. The other two are not master's:
    \ref{thm:vtc-inferproj-struct} is new on \texttt{trproj} (master has no such declaration),
    and \ref{thm:vtc-inferproj} is \texttt{mixed}, its signature and conclusion rewritten by
    \texttt{trproj} over master's \texttt{theorem} keyword line. Every statement in
    \ref{thm:vtc-toplevel} is partial as a result, and the
    whole group additionally inherits \texttt{sorryAx} from \texttt{TrProj.uniq} through
    \texttt{TrExprS.uniq}.
\end{itemize}
```

## levels.tex

### Section "Review notes"

```latex
\section{Review notes}

Every issue recorded for this group, with severity. No fixes are proposed.

\begin{itemize}
\item \textbf{Medium. Stale doc/code mismatch in the level tests.}
\srcloc{Lean4Lean/Tests/Level.lean}{8} states that what is \emph{not} proved, and so is what the
test file checks, is canonicity of \texttt{normalize'} and completeness of
\texttt{isEquiv'}/\texttt{geq'}. All three are in fact proved:
\srcloc{Lean4Lean/Verify/Level.lean}{3849}, \srcloc{Lean4Lean/Verify/Level.lean}{3861} and
\srcloc{Lean4Lean/Verify/Level.lean}{3870}. The test file's stated purpose no longer matches
reality.
\item \textbf{Medium. Dead code that drags in an extra axiom.} \texttt{mkData\_depth},
\texttt{mkData\_hasParam} and \texttt{mkData\_hasMVar} (\srcloc{Lean4Lean/Verify/Level.lean}{41},
\srcloc{Lean4Lean/Verify/Level.lean}{58}, \srcloc{Lean4Lean/Verify/Level.lean}{73}) are
referenced nowhere in the project. They are the only consumers of the
\texttt{Lean.Level.mkData\_eq} axiom, and they need
\texttt{set\_option allowUnsafeReducibility true} plus
\texttt{attribute [local reducible] Data} (lines 38--39) to elaborate.
\item \textbf{Medium. Trust boundary under the level comparison.} Every main theorem of
\srcloc{Lean4Lean/Verify/Level.lean}{1} factors through \texttt{Std.TreeMap.all\_eq\_all\_toList}
and \texttt{any\_eq\_any\_toList}, declared as axioms at
\srcloc{Lean4Lean/Verify/Axioms.lean}{10} and \srcloc{Lean4Lean/Verify/Axioms.lean}{14} with an
upstream issue link. \texttt{NormLevel.le}, \texttt{NormLevel.addable} and the \texttt{BEq}
instance on \texttt{NormLevel} are all defined through \texttt{TreeMap.all}/\texttt{any}, so the
soundness of the level comparison the kernel performs is modulo these two axioms.
\item \textbf{Medium. The only \texttt{sorryAx} in the group is load-bearing for the memo cache.}
\texttt{RelevantEq.uniq} (\srcloc{Lean4Lean/Verify/EquivManager.lean}{81}) and the two theorems
depending on it reach \texttt{sorryAx} through \texttt{TrProj.uniq}
(\srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{992}, \texttt{:= sorry}), because the \texttt{proj}
case of \texttt{RelevantEq} compares two projections by index alone and ignores the structure
name. \texttt{isDefEq.WF} (\srcloc{Lean4Lean/Verify/EquivManager.lean}{325}) is the entry point
used throughout \texttt{Verify/TypeChecker/}, so this hole is on the main path of the verified
type checker, not in a corner.
\item \textbf{Low. Stale doc comment in \texttt{LevelStd}.}
\srcloc{Lean4Lean/Verify/LevelStd.lean}{155} still says the two \texttt{qsort} facts are
``currently unproved because \texttt{Array.qsort} has no specification in the standard library''
and names \texttt{qsort\_perm\_toList} and \texttt{pairwise\_qsort\_normLt}, neither of which
exists. Both facts are now proved, at \srcloc{Lean4Lean/Verify/LevelStd.lean}{228} and
\srcloc{Lean4Lean/Verify/LevelStd.lean}{234}, on top of
\srcloc{Lean4Lean/Verify/QSort.lean}{1}.
\item \textbf{Low. A large verified component that nothing consumes.}
\texttt{normalize'\_eval} (\srcloc{Lean4Lean/Verify/Level.lean}{3822}),
\texttt{normalize'\_complete} (\srcloc{Lean4Lean/Verify/Level.lean}{3849}),
\texttt{isEquiv'\_complete} (\srcloc{Lean4Lean/Verify/Level.lean}{3861}),
\texttt{geq'\_wf} (\srcloc{Lean4Lean/Verify/Level.lean}{3828}) and
\texttt{geq'\_complete} (\srcloc{Lean4Lean/Verify/Level.lean}{3870}) are used nowhere. Only
\texttt{isEquivList\_wf} reaches the verified type checker. In particular the whole
reconstruction layer, roughly lines 1290--2250, supports \texttt{normalize'}, which the kernel
never calls: \texttt{geq'} is called at \srcloc{Lean4Lean/Inductive/Add.lean}{226}, whose code
path has no verification yet, and \texttt{normalize'} appears only in
\srcloc{Lean4Lean/Tests/Level.lean}{1}.
\item \textbf{Low. Leftover dead comment block.}
\srcloc{Lean4Lean/Verify/Level.lean}{16} to line 27 contains a commented-out
\texttt{VLevel.toLevel} definition and a \texttt{toLevel\_inj ... := sorry}. Harmless, but it is
the only occurrence of the token \texttt{sorry} in the group and will show up in any audit.
\item \textbf{Low. No module docstring on a 3880-line file.} The internal section docstrings in
\srcloc{Lean4Lean/Verify/Level.lean}{1} are excellent, but a reader reaches line 166 before
learning that the file is about Géran's canonical form; the paper is cited only in
\srcloc{Lean4Lean/Level.lean}{24}.
\item \textbf{Low. Dead code in the equivalence manager.} \texttt{RelevantEq.symm}
(\srcloc{Lean4Lean/Verify/EquivManager.lean}{41}), \texttt{RelevantEq.trans}
(\srcloc{Lean4Lean/Verify/EquivManager.lean}{58}) and \texttt{M.WF.bind\_le}
(\srcloc{Lean4Lean/Verify/EquivManager.lean}{205}) are never used, here or elsewhere; the
similarly named \texttt{RecM.WF.bind\_le} at
\srcloc{Lean4Lean/Verify/TypeChecker/Basic.lean}{343} is a different declaration.
\item \textbf{Low. Overstatement in the \texttt{NormLt} header.}
\srcloc{Lean4Lean/Verify/NormLt.lean}{6} says the file ``shows it is a strict weak order''. What
is exported is asymmetry (\srcloc{Lean4Lean/Verify/NormLt.lean}{350}) and transitivity of the
negation (\srcloc{Lean4Lean/Verify/NormLt.lean}{354}), exactly what
\texttt{Array.qsort\_sorted} takes, not a packaged strict-weak-order statement.
\item \textbf{Low. Vendored code carrying upstream TODOs and cross-namespace side effects.}
\srcloc{Lean4Lean/Verify/QSort.lean}{34} says ``These attributes still need to be moved to the
standard library''; lines 36--51 are commented-out attribute experiments; line 52 says ``These
are just the patterns resulting from \texttt{grind}, but the behaviour should be explained!''.
The file also declares four lemmas at \texttt{\_root\_} into the \texttt{List}, \texttt{Array} and
\texttt{Vector} namespaces (lines 58--103) and registers them, plus several core lemmas, as
global \texttt{grind} lemmas, which every importer inherits.
\item \textbf{Low. Documented gap in the \texttt{qsort} specification.}
\srcloc{Lean4Lean/Verify/QSort.lean}{27} notes that there is no public theorem giving
\texttt{(qsort as lt lo hi)[i] = as[i]} for \texttt{i} outside \texttt{[lo, hi]}. The private
lemmas exist (\srcloc{Lean4Lean/Verify/QSort.lean}{150} and
\srcloc{Lean4Lean/Verify/QSort.lean}{167}) but are not exported; the current consumer needs only
permutation and sortedness, so this is a latent limitation rather than a defect.
\item \textbf{Low. Invariant sprawl in the end-to-end theorems.} Each of them threads five to
seven separate side conditions about \texttt{normalize u} by hand
(\srcloc{Lean4Lean/Verify/Level.lean}{1222} and the invariants at lines 1807, 2413, 2443, 2524
and 3600); \texttt{geq'\_complete} (\srcloc{Lean4Lean/Verify/Level.lean}{3870}) takes six of them
in a single \texttt{refine}. Bundling them into one predicate would make these statements easier
to read and to reuse.
\item \textbf{Low. \texttt{Std.TreeMap} as the representation costs a whole layer.} Because two
maps with the same entries need not be the same tree, every consumer has to be shown to factor
through \texttt{toList} (\ref{fam:lvl-congr}, \srcloc{Lean4Lean/Verify/Level.lean}{3177}). The
design consequence is honestly documented, but a sorted-association-list representation would
have avoided roughly 150 lines of pure bookkeeping and the awkward \texttt{BEq NormLevel} at
\srcloc{Lean4Lean/Verify/Level.lean}{3741}.
\item \textbf{Low. Automation opacity in the two smaller files.}
\texttt{baseCmp\_swap} (\srcloc{Lean4Lean/Verify/NormLt.lean}{97}) closes its last goals with
bare \texttt{grind}, and \texttt{normLtAux\_eq} (\srcloc{Lean4Lean/Verify/NormLt.lean}{264}) ends
several of its fourteen cases in \texttt{simp\_all} or \texttt{grind};
\srcloc{Lean4Lean/Verify/QSort.lean}{1} is \texttt{grind}-first throughout. A human reviewer
cannot check those arguments by reading, and they are brittle against changes in \texttt{grind}.
\item \textbf{Low. Readability of \texttt{baseCmp} and of \texttt{getUndefParam\_none}.}
\texttt{baseCmp} duplicates its \texttt{max} and \texttt{imax} arms verbatim
(\srcloc{Lean4Lean/Verify/NormLt.lean}{47}); the duplication is forced by matching on two
constructors, but it is a readability smell. \texttt{getUndefParam\_none}
(\srcloc{Lean4Lean/Verify/Level.lean}{101}) is written in a dense
\texttt{have ... := ?\_} style with several \texttt{simp}-then-\texttt{split} chains that are
hard to follow.
\item \textbf{Low. Layering oddity in the equivalence manager file.} The last two theorems,
\texttt{addEquiv.WF} (\srcloc{Lean4Lean/Verify/EquivManager.lean}{313}) and \texttt{isDefEq.WF}
(\srcloc{Lean4Lean/Verify/EquivManager.lean}{325}), live in the namespace
\texttt{Lean4Lean.TypeChecker.Inner} rather than \texttt{EquivManager}, and
\texttt{isDefEq.WF} would more naturally sit in
\srcloc{Lean4Lean/Verify/TypeChecker/IsDefEq.lean}{1}. The placement is defensible, since both
depend on the manager invariant, but it is surprising.
\end{itemize}
```

## experimental-logrel.tex

### Node review notes (29)
- `def:expa-shape`: \texttt{Shape} is an \texttt{@[implicit\_reducible] def} by recursion on \texttt{Nat} rather than an inductive family indexed by the level. That choice is the single largest source of the file's length: almost every lemma below is restated at level $0$, at level $n{+}1$, and then again for \texttt{WShape} and \texttt{TShape}.
- `def:expa-shape-ctors`: \texttt{Shape.trim} (\srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{820}) has no consumer anywhere in the group; it is dead code.
- `def:expa-shape-le`: The order is only a preorder: two tables can dominate each other without being equal. Consequently many later lemmas come in order-equivalence form, taking both $s \le t$ and $t \le s$ (see \ref{thm:expa-hastype-mono}), which doubles their statements.
- `def:expa-shape-plift`: Because those proofs \texttt{simp} through the elaborated \texttt{do} notation, the whole file pins \texttt{set\_option backward.do.legacy true} at \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{10}, referencing leanprover/lean4\#13305 and digama0/lean4lean\#31. That is a file-wide back-compatibility switch for a localised problem.
- `def:expa-shape-wf`: These \texttt{NonZero} side conditions are exactly what makes $\mathtt{lam}'$ and $\mathtt{ctor}'$ collapse to $\bot$, and they are what encodes proof irrelevance at the shape level. This is the key design idea of the whole development and it is documented nowhere in the file.
- `def:expa-wshape`: The two docstrings on these eliminators are among only 13 docstrings in 6100 lines. The \texttt{WShape} layer then duplicates essentially every \texttt{Shape} lemma (\srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{1055}--1400): pure boilerplate caused by defining \texttt{Shape} by \texttt{Nat}-recursion plus a separate \texttt{WF} predicate instead of one well-formed-by-construction inductive family.
- `def:expa-shape-app`: The definition is scattered: \texttt{ShapeFun.app} at line 721, the well-formedness lemma \texttt{ShapeFun.WF.app} at \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{2270}, \texttt{Shape.app} at 2292 and \texttt{WShape.app} at 2304.
- `def:expa-wshape-join`: Both the function \texttt{join} and the relation \texttt{Join} are carried everywhere with \texttt{Join.iff} to translate, doubling the API surface for little apparent benefit.
- `def:expa-tshape`: This is a third full copy of the order/join/compatibility API. \texttt{TShape.type} exists (\srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{1887}) but \texttt{TShape.prop} does not, an asymmetry with both \texttt{Shape} and \texttt{WShape}.
- `def:expa-shape-hastype`: The boolean definition exists only to obtain decidability; all reasoning goes through the inductive characterisation \ref{thm:expa-hastype-unfold}. The recursion is structural in the implicit level index (the \texttt{hasType} handed to \texttt{hasType.core} is the level-$n$ one), which nothing in the source says.
- `def:expa-valuation`: Two of the file's thirteen docstrings sit on \texttt{Valuation.Compat} and \texttt{Valuation.join}, the two most obvious definitions in the file, while \texttt{LE\_Interp} immediately below has none.
- `def:expa-le-interp`: The single most important definition of the file has no documentation whatsoever, and its \texttt{const} rule is unusually subtle: it quantifies over an abstract relation $R$ that is assumed closed under \texttt{LE\_Interp}, a parametricity trick used to handle recursive $\delta$ unfolding. Nothing in the source explains it.
- `def:expa-soundeq-strongsound`: \texttt{StrongSoundCore.const} takes a function producing a \texttt{CtorBundle} for \emph{every} classification of the constant, which looks over-general, since a constant has one classification. It is worth checking whether that hypothesis is ever instantiated non-trivially.
- `thm:expa-le-interp-strongsound`: The \texttt{replace H := H.strong} at line 5055 invokes \texttt{SExpr.IsDefEq.strong}, which is a \texttt{sorry} (\srcloc{Lean4Lean/Experimental/SExpr.lean}{679}); the \texttt{extra} case at line 5232 invokes the genuine \texttt{axiom Params.extra\_pat}. This theorem and everything below it are therefore conditional, and nothing in the file or in a comment says so.
- `structure:expa-logrel`: Bundling the obligations as a record is good design: it lets the successor step \ref{def:expa-lrs} be written once, generically in its predecessor. The two field docstrings (lines 5266 and 5268) are the only documentation here; the nineteen obligations carry none, and several are not obvious, in particular \texttt{trans'} (a heterogeneous transitivity at sort types) and \texttt{mono\_r\_1}, which needs an extra premise $\mathtt{TyDefEq}\ A\ A\ a'$.
- `def:expa-lr0`: Demanding the \emph{same} $u$ on both sides is exactly where sort injectivity enters the model, and the rest of the development exists to propagate this one clause upwards. Nothing in the source says so.
- `def:expa-lrs-components`: The docstrings that start appearing here are refactoring notes (``merged \texttt{PiEdgeDefEq} / \texttt{PiEdgeEq2}'', line 5373) rather than specifications. They are not the file's first: \texttt{WShape.casesOn'} (1001), \texttt{WShape.casesOn} (1020), \texttt{Valuation.Compat} (3297), \texttt{Valuation.join} (3301) and the two \texttt{LogRelBase} fields (5266, 5268) precede them, six of the file's thirteen.
- `def:expa-lrs-tydefeq`: The ``true at $\mathtt{lam}$/$\mathtt{ctor}$/$\mathtt{indTy}$'' clauses encode that a non-type shape carries no type information. That is correct but subtle, and the one-line docstring (``Non-trivial at \texttt{.forallE} (Pi injectivity) and \texttt{.sort} (sort injectivity)'') is all the explanation a reader gets.
- `def:expa-lrs-defeq`: The definition uses a dependent \texttt{match ha : a.1 with} and recovers well-formedness inside each branch by \texttt{have wfa1 := (ha $\triangleright$ a.2).1}. That is why the unfolding lemmas at lines 5629--5655 are needed at all, and why the one that has to expose the repackaged subtypes, \texttt{DefEq.lam\_forallE}, is proved by a \texttt{show} plus \texttt{Subtype.eta} dance (the other thirteen are \texttt{rfl}). A definition through \texttt{WShape.casesOn'} (\ref{def:expa-wshape}) would have avoided the whole block.
- `def:expa-lrs`: The construction is a single 238-line structure-instance term (lines 5657--5894). The nineteen field proofs are unnamed, cannot be stated or tested independently, and carry no comments; this is the least reviewable form the step could take.
- `def:expa-lr-substwf`: The file ends here, at line 6100, with \texttt{LR.SubstWF.symm} and without closing either of its two open namespaces. There is no \texttt{trans} for $\mathtt{SubstWF}$ and no fundamental theorem; the development continues in another module with no signpost saying so.
- `def:expa-lr-adequate`: The central definition of the file has no docstring. \texttt{Adequate.fits} (line 17), which lets a proof assume $\rho.\mathtt{Fits}$ for free because every $\mathtt{SubstWF}$ supplies it, is a useful idiom and is likewise unexplained.
- `thm:expa-lr-adequacy`: Neither the \texttt{sorry} nor the two further holes it rests on (\texttt{SExpr.IsDefEq.strong} and \texttt{axiom Params.extra\_pat}) is mentioned anywhere in the file. The hole predates commit \texttt{84f2b04}, titled ``Finished injectivity!'', which landed \ref{thm:expa-forallE-inv}, \ref{thm:expa-sort-inv} and \texttt{Lean4Lean/Experimental/UniqueTyping.lean} on top of it and left it in place.
- `structure:expa-logrel-classifier`: Dead code: the module is imported by nothing. \texttt{Lean4Lean.SExpr.Classifier'} is also declared, with a different signature, in \srcloc{Lean4Lean/Experimental/StepIndexed.lean}{8}. The two coexist only because no module imports both.
- `def:expa-logrel-classifier-forallE`: Dead code, and \texttt{Lean4Lean.SExpr.NormalType} clashes with the declaration of the same name at \srcloc{Lean4Lean/Experimental/StepIndexed.lean}{41}.
- `inductive:expa-logrel-ind`: Dead code, and \texttt{Lean4Lean.SExpr.LogRel} is declared three times in this directory with incompatible definitions: here as an \texttt{inductive}, at \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{5271} as the record of \ref{structure:expa-logrel}, and at \srcloc{Lean4Lean/Experimental/MoreStepIndexed.lean}{371} as a third structure. The \texttt{stuck} constructor is an interesting concession to Lean's non-normalising theory and is unexplained.
- `def:expa-lristype-weak`: Dead code. The four \texttt{cast} lemmas exist only to fight transport noise in the Kripke indices, which is a symptom of the indexing fighting Lean's definitional equality.
- `def:expa-logrelv`: Dead code, and incomplete internally: \texttt{LVIsType.sort} (line 287) is a bare \texttt{sorry}, \texttt{LVIsType.lift} (line 316) uses \texttt{stop}, which macro-expands to \texttt{repeat sorry}, and \texttt{LVEqSubst.lift}, \texttt{LVEqSubst.hasType} and \texttt{LVHasType.lift} survive only as commented-out stubs at lines 323--343.
- `structure:expa-coind-classifier`: The intended content, the definitions \texttt{IsTyNormal}/\texttt{IsTy}/\texttt{HasTy} and a \texttt{coinductive LogRel ... where} block, sits inside a block comment at lines 20--61 and uses a \texttt{coinductive} command (line 40) that does not exist in Lean 4, so it was never elaborated. The phantom-index alias is well typed but here carries no information at all: unlike the same idiom in \texttt{LogRel.lean}, where \texttt{Classifier.EqTy}/\texttt{HasTy}/\texttt{DefEq} read $\Gamma$, $A$ and $u$ back off the index, every projection that would consume the indices is inside the comment. The module costs a build dependency on \texttt{Lean4Lean.Theory.Typing.HeadReduction} and an olean for nothing.

### Section "Review notes"

```latex
\section{Review notes}

All four modules are master code; none of the issues below is attributable to the \texttt{iota} or
\texttt{trproj} branches.

\begin{itemize}
\item \textbf{High.} \srcloc{Lean4Lean/Experimental/ShapeLogRelAdequacy.lean}{154}: a live
\texttt{sorry} in the \texttt{const} case of \texttt{LR.adequacy}
(\ref{thm:expa-lr-adequacy}). Because that is the fundamental theorem, the three headline results
\ref{thm:expa-forallE-inv}, \ref{thm:expa-sort-forallE-inv} and \ref{thm:expa-sort-inv}, and
everything \texttt{Lean4Lean/Experimental/UniqueTyping.lean} derives from them, are unproved. Bare
constants are not a corner case of a real Lean term. The hole predates commit \texttt{84f2b04},
titled ``Finished injectivity!'', which landed the injectivity theorems and
\texttt{UniqueTyping.lean} on top of it without closing it; no comment in the source warns that a
case is missing.
\item \textbf{High.} \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{5055}:
\texttt{LE\_Interp.strongSound} (\ref{thm:expa-le-interp-strongsound}), and likewise
\texttt{LR.adequacy} at \srcloc{Lean4Lean/Experimental/ShapeLogRelAdequacy.lean}{109}, begin with
\texttt{replace H := H.strong}, where \texttt{SExpr.IsDefEq.strong} is a \texttt{sorry} at
\srcloc{Lean4Lean/Experimental/SExpr.lean}{679}. Everything from line 5054 of
\texttt{ShapeLogRel.lean} onwards is therefore conditional on an unproved strengthening of the
definitional-equality judgement, on top of twenty-nine further \texttt{sorry}-bearing lines in that
file (thirty in all: \texttt{IsDefEqStrong.defeq} 680, \texttt{Params.ctor\_ty} 688, inversion at
735--738, substitution lemmas at 761--798, 825 and 886, \texttt{extra} and reduction cases at
957--1008, and 1069--1324). No file-level comment records this. The boundary is worth stating
precisely because it is narrow: 23 of the 818 declarations of \texttt{ShapeLogRel.lean} are
tainted, all of them at line 5054 or later.
\item \textbf{High.} \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{5232}: the $\delta$ and
$\iota$ (\texttt{extra}) case of \texttt{LE\_Interp.strongSound}, and of \texttt{LR.adequacy}
(\srcloc{Lean4Lean/Experimental/ShapeLogRelAdequacy.lean}{431}), is
discharged with \texttt{axiom Params.extra\_pat}
(\srcloc{Lean4Lean/Experimental/SExpr.lean}{614}), a genuine axiom and not a class field: the
corresponding field is commented out of \texttt{class Params} at
\srcloc{Lean4Lean/Experimental/SExpr.lean}{42}. The axiom asserts that every environment defeq is
an instance of a registered pattern rule, which is the hard content of $\iota$-reduction. It is
invisible from these files.
\item \textbf{Medium.} \srcloc{Lean4Lean/Experimental/LogRel.lean}{353}: \texttt{fundamental}
(\ref{thm:expa-logrel-fundamental}) is unproved, and \texttt{LREqTy.defeq\_r} (243),
\texttt{LREqTy.symm} (246, all three branches), \texttt{LVIsType.sort} (287) and
\texttt{LVIsType.lift} (316) are \texttt{sorry} or \texttt{stop}. Since \texttt{stop tacticSeq}
macro-expands to \texttt{repeat sorry} in Lean core (\texttt{Init/Tactics.lean}), the five
\texttt{stop}s in this file (320, 361, 364, 369, 377) are silent sorries that a \texttt{grep} for
\texttt{sorry} does not find. The module is imported by nothing and is superseded
by \texttt{ShapeLogRel}; it should be deleted or explicitly marked abandoned.
\item \textbf{Medium.} \srcloc{Lean4Lean/Experimental/LogRel.lean}{70}: namespace collisions.
\texttt{Lean4Lean.SExpr.LogRel} is declared three times in this directory with incompatible
definitions (here as an inductive, \texttt{ShapeLogRel.lean}:5271 as a structure,
\texttt{MoreStepIndexed.lean}:371 as another structure); likewise
\texttt{Lean4Lean.SExpr.Classifier'} (\texttt{LogRel.lean}:8, \texttt{StepIndexed.lean}:8) and
\texttt{Lean4Lean.SExpr.NormalType} (\texttt{LogRel.lean}:58, \texttt{StepIndexed.lean}:41). These
compile only because no module imports two of them; combining the developments will break, and
cross-file search for these names is misleading.
\item \textbf{Medium.} \srcloc{Lean4Lean/Experimental/CoinductiveLogRel.lean}{1}: the file is
almost entirely a block comment sketching a \texttt{coinductive} command that does not exist in
Lean 4. Its only live content is \ref{structure:expa-coind-classifier}, which nothing uses and whose
alias discards all three indices. It still imports
\texttt{Lean4Lean.Theory.Typing.HeadReduction} and produces an olean in the
\texttt{Lean4Lean.Experimental} library. Dead weight.
\item \textbf{Medium.} \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{1665}: lines 1665--1732 are
a block comment holding an abandoned 58-line proof of \texttt{Shape.WF.plift}, a declaration that
does not exist in the compiled environment, containing seven \texttt{sorry} occurrences and one
\texttt{stop}, plus three further commented stubs at 1725--1731 carrying three more. This is why
counting \texttt{sorry} in the file reports eight lines for a file with no live \texttt{sorry}, an
easy way to misjudge it in either direction. Delete or convert to a tracked issue.
\item \textbf{Medium.} \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{10}:
\texttt{set\_option backward.do.legacy true} is applied at file scope to keep the
\texttt{Shape.plift} proofs (\ref{def:expa-shape-plift}) working after the \texttt{do} elaborator
change of Lean 4.32 (leanprover/lean4\#13305, tracked as digama0/lean4lean\#31). A file-wide
backward-compatibility option on a 6100-line file is a large blast radius for a localised problem,
and it will have to be removed eventually.
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{3333}: documentation is thin
and badly distributed. Thirteen docstrings in 6100 lines, none on the pivotal definitions
(\texttt{Shape.WF}, \texttt{Shape.hasType}, \texttt{LE\_Interp}, \texttt{InterpTyped},
\texttt{SoundEq}/\texttt{StrongSound}, \texttt{LR}; \texttt{LogRel} documents the two fields it
inherits from \texttt{LogRelBase} and none of its nineteen obligations), while two sit on the
self-evident \texttt{Valuation.Compat} and \texttt{Valuation.join}. Several of those that exist
(lines 5373, 5429) are refactoring notes rather than specifications. Nothing anywhere explains the
central intuition that a shape is a finite lower bound on the meaning of a term and that proofs get
shape $\bot$.
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{820}: \texttt{Shape.trim} is
defined and never used in this group or its dependents. Similarly \texttt{TShape.type} exists with
no \texttt{TShape.prop} counterpart (line 1887), and the \texttt{TShape} head-discrimination grid
(lines 1928--2030 plus a straggler at 2200, \ref{family:expa-tshape-discrimination}) is filled in
only where later proofs happened to need it: twelve of the pairs are proved,
\texttt{indTy\_not\_le\_ctor'} and \texttt{ctor\_not\_le\_sort} are not, so a reader cannot
distinguish deliberate omissions from gaps.
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{3936}: proof-size hygiene.
\texttt{LE\_Interp.Const.compat\_join} (3786--3934, 149 lines),
\texttt{LE\_Interp.compat\_join} (3936--4074, 139), \texttt{LE\_Interp.subst} (4087--4231, 145),
\texttt{LE\_Interp.Matches.of\_matchesS} (4870--4978, 109),
\texttt{LE\_Interp.sound\_lam} (4401--4504, 104),
\texttt{LE\_Interp.strongSound} (5054--5259, 206) and
\texttt{LR.adequacy} (\texttt{ShapeLogRelAdequacy.lean}:106--432, 327) are each a single
uncommented tactic block, and the \texttt{LRS} structure instance (5657--5894, 238) is a single
uncommented term. Combined with the \texttt{variable (ih : ...)} plus \texttt{include}
idiom used for induction hypotheses (lines 1392 and 2733), the development is essentially
unreviewable in detail by anyone but its author.
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{53}: structural design cost.
Because \texttt{Shape} is a \texttt{def} by recursion on \texttt{Nat} rather than an inductive
family indexed by the level, and well-formedness is a separate predicate, essentially every
order, lift, join and typing lemma is stated three times, for \texttt{Shape}, \texttt{WShape} and
\texttt{TShape}. Roughly the first 2500 lines are this boilerplate. A well-formed-by-construction
inductive family, or a single \texttt{TShape}-level API with one transfer principle, would
plausibly have halved the file.
\item \textbf{Medium.} \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{3430}: the pattern-matching
lemmas of \ref{thm:expa-le-interp-matches} rest on the \texttt{Params} field \texttt{pat\_wf},
and from line 3931 onwards the development also uses \texttt{pat\_uniq}. There is no
\texttt{Params} instance anywhere in the repository, so nothing exhibits an environment satisfying
either. Whether they hold for Lean's actual recursor rules is not addressed here, and the point is
nowhere flagged. (\texttt{Params.extra\_pat}, by contrast, was moved out of the class and declared
as a global \texttt{axiom}; see above.)
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{4623}:
\texttt{StrongSoundCore.const} (\ref{def:expa-soundeq-strongsound}) takes a function producing a
\texttt{CtorBundle} for \emph{every} classification of the constant, which looks over-general since
a constant has exactly one classification. It should be checked whether that hypothesis is ever
instantiated non-trivially.
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{6100}: the file stops after
\texttt{LR.SubstWF.symm} (\ref{def:expa-lr-substwf}) without closing either open namespace, with no
\texttt{trans} for \texttt{SubstWF} and no fundamental theorem, and with nothing telling the reader
that the development continues in \texttt{ShapeLogRelAdequacy.lean}.
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/LogRel.lean}{157}: \texttt{LRIsType.irrel'}
(\ref{thm:expa-lristype-irrel}) closes two \texttt{obtain rfl} steps with \texttt{grind}, which is
brittle across toolchain bumps. The lemma is in dead code, but the same reliance appears in live
modules.
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{2716}: \texttt{find\_cycle},
the pigeonhole lemma needed by \ref{thm:expa-hastype-mono}, is a genuinely reusable combinatorial
result declared \texttt{private} in the middle of a shape file; it belongs in
\texttt{Lean4Lean/Std} or upstream.
\end{itemize}
```

## experimental-reduction.tex

### Node review notes (18)
- `structure:expb-typing`: No term of type \texttt{Lean4Lean.Typing} exists anywhere in the repository, so the new obligation is never discharged here; its real counterpart is the class field \texttt{VEnv.Params.pat\_env} (\ref{axiom:cr-params-pat-env}), which is discharged with \texttt{pat\_env := id}. Unlike that one, this field has no docstring.
- `thm:expb-todyping`: This bridging step has no counterpart in \texttt{Theory/Typing/ChurchRosser.lean}: that file proves its results directly about \texttt{env.IsDefEq} under a \texttt{[Params]} instance and never needs to convert into a separate abstract record. The genuine duplicate of \texttt{iota}'s pattern-matching plumbing is the \texttt{pat} case of \texttt{VEnv.IsDefEqU.church\_rosser} below (\ref{thm:expb-isdefequ-church-rosser}), which mirrors \texttt{IsDefEq.church\_rosser} in \texttt{ChurchRosser.lean} (lines 1390--1394) line for line.
- `inductive:expb-isdefeq1`: The stratification choices are the delicate part and they are right: the typing premise is an alternation point and goes to \texttt{HasType1}, as in \texttt{beta}/\texttt{eta}/ \texttt{proofIrrel}, while the side conditions are not and stay recursive, as in \texttt{appDF}/\texttt{trans}. The \texttt{Realizes}-plus-list encoding rather than \texttt{Check.OK} is forced by strict positivity. Neither point is commented, and the core rule this mirrors (\ref{rule:isdefeq-pat}) does carry a docstring.
- `thm:expb-induction1`: Line 79 silently strengthens the exported hypothesis from \texttt{Ordered env} to \texttt{OrderedStrong env}. The change is forced, because on this branch \texttt{IsDefEq.strong} needs subject reduction for the registered $\iota$ rules (\ref{def:patsstrongon}), and \ref{thm:wf-orderedstrong} shows no realistic instance is lost; but no comment says so, and a reader diffing against master sees a weaker theorem with no rationale.
- `inductive:expb-isdefequ1`: In the erased setting \texttt{Realizes} constrains only $t.1$ and $t.2.1$, so the third component of every triple is unconstrained and the rule is a roundabout way of asserting \texttt{r.2.OK}. Uniformity with the typed version is a defensible reason to keep the shape, but no comment says so. Nothing in the file consumes the constructor: the would-be consumer \texttt{IsDefEqU1.induction} is inside the commented-out block at lines 121--142.
- `def:expb-venvprime-out`: Sound but narrowing: every theorem in this file about \texttt{env.out} now speaks only about $\iota$-free environments, so the experiment can never be reconnected to the $\iota$ development without giving \texttt{VEnv'} a real \texttt{pats} field. Given that the file dead-ends in four \texttt{sorry}s the shortcut is pragmatic, but it changes the scope of the file's theorems without a word of comment.
- `class:expb-sexpr-params`: \texttt{Params.extra\_pat} is declared as a global \texttt{axiom} at line 614 rather than as a class field, although the commented-out block at lines 36--44 shows it was meant to be one, along with five further intended fields. Every result in this cluster is therefore conditional on a global axiom that no instance is ever required to justify.
- `inductive:expb-sexpr-isdefeq`: This judgment has \emph{no} $\iota$ or \texttt{pat} rule: the pattern-based rule is commented out at lines 609--610, and reduction rules enter only through the \texttt{extra} rule over \texttt{env.defeqs} plus the global \texttt{Params.extra\_pat} axiom. The \texttt{iota} branch extended \texttt{VEnv.IsDefEq} and \texttt{VEnv.Params} but left this parallel judgment untouched, so the two halves of the project now model $\iota$ differently.
- `family:expb-sexpr-operational`: The soundness bridges \texttt{WHRedS.defeq} (line 1008), \texttt{InferType.hasType} (1091), \texttt{InferTypeS.hasType} (1167), \texttt{WHRedS.parRedS} (1182) and \texttt{Ctx.Subst.id} (770) are all \texttt{sorry}, as is \texttt{CRDefEq.trans} (1295), so the whole operational layer is stated but not connected to the declarative one. Note that the pattern rule that \texttt{SExpr.IsDefEq} lacks \emph{is} present here, in \texttt{WHRed} and \texttt{ParRed}: the two layers disagree about how reduction rules enter.
- `thm:expb-uniq-sort`: \texttt{UniqueTyping.lean} contains no textual \texttt{sorry}, yet \texttt{IsDefEq.strong} is \texttt{:= sorry} at \srcloc{Lean4Lean/Experimental/SExpr.lean}{679}, so this theorem and everything after it in the file are conditional on an admitted statement. The docstring on \texttt{toHasTypeS} is candid about this, but any status derived from grepping for \texttt{sorry} would mislabel the file as complete.
- `thm:expb-isdefeq-prime`: Neither \texttt{IsDefEq} nor \texttt{IsDefEq'} has an $\iota$ rule, so this equivalence has not been checked against the system the \texttt{iota} branch actually extended.
- `family:expb-thierry-domain`: Line 9 declares \texttt{axiom mySorry : $\alpha$} with an auto-bound implicit, that is, an inhabitant of every type and in particular a proof of \texttt{False}. It is used in \texttt{DF.comp}, \texttt{DF.bot} and elsewhere, so this file is deliberately inconsistent. Nothing imports it, but nothing else may ever be allowed to.
- `family:expb-thierry2-shape`: The order-theoretic core is assumed, not proved: \texttt{Shape.Compat.def}, \texttt{Shape.Join.mk}, \texttt{ShapeFun.Join.mk}, \texttt{Shape.HasType.mono}, \texttt{ShapeFun.LE.bot}, \texttt{ShapeFun.bot\_app} and \texttt{Shape.app\_mono\_r} are all \texttt{sorry}. The same construction reappears in \texttt{MoreStepIndexed.lean} and in \texttt{ShapeLogRel.lean}: three near-copies with three independently admitted sets of lattice laws.
- `family:expb-thierry2-model`: \texttt{DF.mk'} (line 421) and \texttt{D.pi} (line 472) are \texttt{sorry}, so the model is incomplete at exactly the connective the adequacy theorem is about; the judgment being interpreted, \texttt{DefEq}, is itself an \texttt{axiom} (lines 607--609) rather than a definition; and this file too opens with \texttt{axiom mySorry}.
- `family:expb-stepindexed`: \texttt{IsTy}, \texttt{IsTyN} and the unfolding equation \texttt{IsTy.def} are \texttt{axiom}s: the fixpoint the file sets out to construct is posited rather than built, which begs the file's own question. \texttt{IsTyN} is declared and never used, and roughly 40\% of the 88-line file is commented out. This is scratch, not a result.
- `family:expb-morestepindexed`: The four bounded judgments and their four monotonicity lemmas are \texttt{axiom}s (lines 38--45): the entire operational layer this file is about is assumed. The step-index bookkeeping is the only content that is actually proved.
- `family:expb-morestepindexed-logrel`: The file contains \texttt{\#exit} at line 420, so the two declarations that would assemble one level from the previous and iterate it, \texttt{TypeEqS} (421) and \texttt{TypeEq} (443), are never elaborated and do not exist in the compiled environment; neither does \texttt{TypeEq.mono}, which is commented out at line 489. Of the five textual \texttt{sorry}s in the file only one, \texttt{ShapeFun.app\_mono\_l} at line 310, is live; the rest are inside comments. Lines 63--336 duplicate the \texttt{Shape} lattice of \texttt{Thierry2.lean} wholesale, admitted order laws included.
- `family:expb-domaintheory`: \texttt{Dom.out} (line 211), which should unfold it again, contains the \texttt{stop} tactic at line 223, and \texttt{stop} is shorthand for \texttt{repeat sorry}: the definition is \texttt{sorryAx}-backed even though a text search for \texttt{sorry} finds nothing in this file. The file then ends at \texttt{Dom.fin} (line 240), a stub mapping every finite element to bottom.

### Section "Contribution summary"

```latex
\section{Contribution summary}

The \texttt{iota} branch changed 28 lines in this group and \texttt{trproj} changed none. In
dependency order the contributions are: the interface field \texttt{Typing.pat\_env}
(\ref{structure:expb-typing}, one line plus a supporting import), which is what lets the two new
cases of
\ref{thm:expb-todyping} and \ref{thm:expb-isdefequ-church-rosser} (eight lines together) promote an
environment-registered rule to an abstract \texttt{Pat} rule; the layer constructor
\texttt{IsDefEq1.pat} with the two cases that produce and consume it
(\ref{inductive:expb-isdefeq1}, \ref{thm:expb-induction1}, \ref{thm:expb-isdefeq1-induction}, nine
lines) and its type-erased twin (\ref{inductive:expb-isdefequ1}, \ref{thm:expb-inductionu1}, eight
lines); and the stub \texttt{pats \_ \_ := False} in \ref{def:expb-venvprime-out} (one line). Two of
those eight-line groups also carry a silent strengthening of an exported hypothesis from
\texttt{Ordered} to \texttt{OrderedStrong}.

Why they exist: \texttt{VEnv} grew a \texttt{pats} field and \texttt{VEnv.IsDefEq} grew a
\texttt{pat} constructor, so every inductive over \texttt{IsDefEq} in the tree acquired a new case
and every construction of a \texttt{VEnv} acquired a new field. CI builds
\texttt{Lean4Lean.Experimental} even though \texttt{lake} does not, so the experiments had to be
repaired rather than left broken.

How much of it is verification work and how much is compile-keeping: only the nine lines in
\texttt{Stratified.lean} do something that nothing else in the repository does, namely decide how
the $\iota$ rule stratifies and check that the decision round-trips. The eight lines in
\texttt{NormalEq.lean} and \texttt{ParallelReduction.lean} are the same argument the branch already
wrote in \texttt{Theory/Typing/ChurchRosser.lean} (\ref{class:cr-params},
\ref{axiom:cr-params-pat-env}, \ref{thm:isdefeq-church-rosser}), in files whose headers ask for their
own deletion. The eight in \texttt{StratifiedUntyped.lean} are dead, since the only consumer is
commented out. The one in \texttt{Stronger.lean} narrows the file to $\iota$-free environments.

What remains open. In this group, all of it: the two theorems the branch extended,
\ref{thm:expb-isdefequ-church-rosser} and \ref{thm:expb-induction1}, are conditional on pre-existing
master \texttt{sorry}s, so nothing here is a proved result. The one substantive gap the branch left
is the \texttt{SExpr} side: \ref{inductive:expb-sexpr-isdefeq} still has no $\iota$ rule, so
\ref{thm:expb-hastypes-uniq}, \ref{thm:expb-uniq-sort} and \ref{thm:expb-isdefeq-prime} are results
about a system that does not model the reduction rules the rest of the project now has.
```

### Section "Review notes"

```latex
\section{Review notes}

\begin{itemize}
\item \textbf{Medium.} \srcloc{Lean4Lean/Experimental/ParallelReduction.lean}{909}: the $\iota$
case added here, together with the \texttt{Typing.pat\_env} field at
\srcloc{Lean4Lean/Experimental/NormalEq.lean}{97}, duplicates exactly what the branch added to
\texttt{Theory/Typing/ChurchRosser.lean} (the \texttt{pat} case of \texttt{IsDefEq.church\_rosser},
lines 1390--1394, and the \texttt{Params.pat\_env} field). Both files carry an upstream
\texttt{TODO: remove, this is now part of ChurchRosser.lean}. The duplication is forced by CI, but
the $\iota$ rule is now maintained in two places with no cross-reference comment in either. The
other $\iota$ case in this file, \texttt{VEnv.IsDefEq.toTyping} at
\srcloc{Lean4Lean/Experimental/ParallelReduction.lean}{857} (\ref{thm:expb-todyping}), is not a
duplicate of anything: it bridges a concrete derivation into the abstract \texttt{Typing} record
that \texttt{ChurchRosser.lean}, working directly over a \texttt{[Params]} instance, has no need for.
\item \textbf{Medium.} \srcloc{Lean4Lean/Experimental/SExpr.lean}{981}: the chapter text describes
\texttt{WHRed} as deterministic (\texttt{WHRed.determ}), but that theorem's proof is \texttt{sorry}
in all five case splits where an \texttt{extra} (pattern-rule) step meets anything, including another
\texttt{extra} step (lines 987, 992, 995--997); only the $\beta$/application fragment is actually
proved deterministic.
\item \textbf{Medium.} \srcloc{Lean4Lean/Experimental/Stratified.lean}{79} and
\srcloc{Lean4Lean/Experimental/StratifiedUntyped.lean}{59}: the hypothesis of an exported theorem
was silently strengthened from \texttt{Ordered env} to \texttt{OrderedStrong env}. The change is
forced and loses no realistic instance, but neither site explains it.
\item \textbf{Medium.} \srcloc{Lean4Lean/Experimental/SExpr.lean}{609}: the whole \texttt{SExpr}
line of work still has no $\iota$ rule in its declarative equality. The pattern-based rule is
commented out and reduction rules enter only through \texttt{env.defeqs} plus the global
\texttt{axiom Params.extra\_pat} at line 614, while \texttt{WHRed} and \texttt{ParRed} on the same
file \emph{do} carry a \texttt{Pat}-based rule. The branch extended \texttt{VEnv.IsDefEq} and
\texttt{VEnv.Params} and left this parallel development untouched.
\item \textbf{Medium.} \srcloc{Lean4Lean/Experimental/UniqueTyping.lean}{138}: the file contains no
textual \texttt{sorry} but \texttt{IsDefEq.toHasTypeS} opens with \texttt{h.strong}, and
\texttt{SExpr.IsDefEq.strong} is \texttt{:= sorry}. \texttt{uniq\_sort} (172),
\texttt{toIsDefEq'} (240) and \texttt{iff\_isDefEq'} (260) are all conditional; a status derived
from grepping would mislabel the file as complete.
\item \textbf{Medium.} \srcloc{Lean4Lean/Experimental/DomainTheory.lean}{223}: \texttt{Dom.out} is
\texttt{sorryAx}-backed through the \texttt{stop} tactic, which is \texttt{repeat sorry}, again
despite no literal \texttt{sorry} in the file. The same pitfall occurs at
\srcloc{Lean4Lean/Experimental/LogRel.lean}{320} and
\srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{1703}.
\item \textbf{Medium.} \srcloc{Lean4Lean/Experimental/MoreStepIndexed.lean}{420}: a
\texttt{\#exit} truncates elaboration, so \texttt{TypeEqS} (421) and \texttt{TypeEq} (443), the two
declarations the file exists to build, are never compiled and do not appear in the environment. A
reader of the source cannot tell this from the text, and the file still builds green.
\item \textbf{High.} \srcloc{Lean4Lean/Experimental/Thierry.lean}{9} and
\srcloc{Lean4Lean/Experimental/Thierry2.lean}{9}: \texttt{axiom mySorry : $\alpha$} is an inhabitant
of every type and therefore a proof of \texttt{False}. It is used in \texttt{DF.comp},
\texttt{DF.bot} and elsewhere. These files are scratch formalizations of an external paper and are
imported by nothing, but the axiom must be recorded so that nothing else is ever allowed to
depend on them. \texttt{Thierry2.lean} additionally axiomatizes the judgment it interprets
(\texttt{DefEq}, \texttt{DefEq.U}, \texttt{DefEq.left}, lines 607--609).
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/NormalEq.lean}{97}: \texttt{Typing.pat\_env} has
no docstring, unlike the field it mirrors in \texttt{ChurchRosser.lean}, which documents it. The
\texttt{Typing} structure is never instantiated anywhere in the repository, so the added obligation
is never discharged and gives no evidence that the $\iota$ rule is realisable in this interface.
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/StratifiedUntyped.lean}{51}: the added
\texttt{IsDefEqU1.pat} constructor is never eliminated, since the only consumer is inside the
commented-out block at lines 121--142, and its \texttt{chk} list has an entirely unconstrained third
component in the erased setting where \texttt{Check.OK} would say the same thing directly.
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/Stronger.lean}{28}: \texttt{pats \_ \_ := False}
silently restricts every theorem about erased environments in the file to $\iota$-free ones. Adding
a real \texttt{pats} field to \texttt{VEnv'} was the general fix; the file dead-ends in four
\texttt{sorry}s anyway, so the shortcut is pragmatic rather than wrong.
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/ParallelReduction.lean}{699}: the two
pre-existing master \texttt{sorry}s in \texttt{NormalEq.parRed} (699, 718), precisely the cases where
a pattern reduction meets a proof-irrelevance step, make \ref{thm:expb-parred-church-rosser},
\ref{family:expb-crdefeq} and \ref{thm:expb-isdefequ-church-rosser} conditional in this file. The
$\iota$ case the branch added therefore extends an unproved theorem; the corresponding case in
\texttt{ChurchRosser.lean} is the one that matters.
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/MoreStepIndexed.lean}{63}: the
\texttt{Shape}/\texttt{ShapeFun} approximation lattice exists in three near-identical copies, here,
at \srcloc{Lean4Lean/Experimental/Thierry2.lean}{21} and in \texttt{ShapeLogRel.lean}, each with its
own partly admitted order laws and nothing keeping them in sync.
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/StepIndexed.lean}{59}: \texttt{IsTy},
\texttt{IsTyN} and \texttt{IsTy.def} are \texttt{axiom}s positing the existence and the unfolding
equation of the very fixpoint the file sets out to construct; \texttt{IsTyN} is declared and never
used, and about 40\% of the file is commented out.
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/NormalEq.lean}{145}: several declarations here
carry fully qualified names that already exist in \texttt{Theory/Typing/ChurchRosser.lean}, for
instance \texttt{Lean4Lean.Pattern.Matches.hasType} and \texttt{Lean4Lean.Pattern.Check.OK.weakN}.
The two modules are never imported together so Lean accepts it, but any name-indexed tooling (an
axiom census, a blueprint cross-reference, a documentation generator) will conflate the sorry-free
copy here with the \texttt{sorryAx}-tainted one there.
\item \textbf{Low.} \srcloc{Lean4Lean/Experimental/Stratified.lean}{160} and
\srcloc{Lean4Lean/Experimental/StratifiedUntyped.lean}{121}: two thirds of each file is a
commented-out block of abandoned unique-typing and weakening-inversion attempts, containing further
\texttt{sorry}s. Besides being dead weight, it makes the last live declaration of each file look
admitted to any line-range-based analysis.
\end{itemize}
```

## contrib-iota.tex

### Section "History and churn"

```latex
\section{History and churn}

28 commits, 2026-07-21 to 2026-09-09, all authored by Alessandro Sosso except one committer
identity (\texttt{3bbdb22}, author still \texttt{sosso@cs.au.dk}), linear with two upstream
merges (\texttt{contrib-iota.md} \S(b), \texttt{claims-iota.md} claim 50). Milestones:

\begin{description}
\item[M1 --- first cut (2026-07-21, 8 commits).] \texttt{cb920e1} relocates
\texttt{Pattern.lean} into \texttt{Theory/} (and incidentally commits agent-tooling files);
\texttt{5a4bdda} adds the \texttt{pats} field; \texttt{a3d6076} the \texttt{IsDefEq.pat} rule;
\texttt{41f3fb6} a real \texttt{addInduct}; \texttt{e92f762} the first \texttt{Params}
instance; \texttt{d0a1ae7}/\texttt{9e186e6} the \texttt{Verify} bridge. At this point
\ref{structure:ind-wf} was deliberately underspecified (positivity, universes and large
elimination ``not yet enforced''), \texttt{AddInduct} hard-coded \texttt{.safe}, and there
were 12 sorries tagged \texttt{IOTA-TODO(soundness)}.
\item[M2 --- toolchain port and first revert (2026-08-06).] Merges upstream master
(v4.33.0-rc2); \texttt{3bbdb22} reverts \texttt{cb920e1}'s file move and removes the committed
agent-tooling files, minimising the diff against upstream.
\item[M3 --- consumer-driven strengthening (2026-08-08 to 2026-08-18).]
\texttt{349da4b} trims comments to house style ($-279/+123$ lines, verified in
\texttt{claims-iota.md} claim 49). \texttt{1a1ebe8} is the pivotal fix: after wiring the
interface to a client of the theory end to end, the opaque $\exists r$ in
\texttt{pats\_iota} could not be instantiated at the trivial check, so the full telescope
split and a \texttt{TrExprS} link are pinned into \texttt{AddInduct.rec\_find} and the witness
is exposed as \texttt{pats\_iota'}.
\item[M4 --- first ``principled rework'' (2026-09-04, +3715/-682).] \texttt{d69ac5d}: derive
\texttt{AddInduct}'s bookkeeping instead of assuming it, drop the \texttt{.safe} gate,
flesh out \ref{structure:ind-wf}, and add the 615-line
\srcloc{Lean4Lean/Verify/Environment/Quot.lean}{1}.
\item[M5 --- second, deeper rework after an adversarial review (2026-09-08, 10 commits).]
\texttt{REVIEW\_2026-09-07.md} mechanised two blockers: \textbf{B1}, a
\texttt{Prop} with two nullary constructors and a \texttt{Sort u} recursor satisfying every
field of the then-current \ref{structure:ind-wf}, from which
$(\forall p{:}\mathtt{Prop},\, p\to p) \equiv (\forall p{:}\mathtt{Prop},\, p)$ followed in a
\texttt{VEnv.WF} environment; \textbf{B2}, \ref{thm:wf-patsstrong} was plausibly false against
an older type former whose rule fired on an axiom. \texttt{4016efa} responds by adding
\texttt{ctors\_positive}, \texttt{universes}/the \texttt{imax} bound, \texttt{LargeElim} and
the block-membership fields \texttt{recs\_over\_block}/\texttt{rec\_counts}/\texttt{rules\_ctor};
\texttt{f53b727} restates \ref{thm:wf-patsstrong} over well-formed prefixes
(\ref{def:wfprefix}). Hygiene commits follow: \texttt{18805a4} deletes a decoder section,
\texttt{30897c0} adds the unsafe-\texttt{Eq} rejection and records it in \texttt{divergences.md},
\texttt{be30d35} closes the four \texttt{Experimental} \texttt{pat} cases.
\end{description}

A sidecar branch, \texttt{iota-consume} (not an ancestor of \texttt{iota} or
\texttt{trproj}), is a client's own proposal for the same three
strengthenings, written independently and handed back for review
(\texttt{iota-consume-review-brief.md}); its first two edits were re-implemented as
\texttt{1a1ebe8}, its third dropped. Churn is visible but concentrated: two
reverts/relocations, two upstream merges, two full reworks of \ref{structure:ind-wf}
(\texttt{d69ac5d}, \texttt{4016efa}), one restatement of \ref{thm:wf-patsstrong}
(\texttt{f53b727}), and two commit pairs duplicated with \texttt{trproj}
(\texttt{7a68882}$\equiv$\texttt{6fd8a1d}, \texttt{3de1dcb}$\equiv$\texttt{b4aba6d}) that will
confuse anyone reading the merged history (\texttt{contrib-iota.md} \S(b)). Two of the
branch's own files were rewritten more than they were extended:
\srcloc{Lean4Lean/Theory/Typing/InductiveParams.lean}{1} took 14 commits, +1039/-576, over
half rewritten, and \srcloc{Lean4Lean/Theory/Typing/InductiveLemmas.lean}{1} took 11
(\texttt{hygiene-review.md} \S(e); by declaration count per \texttt{unused-contrib.md} \S4,
\texttt{InductiveLemmas.lean} is 96\% iota (70/73) and \texttt{InductiveParams.lean} is 88\%
iota (22/25), the rest trproj).
```

### Section "Claims audit"

```latex
\section{Claims audit}
\label{sec:contrib-iota-claims}

Every claim checked in \texttt{claims-iota.md} against the compiled \texttt{trproj} tree,
condensed to one line each. Verdicts are the file's own, upgraded where noted.

\begin{description}
\item[1 (PR\_iota.md, \textbf{TRUE}).] Master's \texttt{VInductDecl.WF}/\texttt{addInduct}
sorries are closed --- \srcloc{Lean4Lean/Theory/Inductive.lean}{316}, \texttt{:335}, no
\texttt{sorry} in the 444-line file.
\item[2 (PR\_iota.md, \textbf{TRUE}).] \texttt{addInduct\_WF} is proved ---
\srcloc{Lean4Lean/Theory/Typing/InductiveLemmas.lean}{229}, axiom-clean.
\item[3 (PR\_iota.md, \textbf{TRUE}).] Exactly one new sorry, \texttt{patsStrong} ---
grep of \texttt{sorry} on \texttt{iota} minus \texttt{master} outside \texttt{Experimental}
yields only \srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{334}.
\item[4 (PR\_iota.md, \textbf{TRUE}).] Non-\texttt{Experimental} sorry count: master 23,
branch 21 --- recounted by hand excluding prose/comment hits.
\item[5 (PR\_iota.md, \textbf{TRUE, recipe wrong}).] No new axioms --- the one apparent diff
line is a docstring continuation, not a declaration; master already carries 12
non-\texttt{Experimental} axioms the claim's own recipe misses.
\item[6 (REVIEW, \textbf{TRUE}).] No \texttt{native\_decide} anywhere in the branch.
\item[7 (PR\_iota.md, \textbf{PARTIAL}).] \texttt{lake build} green on all targets ---
all 117 modules have oleans (120 total, under \texttt{.lake/build/lib/lean/}) and three
re-elaborate from source with zero errors, but
\texttt{Lean4Lean.Tests} is not in \texttt{defaultTargets} and a full rebuild is out of scope
for this review.
\item[8 (REVIEW F15, \textbf{TRUE}).] \texttt{Experimental} sorry counts equal master's
(103$=$103); the four \texttt{pat} cases are closed with real proofs.
\item[9 (PR\_DESCRIPTION.md, \textbf{TRUE, upgraded}).] \texttt{TrEnv.iota\_defeq} is
\texttt{[propext]}-only --- measured directly with \texttt{lake env lean}.
\item[10 (PR\_DESCRIPTION.md, \textbf{PARTIAL}).] \texttt{pats\_iota'}/\texttt{iota\_rec}
inherit \texttt{sorryAx} only via \texttt{TrProj} --- true and measured on \texttt{trproj}
(where \texttt{TrProj} is real, both are clean modulo master's own hash-map axioms);
not directly measured on \texttt{iota} itself, where \texttt{TrProj} is still \texttt{sorry}.
\item[11 (PR\_iota.md, \textbf{TRUE}).] \texttt{TrEnv'.induct} applies at every safety level,
no \texttt{.safe} guard --- \srcloc{Lean4Lean/Verify/Environment/Basic.lean}{582}.
\item[12 (IOTA\_CONTRIBUTION.md, \textbf{FALSE, stale}).] Contradicted by 11; true only at an
earlier commit (\texttt{dc01931}).
\item[13 (IOTA\_CONTRIBUTION.md, \textbf{FALSE now}).] ``12 \texttt{IOTA-TODO} sorries'' ---
zero hits today; accurate only at \texttt{eddf009}.
\item[14 (PR\_DESCRIPTION\_formal.md, \textbf{FALSE, stale}).] \texttt{VInductDecl.WF}
``records only checkable conditions'' --- \texttt{ctors\_positive}, \texttt{universes},
\texttt{recs\_elim} are fields today.
\item[15 (IOTA\_CONTRIBUTION.md, \textbf{FALSE for two, true in spirit for one}).]
\texttt{pat\_uniq}/\texttt{pat\_app\_uniq} are proved; \texttt{extra\_pat} is not proved but
assumed as \texttt{DefEqsAsPats}.
\item[16 (IOTA\_CONTRIBUTION.md, \textbf{FALSE, stale}).] \texttt{Aligned.addInduct} is proved
at \srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{102}.
\item[17 (IOTA\_CONTRIBUTION.md, \textbf{FALSE/misleading}).] ``No new soundness gap for the
consumer'' --- true of the four handback lemmas in isolation; every strong-system consumer
today routes through the sorried \ref{thm:wf-patsstrong} via the \texttt{CoeOut} instance.
\item[18 (PR\_DESCRIPTION.md, \textbf{TRUE}).] \texttt{iotaCheck = .true}: no kernel parameter
check at $\iota$-reduction time.
\item[19 (PR\_iota.md, \textbf{TRUE, upgraded: run}).] \texttt{iotaRHS} matches
\texttt{inductiveReduceRec}'s slicing exactly --- \texttt{lake env lean} on
\texttt{Tests/IotaShape.lean} exits 0 with a failing control confirming the assertions fire.
\item[20 (PR\_iota.md, \textbf{TRUE}).] \texttt{VInductDecl.WF} specifies a direct block;
nested inductives are outside it; \texttt{Tree} is the documented negative control, run at
\srcloc{Lean4Lean/Tests/IotaShape.lean}{605}.
\item[21 (PR\_iota.md, \textbf{TRUE}).] \texttt{AddInduct}'s seven bookkeeping theorems are
derived, not assumed.
\item[22 (PR\_iota.md/REVIEW F06, \textbf{TRUE}).] \texttt{checkEqType} rejects an unsafe
\texttt{Eq}; \texttt{EqSafe} is gone; recorded in \texttt{divergences.md}.
\item[23 (PR\_iota.md, \textbf{TRUE}).] \texttt{Verify/Environment/Quot.lean} replaces a
proof that was vacuous through \texttt{no\_inductInfo} with a real, sorry-free one.
\item[24 (REVIEW F09, \textbf{TRUE, hollow}).] The first internal consumer,
\texttt{inductiveReduceRecCore.WF}, landed, but \texttt{reduceRecursor.WF} is still
\texttt{sorry} and nothing consumes \texttt{inductiveReduceRecCore} itself.
\item[25 (REVIEW F23, \textbf{TRUE, unconsumed}).] \texttt{toParams} is exercised by
\texttt{inductParams}/\texttt{crDefEq\_of\_induct}, but all 13 occurrences of these names are
inside one file with no library consumer.
\item[26 (PR\_iota.md/REVIEW, \textbf{TRUE}).] \ref{def:patsstrong} is restated over
well-formed prefixes (F05 fixed), though it still also quantifies over constant-only
extensions.
\item[27 (PR\_iota.md, \textbf{TRUE}).] 67 \texttt{OrderedStrong} occurrences, 64 declaration
heads retyped from \texttt{Ordered}, all previously at a \texttt{VEnv.WF} call site.
\item[28 (PR\_iota.md, \textbf{FALSE}).] ``Nothing previously sorry-free at a bare
\texttt{Ordered} hypothesis loses that'' --- master's \texttt{Ordered.strong} was exactly such
a theorem and no longer exists.
\item[29 (REVIEW, \textbf{TRUE, upgraded: mechanised here}).] The review's two counterexamples
are refuted sorry-free against the reworked \ref{structure:ind-wf}; the in-repo test suite
stops one step short of this.
\item[30 (REVIEW, \textbf{TRUE}).] No mention of any client project anywhere in code or
docstrings.
\item[31 (REVIEW, \textbf{PARTIAL}).] Style conformance: 2 lines over 100 columns on
\texttt{trproj}, 7 on \texttt{iota} itself, against master's 49; substantively compliant
either way.
\item[32 (iota-consume-review-brief.md, \textbf{TRUE}).] The \texttt{rec\_find} strengthening
creates no proof obligation today: nothing constructs an \texttt{AddInduct}.
\item[33 (the round-4 commission brief, \textbf{TRUE, upgraded}).] A client's
repository pins \texttt{20ec229} and consumes
\texttt{iotaRHS}/\texttt{PatTyped} directly, verified in that checkout.
\item[34 (contrib-iota.md header, \textbf{FALSE}).] ``Byte-identical between \texttt{iota} and
\texttt{trproj} except one file'' --- 17 files differ, +2273/-170;
\srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{1} alone differs by 659 lines.
\item[35 (contrib-iota.md, \textbf{TRUE}).] 45 files, +5628/-331, 28 commits, verbatim.
\item[36 (contrib-iota.md, \textbf{FALSE, both numbers}).] Master's file is 7 lines, not 8;
the current file is 444 (\texttt{trproj})/443 (\texttt{iota}) lines, not 455.
\item[37 (contrib-iota.md, \textbf{TRUE}).] \texttt{Pattern.lean}: 232 master lines, 725 now.
\item[38 (contrib-iota.md, \textbf{PARTIAL}).] \texttt{InductiveParams.lean} is 433 lines on
\texttt{trproj}, 423 on \texttt{iota}.
\item[39 (PR\_iota.md, \textbf{TRUE}).] \texttt{VInductDecl.WF} has exactly 20 fields, counted.
\item[40 (PR\_iota.md, \textbf{TRUE}).] \texttt{SimplePattern.iota} and the \texttt{Params}
class predate the branch; only \texttt{pat\_env} is new.
\item[41 (PR\_iota.md, \textbf{TRUE}).] \texttt{Aligned} gains \texttt{pat} and \texttt{block}
clauses.
\item[42 (PR\_iota.md, \textbf{PARTIAL, stale numbers}).] ``16 adversarial declarations, 49
library inductives'' --- accurate for an earlier commit; the shipped driver runs 48/9/10/10.
\item[43 (PR\_DESCRIPTION.md, \textbf{TRUE}).] \texttt{insertDefs\_wf} was purely relocated,
not rewritten.
\item[44 (PR\_DESCRIPTION.md, \textbf{TRUE}).] \texttt{pats\_iota'} needs an \texttt{hsafe}
hypothesis because master's \texttt{ignore} case can skip an unsafe recursor.
\item[45 (7a68882, \textbf{TRUE}).] The \texttt{Inductive/Reduce.lean} split is
token-identical to the original body apart from variable renaming.
\item[46 (d69ac5d, \textbf{PARTIAL}).] ``Seven previously-assumed fields become theorems'' ---
only four of the seven named were actually fields before.
\item[47 (d69ac5d, \textbf{PARTIAL}).] ``33 to 24'' sorries --- the earlier count was 35, not
33.
\item[48 (dc01931, \textbf{TRUE}).] Handback axiom lists (\texttt{iota\_defeq}
\texttt{[propext]}, \texttt{addInduct\_pat} \texttt{[propext, Quot.sound]}) match today.
\item[49 (349da4b, \textbf{TRUE}).] Comment-only commit, $-279/+123$, verbatim.
\item[50 (contrib-iota.md, \textbf{TRUE}).] \texttt{3bbdb22} is the only commit under a second
committer identity.
\item[51 (PR\_iota.md, \textbf{TRUE, two documented divergences}).] \texttt{VInductDecl.WF}
follows \S2.6.1--2.6.4 line by line, with the recursor-data-as-carried and
$v$-not-pinned divergences named in the docstrings.
\item[52 (docstrings, \textbf{TRUE}).] \ref{rule:isdefeq-pat} states the thesis's regularity
of $\iota$ as a rule, citing \texttt{typesys.tex} and \texttt{unique.tex} verbatim.
\item[53 (docstring, \textbf{TRUE, more permissive than the kernel, stricter than the thesis}).]
\ref{def:ind-large-elim} mirrors \texttt{isLargeEliminator} but tests propositionality by
typing rather than the kernel's syntactic \texttt{isAlwaysZero} --- accepting strictly more
than the kernel, and, against the thesis's \texttt{LEctor} rule, strictly less on recursive
fields.
\item[54 (contrib-iota.md, \textbf{TRUE}).] \texttt{divergences.md} is the only tracked file
touched outside \texttt{Lean4Lean/}.
\item[55 (found in this pass, \textbf{TRUE}).] Master's \texttt{checkEqType.WF} was itself a
false statement once inductives are enterable, not merely a vacuous proof; its deletion was
forced.
\item[56 (contrib-iota.md, \textbf{TRUE}).] Nothing constructs an \texttt{AddInduct} or
establishes \ref{structure:ind-wf} for a real declaration.
\item[57 (PR\_iota.md, \textbf{TRUE}).] \ref{thm:wf-patsstrong} needs type-former
injectivity, itself \texttt{sorry} on master and untouched
(\srcloc{Lean4Lean/Theory/Typing/Injectivity.lean}{12}).
\item[58 (contrib-iota.md, \textbf{TRUE on iota; false on trproj}).] The exported interface
has exactly one in-repo consumer, \texttt{iota\_rec}; on \texttt{trproj},
\texttt{pats\_iota\_inv\_shape} gained a second (projection work, not $\iota$).
\item[59 (d69ac5d, \textbf{UNVERIFIABLE as stated}).] ``65 inductives'' --- the shipped
driver's largest sweep is 48; the figure is a stale snapshot.
\item[60 (PR\_iota.md, \textbf{TRUE}).] \texttt{toParams} is \texttt{@[reducible]};
\texttt{pat\_wf} routes through the \texttt{Realizes}/\texttt{OK} bridge; \texttt{pat\_env}
is the identity.
\end{description}

\textbf{What the notes overclaim.} The PR text's summary sentence for claim 28
(``nothing previously sorry-free loses that'') is contradicted by the deletion of master's
\texttt{Ordered.strong}, even though the paragraph immediately before it discloses the
consequence honestly. \texttt{IOTA\_CONTRIBUTION.md}'s claim that the consumer inherits
``no new soundness gap'' (17) is true only of four lemmas measured in isolation; the model
they describe now routes every strong-system result through \ref{thm:wf-patsstrong}. Three
whole status notes (\texttt{IOTA\_CONTRIBUTION.md}, \texttt{PR\_DESCRIPTION\_formal.md}) are
two reworks out of date on claims 12--16 and would mislead if pasted into a pull request
today. Validation numbers in \texttt{PR\_iota.md} (claim 42) and a commit message (claims
46--47) are stale or slightly wrong. The reader's own \texttt{contrib-iota.md} overstates
byte-identity between \texttt{iota} and \texttt{trproj} (claim 34) and one file's line count
(claim 36); its axiom-recipe for claim 5 is also wrong on both branches.

\textbf{What the notes underclaim.} The two adversarial-review counterexamples are dead only
because this pass mechanised the missing step (claim 29); the shipped tests stop short.
\texttt{PR\_iota.md} asserts the kernel-agreement suite passes without anyone having re-run it
(claim 19); it does, in 1.7s, with a failing control proving the assertions are live.
\texttt{TrEnv.pats\_iota'}/\texttt{iota\_rec} are stronger than claimed: fully
\texttt{sorryAx}-free once \texttt{TrProj} is real (claim 10), not merely tainted-but-isolated.
\texttt{addQuot.WF} is not just ``real'', it replaces a statement of master's that becomes
\emph{false}, not merely vacuous, once inductives enter \texttt{TrEnv} (claim 55). The thesis
alignment (claim 51) is more exact than the PR text states, down to the precise universe
bound, and its two honest divergences live only in docstrings a reviewer would have to go
looking for.
```

### Section "Proof and code hygiene"

```latex
\section{Proof and code hygiene}
\label{sec:contrib-iota-hygiene}

\textbf{Statement quality.} \ref{def:pattyped}'s existential form and \texttt{addPat}'s
totality (above) are the two design choices reviewers flag as needing to be read carefully
before use (\texttt{hygiene-review.md} \S(a), MEDIUM); \ref{def:patsstrong} takes explicit
environment arguments plus six positional hypotheses, an interface the typing chapter's
review calls unlike anything else in the file (\texttt{reviews/typing.md}). Three leaf lemmas
have no consumer anywhere: \texttt{RecShape.one\_le\_numMotives} and
\texttt{RecShape.majorFormer?\_eq} (\srcloc{Lean4Lean/Theory/Inductive.lean}{196}, \texttt{:202}),
and \texttt{LargeElim.shape} (\srcloc{Lean4Lean/Theory/Inductive.lean}{242}), the only bridge
from the typing-level \texttt{LargeElim} to the decidable \texttt{LargeElimShape} that the
test suite bypasses by calling \texttt{LargeElimShape} directly.

\textbf{Proof quality.} The headline item is \ref{thm:wf-patsstrong} itself
(\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{334}, rated HIGH in
\texttt{hygiene-review.md}, \texttt{reviews/typing.md} and \texttt{reviews/metatheory.md}
independently): via \ref{instance:coeout-orderedstrong} and roughly 158 mechanically-rewritten
master call sites, the strong system, the typing inversions, \texttt{Verify/Primitive*} and
the type-checker layer all become conditional where master had them proved. Elsewhere,
\texttt{addQuot\_strong} (\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{188}) hand-unrolls
five \texttt{addQuot} steps into parallel \texttt{l1...l5}/\texttt{d1...d4} chains that a
generic \texttt{foldlM\_addConst\_strong} would cover if \texttt{addQuot} were a fold; the
same repetition pattern recurs at \srcloc{Lean4Lean/Verify/Environment/Quot.lean}{521} (the
same five-line block repeated four times) and \texttt{:584} (four-deep nested lookup chains
written out twice). By contrast, contributed proofs are shorter on average than master's in
the same directories (7.5 code lines per declaration in \texttt{Theory/} against master's 8.5;
\texttt{hygiene-review.md} \S(d)), and \texttt{inductiveReduceRecCore.WF}
(\srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{17}, correctly ι-attributed despite a blame
tag of \texttt{P} --- \texttt{contrib-iota.md}'s attribution caveat, and independently the
duplicated-commit note in \texttt{claims-iota.md}) is the branch's second-longest proof at 124
lines but has no consumer, since \texttt{reduceRecursor.WF} two lines below it is still
\texttt{sorry}.

\textbf{Documentation.} Verified against their statements in a spot check of about 60
declarations, six mismatches were found across the whole \texttt{trproj} diff, none in files
this chapter is responsible for except a stale claim that \texttt{addRecRule}'s redex is
``at \texttt{getMajorIdx}'' where the definition inlines the four summands
(\srcloc{Lean4Lean/Theory/Inductive.lean}{257}, LOW; every consumer restates it with
\texttt{getMajorIdx} regardless, so the two are equal by unfolding but the docstring is
imprecise). The loudest volume signal in the whole diff is here: contributed \texttt{Theory/}
code is 25.3\% comment lines against master's 1.7\% in the same directory, and the single
largest docstring in \texttt{Theory/} is 27 lines on the 5-line \texttt{DefEqsAsPats}
(\srcloc{Lean4Lean/Theory/Typing/InductiveParams.lean}{351}). The content is substantive ---
derivations, thesis section numbers, explicit ``not modelled'' statements --- not filler
restating the code, and master's own maxima elsewhere (105-line blocks in
\texttt{Experimental/}) are comparable, but the ratio would not survive an upstream review
unchanged (\texttt{hygiene-review.md} \S(c)).

\textbf{Dead code.} \texttt{unused-contrib.md} counts 565 author-written iota declarations
across the current run, of which 58 have zero resolved in-repo reference (10.3\%); its own
recovery note, however, attributes 28 of the pass's 78 total zero-reference findings across
both branches to a tooling regression that mis-tags \texttt{Decidable} instances (nearly all
of them in \srcloc{Lean4Lean/Tests/ShapeDecide.lean}{1}, iota's file) as \texttt{def}, and
flags 19 more as provisional; the original, manually-verified run's 31 zero-reference
findings (19 of them iota's, 12 trproj's, out of 875 contributed declarations, 553 iota /
322 trproj) reproduce unchanged and are the trustworthy figure, against which the
regenerated 58/565 above is the uncorrected count. The clearest genuine surplus is the
\texttt{RHS.spine}/\texttt{iotaCounts} cluster (\ref{family:pattern-iota-counts}, eight
declarations, roughly 50 lines, \srcloc{Lean4Lean/Theory/Typing/Pattern.lean}{499}--\texttt{:680}),
proved only to substantiate a docstring's claim that a reduct ``retains ... nothing else of
the telescope split'' and consumed by nothing else (\texttt{hygiene-review.md} \S(g),
MEDIUM); \texttt{WF'.pats\_origin} (\srcloc{Lean4Lean/Theory/Typing/InductiveParams.lean}{93},
32 lines, ``first step of the deferred $\iota$ subject-reduction proof'') is the same pattern
on a smaller scale, and \texttt{Verify/LocalContext.lean:183}'s
\texttt{DecidableEq FVarId} instance sits in the wrong namespace for a core type genuinely
missing it. Against this, the strongest counterweight in the whole review is
\srcloc{Lean4Lean/Tests/IotaShape.lean}{454}: it decides every syntactic
\ref{structure:ind-wf} clause on some 45 real kernel inductives, runs roughly 20 hand-built
negative controls, and checks \texttt{iotaRHS} against the executable
\texttt{inductiveReduceRec} on real recursor/constructor pairs --- genuine validation that
the specification is neither vacuous nor wrong, and the strongest evidence against a
``slop'' reading of the branch (\texttt{hygiene-review.md} \S(g)).

\textbf{Style fit.} Naming, granularity and formatting follow upstream convention
throughout: no line over 100 columns beyond the two noted in claim 31, no trailing whitespace,
naming such as \texttt{addRecRule\_le}/\texttt{PatsIota.induct}/\texttt{WF.pat\_uniq} matches
master's own \texttt{.mono}/\texttt{.le}/\texttt{\_iff} conventions. The one stylistic break
is a preference for named-field \texttt{structure ... : Prop} (\ref{struct:add-induct},
\ref{struct:tr-ind-type}, \ref{struct:tr-recursor}, \ref{structure:indparams-patsiota}) where
master models the analogous \texttt{AddQuot} as a nested existential chain --- better
engineering, but visibly not Mario Carneiro's own idiom
(\texttt{hygiene-review.md} \S(d), LOW).
```

### Section "Upstream situation"

```latex
\section{Upstream situation}

The user's contribution is an open pull request, \texttt{digama0/lean4lean\#43, ``Iota
Reduction''} (\texttt{barabbs:iota} at \texttt{38ea0de} against \texttt{digama0:master} at
\texttt{8223d22}), opened 2026-08-08, +5628/-331 over 45 files, 28 commits, \texttt{mergeable:
true}, zero human review comments (\texttt{upstream-comparison.md} \S3, fetched live
2026-09-14). Upstream has not moved since \texttt{8223d22} (16 days of silence at fetch time,
byte-compared file by file), so the branch is neither superseded nor duplicated, and it
targets exactly the holes upstream's own comments name as open: the constructor-less
\texttt{AddInduct}, the \texttt{sorry} \ref{structure:ind-wf}/\ref{def:ind-add-induct}, and
the vacuous \texttt{addQuot.WF}. No other upstream branch or open pull request touches any of
this. All seven inline review comments on the PR are from a bot, posted five minutes after
opening, reviewing the \emph{first} push; the two human comments on the thread are the
author's own; and every CI run since \texttt{eddf009} is stuck at GitHub's first-time-contributor
\texttt{action\_required} gate, so the last CI verdict the maintainer ever saw is a red run
from 2026-08-11 that the author has since fixed. Three weeks after the PR opened, the
maintainer wrote, on an unrelated thread, that \texttt{addDecl.WF}'s \texttt{inductDecl} case
is ``still open, and unchanged'' because \texttt{VInductDecl.WF} and \texttt{addInduct} are
``still \texttt{sorry}'' --- describing exactly the deliverable of this branch, which was
already sitting in his queue, and naming a handshake (\texttt{checkInductive.WF}'s
\texttt{AddsConsts}) that a repo-wide grep shows the fork does not make
(\texttt{upstream-comparison.md} \S3). The direct precedent is pull request \#32
(kim-em, +24247/-1264, an adjacent verification contribution), closed unmerged after four
weeks when the maintainer judged his own smaller, checker-light version better; by the metric
he used there, this branch's diff (+5628/-331 over 45 files, changing three existing
interfaces: \texttt{VEnv}'s arity, \texttt{AddInduct}'s arity, and the import order between
\texttt{VEnv} and \texttt{Pattern}) sits in the size band he has already criticised once
(\texttt{upstream-comparison.md} \S5).
```

### Section "Assessment"

```latex
\section{Assessment}

\textbf{Solid.} The specification layer --- \ref{structure:ind-wf} and its shape predicates,
\ref{def:indparams-toparams}'s \texttt{PatsIota} invariant, the four-stage
\ref{def:ind-add-induct} --- is carefully designed, honestly scoped in its own docstrings, and
validated against the real kernel by \srcloc{Lean4Lean/Tests/IotaShape.lean}{454}, a test
harness that is itself high quality. Two master \texttt{sorry} definitions, one master
\texttt{sorry} proof, and the vacuous quotient proof are genuinely closed, with axiom-clean
witnesses where claimed
(\S\ref{sec:contrib-iota-sorry}). The one kernel edit that changes behaviour
(\srcloc{Lean4Lean/Quot.lean}{24}) is deliberate and recorded in \texttt{divergences.md}; the
other (\srcloc{Lean4Lean/Inductive/Reduce.lean}{75}) is a provably behaviour-preserving
refactor. Formatting, naming and proof length are within upstream norms, and contributed
proofs are shorter on average than master's own.

\textbf{Questionable.} \ref{def:indparams-toparams} and its specialisation are exercised by
nothing outside their own file (claim 25); a roughly 50-line cluster
(\ref{family:pattern-iota-counts}) and several smaller lemmas are proved to make a docstring's
point and consumed by nothing else; comment density in contributed \texttt{Theory/} code is an
order of magnitude above master's in the same directory; and the branch's own history contains
a created-then-reverted file move, one wholly rewritten file
(\texttt{InductiveParams.lean}), and two commits duplicated with \texttt{trproj} that an
upstream maintainer would ask to be rebased away before review.

\textbf{What a maintainer would push back on, in descending order.} (1) \ref{thm:wf-patsstrong}
is \texttt{sorry} and reached through a \texttt{CoeOut} coercion, so roughly 158 previously
unconditional master call sites became conditional on an admitted lemma without that trade
being stated up front in any single place a reviewer would read first. (2) \ref{structure:ind-wf}
is a 20-field checklist where the thesis, and the kernel's own \texttt{Inductive/Add.lean},
generate the analogous data; its adequacy --- that the checklist implies the thesis's
admissibility --- is exactly what \ref{thm:wf-patsstrong} would need and is nowhere argued,
and the 2026-09-07 review's own recommendation to compute rather than check was not taken.
(3) \texttt{addDecl.WF}'s \texttt{inductDecl} case is still \texttt{sorry}
(\texttt{Verify/Environment.lean:208}), so nothing in the repository ever constructs an
\ref{struct:add-induct} witness or establishes \ref{structure:ind-wf} for a real declaration;
the entire \texttt{Verify}-side interface is usable only by a caller that assumes
\texttt{TrEnv}. (4) The diff changes three existing upstream interfaces
(\texttt{VEnv}'s field arity, the \texttt{Pattern}/\texttt{VEnv} import order, and, via the
\texttt{Ordered}$\to$\texttt{OrderedStrong} retyping, roughly 64 existing signatures) rather
than sitting purely alongside master's code, in a size band the same maintainer has already
declined once on an adjacent contribution.

\textbf{Prioritised open ends} (naming the gap only, no fixes): \ref{thm:wf-patsstrong} itself,
which needs type-former injectivity (\texttt{Injectivity.lean}, untouched, three sorries) to
even be attempted; the missing \texttt{addDecl.WF} $\to$ \ref{struct:add-induct} producer;
the adequacy argument for \ref{structure:ind-wf} against the thesis's generated recursor data;
the \texttt{DefEqsAsPats} hypothesis that confines \ref{def:indparams-toparams} to
environments with no \texttt{def} and no quotient; the orphaned
\texttt{inductiveReduceRecCore.WF} whose consumer, \texttt{reduceRecursor.WF}, is itself
\texttt{sorry}; K-like reduction, recorded but never registered; and, on the process side, the
duplicated-commit history and the still-pending upstream \texttt{action\_required} CI gate
that has kept a maintainer from ever seeing a green run of this work.
```

## contrib-trproj.tex

### Section "History and churn"

```latex
\section{History and churn}

The branch reworked its central design decision twice, each time because the previous version was
diagnosed as wrong before it caused a false theorem, not after. \textbf{M1} (\texttt{f252c3c}
through \texttt{b6a5a38}, 2026-08-26 to 08-28) shipped \texttt{TrProj} with a \emph{free}
existential motive; commit \texttt{7a5e96d} then pinned it to a \emph{constant} motive
$\lambda\_.\,\mathit{fieldTy}$, because on a neutral major premise well-typedness constrains the
motive only on constructor-shaped inputs, so two witnesses with motives agreeing on constructors
but differing on a variable would both satisfy \texttt{TrProj} while not being defeq — making
\texttt{TrProj.uniq} false. Commit \texttt{b6a5a38} then introduced \texttt{TrProjCtor} because the
\emph{previous} statement of \texttt{TrEnv.proj\_defeq} was unprovable: the $\iota$ rule's
constructor name and the spine's constructor name were unrelated. \textbf{M2}
(\texttt{7f62db2}, 2026-09-03) is a documentation-only commit recording a dead end: the
\texttt{rec\_reg} route could not establish that a recursor is a \emph{structure} recursor, because
the $\iota$ key records only the \emph{sum} $\mathit{numMotives}+\mathit{numMinors}+\mathit{numIndices}$.
\textbf{M3} (\texttt{fc9fbfc} through \texttt{f7dabf1}, 2026-09-04) is the decisive rework: commit
\texttt{811a52a} replaced the constant motive with the current chained \emph{dependent} one,
because the constant motive cannot type a dependent field such as \texttt{Sigma.snd}; commit
\texttt{83860e9} turned \texttt{proj\_defeq} into a real theorem, still over the raw telescope
split as a hypothesis. \texttt{f7dabf1} is the commit the project's own 2026-09-07 review was run
against.

\textbf{M4} (\texttt{2a901f4} through \texttt{6fd8a1d}, 2026-09-08) is the review response: eleven
commits, eight of them answering named findings, six of which are worth naming individually:
\texttt{e9fefbe} turns \texttt{TrProjCtor} from a positionally
destructured existential into the current named-field structure (F13) and deletes two zero-use
wrappers (F29); \texttt{e202975} restates \texttt{proj\_defeq} on the kernel's structure facts
instead of the telescope-split hypothesis (F07); \texttt{273cd2c} splits \texttt{inferProj.WF} into
the scoped and general lemmas and documents the general one as not provable as stated (B3/F03);
\texttt{acd6b46} adds the sorry-free inhabitation tests (F19); \texttt{d7ec0fa} re-derives every
builder from \texttt{subst} (F12); \texttt{6fd8a1d} splits \texttt{inductiveReduceRecCore} and
proves \texttt{inductiveReduceRecCore.WF}, the first real consumer of the $\iota$ interface
(answering the $\iota$ half of F09; the \emph{projection} half is still unanswered, \S\ref{sec:contrib-trproj-consumers}).
\textbf{M5} (\texttt{20ec229}, 2026-09-10) is the final merge with \texttt{iota}: trivial, one line
changed, since \texttt{iota} had independently re-landed the M4 kernel-refactor content.

No commit in \texttt{iota..trproj} is a literal \texttt{git revert}; the rework is by replacement.
\texttt{hygiene-review.md} quantifies the cost: non-merge commits on the branch total
$+11439/-3399$ against a net $+7762/-363$ over the whole \texttt{master..trproj} range, so roughly
3000 lines the branch itself wrote were later removed inside the branch — about 27\% of what was
written. The worst offenders by commit count are \texttt{Verify/Environment/Lemmas.lean} (22
commits, $+1734/-678$) and \texttt{Theory/Typing/InductiveParams.lean} (14 commits, over half
rewritten); a whole file, \texttt{Theory/Pattern.lean}, was created over four commits and then
deleted (\texttt{cb920e1}/\texttt{3bbdb22}) and does not exist at the tip. Two pairs of commits
share a patch-id or subject line (\texttt{655dd3f}/\texttt{75ffde9}, \texttt{7a68882}/\texttt{6fd8a1d}),
evidence of re-merging a rebased \texttt{iota} without squashing — the kind of thing an upstream
maintainer would ask to be cleaned up before review. Since the repository's own workflow
squash-merges branches, none of this history reaches upstream if the branch is ever proposed; the
cost is review time inside this project, not permanent record.
```

### Section "Claims audit"

```latex
\section{Claims audit}

\texttt{understand/claims-trproj.md} independently re-checked every claim
\texttt{contrib-trproj.md} attributes to the branch's own documentation
(\texttt{PR\_trproj.md}, \texttt{TRPROJ\_CONTRIBUTION.md}, \texttt{trproj-commission.md},
the round-3 commission brief) against the \texttt{20ec229} checkout, using
\texttt{git grep/diff/show/log/blame} and \texttt{lake env lean} re-elaboration; of 50 claims, 28
came back \textbf{TRUE}, 12 \textbf{PARTIAL}, 8 \textbf{FALSE} and 2 \textbf{UNVERIFIABLE} without
a client's own repo. The headline technical claims all check out exactly as stated: \texttt{TrProj} is
a real definition, \ref{thm:tr-env-proj-defeq} is proved, the sorry census, the axiom cone and the
two test files are as described. What follows is the audit of what does \emph{not} check out
cleanly, restated as a description list; verdicts are the claims file's own.

\begin{description}
\item[\textbf{TRPROJ\_CONTRIBUTION.md — FALSE where cited.}]
It is not a description of this branch: the file is dated 2026-08-28 and documents the
\emph{abandoned} constant-motive design from M1. It quotes a \texttt{TrProj} definition that no
longer exists, advertises \texttt{TrEnv.pats\_iota\_inv} and two \texttt{TrProjCtor} wrappers
deleted in M4, counts 15 \texttt{IOTA-TODO} and 3 \texttt{PROJ-TODO} markers where
\texttt{git grep} at \texttt{20ec229} finds zero, and cites three \texttt{PROJ-TODO} line numbers
one of which now names a \emph{proved} theorem (\ref{thm:tr-env-proj-defeq}). It should not be
handed to a reviewer as a current description.
\item[\textbf{``every lemma about it was sorry on master'' — PARTIAL.}]
\texttt{TrProj.weakN} was already proved on master (a one-line \texttt{simpa} off the sorried
\texttt{weak'}), and \texttt{TrProj.mono} did not exist on master at all. Seven of \texttt{TrProj}'s
eight master-era lemmas were \texttt{sorry}, not eight, and \ref{thm:trproj-mono} is a genuinely new
obligation the branch introduced for itself (required by \texttt{TrExprS.mono}).
\item[\textbf{the constant-motive scope note — FALSE, stale.}]
``The constant motive is correct for non-dependent fields; dependent fields are out of scope'' is
\texttt{TRPROJ\_CONTRIBUTION.md} \S A1 describing the design \texttt{811a52a} replaced eight days
later. The current motive is the chained dependent one, and
\texttt{Tests/ProjShape.lean:120-145} exercises \texttt{Sigma.snd}, \texttt{PSigma} and
\texttt{Subtype}.
\item[\textbf{``the general inferProj.WF keeps its statement'' — FALSE.}]
It does not. Master's version asserted, via an auto-bound implicit, that the translation of the
\emph{struct} is the translation of the \emph{projection}; \texttt{trproj} corrected this to an
existential over the projection's own translation (\S\ref{sec:contrib-trproj-design} above). The
branch fixed a latent statement bug in a master theorem, and \texttt{PR\_trproj.md} itself denies
having touched it.
\item[\textbf{``no new trust'' for TrProj.defeqDFC — PARTIAL.}]
\ref{thm:trproj-defeqdfc}'s computed \texttt{sorryAx} cone includes \texttt{VEnv.WF.patsStrong}
(\ref{thm:wf-patsstrong}), a gap the \emph{same author's} \texttt{iota} branch introduces, not only
master's pre-existing $\Pi$/sort-injectivity gaps (\ref{thm:injectivity-open}). ``No new trust
beyond master'' is the wrong claim; the accurate one is ``no trust beyond what \texttt{iota}
already added.''
\item[\textbf{``DELIVERED, do not re-open'' — PARTIAL, misleading as to reach.}]
The round-3 commission brief's verdict on \texttt{TrEnv.proj\_defeq} is true as to proof
status: the theorem is sorry-free in its own body. It is misleading as to reach: the theorem has
zero consumers inside lean4lean (\S\ref{sec:contrib-trproj-consumers}), and the same document's
further claim that it is ``in active use today'' by a client of the theory could not be
confirmed — that client pins \texttt{lean4lean} at exactly \texttt{20ec229} but its current branch
mentions neither \texttt{proj\_defeq} nor an \texttt{of\_trEnv} lemma outside a scratch file.
\item[\textbf{the four upstreaming blockers B1--B4 — FALSE as stated, superseded in substance.}]
\texttt{contrib-trproj.json}'s ``not upstreamable as it stands'' verdict names B4 (does not build
against current master) as unresolved; it is not: \texttt{git merge-base --is-ancestor master
trproj} succeeds. B1/B2's mechanized counterexamples
(\texttt{review-artifacts/counterexamples/cexA.lean}, \texttt{cexB.lean}) no longer elaborate
against the redesigned \texttt{VInductDecl.WF} — the spec changed under them. What genuinely
remains is the residual obligation, not the counterexample: \ref{thm:wf-patsstrong} is still
\texttt{sorry} and gates every strong-system consumer, including this branch's own
\ref{thm:trproj-defeqdfc} and \ref{thm:tr-env-proj-defeq}.
\end{description}

Two findings the claims audit flags as \textbf{underclaimed} are worth carrying into the
assessment. First, because master's \texttt{TrProj} was a \texttt{sorry} \emph{definition}, every
master declaration whose type merely mentioned \texttt{TrExprS}/\texttt{TrExpr} carried
\texttt{sorryAx} by construction; \texttt{claims-trproj.md} \#45 reports 663
\texttt{Lean4Lean.*} declarations whose type mentions these relations, of which 614 are now
\texttt{sorryAx}-free — a change in the trust status of most of \texttt{Verify}, undersold by the
branch's own ``five sorries closed'' framing. Second, the kernel-to-model bridge
(\ref{thm:tr-env-structure-rec}, \texttt{TrEnv.ctor\_arity}, \texttt{TrEnv.pats\_iota\_inv\_shape})
is itself \texttt{sorryAx}-free; all of \ref{thm:tr-env-proj-defeq}'s inherited taint enters through
\texttt{VEnv.IsDefEqU.betaN}, i.e.\ through master's unique-typing layer plus
\ref{thm:wf-patsstrong}, not through anything this branch built.
```

### Section "Proof and code hygiene"

```latex
\section{Proof and code hygiene}

\texttt{hygiene-review.md}'s whole-diff review (\texttt{master..trproj}, $+7762/-363$ over 49
files) and the per-chapter adversarial reviews of \texttt{proj}, \texttt{trexpr}, \texttt{trenv},
\texttt{typechecker}, \texttt{syntax} and \texttt{kernel} agree on the overall picture: this is
substantive, carefully engineered work with a specific, bounded set of defects, not the pattern
hygiene-review.md's own closing section calls ``slop'' (grandiose docstrings over trivial lemmas,
\texttt{simp}-spam, \texttt{decide}/\texttt{omega} papering over unchecked statements). Concretely:

\begin{itemize}
\item \textbf{Statement quality.} \ref{thm:vtc-inferproj}'s own docstring says it is not provable
as stated, yet \texttt{inferType'.WF} consumes it unconditionally
(\texttt{hygiene-review.md} (a), \textbf{HIGH}) — keeping a knowingly-false statement on the
soundness theorem's import path is worse than master's admittedly-also-wrong version, and the
\texttt{typechecker} chapter review independently confirms the same headline weakness. Lower down,
\texttt{VExpr.projTy} (\ref{def:proj-ty}) is documented as ``the kernel's \texttt{inferProj}
result'' but its docstring's own identity to \texttt{projMotiveBody} is never proved, and
\texttt{TrProjCtor} types the projection through \texttt{projMotiveBody} instead — the \texttt{proj}
chapter review confirms this identity has no proof anywhere in the repository.
\item \textbf{Proof brittleness.} \ref{thm:tr-env-proj-defeq}, at 131 lines the branch's longest
proof, and \texttt{inductiveReduceRecCore.WF} (\ref{thm:vtc-iota-reduce-core}), at 124, both lean
heavily on \texttt{omega}/\texttt{decide}: the branch's \texttt{omega} density is $2.0\%$ of code
lines against master's $0.4\%$, and \texttt{decide} $1.1\%$ against $0.2\%$
(\texttt{hygiene-review.md} baseline table), concentrated in exactly these two proofs. Three of
\ref{thm:trproj-weak}, \texttt{instN} and \texttt{instL} each rebuild the same eight-field
\texttt{TrProjCtor} record by hand rather than through a shared lemma — the ``prove once against
\texttt{subst}'' factoring stops at the \texttt{Theory/Proj.lean} builder level and is not carried
up into \texttt{Verify/Typing/Lemmas.lean} (\texttt{trexpr} chapter review, confirmed).
\item \textbf{Documentation volume.} Contributed \texttt{Theory/} code runs $25.3\%$ comment
lines against master's $1.7\%$ in the same directory, with a 56-line module header on the 449-line
\texttt{Proj.lean} and a 27-line docstring on a 5-line definition
(\texttt{Theory/Typing/InductiveParams.lean:351}, iota-side) — \texttt{hygiene-review.md} calls
this ``the single loudest AI-authored-looking signal in the diff,'' while noting the content itself
is substantive (derivations, thesis section numbers, explicit statements of what is not modelled)
rather than restatement.
\item \textbf{Unused declarations.} \texttt{unused-contrib.md}'s original, hand-verified count is
\textbf{31} zero-reference declarations out of 875 contributed (19 iota, 12 trproj), a $3.5\%$
rate, lower than the $11.2\%$ consumer-less rate the same resolver finds in upstream master's own
core. A later mechanical regeneration of the same script instead reports 78 out of 889 ($8.8\%$;
$10.3\%$ iota, $6.2\%$ trproj); the report flags this itself as an artefact, not a new finding —
the regenerated \texttt{decls.tsv} mislabels 28 user-written \texttt{instance}s as \texttt{def},
and the rerun adds 19 further entries never individually re-verified by hand — so 31 is the figure
this chapter relies on. On the trproj side specifically, the confirmed dead declarations are the
two witness theorems \texttt{trProj0}/\texttt{trProjDep1} in \texttt{Tests/ProjInhabit.lean} (built
and checked, but read by nothing), two never-projected test-fixture fields (\texttt{V3.h},
\texttt{Refl.next}), \texttt{projMotiveBody\_zero} and \texttt{instFields\_nil} (\texttt{@[simp]},
never invoked explicitly), and the two open, unreferenced \texttt{sorry}s
\texttt{VEnv.IsDefEq.crDefEq\_of\_induct} and \ref{thm:vtc-inferproj-struct}. (\texttt{VExpr.projTy}
is not on the dead list itself; it is reached only from two \texttt{example}s in
\texttt{Tests/ProjShape.lean}.) The resolver's headline finding is about wiring, not volume:
\ref{thm:tr-env-proj-defeq} itself, the branch's headline theorem, has no consumer beyond an
axiom-profile test (\S\ref{sec:contrib-trproj-consumers}).
\item \textbf{Orphaned master code.} \texttt{trproj}'s generalisation of \texttt{lift'\_inst\_hi}
into \texttt{lift'\_instN\_hi} (\ref{fam:proj-fn-subst} territory in Chapter~\ref{chap:proj}) left
a six-declaration master cluster in \texttt{Theory/VExpr.lean}
(\texttt{lift\_r\_one}, \texttt{Subst.lift\_r\_comm}, \texttt{Subst.trunc},
\texttt{Subst.Depth.\{one,id\}}, \texttt{Subst.Depth}) with no live consumer, without removing it
— \texttt{unused-contrib.md} \S5 calls this ``the one place where the branches made the host repo
measurably worse rather than merely not-better.'' The \texttt{syntax} chapter review independently
confirms only \texttt{consN\_cons} of the four-lemma block it moved is used.
\item \textbf{Test discipline (positive).} Both test modules re-elaborate clean and validate the
design on two independent axes — \texttt{ProjShape.lean} against the real kernel's own
\texttt{addDeclCore}/\texttt{whnf}/\texttt{isDefEq}, \texttt{ProjInhabit.lean} against the model's
\texttt{VEnv.addInduct} — which \texttt{hygiene-review.md} calls ``the strongest evidence against a
`slop' reading of the branch.'' The \texttt{proj} chapter review qualifies this: the two negative
controls are weaker than they look (a \texttt{try}/\texttt{catch} wrapper that passes vacuously on
any internal failure, and a ``some clause fails'' check that does not pin \emph{which} clause), and
neither hand-built environment in \texttt{ProjInhabit.lean} is ever shown well-formed, so the
witnesses show the premises of \ref{struct:trprojctor} are jointly satisfiable, not that they hold
in a well-formed environment.
\item \textbf{Formatting and naming.} Zero added lines exceed 100 columns, zero carry trailing
whitespace, and contributed declarations are \emph{shorter} on average than master's in the same
directories (5.6--7.5 code lines per declaration against master's 8.5--12.0). Naming follows
upstream convention throughout, and the branch's preference for named-field
\texttt{structure ... : Prop} (\texttt{TrProjCtor}, \texttt{AddInduct}, \texttt{TrIndType}) over
master's existential-chain style is a real, if stylistically visible, improvement.
\end{itemize}
```

### Section "Upstream situation"

```latex
\section{Upstream situation}

Nothing in this branch has ever been proposed upstream. \texttt{upstream-comparison.md} confirms
that no upstream commit, PR or issue in the relevant window touches inductives, $\iota$ or
projections beyond a documentation note (\texttt{3adf6da6}, ``docs: justify the projection
divergence by the generated recursor'') and an unrelated checker performance change
(\texttt{62441418}, \texttt{lazyDeltaProjReduction}); \texttt{git log} on upstream's default branch
in the same window shows no commit by the maintainer that touches
\texttt{Verify/Typing/Expr.lean} or \texttt{Verify/Typing/Lemmas.lean}'s \texttt{TrProj} lemmas.
The files this branch adds outright — \texttt{Theory/Proj.lean} (449 lines),
\texttt{Tests/ProjInhabit.lean} (597), \texttt{Tests/ProjShape.lean} (185), and the
\texttt{TrProj}/\texttt{TrProjCtor} rewrite in \texttt{Verify/Typing/Expr.lean} — exist in no
upstream pull request. \texttt{trproj} is 52 commits ahead of \texttt{master} and 24 ahead of
\texttt{iota}, and \texttt{git merge-base --is-ancestor master trproj} succeeds, so a textual merge
would go through; that is a low bar, since \texttt{master}'s own state at the relevant commit still
has \texttt{AddInduct} as a constructorless \texttt{inductive} and \texttt{TrProj := sorry}, so
almost anything merges cleanly against a placeholder.

\texttt{upstream-comparison.md}'s size argument applies here as much as to \texttt{iota}: at
$+7762/-363$ over 49 files, \texttt{trproj} (together with the \texttt{iota} it depends on, at
$+5628/-331$ over 45 files) sits in the size band the maintainer has previously pushed back on for
unrelated PRs, and it changes three existing interfaces at once
(\texttt{VEnv}'s arity, \texttt{TrProj}'s arity, \texttt{addDecl.WF}'s case split). Set against
that: this is, by the hole-closing count, the more valuable of the two branches per line changed —
it retires the \texttt{TrProj} \texttt{sorry} definition plus five of its seven lemma
\texttt{sorry}s — and its closing questions to a maintainer (quoted in
\texttt{understand/contrib-trproj.md} (e)) are specific and well posed: whether \texttt{TrProj}'s
typing side conditions are acceptable inside a translation relation, whether a real
\texttt{VExpr} projection node with its own $\iota$/$\eta$ rules would be preferred instead, and
whether \texttt{TrProjCtor}'s scope restriction (non-mutual, single-constructor, non-recursive,
non-indexed) is the right cut. \texttt{trproj} cannot be upstreamed before \texttt{iota} is, since
it depends on \texttt{iota}'s registered-$\iota$-rule interface throughout; and \texttt{iota}'s own
open blockers — \ref{thm:wf-patsstrong} chief among them — are therefore also blockers for this
branch, inherited rather than introduced.
```

### Section "Assessment"

```latex
\section{Assessment}

\textbf{What is solid.} The design decision is right for this model and cheap in the sense that
matters most: it adds no rule to \texttt{IsDefEq} (\ref{def:isdefeq}), so none of the model's
existing metatheory has to be redone, and a projection computes because the structure's own
$\iota$ rule computes. \ref{thm:tr-env-proj-defeq} is a genuine, complete, non-circular proof of
the thesis-adjacent computation rule, derived rather than postulated. The two design corrections
(free motive, then constant motive, then chained dependent motive) each closed a real defect
identified \emph{before} it produced a false theorem, which is the right way to make mistakes in a
verification project. The test discipline — real-kernel validation in
\texttt{Tests/ProjShape.lean}, sorry-free model-side inhabitation in \texttt{Tests/ProjInhabit.lean}
— is better than most of the surrounding repository, upstream included. No new axiom, no
\texttt{native\_decide}, no line over 100 columns, contributed proofs shorter on average than
master's.

\textbf{What is open.} \ref{thm:trproj-uniq} is the single highest-value remaining item: it is the
one \texttt{sorry} this branch owns that gates \texttt{TrExprS.uniq} and, through it, a large
fraction of \texttt{Verify}. \ref{thm:vtc-inferproj-struct} and \ref{thm:vtc-inferproj} are the
bridge from a real kernel projection to a \texttt{TrProjCtor} witness, and neither exists; until one
does, \ref{thm:tr-env-proj-defeq} is evidence about a satisfiable specification, not a theorem
about anything the checker does. And \ref{thm:add-decl-wf}'s \texttt{inductDecl} case being
\texttt{sorry} means every result in this chapter and in Chapter~\ref{chap:trenv} that mentions
\texttt{AddInduct} is conditional on a hypothesis nothing yet constructs — the branch, like
\texttt{iota} beneath it, has built the specification and its consequences without yet building the
thing that would make either fire on a real inductive declaration.

\textbf{What is weak.} \texttt{TRPROJ\_CONTRIBUTION.md} is stale to the point of being actively
misleading and should not circulate. The thesis attribution in the earliest commit titles overclaims
what \texttt{Theory/Proj.lean}'s current, more careful docstring already corrects. Documentation
volume in the contributed \texttt{Theory/} files is out of proportion with upstream's own norms,
though not with its substance. And \texttt{lift'\_inst\_hi}'s generalisation left a small cluster
of master code newly dead without removing it — a real, if minor, regression in tidiness that an
upstream reviewer would flag on sight.

\textbf{Priority order for closing the open ends.} (1) \ref{thm:trproj-uniq} — it is this branch's
own load-bearing gap, its residual (unique typing of the projection function, type-former
injectivity, functionality of the $\iota$ registry) is precisely named in the theorem's own
docstring, and closing it removes \texttt{sorryAx} from the uniqueness layer of the entire
translation. (2) \ref{thm:add-decl-wf}'s \texttt{inductDecl} case — without a producer for
\texttt{AddInduct}, neither this chapter's theorems nor Chapter~\ref{chap:trenv}'s apply to any
concrete environment, and this is shared, prerequisite work for \texttt{iota} as much as for
\texttt{trproj}. (3) \ref{thm:vtc-inferproj-struct} — inhabiting it in general, even under the
scope restriction \texttt{TrProjCtor} already imposes, is what would let a real kernel projection
ever reach \ref{thm:tr-env-proj-defeq}. (4) \ref{thm:wf-patsstrong} — not owned by this branch, but
the single admission that taints \ref{thm:trproj-defeqdfc} and \ref{thm:tr-env-proj-defeq} alike,
and closing it benefits every chapter in this development, not only this one. (5) Housekeeping:
retire \texttt{TRPROJ\_CONTRIBUTION.md} or mark it superseded, restore a consumer for the six
declarations \texttt{lift'\_inst\_hi}'s move orphaned, and rebase away the duplicated commits before
proposing anything upstream.
```

## status.tex

### Section "Issue registry"

```latex
\section{Issue registry}
\label{status:sec:issues}

Every issue below is sourced from at least one of: the \emph{Review notes} section of one of the
fourteen module chapters (Chapters \ref{chap:syntax}--\ref{chap:experimental-reduction}),
\texttt{reviews/*.md} (the adversarial per-chapter reviews), \texttt{hygiene-review.md},
\texttt{unused-contrib.md}, or a FALSE/PARTIAL verdict in \texttt{claims-iota.md}/
\texttt{claims-trproj.md}. Entries confirmed by more than one source are merged into one entry
citing the fullest description; the parenthetical after each entry names the chapter(s) and/or
report the entry is drawn from. No fixes are proposed. Severity and attribution follow the
source material's own judgement.

\subsection{High severity}

\subsubsection*{iota}

\begin{itemize}
\item \srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{334}: \texttt{VEnv.WF.patsStrong} is
\texttt{sorry}, and the paired \texttt{CoeOut (VEnv.WF E) E.OrderedStrong} instance (line 343)
makes every \texttt{VEnv.WF} hypothesis silently yield the strong-system hypotheses, so the
entire strong system and the whole \texttt{Verify/} typechecker-correctness layer become
conditional on it; \texttt{Verify/Primitive.lean} alone gained 30 mentions of
\texttt{OrderedStrong}/\texttt{orderedStrong} where it had none on master. Master's
corresponding entry point, \texttt{Ordered.strong}, was a proved theorem in a sorry-free file;
it no longer exists. See \S\ref{status:sec:sorries} for the full 343-declaration reach. (typing,
metatheory, primitives-core, primitives-arith Review notes; hygiene-review.md \S(a); claims-iota
\#17, \#28)
\item \srcloc{Lean4Lean/Theory/Typing/Basic.lean}{60}: \texttt{IsDefEq.pat} asserts the reduct
at the redex's type with no typing premise on the reduct, i.e.\ it builds subject reduction for
$\iota$ into the judgment itself. The author's own counterexample
(\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{327}, \texttt{List Nat $\equiv$ List Bool})
shows the assumption is false over a merely \texttt{Ordered} environment, so every lemma of
\texttt{Lemmas.lean} proved under \texttt{Ordered} may characterise a relation strictly larger
than the thesis's; \texttt{IsDefEqStrong.pat} (\ref{inductive:isdefeqstrong-pat},
\srcloc{Lean4Lean/Theory/Typing/Strong.lean}{89}) has the correct shape. Any claim of the form
``lean4lean proves $X$ about \texttt{IsDefEq}'' must be qualified by \texttt{patsStrong}.
(typing Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Basic.lean}{583}: nothing derives
\texttt{VInductDecl.WF} from the kernel's own inductive checker
(\texttt{Lean4Lean/Inductive/Add.lean}). \texttt{TrEnv'.induct} takes \texttt{decl.WF env} as a
bare hypothesis; \texttt{Tests/IotaShape.lean} validates the record by \texttt{decide} on
concrete kernel data, which is evidence, not a proof. This is better than master (where the
predicate itself was \texttt{sorry}), but the contribution should be described as specified and
validated, not verified. (inductive Review notes)
\end{itemize}

\subsubsection*{trproj}

\begin{itemize}
\item \srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{400}: \texttt{inferProj.WF}'s own
docstring states it is not provable as stated, because kernel-accepted projections of
reflexive, indexed and nested single-constructor structures have no \ref{def:trproj} derivation
at all. Since \texttt{inferType'.WF} consumes it and \texttt{checkType.WF} has no hypothesis
that its input is translatable, the top-level statements \texttt{inferType.WF'} and
\texttt{checkType.WF} (part of \ref{thm:vtc-toplevel}) are, as of this HEAD, known to be
unprovable without extending the model; neither weakening the conclusion nor adding a scope
hypothesis is discussed. (typechecker Review notes; trexpr Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{1021}: \texttt{TrEnv.proj\_defeq}
(\ref{thm:tr-env-proj-defeq}), trproj's strongest result connecting the projection model to a
translated environment, is orphaned: its only consumer anywhere in the repository is the
\texttt{\#print axioms} check at \srcloc{Lean4Lean/Tests/ProjInhabit.lean}{595}. Its would-be
consumers (\texttt{reduceProjCore.WF}, \texttt{inferProj.WF\_struct}, \texttt{inferProj.WF}) are
all \texttt{sorry}, and its premise \texttt{TrProjCtor} is itself only ever inhabited by hand in
tests. (trenv Review notes; claims-trproj \#25)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{1236}: the \texttt{iota}
retype of this chapter's hypotheses does not only enter at the attributed lines.
\texttt{Reflection.WF.genTele} is master-attributed on every line of its statement and proof, yet
is newly \texttt{sorryAx}-tainted on this branch: its one call \texttt{hXY'.subst E.wf} used to
coerce \texttt{VEnv.WF} to \texttt{VEnv.Ordered} (what \texttt{IsDefEqU.subst} took on master),
and that lemma now takes \texttt{VEnv.OrderedStrong}, so the identical text coerces the other
way. Any line-count of ``what the branch touched'' understates its blast radius. (primitives-arith
Review notes)
\end{itemize}

\subsubsection*{master (pre-existing)}

\begin{itemize}
\item \srcloc{Lean4Lean/Theory/Typing/Injectivity.lean}{11}: the whole file is three
\texttt{sorry}'d inversion principles (\ref{thm:injectivity-open}) and nothing else. They are
what a proof of \texttt{patsStrong} is said to need, so the iota branch's open obligation rests
on an already-open master foundation, and \ref{thm:foralle-inv-derived} carries two independent
gaps. (typing Review notes)
\item \srcloc{Lean4Lean/Theory/Typing/Strong.lean}{679}: \ref{struct:orderedstrong} makes the
environment hypothesis of the strong system non-derivable in the way master's
\texttt{Ordered.strong} was; theorems in \texttt{Strong.lean} are themselves \texttt{sorryAx}-free
because they take \texttt{OrderedStrong} as a hypothesis, but every call site that discharges it
from \texttt{VEnv.WF} --- all of \texttt{UniqueTyping.lean} and through it
\texttt{ChurchRosser.lean}, \texttt{HeadReduction.lean} and the \texttt{Verify} layer --- is
newly tainted. (metatheory Review notes)
\item \srcloc{Lean4Lean/Theory/Typing/ChurchRosser.lean}{1193}: \texttt{NormalEq.parRed}
contains two sorries (1193, 1212), both in the case where a rule step meets a normal equality
(the thesis's Lemma \texttt{gg\_compat}); this is the load-bearing step of Church--Rosser, so
\texttt{ParRedS.church\_rosser}, \texttt{CRDefEq.trans}, \texttt{IsDefEq.church\_rosser},
\texttt{IsDefEq.reduce\_sort}, \texttt{IsDefEq.reduce\_forallE} and \texttt{InferType.exists}
are all unproved. (metatheory Review notes)
\item \srcloc{Lean4Lean/Theory/Typing/UniqueTyping.lean}{174}: the forward direction of
\texttt{IsDefEqU.weakN\_iff} is \texttt{sorry}, consumed by \texttt{NormalEq.weakN\_inv\_DFC},
\texttt{ParRed.weakN\_inv}, \texttt{hasType\_app\_bvar0}, \texttt{IsDefEq.skips},
\texttt{OnCtx.weakN\_inv} and the whole \texttt{weakN\_iff}/\texttt{weak'\_iff} family, hence
most of \texttt{ChurchRosser.lean} and \texttt{HeadReduction.lean}. (metatheory Review notes)
\item \srcloc{Lean4Lean/Verify/Environment.lean}{208}: the \texttt{inductDecl} case of
\texttt{addDecl.WF} is \texttt{sorry}, and nothing anywhere constructs an \ref{struct:add-induct}
witness from \texttt{Environment.addInductive}; the whole inductive-block apparatus of both
branches (\ref{struct:add-induct}, \ref{struct:tr-ind-type}, \ref{thm:tr-env-proj-defeq}, and the
$\sim$1000 lines of lemmas built on them) is correct but, end to end, currently vacuous.
(trenv Review notes; hygiene-review.md \S(g), ``HIGH (value, not hygiene)'')
\item \srcloc{Lean4Lean/Experimental/ShapeLogRelAdequacy.lean}{154}: a live \texttt{sorry} in the
\texttt{const} case of \texttt{LR.adequacy}, the fundamental theorem of the shape logical
relation. \ref{thm:expa-forallE-inv}, \ref{thm:expa-sort-forallE-inv},
\ref{thm:expa-sort-inv} and everything \texttt{UniqueTyping.lean} (Experimental) derives from
them are unproved; the hole predates the commit that landed the injectivity theorems and
\texttt{UniqueTyping.lean} on top of it, and no comment in the source warns of it.
(experimental-logrel Review notes)
\item \srcloc{Lean4Lean/Experimental/SExpr.lean}{679}: \texttt{IsDefEq.strong} is \texttt{sorry};
both \texttt{LE\_Interp.strongSound} and \texttt{LR.adequacy} open with \texttt{replace H :=
H.strong}, so the entire logical-relation layer from \texttt{ShapeLogRel.lean:5054} onward is
conditional on it, on top of 29 further sorry-bearing lines in the same file (30 in all).
(experimental-logrel Review notes)
\item \srcloc{Lean4Lean/Experimental/SExpr.lean}{614}: \texttt{axiom Params.extra\_pat} is a
genuine global axiom, not a class field (the corresponding field is commented out of
\texttt{class Params} at line 42); it asserts that every environment defeq is an instance of a
registered pattern rule, the hard content of $\iota$-reduction, invisible from the files that
use it. (experimental-logrel Review notes)
\item \srcloc{Lean4Lean/Experimental/Thierry.lean}{9} and
\srcloc{Lean4Lean/Experimental/Thierry2.lean}{9}: \texttt{axiom mySorry : $\alpha$} is an
inhabitant of every type, i.e.\ a proof of \texttt{False}, used in \texttt{DF.comp},
\texttt{DF.bot} and elsewhere; both files are scratch formalizations imported by nothing, but the
axiom must be on record so nothing else is ever allowed to depend on them.
\texttt{Thierry2.lean} additionally axiomatizes the judgment it interprets. (experimental-reduction
Review notes)
\end{itemize}

\subsection{Medium severity}

\subsubsection*{iota}

\begin{itemize}
\item \srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{130}: \texttt{VEnv.PatsStrong} is a
six-hypothesis statement with both environments explicit, so every call site reads \texttt{hp \_
\_ hpre₀ .rfl \ldots{} rfl rfl hord} (eight sites), forcing the \texttt{*\_strong} lemmas to
repeat the same composition three or four times; since the statement is discharged only by
\texttt{sorry}, it is also unverified that it is provable in this generality. (typing Review
notes; hygiene-review.md \S(a))
\item \srcloc{Lean4Lean/Theory/Typing/Basic.lean}{92}: \texttt{VEnv.PatTyped} is existential in
$U,\Gamma,e,m_2,B$ and \texttt{Pattern.RHS.Generic} constrains only the holes the reduct uses, so
\texttt{PatWF}/\texttt{Ordered.pat} admits a rule that typechecks only at one convenient
instantiation; documented at \srcloc{Lean4Lean/Theory/Typing/Pattern.lean}{181}, but the name
promises more than the predicate delivers. (typing Review notes; hygiene-review.md \S(a))
\item \srcloc{Lean4Lean/Theory/Typing/Basic.lean}{62}: the \texttt{Pattern.Check}/\texttt{Realizes}
side-condition machinery threaded through \texttt{IsDefEq.pat} and nine induction cases is
exercised only at the trivial check: the one registration point,
\texttt{VEnv.addRecRule}, hard-codes \texttt{Check.true}, and K-like reduction (the rule that
would need a real side condition) is not modelled. Seven supporting lemmas and one premise per
induction case support a condition no registered rule yet uses. (typing Review notes)
\item \srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{188}: \texttt{addQuot\_strong} hand-unrolls
\texttt{addQuot}'s five steps into $\sim$25 lines of explicit \texttt{.trans} chains, brittle to
any change to the quotient block, because \texttt{addQuot} is an \texttt{Option} bind chain
rather than a fold and so cannot reuse \texttt{foldlM\_addConst\_strong}. (typing Review notes)
\item \srcloc{Lean4Lean/Theory/Typing/ChurchRosser.lean}{30}: the docstring of
\texttt{Params.pat\_env} justifies the field by \texttt{extra\_pat}, but the two fields are
logically independent (one is about \texttt{env.defeqs}, the other about \texttt{env.pats});
the comment reads as if \texttt{pat\_env} were derivable. (metatheory Review notes)
\item \srcloc{Lean4Lean/Theory/Typing/ChurchRosser.lean}{12}: the \texttt{Params} class has
exactly one construction, requiring \texttt{DefEqsAsPats}, which fails as soon as an environment
contains a \texttt{def} or the quotient rule; the Church--Rosser/standardization/inference
development of Chapter \ref{chap:metatheory} therefore applies today to no realistic
environment. Documented in the \texttt{DefEqsAsPats} docstring but not stated in the chapters
that build on it. (metatheory Review notes)
\item \srcloc{Lean4Lean/Theory/Typing/Strong.lean}{684}: the pair of \texttt{CoeOut} instances
(\texttt{OrderedStrong}$\to$\texttt{Ordered} and \texttt{VEnv.WF}$\to$\texttt{OrderedStrong})
makes the new sorry-backed hypothesis invisible at use sites: \texttt{UniqueTyping.lean} is
byte-identical to master yet silently acquired the \texttt{patsStrong} dependency. (metatheory
Review notes)
\item \srcloc{Lean4Lean/Theory/Typing/Strong.lean}{672}: the deferred obligation is heavier than
``the $\iota$ rules of the final environment preserve types'': \texttt{PatsStrongOn} is stated
for one environment, while \texttt{VEnv.PatsStrong} quantifies over every well-formed prefix and
every constant-only extension of it traversed by the strengthening induction. (metatheory Review
notes)
\item \srcloc{Lean4Lean/Theory/Typing/InductiveParams.lean}{393}: \texttt{toParams} is a
\texttt{Params} instance only for environments satisfying \texttt{DefEqsAsPats} (no
\texttt{def}, \texttt{mutualDef} or \texttt{quot} at all); every realistic Lean environment fails
it, so the model's own well-formed environments are still not connected to the Church--Rosser
development. (inductive Review notes)
\item \srcloc{Lean4Lean/Theory/Inductive.lean}{174}: \texttt{VExpr.RuleShape} pins only the
number of arguments the reduct passes to the minor premise, not their shape (the thesis requires
$v_i = \lambda x{::}\xi_i.\,\mathrm{rec}_P\,C\,e\,\pi_i[b,x]\,(u_i\,x)$); together with
\texttt{rules\_wf}, which only forces well-typedness, \texttt{VInductDecl.WF} accepts $\iota$
rules the kernel would never generate. (inductive Review notes)
\item \srcloc{Lean4Lean/Theory/Inductive.lean}{257}: K-like reduction is not modelled;
\texttt{addRecRule} registers only the constructor rule and \texttt{VRecursor.k} is recorded but
never used, while the kernel's \texttt{toCtorWhenK} does perform it. For K-like recursors the
model's reduction relation is strictly weaker than the kernel's. (inductive Review notes)
\item \srcloc{Lean4Lean/Theory/Inductive.lean}{93}: \texttt{FieldPositive}, \texttt{CtorPositive}
and \texttt{WF.universes} read the manifest $\Pi$-binders of a field type, whereas the kernel's
\texttt{checkPositivity} reduces to whnf at each step; the model is strictly stricter than the
kernel, which obstructs ever discharging the previous item. (inductive Review notes)
\item \srcloc{Lean4Lean/Theory/Inductive.lean}{335}: \texttt{recs\_over\_block}/\texttt{rules\_ctor}
require every recursor to eliminate one of the block's own type formers, excluding nested
inductives, which the kernel's \texttt{Environment.addInductive} does add; \texttt{TrEnv'} can
never be constructed for such a block. Documented as future work. (inductive Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Basic.lean}{272}: \texttt{AddInduct} carries no
\texttt{: Prop} ascription, so it is \texttt{Type}-valued and the \texttt{induct} constructor of
\texttt{TrEnv'} quantifies over data; necessary for the derived field projections, harmless for
present (all-\texttt{Prop}-eliminating) consumers, but an undocumented departure from master's
\texttt{inductive AddInduct \ldots{} : Prop}. (trenv Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Basic.lean}{240}: \texttt{TrRecursor.all} and
\texttt{TrRecursor.k} (line 245) are never used anywhere; extra proof obligations on
\ref{struct:add-induct}'s producer that buy nothing, \texttt{k} in particular recording a K-like
flag the model has no corresponding rule for. (trenv Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Basic.lean}{165}: \texttt{insertConsts\_find?\_none}
is dead code, its only occurrence besides its own statement being its own recursive call.
(trenv Review notes; unused-contrib.md)
\item \srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{903}: \texttt{TrEnv.pats\_iota\_inv\_shape}
is redundant with \texttt{TrEnv'.pats\_iota\_inv\_shape} (the proof is literally that lemma
applied), and unlike its sibling \texttt{pats\_iota'} it does not convert \texttt{SMap.find?}
into \texttt{Environment.find?} despite its docstring's claim; \texttt{proj\_defeq} still does
the conversion by hand. (trenv Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{959} and
\srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{1166}: misfiled material --- the
$\beta$-telescope family and \texttt{TrExpr.mkAppList} are pure \texttt{VExpr}/\texttt{TrExpr}
metatheory with no environment-translation content, living in
\texttt{Verify/Environment/Lemmas.lean} only because \texttt{proj\_defeq} needs them there.
(trenv Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Lemmas.lean}{917}: \texttt{TrEnv.iota\_defeq} is a
three-line wrapper over \texttt{VEnv.IsDefEq.pat} with no \texttt{TrEnv} hypothesis at all, yet
is named as if it had one. (trenv Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Quot.lean}{27}: \texttt{AddQuotAux} hand-replays the
binder names, binder infos and \texttt{withLocalDecl} order of \texttt{Lean4Lean/Quot.lean} with
nothing linking the two beyond the proofs breaking if they diverge; the
\texttt{T\ldots\_tr} derivations (line 331) are 60 lines of hand-built \ref{ind:trexprs} trees.
Correct, expensive to maintain. (trenv Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{421}: all 67 iota-attributed
lines of Chapter \ref{chap:primitives-arith} are the same \texttt{Ordered}$\to$\texttt{OrderedStrong}
re-threading; every theorem there now depends on \texttt{patsStrong} where on master it depended
only on \texttt{Ordered}. The declaration site documents this in a comment; none of the
consuming files does, and \texttt{DivMod.lean}/\texttt{Gcd.lean}/\texttt{Bitwise.lean} have no
module docstring at all, so a reviewer reading any one of them in isolation would conclude the
arithmetic primitives are fully verified. (primitives-arith Review notes)
\item \srcloc{Lean4Lean/Verify/Primitive.lean}{29}: the same retype (\texttt{Ordered}$\to$
\texttt{OrderedStrong}) was applied uniformly across Chapter \ref{chap:primitives-core} rather
than minimally; 19 declarations there gained \texttt{sorryAx} on master's route alone, when only
4 lemmas actually need the stronger hypothesis (through \texttt{HasType.const\_inv}) and the
rest could have kept \texttt{Ordered}. Reads as a global search-and-replace rather than a
considered minimisation. (primitives-core Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive.lean}{6}: the module docstring's claim that
``the checker, extension, and declaration modules introduce no additional sorry-backed
assumptions'' is still literally true but now understates the layer's real hypotheses
(\texttt{OrderedStrong}, produced only by the admitted \texttt{patsStrong}); not revisited when
the hypotheses were strengthened. (primitives-core Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive/Basic.lean}{856}: the syntactic guard
\texttt{Expr.natBinderTypes} is a hypothesis of the well-founded-recursion theorems, not a check
the recogniser performs; true by \texttt{rfl} at today's call sites, but the verified statement
is conditional on a caller property the kernel never tests. (primitives-core Review notes)
\item \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{17}: \texttt{inductiveReduceRecCore.WF}
(\ref{thm:vtc-iota-reduce-core}) has no consumer; \texttt{reduceRecursor.WF} two declarations
below is still \texttt{sorry} and a repo-wide grep finds no other reference. The contribution
proves the hard arithmetic of the $\iota$ step but connects it to no statement about the kernel.
(typechecker Review notes; hygiene-review.md \S(g))
\item \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{24}: \texttt{hmaj} requires the major
premise, as it occurs in the recursor spine, to already be a constructor application, whereas
\texttt{inductiveReduceRec} passes a major obtained by \texttt{toCtorWhenK}, \texttt{whnf},
literal conversion and \texttt{toCtorWhenStruct}; the bridging step rebuilding the spine and
transporting the translation is neither provided nor mentioned. (typechecker Review notes)
\item \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{23}: \texttt{hsat} (exact saturation of
the constructor application) is assumed and the docstring calls it a consequence of well-typing
``left to the caller'', but that consequence is proved nowhere in the repository; it also
excludes over-applied constructor applications, exactly where the kernel's and the pattern's
argument-slicing conventions could genuinely disagree. (typechecker Review notes)
\item \srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{392}: \texttt{inferProj.WF\_struct}
is sorry and unreferenced (0 dependants, \texttt{sorry-grep.md} \S5); its docstring advertises
coverage of \texttt{TrProjCtor}, which does not occur in its actual hypotheses (kernel-side
metadata facts), and even proved it would not discharge \ref{thm:vtc-inferproj} since its listed
conditions are not the ones \texttt{inferProj} checks. (typechecker Review notes; proj Review
notes; hygiene-review.md \S(c))
\item \srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{398}: the whole projection story
rests on \texttt{inferProj.WF\_struct}, which is sorry, with its 15-line informal proof sketch
living only in a docstring and mechanised only on two hand-built \texttt{Tests/ProjInhabit.lean}
instances; nothing shows a kernel-accepted projection yields a \texttt{TrProjCtor}, so
\ref{def:trproj}'s \texttt{proj} case is never inhabited from a real term. (proj Review notes)
\item \srcloc{Lean4Lean/Theory/Proj.lean}{127}: \texttt{VExpr.projTy} has no library consumer
(only an \texttt{example}), and the identity its docstring asserts,
$\mathrm{projTy}=(\mathrm{projMotiveBody}\,i).\mathrm{inst}\,e$, is never proved; the model types
a projection through \ref{def:proj-motive-body} instead, so the two readings of ``the
projection's type'' coexist unreconciled, visibly so in \texttt{Tests/ProjShape.lean}'s own
error message, which names \texttt{projTy} while the type actually checked is built from
\texttt{projMotiveBody}. (proj Review notes)
\item \srcloc{Lean4Lean/Tests/ProjInhabit.lean}{49}: \texttt{VEnv.addInduct} checks only name
clashes and closedness, never well-formedness, and neither \texttt{VInductDecl.WF} nor
\texttt{env.WF} is ever proved for the two hand-built environments; the witnesses show the
premises of \ref{struct:trprojctor} are jointly satisfiable, not satisfiable in a well-formed
environment, so \ref{thm:tr-env-proj-defeq} (which needs a \texttt{TrEnv}) is not exercised end
to end on them. (proj Review notes)
\item \srcloc{Lean4Lean/Experimental/LogRel.lean}{353}: \texttt{fundamental} is unproved and
\texttt{LREqTy.defeq\_r}, all three branches of \texttt{LREqTy.symm}, \texttt{LVIsType.sort} and
\texttt{LVIsType.lift} are \texttt{sorry} or \texttt{stop} (which macro-expands to
\texttt{repeat sorry} and so is invisible to \texttt{grep}); the module is imported by nothing
and superseded by \texttt{ShapeLogRel.lean}. (experimental-logrel Review notes; master)
\item \srcloc{Lean4Lean/Experimental/LogRel.lean}{70}: \texttt{Lean4Lean.SExpr.LogRel} is
declared three times in this directory with incompatible definitions (inductive here, structure
in \texttt{ShapeLogRel.lean} and in \texttt{MoreStepIndexed.lean}); likewise
\texttt{Classifier'} and \texttt{NormalType} twice each. Compiles only because no module imports
two of them. (experimental-logrel Review notes; master)
\item \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{1665}: lines 1665--1732 are a block
comment holding an abandoned 58-line proof of a declaration (\texttt{Shape.WF.plift}) absent
from the compiled environment, containing seven \texttt{sorry}s and a \texttt{stop}; this is
why a naive \texttt{grep -c sorry} reports 8 for a file with no live sorry. (experimental-logrel
Review notes; master)
\item \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{10}: \texttt{set\_option
backward.do.legacy true} at file scope, on a 6100-line file, works around
leanprover/lean4\#13305 for one proof family; large blast radius for a localised problem.
(experimental-logrel Review notes; master)
\item \srcloc{Lean4Lean/Experimental/CoinductiveLogRel.lean}{1}: almost entirely a block comment
sketching a \texttt{coinductive} command that does not exist in Lean 4; its only live content is
unused, yet the file still imports \texttt{HeadReduction.lean} and produces an olean under the
\texttt{Lean4Lean.Experimental} glob. (experimental-logrel Review notes; master)
\item \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{3430}: the pattern-matching lemmas rest on
the \texttt{Params} field \texttt{pat\_wf}/\texttt{pat\_uniq}, and there is no \texttt{Params}
instance anywhere in the repository, so nothing exhibits an environment satisfying either.
(experimental-logrel Review notes; master)
\item \srcloc{Lean4Lean/Experimental/ParallelReduction.lean}{909}: the $\iota$ case added here,
plus the \texttt{Typing.pat\_env} field in \texttt{NormalEq.lean}, duplicates exactly what the
branch added to \texttt{ChurchRosser.lean}; both files carry an upstream \texttt{TODO: remove,
this is now part of ChurchRosser.lean}, so the $\iota$ rule is maintained in two places with no
cross-reference. (experimental-reduction Review notes)
\item \srcloc{Lean4Lean/Experimental/SExpr.lean}{981}: the chapter narrative calls \texttt{WHRed}
deterministic, but \texttt{WHRed.determ}'s proof is sorry in all five case splits where an
\texttt{extra} step meets anything, including another \texttt{extra} step; only the
$\beta$/application fragment is actually proved deterministic. (experimental-reduction Review
notes)
\item \srcloc{Lean4Lean/Experimental/Stratified.lean}{79} and
\srcloc{Lean4Lean/Experimental/StratifiedUntyped.lean}{59}: the hypothesis of an exported
theorem was silently strengthened from \texttt{Ordered env} to \texttt{OrderedStrong env}; forced
and loses no realistic instance, but neither site explains it. (experimental-reduction Review
notes)
\item \srcloc{Lean4Lean/Experimental/SExpr.lean}{609}: the \texttt{SExpr} line of work still has
no $\iota$ rule in its declarative equality; the pattern-based rule is commented out and
reduction enters only through \texttt{env.defeqs} plus the global \texttt{Params.extra\_pat}
axiom, while \texttt{WHRed}/\texttt{ParRed} in the same file do carry a \texttt{Pat}-based rule.
(experimental-reduction Review notes)
\item \srcloc{Lean4Lean/Experimental/UniqueTyping.lean}{138}: no textual \texttt{sorry}, but
\texttt{IsDefEq.toHasTypeS} opens with \texttt{h.strong} and \texttt{SExpr.IsDefEq.strong} is
\texttt{:= sorry}; \texttt{uniq\_sort}, \texttt{toIsDefEq'} and \texttt{iff\_isDefEq'} are all
conditional, so a grep-based status label would mislead. (experimental-reduction Review notes)
\item \srcloc{Lean4Lean/Experimental/DomainTheory.lean}{223}: \texttt{Dom.out} is
\texttt{sorryAx}-backed through the \texttt{stop} tactic despite no literal \texttt{sorry} in the
file; the same pitfall recurs at \srcloc{Lean4Lean/Experimental/LogRel.lean}{320} and
\srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{1703}. (experimental-reduction Review notes)
\item \srcloc{Lean4Lean/Experimental/MoreStepIndexed.lean}{420}: a \texttt{\#exit} truncates
elaboration, so \texttt{TypeEqS}/\texttt{TypeEq}, the two declarations the file exists to build,
are never compiled and do not appear in the environment; the file still builds green.
(experimental-reduction Review notes)
\end{itemize}

\subsubsection*{Documentation and process (iota/trproj, hygiene)}

\begin{itemize}
\item \texttt{Theory/} comment density: contributed code is 25.3\% comment lines against
master's 1.7\% in the same directory (\texttt{hygiene-review.md} \S(c)); extremes are a 56-line
module header on the 449-line \srcloc{Lean4Lean/Theory/Proj.lean}{3} and a 27-line docstring on
the 5-line \texttt{DefEqsAsPats}
(\srcloc{Lean4Lean/Theory/Typing/InductiveParams.lean}{351}, the longest docstring in
\texttt{Theory/}; master's own \texttt{Theory/} maximum outside \texttt{LevelSat.lean} is 11
lines). The single loudest AI-authored-looking signal in the diff, though the content itself is
substantive (derivations, thesis section numbers, explicit non-coverage statements) rather than
restatement. (hygiene-review.md \S(c))
\item History hygiene: two pairs of commits are duplicated re-merges of a rebased \texttt{iota}
(\texttt{655dd3f}/\texttt{75ffde9} share a patch-id; \texttt{7a68882}/\texttt{6fd8a1d} share a
subject and are, per \texttt{typechecker.tex}'s own review note, literally the same patch under
two branch labels, so blame over-attributes 141 lines of \texttt{WHNF.lean} to trproj that are
really iota's); a whole file, \texttt{Theory/Pattern.lean}, was created over 4 commits and then
deleted again 2 commits later without ever reaching the branch tip. Roughly 27\% of the branch's
own written lines (net +7762/-363, gross +11439/-3399) were written and then removed inside the
branch, the two largest offenders being \texttt{Verify/Environment/Lemmas.lean} (22 commits) and
\texttt{Theory/Typing/InductiveParams.lean} (14 commits, over half rewritten). (hygiene-review.md
\S(e); typechecker Review notes)
\end{itemize}

\subsection{Low severity}

\subsubsection*{iota}

\begin{itemize}
\item \srcloc{Lean4Lean/Theory/Inductive.lean}{196}, \srcloc{Lean4Lean/Theory/Inductive.lean}{202},
\srcloc{Lean4Lean/Theory/Inductive.lean}{242}: dead code. \texttt{RecShape.one\_le\_numMotives},
\texttt{RecShape.majorFormer?\_eq} and \texttt{LargeElim.shape} have no reference anywhere in the
repository. (inductive Review notes; unused-contrib.md \#45,\#46,\#47)
\item \srcloc{Lean4Lean/Theory/Typing/Pattern.lean}{509}: the \texttt{RHS.spine}/\texttt{iotaCounts}
cluster (8 declarations, $\sim$70 lines, lines 509--678) is used only by itself, ending in
\texttt{iotaRHS\_iotaCounts}, which exists only to substantiate a section docstring's claim.
(inductive Review notes; hygiene-review.md \S(g); unused-contrib.md \#60)
\item \srcloc{Lean4Lean/Theory/Typing/InductiveLemmas.lean}{451}: placement/naming.
\texttt{nodup\_map\_inj\_on} is a pure \texttt{List} lemma declared as
\texttt{Lean4Lean.VEnv.nodup\_map\_inj\_on}; the generic \texttt{foldlM} toolkit and the
\texttt{addQuot}/\texttt{addDefEqs} lemmas live in a file named \texttt{InductiveLemmas};
\texttt{Pattern.inter\_app\_const} and two siblings are \texttt{\_root\_} \texttt{Pattern} lemmas
declared inside \texttt{namespace VEnv}. (inductive Review notes)
\item \srcloc{Lean4Lean/Theory/Inductive.lean}{259}: \texttt{addRecRule} spells the major index
out by hand (\texttt{numParams + numMotives + numMinors + numIndices}) instead of using
\texttt{r.getMajorIdx}, which every lemma about it does use, and its own docstring claims
``major at \texttt{getMajorIdx}''. (inductive/syntax Review notes; hygiene-review.md \S(c))
\item \srcloc{Lean4Lean/Theory/Inductive.lean}{75}, \srcloc{Lean4Lean/Theory/Inductive.lean}{107},
\srcloc{Lean4Lean/Theory/Inductive.lean}{226}: fidelity gaps against the kernel.
\texttt{ValidIndApp} drops the kernel's exact-arity check although its docstring claims to
mirror \texttt{isValidIndApp?}; \texttt{FieldInIndices} searches only arguments past
\texttt{nparams} where the kernel searches all of them; \texttt{LargeElim} tests a typing at
\texttt{sort 0} where the kernel tests \texttt{isAlwaysZero} on the inferred level. The three
agree only up to unrecorded side arguments. (inductive Review notes)
\item \srcloc{Lean4Lean/Theory/Inductive.lean}{351}: \texttt{WF.universes} hides the purely
syntactic bound \texttt{decl.nparams} $\le$ \texttt{t.type.piArity} inside a clause guarded by
\texttt{addTypes} succeeding, so it is unavailable if stage 0 fails; and no clause of
\texttt{VInductDecl.WF} mentions \texttt{VRecursor.all}. Neither is recorded in the source.
(inductive Review notes)
\item \srcloc{Lean4Lean/Theory/Inductive.lean}{134}: \texttt{MinorFor} makes the
constructor-to-minor map injective but no lemma derives that and nothing uses it; the proofs
that need injectivity appeal to \texttt{rules\_nodup} instead. (reviews/inductive.md)
\item \srcloc{Lean4Lean/Theory/VExpr.lean}{919}: dead upstream code created by a refactor.
Master's one-line proof of \texttt{lift'\_inst\_hi} was replaced by a re-derivation from a new
\texttt{lift'\_instN\_hi}, leaving \texttt{lift\_r\_one} (and the chain that fed only it ---
\texttt{Subst.lift\_r\_comm}, \texttt{Subst.trunc}, \texttt{Subst.Depth.one},
\texttt{Subst.Depth}, 6 declarations) with no remaining consumer. (syntax Review notes;
hygiene-review.md \S(g))
\item \srcloc{Lean4Lean/Theory/VExpr.lean}{1232}: \texttt{CtorHeaded.forallE} is unused, proved
by \texttt{:= h} because definitionally trivial, and its docstring states a different
proposition than the lemma. (syntax Review notes; hygiene-review.md \S(a),\S(c))
\item \srcloc{Lean4Lean/Theory/VExpr.lean}{1046}: stale section docstring, still promising
readers decidability instances that were relocated to \texttt{Tests/ShapeDecide.lean}.
(syntax Review notes; hygiene-review.md \S(c))
\item \srcloc{Lean4Lean/Theory/VExpr.lean}{753}: \texttt{Lift.liftVar\_consN\_lt} and
\texttt{liftVar\_consN\_succ} have no consumer, making \texttt{Lift.consN\_fixes} dead in effect
too; of the four-lemma block only \texttt{consN\_cons} is used. (syntax Review notes;
unused-contrib.md \#63,\#64)
\item \srcloc{Lean4Lean/Theory/VExpr.lean}{1009}: redundancy left unresolved and inconsistently.
\texttt{subst\_instN} subsumes master's \texttt{subst\_inst} at $n=0$ and
\texttt{liftN\_subst\_liftN} subsumes master's \texttt{lift\_subst\_lift} at $i=0$ (the latter's
own docstring says so), yet both master lemmas keep independent hand proofs while
\texttt{lift'\_inst\_hi} in the same block \emph{was} re-derived; also, \texttt{subst\_instN}'s
docstring says ``under \texttt{m} binders'' while the statement binds \texttt{n}. (syntax Review
notes; hygiene-review.md \S(c))
\item \srcloc{Lean4Lean/Theory/VExpr.lean}{1133}: the $\lambda$-telescope block
(\texttt{lamBinders}, \texttt{lamBinders\_length}, \texttt{foldr\_lam\_lamBinders}) has exactly
one consumer, and \texttt{lamBinders\_length} is reached only through \texttt{simp}, not by
name; thin, but not dead. (syntax Review notes)
\item \srcloc{Lean4Lean/Theory/VExpr.lean}{1295}: \texttt{const\_mkApps\_spine} bundles two
independent facts into one conjunction consumed only as \texttt{.1}/\texttt{.2}, and together
with \texttt{eq\_const\_mkApps\_of\_spine} has no consumer outside the file. (syntax Review
notes; unused-contrib.md \#67)
\item \srcloc{Lean4Lean/Theory/VExpr.lean}{1200}: a docstring attached to \texttt{isSort} alone
describes all six declarations of the block, which exists only to serve the decidability
instances of the test file. (syntax Review notes)
\item \srcloc{Lean4Lean/Theory/VExpr.lean}{108}: \texttt{decClosedN} stayed in the theory file
while sibling head-shape instances moved to \texttt{Tests/ShapeDecide.lean}; it is the one such
instance a \emph{definition} (\texttt{VEnv.addRecRule}) depends on, which the module docstring
does not flag as the exception. (syntax Review notes)
\item \srcloc{Lean4Lean/Theory/VDecl.lean}{51}: \texttt{VRecursor.getFirstIndexIdx} is defined
and documented but has no consumer anywhere; every other use of the concept calls Lean's own
\texttt{RecursorVal} field. (syntax Review notes; hygiene-review.md \S(a))
\item \srcloc{Lean4Lean/Theory/VDecl.lean}{41}: \texttt{VRecursor.k} records the K-like flag but
is, by its own docstring, unused by the theory; the structure advertises coverage the
development does not have. (syntax Review notes)
\item \srcloc{Lean4Lean/Theory/VEnv.lean}{44}: \texttt{VEnv.addPat} cannot fail --- unlike
\texttt{addConst} it performs no freshness or consistency check, so an \texttt{Ordered}
environment may carry two conflicting reducts for one pattern until \texttt{VEnv.WF} recovers
functionality later. (syntax Review notes; hygiene-review.md \S(a))
\item \srcloc{Lean4Lean/Theory/Quot.lean}{11}: after the iota work the model has two mechanisms
for computation rules (\texttt{quotDefEq} is still a \texttt{VDefEq}, not a \texttt{pats}
entry); the duplication is acknowledged nowhere in the code. (syntax Review notes)
\item \srcloc{Lean4Lean/Theory/Proj.lean}{111}: \ref{def:proj-fns} mentions itself twice in its
own defining equation, so the unfolded expansion of field $i$ is exponential in $i$ and every
substitution lemma applies its induction hypothesis twice. (proj Review notes)
\item \srcloc{Lean4Lean/Theory/Proj.lean}{195}: \ref{def:proj-inst-fields} is a second
telescope-substitution convention beside master's \texttt{VExpr.insts}; no lemma relates them, so
the two only ever meet through raw \texttt{inst}. (proj Review notes)
\item \srcloc{Lean4Lean/Theory/Proj.lean}{136}: \ref{def:proj-binder-arity} pins only the number
of the minor premise's binders, not their types, yet its docstring and
\texttt{TrProjCtor.minor\_arity} read it as pinning the fields exactly. (proj Review notes)
\item \srcloc{Lean4Lean/Theory/Proj.lean}{140}: \ref{def:proj-ty} has no library consumer, and
\texttt{projMotiveBody\_zero}/\texttt{instFields\_nil} are \texttt{@[simp]} but never invoked
explicitly. (proj Review notes; hygiene-review.md \S(c))
\item \srcloc{Lean4Lean/Theory/Proj.lean}{1}: the thesis citations attached to the projection
work (\texttt{inv\_x}, typesys.tex; $\pi_2$, Wtypes.tex) are individually accurate but are
borrowed idioms from results that prove different things, not inherited theorems.
(proj Review notes)
\item \srcloc{Lean4Lean/Tests/ShapeDecide.lean}{20}: 22 global \texttt{Decidable} instances
declared from a \texttt{Tests} module (21 in \texttt{Lean4Lean.VExpr}); safe only because
nothing in the library imports the module, and the widest of them
(\srcloc{Lean4Lean/Tests/ShapeDecide.lean}{27}) decides an existential over any
\texttt{Option}/\texttt{DecidablePred} pair, not a library predicate at all. (proj Review notes;
hygiene-review.md \S(d))
\item \srcloc{Lean4Lean/Tests/IotaShape.lean}{151}: the $\iota$ oracle is lean4lean's own
\texttt{inductiveReduceRec}, whose $\iota$ step is the 21 trproj lines of
\texttt{Inductive/Reduce.lean}, so both sides of the comparison live in this repository; a
shared misreading would not be caught. (proj Review notes)
\item \srcloc{Lean4Lean/Tests/IotaShape.lean}{86}: the \texttt{recs\_elim} check assumes the
recursor's extra universe parameter sits at index 0 of \texttt{levelParams}, which is how Lean
generates recursors but is nowhere checked. (proj Review notes)
\item \srcloc{Lean4Lean/Tests/IotaShape.lean}{295}: \texttt{checkBlockRejected} only asks that
\emph{some} block clause fail; which clause a nested block is expected to fail is pinned for one
fixture (\texttt{Tree}) and discarded for the other eight. (proj Review notes)
\item \srcloc{Lean4Lean/Tests/IotaShape.lean}{336}: the fixture docstring mislabels
\texttt{Wrap} as small-eliminating; it is in fact subsingleton-eliminating and carries the extra
universe parameter (only the wording is wrong; the fixture is exercised correctly).
(proj Review notes)
\item \srcloc{Lean4Lean/Tests/IotaShape.lean}{454}: the whole battery is one $\sim$150-line
\texttt{run\_meta} block, so a failure reports only the first mismatch and every later
assertion, including the remaining negative controls, is never reached. (proj Review notes)
\end{itemize}

\subsubsection*{trproj}

\begin{itemize}
\item \srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{643}: \ref{def:trproj} existentially
quantifies six pieces of data, two of which are pinned by other fields (parameter count by
\texttt{params\_length}, field telescope by \texttt{ctor}); replacing them by definitions would
remove an obligation from each of the three proofs that rebuild the record. (trexpr Review
notes)
\item \srcloc{Lean4Lean/Verify/Typing/Expr.lean}{97}: \texttt{TrProjCtor.pat} asserts only that
\emph{some} reduct is registered under the $\iota$ key; the reduct itself is not pinned and the
key, a sum, does not exclude a different motive/minor/index split adding to the same total. Is
the stated obstacle to \ref{thm:trproj-uniq}. (trexpr Review notes)
\item \srcloc{Lean4Lean/Verify/LocalContext.lean}{183}: a global \texttt{DecidableEq FVarId}
instance is installed inside \texttt{namespace Lean.LocalContext}, under a section heading about
the empty local context, though it has nothing to do with \texttt{LocalContext} and could have
reused \texttt{instDecidableEqOfLawfulBEq} as \texttt{DefinitionSafety} does nearby.
(trexpr Review notes; hygiene-review.md \S(d))
\item \srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{2349}: \texttt{TrExprS.mkAppList\_inv}
overlaps with the pre-existing \texttt{AppStack.build}, leaving two spine-inversion idioms in
one file. (trexpr Review notes)
\item \srcloc{Lean4Lean/Verify/Expr.lean}{745}: of the three spine lemmas added here, only
\texttt{getAppArgsList\_mkAppList} has an explicit consumer;
\texttt{getAppArgsRevList\_mkAppList} has no consumer outside its own file. (trexpr Review notes)
\item \srcloc{Lean4Lean/Verify/Typing/Expr.lean}{84}: the scope paragraph of
\texttt{TrProjCtor} makes precise prose claims about the kernel's \texttt{inferProj} that nothing
in the repository formalizes; the completeness boundary is asserted, not verified. (trexpr
Review notes)
\item \srcloc{Lean4Lean/Verify/LocalContext.lean}{181}: within the iota block,
\texttt{toList\_empty} and \texttt{WF.empty} exist only to serve \texttt{find?\_empty} three
lines later. (trexpr Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Quot.lean}{521}: mechanical repetition ---
\texttt{addQuot.WF} extracts four \texttt{checkName} results with four near-identical
seven-line blocks and rebuilds \texttt{safePrimitives} with a 22-line hand-nested chain that a
single auxiliary lemma would remove. (trenv Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Quot.lean}{20}: \texttt{withLocalDecl\_run} lands in
the root namespace under a very general name; \texttt{AddQuotAux.Environment.get\_ok} is a
generally useful lemma buried in a private auxiliary namespace. (trenv Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Basic.lean}{34}: some lines the per-line blame marks
as contributed are master code relocated by refactor commits
(\texttt{TrConstant.sf\_mono}/\texttt{mono}, \texttt{TrConstVal.mono}, \texttt{TrDefVal.mono},
\texttt{insertDefs\_wf}); 16 of the 398 iota lines in \texttt{Basic.lean} are of this kind, so
raw line counts overstate the branch slightly. (trenv Review notes, ``reviewer caveat, not a
defect'')
\item \srcloc{Lean4Lean/Verify/TypeChecker/Reduce.lean}{143}: \texttt{reduceProjCore.WF} and
\texttt{tryEtaStructCore.WF} are the two structure-side obligations the richer
\texttt{TrProj}/\texttt{TrProjCtor} metatheory was built to support, and neither was attempted;
since the branch closed 5 of master's 7 \texttt{TrProj} sorries elsewhere, leaving these
untouched makes the visible contribution narrower than its supporting infrastructure.
(typechecker Review notes)
\item \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{1}: the precomputed blame tags all 141
lines of this file as trproj, but \texttt{git diff iota trproj} on the file is empty and the
iota/trproj commits are the same patch with the same author date; any line count of ``trproj
lines'' over-attributes this file. (typechecker Review notes; see Documentation/process above)
\item \srcloc{Lean4Lean/Verify/TypeChecker.lean}{21}: \texttt{VEnvs.axiom\_of\_choice} is a
deliberately misleading name for a finite case split; documented as such, but will still
surprise a grep-based audit for appeals to choice. (typechecker Review notes)
\item \srcloc{Lean4Lean/Tests/ProjShape.lean}{136}: the \texttt{Sigma.snd} level-list negative
control wraps \texttt{checkProj} in \texttt{try \ldots{} catch \_ => pure false}, so any
unrelated failure makes the control pass vacuously. (proj Review notes)
\item \srcloc{Lean4Lean/Tests/ProjShape.lean}{78}: \texttt{(VLevel.ofLevel lps
(lvls j)).getD .zero} and \texttt{toLevel}'s \texttt{ls.getD i .anonymous} silently default a
mistyped level argument instead of failing. (proj Review notes)
\item \srcloc{Lean4Lean/Tests/ProjShape.lean}{113}: the agreement between
\ref{def:proj-motive-body} and the kernel's \texttt{inferProj} is checked with \texttt{isDefEq},
which on the kernel side may use structure eta and projection reduction the model deliberately
lacks; establishes agreement up to kernel conversion, strictly weaker than anything the model
reproduces. (proj Review notes)
\item \srcloc{Lean4Lean/Tests/ProjInhabit.lean}{586}: the \texttt{\#guard\_msgs in \#print axioms}
block hardcodes a seven-element axiom list, brittle under any unrelated upstream proof change,
and the prose attribution of \texttt{sorryAx} to unique typing and $\Pi$-injectivity is a claim
the guard cannot itself verify. (proj Review notes)
\item \srcloc{Lean4Lean/Tests/ProjInhabit.lean}{179}: the \texttt{Plain} and \texttt{Dependent}
namespaces duplicate about 20 near-identical declarations, \texttt{Dependent} subsuming
\texttt{Plain} except for one case; untracked near-copies also sit in
\texttt{review-artifacts/inhabitation/}. (proj Review notes)
\item \srcloc{Lean4Lean/Tests/ProjInhabit.lean}{172}: asymmetric packaging --- \texttt{Plain}
exposes \texttt{trProj0} but no \texttt{trProj1}; \texttt{Dependent} exposes
\texttt{trProjDep1} but no \texttt{trProjDep0}. (proj Review notes)
\item \srcloc{Lean4Lean/Tests/ProjInhabit.lean}{353}: 22 declarations for a six-step $\beta$
reduction, because \texttt{IsDefEqU.betaN} needs \texttt{VEnv.WF}, which these hand-built
environments lack; separately, $\sim$50 namespace-level one-use theorems
(\texttt{hbeta5}, \texttt{hc5}, \ldots) are declared where upstream style would use local
\texttt{have}s. (proj Review notes; hygiene-review.md \S(d))
\item \srcloc{Lean4Lean/Tests/ProjShape.lean}{155}: several top-level definitions
(\texttt{usS}, \texttt{ps}, \texttt{Fs}, \texttt{structTy}, \texttt{P₀}) use maximally generic
names inside an unscoped section. (hygiene-review.md \S(d))
\item \texttt{.github/workflows/ci.yml:25}: the comment states \texttt{Lean4Lean.Tests} is among
\texttt{defaultTargets}, but \texttt{lakefile.toml:2} lists only \texttt{Lean4Lean},
\texttt{lean4lean}, \texttt{Lean4Lean.Theory} and \texttt{Lean4Lean.Verify}; the test modules
are in fact built by a separate CI step, so nothing is unchecked, but the comment is wrong.
(proj Review notes)
\item \srcloc{Lean4Lean/Experimental/StratifiedUntyped.lean}{51}: the added
\texttt{IsDefEqU1.pat} constructor is never eliminated; its only would-be consumer is inside a
commented-out block. (experimental-reduction Review notes)
\item \srcloc{Lean4Lean/Experimental/Stronger.lean}{28}: \texttt{pats \_ \_ := False} silently
restricts every theorem about erased environments in the file to $\iota$-free ones; pragmatic,
since the file dead-ends in four sorries regardless. (experimental-reduction Review notes)
\item \srcloc{Lean4Lean/Inductive/Reduce.lean}{71}: \texttt{inductiveReduceRecCore}, the
21-line ι-step extraction trproj carved out of \texttt{inductiveReduceRec}, sits inside a
\texttt{section} whose \texttt{variable}s (\texttt{[Monad m], env, whnf, inferType, isDefEq}) it
does not use; correct today only because Lean binds \texttt{variable}s on use, so a future
reference to \texttt{env} would silently change its signature. (kernel Review notes;
hygiene-review.md \S(f))
\end{itemize}

\subsubsection*{master (pre-existing)}

\begin{itemize}
\item \srcloc{Lean4Lean/Inductive/Reduce.lean}{91}: after the trproj split, the unchanged master
docstring of \texttt{inductiveReduceRec} still describes the $\iota$ slicing in full, now
\texttt{inductiveReduceRecCore}'s job and documented there too, so the algorithm is stated
twice. (kernel Review notes)
\item \srcloc{Lean4Lean/TypeChecker.lean}{946}: \texttt{TypeChecker.etaExpand} has no call site
anywhere under \texttt{Lean4Lean/}; if it realizes the thesis's $\mathrm{rec}$-normal-form
preprocessing, that intent is undocumented and unenforced. (kernel Review notes)
\item \srcloc{Lean4Lean/ForEachExprV.lean}{25}: \texttt{Expr.forEachV}/\texttt{forEachV'} appear
dead; the module is imported by \texttt{TypeChecker.lean} but neither function has a call site.
(kernel Review notes)
\item \srcloc{Lean4Lean/TypeChecker.lean}{593}: \texttt{quickIsDefEq} destructures
\texttt{TypeChecker.State} positionally as \texttt{.mk a1 \ldots{} a7 (eqvManager := m)};
reordering or adding a field would silently or confusingly change what this matches.
(kernel Review notes)
\item \srcloc{Lean4Lean/TypeChecker.lean}{299}: the \texttt{eagerReduce} marker (consulted at
four sites) has no thesis counterpart and no local docstring stating what the sites jointly
guarantee, though it mirrors core Lean's own gadget and is correctly absent from
\texttt{divergences.md}. (kernel Review notes)
\item \srcloc{Lean4Lean/Inductive/Add.lean}{453}: \texttt{AddInductive.run} computes its
\texttt{isUnsafe} binding twice (lines 453 and 470), the second silently shadowing the first.
(kernel Review notes; hygiene-review.md \S(f))
\item \srcloc{Lean4Lean/TypeChecker.lean}{493}: \texttt{reducePowMaxExp} silently declines to
reduce \texttt{Nat.pow} above exponent $2^{24}$ (matching the C++ kernel's own cap), but the
incompleteness is not listed in \texttt{divergences.md}. (kernel Review notes)
\item \srcloc{Lean4Lean/TypeChecker.lean}{845}: the \texttt{s.isConstOf ``true} shortcut in
\texttt{isDefEqCore'} is an asymmetric special case with neither a thesis counterpart nor a
\texttt{divergences.md} entry. (kernel Review notes)
\item \srcloc{Lean4Lean/TypeChecker.lean}{355}: \texttt{reduceProj} is written in an awkward
explicit-bind style for the benefit of its own proof, and a commented-out scratch block is left
at the end of the file (line 968). (kernel Review notes)
\item \srcloc{Main.lean}{29}: \texttt{FuelConfig.toObj} uses \texttt{panic!} when the derived
JSON encoding is not an object, inside a command-line argument parser. (kernel Review notes)
\item \srcloc{Lean4Lean/FuelConfig.lean}{12}: the docstring's claim ``Defaults are set so
mathlib passes'' has zero supporting evidence anywhere in the repository (no CI job, test or
benchmark mentions mathlib). (reviews/kernel.md)
\item \texttt{divergences.md:17} vs.\ \texttt{divergences.md:19}: internal inconsistency in the
project's own divergence log. Entry 17 correctly states lean4lean does \emph{not} recheck the
constructor/recursor declarations restored after nested-inductive elimination; entry 19 asserts
the opposite. Reading \texttt{Environment.addInductive}
(\srcloc{Lean4Lean/Inductive/Add.lean}{733}) confirms entry 17: the restored declarations are
inserted with a bare \texttt{.add}, no further \texttt{checkType}/\texttt{isDefEq} call. Not a
blueprint issue, but confusing for the next reader of that file. (reviews/kernel.md)
\item \srcloc{Lean4Lean/PtrEq.lean}{17}: the two pointer-equality soundness axioms are genuine
trusted assumptions, honestly documented and used in only two places, but at
\srcloc{Lean4Lean/TypeChecker.lean}{739} \texttt{ptrEqConstantInfo} gates a different algorithm
rather than a shortcut. (kernel Review notes)
\item \srcloc{Lean4Lean/Verify/Environment.lean}{208}: \texttt{addDecl.WF}'s \texttt{inductDecl}
case is sorry, so everything either branch proves about inductive blocks lives on the model side
of that gap; master's hole, not a contributed one, but it bounds every claim built on it.
(kernel Review notes; see High severity above for the fuller framing)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive.lean}{73}: a documented-but-dead cluster
(\texttt{AddsConsts}, \texttt{constants\_stable}, \texttt{constants\_of\_mem},
\texttt{PrimitiveInductiveResult}, \texttt{checkInductive.WF}, \ldots, 123 of the file's 195
lines) waits on the same \texttt{addDecl.WF} case above; \texttt{AddsConsts} itself is
constructed nowhere. (primitives-core Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive.lean}{121}: \texttt{AddsConsts.hasPrimitives\_bool}
and \texttt{.hasPrimitives\_nat} are byte-for-byte the same proof script with the constant list
swapped. (primitives-core Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive/Basic.lean}{318}: namespace inconsistency
for \texttt{List} helpers --- some declared with \texttt{\_root\_.}, others declared bare inside
\texttt{namespace Lean4Lean} and so landing in the shadow \texttt{Lean4Lean.List}.
(primitives-core Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive/Recursion.lean}{587}:
\texttt{unfoldNatWellFounded.WF'} is a single 1135-line tactic proof requiring
\texttt{maxHeartbeats 1000000}, not practically reviewable at that size; its \texttt{BlockQ}
docstring is also stale (says two checks are recorded, the definition records four).
(primitives-core Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive/Recursion.lean}{376}: three adjacent lines
spell the same environment coercion three different ways after the iota merge.
(primitives-core Review notes)
\item \srcloc{Lean4Lean/Verify/Primitive.lean}{458}: small pre-existing interface asymmetries ---
\texttt{ReflectsNatNat'.of\_pred\_equations} hard-codes \texttt{Nat.pred} instead of taking it as
a parameter, unlike its six siblings; \texttt{VExpr.liftN\_lams} returns only an existential
where \texttt{liftN\_lams'} computes the lifted domains. (primitives-core Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{26}: stale module docstring
--- says \texttt{Nat.bitwise}/\texttt{unfoldNatWellFounded}'s \texttt{Condition.check} calls
``currently sit under binders'' when the hoisting it describes as future work
(\srcloc{Lean4Lean/Primitive.lean}{409}, \texttt{372}) has already happened, which is why
\texttt{Bitwise.lean}/\texttt{Gcd.lean} can pass \texttt{rfl} for \texttt{hnil}.
(primitives-arith Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{1448}: inconsistent
spelling of the same coercion within one proof (\texttt{c.Ewf.orderedStrong} vs.\ bare
\texttt{c.Ewf} relying on \texttt{CoeOut}, at 1448--1451 and 1850--1851). (primitives-arith
Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive/Bitwise.lean}{41}: the local abbreviation
\texttt{hE := ctx.Ewf.orderedStrong} carries the wrong strength for 7 of its 12 uses, which
immediately downgrade it with \texttt{hE.ordered}; \texttt{Gcd.lean} made the same edit without
needing any downgrades. (primitives-arith Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive/Bitwise.lean}{31}: \texttt{checkNatBitwise.WF}
has no docstring, unlike every other clause-level \texttt{WF} theorem in the group, and is the
longest (375 lines) and most intricate declaration in the chapter. (primitives-arith Review
notes)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive/Clauses.lean}{225}: \texttt{checkNatLAnd.WF},
\texttt{checkNatLOr.WF} and \texttt{checkNatXor.WF} are near-identical 25--30-line proofs;
\texttt{checkNatBoolCases.WF} nearby shows the parametrised alternative. (primitives-arith
Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{2438}:
\texttt{Condition.fvarsIn\_ite} is dead code; its sibling \texttt{fvarsIn\_dite} is used once.
(primitives-arith Review notes)
\item \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{713}: \texttt{TrExprS.bvar0}
through \texttt{bvar3} are the only declarations in the file escaped with \texttt{\_root\_} to
\texttt{Lean4Lean.TrExprS}, easily confused with the generic \texttt{TrExprS} API.
(primitives-arith Review notes)
\item \srcloc{Lean4Lean/Verify/TypeChecker/IsDefEq.lean}{211}: a commented-out \texttt{have} is
left inside \texttt{tryEtaExpansionCore.WF}'s proof. (typechecker Review notes)
\item \srcloc{Lean4Lean/Verify/TypeChecker/Reduce.lean}{21}: \texttt{reduceBinNatOpG}, an
executable definition, is introduced inside a verification file as a generalisation of the
kernel's own \texttt{reduceBinNatOp}, duplicating kernel code in a proof file.
(typechecker Review notes)
\item \srcloc{Lean4Lean/Tests/Level.lean}{8}: states that canonicity of \texttt{normalize'} and
completeness of \texttt{isEquiv'}/\texttt{geq'} are \emph{not} proved; all three now are
(\srcloc{Lean4Lean/Verify/Level.lean}{3849}, \texttt{3861}, \texttt{3870}). Stale doc/code
mismatch. (levels Review notes)
\item \srcloc{Lean4Lean/Verify/Level.lean}{41}: \texttt{mkData\_depth},
\texttt{mkData\_hasParam} and \texttt{mkData\_hasMVar} are referenced nowhere in the project and
are the only consumers of the \texttt{Lean.Level.mkData\_eq} axiom, needing
\texttt{allowUnsafeReducibility} to elaborate. (levels Review notes)
\item \srcloc{Lean4Lean/Verify/EquivManager.lean}{81}: \texttt{RelevantEq.uniq} and two dependent
theorems reach \texttt{sorryAx} through \texttt{TrProj.uniq}, because \texttt{RelevantEq}'s
\texttt{proj} case compares two projections by index alone, ignoring the structure name; this
sits on the main path of the verified type checker's memo cache
(\srcloc{Lean4Lean/Verify/EquivManager.lean}{325}), not in a corner. (levels Review notes)
\item \srcloc{Lean4Lean/Verify/LevelStd.lean}{155}: stale doc comment naming two lemmas
(\texttt{qsort\_perm\_toList}, \texttt{pairwise\_qsort\_normLt}) as unproved and nonexistent;
both facts are now proved under different names. (levels Review notes)
\item \srcloc{Lean4Lean/Verify/Level.lean}{3822}: \texttt{normalize'\_eval},
\texttt{normalize'\_complete}, \texttt{isEquiv'\_complete}, \texttt{geq'\_wf} and
\texttt{geq'\_complete} are used nowhere; the reconstruction layer supporting
\texttt{normalize'} (roughly lines 1290--2250) supports a function the kernel never calls.
(levels Review notes)
\item \srcloc{Lean4Lean/Verify/Level.lean}{16}: a commented-out \texttt{VLevel.toLevel}
definition and a \texttt{toLevel\_inj := sorry} are left in the file; the only occurrence of the
token \texttt{sorry} in this master-only group. (levels Review notes)
\item \srcloc{Lean4Lean/Verify/Level.lean}{1}: no module docstring on a 3880-line file; a reader
reaches line 166 before learning the file formalizes G\'eran's canonical form.
(levels Review notes)
\item \srcloc{Lean4Lean/Verify/EquivManager.lean}{41}: \texttt{RelevantEq.symm},
\texttt{.trans} and \texttt{M.WF.bind\_le} are never used anywhere. (levels Review notes)
\item \srcloc{Lean4Lean/Verify/NormLt.lean}{6}: the header overstates what is proved
(``a strict weak order'') against what is exported (asymmetry and negation-transitivity, exactly
what \texttt{Array.qsort\_sorted} needs). (levels Review notes)
\item \srcloc{Lean4Lean/Verify/QSort.lean}{34}: vendored code still carrying upstream TODOs
(``these attributes still need to be moved to the standard library''), commented-out attribute
experiments, and global \texttt{grind}-lemma registrations that every importer inherits.
(levels Review notes)
\item \srcloc{Lean4Lean/Verify/QSort.lean}{27}: no public theorem gives
\texttt{(qsort as lt lo hi)[i] = as[i]} outside \texttt{[lo,hi]}; the private lemmas exist but
are not exported. Latent limitation, not a defect for the current consumer. (levels Review
notes)
\item \srcloc{Lean4Lean/Verify/Level.lean}{1222}: end-to-end theorems each thread five to seven
separate side conditions about \texttt{normalize u} by hand rather than through one bundled
predicate. (levels Review notes)
\item \srcloc{Lean4Lean/Verify/Level.lean}{3177}: \texttt{Std.TreeMap} as the representation
costs a whole \texttt{toList}-factoring layer ($\sim$150 lines); a sorted-association-list
representation would have avoided it. (levels Review notes)
\item \srcloc{Lean4Lean/Verify/NormLt.lean}{97}: \texttt{baseCmp\_swap} and
\texttt{normLtAux\_eq} close several goals with bare \texttt{grind}/\texttt{simp\_all}, not
independently checkable by reading; \texttt{QSort.lean} is \texttt{grind}-first throughout.
(levels Review notes)
\item \srcloc{Lean4Lean/Verify/NormLt.lean}{47}: \texttt{baseCmp} duplicates its \texttt{max}
and \texttt{imax} arms verbatim; \texttt{getUndefParam\_none}
(\srcloc{Lean4Lean/Verify/Level.lean}{101}) is dense and hard to follow.
(levels Review notes)
\item \srcloc{Lean4Lean/Verify/EquivManager.lean}{313}: \texttt{addEquiv.WF} and
\texttt{isDefEq.WF} live in \texttt{Lean4Lean.TypeChecker.Inner} rather than
\texttt{EquivManager}; defensible but surprising. (levels Review notes)
\item \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{53}: \texttt{Shape} is a \texttt{def} by
recursion on \texttt{Nat} rather than an inductive family, so essentially every order/lift/join/
typing lemma is stated three times (for \texttt{Shape}, \texttt{WShape}, \texttt{TShape}); the
first $\sim$2500 lines are this boilerplate. (experimental-logrel Review notes)
\item \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{3333}: 13 docstrings in 6100 lines, none
on the pivotal definitions (\texttt{Shape.WF}, \texttt{LE\_Interp}, \texttt{LR}, \ldots); two sit
on self-evident lemmas instead. (experimental-logrel Review notes)
\item \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{3936}: proof-size hygiene --- several
single-tactic-block proofs of 100--330 lines with no internal comments, essentially unreviewable
by anyone but the author. (experimental-logrel Review notes)
\item \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{820}: \texttt{Shape.trim} is defined and
never used. (experimental-logrel Review notes)
\item \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{2716}: \texttt{find\_cycle}, a reusable
pigeonhole lemma, is declared \texttt{private} in the middle of a shape file; belongs in
\texttt{Lean4Lean/Std} or upstream. (experimental-logrel Review notes)
\item \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{6100}: the file ends after
\texttt{LR.SubstWF.symm} without closing either open namespace and with no pointer to
\texttt{ShapeLogRelAdequacy.lean}, where the development continues. (experimental-logrel Review
notes)
\item \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{1887}: \texttt{TShape.type} has no
\texttt{TShape.prop} counterpart, and the head-discrimination grid omits two of its fourteen
pairs with no comment distinguishing omission from oversight. (experimental-logrel Review notes)
\item \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{4623}: \texttt{StrongSoundCore.const}
takes a bundle for every classification of a constant, though a constant has exactly one;
whether the generality is ever exercised is unchecked. (experimental-logrel Review notes)
\item \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{1392}: a \texttt{variable}/\texttt{include}
idiom threads induction hypotheses invisibly through a 165-line namespace, making several lemmas
look like standalone results with undocumented hypotheses. (experimental-logrel Review notes)
\item \srcloc{Lean4Lean/Experimental/LogRel.lean}{157}: \texttt{LRIsType.irrel'} closes with
\texttt{grind}, brittle across toolchain bumps (in dead code, but the same reliance appears in
live modules). (experimental-logrel Review notes)
\item \srcloc{Lean4Lean/Experimental/NormalEq.lean}{97}: \texttt{Typing.pat\_env} has no
docstring, unlike the field it mirrors in \texttt{ChurchRosser.lean}; the \texttt{Typing}
structure it belongs to is never instantiated anywhere. (experimental-reduction Review notes)
\item \srcloc{Lean4Lean/Experimental/MoreStepIndexed.lean}{63}: the \texttt{Shape}/\texttt{ShapeFun}
approximation lattice exists in three near-identical copies (here, \texttt{Thierry2.lean},
\texttt{ShapeLogRel.lean}), each with its own partly admitted order laws. (experimental-reduction
Review notes)
\item \srcloc{Lean4Lean/Experimental/StepIndexed.lean}{59}: \texttt{IsTy}, \texttt{IsTyN} and
\texttt{IsTy.def} are axioms positing the fixpoint the file sets out to construct;
\texttt{IsTyN} is unused and $\sim$40\% of the file is commented out. (experimental-reduction
Review notes)
\item \srcloc{Lean4Lean/Experimental/NormalEq.lean}{145}: several declarations here carry fully
qualified names that already exist in \texttt{ChurchRosser.lean}
(\texttt{Pattern.Matches.hasType}, \texttt{Check.OK.weakN}); any name-indexed tool will conflate
the sorry-free copy here with the tainted one there. (experimental-reduction Review notes)
\item \srcloc{Lean4Lean/Experimental/Stratified.lean}{160}: two thirds of this file and
\texttt{StratifiedUntyped.lean} are commented-out abandoned attempts containing further sorries,
making the last live declaration of each look admitted to any line-range-based analysis.
(experimental-reduction Review notes)
\item \srcloc{Lean4Lean/Experimental/ParallelReduction.lean}{699}: two pre-existing master
sorries in \texttt{NormalEq.parRed} make the file's Church-Rosser corollaries conditional; the
$\iota$ case the branch added extends an already-unproved theorem. (experimental-reduction
Review notes)
\end{itemize}
```

### Section "Blueprint limitations"

```latex
\section{Blueprint limitations}
\label{status:sec:limits}

What this blueprint does not check, stated plainly so its claims are not over-read:

\begin{itemize}
\item \textbf{One build snapshot.} \texttt{decls.tsv}/\texttt{all-constants.tsv} come from a
single compiled tree (2026-09-10, HEAD \texttt{20ec229}); nothing was rebuilt for this pass
(\texttt{CONVENTIONS.md} forbids \texttt{lake build}). A later commit on \texttt{trproj} is not
reflected anywhere in this blueprint until the census is regenerated.
\item \textbf{\texttt{Experimental/} is only partially censused.} Its five mutually-exclusive
draft modules cannot be imported together, so the census ran one pass per module and merged;
cross-module interactions (e.g.\ the three duplicate \texttt{LogRel} declarations of
\S\ref{status:sec:issues}) are visible only because a reviewer read the source, not because any
one build surfaces them.
\item \textbf{Reach counts are exact only where cited to a source.} The five reach numbers in
\S\ref{status:sec:sorries} (343/138/92/61/0) come from \texttt{sorry-grep.md}'s own dependency
walk; reach for the eleven master sorries is described qualitatively (which named lemmas and
families become conditional), not as an exhaustively enumerated transitive closure, because no
committed tool computes that closure for arbitrary declarations.
\item \textbf{Blame attribution is a line-majority heuristic, not a commit-history fact.} A
declaration whose range mixes tags is \texttt{mixed}; a declaration whose file has no blame
entry is assumed byte-identical to master. This mis-attributes at least one file outright
(\srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{1}, tagged entirely trproj by line count while
being, by commit content, iota's --- \S\ref{status:sec:issues}), and 16 lines elsewhere are
known-relocated master code counted as contributed (\S\ref{status:sec:issues}, trenv).
\item \textbf{\texttt{sorry}-detection is textual.} \texttt{sorry-grep.md} and this chapter's own
re-verification find literal \texttt{sorry} tokens by regex; the \texttt{stop} tactic
(\texttt{repeat sorry}) and axioms that assert a fixpoint's existence achieve the same effect
without the token, and are caught in this chapter only where a chapter's own review notes
happened to name them (\S\ref{status:sec:issues}, experimental-logrel/-reduction). An
exhaustive audit for every such disguised gap was not performed.
\item \textbf{No claim here was checked by building.} Every axiom profile and
\texttt{\#print axioms} figure quoted in \S\ref{status:sec:trust}--\ref{status:sec:issues} was
either read from a committed \texttt{\#guard\_msgs} pin or, per \texttt{claims-iota.md}/
\texttt{claims-trproj.md}'s own methodology, obtained via \texttt{lake env lean} on individual
files, never a full \texttt{lake build}; PARTIAL verdicts in those two files exist specifically
because the full build was out of scope.
\item \textbf{The claims audit is not exhaustively reproduced here.} \texttt{claims-iota.md} and
\texttt{claims-trproj.md} between them adjudicate 110 claims (60 iota, 50 trproj) from the
branches' own PR descriptions; \S\ref{status:sec:issues} reproduces only the handful whose
FALSE/PARTIAL verdict
corresponds to a concrete code- or documentation-level issue distinct from what the module
chapters already record, not the full claim-by-claim ledger.
\item \textbf{Severity and branch labels are inherited, not re-derived.} Where a chapter's Review
notes or a \texttt{reviews/*.md} file calls something High/Medium/Low or attributes it to a
branch, this chapter keeps that judgement; it does not independently re-score severity.
\item \textbf{This chapter is not a duplicate of Chapters \ref{chap:contrib-iota}/
\ref{chap:contrib-trproj}.} Those chapters argue the overall quality case for each branch in
narrative form; this chapter is the flat, deduplicated ledger behind both of them plus every
master-only and \texttt{Experimental} issue neither branch chapter is scoped to cover.
\end{itemize}
```


# Remark environments as they stood before the refurbishment

## metatheory.tex (1 remarks)
- Notation used throughout. $\Gamma \vdash e_1 \equiv e_2 : A$ is \texttt{VEnv.IsDefEq}, $\Gamma \vdash e : A$ is \texttt{VEnv.HasType} (the diagonal of the former), and $\Gamma \vdash e_1 \equiv e_2$ is the untyped \texttt{VEnv.IsDefEqU}. The strong (fully annotated) judgments are written $\Gamma \Vdash e_1 \equiv e_2 : A$ (\texttt{IsDefEqStrong}) and $\Gamma \Vdash e : A$ / $\Gamma \Vdash e :!\, A$ (\texttt{HasTypeStrong}, with and without the conversion rule); $\Gamma \vdash_n e : A$ is the stratified judgment. The reduction relations are $\equiv_p$ (normal equality), $\gg$ (parallel reduction), $\ggg$ (complete parallel reduction), $\gg^*$ (its iteration), $\gg\ll$ (Church--Rosser equality), $\rightsquigarrow$ and $\rightsquigarrow^*$ (weak head reduction), $\rightsquigarrow_<$ (standard reduction), $\triangleright$ and $\triangleright^*$ (type inference). All of them live under a fixed environment and universe count taken from the class \texttt{Params} (Definition~\ref{class:cr-params}) in the last two files.

## trexpr.tex (11 remarks)
- These three lemmas fill a real gap in master's spine API, which had only the \texttt{mkAppList\_getAppArgsList} direction. Only one of the three has an external consumer: \texttt{getAppArgsList\_mkAppList} is rewritten with at \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{50} in the projection and $\iota$ reduction proof. \texttt{getAppFn\_mkAppList} is \texttt{@[simp]} and has no explicit call site, but it fires inside the \texttt{simp} at \texttt{WHNF.lean:52}, where the argument list is not a literal. \texttt{getAppArgsRevList\_mkAppList} has no consumer at all outside \srcloc{Lean4Lean/Verify/Expr.lean}{749}, where it serves only to prove the forward form.
- The design point is real and is stated in the source: dropping the freshness side condition is what makes a chain of six \texttt{mkLocalDecl} steps resolvable without discharging six freshness obligations. Four of the seven declarations (\texttt{empty\_map\_wf}, \texttt{map\_wf\_mkLocalDecl}, \texttt{find?\_mkLocalDecl}, \texttt{find?\_empty}) are used, heavily, in \srcloc{Lean4Lean/Verify/Environment/Quot.lean}{1}, where the \texttt{Quot} axiom shapes are built by hand, and the \texttt{DecidableEq FVarId} instance is what makes the \texttt{if x = fv} of \texttt{find?\_mkLocalDecl} reducible there; \texttt{WF.empty} and \texttt{toList\_empty} serve only \texttt{find?\_empty} inside the block itself.
- Three points about the interface. (1) The \texttt{pat} field asserts only that \emph{some} reduct is registered under that key: the reduct itself is not pinned, so \texttt{TrProjCtor} alone does not determine reduction behaviour, and the key, being a sum, does not by itself exclude reading a two-minor recursor as \texttt{(np+1)+1+1+0}. The docstring says so and defers to \texttt{TrEnv.proj\_defeq} (Theorem \ref{thm:tr-env-proj-defeq}) for the kernel-side facts. (2) \texttt{uss} is a total function \texttt{Nat} to \texttt{List VLevel}, so the relation quantifies over a whole level assignment of which only the first \texttt{i+1} values matter; this is what makes \texttt{TrProj.uniq} hard. (3) The scope paragraph, which restricts the relation to single constructor, non-recursive, non-indexed, non-mutual structures and declares reflexive, indexed and nested structures a completeness rather than a soundness boundary, makes precise claims about the kernel's \texttt{inferProj} that are prose only; nothing in the repository formalizes them. Documentation density is otherwise unusually high, with a per-field docstring naming the kernel fact each field stands in for.
- Two of the six existentials are pinned by other fields: \texttt{np} is \texttt{params.length} by \texttt{params\_length}, and \texttt{fieldTys} is determined by \texttt{ctorName}, \texttt{usS} and \texttt{params} by \texttt{ctor}. Replacing them by definitions would shrink the relation and remove an obligation from each of the three proofs that rebuild the record (\texttt{weak'}, \texttt{instN}, \texttt{instL}), where they reappear as \texttt{params\_length := by simpa} and \texttt{field\_lt := by rw [hlen]}; \texttt{defeqDFC} and \texttt{mono}, which reuse the old record with \texttt{\{H with \ldots\}}, pay nothing.
- Master's inductive; the \texttt{trproj} branch changed the \texttt{proj} rule's premise from \texttt{TrProj $\Delta$.toCtx s i e' e''} to \texttt{TrProj env Us.length $\Delta$.toCtx s i e' e''}. The change is forced by \texttt{TrProj} now carrying typing premises, and it means that in the projection case \texttt{TrExprS} is no longer environment-independent, which is what creates the obligation \texttt{TrProj.mono}.
- The sketch does not say how the per-field level list \texttt{uss} is pinned. Two \texttt{TrProjCtor} witnesses for the same projection may in principle choose different \texttt{uss}, in which case the two expansions are syntactically different recursor applications at different universe instances, and a definitional equality between them is not obviously available. Either the sketch is incomplete or \texttt{TrProjCtor} needs a further field tying \texttt{uss i} to the sort of the field type \texttt{F}$_i$.
- The \texttt{proj} clause being \texttt{False} is where the absence of a projection node in \texttt{VExpr} becomes visible: a projection has no canonical target, only a definitional-equality class. The \texttt{trproj} work does not change this and arguably could not, since \texttt{TrProjCtor} leaves the per-field level list \texttt{uss} free (Definition \ref{struct:trprojctor}).
- It is used five times in the projection and $\iota$ WHNF proof, \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{87} to \texttt{:93}. It partly duplicates \texttt{AppStack.build} (Definition \ref{ind:appstack}), which sits immediately above it at \srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{2344} and gives the same decomposition in a different shape; the pointwise-list form is the one the WHNF proof needs, so the duplication is defensible, but it leaves two spine-inversion idioms side by side.
- The docstrings explain carefully why the typing clause cannot be dropped: a \texttt{Nat} primitive is consumed as an \emph{operator} inside another primitive's recurrence, and congruence under an application needs the codomain to be known non-dependent, which inverting an application does not give. For \texttt{ReflectsBoolBoolBool'} there is a second reason, spelled out in the source: a term of type \texttt{(x : Bool)} to \texttt{(if x then Bool else Bool)} satisfies the evaluation clause but is not a \texttt{boolOp2}. This is good documentation of a non-obvious design choice.
- Eight signature lines here were changed on the \texttt{iota} branch from \texttt{env.Ordered} to \texttt{env.OrderedStrong} (\srcloc{Lean4Lean/Verify/Typing/Lemmas.lean}{1856} onwards), together with two call sites where \texttt{wf.constWF} became \texttt{wf.ordered.constWF}. The change is forced by \texttt{HasType.const\_inv} alone (\srcloc{Lean4Lean/Theory/Typing/Strong.lean}{915}), whose own hypothesis moved because the strengthening lemma it invokes, \texttt{IsDefEq.strong} (\srcloc{Lean4Lean/Theory/Typing/Strong.lean}{805}), now needs subject reduction of the registered $\iota$ rules. The other inversion used here, \texttt{HasType.forallE\_inv} (\srcloc{Lean4Lean/Theory/Typing/Lemmas.lean}{854}), still takes only \texttt{Ordered} and is simply fed the stronger hypothesis. The edit is mechanical, but it means every \emph{use} of these lemmas (\srcloc{Lean4Lean/Verify/TypeChecker/Reduce.lean}{16}, \srcloc{Lean4Lean/Verify/TypeChecker/IsDefEq.lean}{406}, \srcloc{Lean4Lean/Verify/TypeChecker/InferType.lean}{420}) now discharges \texttt{OrderedStrong} through \texttt{VEnv.WF.orderedStrong}, which rests on the admitted \texttt{VEnv.WF.patsStrong} (\srcloc{Lean4Lean/Theory/Typing/EnvLemmas.lean}{334}). A hypothesis strengthening in this group therefore imports a new admission into the checker's literal handling.
- The hypothesis of both members was changed on \texttt{iota} from \texttt{env.Ordered} to \texttt{env.OrderedStrong}, forced by the new signature of \texttt{HasType.const\_inv} (\srcloc{Lean4Lean/Theory/Typing/Strong.lean}{915}); the proof terms are otherwise identical to master's. These two lines are the whole of the \texttt{iota} branch's footprint in \srcloc{Lean4Lean/Verify/Typing/TrTerm.lean}{1}.

## trenv.tex (10 remarks)
- These four lemmas are marked as contributed by the per-line blame, but they are verbatim master code relocated from \texttt{Lemmas.lean} into \texttt{Basic.lean} by the \texttt{iota} refactor commit \texttt{3046dff}. The attribution is ``moved'', not ``written''.
- The core of \texttt{TrIndType} (the fields \texttt{tr}, \texttt{ctor\_names}, \texttt{ctors}) is \texttt{iota}; the parameters $nparams$ and $block$ and the fields \texttt{all}, \texttt{numParams}, \texttt{numIndices} are \texttt{trproj} additions. The arity equation $cval.\mathtt{numParams} + cval.\mathtt{numFields} = c.\mathtt{type}.\mathtt{piArity}$ is the second conjunct of the \texttt{ctors} field and so is \texttt{iota} as well, not a \texttt{trproj} addition; it is the bridge that makes \ref{thm:add-induct-ctor-find} and \ref{thm:tr-env-ctor-arity} usable. Note that the witness mentions three different environments: type formers translate in $env_1$, constructors in $env_T$, and (in \ref{struct:tr-recursor}) reducts in $env_R$. That is correct, but demanding on a producer.
- On master this was a deliberately empty \texttt{Prop} inductive whose docstring called it ``essentially a \texttt{sorry}'': it had no constructors, so the \texttt{induct} step of $\mathtt{TrEnv}'$ could never fire and environments containing inductives were outside the verified relation. Replacing it is the single largest structural change of the \texttt{iota} branch. Two consequences deserve review. First, \texttt{AddInduct} is declared without a \texttt{: Prop} ascription, so it is \texttt{Type}-valued and the \texttt{induct} constructor of $\mathtt{TrEnv}'$ now carries data. This is needed because the derived lemmas project its fields (\texttt{ivals}, \texttt{envR}, \texttt{order}), which a \texttt{Prop}-valued structure would not allow. The often-stated consequence ``$\mathtt{TrEnv}'$ loses large elimination'' would be wrong: $\mathtt{TrEnv}'$ has nine constructors, so it never had large elimination. What is true is that an \texttt{AddInduct} witness cannot be recovered from a $\mathtt{TrEnv}'$ proof except into \texttt{Prop}, which is all the present consumers need; the change to the shape of the project's central invariant relative to master's \texttt{inductive AddInduct \ldots : Prop} is nowhere documented. Second, nothing in the repository ever constructs an \texttt{AddInduct}, so every result below is conditional on a witness that \ref{thm:add-decl-wf} still \texttt{sorry}s.
- The chapter's source history shows this lemma, and the arity conjunct of \texttt{TrIndType.ctors} it rests on, entering on \texttt{iota} in the commit \texttt{d69ac5d} ``derive \texttt{AddInduct}'s $\iota$ bookkeeping instead of assuming it'', not on \texttt{trproj}; per-line blame agrees. It is the only place the arity conjunct of \texttt{TrIndType} earns its keep, and its only consumer is \ref{thm:tr-env-structure-rec}, that is, the projection work: the $\iota$ pipeline itself never calls it.
- This is a master relation; the \texttt{iota} branch changed exactly one line, the \texttt{AddInduct} argument of the \texttt{induct} constructor (\srcloc{Lean4Lean/Verify/Environment/Basic.lean}{584}), which now carries $safety$. Since \texttt{AddInduct} is \texttt{Type}-valued, that constructor is the one place where $\mathtt{TrEnv}'$, itself still a \texttt{Prop}, quantifies over data that no consumer can read back out.
- The \texttt{block} constructor is the crux. A nested mutual block is inserted type by type by the kernel, but the types of the block's recursors mention every type former and constructor of the block, so it cannot be aligned one constant at a time. The constructor's docstring says exactly that. \texttt{pat} is a one-line addition mirroring the new \texttt{VEnv.addPat}.
- Both branches contributed here, but not equally: \texttt{AddQuot1.pull} and \texttt{AddQuot.pull} were introduced with the $\iota$ work and then generalised on \texttt{trproj}, which also added \texttt{pull\_insert} for \ref{thm:tr-env-structure-rec}; per-line blame is 18 lines \texttt{trproj} to 6 \texttt{iota}. The family is needed because \ref{thm:tr-env-pats-iota} and \ref{thm:tr-env-structure-rec} induct over $\mathtt{TrEnv}'$ and must survive the \texttt{quot} step.
- This is the hardest theorem of the \texttt{trproj} branch in this group and the reason \ref{thm:add-induct-rec-reg} exists. The statement is the right one: \ref{thm:tr-env-proj-defeq} needs to know that a pattern it found through the \texttt{pat} field of \texttt{TrProjCtor} really is the recursor's rule.
- This is the single point where the $\iota$ work of this group is consumed by the kernel model: \texttt{inductiveReduceRecCore.WF} (declared at \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{17}, calling \ref{thm:tr-env-iota-rec} at \srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{119}). That theorem has no \texttt{sorry} of its own, though it inherits \texttt{sorryAx} through the strong system. The enclosing \texttt{reduceRecursor.WF} (\srcloc{Lean4Lean/Verify/TypeChecker/WHNF.lean}{147}, \texttt{sorry} at line 149) is not proved, so the chain to \texttt{whnf} is not closed.
- This replaces master's \texttt{checkEqType.WF}, which proved \texttt{False}: on master no \texttt{TrEnv} could contain the inductive \texttt{Eq}, because \texttt{AddInduct} had no constructors, so quotient initialization was vacuously well-formed in the interesting branch. Making \texttt{AddInduct} inhabitable forced this file into existence, and it is the clearest example of the \texttt{iota} contribution paying for itself.

## primitives-core.tex (54 remarks)
- Notation. $\Gamma \vdash e : A$ is \texttt{VEnv.HasType}, $\Gamma \vdash e \equiv e'$ is the type-erased \texttt{VEnv.IsDefEqU} (the typed form carries its type explicitly), and $\overline{k}$ is the model numeral \texttt{VExpr.natLit k}, that is $k$ applications of \texttt{Nat.succ} to \texttt{Nat.zero}. All judgements are relative to a universe-parameter count $U$, suppressed when it is $0$. Throughout, \texttt{HasPrimitives} is the invariant recording, for each reserved name, what the model assumes about it; it is a fact about the \emph{empty} context, which is why so much of this chapter is about weakening it to a context of interest and back.
- The \texttt{iota} branch changed \texttt{henv : env.Ordered} to \texttt{henv : env.OrderedStrong} in all seven. None of them needs it: their bodies invoke only \texttt{HasType.weak0} (\srcloc{Lean4Lean/Theory/Typing/Lemmas.lean}{610}) and \texttt{IsDefEq.isType} (\srcloc{Lean4Lean/Theory/Typing/Lemmas.lean}{945}), both of which still take \texttt{Ordered}. Because \texttt{OrderedStrong} is here a \emph{hypothesis} rather than something derived, these seven statements are still free of \texttt{sorryAx}; the cost is paid by every caller that has only \texttt{VEnv.WF} and must go through \texttt{VEnv.WF.orderedStrong}.
- All seven genuinely need \texttt{OrderedStrong}: \texttt{contains\_nat\_of\_hasType} and \texttt{boolOfBitwise} directly, through \texttt{HasType.const\_inv} (\srcloc{Lean4Lean/Theory/Typing/Strong.lean}{915}), which moved to \texttt{OrderedStrong} on the \texttt{iota} branch, and the five \texttt{natOf*} wrappers through \texttt{contains\_nat\_of\_hasType}. The one non-signature edit in the file, \texttt{henv.constWF} becoming \texttt{henv.ordered.constWF} at \srcloc{Lean4Lean/Verify/Primitive.lean}{80}, is faithful.
- \texttt{iota} strengthened the hypothesis to \texttt{OrderedStrong}; the body uses only \texttt{natLitT} and \texttt{isType}, so \texttt{Ordered} would still suffice were \texttt{natLitT} not itself over-strengthened.
- These two are the genuine reason the file needs \texttt{OrderedStrong}, and every node above them in this chapter inherits it from here.
- Only \texttt{appChar\_inv'} was touched by \texttt{iota}, and only in its \texttt{henv} hypothesis; its body uses \texttt{weak0}, which still takes \texttt{Ordered}, so this is another gratuitous strengthening.
- \texttt{IsDefEqU.forallE\_inv} lives in \srcloc{Lean4Lean/Theory/Typing/Injectivity.lean}{23} and is \texttt{sorry}-backed on both branches, so this branch of the primitive verification was never unconditional.
- \texttt{IsDefEqU.of\_l} goes through \texttt{IsDefEq.uniq} (\srcloc{Lean4Lean/Theory/Typing/UniqueTyping.lean}{13}), which is backed by the \texttt{sorry}s of \texttt{Injectivity.lean}. Every node below that chains two definitional equalities therefore carried \texttt{sorryAx} already on \texttt{master}.
- The two instantiation hypotheses are equalities of \texttt{VExpr}s rather than definitional equalities. That is a slightly awkward interface, but it is exactly what the branch proofs can produce syntactically, so the choice is defensible.
- \texttt{of\_closed\_cases} is a trivial repackaging and is arguably not worth a lemma, but it keeps the branch proofs uniform.
- The conclusion hard-codes the meta-level function \texttt{Nat.pred} instead of taking it as a parameter, unlike its siblings. Harmless, but asymmetric.
- This is where every primitive's specification is actually established, so it is the point at which the \texttt{OrderedStrong} hypothesis introduced on \texttt{iota} reaches the top-level primitive guarantee.
- The reservedness hypothesis is an auto-parameter discharged by \texttt{simp}, so callers never write it and the lemma's cost is invisible at the call sites.
- \texttt{natBinLitBool} inlines the same proof rather than reusing an \texttt{applyLit} analogue for the \texttt{Bool}-valued case; a small asymmetry.
- \texttt{iota} edited four lines here, all \texttt{c.Ewf.ordered} becoming \texttt{c.Ewf.orderedStrong}. The adaptation is forced by \texttt{trNat}/\texttt{trBool} and is faithful.
- \texttt{liftN\_lams} only produces an \emph{existential} for the lifted domains rather than computing them; the docstring justifies this by observing that nothing later looks at them, only at how many there are. The computed form is available as \texttt{liftN\_lams'}.
- The namespaces are inconsistent: \texttt{map\_right'} and \texttt{forall\_left} are declared at \texttt{\_root\_.List}, while the other six are written as \texttt{List.\dots} inside \texttt{namespace Lean4Lean} and therefore land in \texttt{Lean4Lean.List}, shadowing the real \texttt{List} namespace inside the project.
- Both signatures were strengthened to \texttt{OrderedStrong} by \texttt{iota}; neither needs more than its \texttt{VLCtx} original does, and those are themselves over-strengthened. Neither is confined to one branch: \texttt{natIsType'} is used at \srcloc{Lean4Lean/Verify/Environment/Primitive/Recursion.lean}{376}, at nine places in \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{762} and twice in \srcloc{Lean4Lean/Verify/Environment/Primitive/DivMod.lean}{102}, and \texttt{boolIsType'} at \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{1043} and 1131.
- The \texttt{trproj} blame here is misleading: that commit only re-wrapped the signature across three lines (431--433) to keep it under 100 columns after the \texttt{iota} edit. Its only other lines in this chapter are the two call sites it re-flowed inside \ref{vpc:thm:wf-appn-inv} (455--456). There is no projection content in either place.
- \texttt{iota} changed the \texttt{variable!} hypothesis and two call sites; both are genuine, since these go through \texttt{app\_inv}, which moved to \texttt{OrderedStrong}. The two lines the \texttt{trproj} commit re-wrapped are the call sites.
- \texttt{iota} touched four lines here. \texttt{lam\_inv'}'s hypothesis moved to \texttt{OrderedStrong}, which is genuine; the other two take \texttt{env.WF} and simply call \texttt{.orderedStrong} where they used to call \texttt{.ordered}.
- This is the key that lets an equation the checker verified \emph{under} a telescope be closed off at ground arguments, which is why the recogniser's open probes reach the closed reflection statements at all.
- The \texttt{iota} signature change is needed here (\texttt{app\_inv}). Its only use among this chapter's four files, at \srcloc{Lean4Lean/Verify/Environment/Primitive/Recursion.lean}{380}, is what forced that file's one contributed line; it is used nine more times in \srcloc{Lean4Lean/Verify/Environment/Primitive/Condition.lean}{1466}, which belongs to Chapter~\ref{chap:primitives-arith}.
- The \texttt{iota} signature change is needed here, \texttt{lam\_inv} having moved to \texttt{OrderedStrong}.
- Five \texttt{iota}-touched lines, all genuine: they feed \texttt{lam\_inv}, \texttt{app\_inv} and \texttt{IsDefEq.subst}. Together with \texttt{lambdaTelescope.WF} this is one of the two load-bearing theorems of the file.
- A good design decision, explained by its docstring. \texttt{Ext.cast} takes its environment equation as an auto-parameter defaulting to \texttt{rfl}, which makes context changes invisible at call sites.
- The hypotheses about $A$ and $B$ are quantified over \emph{any} translation of them, which the docstring justifies (nested applications then compose without a uniqueness side condition). That is the right choice, but it makes the statement heavier than it looks. The single \texttt{iota}-touched line is \srcloc{Lean4Lean/Verify/Environment/Primitive/Basic.lean}{774}, where \texttt{app\_inv₂} is now fed \texttt{E.wf.orderedStrong}.
- The docstring explains the deliberate choice of \texttt{mkLambda'} over \texttt{VExpr.lams}: the two agree only when every binder is a \texttt{vlam}, which is true of \texttt{lambdaTelescope} but should not be assumed silently. Good discipline.
- This is a \emph{hypothesis} of the well-founded-recursion theorems, not a check the recogniser performs: the docstring argues that it holds by \texttt{rfl} at the call sites because the caller wrote the measure. The verified statement is therefore conditional on a property of the caller's measure that the kernel never tests. The checker's behaviour is unchanged, so this is a specification-scope note and not a soundness bug.
- Central plumbing, and heavy: the continuation hypothesis takes eleven arguments. The file's own docstring concedes that threading them one at a time is unreadable, which is why \texttt{Inv} exists.
- The design goal recorded in the docstring is that each branch becomes a standalone theorem taking \texttt{Data} instead of the enclosing context; that is realised in \srcloc{Lean4Lean/Verify/Environment/Primitive/Clauses.lean}{1} and is a genuine modularisation.
- Thirteen \texttt{iota}-touched lines here (1074--1124), all \texttt{c.Ewf.ordered} becoming \texttt{c.Ewf.orderedStrong}, all forced by the new signatures of \texttt{trNat}, \texttt{trBool}, \texttt{natIsType}, \texttt{boolIsType} and \texttt{TrTerm.ofConst}. Of the nineteen atoms, only \texttt{zerob}, \texttt{succb}, \texttt{oneb}, \texttt{twob} and \texttt{boolb} came through the edit still free of \texttt{sorryAx}; the other fourteen acquired one. The docstring records that routing the enclosing theorem's branches through these atoms costs about 40 seconds of elaboration, so that theorem keeps duplicate local copies; an acknowledged duplication that is to disappear once the branches are extracted.
- The quantification over extensions is the right shape: primitive semantics are claimed only in well-formed extensions of the environment recognition ran in, which is what keeps the recogniser's syntactic implementation out of the rest of the metatheory.
- Three near-identical proof scripts, \texttt{mkResult}, \texttt{mkResult1} and \texttt{mkResultBool}, differing only in the specification constructor and the pinned type; \texttt{mkResultTypeEq} is a different and shorter proof. A reviewer might ask for one polymorphic lemma for the first three, but the \texttt{PrimSpec} constructors have different arities, so the duplication is defensible.
- This is the branch whose higher-order specification forced \texttt{VContext.Ext} to exist at all.
- The docstring says the type is spelled out at each use rather than named, because naming it makes the peeling \texttt{simp}s unfold it. It is in fact named, as \texttt{natGoType}, but as an \texttt{abbrev}, hence reducible, which is the same thing for \texttt{simp}; the performance-driven point stands, the wording does not.
- Four \texttt{iota}-touched lines, all forced by \texttt{app\_inv}.
- A well-chosen abstraction: \texttt{Nat.div} and \texttt{Nat.mod} differ only in what the step does to the recursive call and in what the recursion returns when it stops, so both branches are this one lemma. Ten hypotheses is a lot, but each is motivated in the docstring.
- The docstrings are unusually candid about what the recogniser does \emph{not} check (nothing here relates $\mathit{Aty}$ to the packer), and push that obligation to the caller through \texttt{applied}. The honesty is right, but it means the bundle's interface is wider than it looks.
- The docstring justifies abbreviations over extra parameters (one bundle instead of a handful of expressions that have to be kept in step) and notes that the recursion arguments are already closed, being literals, so they are not closed by $\gamma$.
- The restriction to smaller measures is what stops the hypothesis from being vacuous, and is also all that the fuel induction can supply: a \texttt{go} at fuel $t$ is stuck below $t$.
- The twenty-line docstring explaining why $\mathit{go}$ is a family, and why the two axes (the closing of the recogniser's context and the indexing of the recursion arguments) are separate, is the single most useful piece of documentation in the chapter.
- The induction is on the fuel, not on the argument: the recursive call has a smaller measure but whatever fuel the outer call had left, so an induction on the argument would not line the two up. The proof is short and clean, in pleasant contrast to \texttt{unfoldNatWellFounded.WF'}.
- The single \texttt{iota} line in this 1775-line file is inside this proof, at \srcloc{Lean4Lean/Verify/Environment/Primitive/Recursion.lean}{380}, forced by \texttt{TrExprS.appN}'s new hypothesis. Three adjacent lines now spell the same coercion three ways: line 376 passes \texttt{c.Ewf} bare through the \texttt{CoeOut} instance, line 380 writes \texttt{.orderedStrong} explicitly, line 381 keeps \texttt{.ordered}.
- The condition that the recursor does not mention the fuel variable is essential and well explained: without it, closing the telescope at two different fuels would give two unrelated recursors. These three definitions are, however, very wide existentials: \texttt{StepIH} and \texttt{StepBranch} bind nine variables each (three and four conjuncts respectively) and \texttt{Step} binds sixteen under nine conjuncts.
- The docstring explains why this cannot be exported as an implication conditioned on the decision being a boolean literal: that premise would live at the probe context, where the decision is precisely what is not a literal, so no consumer could supply it. The instantiation therefore happens inside the block. An excellent explanation of a subtle design forcing.
- The docstring's last paragraph says that only the first two checks are recorded so far. That is stale: the definition records all four, \texttt{Step} and \texttt{Eager} included.
- Two design decisions are recorded in the preamble, worked out before the proof was written: the packer is used applied and never as an abstraction, and the telescope is closed per base point. Both are right. The proof itself is, at this size, not practically reviewable and is a maintenance liability.
- The user-facing statement is the right one: the caller's only obligation is \texttt{Done}, and $R$ is quantified after the closing so that the answer may depend on it, which \texttt{Nat.bitwise} needs. Both consumers take the specialised \texttt{WF₂}: \srcloc{Lean4Lean/Verify/Environment/Primitive/Gcd.lean}{31} and \srcloc{Lean4Lean/Verify/Environment/Primitive/Bitwise.lean}{61}. Nothing consumes the general \texttt{WF}.
- The docstring records why this shape is available at all: \texttt{addDefinition} reorders type and value checking before calling the recogniser, so that the two translations arrive here as hypotheses. Consumed at \srcloc{Lean4Lean/Verify/Environment/Checker.lean}{201}.
- Nothing in the repository constructs an \texttt{AddsConsts}; it is a placeholder, as the file's own docstring says.
- The two are byte-for-byte the same proof script with the constant list swapped; one lemma parameterised by a three-element list would remove the duplication.
- The docstring is candid about the missing half of the handshake: a constructive \texttt{AddInduct} whose added constants are these, which the declaration checker's inductive case still waits on.
- Unused: the environment checker calls \texttt{Primitive.checkInductive}, but no verification of the declaration checker's inductive case consumes this theorem yet.

## experimental-logrel.tex (17 remarks)
- The same inversion lemmas are restated for \texttt{WShape} (\srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{1242}) and again for \texttt{TShape} (\srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{1889}). Three near-identical copies; a \texttt{Shape}-only development with one systematic transfer lemma would have been much shorter.
- The \texttt{variable (ih : ...)} plus \texttt{include ih} idiom used to thread the induction hypothesis through a 160-line namespace makes the helper lemmas (\texttt{exists\_max}, \texttt{app\_core}, \texttt{of\_compat}) look like standalone results with undocumented hypotheses. \texttt{WShape.join\_prop.join\_mem'} also shadows the earlier \texttt{WShapeFun.join\_mem'} (\srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{1374}).
- \srcloc{Lean4Lean/Experimental/ShapeLogRel.lean}{1665} \emph{Dead: well-formedness under partial lowering.} The claim that for a well-formed $x : \mathtt{WShape}\ n$ the approximation $(\mathtt{plift}\ x.1).1$ is well formed at level $m$, and so is any exact preimage $(\mathtt{plift}\ x.1).2$ (\ref{def:expa-shape-plift}), has no declaration in the compiled environment. The statement and its abandoned 58-line induction on $m$ and $n$ sit inside a block comment spanning lines 1665--1732, together with three further commented stubs for \texttt{ShapeFun.WF'.plift}, \texttt{Shape.WF.plift} and \texttt{ShapeFun.WF.plift} at lines 1725--1731; the live development never needs the result. All ten textual \texttt{sorry} occurrences (spread over eight lines) and the one \texttt{stop} in \texttt{ShapeLogRel.lean} live in this dead block, which makes a naive \texttt{grep sorry} of the file misleading in both directions: the file has no live \texttt{sorry}, yet everything from \ref{thm:expa-le-interp-strongsound} onwards is tainted through \texttt{Lean4Lean/Experimental/SExpr.lean}.
- The grid is not systematic: there is no \texttt{indTy\_not\_le\_ctor'} and no \texttt{ctor\_not\_le\_sort}. Only the instances the later proofs happened to need were proved, so a reader cannot tell which omissions are deliberate.
- \texttt{find\_cycle} is a genuinely reusable combinatorial lemma buried as a \texttt{private theorem} in the middle of a shape file; it belongs in \texttt{Lean4Lean/Std} or in Batteries. That \texttt{mono\_l} needs order-equivalence rather than $\le$ is a real limitation which propagates to every use site: the \texttt{mono\_l} field of \ref{structure:expa-logrel} has to carry two \texttt{HasType} premises to compensate.
- This is the conceptual heart of the approach: the model has no room for the content of a proof, because every inhabitant of a proposition-shape is $\bot$. It has no docstring.
- These lemmas rest on the \texttt{Params} class field \texttt{pat\_wf}, and from line 3931 onwards on \texttt{pat\_uniq} as well. Both are assumptions: the repository contains no \texttt{Params} instance at all, so nothing shows that they hold for Lean's actual recursor rules, and this development does not address the question.
- \texttt{Const.compat\_join} alone runs from line 3786 to line 3934, 149 lines with no intermediate structure and no comments. Only \texttt{LE\_Interp.strongSound} (206 lines), the \texttt{LRS} term (238) and \texttt{LR.adequacy} (327) are longer.
- \texttt{LE\_Interp.subst} is an exact biconditional with an existentially quantified valuation and is one of the best-designed results in the file.
- \texttt{sound\_lam} is about 105 lines and \texttt{sound\_forallE} about 100, both single tactic blocks with no comments.
- This is a highlight of the development. The thesis obtains unique typing only relative to the stratified judgement $\vdash_n$ and only after Church--Rosser; here it falls out of the model directly. It is, however, a statement about \texttt{StrongSound}, and \texttt{StrongSound} is supplied for arbitrary derivations only by \ref{thm:expa-le-interp-strongsound}, which is conditional.
- These lemmas return an existential of the form ``there is a level $n'$ such that for all $k \ge n'$'', so the level-polymorphism bookkeeping is threaded by hand everywhere; a \texttt{TShape}-first design would have avoided it.
- Because the $\mathtt{LogRel}$ structure is level-indexed while the interpretation (\ref{def:expa-le-interp}) is level-erased, these transport lemmas must be applied by hand at nearly every use site in \texttt{ShapeLogRelAdequacy.lean}. They are the main source of proof noise there.
- This is a dense 47-line declaration (lines 45--91) whose 39-line proof body is essentially all level bookkeeping; the mathematical content, ``join the two shapes'', is hidden inside it. It is the clearest place where the $\mathtt{WShape}\ n$ versus $\mathtt{TShape}$ duality costs the development.
- This is one of only four docstrings in \texttt{ShapeLogRelAdequacy.lean} (lines 93, 105, 448, 458). It factors out a pattern used at eighteen call sites, all inside \ref{thm:expa-lr-adequacy}, but it was extracted late: \ref{thm:expa-adequate-cons}, which precedes it, still inlines the same argument twice (lines 58--63 and 82--88).
- Probing the model with the least informative shape that still discriminates a head form is the trick that makes the whole construction pay off, and it is what the preceding 6500 lines exist to support. It is undocumented.
- This is the best-executed part of \texttt{LogRel.lean}: the custom \texttt{@[elab\_as\_elim]} eliminator and the \texttt{Subsingleton} instance at line 189 are exactly the right API. The two \texttt{grind} calls that discharge the family equalities are brittle across toolchain bumps.
