# lean4lean blueprint — annotation conventions (binding)

How nodes are annotated. How they are *written* is in [`STYLE.md`](STYLE.md); read both before editing a
chapter. Documented commit: fork branch `trproj` at `20ec229`, Lean `v4.33.0-rc2`.

## Files

```
src/web.tex, src/print.tex      drivers; both \input{content}
src/content.tex                 chapter order
src/macros/common.tex           shared macros (define none in a chapter)
src/macros/web.tex, print.tex   format-specific overrides
src/chapters/<name>.tex         one file per chapter; starts with \chapter{...}\label{chap:<name>}
```

Chapters follow the source tree: `Theory/` (syntax, typing, metatheory, inductive, proj), `Kernel/`
(kernel), `Verify/` (trexpr, trenv, primitives-core, primitives-arith, typechecker, levels),
`Experimental/` (experimental-logrel, experimental-reduction), framed by `intro`, the two contribution
chapters (`contrib-iota`, `contrib-trproj`) and `status`.

## Nodes

- **Environments**: `definition` (def, abbrev, structure, inductive, instance, axiom, opaque), `theorem`
  (headline results), `lemma` (everything else, and *families*: one node for a group of parallel
  declarations, all listed in `\lean{}`), `example` (declarations of test and example files),
  `proposition` (a specification stated as a `Prop`; rare). `remark` is prose, not a node.
- **Shape**: `\begin{env}[Title] \label{id} \lean{A.b, C.d} \leanok \uses{...} <furniture> <body> \end{env}`,
  then for a result a SIBLING `\begin{proof} \uses{...} \leanok ... \end{proof}` — never nested: plasTeX
  pairs a proof with the preceding sibling, and a nested proof renders the node as unproved.
- **`\label`**: globally unique; letters, digits, `:` `-` `_` `.`. Never rename a label: other chapters and
  the registry refer to it.
- **`\lean{}`**: only names of the compiled environment (`tools/check_chapter.py` verifies them against the
  declaration census). Never invent a name.
- **`\leanok` in a statement**: always — every node documents existing Lean code.
- **`\leanok` in a proof**: iff the declaration's own body contains no literal `sorry`. Otherwise omit it and
  open the proof with `\stSorry{}` and what is missing. The dependency graph then shows the node as not
  proved, and every node that depends on it loses its "fully proved" colour.
- **`\uses{}`**: labels only. In the statement: what the statement mentions. In the proof: what the proof
  relies on. A dependency without a node is named in prose as `\texttt{Name}`.

## Node furniture (first lines of the body, in this order)

- `\contrib{iota}` / `\contrib{trproj}` / `\contrib{mixed}` — on every node that is not inherited unchanged
  from upstream (digama0/lean4lean). `mixed` = an upstream declaration modified by a contribution.
- `\srcloc{Lean4Lean/Theory/Proj.lean}{123}` — source pointer at the documented commit (a GitHub link in the
  web version). The only place where line numbers appear.
- `\thesisref{...}` — the counterpart in Carneiro's thesis, one line, or "no thesis counterpart".
- `\axfoot{sorryAx via X; propext}` — last line of the body of a node that is proved but depends on a
  `sorry` elsewhere. Required on contributed nodes, optional on upstream ones.

## Dependency graph

One graph for the whole project (no `dep_by` option). Per-chapter graphs would cut the 36% of `\uses`
edges that cross chapters — the theory-to-verification story — and leanblueprint computes "fully proved"
inside one graph only, so a `sorry` in `Theory/` would not reach the nodes of `Verify/` that depend on it.

## Underscores and titles

Outside `\lean{}`, `\srcloc{}`, `\label{}`, `\uses{}`, `\ref{}` write every `_` as `\_`, also inside
`\texttt{}` and titles. No `$...$` in a `\chapter`/`\section` title without `\texorpdfstring{$x$}{x}`.
