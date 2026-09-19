# lean4lean blueprint — authoring conventions (binding for all agents)

Repo: /home/barabba/Documents/Research/Projects/Peregrine/lean4lean (branch trproj, HEAD 20ec229; remote github.com/barabbs/lean4lean; upstream digama0/lean4lean).
Blueprint lives in `<repo>/blueprint/` (untracked for now; committed later on a new branch `blueprint`). NEVER edit anything else in the repo. NEVER run `lake build`.
Scratch inputs: `.blueprint-work/understand/` — `<group>.json` (node maps), `<group>.md` (narratives), `thesis-map.{json,md}`, `contrib-{iota,trproj}.{json,md}`, `census.md`, `sorry-grep.md`, `decls.tsv` / `all-constants.tsv` (ground-truth declaration names from the compiled environment: name, module, kind, line, axioms, usesSorry), `blueprint-tooling.md` (leanblueprint reference), `registry.tsv` (all blueprint labels), `enriched/<group>.json` (nodes with census data merged in).

## Files
```
blueprint/src/web.tex, print.tex        (drivers; both \input{content})
blueprint/src/content.tex               (\input{chapters/intro} ... in the fixed order below)
blueprint/src/macros/common.tex         (shared macros; see below)
blueprint/src/macros/web.tex, print.tex (format-specific)
blueprint/src/plastex.cfg, blueprint.sty, latexmkrc, extra_styles.css
blueprint/src/chapters/<name>.tex       (one file per chapter, exactly these names)
```
Chapter order and source group:
 1 intro.tex               — (synthesis) project, trust boundary, how to read this blueprint, contribution overview
 2 syntax.tex              — theory-syntax
 3 typing.tex              — theory-typing
 4 metatheory.tex          — theory-metatheory
 5 inductive.tex           — theory-inductive          (iota focus)
 6 proj.tex                — theory-proj-and-tests     (trproj focus)
 7 kernel.tex              — kernel-impl
 8 trexpr.tex              — verify-typing             (contains TrProj/TrProjCtor, trproj focus)
 9 trenv.tex               — verify-environment        (AddInduct, quotients, proj_defeq; iota+trproj focus)
10 primitives-core.tex     — verify-primitive-core
11 primitives-arith.tex    — verify-primitive-arith
12 typechecker.tex         — verify-typechecker        (WHNF projection coverage, trproj)
13 levels.tex              — verify-level-and-utils
14 experimental-logrel.tex — experimental-a
15 experimental-reduction.tex — experimental-b
16 contrib-iota.tex        — (synthesis) review of the iota contribution
17 contrib-trproj.tex      — (synthesis) review of the trproj contribution
18 status.tex              — (synthesis) sorry/axiom census, trust boundary, issue registry
Each chapter file starts with `\chapter{...}` and `\label{chap:<name>}`; sections `\section{...}` freely.

## Macros (defined in macros/common.tex; use them, do not define new ones in chapters)
- `\contrib{iota}` / `\contrib{trproj}` / `\contrib{mixed}` — attribution badge. MUST be the first thing in the body of every node whose attribution is not master. `mixed` = a master declaration modified on a branch; say in prose which branch changed what.
- `\srcloc{Lean4Lean/Theory/Proj.lean}{123}` — source pointer (renders as a monospace path:line; the web build links it to GitHub blob at HEAD). Use in every node (after the badge) and in review notes.
- `\thesisref{Theorem 2.3 (typesys.tex, thm:foo)}` — thesis correspondence line.
- `\axfoot{sorryAx via VEnv.WF.patsStrong; propext}` — axiom footprint line; REQUIRED on every non-master theorem/lemma/definition whose axioms include sorryAx (list the sorry sources you can identify from census.md), optional otherwise.
- `\reviewnote{...}` — a short critical remark rendered as an emphasised paragraph. Use for issues found (no fixes).
- Underscores: outside `\lean{}`, `\srcloc{}`, `\label{}`, `\uses{}` every `_` must be written `\_` (also inside `\texttt{}` and in environment titles). Inside `\lean{}`, `\srcloc{}`, `\label{}`, `\uses{}` write raw `_`. Never put `$...$` in `\chapter{}`/`\section{}` titles without `\texorpdfstring{$x$}{x}`.

## Nodes
- Environments: `definition` (def/abbrev/structure/inductive/instance/axiom/opaque), `theorem` (importance 3), `lemma` (importance 1–2 and `family` nodes), `example` (test/example files), `proposition` for specifications stated as Props that are neither def nor theorem (rare). Prose that is not a node: `remark` environment (no \label needed) or plain text.
- Every node: `\begin{<env>}[<Title>]  \label{<id>}  \lean{Fully.Qualified.Name, Other.Name}  \leanok  ...body...  \end{<env>}` then for theorem/lemma a SIBLING `\begin{proof} ... \end{proof}` right after (never nested).
- `\label` = the node `id` from the group json (already globally unique; keep verbatim). Valid characters: letters, digits, `:` `-` `_` `.`.
- `\lean{}`: only names present in `all-constants.tsv` (ground truth). If a name from the json is missing there, find the right one with grep or drop it; never invent. Comma-separated, no spaces required.
- `\leanok` on the statement: always (all nodes describe existing Lean code). Exception: nodes for declarations that are literally `sorry` as a *definition* (status axiom/sorry-def): still `\leanok` on the statement but explain.
- `\uses{label, label}`: labels from registry.tsv only (any chapter). Put `\uses` inside the definition body for definitions, inside the `proof` for theorems/lemmas (uses of the *statement* — e.g. the definitions it mentions — go in the statement body; uses of the *proof* go in the proof). A dependency with no label is mentioned in prose as `\texttt{Name}` (escape underscores) instead.
- `proof` environment: contains `\uses{...}` then `\leanok` IFF the declaration has NO literal `sorry` in its own body (field `direct_sorry=false` in enriched json). If it does contain a sorry: omit `\leanok`, and begin the proof text with `\textbf{Not proved in Lean.}` + what is missing. Then 1–3 sentences of proof sketch naming the key lemmas (escape underscores) — faithful to the actual Lean proof, not a guess.
- Transitive sorry taint (usesSorry=true but direct_sorry=false): keep `\leanok` in the proof, add `\axfoot{...}` naming the sorry source(s). For master-attributed nodes this is optional; for contributed nodes it is mandatory.
- Titles: the short human title from the json, plus the main Lean short name in `\texttt{}` if helpful; escape underscores.
- Statements must be faithful to the Lean statement (hypotheses, direction, universes/contexts). Prefer $\Gamma \vdash e : A$-style notation consistent with the thesis; define notation once in the chapter intro if needed.
- Nodes tagged `family`: use `lemma`, list all lean names, describe the family; proof sketch may be collective.
- Master nodes may be terse (2–4 lines each). Contributed nodes must be complete: badge, srcloc, thesisref (or "no thesis counterpart"), statement, proof sketch, axfoot if tainted, reviewnote if the json `notes` flags something.

## Chapter layout
1. `\chapter{Title}\label{chap:x}` + 2–5 paragraph overview (from `<group>.md`): purpose, files (with `\srcloc`), thesis correspondence, what the branches contributed (line counts from file_summaries), overall assessment in one paragraph.
2. Sections following the files/themes, nodes in dependency-respecting order (definitions before theorems that use them), each with the mandatory fields.
3. Final `\section{Review notes}`: bullet list (`itemize`) of every issue from the json `issues` array and the md narrative, each with `\srcloc` and severity in bold; no fixes, no softening. Contributed chapters also get a `\section{Contribution summary}` before the review notes: what was added, why, how it connects to the rest (with `\ref{}` to labels), and what remains open.

## Style
Plain, precise, technical English; no marketing language. Never claim something is verified/proved unless the census says so. Cite the thesis by file and label. Avoid em-dashes. Keep each node body under ~12 lines.
