# lean4lean blueprint — writing style (binding)

**Goal.** A reader grasps any node in 15 seconds and any chapter's shape in one minute. The blueprint is
**schematic**: bulleted, with bold run-in labels, one highlight per node, tables for anything enumerable.
As concise and as clear as possible. Apply Strunk's *Elements of Style*: active voice, positive form,
definite concrete language, **omit needless words**, one idea per sentence, emphatic word last, parallel
form for parallel ideas.

**Point of view.** This is the blueprint of **lean4lean**: a standalone account of the project's formal
content — the theory of Lean's type system, the executable kernel, the verification of the kernel against
the theory — with the fork's two contributions marked where they sit: **iota** (reduction rules for
recursors of inductive blocks) and **trproj** (structure projections, `TrProj`). It is *not* a review
report. Therefore:

- No review framing in the chapters: no "review notes", "claims audit", "hygiene", "assessment",
  "churn/history", severity labels, or advice to the author. Review material lives in
  `blueprint/review-data/` (everything removed from the chapters is preserved verbatim in
  `review-data/extracted-review-notes.md`).
- **Never mention any client or consumer project** of lean4lean, by name or by allusion (its name, its
  purpose, what it asks of lean4lean). A design decision is motivated from lean4lean's own side (the
  kernel does X, so the theory states Y) or not motivated at all.
- References to Carneiro's thesis stay: it is lean4lean's own specification.

## 1. Invariants — never change these (`tools/skeleton.py` checks them)

- Every node stays, in the same order: same environment (`definition`, `lemma`, `proposition`, `theorem`,
  `corollary`, `example`), same `\label{}`, same `\lean{...}` list, same `\leanok`, same `\uses{...}` lists
  in the statement and in the proof. Copy these lines verbatim. Add no node, remove no node.
- **Node furniture stays verbatim**: `\contrib{iota|trproj|mixed}`, every `\srcloc{path}{line}`, every
  `\axfoot{...}`. A node that had a `\thesisref{...}` keeps one; its text may be tightened to one line.
- A `proof` environment FOLLOWS its statement's `\end{...}`, never nested. A proof WITHOUT `\leanok` marks
  a Lean proof that contains a literal `sorry`: keep it without `\leanok`, and open it with `\stSorry{}`
  and what is missing.
- Keep every `\label{}` in the file (chapter, sections, nodes) and the `\chapter{...}` line, unless your
  task says the chapter is retitled.
- **Fidelity.** The old text is the accurate reference. Add no fact. Drop no hypothesis and no conclusion
  of a statement. When you cut, cut commentary.
- ASCII only. Every `_` outside `\lean{}`, `\srcloc{}`, `\label{}`, `\uses{}`, `\ref{}` is written `\_`,
  also inside `\texttt{}` and titles. No `$...$` in a `\chapter`/`\section` title without
  `\texorpdfstring{$x$}{x}`.
- Allowed LaTeX: `itemize`, `enumerate`, `description`, `tabular` with booktabs rules (`\toprule`,
  `\midrule`, `\bottomrule`; text-heavy columns as `p{0.xx\linewidth}`; **no `\multirow`**), `remark`,
  `\emph`, `\textbf`, `\texttt`, `\ref`, math, and the macros of `src/macros/common.tex` (read it). No new
  packages, no `\cite`, no tikz, no footnotes. Define no macro in a chapter.

## 2. Macros for the schematic style (`src/macros/common.tex`)

- `\lead{Label}` — bold run-in label. Fixed vocabulary: `In short`, `Given`, `Then`, `Where`, `Lean`,
  `Idea`, `Steps`, `Status`, `Caveat`, `Why`, `Goal`, `Main results`, `Lean files`, `Thesis`,
  `Contribution`, `Missing`.
- `\hl{phrase}` — coloured bold highlight. **At most one per node.**
- Status badges: `\stProved` (proved, no `sorry` in its closure), `\stSorry` (the Lean proof contains a
  literal `sorry`), `\stTainted` (proved, but depends on a `sorry` elsewhere; `\axfoot` already prints
  it), `\stExperimental` (research module off the verified path).
- `\contrib{iota|trproj|mixed}` renders as a coloured `[iota]` / `[trproj]` / `[mixed]` badge.
  `\srcloc`, `\thesisref`, `\axfoot` render small and grey. In print, `\lean{}` typesets the declaration
  names under the node title — so **never** spend a sentence restating a Lean name.

## 3. Node templates

### 3.1 Result (lemma / theorem / proposition / corollary)

```latex
\begin{theorem}[Short title, 2-6 words]
  \label{...}
  \lean{...}
  \leanok
  \uses{...}
  \contrib{trproj}\srcloc{Lean4Lean/Theory/Proj.lean}{123}      % verbatim, when present
  \thesisref{one line.}                                        % when present
  \lead{In short} One sentence, at most 25 words, plain words, with \hl{the key phrase}.
  \begin{itemize}
  \item \lead{Given} one hypothesis per bullet (group trivial side conditions);
  \item \lead{Then} the conclusion (sub-bullets for a conjunction).
  \end{itemize}
  \axfoot{...}                                                 % verbatim, when present
\end{theorem}
\begin{proof}
  \uses{...}
  \leanok
  \lead{Idea} One sentence. \lead{Steps} (optional) an `enumerate` of at most 4 short items.
\end{proof}
```

Budget: statement at most 70 words (a headline theorem at most 120); proof at most 40 words. A small
technical lemma needs only `\lead{In short}` and perhaps one formula — no list. `family` lemmas (many
Lean names, one node): `\lead{In short}` for the family, then a bullet or table row per member group.

### 3.2 Definition

```latex
\begin{definition}[Short title]
  ...annotations and furniture verbatim...
  \lead{In short} What it is and what it is for, one sentence.
  \begin{itemize}                 % a `tabular` when there are more than 6 rows
  \item \texttt{ctor\_or\_field}: meaning in at most 15 words;
  \end{itemize}
\end{definition}
```

Inductive relations with many rules (typing, definitional equality, reduction, `TrExprS`, ...): **one
table**, e.g. `Rule | Premises | Conclusion`. Defining equations of a function: a short aligned display
or bullets, not a sentence.

### 3.3 What happens to review notes and remarks

- Delete every `\reviewnote{...}`. If — and only if — a note states something the reader needs in order
  to read the statement correctly (a side condition the statement silently relies on, a totality gap, a
  known incompleteness boundary), keep its content as one line inside the node:
  `\lead{Caveat} at most 25 words.` Never keep advice, severity, praise or style comments.
- `remark` environments: keep only what helps understand the mathematics; start with `\lead{Why}` or
  `\lead{Caveat}`; at most 40 words. Delete the rest.

## 4. Chapter frame

- **Opener**, directly after `\chapter`/`\label`:
  ```latex
  \section*{At a glance}
  \begin{itemize}
  \item \lead{Goal} one sentence.
  \item \lead{Main results} Theorem~\ref{...} (gist in 8 words); ...
  \item \lead{Status} \stProved{} ... ; \stSorry{} n proofs (Theorem~\ref{...}, ...) ; \stTainted{} ... .
  \item \lead{Contribution} what iota / trproj added in this chapter, one line each (omit if nothing).
  \item \lead{Lean files} \texttt{Lean4Lean/Theory/X.lean}, ...
  \item \lead{Thesis} the corresponding thesis sections, one line.
  \end{itemize}
  ```
- **Sections** open with at most two sentences of orientation. No other free prose between nodes unless
  it fixes notation (then a short bullet list or a table).
- **Closer**: delete `\section{Review notes}` and `\section{Contribution summary}` (their labels, if any,
  must survive: put the `\label` on the new closer). End the chapter with `\section*{Caveats}`: at most
  6 bullets of at most 30 words — only facts that limit what the chapter's results mean (what is
  `sorry`, what is assumed, what a definition deliberately does not cover).

## 5. Words

- Sentences at most 25 words. At most one `---` aside per paragraph; prefer none.
- Ban: "it should be noted", "in other words", "load-bearing", "exactly" as filler, "simply", "of course",
  rhetorical contrasts ("not X but Y") when "Y" suffices, evaluative adjectives ("convincingly",
  "clean", "careful", "unfortunately").
- Say *upstream* for code inherited unchanged from digama0/lean4lean, and name the contribution
  (`iota`, `trproj`) for the rest. Do not narrate branch history, line counts, or commit archaeology.
- Line numbers live only in `\srcloc{}`. Prefer a table or bullets to any sentence that enumerates three
  or more things.

## 6. Worked example

Before (a definition with a review note, 110 words):

```latex
\begin{definition}[Field selector \texttt{fieldSelector}]
  \label{def:proj-field-selector}
  \lean{Lean4Lean.VExpr.fieldSelector}
  \leanok
  \uses{ind:vexpr}
  \contrib{trproj}\srcloc{Lean4Lean/Theory/Proj.lean}{70}
  \thesisref{axioms.tex \S2.6.3, the recursor: the minor premise $\varepsilon_c=...$.}
  $\mathrm{fieldSelector}\;Fs\;i$ is $Fs.\mathrm{foldr}\;\lambda\;(\mathrm{bvar}(|Fs|-1-i))$, the
  $\lambda$-telescope over the field types whose body is the $i$-th binder counted from the outside. It
  is the minor premise handed to the structure's recursor to read out field $i$.
  \reviewnote{The \texttt{Nat} subtraction $|Fs|-1-i$ is unguarded: for $i\ge|Fs|$ it truncates to $0$
  and silently selects the innermost binder instead of being undefined. Callers are expected to carry
  \texttt{TrProjCtor.field\_lt}.}
\end{definition}
```

After (55 words):

```latex
\begin{definition}[Field selector]
  \label{def:proj-field-selector}
  \lean{Lean4Lean.VExpr.fieldSelector}
  \leanok
  \uses{ind:vexpr}
  \contrib{trproj}\srcloc{Lean4Lean/Theory/Proj.lean}{70}
  \thesisref{axioms.tex \S2.6.3: the recursor's minor premise $\varepsilon_c$.}
  \lead{In short} The minor premise that makes a structure's recursor \hl{return field $i$}.
  \begin{itemize}
  \item $\mathrm{fieldSelector}\;Fs\;i = \lambda\,Fs.\ \mathrm{bvar}(|Fs|-1-i)$: a $\lambda$-telescope
        over the field types, returning the $i$-th binder from the outside.
  \item \lead{Caveat} For $i \ge |Fs|$ the subtraction truncates and selects the innermost binder;
        callers carry \texttt{TrProjCtor.field\_lt}.
  \end{itemize}
\end{definition}
```

## 7. Procedure for a rewriter

1. Read this file, `src/macros/common.tex`, then the whole chapter.
2. Rewrite the chapter in place, a whole section per edit (or write the new chapter as a few part files
   in a scratch directory and `cat` them over the chapter). Do not edit node by node: aim for fewer than
   40 tool calls. Copy annotation and furniture lines verbatim; rewrite bodies from the old bodies only.
3. Run `python3 blueprint/tools/skeleton.py blueprint/src/chapters/<file> blueprint` from the repository
   root until it prints `SKELETON OK` and the word ratio your task names. Symbolic bullets are welcome
   where clearer than prose; never trade a hypothesis for the word budget.
4. Do not run lake, leanblueprint, latexmk or xelatex. Edit no other file. Do not use git to change
   anything (no commit, checkout, stash, tag).

## 8. Current state only (no history)

The blueprint is a consistent picture of the fork at the documented commit; it is not a changelog. Never
write "since ...", "was fixed", "has been restated", "used to", or describe a state and then its later
changes; state what is. What is not proved is an open item in the present tense (`\stSorry{}`,
`\stTainted{}`, or a Caveats bullet). Git holds the history.
