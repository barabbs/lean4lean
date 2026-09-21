# lean4lean blueprint

A [leanblueprint](https://github.com/PatrickMassot/leanblueprint) of this `lean4lean` fork: the theory
of Lean's type system, the executable kernel, and the verification of the kernel against the theory —
with the fork's two contributions marked where they sit:

- **iota** — reduction rules for the recursors of inductive blocks;
- **trproj** — structure projections (`TrProj`).

The Lean code is already written. The blueprint is a map of it: every node cites its declarations, its
source location and its thesis counterpart, and the dependency graph shows what is proved, what
contains a `sorry`, and what depends on one.

Documented commit: branch `trproj` at `20ec229`, Lean `v4.33.0-rc2`.

## Layout

```
src/chapters/*.tex   18 chapters (see below)
src/macros/          common.tex (shared) + print.tex / web.tex overrides
src/content.tex      chapter order
src/{web,print}.tex  leanblueprint drivers
tools/               validation scripts and the declaration census
review-data/         review material kept out of the chapters (see its README)
STYLE.md             how nodes and chapters are written (schematic style)
CONVENTIONS.md       how nodes are annotated
```

## Chapters

| Part | Chapters |
|---|---|
| Frame | `intro` |
| Theory (`Lean4Lean/Theory`) | `syntax`, `typing`, `metatheory`, `inductive` (iota), `proj` (trproj) |
| Kernel | `kernel` |
| Verification (`Lean4Lean/Verify`) | `trexpr` (trproj), `trenv` (iota, trproj), `primitives-core`, `primitives-arith`, `typechecker` (trproj), `levels` |
| Experimental | `experimental-logrel`, `experimental-reduction` |
| Contributions and status | `contrib-iota`, `contrib-trproj`, `status` |

Chapters follow the source tree. There is **one dependency graph for the whole project**: 36% of the
`\uses` edges cross chapters, and leanblueprint computes "fully proved" inside one graph only, so
per-chapter graphs would hide how a `sorry` in the theory reaches the verification.

## Reading a node

- Badges: `[iota]` / `[trproj]` / `[mixed]` — attribution (no badge = upstream, unchanged);
  `[SORRY]` — the Lean proof contains a literal `sorry`; `[USES SORRY]` — proved, but depends on one
  (the line lists the axiom footprint); `[EXPERIMENTAL]` — research module off the verified path.
- Grey lines: source pointer (`path:line`, a GitHub link in the web version), thesis counterpart.
- Graph colours: green border = stated in Lean; green fill = proved; dark green = proved with every
  ancestor proved; blue fill = the proof is not complete.

## Build

Needs a Python venv with `leanblueprint`, Graphviz, and a TeX distribution with `xelatex` and the
FreeSerif, FreeSans and JetBrains Mono fonts. From the repository root:

```
python3 -m venv .venv && .venv/bin/pip install leanblueprint
export PATH="$PWD/.venv/bin:$PATH"
leanblueprint pdf      # blueprint/print/print.pdf
leanblueprint web      # blueprint/web/index.html
leanblueprint serve    # local preview
```

Building reads only `blueprint/src/`. `leanblueprint pdf` runs latexmk without
`-interaction=nonstopmode`: on a LaTeX error it waits forever on a prompt. To see the error, run from
`blueprint/src`:

```
latexmk -xelatex -interaction=nonstopmode -halt-on-error -output-directory=../print print.tex
```

## Validation

| Tool | Checks |
|---|---|
| `tools/check_chapter.py <chapter.tex>...` | labels, `\lean{}` names against the compiled environment, `\contrib` / `\axfoot` / `\leanok` against the declaration census, unescaped underscores |
| `tools/check_global.py` | duplicate and unresolved labels, `\uses` cycles |
| `tools/skeleton.py <chapter.tex> [git-ref]` | an edit left the graph skeleton and the node furniture unchanged against a reference commit; house style (no review notes, no client projects, ASCII) |
| `tools/rebuild_registry.py` | regenerates the label registry after an edit |
| `tools/run_census.sh` | regenerates the declaration census from a built checkout |

`leanblueprint checkdecls` is not wired: it needs a `checkdecls` dependency in the host `lakefile.toml`,
which is deliberately untouched. `check_chapter.py` covers the same ground.

## Limitations

- `\uses{}` edges were curated by reading the code, not derived from the elaborator: approximate.
- Upstream code is mapped more coarsely than the two contributions.
- Source pointers and the census are pinned to `20ec229`; rerun `tools/run_census.sh` and
  `tools/rebuild_registry.py` before trusting the blueprint against a later commit.

## Continuous integration

`.github/workflows/blueprint.yml` runs on pushes to branch `blueprint`, on `workflow_dispatch`, and
(build and validate only) on pull requests touching `blueprint/**`. Four jobs:

- `validate` — builds the Lean project, regenerates the census and the registry, runs both checkers.
- `blueprint` — `leanblueprint pdf` and `leanblueprint web`; output uploaded as an artifact on every run.
- `api-docs` — best-effort `doc-gen4` build so the `\lean{}` links resolve; never blocks deployment.
- `deploy` — publishes `blueprint/`, `blueprint.pdf` and `docs/` to GitHub Pages; skipped on pull requests.

It does not use leanblueprint's stock `docgen-action`, whose blueprint path always runs
`lake exe checkdecls`. Owner-side settings: GitHub Pages source set to *GitHub Actions*; the
`github-pages` environment must allow deployments from branch `blueprint`; `workflow_dispatch` appears in
the Actions tab only once the workflow file exists on the default branch.
