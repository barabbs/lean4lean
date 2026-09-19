# lean4lean blueprint

A [leanblueprint](https://github.com/PatrickMassot/leanblueprint) of this
`lean4lean` fork. It is not a blueprint in the usual sense of a plan for work
not yet done: the Lean code is already written. Its purpose is self-review of
two contributions layered on this fork — branch `iota` (ι-reduction /
inductive-block specification) and branch `trproj` (projection support,
`TrProj`) — set inside a map of the whole project, so that every claim about
what is proved, what is `sorry`, and what each branch changed can be checked
against the compiled environment rather than against prose.

Snapshot: branch `trproj`, commit `20ec229`, Lean `v4.33.0-rc2`, built and
reviewed on 2026-09-19. Source pointers, axiom footprints and the declaration
census below are all pinned to this commit; see Limitations.

## Layout

```
blueprint/
  src/chapters/*.tex     18 chapter files, one per topic (see Reading guide)
  src/macros/            common.tex (shared macros) + print.tex/web.tex overrides
  src/content.tex        chapter include order
  src/{web,print}.tex    leanblueprint drivers
  src/plastex.cfg, blueprint.sty, latexmkrc, extra_styles.css
  tools/                 validation scripts + the census generator (see Validation)
  review-data/           the evidence base the chapters were written from (see its README)
  print/, web/           leanblueprint build output (gitignored, see Build)
  lean_decls             declaration list for `leanblueprint checkdecls` (not wired, see Validation)
  CONVENTIONS.md         authoring conventions for anyone (or any agent) editing chapters
```

## Build

Requires a Python venv with `leanblueprint`, Graphviz, and a TeX distribution
with `xelatex` plus the FreeSerif and JetBrains Mono fonts.

```
python3 -m venv .venv && .venv/bin/pip install leanblueprint
export PATH="$PWD/.venv/bin:$PATH"
leanblueprint pdf      # -> blueprint/print/print.pdf
leanblueprint web      # -> blueprint/web/index.html
leanblueprint serve    # local preview server
```

Building does not touch the Lean project; it only reads `blueprint/src/`.

## Reading guide

Start with `intro.tex` (project overview, trust boundary, how the rest is
organised), then `contrib-iota.tex` and `contrib-trproj.tex` (the actual
self-reviews), then `status.tex` (sorry/axiom census, issue registry). The
chapters in between are the whole-project map, in dependency order:

1. `syntax.tex` — core syntax of the idealised type theory (VLevel/VExpr/VDecl/VEnv)
2. `typing.tex` — the `Lean.Expr` → `VExpr` translation layer's typing theory
3. `metatheory.tex` — Church-Rosser, head reduction, unique typing, strong normalisation
4. `inductive.tex` — inductive blocks and ι-reduction patterns (iota focus)
5. `proj.tex` — projection theory and its tests (trproj focus)
6. `kernel.tex` — the executable Lean 4 kernel re-implementation
7. `trexpr.tex` — `TrExprS`/`TrProj`/`TrProjCtor`, the model-vs-implementation bridge (trproj focus)
8. `trenv.tex` — environments, `AddInduct`, quotients, `proj_defeq` (iota + trproj focus)
9. `primitives-core.tex` — primitive (Nat/String) operation verification, core
10. `primitives-arith.tex` — primitive operation verification, arithmetic
11. `typechecker.tex` — the verified type-checker, including WHNF projection coverage (trproj)
12. `levels.tex` — universe levels and shared utilities
13. `experimental-logrel.tex` — logical-relation research modules
14. `experimental-reduction.tex` — further research modules under `Experimental/`
15. `contrib-iota.tex` — review of the iota contribution
16. `contrib-trproj.tex` — review of the trproj contribution
17. `status.tex` — sorry/axiom census, trust boundary, issue registry

Every non-master node carries a `\contrib{iota|trproj|mixed}` badge and a
`\srcloc{}` source pointer (a GitHub link at the pinned commit, in the web
build). Sorry-tainted nodes carry an `\axfoot{}` axiom footprint. Every
chapter ends with a review-notes section; contributed chapters also have a
contribution-summary section. Each chapter has its own dependency graph in
the web build (`leanblueprint web`, linked from that chapter's page); there is
no single whole-blueprint graph.

## Validation

`tools/check_chapter.py <chapter.tex>...` and `tools/check_global.py` lint the
chapters against `.blueprint-work/understand/registry.tsv` and the ground-truth
declaration census (duplicate/unresolved labels, `\uses` cycles, `\lean{}`
names that don't exist, missing `\contrib`/`\axfoot`, unescaped underscores).
`tools/rebuild_registry.py` regenerates that registry from the chapters after
an edit. `tools/run_census.sh` regenerates the census itself
(`decls.tsv`/`all-constants.tsv`) from a *built* checkout via `lake env lean`;
see its header comment for why it runs in ~30 separate passes. None of the
three checkers are wired into `leanblueprint`'s own commands; run them by hand
after editing a chapter.

`leanblueprint checkdecls` (cross-checking `\lean{}` names via `#check`) is
**not** wired up, even though `lean_decls` exists. It needs an executable
`checkdecls` target added as a dependency of the *host* project's own
lakefile, and this project's `lakefile.toml` was deliberately left untouched
(the review task this blueprint was built under forbids editing anything in
the repo outside `blueprint/` and `.blueprint-work/`). `tools/check_chapter.py`
covers the same ground — existence of `\lean{}` names in the compiled
environment — without needing that.

## Limitations

- `\uses{}` edges (and hence the dependency graphs) were curated by the
  reviewing agents from reading the chapters, not derived from the Lean
  elaborator's own dependency graph; treat them as approximate.
- Coverage of master (pre-fork) code is coarse: master chapters are terser by
  convention (see `CONVENTIONS.md`) and are not reviewed to the same depth as
  the iota/trproj material.
- `\lean{}` names render as plain `\dochome`-relative links in the web build,
  pointing at a doc-gen4 site (`barabbs.github.io/lean4lean/docs`) that has
  not been generated or published; those links currently 404.
- This is a snapshot at `20ec229`. Source pointers, line numbers and the
  census all go stale as soon as the underlying branches move; rerun
  `tools/run_census.sh` and `tools/rebuild_registry.py` and re-review before
  trusting this against a later commit.

## Continuous integration

`.github/workflows/blueprint.yml` (repo root, not under `blueprint/`) builds
and publishes this blueprint to GitHub Pages on every push to branch
`blueprint`, manually via `workflow_dispatch`, and (build + validate only,
never deploy) on pull requests touching `blueprint/**`.

It does **not** use `leanblueprint`'s stock GitHub Actions template
(`leanprover-community/docgen-action` with `blueprint: true`): that action's
blueprint path unconditionally runs `lake exe checkdecls`, which needs the
`checkdecls` lake dependency this project's `lakefile.toml` deliberately does
not carry (see Validation above, and there is no input to turn that step
off). Instead, the workflow has four jobs:

- **`validate`** builds the Lean project the way `ci.yml` does (no lint, no
  `mk_all-check`), then runs `tools/run_census.sh` +
  `tools/rebuild_registry.py` + `tools/check_chapter.py` (all chapters) +
  `tools/check_global.py` -- the same checks described in Validation above,
  now run in CI instead of by hand, failing the job on any `ERROR`.
- **`blueprint`** builds `leanblueprint pdf` and `leanblueprint web` on a
  runner provisioned with TeX Live (xelatex), the
  FreeSerif/FreeSans/JetBrains Mono fonts print.tex needs, and Graphviz.
  It's independent of the Lean project (per Build above) and so runs in
  parallel with `validate`. Its PDF and web output are uploaded as a normal
  build artifact on every run, including pull requests, so they're
  inspectable without a deployment.
- **`api-docs`** is a best-effort `doc-gen4` build: the standard `docbuild`
  nested-project recipe (a separate, throwaway Lake project that requires
  this package by path plus `doc-gen4` pinned to the `v4.33.0-rc2` tag
  matching `lean-toolchain`), so the blueprint's `\lean{}` links
  (`plastex.cfg`'s `\dochome`) resolve. It's marked `continue-on-error:
  true`: a failure here never blocks deployment, it just means `/docs` (and
  hence those links) 404 for that deployment, same as the pre-existing state
  described in Limitations above.
- **`deploy`** assembles the above into one site and publishes it with
  `actions/upload-pages-artifact` + `actions/deploy-pages`. It's skipped on
  pull requests.

### Site layout

```
https://barabbs.github.io/lean4lean/
├── index.html      minimal landing page linking to the three below
├── blueprint/      leanblueprint web output (dependency graphs, per-chapter pages)
├── blueprint.pdf   leanblueprint PDF output
└── docs/           doc-gen4 API docs (best effort; see api-docs above)
```

### Owner-side settings this needs

- GitHub Pages must be enabled with **Settings > Pages > Build and
  deployment > Source: GitHub Actions** (already the case for this fork).
- The `github-pages` deployment environment currently restricts deployments
  to branch `master` only (checked via `gh api
  repos/barabbs/lean4lean/environments/github-pages/deployment-branch-policies`).
  Since this workflow deploys from `blueprint`, add a branch rule for it
  under **Settings > Environments > github-pages > Deployment branches and
  tags > Add deployment branch or tag rule**, entering `blueprint`; otherwise
  the `deploy` job's `actions/deploy-pages` step fails with an
  environment-protection error.
- `workflow_dispatch` only appears in the Actions tab's "Run workflow" list
  once `.github/workflows/blueprint.yml` exists on the default branch
  (`master`); until then the workflow only runs via `push`/`pull_request`.

Once a `deploy` run succeeds, the doc links throughout this blueprint resolve
against `/docs`, and the "have not been generated or published" part of the
`\lean{}`-links caveat in Limitations above no longer applies -- though
`api-docs`'s `continue-on-error` means any given deployment's `/docs` should
still be treated as best-effort, not guaranteed present or current.
