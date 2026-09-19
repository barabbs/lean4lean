# Review data

Evidence base for the blueprint's review chapters (`contrib-iota.tex`,
`contrib-trproj.tex`, `status.tex`, and every chapter's review-notes section).
Produced by AI reader and reviewer agents working from the compiled
environment and git history, then adversarially fact-checked by further
agent passes (`reviews/factcheck-*.md`, `reviews/finalize-notes.md`); treat
as a heavily-checked draft, not independent peer review. The `.tex` chapters
are normative, not these files.

Top level: `thesis-map.md` maps the thesis to the repo; `contrib-{iota,trproj}.md`
inventory what each branch changed; `claims-{iota,trproj}.md` verdict specific
PR/handoff claims (TRUE/FALSE/PARTIAL/UNVERIFIABLE); `hygiene-review.md` is a
dead-code/documentation review of the full diff; `unused-contrib.md` is a
dead-declaration census (see caveat below); `upstream-comparison.md` diffs
against `digama0/lean4lean`; `census.md` and `sorry-grep.md` are the
human-readable axiom/sorry census (machine form: `decls.tsv`,
`all-constants.tsv`); `ISSUES.md` backs `status.tex` section 4; `reader-summaries.md`
and the 14 `theory-*`/`verify-*`/`kernel-impl.md`/`experimental-*.md` files are
one narrative per chapter group. `reviews/` holds one fact-check per chapter
plus `*-finish-notes.md` follow-ups and the final cross-check `finalize-notes.md`.

Caveats: some files (mainly `reviews/finalize-notes.md`) cite absolute
`/tmp/claude-*/.../scratchpad/...` paths from the session that produced them;
these no longer exist, read them as historical pointers only. `unused-contrib.md`
was regenerated after a scratch wipe and its numbers do not match the original
run: 875 contributed declarations / 31 zero-reference in the original vs. 889 / 78
here, a gap its own recovery note traces to `decls.tsv` now tagging some
`instance`s as `def`, not to new dead code; the original 31 findings all hold.
