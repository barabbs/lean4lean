# New code issues noted while completing proj

- Lean4Lean/Tests/IotaShape.lean:86 - the recs_elim check spells the recursor's extra universe as `param 0`, i.e. assumes the fresh universe sits at index 0 of `levelParams`; that is how Lean generates recursors but nothing checks it.
- Lean4Lean/Tests/IotaShape.lean:295 - `checkBlockRejected` only demands that *some* block clause fail; the docstring's expectation that a nested block fails `ctors_positive` and `recs_over_block` in particular is pinned in no test.
- Lean4Lean/Tests/IotaShape.lean:454 - the whole battery is one ~150-line `run_meta` block, so a failure reports only the first mismatch and every later assertion (including all remaining negative controls) is never reached.
- .github/workflows/ci.yml:25 - the comment claims `Lean4Lean.Tests` is among the `defaultTargets`, but lakefile.toml:2 lists only `Lean4Lean`, `lean4lean`, `Lean4Lean.Theory` and `Lean4Lean.Verify`; the tests are in fact built by the separate `lake build Lean4Lean.Tests` step.
- Lean4Lean/Tests/IotaShape.lean:595 - `checkAll` is run on forty-eight type formers, not the forty-one stated in the analysis node map / narrative; the chapter states the code's number.
