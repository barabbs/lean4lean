# New code issues noted while completing trexpr

- Lean4Lean/Verify/Typing/Lemmas.lean:2344 vs :2349 — the json/narrative say AppStack.build sits 'twelve lines above' TrExprS.mkAppList_inv; it is in fact immediately above (build at 2344-2345, the mkAppList_inv docstring at 2347). Corrected in the chapter text.
- Lean4Lean/Verify/Typing/Lemmas.lean:947 — TrExpr.wf takes no hypotheses at all (the witness carries its own typing), unlike TrExprS.wf which needs Ordered env and a well-formed VLCtx; the node map's single statement line elided this asymmetry.
- Lean4Lean/Verify/Typing/Lemmas.lean:1676 — TrExprS.instL concludes a TrExpr, not a TrExprS, because Lean's mkLevelMax'/mkLevelIMax' normalise; the node map's statement did not record the weakening of the conclusion.
