# Pure-cut tree response: technical review

2026-09-11. Reviewer: another agent of the same currently available model, independently reviewing the two root-authored response declarations. This is **not the stronger-model statement-fidelity approval requested by the user**, and not source acceptance. I authored `PureCutBoundaryBounds`; this report checks its application, while the root agent's separate `silent-boundary-geometry-technical-review-20260911.md` reviews that authored dependency. No Lean/kernel/build or frozen/canonical/map edit was performed.

**Finding:** no mathematical or source-domain defect found in `pure_cut_tree_silent_near` or `pure_cut_tree_silent`. They prove the complete root-output silence in `thm:A-R3E(ii)` for pure cuts, with all physical roots and independent side parameters. They do not assert equality of individual open sums at a point-triple wall.

The only geometric input is the actual `PureCutAt i j k` predicate with ambient `3 ≤ n`. Its singleton point-zero support has cardinality three, so the three named labels cannot coincide. `NoConsecutive` and that cardinality derive n at least six. The proof therefore applies `singlePointTriple_vertices_injective` with a **derived**, valid n at least four, obtaining physical distinctness of the central points. It does not infer physical distinctness from singleton support at arity three or impose a new size hypothesis on callers.

For an arbitrary root, `single_triple_boundary_data` sorts the complete unordered support into the unique increasing boundary triple. It transports both physical distinctness and the actual chirotope sign-change predicate, including odd permutations through sign-change invariance under negation. The candidate then constructs affine coordinates from the true collinear points with nonzero direction and all three scalar inequalities. No label ordering, middle-point order on the line, chosen affine data or sign of an epsilon is supplied by the caller.

Both interval gaps are nonleaf, and the critical span is proper, by the exact `NoConsecutive` boundary bounds. Those bounds retain lower position zero or upper position n−1 separately; their simultaneous occurrence would put the two adjacent physical root endpoints in the critical support. Thus incident-root readings and the cyclic seam remain covered. The actual nonzero endpoint displacement gives `wall_epsilon_positive`; this uses the sum of the two line displacements and works for every line order. At least one nonleaf U factor is the zero unit-array value, so the **proper-span** U product is zero. The proof applies that branch of the existing integer single-triple response and multiplies by zero; it never cancels or assumes a nonzero contracted coefficient.

The contracted tuple and its G1/arity witnesses remain those of the actual single-triple response. An identification with another named polygon is unnecessary for a zero multiplier. The proof path introduces no hypothetical tuple equality, center genericity, inverse-coefficient integrality or additional concurrence condition beyond `PureCutAt`.

The near theorem supplies one positive radius for all sufficiently close independently chosen negative/positive parameter pairs at the fixed root. The final theorem consumes this proved premise in `tree_sides_equal_of_local_zero`, constructs an actual local pair, and transports each side's coefficient separately by continuous generic-side chirotope constancy. It concludes equality at **every** independently chosen s and t in the full side interval, without a remaining radius restriction. Its conclusion concerns the complete tree coefficient only, matching the source's explicit limitation on open sums.

Receipt records second root session **73319**, exit **0**. All **38/38** manifest hashes match; all bound bodies occur once in the prototype. Both printed declarations have only `propext`, `Classical.choice`, `Quot.sound`; the successful log has no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool` marker. The preserved first run **55482** lacked the canonical unordered-support import, causing missing `signChanges_neg` and `three_support_predicate` declarations in an embedded dependency. I verified that the body is byte-identical and the sole prototype change adds `import SM.UnorderedWallTriples`. The first failed log is not treated as successful evidence.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/PureCutTreeResponse.body.lean` (also preserved first body) | `9fc9c04cdc1d68c85753c66bec09d2f3ab17b2df766ecac4d984772afcf5872f` |
| `work/checks/PureCutTreeResponse.prototype.lean` | `8318d855d5ffee416d2c800cb058888d9877f29bdb37a348331abcc955db2b43` |
| `work/checks/PureCutTreeResponse-second-kernel.log` | `79ded5cee06e115e3fcdc533f4088c16433b3809ab7668d8ca67c2236829d6b2` |
| `work/checks/PureCutTreeResponse-prototype-result.json` | `128d32efa168547fb167701871b0a053bd041f460aba5433e7323b0948123aee` |
| `work/checks/PureCutTreeResponse-first.prototype.lean` | `042bf961619879f1dc890eacfd78a3b0fe9336e858624b951df0caea6d090180` |
| `work/checks/PureCutTreeResponse-first-kernel.log` | `e42da63041384addc719c248dac440882fa46afbfd03766cca3c27bfba4591fb` |
| `work/checks/PureCutBoundaryBounds.body.lean` | `3283ab71d8cd9074e3eccb36ea5809a6a13e8bd0ee927ab91257f8aa8ae2d5c9` |
| `work/checks/UnorderedCriticalTriple.body.lean` | `985956064e7fa879661ee9a144753639f56a73cf48741d1e8e503cf5a201c110` |
| `work/checks/CriticalAffineData.body.lean` | `eac6a342f4efb6e55da13322feab4e3f685e63828440ccc820297813971b5be1` |
| `work/checks/SilentIntegerFactors.body.lean` | `52225243bc48a9a04c37f1fe92c52f28819033adc222a2d41a43fde9e6be3552` |
| `work/checks/GermTreeEquality.body.lean` | `23ae56adbfd3faec1538d1ba80c8471b33b31d62afb85d5d77e6ef8daeb9bc0d` |
| `work/checks/IntegerSingleTripleResponse.body.lean` | `227462b1bbe0456ce83377b04e35bc6d78ef8aed641200b783f83f9779d4d130` |
| `work/lean/SM/PureCutIndices.lean` | `6ba45cb5653d6d5a768729309e8bb632b73ff1ef3525d347d267c6e06037f426` |
| `work/lean/SM/SinglePointTriple.lean` | `5930e77bd3eb05d371b5226c226d9caa464f99d0be48038b1154d02c623dc2c8` |
| `work/lean/SM/UnorderedWallTriples.lean` | `99cb9bfe32248b00e9ab5890e68a8ff5865b8038958d04b607d7b64b623041e1` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

The receipt binds the remaining verified files. Comparison concerns `thm:A-R3E(ii)`, particularly the pure-cut paragraph at lines 634–651, and the single-triple proper response. Passing evidence does not establish stronger fidelity approval; acceptance remains **39/192 (20.3%)**, targets **0/8**.
