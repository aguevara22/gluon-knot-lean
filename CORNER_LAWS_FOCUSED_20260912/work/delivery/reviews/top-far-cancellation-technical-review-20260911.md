# Unary isolation and conditional top cancellation: technical review

Independent technical review of root-authored TopFarCancellation by another agent of the **same currently available model**. This is **not the stronger-model statement-fidelity approval requested by the user**. I authored the earlier SelectedCutRefinement and original PositionalCutDecomposition helpers; root's independent reviews of those dependencies are bound below. This report does not self-review those constructions. No kernel/build/audit or frozen-file/map edit was performed.

Read both complete statements/proofs, canonical UnaryComposition, and the exact top decomposition used in source `pf:formal-cancellation` (`reference/SM/sm-2-amplitude.tex:860–936`). No defect was found in the stated algebraic helper scope.

`topFar_single_summand` uses the actual `IntervalComposition.single I`. Its physical selected-cut product is reindexed to Fin0 and hence equals one, including when the supplied U values are zero. The sole actual part is I by canonical single_product, so the one remaining gap sum is the complete positional H sum on I. Its child array is still exactly X, and fixed-outer intervalFarCutWeight still uses I. The proved positional/far-transform identity gives precisely farTransform H X I. It neither omits the unary child nor replaces the inner sum by one.

`farTransform_add_eq_of_nonunary_zero` first rewrites by the complete H+U top decomposition. For every composition different from single I, positive part count and canonical uniqueness of a one-part composition prove at least two parts. The supplied hzero therefore kills every other actual summand. The sum's selected singleton is always present in the finite universe; its value is the preceding unary identity. This covers all selected-cut sets and all inner gap compositions, including empty selected sets, empty inner cuts and one-leaf intervals, without division or a nonzero-weight assumption.

The hypothesis is explicit and substantial: **every nonunary full contribution** (selected U product times all H gap sums) must vanish. It is not assumed to follow merely from U being supported on silent positions. Actual geometric discharge, inverse constancy and full-root reversed output are separate required work; this helper is not itself source formal cancellation. The statement remains valid for arbitrary H,U,X and any CommRing with invertible two, including zero divisors.

Root second49406 exited0. All 6/6 receipt-bound hashes match and all four embedded bodies occur exactly once. Both traces contain only propext, Classical.choice and Quot.sound, with no error, sorryAx, native_decide or Lean.ofReduceBool marker. Comparing first40707 body/prototype shows only the explicit Fin0 product proof plus the missing canonical UnaryComposition import; both theorem types are unchanged. The failed evidence remains preserved.

SHA-256 bindings:

| File | SHA-256 |
|---|---|
| `work/checks/TopFarCancellation.body.lean` | `fd57112cda0a7cfbfb7f15d91d224723e60f5ae5a7f9032f585aeeccae882a44` |
| `work/checks/TopFarCancellation.prototype.lean` | `4bc2719ba55447f35aad82ad4b85245cf8d8908156f929de84dd336c4e953c16` |
| `work/checks/TopFarCancellation-second-kernel.log` | `7b1aad23a0cc313d028cb56eb9a304da0a8761201c4f048c64da518346291592` |
| `work/checks/TopFarCancellation-prototype-result.json` | `0a290b8f52d5d50ab286dfd00e9be6c21ade338fb6a4759349953f9623cdc9dd` |
| `work/checks/TopFarCancellation-first-failed.body.lean` | `c00c4d5a63c743bbf6aa5061820a64885b5e76dfd77b543f8513aafb4fe30a63` |
| `work/checks/TopFarCancellation-first-failed.prototype.lean` | `378a0595be03fe5f23abaeeed152413741f56fdcfba1df6e93887cfab6cbddec` |
| `work/checks/TopFarCancellation-first-kernel.log` | `81d66e1a9e4b0f2a3d4f04799118740eade5ce2b5f412c217e188ac6b4780291` |
| `work/checks/TopFarDecomposition.body.lean` | `2cc1eb1027a60fd62c29ba50c6e933c3ea3c84ec524b550fda66a3be4cdf4231` |
| `work/lean/SM/UnaryComposition.lean` | `2ab97aefcf1216934b9e44ce6897c73e70d6d16487a4f82123e68d415c47176d` |
| `work/reviews/selected-cut-refinement-technical-review-20260911.md` | `fdc5706133aabcdd77ca0c7419269866b257b8c77377f9cc2336904738af1c13` |
| `work/reviews/positional-cut-decomposition-core-review-20260912.md` | `5fd3bb4bf8bdff142159fbe4e01d0b81485e85efe886f5cc9447c13af94301e0` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Stronger fidelity and source acceptance remain pending. Accepted progress unchanged: 39/192 (20.3%); targets 0/8.
