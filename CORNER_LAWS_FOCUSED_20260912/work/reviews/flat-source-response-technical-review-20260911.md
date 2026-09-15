# All-root and final flat response — technical review

2026-09-11. Review by another agent of the **same currently available model**. This is **not the stronger-model statement-fidelity approval requested by the user**, and supplies no original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8.

Scope: the two declarations in `FlatAllRootResponse`, `nearby_same_chirotope` in `GermNearbyChirotope`, and `flat_right_minus_left` in `FlatSourceResponse`. No mathematical defect was found in these four declarations or their assembly. The orientation helper in `TurnResponseOrientation` was authored by this reviewer and checked/reviewed separately by root; this report reviews its application, **not its proof as independent reviewer evidence**.

## Domain, roots and orientation

`flat_signed_response_all_roots` splits on exactly `incident j g`, applying the checked incident all-size response or the nonincident response. The incident branch already covers g = j-1 and g = j. Thus all physical roots are covered, including the four-vertex case. Its only geometric caller input is the actual `FlatAt` predicate: the source lower arity bound, singleton unordered zero triple, empty concurrence set, strict betweenness and local turn sign change. Parent arity n+1 is just a parameterization of every source arity at least four; child n is at least three by that bound, so `[NeZero n]` is implied by the source size condition and imposes no extra geometric restriction.

The response chooses one d in {-1,1} and one positive radius before both independently quantified negative/positive parameters. The signed turn difference and coefficient difference use the same d and pair. Neither symmetric sampling nor caller-supplied affine coordinates appear. The center output is the actual integer `treeCoefficient` of `deleteVertex w.center j`, with its proved G1 and exact root `fusionIndex j g`. In the incident cases this is the fused edge; otherwise it is the retained edge. The complete tuple identifications, not just endpoint identities, were checked in the separate incident/nonincident reviews.

`flat_right_minus_left_near` applies the orientation helper with F equal to the actual integer coefficient at each punctured parameter and C equal to that deletion coefficient. F is assigned 0 at the center only to make it a total function. Every use of F in the response and conclusion carries a proved nonzero parameter, and simplification selects its coefficient branch; the center placeholder cannot enter the equality. The helper's required fixed sign, common radius, independent-pair response, actual right turn -1 and left turn +1, puncture and proximity premises are all supplied. The resulting sign is **right minus left equals positive C**, as printed in `thm:A-S3`; no residual d, doubled coefficient, or unspecified orientation remains.

## Removing proximity without losing hypotheses

`nearby_same_chirotope` first represents an arbitrary punctured parameter by `sideTime b r`. It constructs a new parameter on that same Boolean side at distance δ/2. Positivity and δ ≤ radius put δ/2 strictly inside the actual open side interval, and the new parameter is nonzero and strictly closer than δ. This uses no extension of the curve, differentiability, or assumption about transverse speed.

The equality holds for **every** triple of labels. The supporting `generic_family_chi_constant` is proved from continuity of the generic chirotope into its discrete sign type and preconnectedness; `GermSides` supplies connectedness of the whole interval (0,radius). Genericity and continuity of the side tuple come from the actual `WallGerm`. Consequently the comparison reaches the original parameter anywhere in the punctured germ, not merely a smaller unstated interval. Repeated-label triples are included.

`flat_right_minus_left` constructs the close representatives independently for the supplied right and left points. Their turns are preserved by the particular neighboring triple. It applies the near response and then transports each coefficient back with the proved `treeCoefficient_eq_of_chi`, which unfolds the actual rooted tree sum and its sign-dependent ordinary/root weights. Thus coefficient constancy is not assumed as a premise or deduced circularly from the desired flat law. Genericity at all four evaluations is obtained from `generic_punctured`.

The final theorem has **no proximity restriction**: it covers every independent punctured pair in the full germ parameter interval with the source right/left turn values. These selectors are nonvacuous under `FlatAt`: the existing `flat_named_sides` proves one side has turn -1 everywhere and the opposite side +1 everywhere. The statement is the rooted, labelled representative formulation of the source side-value equation; it does not assert the equality at the nongeneric center or outside the germ domain.

The compared source is `sm-2-amplitude.tex` lines 395–452 (`thm:A-S3` and its three root cases), the physical deletion definition at 380–386, and `sm-1-polygons.tex` lines 653–668 and 710–718 (germ/side and flat predicates). No flat-law conclusion was added as a premise. No unhandled flat branch or additional source hypothesis was found in this aggregate. This does not approve the entire source-to-formalization chain, resolve the separate original shift-scope issue, or accept `thm:A-S3`.

## Frozen evidence

All **46/46** all-root receipt hashes and **48/48** final-response receipt hashes match current files. Every listed body appears verbatim exactly once in its respective prototype. Root's first sessions **58448** and **25627** exited 0. Their logs print the respective two declarations, each depending only on `propext`, `Classical.choice`, and `Quot.sound`; neither log contains `error:`, `sorryAx`, `native_decide`, or `Lean.ofReduceBool`. This reviewer ran no Lean kernel or build. Receipt hashes bind the complete listed manifests; principal SHA-256 bindings follow.

| File | SHA-256 |
|---|---|
| `work/checks/FlatAllRootResponse.body.lean` | `9bf291f627d0b0155017b19db06b923f122aa1bc04334b7ade1396a4f1fe0e90` |
| `work/checks/FlatAllRootResponse.prototype.lean` | `a1bd4b5732833f73f3696b73585be2dde90f5210b9e30e49fca337f271a1e4d8` |
| `work/checks/FlatAllRootResponse-first-kernel.log` | `fd80b26b28a29e5795fbe0299332b5b75e8961f3a394aab9631ab601546c7860` |
| `work/checks/FlatAllRootResponse-prototype-result.json` | `d80c9a484276b33ff3fd29c6a314fcd25b37ebdf03131021e7200c3b824398e1` |
| `work/checks/GermNearbyChirotope.body.lean` | `2f821bb9f085ac543e1b1d0791cedfc8846e2a5a125e087acab1a88648eed1e2` |
| `work/checks/FlatSourceResponse.body.lean` | `9805987c03dd2d412f6191d5b67d2545fc107e770e8f97a647038087b1de7609` |
| `work/checks/FlatSourceResponse.prototype.lean` | `16087e1546a58801c7129cd83a6edc30b978ce0b65f1543dbcf8d165539f0715` |
| `work/checks/FlatSourceResponse-first-kernel.log` | `c2b264af7a6bca002152f7d5033005278fb510225a7621f385671728ff5d7870` |
| `work/checks/FlatSourceResponse-prototype-result.json` | `e3f0fae2c23d7475bf2e168c61c07f861cb3a662e9ad100d5afb1797ea9e84a0` |
| `work/lean/SM/ChamberPaths.lean` | `cabb36d739563036aeee39c1a7bc0cf925a6259c5f90a22ecd61c9e2e737d44a` |
| `work/lean/SM/GermSides.lean` | `a95418d15b11a300c5e6a88cbb43ecd9877b5fd061dab754e2efc19eac625d0a` |
| `work/lean/SM/TreeCoefficient.lean` | `d070e70dfbb61e036641f0d5fac4adae83fd1cadfe22f3ce2ffd8c8e1de9ab06` |
| `work/lean/SM/WallGerm.lean` | `fca24dab7111c6b6f404b075ab4e1b8c20d2fb48083565b6ba89758ebf684f9b` |
| `work/lean/SM/NamedWallPredicates.lean` | `828a9c5dc91455d6d171a01c0ece96901708dd9720f3a379563850b0a61e7513` |
| `work/lean/SM/NamedWallSides.lean` | `3d9b506ccb943d47e4ae169ed554952ca81cb57ac0ee081c2917acbd0ee67ea1` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |

Hashes and successful kernel evidence identify checked artifacts; they do not establish source fidelity. No frozen body, canonical/source file, map, or acceptance status was edited.
