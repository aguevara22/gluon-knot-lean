# Vertex-edge source response: technical review

2026-09-11. Reviewer: another agent of the same currently available model, independently reviewing the root-authored `SM.WallGerm.vertex_edge_tree_law`. This is **not the stronger-model statement-fidelity approval requested by the user** and does not accept `thm:A-S7`. No Lean/kernel/build, frozen-proof edit, canonical change or acceptance-map edit was performed. My authorship of the affine-sign, boundary-position and integer-factor dependencies is disclosed; the root agent supplies their independent review. This report checks the final theorem and its use of those dependencies.

**Finding:** no defect or remaining local-radius, root-case or sign-normalization gap found in this candidate for the source vertex-edge tree law. This is the tree coefficient law, not the final corner theorem or an assertion about an R/BRIDGE quantity.

The theorem's hypotheses match the source simple vertex-edge domain: an actual continuous `WallGerm`, `3 ≤ n`, and `VertexEdgeAt M a`. The latter is the printed separation, singleton point-zero support, empty concurrence set, relative-interior contact and sign change. Source bigon and sliding are the equality/inequality alternatives for the two neighbour signs, so `VertexEdgeAt` covers both without adding either as a premise. Child bounds follow from separation; no additional n restriction, caller affine coordinates, generic central parent or nonvanishing coefficient assumption is imposed. In particular, small sizes excluded by separation are excluded by the source itself.

The conclusion uses the actual integer `treeCoefficient` of the positive side minus that of the negative side at arbitrary physical root g. Its factors are the first and second halves of the centre in the source's prescribed order, at `contactHalfRoots M a g`. This is the previously proved directed root map: the contacted edge gives first-half closing root −1 and second-half opening root 0; the two inherited arcs retain the old root in the appropriate half. The whole tuple and equality-of-arity proofs underpin the contractions, so the coefficient identities do not rely on endpoint equality alone. The G1 witnesses and child arities are derived. The source's full genericity of these same halves is also supplied by the existing `vertex_halves_children` theorem under these identical hypotheses, although `treeCoefficient` itself only requires G1.

`contactSign` is defined as chi(a,a+1,M) on the negative side at `sideBase`, independently of g. `contactSign_eq_at` makes this its value at every negative-side parameter. `vertex_contact_signs` derives its nonzero value and the opposite positive-side sign from the actual local sign-change predicate and continuous generic side families; it is not an assumed orientation convention.

The final proof takes the local signed response and constructs the specific positive parameter q=δ/2. Positivity and δ≤radius prove that q lies in the side domain and that both −q and q are strictly within the response radius. Substituting the two actual side signs into the doubled far-sign jump makes the left side twice `contactSign`. Integer arithmetic cancels the common factor two and proves the selected d equals `contactSign`. There is no integer half-division convention or loss of information through a nonfaithful coefficient ring. The earlier integer response uses rational specialization and integer cast injectivity; no integrality of inverse coefficients is asserted.

Although this intermediate application uses one equal-distance pair, the conclusion quantifies **independently over all** s and t in `(0, radius)`. For the positive side, `generic_family_chi_constant` identifies every chirotope at q and t; `treeCoefficient_eq_of_chi` therefore identifies their complete tree coefficients. The negative side is transported separately from q to s. The side families are continuous maps to generic tuples on a preconnected real interval, and the coefficient invariance is proved from all near/far signs in the tree expression. This step does not assume the requested wall equation or cross the singular centre. `sideTime false` evaluates at −s and `sideTime true` at t, covering every negative/positive punctured pair. No radius restriction, synchronized-time condition or selected-side witness remains in the theorem statement.

Compared with `sm-2-amplitude.tex`, `thm:A-S7` at lines 520–586 and induced roots at lines 386–394, the conclusion is the exact source sign times first-half amplitude times second-half amplitude, with all physical roots and both subtypes. The three source cases and exact factors were checked separately in `contact-signed-response-technical-review-20260911.md`. No additional source assertion within this theorem was identified as untranslated; stronger fidelity approval and source acceptance nevertheless remain separate and pending.

Receipt records first root session **96621**, exit **0**. All **49/49** manifest hashes match, with every bound body embedded exactly once in the prototype. The log prints the expected theorem and only `propext`, `Classical.choice`, `Quot.sound`; no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool` marker occurs. Hashes and successful checks do not themselves prove source fidelity.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/ContactSourceResponse.body.lean` | `4ab1650111909f9ee0dbb406db7a5e431240c510331befaa148ca1ccbcece874` |
| `work/checks/ContactSourceResponse.prototype.lean` | `6e43fc42a0877b487a3e39dae72fc46d0ae9323b0e30a24c58f3470874ee1fb2` |
| `work/checks/ContactSourceResponse-first-kernel.log` | `5485250363aa67d4c033b16dc9b4e822c4ed8b14d210870b87063af5308e0203` |
| `work/checks/ContactSourceResponse-prototype-result.json` | `7808a857d7acec4746132d1aaadfa8cb42fbf64ad36f0312ed2ef26be18d5083` |
| `work/checks/ContactSignedResponse.body.lean` | `9f11f6f9e4c2a99728045722a1488f1f9bb11555e697d5cd865d0b368aab8d0c` |
| `work/checks/ContactHalfRoots.body.lean` | `58a657d17361ddf4eba802a2367c9a0f4a27006c0cc26086374cb2b4cb188cfa` |
| `work/checks/IntegerSingleTripleResponse.body.lean` | `227462b1bbe0456ce83377b04e35bc6d78ef8aed641200b783f83f9779d4d130` |
| `work/lean/SM/NamedWallPredicates.lean` | `828a9c5dc91455d6d171a01c0ece96901708dd9720f3a379563850b0a61e7513` |
| `work/lean/SM/NamedWallSides.lean` | `3d9b506ccb943d47e4ae169ed554952ca81cb57ac0ee081c2917acbd0ee67ea1` |
| `work/lean/SM/WallGerm.lean` | `fca24dab7111c6b6f404b075ab4e1b8c20d2fb48083565b6ba89758ebf684f9b` |
| `work/lean/SM/ChamberPaths.lean` | `cabb36d739563036aeee39c1a7bc0cf925a6259c5f90a22ecd61c9e2e737d44a` |
| `work/lean/SM/TreeCoefficient.lean` | `d070e70dfbb61e036641f0d5fac4adae83fd1cadfe22f3ce2ffd8c8e1de9ab06` |
| `work/lean/SM/Children.lean` | `3057e5b6313378d192d08c5892b453a2206212a95c3dad1803c0448a91957e1c` |
| `work/lean/SM/ContactHalfInteriors.lean` | `aa0713f0d61148382a2cacc31b7ef9144ee962779a422aee5cdf6547143b55c7` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |

The receipt hash binds the remaining verified evidence entries. Acceptance remains **39/192 (20.3%)**, targets **0/8**; this review changes neither count.
