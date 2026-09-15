# Contact half-root map — technical review

2026-09-11. Independent review by another agent of the **same currently available model**. This is **not stronger-model statement-fidelity approval** and supplies no original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8. Root authored these six declarations; this reviewer ran no Lean kernel or build.

Compared `contactHalfRoots`, its three branch theorems, `contactHalfRoots_spec` and `contactHalfRoots_vertices` with `def:induced-roots`, `reference/SM/sm-2-amplitude.tex` lines 387–394, and the actual halves in `sm-1-polygons.tex` lines 1230–1240. No mathematical, definition or domain defect was found.

The product type fixes the prescribed order: first component belongs to `firstHalf`, the source λ₁, and second to `secondHalf`, the source λ₂. The map has exactly these rows:

| Original root | First-half root | Second-half root |
|---|---|---|
| a | -1, the closing edge a→M | 0, the opening edge M→a+1 |
| inherited in M through a-1 | its actual child label i, with i ≠ -1 | 0 |
| inherited in a+1 through M-1 | -1 | its actual child label i, with i ≠ 0 |

The casts in the definition recover these exact child labels, not just labels with an equal vector. `contactHalfRoots_first` and `_second` use the respective injective parent-index maps to exclude a, the checked arc characterizations to choose the correct branch, and the exact cyclic offset to recover i from its representative. The specification theorem applies the exhaustive root partition and includes the actual parent-label equality in each inherited case. The separately reviewed partition proves the rows disjoint; no named half is swapped.

`contactHalfRoots_vertices` proves **ordered pairs of actual points** for both output roots, simultaneously. At g=a its first pair is (P a,P M), and its second is (P M,P(a+1)). For a first-arc root, the first pair is (P g,P(g+1)), using `firstHalfIndex_next` for every i ≠ -1; the second is the opening pair. For a second-arc root, the second pair is (P g,P(g+1)), using `secondHalfIndex_next` for every i ≠ 0; the first is the closing pair. The second successor theorem explicitly handles its last-to-zero wrap, so the edge ending at M is retained. The first-arc edge starting at M and the other endpoint-adjacent roots are included too. Thus neither mere vector equality nor equality of unordered endpoint sets substitutes for the source directed root.

The map and branch/specification theorems are valid for all nonzero n and require no geometry. The endpoint theorem assumes precisely `3 ≤ n` and `ContactSeparated M a`, and is valid for every actual tuple P. Those source separation conditions imply the required child arities; there is no extra caller lower bound, genericity, contact-interiority, emptiness or affine assumption. Specializing P to the wall center therefore gives the exact source map. The general algebraic map remains defined in degenerate small cases, but those cases are not passed off as source polygon amplitudes.

These results establish the physical root map, not the S7 amplitude product or any contraction tuple equality. The latter still require their own complete tuple proofs. No circular wall-law premise or root-independence assumption appears.

## Frozen evidence

All **4/4** receipt hashes match current bytes; both listed bodies occur verbatim exactly once in the prototype. Root's first session **90785** exited 0. The first five declaration traces use only `propext` and `Quot.sound`; the endpoint theorem additionally uses `Classical.choice`. The log contains no `error:`, `sorryAx`, `native_decide`, or `Lean.ofReduceBool`.

Principal SHA-256 bindings, relative to the focused root:

| File | SHA-256 |
|---|---|
| `work/checks/ContactHalfRoots.body.lean` | `58a657d17361ddf4eba802a2367c9a0f4a27006c0cc26086374cb2b4cb188cfa` |
| `work/checks/ContactHalfRoots.prototype.lean` | `249cf99f98d1a4676fff8843aa342d8d13eb6183ce79bfcf334dffed5a2a81e6` |
| `work/checks/ContactHalfRoots-first-kernel.log` | `7f7fb8b726688252e94488248177d306fda28f3370f64ca8494ce7881c7474d2` |
| `work/checks/ContactHalfRoots-prototype-result.json` | `071fb9310622f408ad1062290f1a9a7a1e73a6feb80e3933c11d1d3d576db99e` |
| `work/checks/ContactRootPartition.body.lean` | `efecdb4cbb8581ed5fd9a922eaeb66ecfa44d2d2fcd6ae041a2e3f43c4b1504a` |
| `work/lean/SM/ContactHalfSizes.lean` | `801a5afe127b3640e922847d052696e88e2998c4e92bbc8af4b851291c1c1140` |
| `work/lean/SM/ContactHalfIndices.lean` | `137e1b2a30581d4ce11cee87a7b59c60b7cad24f039ee6a822f30559e2446323` |
| `work/lean/SM/ContactHalfTuples.lean` | `10656209764059bc91a9a16cde47b3ec0b136a6d0112e5932a61bb841721a51f` |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

These bindings identify the inspected artifacts without establishing statement fidelity. No proof, frozen evidence, canonical/source file, map or acceptance status was edited.
