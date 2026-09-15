# Contact contraction labels and tuples — technical review

2026-09-11. Independent technical/source comparison by another agent of the **same currently available model**. This is **not stronger-model statement-fidelity approval** and supplies no original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8.

Root authored the four reviewed declarations in `ContactContractionLabels.body.lean`. This reviewer authored their boundary-position dependency, which root checked and reviewed as nonauthor; the present report does not represent an author's review of that dependency as independent evidence. No mathematical defect was found in the four inspected statements/proofs. This reviewer ran no Lean kernel or build.

## Complete labels and cut arithmetic

The source comparison is with the two inherited-root contraction paragraphs of `thm:A-S7`, `reference/SM/sm-2-amplitude.tex` lines 559–578. Put u = (g-M).val and d = `contactDistance M a`. Each theorem uses the actual source half size, transported through its proved equality with the contracted size. The equivalence preserves both subtraction by one and the natural representative; it is not an arbitrary cyclic permutation or a cast between unequal moduli.

For the first arc, u < d. The child size is d+1, the shift is u, the cut threshold is k=d-u, and the erased count is n-d-1. The proof supplies the required relation u+(k+1)=0 in the child ring. For v=(e i-1).val below k, the expansion keeps v and the shifted first-half representative is v+u+1. For v at or above k, expansion adds n-d-1 and the shifted representative is v-k. The parent cast identities show that both branches label the same original vertex. All natural subtraction bounds are provided before their casts; the proof includes equality at the cut.

For the second arc, d < u. The child size is n-d and the inherited half-root representative is r=(g-a).val=u-d. The threshold is k=n-u and the erased count is d. `secondHalfIndex_range` expresses the entire second half through its consecutive range starting at a+1, including its exceptional zero label. Consequently the shift calculation uses r-1 and the proved relation (r-1)+(k+1)=0. Below the threshold the representative is v+r; at or above it, v-k. Combining these with the two expansion branches gives the actual parent label in every case. The representative r is justified by the checked origin-change formula, rather than assumed equal to an unrestricted natural subtraction.

The generic `zmod_cut_shift_val` used here has only finite-ring and cut-relation hypotheses. Neither it nor the reused contraction definitions require a flat wall or betweenness.

## Roots, endpoint cases and whole tuples

Both label theorems quantify over **every** cyclic child label. At local label zero, v is the child size minus one and falls in the post-cut branch; its expanded position is n-1, so the parent vertex is g. At local label one, v=0 lies before the positive threshold and expands to position zero, giving parent vertex g+1. Thus the local root is the original directed edge, consistently with the independent `contractedWord` endpoint API.

On the first arc, u=0 is included: the shift is zero and the original root starts at M. The other endpoint u=d-1 is also included and preserves the root ending at A. The newly fused edge occupies the half's closing label -1 and runs A→X; the inherited root is never mistaken for that new edge. On the second arc, u=n-1 is included: its inherited label is the last second-half label, and its successor wraps to zero at X=M. The first root of that arc, u=d+1, is included too. The new edge is X→B at second-half label zero, while r>0 identifies an inherited root.

The two tuple theorems use function extensionality and these universal label identities after inverse size transport. Their conclusions are exactly the complete first half shifted by the inherited label u, and the complete second half shifted by the inherited label r. They do not infer tuple equality from endpoints. These are the source surviving polygons with their actual root cuts; no equality between coefficients at different physical roots is asserted or assumed here.

The domain retains n nonzero, `3 ≤ n`, `ContactSeparated M a`, and the relevant strict root-offset inequality. Source separation itself implies d≥2, d≤n-3 and both half arities at least three. No extra source size bound, genericity, affine data or zero-support premise is imposed on these label/tuple identities. P is arbitrary. The coefficient transport and final S7 response remain separate theorems.

## Frozen receipt and repair

All **12/12** receipt hashes match current bytes; every listed body occurs verbatim exactly once in the prototype. Root's second session **78081** exited 0. All four printed traces contain only `propext`, `Classical.choice`, and `Quot.sound`; the passing log contains no `error:`, `sorryAx`, `native_decide`, or `Lean.ofReduceBool`.

First session **73837** is preserved with two ill-typed dependent rewrite motives and four affected `sorryAx` traces. All four statement texts before `:= by` are byte-for-byte unchanged. The only repairs split the `expandPosition_val` rewrite from subsequent rewrites and insert `change` to reduce its Fin projection to the displayed natural conditional before rewriting representatives. The cut branches, indices and domains were not altered.

Principal SHA-256 bindings, relative to the focused root:

| File | SHA-256 |
|---|---|
| `work/checks/ContactContractionLabels.body.lean` | `1f64ec78ee9419379e3fa58af25ad9b53c3e5ccb02323e7a9ad18600d677019f` |
| `work/checks/ContactContractionLabels.prototype.lean` | `646892965640cfd3c5de26b4668f909896300d4033227ef405ec3c9a8d3d2af6` |
| `work/checks/ContactContractionLabels-second-kernel.log` | `b974218aebdeb163d43d375f3d02dfe2a3caf025d5d82cb79e863ccfe540b125` |
| `work/checks/ContactContractionLabels-prototype-result.json` | `b35a5d5b28e33986be3620d4894627377897b2a590ec969634f77c848c92e8e8` |
| `work/checks/ContactContractionLabels-first.body.lean` | `f553f3f6dc539e029606575a86878afc90a46258f7f6a757e2bf296fd02b2092` |
| `work/checks/ContactContractionLabels-first.prototype.lean` | `d04f1ee29c2df530f22dce92a319868fa0a0102c178ac80ae4d2984a68b2b9e8` |
| `work/checks/ContactContractionLabels-first-kernel.log` | `03f361a918e150697b675c31ac563bb5c2f682f9fbdf9bf638fb885f6b1212fa` |
| `work/checks/ContactBoundaryPositions.body.lean` | `61d797a366cb8db5312ac0739037da47361b87eed4ed50e786ee3b72b7c2c4b7` |
| `work/checks/ContactRootPartition.body.lean` | `efecdb4cbb8581ed5fd9a922eaeb66ecfa44d2d2fcd6ae041a2e3f43c4b1504a` |
| `work/checks/FlatContractionArithmetic.body.lean` | `45aa1ca887728c3d32dbf7a0e1df36966894d273d868bf6fc3a4f842eaa7f52a` |
| `work/checks/ContractedGeometricWord.body.lean` | `c020155992147c8a5c79ba7e69d48814491984d42d339e4cb98a56a584a43382` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

These bindings identify the inspected artifacts without establishing statement fidelity. No reviewed proof, frozen evidence, canonical/source file, map or acceptance status was edited.
