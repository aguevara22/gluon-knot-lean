# Flat affine coordinates and signs — technical review

2026-09-11. Independent review by another agent of the **same currently available model**, **not stronger-model statement-fidelity approval** and not original-source acceptance. Progress remains 39/192 accepted (20.3%), targets 0/8.

## Findings

No mathematical defect was found in the nine declarations in `FlatAffineSigns.body.lean`, compared with `afr:wall-epsilons` and the three root cases of the `thm:A-S3` proof in `reference/SM/sm-2-amplitude.tex` lines 407–452.

- **The three epsilon pairs are exact.** For the nonincident coordinates (0,r,1), both ratios have positive numerator and denominator when 0 < r < 1. For incoming coordinates (r,1,0), the common denominator is -r; the left numerator 1-r is positive and the right numerator -1 is negative, giving (-1,+1). For outgoing coordinates (1,0,r), the common denominator r-1 is negative; the left numerator -1 is negative and the right numerator r is positive, giving (+1,-1). These are direct evaluations of the existing `wallLeftEpsilon` and `wallRightEpsilon` definitions. Every denominator is nonzero by the stated strict bounds.
- **The affine data are constructed from actual strict betweenness.** `StrictBetween a x b` includes a ≠ b and an actual parameter r strictly between 0 and 1 with the affine point equation. `strictBetween_flat_affine` retains that same parameter and equation, proves the direction b-a nonzero from endpoint separation, and supplies the endpoint coordinates 0 and 1. Reordering these three equations gives the incoming and outgoing coordinate orders. The inequalities r > 0 and r < 1 also provide the distinct scalar coordinates needed by the response theorem; no extra geometric oracle is assumed.
- **The boundary-order predicate is exactly the source combinatorics.** `CyclicTurnBoundaryOrder` contains precisely the three ordered label triples (j-1,j,j+1), (j,j+1,j-1), and (j+1,j-1,j). It is independent of P and imposes no convexity, G1, sign, or wall condition. The previously reviewed boundary-position theorems supply its respective alternatives for all three physical-root cases, including n=4. It does not permit arbitrary odd reorderings.
- **The reversed far sign is the actual negative turn.** `turn` is the neighboring-point chirotope; the existing `turn_det` identifies it with the determinant sign of consecutive edge vectors. `turn_far_cyclic_signs` uses the three established odd-swap identities, yielding the negative of that same turn in each reversed cyclic order. `flat_boundary_chi_eq_neg_turn` substitutes the actual boundary labels case by case. `flat_boundary_geometric_sign` transports this identity through the integer cast used by `geometricBoundaryArray`; no rational factor or orientation convention is silently inserted. The identities also hold at zero, so no punctured-genericity premise is needed for them.
- **The germ transport keeps the source predicate.** `WallGerm.flat_boundary_chi_signChanges` proves equality of the entire real-valued observable with the negative turn observable. It then uses `signChanges_neg`, which unfolds the exact local paired-product sign-change condition and cancels the two negations. Thus all parameter/radius requirements and the same local witness are preserved; no derivative, transversality, or symmetric-point replacement for the eventual response is introduced.

The dependency path is strict affine geometry and chirotope antisymmetry → epsilon/sign identities → negation-invariant germ predicate. No flat response is assumed. These helpers do not yet assemble the tree equation or select the subtraction order of the source right and left sides; that remaining assembly must use right = turn -1 and left = turn +1. They add no narrower source arity or geometric restriction.

## Receipt and hash verification

Root's **first session 53680** exited 0. All **4/4** hashes in its receipt match current bytes. Both listed bodies occur verbatim exactly once in the prototype. The passing log prints all nine declarations and lists only `propext`, `Classical.choice`, and `Quot.sound` (or subsets). It contains no error, `sorryAx`, `native_decide`, or `Lean.ofReduceBool`. Its unused-section-variable warning introduces no new hypothesis beyond the printed signatures. No Lean kernel or build was run by this reviewer.

SHA-256 bindings (relative to the focused root):

| File | SHA-256 |
|---|---|
| `work/checks/FlatAffineSigns.body.lean` | `cae5189896235fe01203b831cb1f390cf315fcd3cbaa42b831ba1ceb0ac9e07b` |
| `work/checks/FlatAffineSigns.prototype.lean` | `ab23424941f3b583c6072facd3b24f6635b1390eaf642c62826407552b06e5d6` |
| `work/checks/FlatAffineSigns-first-kernel.log` | `0b3e4a4a7f244b8990250baf8b6aa8e8a1cff4028d23614e03049815bfac8e9a` |
| `work/checks/FlatAffineSigns-prototype-result.json` | `a55636ddf2ffaf9451c499e71ff6e0e1a6c54881c363f8aa40fc039ce531107e` |
| `work/checks/CollinearGateSigns.body.lean` | `a26b36fbead365ba221a10ec0658fc5d7c6e70462e924f9c4e7d5d5c4cfd4e40` |
| `work/lean/SM/StrictBetween.lean` | `8237f0fbd090fd42b15f62c1436cb3ba7f790e921df48d6a9d6a8e4b80becdce` |
| `work/lean/SM/Chirotope.lean` | `e0225bc712162273f43269ed764ac4849ae8fcd8798245a367d4262858fbf575` |
| `work/lean/SM/GermSignChange.lean` | `18a9abb6b32839d22aabfdba3e45d533ff515aef021adc6efb5337854be0d91a` |
| `work/lean/SM/UnorderedWallTriples.lean` | `99cb9bfe32248b00e9ab5890e68a8ff5865b8038958d04b607d7b64b623041e1` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

Recorded checks and hash agreement bind the reviewed artifacts, without establishing stronger fidelity approval. No frozen Lean body, canonical file, map, or acceptance status was edited.
