# Contact signed response: technical review

2026-09-11. Reviewer: another agent of the same currently available model, reviewing four root-authored declarations. This is **not the stronger-model statement-fidelity approval requested by the user**, and does not accept the source claim. No Lean/kernel/build, frozen-file edit or acceptance-map change was performed. I authored `ContactAffineSigns`, `ContactBoundaryPositions` and `ContactIntegerFactors`; their application is checked here, while their independent proof review belongs to the root agent.

**Finding:** no defect found in the four signed-response statements or their assembly. They are intermediate local responses: they retain a positive radius and an existential sign fixed before both side parameters. Identification with the source contact sign and removal of this radius belong to the separately reviewed `ContactSourceResponse` theorem.

The source is `thm:A-S7` and its proof (`sm-2-amplitude.tex`, lines 520–586), using the induced half-root map at lines 386–394. The caller supplies only `3 ≤ n`, an actual `WallGerm`, and `VertexEdgeAt M a`; the individual inherited-arc lemmas additionally select their actual root range. `VertexEdgeAt` contains the source separation, singleton point-zero support, empty concurrence set, interior contact and sign change. Neither the construction nor the theorem assumes `FlatAt`, `CuspAt`, chosen affine data, a special neighbour-side configuration or a generic central parent. The separation bounds derive both child arities at least three (and imply n at least five); no additional lower-size restriction is imposed. Thus both bigon and sliding types are covered.

Write D for `contactDistance M a`, u for `(g-M).val`, and r for the derived affine coordinate of M between a and a+1. The following source specializations are actually used:

| Root case | Ordered coordinates; epsilon pair | Actual factor and contraction |
| --- | --- | --- |
| g=a | (1,r,0); (+,+) | Full span. Gaps have n−D−1 and D leaves, both nonleaf. U product is zero. V product is second-half root 0 times first-half root −1. Scalar commutativity restores the prescribed first/second half order. |
| u<D | (0,1,r); (+,−) | Proper span. Left gap is a leaf; right gap has n−D−1 leaves and integer output second-half root 0. The complete contracted tuple gives first-half root u. |
| D<u | (r,0,1); (−,+) | Proper span. Left gap has D leaves and integer output first-half root −1; right gap is a leaf. The complete contracted tuple gives second-half root `(g-a).val`. |

The affine coordinates, nonzero direction and all three coordinate inequalities are derived from actual interior contact. Each cut's exact support supplies the single-triple hypothesis. Each ordered critical triple is a cyclic permutation of (a,a+1,M); the reversed far sign is consequently minus that chirotope. The doubled sign equation in the conclusions therefore has the source orientation: minus the positive-side chi plus the negative-side chi equals twice the selected integer sign. No unproved reversal or half interchange is used.

The nonleaf/leaf factor lemmas inherited from `CuspIntegerFactors` have purely algebraic hypotheses, with no cusp or flat predicate. Their use here introduces no geometric restriction. All B values are complete integer gap outputs with derived G1; the proper branch uses the proved full contracted-half tuple and size transport, not merely endpoint equality. This path does not assert integrality of inverse coordinates. The underlying integer single-triple response specializes faithfully through the rationals and integer cast injectivity.

For each fixed root, one sign in {−1,1} and one common positive radius precede the universal quantification over independently chosen negative and positive parameters. The negative/positive conditions supply the punctured genericity witnesses. No equal-distance condition remains, and the positive radius gives actual pairs, preventing an empty conditional conclusion. The all-roots lemma first splits g=a, then u<D, and derives D<u in the remaining case: equality u=D would force g=a by injectivity of the ZMod representatives and subtraction. This covers both inherited endpoint roots and the cyclic seam. The stated `contactHalfRoots` is the map already proved to preserve the actual directed endpoint pairs.

Receipt records first root session **65026**, exit **0**. All **48/48** manifest hashes match; every bound body occurs exactly once in the prototype. The log prints the four expected declarations and only `propext`, `Classical.choice`, `Quot.sound` for each. There is no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool` marker. This evidence supports the frozen candidate, not stronger source approval.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/ContactSignedResponse.body.lean` | `9f11f6f9e4c2a99728045722a1488f1f9bb11555e697d5cd865d0b368aab8d0c` |
| `work/checks/ContactSignedResponse.prototype.lean` | `210283ddc70f6a173c7a37d426ecdaaa1efd8ce10c664f4009cb9d2ed3cc6f41` |
| `work/checks/ContactSignedResponse-first-kernel.log` | `b5491ed6dca6208945465540fd8fae1e357ad9a5eb0be41150253e7dabc40920` |
| `work/checks/ContactSignedResponse-prototype-result.json` | `2fe6746493faa5df29456aae47d15f6eb604e21ac434a21e268b64bd49b1c895` |
| `work/checks/ContactAffineSigns.body.lean` | `eb17b5a65fb80e38549b9c7be114cb000caf8469e6dc3a43265105e5ab525b47` |
| `work/checks/ContactBoundaryPositions.body.lean` | `61d797a366cb8db5312ac0739037da47361b87eed4ed50e786ee3b72b7c2c4b7` |
| `work/checks/ContactIntegerFactors.body.lean` | `406f96eee710116768518910df04615235b4ee4842106b1d4d847dfd3fcb27e7` |
| `work/checks/CuspIntegerFactors.body.lean` | `f34d8db440519782d6e12a16afe9e2146a5ff3d8288fa0267378c800f832429d` |
| `work/checks/ContactGapWords.body.lean` | `27891ffab2f368aa0afe2ffb333d14b17dc50a2aa9aec7cc457abc4bad50087d` |
| `work/checks/ContactContractionCoefficients.body.lean` | `b205652841dfed1f37a9ddf77d8f41e2fe033ef221f4b8af945407670f06d328` |
| `work/checks/ContactHalfRoots.body.lean` | `58a657d17361ddf4eba802a2367c9a0f4a27006c0cc26086374cb2b4cb188cfa` |
| `work/checks/IntegerSingleTripleResponse.body.lean` | `227462b1bbe0456ce83377b04e35bc6d78ef8aed641200b783f83f9779d4d130` |
| `work/lean/SM/NamedWallPredicates.lean` | `828a9c5dc91455d6d171a01c0ece96901708dd9720f3a379563850b0a61e7513` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |
| `reference/SM/sm-1-polygons.tex` | `8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00` |

The receipt hash binds the remaining verified manifest entries. Stronger statement-fidelity approval remains pending; acceptance is unchanged at **39/192 (20.3%)**, targets **0/8**.
