# Visible tree continuation: technical and source comparison

2026-09-11. Reviewer: another agent of the same currently available model, independently reviewing five root-authored declarations against source `thm:A-continuation` and `rem:silent-amplitude`. This is **not the stronger-model statement-fidelity approval requested by the user**, nor acceptance of the source claim. No Lean/kernel/build, proof edit, canonical edit or acceptance-map change was performed. The reviewer authored the earlier dependency `WeakCenterSilent`; root supplied its separate independent review. This report does not independently approve that self-authored dependency.

**Finding:** no mathematical or domain defect found in the five declarations or their assembly. `SM.A_continuation` exposes the complete continuation assertion: for each n≥3 and each fixed physical root, there is exactly one integer-valued function on all actual `WeakTuple n`, constant on actual labelled visible connected components and agreeing with the original tree coefficient at every `GenericTuple n`. No additional certificate, regularity, R identity or root-independence premise appears.

`polygonalJoin_joinedIn` uses the actual finite reflexive-transitive chain of closed straight segments. The reflexive case is the constant path at the given point of S; each step concatenates the preceding path with the genuine real segment path whose whole range lies in S. This proves the continuous path needed from the source polygonal-connectivity result, without assuming that any connected set is automatically path connected.

`weak_visible_path` applies the proved `weak_visible_components` theorem to the ambient image of the actual component `connectedComponent P` in the weak subtype. Both endpoints belong to that image, and the polygonal chain remains in it. Mapping component membership to each tuple's weak property gives a path inside the actual weak locus. The canonical image theorem identifies this image with `connectedComponentIn (weakLocus n) P.val`; no larger substitute chamber is used.

`tree_coefficient_visible_chamber` selects that genuine path between the given generic representatives and applies the previously proved arbitrary weak-path endpoint theorem. That dependency constructs the relative-general-position perturbation, retains weak membership, classifies actual shifted simple germs as E/C, and proves their zero response before gluing. Exact path source and target identities transfer both endpoint `GenericTuple` values, so dependent G1 proof witnesses do not obstruct the result. The same root g is retained throughout.

`visible_chamber_has_generic` applies full generic density (both G1 and G2) to the nonempty **ambient open component image**. Its nonemptiness is witnessed by the original weak tuple, even when that tuple has simultaneous silent zeros. The selected ambient point is then recovered as an actual weak representative belonging to the same component. This is the correct use of ambient density on an open set, not an assertion that generic parameters of an arbitrary path are dense.

`A_continuation` chooses one generic representative in each pointed component and defines F using its original integer tree coefficient. The intermediate `hcommon` proves that F has the same value at every generic representative of that component: equality of connected components changes the component base point to the chosen representative, and the preceding coefficient theorem gives the equality. Component equality also places the generic representative chosen at Q inside the component based at P, proving chamber constancy. Taking the original generic point as its own comparison point proves agreement. For any competing G, chamber constancy identifies G(P) with G at the chosen generic representative; generic agreement identifies the latter with the defining integer coefficient of F(P). Function extensionality proves uniqueness on the entire weak subtype. Choice is used only after proving existence, and the argument proves independence of every such choice.

The final domain matches the labelled coordinate-space reading explicitly used in the source continuation proof. n≥3 is retained; `NeZero n` is redundant under that bound. Agreement is required on the whole original generic locus U, as printed, rather than on a caller-selected dense subset. The integer codomain agrees with source `def:treesum`, whose interval sums and rooted output are integer-valued. There is no shrinkage to single silent walls: any weak tuple, including simultaneous silent zeros, is in the continuation's domain.

Source comparison covers `thm:A-continuation` (lines 655–696, including the requested 656–692 range) and its following warning (698–712). The proof supplies existence, chamber constancy, original generic agreement and uniqueness, with the printed openness/density/path argument implemented through proved dependencies. All coefficient evaluations in the construction occur at chosen **generic** representatives. It neither assigns gate values at zero nor claims a polynomial evaluation at simultaneous silent zeros. It proves a separate continuation for each root; equality between different roots, quotient descent, the six-gon warning's numerical example, the later comparison theorem and the subsequent multi-affine lemma are not claimed. No untranslated assertion was identified within the continuation theorem itself in this limited same-model comparison; stronger fidelity review remains pending.

Verified receipt: first root **90683**, exit **0**, all **64/64** manifest hashes match. The exact body occurs once in the prototype. All five successful axiom traces contain only `propext`, `Classical.choice`, `Quot.sound`; no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool` marker occurs in the successful log. Hashes and kernel success support the frozen proof evidence and do not by themselves establish source fidelity.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/VisibleTreeContinuation.body.lean` | `2da035de3fc2da322de9725aa607703aa3e273d18a46f1c20bceec67d4f4d588` |
| `work/checks/VisibleTreeContinuation.prototype.lean` | `60525e3738b1f9af809705ee6f1b08d69deefbd13ca8ea3e80d464f566add717` |
| `work/checks/VisibleTreeContinuation-first-kernel.log` | `3026328f75e6c5cab00987c530e4f4aa1c4b0380f687f8e0e31a0e9dcdc5ed73` |
| `work/checks/VisibleTreeContinuation-prototype-result.json` | `dd3bc02b1bd742aad3cd1b9aa4dd1e58449e3b396d8fc63f17cfff4913d1c55a` |
| `work/checks/TreePathGluing.body.lean` | `326e810eb8199deadf18bef44c54d99b960d1b5fb0774a5d9a99fbafaabf4269` |
| `work/checks/TreePathGluing-prototype-result.json` | `5fb4ab05bcabd7943e37403eda420b36030ab22c4ae54d17a7006c02da00e641` |
| `work/lean/SM/WeakGeneric.lean` | `1a72ebddb4ddb4d72a89f14a5fede9badc3dbed095a972f6dd1b85db30789b22` |
| `work/lean/SM/WeakOpen.lean` | `d529ddd96240311708fe3a840c9fb4cf2692764943435b77dae59e5c56b79bd5` |
| `work/lean/SM/PolygonalConnected.lean` | `63c87005b5678e811be587290a0cfb2924825f3463c7263119611940db6e33e2` |
| `work/lean/SM/GenericDensity.lean` | `6b6880d31118c202d47ca340811b3006e4ef565e7d6dfe666b5ac7f115ae39c1` |
| `work/lean/SM/TreeCoefficient.lean` | `d070e70dfbb61e036641f0d5fac4adae83fd1cadfe22f3ce2ffd8c8e1de9ab06` |
| `work/lean/SM/RelativeGeneralPosition.lean` | `1b0a8d1802d97de912b73baa08b718cf18732c75d42eba564d4f49dd1f3f5d3b` |
| `work/lean/.lake/packages/mathlib/Mathlib/Analysis/Convex/PathConnected.lean` | `e361be68d7c22691466bb61dbcbce809cd0fee45b4d0fb578c937ce6504bcadc` |
| `work/lean/.lake/packages/mathlib/Mathlib/Topology/Connected/Basic.lean` | `3b07f29fae4e2d035bbec95d4ea9812e326201fb1383cb473ed7d4a12068c9ff` |
| `work/reviews/tree-path-gluing-technical-review-20260911.md` | `6c3c1bf313c8ed2eb8f91d7602495aec2f3ed16be3a9a4075df4b0ff33559cc1` |
| `work/reviews/weak-center-silent-technical-review-20260911.md` | `266a29f84ae07d56aeca52cc142c1aa358ace3dc1ef3141a530085f303fab2c5` |
| `reference/SM/sm-2-amplitude.tex` | `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf` |

The receipt binds the remaining embedded dependencies. Acceptance remains **39/192 (20.3%)**, targets **0/8**.
