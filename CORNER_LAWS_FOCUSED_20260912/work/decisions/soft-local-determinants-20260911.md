# Local soft-insertion determinants and crossing sector

Authored by `/root/review_contraction_candidates`, the same currently available model as root. This is an implementation candidate, not an independent self-review or stronger-model statement-fidelity approval. No Lean kernel, build or audit was run. Root owns compilation and independent review; all prior frozen files and accepted state remain unchanged.

The candidate covers the point-level determinant/attachment/turn/straddle part of `def:soft` and `lem:soft-generic`, source lines 991–1150. It uses no cyclic labels, polygon genericity, soft-family theorem, inherited-crossing claim, or oracle. The two definitions are the actual point `softLocalPoint M q ε = M + ε • q` and return direction `softLocalReturn M B q ε = B - M - ε • q`; their endpoint identity proves that the return ends at B.

The main theorem `softLocal_small_crossing_sector` assumes exactly the three nonzero real determinants `det (M-A) (B-M)`, `det (M-A) q`, and `det q (B-M)`. It produces a common positive radius and, for every positive ε below it, both ordered incoming/return direction signs, the equivalence between an actual closed-segment parameter intersection and the two loop-sector sign equalities, and each of the two separate strict-straddle equivalences. The loop-sector signs are precisely the attachment values given by `softLocal_attachment_signs`. There is no restriction on the sign of the original turn or either attachment determinant.

Every determinant identity is proved by expanding the two real coordinates and applying ring arithmetic; it remains valid at ε=0 and at degenerate point choices. The new-old area theorem also covers any other old point X. The two attachment and new-turn sign theorems use positivity of ε and multiplicativity/negation of SignType.sign and hold for every ε>0.

For sufficiently small ε, the direction determinant and the return-line height of A have the same nonzero constant term T. Their exact linear expressions are respectively `T - ε * det (M-A) q` and `T + ε * (det q (B-M) - det (M-A) q)`. Continuity of the real linear expressions, continuity of sign away from zero, and a metric-neighborhood extraction prove a sign-persistence radius for each. The minimum gives one radius for both. This does not assume their signs as a caller premise of the main theorem.

For the first straddle, the incoming-line heights are ε times the incoming attachment determinant and T. For the second, the return-line heights are ε times the outgoing attachment determinant and the sign-persistent height of A. The scalar sign-product lemma, with nonzero sign T, proves each equivalence separately. The canonical `segment_crossing_criterion` then identifies their conjunction with an intersection in both open segments and proves transversality.

To cover closed segments as well, `softLocal_closed_iff_strict` proves a generic point-level helper: a transverse pair with all four endpoint heights nonzero cannot have an endpoint intersection. If a parameter were zero or one, its endpoint would lie on the other supporting line; its height would vanish because `det w (r • w) = 0`, contradicting the corresponding height hypothesis. In the main theorem, all four heights are proved nonzero from the three printed determinant assumptions and the established small-parameter sign. Thus other sectors cannot hide endpoint-only contacts.

The two conditional straddle/interior helpers expose their actual height-sign condition. The main theorem derives it, so it is not a remaining source premise. This unit does not claim the full soft-generic lemma: cyclic insertion/edge maps, simultaneous global G1/G2, inherited crossing persistence/order, unique newborn convergence and Gauss-word adjacency remain for subsequent assembly. Canonical intersection-parameter uniqueness and continuity are available for that later work.

The prototype imports only `SM.CrossingCriterion`, `SM.ContinuousGeometry`, `Mathlib.Topology.Instances.Sign`, and `Mathlib.Tactic`. It embeds the exact body once and requests the type and axiom trace of every declaration. The first draft is separately preserved before any repair.

## Exact declarations

- `SM.softLocalPoint`
- `SM.softLocalReturn`
- `SM.softLocalPoint_add_return`
- `SM.softLocal_new_old_area`
- `SM.softLocal_attachment_determinants`
- `SM.softLocal_turn_determinants`
- `SM.softLocal_incoming_heights`
- `SM.softLocal_return_heights`
- `SM.softLocal_return_determinants`
- `SM.softLocal_attachment_signs`
- `SM.softLocal_turn_signs`
- `SM.softLocal_sign_product_iff`
- `SM.softLocal_linear_sign_persistence`
- `SM.softLocal_small_signs`
- `SM.softLocal_first_straddle_iff`
- `SM.softLocal_second_straddle_iff`
- `SM.softLocal_interior_crossing_iff`
- `SM.softLocal_closed_iff_strict`
- `SM.softLocal_small_crossing_sector`

## Candidate hashes

- `work/checks/SoftLocalDeterminants.body.lean`: `74e92cba16088e18f22dfbf273892025bd108bd1296d08d5f19bf60c69169a43`
- `work/checks/SoftLocalDeterminants.prototype.lean`: `977bdf765d9716c5e4d10c9bede814ba9a9545c48ebb31aae475ab3b1e6a64b1`
- `work/checks/SoftLocalDeterminants-first-draft.body.lean`: `74e92cba16088e18f22dfbf273892025bd108bd1296d08d5f19bf60c69169a43`
- `work/checks/SoftLocalDeterminants-first-draft.prototype.lean`: `977bdf765d9716c5e4d10c9bede814ba9a9545c48ebb31aae475ab3b1e6a64b1`

## Inspected dependency and source hashes

- `work/lean/SM/CrossingCriterion.lean`: `855c16a0d99ed9abb634a5494f7e30d947d68592d4f2878762b5ecd6c8aef648`
- `work/lean/SM/ContinuousGeometry.lean`: `61250145831b23c7d8bedc54956643d844bc52ef4ff1ab55b87b81b26cc2000c`
- `work/lean/SM/Segment.lean`: `40fcfef972866bf0d762b08240941b3f7cd189259692d330709702ad1c9a7465`
- `work/lean/SM/Chirotope.lean`: `e0225bc712162273f43269ed764ac4849ae8fcd8798245a367d4262858fbf575`
- `work/lean/SM/Polygon.lean`: `d0b5d37591c252d66e1a3f060cea1e3d58625fedd6c5491cf4c1cf6d2b8c149d`
- `work/lean/.lake/packages/mathlib/Mathlib/Topology/Instances/Sign.lean`: `ccfd4dd3593c6c1f210133749c73e4a778fa70e4772e48b50cde116f0b334020`
- `work/lean/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`: `68fd1ff4f04d8f126d92f53f080fa6d7bd604a9cbaca521a3511f8760f63570f`
- `reference/SM/sm-2-amplitude.tex`: `014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf`
