# Positive smoothing segments and closed marked traces — checkpoint104

Goal active and incomplete. Accepted source proofs **19/132 (14.39%)**;
original checklist **38/191 (19.90%)**; expanded checklist **39/192 (20.31%)**;
final targets **0/8**. This batch adds **23 kernel-checked implementation
declarations in four groups**, with zero source acceptance increment.

| Group | Declarations | Proved scope |
|---|---:|---|
| CarrierAffineSegments | 7 | Exact original-edge affine algebra, actual smoothingSegment definition, endpoints, gluing and continuity. |
| CarrierMarkedSegments | 3 | Original successor has no fixed mark; actual next mark is later on the same edge or the next original vertex; positive parameter interval including wraparound. |
| CarrierSegmentGeometry | 7 | Actual smoothing segments follow positive original-edge intervals, have positive Euclidean length, remain on the original edge for unit parameters, are individually injective, and rule out fixed smoothed marks. |
| CarrierClosedTrace | 6 | Actual owner-filtered mark list and evaluated plane cycle; independent inherited order identifies modular next edges with actual smoothing segments; all cyclic edges have positive length, gluing and individual continuity. |

The marked-gap proof changes only the cut on traversal positions. The actual
no-intervening-mark theorem excludes the next original vertex from the open
gap; the shifted successor key must lie strictly above the starting parameter
and at most one. This yields increasing parameters on the same original edge
or exactly the next vertex, including the last-edge wraparound case.

The actual selected outgoing-slot permutation preserves plane evaluation.
Applying the proved original gap to that slot supplies a positive parameter
difference, so every smoothing segment is a positive multiple of its actual
original edge. G1 makes that edge nonzero. Euclidean length is the source plane
length from EuclideanPlane, not the product-space norm. At a selected site no
extra segment from a visit to its twin is inserted.

Each component uses the complete original mark list filtered by actual owner.
Its nonemptiness and exact membership are proved. Under actual support
independence, inherited order identifies the next list index modulo length
with the actual smoothed successor. The closing edge is therefore included.
Plane evaluation retains repeated entries and never identifies abstract owners;
local segment injectivity does not assert that a carrier is embedded.

Passing root sessions: AffineSegments24066, MarkedSegments4362,
SegmentGeometry20830 and ClosedTrace14350. All23 traces use only propext,
Classical.choice and Quot.sound. Two first failures are preserved and excluded:
MarkedSegments19499 needed explicit equality of zero interval-subtype values;
ClosedTrace77729 incorrectly supplied an explicit mark to an EqOn application.
Both repairs change only proof steps, with all public headers and dependencies
unchanged. ClosedTrace used recorded CLI maxHeartbeats=1000000 for the unchanged
sorted-arc closure in both attempts; no trust setting or mathematical assumption
changed.

Four independent same-model AI technical reviews passed **126 bindings across
88 unique files**. Candidate verification passed **69 evidence files**,
**2326 frozen baseline files**, and **327 unchanged canonical modules**.
Both verifiers passed first execution after independent static adaptation
review. Before execution, root corrected a stale group-count field in verifier
output metadata from three to four; the original draft and correction record
are retained. No acceptance check was relaxed. Stronger statement-fidelity
approval, canonical integration and source acceptance remain pending. The
accepted map is unchanged; last canonical whole-library audit070.

Next follow [the true-corner plan](../decisions/carrier-true-corners-next-step-20260912.md),
an unproved implementation plan. Prove that every component contains an actual
true corner, construct its corner filter, and prove that omitting unselected
marks compresses same-direction positive pieces with trace-image equality.
Then construct the source compressed cyclic corner tuple and establish its
regularity and at least three corners. The checked finite marked trace is not
yet that source polygon. A separate global continuous-circle parameterization
is optional unless a concrete consumer needs it.

Exact retained crossings, all-visit noncrossing, actual corner coefficients and
state sum, all-sector soft theorem, wall laws, full-cusp/comparison and R/bridge
remain, together with stronger fidelity and final acceptance checks. No whole
carrier lemma or final theorem is accepted here.
