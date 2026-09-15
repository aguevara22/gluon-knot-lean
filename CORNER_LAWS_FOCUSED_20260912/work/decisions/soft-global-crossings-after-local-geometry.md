# Resume the complete soft-family geometry

Checkpoint088 proves 68 candidate declarations. The source insertion is exact
at every physical position, including insertion after label n. Parent G1 and
the exact admissibility predicate give G1 for all sufficiently small positive
parameters. Source attachment signs, turns, limiting return direction and its
ordered determinant signs are proved. The soft edge has precisely its two
incident endpoint contacts. The actual incoming/return pair is remote and
crosses exactly when both attachment signs equal the parent turn.

These are candidates, not accepted source rows. All nine passing groups and
their prototypes/receipts are frozen. Do not change the canonical327 modules,
approved map or supplied sources. The whole of lem:soft-generic is unfinished.

## Immediate next implementation

1. Define the parent-edge correspondence by sending parent j to softNewIndex j
   and each other k to softOldIndex j k. Prove injectivity and exhaustion of
   every enlarged edge except the soft edge. Keep the physical traversal cut
   and all small-arity/wrap cases explicit. Prove the actual return edgePoint
   equals the parent j edgePoint plus (1-t) times epsilon*q; other corresponding
   edgePoints are unchanged. These are identities for every real parameter.
2. For every parent pair remote to j, transport disjointness using compact
   closed-segment stability, including parallel directions. Transport an actual
   parent crossing with the canonical Cramer intersection parameters, prove
   both strict parameter inequalities, convergence of point and parameters,
   and persistence of the ordered direction determinant sign. No G2 or Generic
   premise at the inserted tuple may be used to prove that tuple generic.
3. Exhaust all enlarged edge pairs: unchanged/unchanged, return/remote-parent,
   return/following adjacent edge, incoming/return, and soft/any edge. Use
   SoftEdgeAvoidance and SoftFamilyLocalCrossing for the last two cases. Establish
   the complete list of crossings, including absence of births in both the
   same-sign and mixed sectors. A single-pair theorem is insufficient.
4. Define the newborn supporting-line intersection via the actual incoming and
   return directions. Their determinant stays nonzero because its limit is the
   parent turn determinant. At epsilon zero the unique point is Pj, incoming
   parameter one and return parameter zero. Prove these limits. Use the local
   sector theorem to obtain a genuine interior crossing in the loop sector.
5. Use parent G2 to separate every distinct parent crossing point, and parent G1
   to separate those points from Pj. Finite continuity preserves all inherited
   separations and separates the newborn. Together with the complete crossing
   classification and G1's disjoint adjacent interiors, prove G2 for the actual
   inserted polygon. Obtain one positive interval for all clauses by finite
   intersection/minima. Its continuous image in the actual Generic locus lies
   in one connected-component chamber; use the real chamber definitions.
6. Preserve the order of every pair of inherited visits on each directed edge
   by strict parameter separation. In the loop sector the newborn incoming
   visit follows every inherited incoming visit and its return visit precedes
   every inherited return visit. The intervening soft edge has no visits.
   Prove the source cyclic Gauss-word identification and deletion statement.
   Do not replace it with equality of linearly cut lists without proving that
   representation matches, particularly at insertion after source label n.
7. Assemble all four clauses of lem:soft-generic, with one epsilon0 and the full
   source domain. Only then proceed to the amplitude soft theorem and the
   remaining corner soft proof; this geometry alone is not that theorem.

## Existing candidate interfaces

- SoftInsertionIndices, SoftInsertionSuccessors and SoftInsertionTuple: exact
  physical labels, exhaustive labels, edges, continuity and SoftAdmissible.
- SoftLocalDeterminants: explicit local determinants, one common sign radius,
  both strict-straddle tests and closed/interior crossing equivalence.
- SoftFamilyG1: softInsertion_small_G1.
- SoftAttachmentSigns: soft_insertion_definition and both attachment turns.
- SoftFamilyTurns: softInsertion_small_turns and softInsertion_return_tendsto.
- SoftFamilyLocalCrossing: softFamily_local_crossing for the actual pair.
- SoftEdgeAvoidance: softEdge_only_incident_contacts for every enlarged edge.

Canonical SM.SegmentStability handles compact disjointness even at zero soft
direction. SM.ContinuousGeometry supplies Cramer continuity and strict order
stability. SM.Crossings and SM.G1Consequences give actual crossing definitions,
pair witnesses, uniqueness, parameters and adjacent intersections. Read their
exact types before reuse. Embed candidate bodies in proved dependency order,
obtained from prototype positions, not arbitrary JSON dictionary order.

The existing generic_curve_local_chamber requires Generic at its zero centre,
so it cannot be applied to softInsertion at epsilon zero (two vertices coincide).
Reuse its connected-image argument on Ioo 0 delta, with a positive basepoint
such as delta/2, after proving Generic everywhere on that interval.
Likewise, generic_family_visitParameterOrder transports within a fixed arity;
it does not itself compare the n-vertex parent with its n+1-vertex child.
SM.FusionGaussWord is a useful example of proving rotation of actual visit
lists after changing arity; its fusion hypotheses are not soft hypotheses.
SM.CrossingVertexExclusion and SM.GeometricParameters may supply the actual
point exclusion and parameter formulas after their precise premises are met.

Root alone runs one Lean kernel/build/audit at a time. Preserve exact failed
body/prototype/log before any repair, freeze each passing group and keep a
separate declaration ledger. Obtain technical review by a nonauthor; disclose
that it is same-model review and does not grant stronger fidelity approval.
Source acceptance remains 19/132; new helper counts do not increase it. Continue
progress reporting and resumable checkpoints without author questions.
