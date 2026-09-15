# Direct C-soft: searched inventory and next construction

Read-only mathematical inventory by `/root/spanning_gates`, 2026-09-12.
No Lean kernel, build or audit was run; no existing proof was edited. Source
acceptance increment0; stronger fidelity and canonical integration remain
unapproved. This supplements the active A-soft work and preserves the full
corner wall/soft goal.

**Scope of the finding.** Searches of `work/lean/SM` (327 Lean files) and
`work/checks` (563 Lean files excluding names ending `prototype.lean`) for
`carrier|named.?record|corner.?coefficient|corner.?state|state.?sum|HOMFLY|Laurent|positive.?lift|smoothing`
(case insensitive) returned no matches. Additional declaration-name and
`record`/`independent.*support` searches located the APIs below. Within that
searched implementation corpus I did not identify actual carrier, named knot
record, positive-lift polynomial, corner coefficient or C-state-sum definitions.
This is an inventory result, not proof of absence under every possible name
or elsewhere. `GeometricRecordsAgree` is geometry/Gauss transport, not the
named decorated-record polynomial bridge. A-soft or an abstract lawful
quantity cannot substitute for the actual C definition.

**Authoritative next targets.** `reference/SM/sm-3-statesum.tex`9–90 and97–242
define independent decompositions, oriented reconnection and incoming-visit
ownership, then prove the carrier assertions. Lines325–375 define positive
lifts and named records;1215–1226 state the actual-record polynomial bridge;
1041–1060 identify the source polynomial;1688–1700 define c(Q) and C;
4801–4819 give the embedded-carrier value1 and isolated-crossing value0.
The direct C-soft proof is `reference/SM/sm-4-knotlaws.tex`984–1128.
Historical source status tags are not Lean evidence.

**Existing executable foundations.** All names below are in namespace `SM`.

| Need | Exact file and APIs |
|---|---|
| Actual traversal/marks | `work/lean/SM/Traversal.lean`: `TraversalPoint`, `traversalEvaluation`, `traversalKey_injective`, `traversalKey_lt_iff`, `traversalBetween`. `GaussVisits.lean`: `Visit`, `visitPosition`, `visitPosition_interior`, `visitPosition_evaluation`, `visitPosition_injective`. `CrossingPair.lean`: `crossing_other_visit`, `crossing_visits_exhaust`. |
| Full crossing cycles/supports | `GaussWord.lean`: `gaussList`, `gaussList_nodup`, `mem_gaussList`, `gaussCycle`, `gaussWord`. `GaussCyclicGap.lean`: `nextGaussVisit`, `gauss_next_no_visit_between`. `InterlaceSupports.lean`: `independentSupports`, `mem_independentSupports_iff`, `supportNeighbors`, `supportUnselected`. These include the empty support. |
| Actual soft geometry | `work/checks/SoftFamilyAssembly.body.lean`: `soft_family_generic_source hn hP j q hq` supplies one positive interval, Generic parent insertions, all soft-edge contacts, attachment/old turn signs, inherited point/parameter limits and determinant signs, exact crossing classification, nonloop Gauss word, and loop adjacency/deletion/vertex arc. |
| Useful smaller soft APIs | `SoftCrossingTransport.body.lean`: `softInheritedCrossing`, `softInheritedVisit`, `softInheritedVisit_pairing`, `softCrossingEquivNonloop`, `softVisitEquivNonloop`, `softNewbornCrossing`, `softInheritedCrossing_range_loop`. `SoftVisitOrder.body.lean`: `softInheritedVisit_key_lt_iff`. `SoftGaussDeletion.body.lean`: `soft_gaussCycle_delete_newborn`, `soft_gaussWord_delete_newborn`. `SoftNewbornVertexArc.body.lean`: `softNewbornVisits_vertex_arc`. `SoftAttachmentSigns.body.lean`: `softAttachment_signs_nonzero`, `softInsertion_attachment_turns`. |
| Actual rotation | `work/lean/SM/RotationNumber.lean`: `rotationNumber`, `rotationNumber_integer`. `RotationContinuity.lean`: `continuousAt_principalAngle`, `continuous_rotationNumber_family`, `rotationNumber_family_constant`. `RegularPerturbation.lean`: `rotationNumber_locally_constant`. `AngleScaling.lean`: `principalAngle_smul`, `regularPair_smul`. `Chirotope.lean`: `leftTurns`. |

**First concrete implementation.** Construct marks from the actual polygon:
`ZMod n ⊕ Visit P`, with original vertex i at traversal position `(i,0)` and
a visit at `visitPosition hn hP.1`. Strict visit interiority separates the two
kinds of marks, and the existing injectivity results give distinct traversal
keys. Sort all marks by that key and construct its cyclic successor permutation
rho. Ordinary vertices make this list nonempty even for crossing-free P.
Derive the twin involution on visits from the actual two-member crossing
fiber. For S in `independentSupports hn hP`, swap only the outgoing slots of
its two visits: compose rho with the selected-twin involution, fixing every
ordinary vertex and unselected visit. This implements the source incoming-visit
ownership; do not accept rho or carrier correspondence as supplied data.

Prove the actual orbit/cycle splitting and order independence, then evaluate
cycles geometrically. Keep all visit ownership for records; suppress unselected
straight-through marks only when extracting carrier corners. Prove positive
inherited subsegments, nonzero edges, at least three corners, Regular and the
original/smoothing turn formulas. Retained self-crossings and their unique
owners must be derived. None of these carrier conclusions is currently supplied
by the Gauss-cycle APIs alone.

**Sector work after that construction.**

- Mixed: derive from soft-edge contact exclusion that every selected successor
  permutation keeps M→Mε intact. They are adjacent original corners of one
  actual carrier, with distinct nonzero turns −chiMinus and −chiPlus. Therefore
  every independent support fails uniformity. This carrier obstruction can be
  proved before knot-polynomial development; the actual C zero follows when
  its finite uniform-support sum is defined.
- Same-sign: derive the soft interlacement/support equivalence from actual
  inherited visit order and pairing. Contract the extra ordinary mark in each
  selected-successor cycle. Prove uniformity equivalence, retained record
  equivalence and equal rotations; then products of actual coefficients agree.
- Loop supports: prove inherited interlacement is preserved and newborn y
  interlaces nothing, using its empty cyclic visit arc. Obtain the exhaustive
  actual independent-support correspondence S and S∪{y}, including S empty.
  I found no existing soft-specific interlacement/support theorem in the above
  searched corpus.
- Loop omitted: for every S omitting y, carrier ownership puts both y visits
  on one carrier and the unchanged short arc makes y isolated in its retained
  interlacement graph. Nonuniform terms are excluded; uniform terms vanish by
  the actual isolated-crossing coefficient theorem. This must include supports
  whose corresponding parent support is nonuniform.
- Loop selected: commute swaps to process y first. Prove the literal triangle
  cycle `(b,M,Mε)` and residual cycle containing a. The triangle is embedded
  and all three turns are −turn(P,j), hence its coefficient is1. All inherited
  selected pairs lie in the residual; derive its subsequent carrier bijection,
  with M replaced by the smoothing corner y of sign turn(P,j). Every resulting
  curve is a carrier of Generic Pε. Do not introduce residual G1.

**Remaining analytic/coefficient obligations.** Equal turn *signs* do not
prove equal rotations. In the same-sign case prove the principal-angle wedge
split with no wrap; the inserted edge degenerates at zero, so direct fixed-size
local constancy at that zero tuple is inapplicable. In the loop residual case
use y→M and return-direction→old-direction; use the continuous regular
principal angles of every corresponding carrier, including moved carriers
away from M. Finite turn-sum convergence plus proved integral rotations gives
one common small interval of equality. This requires the actual carrier
families and is not provided by ambient polygon rotation alone.

Define named records with oriented successor, pairing, over/under bits, signs
and all crossing-free components. Derive positive-lift bit preservation from
positive direction multiples and the exported ordered determinant signs;
prove the source polynomial/identification bridge and equality of actual
c(Q) at equal crossing counts and rotations. Prove the two elementary corner
values on their printed carrier domains. Finally establish the actual soft
`leftTurns` increments and support-cardinality signs, and reindex the complete
C sum. No sign prefactor or coefficient-product transport should be assumed.
