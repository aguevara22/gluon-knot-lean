# Continue source thm:A-S7 after checkpoint080

Goal active; this is an IMPLEMENTATION PLAN, not a new theorem. Checkpoint080
adds43 Lean-checked candidates for the source half-root map, contact affine
signs, all three exact root cuts, and complete gap words/coefficient transport.
No source row was accepted. Stronger fidelity approval and controlled canonical
integration remain pending. Keep accepted definitions/axioms/map,327 canonical
modules, all prior passing bodies and source/reference/provenance frozen.

Read checks/ContactRootPartition.body.lean, ContactHalfRoots.body.lean,
ContactAffineSigns.body.lean, ContactBoundaryPositions.body.lean,
ContactGapTuples.body.lean and ContactGapWords.body.lean with their receipts.
The full directed-pair half-root map is now proved. All four nontrivial gap
words are identified at every cyclic label: base-left/first-arc-right equal
secondHalf at local root0; base-right/second-arc-left equal shift(-1) firstHalf,
so local root0 maps to the source first-half closing root-1. Their arity/start
facts are derived in ContactGapWords, not assumed there. Generic coefficient
transport in ContactGapTuples has explicit local G1/nonleaf premises; source
specialization must derive those premises from the actual singleton support.

Next prove the TWO FULL CONTRACTED TUPLE identities. A size equality and a
physical root edge equality alone do not establish these identities. Use the
frozen CriticalContractionPositions and ContractedGeometricWord bodies:
contractedVertexIndex g t j reads boundaryIndex g at expandPosition of (j-1).val.
expandPosition retains positions through t.lower and then adds the proved
strict-interior deletion count. Both endpoints survive. Let d=(a-M).val,
u=(g-M).val, and use the actual contactDistance bounds and u<n.

First inherited arc u<d: t=contactFirstArcTriple. The contracted size is d+1
and its first surviving labels start at g+1 along the firstHalf cycle. Let e
be the ringEquivCongr for the proved size equality. Prove, for every local j,
contractedVertexIndex g t j = firstHalfIndex M a (e j + (u : ZMod (d+1))).
Equivalently the reindexed contracted tuple is shift(u) firstHalf. Use explicit
representative arithmetic with the wrap case (j-1).val and the expansion
threshold d-u-1. Preserve the u=0 endpoint and local j=0. Then transport the
coefficient from local root0 to the inherited root u, using treeCoefficient_shift.

Second inherited arc d<u: t=contactSecondArcTriple, contracted size n-d.
Use v=(g-a).val=u-d, as proved by contact_relative_offset_val M a g with its
explicit parameters. Prove every contracted vertex equals secondHalfIndex M a
at the size-transported label plus v. Equivalently the reindexed tuple equals
shift(v) secondHalf. Canonical secondHalfIndex_range expresses it as the
consecutive range starting a+1 at label-1, including its wrap at zero. Handle
u=n-1 and local zero explicitly. Transport coefficient to the inherited root v.
Do not apply earlier one-vertex deletion identities to these longer arcs.

Derive each cut's vertexSet=contactSupport from its proved labels. This allows
actual VertexEdgeAt singleton support/concurrence premises into the generic
single-triple response, contractedWord_G1 and critical interval outputs. Use
g1_firstHalf/g1_secondHalf with the actual center singleton contact support;
both child sizes>=3 follow from contactHalfSizes_bounds. Unfold the nonleaf
criticalIntervalIntegerOutput branch only with proved gap length>=2, then
apply the complete gap tuple and coefficient transport results.

Scalar factors: add the base two-nonleaf (+,+) lemma proving Uleft*Uright=0
and Vleft*Vright=Bleft*Bright. CuspIntegerFactors has no CuspAt hypothesis:
reuse integer_wall_factor_left_leaf_pos_neg for the first arc and
integer_wall_factor_right_leaf_neg_pos for the second. Together with actual
contraction/gap coefficients these give the exact prescribed half products.
For base, only commute integer multiplication to place firstHalf before
secondHalf; do not exchange the named halves.

ContactAffineSigns constructs actual coordinates A=0,B=1,X=r with 0<r<1
and nonzero B-A directly from VertexEdgeAt. It proves all three epsilon pairs
and reverse far sign=-chi(a,a+1,M). The generic integer single-triple theorem
uses one fixed d and a local radius before arbitrary negative/positive times.
Canonical NamedWallSides.contactSign is chi on sideTuple false; its
vertex_contact_signs theorem gives this value on every false-side point and
its negative on every true-side point. Derive the generic jump d=contactSign
from the far-sign equality and a point within the supplied radius, checking
the sideTuple/time definitions. Use nearby_same_chirotope to transport each
independent germ-side point to the valid local radius; tree coefficients are
preserved by the proved full chirotope equality. Do not impose a new radius
restriction in the final source law. No neighboring-side condition is needed,
so both bigon and sliding branches remain covered.

Finally assemble all roots using contact_root_cases and contactHalfRoots_spec,
retaining the exact source product/root order. Target is the tree coefficient
vertex-edge law thm:A-S7; it remains a dependency, not the final corner state
sum theorem. Root owns one Lean kernel/build/audit at a time; no reviewer
kernels. Preserve each failed body/prototype/log before repair and freeze each
passing receipt. Obtain same-model nonauthor review without treating it as
stronger fidelity approval. Keep acceptance and all final targets pending.

Progress at080: source proofs19/132 (14.39%), original checklist38/191 (19.90%),
expanded checklist39/192 (20.31%), final targets0/8. Start one ten-minute watcher
on resumption, retain the existing hourly automation, and stop that exact watch
at exit. Continue without author questions. Check STATUS and checkpoint080 for
terminal handles and full evidence. The unrelated original shift-scope source
obstruction does not stop these contact proofs.
