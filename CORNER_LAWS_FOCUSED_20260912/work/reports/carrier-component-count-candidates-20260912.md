# Exact carrier component count — checkpoint103

Goal active and incomplete. Accepted source proofs **19/132 (14.39%)**;
original checklist **38/191 (19.90%)**; expanded checklist **39/192 (20.31%)**;
final targets **0/8**. This batch adds **7 kernel-checked implementation
declarations in three groups**, with zero source acceptance increment.

| Group | Declarations | Proved scope |
|---|---:|---|
| CarrierComponentFibers | 2 | The actual quotient forget map has exactly the two distinct endpoint owners over the affected old component and a singleton over every unaffected component. |
| CarrierFiberCard | 1 | Summing literal finite fibers proves that one two-element fiber and all other singleton fibers increase cardinality by one. |
| CarrierComponentCount | 4 | Actual insertion increases component count by one; every processed subset of an independent support has support cardinality plus one components; the final result is bundled with inherited order and selected-owner separation. |

The affected-fiber proof uses actual quotient representatives, the common full
original rotation and both child owner characterizations. It includes empty
open arcs and singleton components. The unaffected-fiber proof uses exact
unchanged owner equivalence, with no arbitrary supplied partition.

The cardinality argument sums every fiber and isolates the affected old owner.
The support induction obtains an actual visit of the inserted crossing and
uses the already checked partial invariants to discharge inherited-order and
same-current-owner premises. Thus the final count assumes only the original
polygon hypotheses and actual support independence. Its components are the
actual smoothing-successor orbit quotient, not geometric connected components
of the union of images.

All three root attempts passed first time: ComponentFibers68743,
FiberCard51491 and ComponentCount35180. All7 traces use only propext,
Classical.choice and Quot.sound. No failures or proof repairs occurred.
The count closure used recorded CLI maxHeartbeats=1000000 for the unchanged
sorted-arc dependency; no mathematical body or trust setting was changed.

Three independent same-model AI technical reviews passed **86 bindings across
60 unique files**. Candidate verification passed **47 evidence files**,
**2284 frozen baseline files**, and **327 unchanged canonical modules**.
Both verifiers passed first execution after independent static adaptation
review. Stronger statement-fidelity approval, canonical integration and source
acceptance remain pending. The accepted map is unchanged; last canonical audit070.

Next follow [the geometry note](../decisions/carrier-geometric-realization-next-step-20260912.md).
It is an unproved implementation plan. Derive positive original subsegments
from the actual marked successor, transport them through the physically equal
twin switch, and construct affine smoothing segments and closed marked traces.
True corners, regularity/turns, retained crossings, full visit noncrossing,
actual corner coefficients/state sum, all-sector soft theorem, wall laws,
full-cusp/comparison and R/bridge remain, alongside stronger fidelity and final
acceptance checks. No whole carrier lemma or final theorem is accepted here.
