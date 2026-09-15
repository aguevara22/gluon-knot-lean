# Independent carrier induction — checkpoint102

Goal active and incomplete. Accepted source proofs **19/132 (14.39%)**;
original checklist **38/191 (19.90%)**; expanded checklist **39/192 (20.31%)**;
final targets **0/8**. This batch adds **11 kernel-checked implementation
declarations in three groups**, with zero source acceptance increment.

| Group | Declarations | Proved scope |
|---|---:|---|
| CarrierPendingPairs | 3 | Define co-location of every remaining actual twin pair; prove the empty case and insertion preservation using physical filtered arcs and unaffected orbit transport. |
| CarrierInheritedInsert | 4 | Absorb owner filters on the full original circle, derive both actual affected inherited cycles, and prove inherited-order insertion. |
| CarrierIndependentOrder | 4 | Simultaneously prove both invariants for every processed subset of an actual independent support; obtain final inherited order, remaining-pair co-location and final selected-owner separation. |

The finite induction fixes an actual independent support S and processes any
T contained in S. At insertion, a real visit is obtained from the selected
crossing's proved two-visit fiber. The old conjunction supplies both inherited
order and the current owner equality required by the two preservation results.
Thus the final independent-support statements have no supplied current-order or
same-current-component premise.

Affected inherited cycles are derived using one common original rotation.
A global new-owner-implies-old-owner proof justifies filter absorption before
restricting to the affected old component. For final selected-owner separation,
process the support with that crossing erased and insert it last; exact child
orbit disjointness gives separation at the final support. Empty arcs and
singleton successor-orbit components remain included.

Passing root sessions: PendingPairs4075, InheritedInsert2363 and
IndependentOrder81955. All11 axiom traces use only permitted foundational axioms.
IndependentOrder first59463 failed only transport of the final support index;
the entire failed attempt is preserved and excluded. The repair explicitly
transports the full owner-inequality proposition along the proved insert-erase
equality. All public headers and dependency closures are unchanged.

PendingPairs and IndependentOrder used CLI maxHeartbeats=1000000 for the
unchanged sorted-arc dependency, with execution metadata bound separately.
Their mathematical bodies/prototypes were not altered to raise this limit.
An initial metadata write used the wrong relative directory and was corrected;
it did not change the executed Lean command or mathematical evidence.

Three independent AI technical reviews passed **107 bindings across61 unique
files**. Candidate verification passed **50 evidence files**, **2235 frozen
baseline files**, and **327 unchanged canonical modules**. Both verifiers passed
first execution, and their adaptation received independent static review.
Stronger statement-fidelity approval, canonical integration and source
acceptance remain pending. The accepted map is unchanged; the last canonical
whole-library audit remains070.

Next follow [the component count note](../decisions/carrier-component-count-next-step-20260912.md).
Prove the actual quotient forget-map fiber is the distinct endpoint-owner pair
over the affected component and a singleton elsewhere. Sum these literal fibers
to prove the one-step increase, then use the checked independent partial
invariants for the general support-cardinality-plus-one result. The note records
a proof route, not a checked count theorem.

Geometric carrier realization, regularity and turns, retained crossings, full
visit noncrossing, actual corner coefficients/state sum, all-sector soft
theorem, wall laws, full-cusp/comparison and R/bridge remain, alongside stronger
fidelity and final acceptance checks.
