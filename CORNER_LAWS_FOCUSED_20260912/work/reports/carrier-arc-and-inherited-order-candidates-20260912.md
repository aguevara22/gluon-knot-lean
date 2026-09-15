# Carrier arcs and inherited order — checkpoint100

Goal active and incomplete. Accepted source proofs **19/132 (14.39%)**; original
checklist **38/191 (19.90%)**; expanded checklist **39/192 (20.31%)**; final
targets **0/8**. This checkpoint adds **29 kernel-checked implementation
declarations in four groups**, with zero source acceptance increment.

| Candidate group | Declarations | Checked result |
|---|---:|---|
| CarrierFilteredCycles | 10 | Define each component cycle by filtering the original marked circle by actual owner; prove exact membership, nonemptiness, disjointness, injectivity and literal filtered split representation. |
| CarrierSortedArcLists | 6 | Strict cyclic order equals rotated sorted-list open-slice membership, including wraparound and excluded endpoints. |
| CarrierMarkedArcLists | 6 | Specialize to actual physical traversal arcs; owner filtering adds exactly owner equality; independent twin visits occupy one original slice, or one filtered slice under explicit current-owner inputs. |
| CarrierInheritedOrder | 7 | Define the current-successor/inherited-order invariant explicitly; prove it for empty and singleton support and derive the two actual singleton component cycles. |

The singleton proof does not assume successor compatibility. It derives owner
filters from exact child orbits, identifies the two inherited cycles, and uses
disjoint permutation factors to prove their successor actions. Empty arcs and
singleton children are included. The general independence induction remains
unproved: original same-arc membership alone does not establish current
same-component membership after earlier splits.

Root passing sessions: FilteredCycles72620, SortedArcLists43464,
MarkedArcLists74734, InheritedOrder33064. All29 successful axiom traces contain
only propext, Classical.choice and Quot.sound. Four failed attempts are retained
with exact bodies, prototypes, dependency lists and logs; compiler placeholders
are excluded from passing evidence.

SortedArcLists first29587 needed explicit natural-number annotations at four
zero indices in one invalid theorem header and a local index. The header text
changed; its intended meaning did not. MarkedArcLists first38819 exceeded the
default heartbeat limit while rechecking an unchanged dependency. Only the
prototype heartbeat limit was raised; the repair note explicitly corrects an
earlier mistaken diagnosis. InheritedOrder first10734 and second25323 required
proof-only dependent-type and decidability transport repairs; all seven
headers and dependencies were preserved.

Candidate verification passed **70 evidence files**, **2095 frozen baseline
files** and **327 unchanged canonical modules**. Four independent AI technical
reviews passed123 bindings across94 unique files, recorded in
checkpoint-100-review-bindings.json; they
grant no stronger-model statement-fidelity approval, canonical integration or
source acceptance. The accepted declaration map is unchanged. The last
canonical whole-library audit remains070; no unchanged-library audit was rerun.

Continue with [the ambient transport note](../decisions/carrier-ambient-transport-next-step-20260912.md):
prove orbit transport for permutations agreeing on an invariant set, specialize
to the two actual filtered children, and establish unaffected component
transport. Then maintain inherited order and remaining-pair current-orbit
membership together, and prove exact forget-map fibers for the general count.
The note is an implementation proposal, not proof evidence.

Carrier geometry, turns, retained crossings, noncrossing ownership, actual
corner coefficients/state sum, all-sector soft theorem, wall laws,
full-cusp/comparison, R/bridge, stronger fidelity and final acceptance remain.
