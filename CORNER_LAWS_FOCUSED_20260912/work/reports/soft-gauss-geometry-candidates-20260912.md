# Actual soft-family Gauss transport and oriented newborn adjacency

Goal active and incomplete. Source proofs19/132 (14.39%); original checklist
38/191 (19.90%); expanded checklist39/192 (20.31%); final targets0/8.
No source claim newly accepted. The accepted map remains frozen; the new
candidates are in checkpoints/goal-turn-090-candidates.json, not its empty
compiled_proofs_awaiting_review list.

## Checked work in checkpoint090

| Group | Implementation declarations | Extra consumers | Terminal root run |
|---|---:|---:|---|
| SoftParentOrder | 7 | 0 | second81102 |
| SoftCrossingTransport | 27 | 0 | second16475 |
| SoftVisitOrder | 5 | 0 | first90703 |
| SoftParentArc | 2 | 0 | first87223 |
| SoftGaussLists | 5 | 0 | second50181 |
| CycleFiltering | 9 | 0 | second31100 |
| SoftGaussDeletion | 3 | 0 | second23514 |
| SoftNewbornVisits | 13 | 0 | first40868 |
| GaussNextFromEmptyArc | 3 | 4 | second7198 |
| SoftGaussGeometry | 2 | 0 | first31945 |
| Total | 76 | 4 | all exit0 |

The exact parent-edge map preserves numerical traversal order, including
insertion after residue0. Actual crossing supports are mapped by Finset.image;
actual visits retain their member edges and crossing pairing. The image is
exactly the inherited crossings/visits; in a non-loop sector it is the whole
child set. The source assumptions derive these facts and child Generic on a
common positive interval, with no Generic premise at epsilon0.

Geometric same-edge parameter order and numerical edge order prove actual
visit-key order. Together with exhaustive membership, this proves equality
of the mapped parent sorted list and the child list filtered to inherited
visits. This is order equality, not merely a permutation. It includes an empty
parent list. Consequently the actual non-loop cyclic Gauss word is the parent
word under the proved crossing map.

Cycle.filter is constructed on the genuine rotation quotient, with a proof
that list filtering respects rotation. It preserves repetitions and commutes
with non-injective letter maps. Thus deleting the actual newborn crossing
removes both its visit occurrences, and the resulting Cycle and Gauss word
are exactly the mapped parent's.

The two newborn visits are actual visits on the incoming and return edges.
Their canonical parameters are the proved Cramer values, lie strictly in the
edge interiors, and bound all inherited visits on those edges. Exact successor
labels and endpoint evaluations expose the intervening soft edge through Pj
and Pj+epsilon q. The complete child visit classification then proves that
no actual crossing visit lies on the oriented incoming-to-return arc, including
wrap at the numerical cut. A separate finite sorted-order converse proves
that its actual nextGaussVisit is the return visit. Four prototype consumers
exercise two- and three-member forward/wrapped successors; they are additional
checks, not source claims or implementation declarations.

The combined soft_small_gauss_geometry theorem takes one positive radius
for the word and arc results. It supplies child Generic, actual support maps,
non-loop word equality, and all loop interior/path/empty-arc/next/deletion
conclusions. Proof irrelevance only identifies proofs of identical Generic,
persistence and classification propositions; it identifies no freely chosen
geometric data or distinct radii.

## Evidence and limits

All80 printed declarations use only propext, Classical.choice and Quot.sound.
The verifier checked97 candidate evidence files,1180 frozen baseline files
and327 unchanged canonical modules. It did not rerun the whole canonical
library audit (last audit070). Six first attempts failed and remain preserved:
17757,21028,39816,10890,40948,33249. All repairs changed proof syntax or explicit
coercions/type arguments; theorem statements remain unchanged. The passing
proof files and their receipts are frozen.

All ten same-model technical reviews are sealed; the review verifier checked
717 file bindings. Review records contain complete body bindings,
reviewer/implementer identity and strategy/dependency contributions disclosed.
It does not grant stronger statement/definition fidelity, source acceptance
or canonical integration. Check checks/checkpoint-090-review-bindings.json
for the final review-binding receipt; hashes and successful builds do not
supply the missing fidelity judgment.

The full source lemma is still incomplete as one formal statement. Explicit
traversalBetween witnesses for the two intervening vertex coordinates and a
common-radius assembly of all four printed clauses remain. The earlier
Generic/chamber, contacts, turns, directions, inherited crossing limits/signs
and newborn limits must be included with these Gauss results. Preserve the
original chamber basepoint when shrinking its radius. Then proceed to
thm:A-soft, thm:C-soft and the full corner wall-law target. None is assumed
or declared completed here. The wider shift-source obstruction remains separate.

Resume decisions/soft-family-assembly-after-gauss.md. Every kernel is terminal;
checkpoint090 records the progress watcher exit and the next executable task.
