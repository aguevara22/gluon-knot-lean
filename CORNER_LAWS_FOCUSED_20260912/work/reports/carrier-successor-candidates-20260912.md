# Actual carrier successor candidates — checkpoint098

The full marked traversal and its selected outgoing reconnections are now
constructed in Lean. This checkpoint adds80 checked declarations in four groups.
They are candidates under work/checks, with stronger statement/definition
fidelity and controlled canonical integration still pending. Accepted source
progress remains19/132 (14.39%); original checklist38/191 (19.90%); expanded
checklist39/192 (20.31%); main targets0/8.

| Group | Declarations | Checked scope | Passing root run |
|---|---:|---|---:|
| CarrierMarks | 18 | Every original vertex and actual crossing visit; injective traversal positions, sorted complete list, exact length and nonemptiness | second24989 |
| CarrierVisitTwin | 19 | Actual two-visit crossing fiber, distinct unique twin, selected involution, commutation and disjoint-union law | first56376 |
| CarrierSuccessor | 20 | Actual cyclic successor and predecessor, inverse and modular index laws, empty traversal gaps, and derived single orbit through every mark | second45949 |
| CarrierSmoothing | 23 | Actual outgoing-slot reconnection, endpoint evaluation preservation, component orbit quotient, incoming-node ownership, finite/nonempty components and singleton empty support | second67282 |

The source is reference/SM/sm-3-statesum.tex: definitions and convention at
lines14–39, lem:carriers at55, and its finite successor construction at97–115.
A selected visit is sent to the old successor of its actual twin. Node identity
is retained, expressing the incoming-visit convention. Both endpoints evaluate
to the same crossing point. The permutation algebra works for arbitrary
selected supports; the source's independence restriction is still needed for
the later splitting/count theorem.

Three failed first attempts are preserved with exact bodies, prototypes,
dependency lists and logs. Marks replaced the nonexistent List.Nonempty header
with the intended explicit existential, using the unchanged vertex-zero
witness. Successor supplied a membership proof and annotated the zero index as
a natural number; that annotation changes one header's text. Smoothing changed
only quotient-equality and singleton-count proofs. The first invalid headers
were never accepted, and compiler error placeholders in failed logs are
excluded from all successful evidence. No source premise or target was changed.

All80 successful axiom traces use only propext, Classical.choice and Quot.sound.
The four independent AI technical reviews bind104 file references across73
unique files. Candidate verification checks52 evidence files,1920 frozen
baseline files and327 unchanged canonical modules. The new verifier was also
independently inspected against its frozen predecessor before execution.
These checks do not grant stronger mathematical fidelity approval. The accepted
map is unchanged; candidates are tracked in goal-turn-098-candidates.json.
No whole-library build was repeated; the last canonical audit remains070.

This is not the full smoothing/carrier theorem: straight positive subsegments,
actual polygonal carriers and corners, independent-support cycle count,
inherited order, endpoint separation, retained crossings and all-visits
noncrossing ownership still need proof. The actual corner sum, its all-sector
soft theorem and wall laws, full-cusp/comparison and R/bridge remain in scope.
The complete A-soft source candidate from097 remains frozen.

Continue with decisions/carrier-cycle-splitting-inventory-20260912.md: prove
the concrete outgoing-swap split identity, including empty intervening lists
and singleton children; establish the actual noninterlacement and inherited
cyclic-order induction; then prove the orbit-count increment. Counting only
nontrivial permutation cycle factors would omit singleton components. The
inventory is bounded implementation research, not a proof receipt.
