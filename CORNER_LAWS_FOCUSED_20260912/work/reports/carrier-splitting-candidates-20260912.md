# Carrier splitting candidates — checkpoint099

Lean now proves that one actual selected crossing produces exactly two actual
successor-orbit components, with its two incoming endpoint owners distinct.
The complete marked traversal supplies the split-list representation; no
arbitrary list representation or ownership correspondence is assumed.

This checkpoint adds45 checked declarations in six groups. They remain
candidates pending stronger statement/definition fidelity and controlled
canonical integration. Accepted source progress remains19/132 (14.39%);
original checklist38/191 (19.90%); expanded39/192 (20.31%); main targets0/8.

| Group | Declarations | Checked scope | Passing root run |
|---|---:|---|---:|
| CarrierSingleSwitch | 7 | Actual selected singleton equals its twin transposition; exact outgoing insert rule and unchanged slots | second65819 |
| CarrierSameArc | 8 | Actual noninterlacement iff equal original open-arc status; actual independent-support and twin consequences | second34983 |
| CarrierCycleList | 4 | Actual original successor equals full-list permutation; derived complete rotated split-list representation | first90210 |
| CarrierSplitList | 12 | Concrete outgoing split identity, both exact child orbits and endpoint separation, including empty arcs and singleton children | second33822 |
| CarrierSingleSupport | 4 | Actual singleton split list, distinct incoming owners, exhaustion of all actual components and exact count two | first86071 |
| CarrierOrbitRefinement | 10 | Under an explicit same-current-orbit premise: actual orbit refinement, persistence of previous separation, constructed quotient forget map, surjectivity and weak count inequality | second11497 |

The source is reference/SM/sm-3-statesum.tex: finite successor model and
splitting induction at97–145. Right multiplication by the actual endpoint
transposition swaps outgoing slots. The concrete split formula gives the
children containing each incoming endpoint, and IsCycleOn plus full orbit
membership retains singleton children. The actual singleton count follows
because the two distinct endpoint owners exhaust the entire component quotient.

The distinction between original traversal arcs and current components remains
essential. SameArc proves facts about original physical traversal positions.
CycleList represents the complete original successor. Neither alone proves
that an arbitrary remaining selected pair lies on one current component after
earlier splits. OrbitRefinement keeps that premise explicit; it does not assert
the exact general plus-one count or silently discharge independence.

Four failed first attempts are preserved with exact bodies, prototypes,
dependency lists and logs. Repairs were confined to proofs: explicit Equiv.ext;
explicit predicate cases in place of a failed tauto; nil-append normalization;
and clearing a redundant local hypothesis after extracting its power witness.
Every public header and dependency closure remains unchanged. Failed compiler
placeholders are excluded from passing evidence. SingleSupport had only a
pre-freeze correction to an API spelling and passed its first kernel attempt.

All45 successful axiom traces contain only propext, Classical.choice and
Quot.sound. Six independent AI technical reviews passed153 file bindings across
107 unique files. Candidate verification passed80 evidence files,1995 frozen
baseline files and327 unchanged canonical modules. Both new verifiers passed
their first execution after independent static comparison with the frozen
predecessors. Sources, accepted map and prior passing candidates are unchanged.
The last whole-library audit remains070; no unchanged canonical rebuild was
repeated. These checks do not grant stronger mathematical fidelity approval.

Continue with decisions/carrier-independent-induction-after-singleton-20260912.md.
First prove actual rotated open-slice membership iff traversalBetween, including
wraparound, then the filtered-owner forms. Maintain inherited filtered cyclic
order and remaining-pair current-orbit membership together. Prove the affected
forget-map fiber has exactly two elements and all unaffected fibers one; only
then derive the general plus-one count. Geometry, regularity, retained crossings,
all-visits noncrossing, rotations, named records and coefficients remain open,
as do the actual corner sum's all-sector soft law and wall laws,
full-cusp/comparison and R/bridge. The A-soft source candidate from097 is frozen.

The existing thread heartbeat was verified active every hour, with no change
made. A separate ten-minute terminal watcher covered active work and is stopped
at checkpoint exit. Progress percentages count accepted source/checklist rows,
not these newly checked candidate declarations.
