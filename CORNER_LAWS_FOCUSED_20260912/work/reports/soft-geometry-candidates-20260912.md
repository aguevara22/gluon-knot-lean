# Soft insertion and local geometry candidates

Checkpoint088 adds **68 kernel-checked declarations in nine groups**. Accepted
source proofs remain **19/132 (14.39%)**; original checklist38/191 (19.90%),
expanded checklist39/192 (20.31%), final corner targets0/8. The goal is active.
Declarations include definitions and helper lemmas, not 68 source claims.

| Group | Declarations | Proved scope |
| --- | ---: | --- |
| SoftInsertionIndices | 10 | Exact physical insertion labels, injectivity and exhaustive old/new labels |
| SoftInsertionSuccessors | 4 | Old successors, new successor and every wrap case |
| SoftInsertionTuple | 11 | Actual tuple, continuity, edges, exact admissibility and attachment definitions |
| SoftLocalDeterminants | 19 | Local determinants, sign persistence, both straddle tests and crossing sector |
| SoftFamilyG1 | 9 | All old/new triples and one positive interval of G1 |
| SoftAttachmentSigns | 4 | Source attachment signs, two new turns and packaged insertion identities |
| SoftFamilyTurns | 4 | Every other old turn, return-direction limit and both ordered determinant signs |
| SoftFamilyLocalCrossing | 4 | Actual incoming/return remoteness and crossing exactly in the loop sector |
| SoftEdgeAvoidance | 3 | Soft edge contacts only its two incident endpoints, on one positive interval |

The source domain has arbitrary attachment vertex and admissible vector. The
index construction literally inserts after that vertex in physical order1,...,n,
including after label n; it is not a cyclically shifted replacement. Extending the
formula to real epsilon supplies limits at zero, while the source family is its
positive restriction. No G1 or Generic premise is asserted at the doubled-vertex
zero tuple. G1 is proved by exhausting old/new triples and preserving the finite
set of nonzero determinants. The exact admissibility clauses handle triples
containing both the old attachment and new vertex.

The local crossing proof retains both strict-straddle tests and separately
excludes endpoint-only intersection. Thus the actual incoming/return pair
crosses if and only if both attachment signs equal the parent turn. The soft
edge exclusion uses compact closed-segment stability at its collapsed limit;
it does not require independent directions for disjoint pairs. Adjacent contacts
are the precise singleton endpoints, and all other enlarged labels are covered.

This covers def:soft and portions of lem:soft-generic. **The complete lemma is
not proved.** Still required: complete inherited-crossing correspondence and
convergence, all visit orders and direction signs, no other births, newborn
convergence, G2, one actual chamber, and the cyclic Gauss-word/short-arc claims.
The final corner soft theorem and wall-laws theorem are also unfinished.

All requested axiom traces use only propext, Classical.choice and Quot.sound.
Six failed root kernels have exact bodies, prototypes and logs preserved;
repairs leave theorem statement text unchanged. The insertion definition repair
only supplies the constant Plane family to dependent Fin.insertNth. All passing
files are frozen. No source axiom, placeholder or source-scope repair was added.

Evidence verification checks68 traces,48 unique candidate evidence files,
1034 frozen baseline files and327 unchanged canonical modules. The last whole
canonical audit is070; no whole-library audit was rerun for these isolated
prototypes. Same-model technical reviews by nonauthors are separate evidence;
they do not grant stronger statement/definition fidelity approval or canonical
integration. Checkpoint088's review-binding receipt verifies all nine group reviews and159
quoted file bindings.

Evidence: checks/checkpoint-088-verification.json,
checks/checkpoint-088-review-bindings.json,
checks/soft-geometry-preserved-failures-20260912.json and
checkpoints/goal-turn-088-candidates.json. Each group's prototype-result.json
binds its actual terminal root kernel, exact code, dependencies and log.

Resume decisions/soft-global-crossings-after-local-geometry.md. Next construct
the actual parent-edge correspondence, then carry the existing Cramer and
compact-disjointness results through all edge pairs. Keep stronger fidelity
review and source acceptance separate from successful Lean compilation.
