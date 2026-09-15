# Soft crossing geometry and Generic chamber candidates

Checkpoint089 adds **59 kernel-checked declarations in seven groups**. Accepted
source proofs remain **19/132 (14.39%)**; original checklist38/191 (19.90%),
expanded checklist39/192 (20.31%), final corner targets0/8. Definitions and
helpers are counted among the59; these are not59 accepted source claims.

| Group | Declarations | Proved scope |
| --- | ---: | --- |
| SoftParentEdges | 15 | Exact parent-edge injection, exhaustive non-soft image, successors and affine edgePoint formula |
| SoftNewbornParameters | 12 | Actual incoming/return parameters, limits1/0/Pj and loop crossing identification |
| SoftInheritedParameters | 13 | Actual parent parameter/point limits, strict crossing persistence and ordered direction signs |
| SoftParentPairStability | 6 | Every remote pair's crossing status, disjoint parallel pairs and simultaneous inherited order |
| SoftCrossingClassification | 3 | Every crossing support is inherited or the loop-sector newborn; no overlap |
| SoftNewbornVisitWindows | 3 | All incoming inherited visits before the newborn parameter; all return inherited visits after |
| SoftFamilyG2 | 7 | Full Generic, G2 and one actual labelled and quotient chamber on a positive interval |

The crossing classification quantifies over every enlarged support. Its proof
exhausts every edge as soft or a corresponding parent edge, excludes remote soft
intersections, and proves that only the incoming/return pair can become remote
after insertion. Its local crossing criterion gives exactly the loop sector.
Injectivity of the support image proves the extra support is not inherited.

The Generic proof uses compact closed-triple persistence. Parent Generic
excludes three distinct closed edges meeting: a remote triple would violate G2,
and an adjacent pair meets at a vertex excluded from any third edge by G1.
Corresponding child segments equal the parent segments at epsilon0, so closedness
and finite continuity preserve all triple exclusions. Soft-edge avoidance
handles every remaining possible child triple. This derives child G2 without
assuming child Generic or the desired crossing classification. The positive
interval's continuous Generic-valued image lies in one actual connected-component
chamber, based at its positive midpoint. The doubled-vertex zero tuple is never
treated as Generic.

Every inherited crossing uses canonical Cramer edge parameters, both strictly
inside the directed segments. Its point/parameters converge to the actual parent
crossing data; ordered determinant signs and all same-edge visit comparisons
persist. The newborn's parameters tend to1 and0 and its point toPj. The loop
theorem identifies them with the actual crossing data. Finite strict comparison
gives the parameter windows needed for its empty oriented arc.

**The full source lemma is still unfinished.** Actual cyclic Gauss-word transport,
oriented newborn adjacency, deletion of its two visits and common-radius assembly
of all printed clauses remain. Parameter inequalities and crossing enumeration
are not being substituted for a proof about the actual Cycle objects. The final
corner soft theorem and wall-laws theorem are also unfinished.

All59 traces use only propext, Classical.choice and Quot.sound. Three failed
root runs have exact bodies/prototypes/logs preserved; repairs change proof
terms only, with unchanged theorem statement text. Verification passed46 unique
candidate evidence files,1115 frozen baseline files and327 unchanged canonical
modules. Last whole canonical audit070; no whole-library audit rerun.

All seven technical-review records are sealed; their binding receipt verifies155
quoted file bindings and coverage of all59 declarations.
These are same-model reviews by body nonauthors. Root's proposed G2 proof strategy
and reviewers' dependency authorship are disclosed; no stronger fidelity approval
or source acceptance is granted. The visit-window docstring's soft-edge exclusion
is contextual: that fact uses the separate admissibility/contact theorem and is
not an arbitrary-q conclusion of the window inequalities.

See checks/checkpoint-089-verification.json,
checks/checkpoint-089-review-bindings.json,
checks/soft-crossings-preserved-failures-20260912.json and
checkpoints/goal-turn-089-candidates.json. Each group has an exact
prototype-result.json receipt. Resume decisions/soft-gauss-word-after-crossing-geometry.md
without changing any frozen proof, source, canonical module or accepted map.
