# Full flat tree coefficient response: candidate checkpoint078

The Lean-checked candidate `SM.WallGerm.flat_right_minus_left` now states the
flat law for the actual rooted tree coefficient: every permitted source size,
every physical root, and arbitrary independent punctured right/left parameters
in the actual wall germ. Right has turn -1 and left has turn +1. The right-hand
side is the actual center-deletion coefficient at `fusionIndex j g`. There is
no nearby-radius restriction, root-independence assumption or R parameter.
This is the dependency source thm:A-S3, not the final corner state-sum theorem.

Accepted progress is unchanged: original source proofs19/132 (14.39%); original
checklist38/191 (19.90%); expanded checklist39/192 (20.31%); final targets0/8.
The source row remains pending. All new work is candidate material, awaiting
stronger statement/definition-fidelity approval and controlled canonical
integration/checker acceptance. Same-model technical reviews do not supply
that stronger approval.

## Checked work

| Group | New declarations | Passing root |
|---|---:|---:|
| FlatContractionArithmetic | 5 | 93700 |
| TupleArityTransport | 3 | 29466 |
| TurnResponseOrientation | 2 | 81061 |
| NonincidentFlatContraction | 4 | 86583 |
| FlatNonincidentResponse | 1 | 31841 |
| FlatAllRootResponse | 2 | 58448 |
| GermNearbyChirotope + FlatSourceResponse | 2 | 25627 |

All19 declarations passed with exit0; each printed axiom trace is a subset of
propext, Classical.choice and Quot.sound. No literature axiom or sorryAx occurs
in those traces. Receipts bind the complete embedded candidate bodies, exact
prototype and successful log. The final aggregate binds48 files. Earlier
failed roots5271 and7171, their bodies/prototypes/logs, and the unchanged theorem
statements are preserved. Repairs only handled equality induction and reduction
of a dependent Fin projection before rewriting its natural representative.

The nonincident calculation proves every surviving label and the whole tuple
identity after explicit size transport. It derives the exact physical-root
coefficient using proved cyclic covariance. Both singleton gaps give unit
factor1 and the span is proper. The signed germ response combines with the
previous incident cases to exhaust all roots. The orientation proof handles
both possible time orders. For arbitrary punctured representatives, an explicit
same-side parameter at distance δ/2 preserves the entire chirotope; established
coefficient constancy then removes the local restriction. No geometric
hypothesis was replaced by an assumed invariance rule.

The evidence verifier passed19 traces,60 distinct evidence files,524 frozen
baseline hashes and all327 canonical SM modules unchanged. This is evidence
verification, not a fresh whole-library build or fidelity certificate. The
last canonical audit remains070 (4,263 declarations and39 mapped claims).
The accepted map and axiom policy remain unchanged. Candidate ledger:
`work/checkpoints/goal-turn-078-candidates.json`.

Technical review scope: arithmetic/size transport, full nonincident tuple and
coefficient, signed/nonincident/all-root assembly and final representative
extension. Root independently reviewed the separate agent's orientation body;
that agent reviews the root-authored bodies. Reviews are disclosed as same-model
only. One documentation misnomer is recorded: the nonincident helper comment's
'fused root' means the induced retained root; the theorem itself uses the correct
`fusionIndex` and never identifies it with the fused edge.

Next: `work/decisions/cusp-tree-law-after-flat.md`. Reuse the geometry-independent
deleted tuple identities; derive the cusp's exterior coordinates and four
incident epsilon/factor cases; inspect existing rotation and loop-side results
for exact-domain assembly. Full cusp, other corner laws, soft theorem and R
assembly remain incomplete. No author question is required.
