# Full cusp tree coefficient law: candidate checkpoint079

The Lean-checked candidate `SM.WallGerm.cusp_tree_law` now derives the source
cusp law, thm:A-S4. It constructs the unique central cusp case and a single
integer rotation jump, either -1 or+1, before all independent loop/no-loop side
parameters and all physical roots. The actual coefficient difference is minus
that jump times the actual center-deletion coefficient at `fusionIndex j g`.
The jump is proved equal to the actual real rotation-number difference. There
is no emptiness, nearby-radius, root-independence or R assumption. This is a
rooted tree coefficient dependency, not the final corner state-sum theorem.

Accepted progress remains19/132 original source proofs (14.39%),38/191 original
checklist rows (19.90%),39/192 expanded rows (20.31%), and0/8 final targets. The
source row remains pending stronger statement/definition-fidelity approval and
controlled canonical integration/checker acceptance. Same-model technical
reviews do not meet that stronger approval requirement.

## Checked additions

| Group | Declarations | Passing root |
|---|---:|---:|
| CuspIntegerFactors | 4 | 35543 |
| CuspAffineSigns | 5 | 39700 |
| CuspSignedResponse | 5 | 30121 |
| CuspOrientedResponse | 2 | 95209 |
| CuspSourceResponse | 2 | 68098 |

All18 declarations passed with exit0. Each printed axiom trace is a subset of
propext, Classical.choice and Quot.sound, with no sorryAx or literature axiom.
The final aggregate receipt binds53 files. Failed first roots7575 and64876,
exact bodies/prototypes/logs and unchanged statement text are preserved. Repairs
only enabled explicit SignType conditional simplification and unfolded the
actual sideTuple definition for comparison with curve values at sideTime.

The source cusp predicate gives separated endpoints and a zero determinant.
The coordinate proof constructs its scalar by the dot-product formula and uses
the actual exterior condition to prove r<0 or r>1. Four ratio calculations and
four integer-factor conjunctions reproduce all incident table cases, including
which summand is zero. The nonincident unit factor and full contracted/deleted
identities are valid independently of flat betweenness. No FlatAt hypothesis
enters the cusp proof, despite historical 'flat' names on shared index helpers.
Deletion G1 is derived from the actual singleton critical support.

The signed response includes both incident roots and every nonincident root,
then covers every source size including four vertices. Negative-chirotope
minus positive-chirotope equals the deletion coefficient. Generic connected-side
chirotope constancy removes the temporary proximity restriction. Actual
cusp_loop_turns and cusp_rotation_jump identify the loop orientation. The final
wrapper uses side constancy to choose one integer jump before all parameters
and roots; it does not merely assign a separate sign to each evaluation.

Evidence verification passed18 traces,61 distinct candidate evidence files,
559 frozen baseline hashes and327 unchanged canonical SM modules. This is not
a fresh whole-library build or source fidelity certificate. The last canonical
audit remains070 (4,263 declarations,39 mapped claims). Accepted definitions,
axioms, declaration map, supplied sources, templates and prior passing bodies
are unchanged. Candidate ledger: checkpoints/goal-turn-079-candidates.json.

Separate nonauthor same-model technical reviews cover the integer factors,
affine/sign construction, signed/oriented assembly, and final loop/rotation
normalization. Root reviews the separate agent's affine body; that agent reviews
root-authored bodies. No stronger fidelity or source acceptance is claimed.

Next: decisions/vertex-edge-tree-law-after-cusp.md, targeting thm:A-S7 on both
bigon and sliding branches with exact half-root maps and complete tuple
identities. Other corner laws, soft theorem and R assembly remain incomplete.
The existing original shift-scope obstruction remains separate. No author
question is required.
