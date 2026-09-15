# Flat-wall incident responses: checked candidates

Accepted original claims remain **19/132 (14.39%)**. Original checklist:
38/191 (19.90%); expanded checklist: 39/192 (20.31%); final targets: 0/8.
This checkpoint adds 40 checked candidate declarations, with no new accepted
source claim and no change to canonical definitions or the axiom policy.

The boundary calculation covers all three physical-root cases, including
four vertices. A nonincident root gives three consecutive critical positions,
two singleton gaps and a proper span. Incoming and outgoing roots give a full
span with gap lengths respectively (1,n-2) and (n-2,1). Each case has the exact
critical labels and unordered support, not just abstract interval positions.

Strict betweenness constructs the actual affine coordinates and a nonzero
direction. The three epsilon pairs are proved to be (+,+), (-,+), and (+,-).
For every cyclic critical order the reversed boundary sign equals minus the
turn at the deleted vertex; this also transports the germ sign-change premise.
The integer gap factors are proved exactly: two leaves contribute one; each
incident case has unbarred product zero and barred product equal to its nonleaf
B output.

Both incident nonleaf closed words are proved pointwise equal to the deleted
polygon shifted by -1, including the wrap at local index zero. This sends the
gap root zero to the fused deletion root -1. A proved tuple-equality lemma
transports the dependent G1 witness; cyclic covariance then identifies each
integer B output with the actual deletion tree coefficient at fusionIndex.
Parent G1 is not assumed: deletion G1 follows from the singleton turn support.

The assembled incident germ theorem has one fixed integer sign and one positive
radius, followed by arbitrary independent nearby negative and positive
parameters. It proves the integer turn-difference normalization and amplitude
difference equal to that sign times the deletion coefficient at the physical
fused root. The final wrapper covers every source size: FlatAt supplies the
minimum arity, from which the normalized m+4 presentation is constructed.

This is still a **signed time-side response for incident roots**. The source's
right-minus-left normalization and the nonincident contracted/deleted tuple
identification remain to be proved and assembled. Consequently thm:A-S3 and
the final corner wall laws/soft theorem are not claimed complete or accepted.

## Evidence

| Candidate group | New declarations | Successful session |
|---|---:|---:|
| FlatBoundaryPositions | 16 | 50897, second attempt |
| FlatAffineSigns | 9 | 53680, first attempt |
| IncidentFlatGapTuples | 7 | 40179, fourth attempt |
| FlatIntegerFactors | 4 | 65014, first attempt |
| FlatIncidentResponse | 3 | 5174, second attempt |
| FlatIncidentAllSizes | 1 | 86495, first attempt |

All successful sessions exited zero. Printed axiom traces use only propext,
Classical.choice and Quot.sound, or subsets. Failed attempts and their exact
bodies/prototypes/logs are preserved. Repairs exposed reducible index/size
definitions, transported a dependent G1 proof across tuple equality, supplied
the explicit child arity, and unfolded the germ's zero-support abbreviation.
All original statements were retained; one general coefficient-congruence
helper was added and proved.

checks/verify_flat_incident_candidates.py passed on 40 candidate traces,
50 distinct evidence files, 485 frozen baseline files and all 327 canonical
modules. This verifies recorded evidence and preservation; it does not replace
source review or a canonical build. The last whole-library audit remains070.
The accepted map is untouched. Candidate declarations are recorded separately
in checkpoints/goal-turn-077-candidates.json.

Separate-agent technical reviews use the same currently available model. They
do not supply the stronger statement/definition-fidelity approval requested by
the user. Stronger review and controlled canonical integration remain pending.
No source, reference, supplied addendum, template or archive was edited.

Next implement decisions/nonincident-flat-tuple-identification-20260911.md,
then the full source side-order normalization. That file is an untested proof
plan, not evidence that the nonincident identity already compiles.
