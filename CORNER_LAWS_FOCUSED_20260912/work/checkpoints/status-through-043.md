# Execution checkpoint — 2026-09-10

Accepted ORIGINAL source proofs: 12/132 (9.09%).
Accepted ORIGINAL checklist: 25/191 (13.09%): twelve proofs and thirteen definitions.
Additional accepted support: lem:weak-open, absent from the frozen focused DAG.
Expanded checklist: 26/192 (13.54%; standard reporter rounds to 13.5%).
Main targets: 0/8. State-sum wall laws, the soft theorem and unconditional R
remain incomplete. The goal remains active. Helpers never add original proofs.

Original accepted proofs:
lem:chi-basic, lem:crossing-test, lem:cusp-sides, lem:fibres, lem:flat-sides,
lem:g1, lem:rot, lem:triple-sides, lem:uniformrot, lem:wall-segment-stability,
lem:wall-sides, prop:chambers.
Accepted definitions:
def:admissible, def:chamber, def:chirotope, def:crossings, def:gauss, def:generic,
def:germ, def:interlace, def:polygon, def:regular, def:shift, def:visible, def:weak.

## Latest accepted source result: full cusp lemma

Full original lem:cusp-sides is independently accepted as
SM.cusp_sides_of_continuous_curve in lean/SM/CuspCurve.lean, source
reference/SM/sm-1-polygons.tex:1024–1225. All four clauses are proved:

- The exact raw continuous curve hypotheses construct the actual WallGerm;
  central nongenericity follows from the sole zero triple. The two central
  cases are exclusive, and the selected remote pair and cyclic indices include n=4.
- One positive common radius controls actual nonzero Delta and its sign,
  including zero. Actual finite-segment tests and source SignChanges derive
  the unique loop side. Every other unordered crossing support persists.
  Needle signs and all side comparisons permit independent side parameters.
- The actual newborn visits are distinct, have the same crossing and exhaust
  its two occurrences in the actual cyclic Gauss word. The closed short arc
  is precisely terminal edge f, full edge f+1, initial edge f+2, with exactly
  the two source polygon vertices. A thread has its actual partner in the
  complementary arc. Actual cyclic successor adjacency makes this particular
  short arc empty, hence the middle edge crossing-free on both entire sides.
- Actual principal-angle limits at the antiparallel corner are plus/minus pi,
  selected by the actual determinant signs. Other principal turns have common
  limits. Proved rotation integrality and constancy on each connected Generic
  side give rot(loop)-rot(no)=turn_j(loop), with sign in {-1,1}. The source
  rotation at the singular centre is never assigned or assumed.

The 18 new modules finish the nine local cusp modules at041. All 185 prior SM
files are unchanged. This is the geometric cusp lemma, not a main state-sum law.

Independent full review: reviews/lem-cusp-sides.json.
Reviewer: review_chirotope-independent-20260910, not the implementation author.
Review SHA256: 1e4fe3928dab67e4c8b5f27fc76777bbbfc7b620684fefae96d946d20c665cb0.
Exact 74-file source/body import closure; 108 semantic definition entries.
Main semantic SHA256:
fc86e8effeeb5b38737a86d14fe2a5191f1eabb2986f88aa886538910940df59.
The adjacency interpretation, all raw-domain clauses and the full rotation
argument were independently reviewed against actual compiled types and bodies.

## Current verification: checkpoint043

Candidate042 and final043 both passed. Final043:
203 SM modules; 1946 local declarations; 26 mapped claims; 209 project files;
38 frozen files. Exact inventories and all project/frozen hashes match.
All 26 accepted reviews and their complete supporting-file hashes are current.
Only propext, Classical.choice and Quot.sound occur. No literature interface
or new project axiom is used. Full-stage acceptance remains false.

Receipt: checks/checkpoint-043-output.json.
SHA256: be4572aa34f404d05a299fa793e4270eec1d7ae7ad68d88d9722d1e29219eb6b.
Verification: checks/checkpoint-043-verification.json.
Type/definition/axiom trace: checks/cusp-sides-types.log.
Trace SHA256: be8caa6e8d190061185aff85bc935db2949ba7c3deab7c185060ed550f9506ef.
Handles: audit042 session26283, trace70259, audit043 session33786: all terminal0.
No proof file changed between the reviewed candidate and final audit.
Prior cumulative statuses are archived in checkpoints/status-through-038.md
and checkpoints/status-through-041.md. Historical partial cusp review041 is
superseded for source acceptance by the full review, while retaining its evidence.

## Next work and local source obstruction

Execute decisions/children-after-cusp.md: actual deletion/halves definition
and full lem:children, source sm-1-polygons.tex:1227–1290. The flat deletion,
central Generic child and nearby chamber branch are already proved and should
be reused. Construct both actual contact halves, prove size bounds 3..n-2,
inherited cyclic order, injective vertex/edge maps, positive cut-edge interior
inclusions, then G1/G2 and the full original aggregate. No literature is needed.

Do not redo cusp-sides-next.md or cusp-after-local041.md; both are complete.
Full def:walls stays pending/unmapped until all side/empty conventions,
mutual exclusivity, centre classification and cyclic transports are proved.
The completed cusp theorem now supplies its K local geometry and loop/empty
consequences, but does not by itself accept that larger definition.

Original lem:shift stays pending: its unrestricted left-count reversal is false
with a zero turn. The reviewed kernel counterexample has counts 3 and 0, while
n-left is 1. Use the separate reviewed repair only with its explicit nonzero-turn
premise, discharged for Generic consumers. It is not accepted as the original.
Its evidence is in repairs/index.json and is unchanged. This is a local issue,
not a reason to stop independent work.

## Runtime and reporting

Lake: /Users/aguevaragonzalez/.elan/bin/lake.
Lean: leanprover/lean4:v4.34.0-rc2.
Mathlib: 85e3a25e006c35636f0e53b0e9296caca2685bc0.
.lake/packages uses the exact cache at
/tmp/lean-handoff-mathlib-smoke/lean/.lake/packages. Eventual delivery must not
rely on this temporary cache; restore exact pins if needed, without asking.

Run python3 work/claim_progress.py for ORIGINAL proof percentage;
python3 tools/progress.py --once reports the separate EXPANDED checklist.
Latest checkpoint reports at 22:34:54 UTC: 9.09% original, 13.5% expanded.
Hourly automation hourly-lean-formalization-progress remains active. The user
requested hourly reporting, overriding the ten-minute handoff default. Keep
one watcher only: session 42482 confirmed live at 22:35 UTC. Last hourly output
22:00:09 UTC was relayed; next is 23:00 UTC. Poll that actual handle before any
replacement. A timeout is not terminal; continue observing the same live handle.

## Source availability

The sources addendum is sufficient to continue. Its prior intake/reverification
passed 8 checks for 11 PDFs and 103 manifest entries; see reports/sources-addendum-review.md.
Full Lickorish–Millett 1987, Lickorish 1997 pp.168–172 and Geiges 2008 pp.108–132
originals would improve page/figure checks; existing extracts suffice now.
Reidemeister proof-depth review remains open, with Queffelec 2024 already supplied.
The five-interface policy is unchanged and none has been used. No author
question is required. Record nonblocking decisions in AUTHOR_NOTES.md.
