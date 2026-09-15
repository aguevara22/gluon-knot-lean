# Execution checkpoint — 2026-09-10, audit047

Accepted ORIGINAL source proofs: 13/132 (9.85%).
Accepted ORIGINAL checklist: 28/191 (14.66%): thirteen proofs and fifteen definitions.
Additional accepted support: lem:weak-open, absent from the frozen focused DAG.
Expanded checklist: 29/192 (15.10%; standard reporter rounds to 15.1%).
Main targets: 0/8. The state-sum wall laws, soft theorem and unconditional R
remain incomplete. The goal remains active. Helpers never add original proofs.

Original accepted proofs:
lem:chi-basic, lem:children, lem:crossing-test, lem:cusp-sides, lem:fibres,
lem:flat-sides, lem:g1, lem:rot, lem:triple-sides, lem:uniformrot,
lem:wall-segment-stability, lem:wall-sides, prop:chambers.
Accepted definitions:
def:admissible, def:chamber, def:chirotope, def:crossings, def:deletion-halves,
def:gauss, def:generic, def:germ, def:interlace, def:polygon, def:regular,
def:shift, def:visible, def:walls, def:weak.

## Latest full source acceptance: named walls

Original def:walls is accepted as SM.named_walls_definition in
lean/SM/NamedWallsDefinition.lean, source sm-1-polygons.tex:710–750.
NamedWallsDefinitionData universally quantifies every source-sized actual
continuous wall germ. No desired wall predicate is a top-level assumption.
NamedWallsData exposes all six actual central conditions and real SignChanges,
F/K size restrictions, actual side conventions, and representative independence.

The six kinds are mutually exclusive. Their actual central conditions determine
the type between already simple germs; no arbitrary singularity classification
or claim that the centre forces transversality was introduced. V contact support
has unique marked vertex and edge, and its bigon/sliding subtype follows exactly
the printed central neighbour-chi equality/inequality. The contact sign is actual
negative-side chi, nonzero and independent of side parameter.

F has a unique right(-1) side and complementary left(+1) side. K has its unique
actual betweenness case, exact newborn pair, and loop/no-loop side characterized
by crossing membership at every side parameter. CuspEmptyAt is equivalent to
adjacency of the actual two newborn visits at ANY loop-side point. The actual
cyclic successor transport retains wraparound and two-visit cases. No thread
visits are omitted. Every named predicate and F/V/K convention is equivariant
under actual cyclic parent relabelling. T/C predicates are independent of ANY
equal unordered support, using proved minus-sign invariance of the real product
condition and the actual cardinal-three central sets.

Independent full review: reviews/def-walls.json, exact 92-file source/body closure.
Reviewer: review_chirotope-independent-20260910, distinct from Lean author
root-implementation-20260910; reviewer made no Lean/map changes.
Review SHA256: 1c337dbfccd7961c2360b02e97433d4ec2b4909ed50bf6dd9b8489836f00c0e0.
Main semantic hash (134 entries):
8ff086fefee29d16819d4feb0335c0d3c6b062abdfaa3e4e9d1dfdea869e1086.
The three preceding partial reviews remain in reviews/def-walls-*-partial.json.
All earlier full wall-sides/cusp-sides/children/deletion reviews remain current.

## Current verification: checkpoint047

Final audit047 passed, session19490 terminal exit0. Current inventory:
226 SM modules,2341 local declarations,29 mapped claims,232 project files,
38 frozen files. All exact inventories and hashes match. All29 accepted reviews
and every supporting-file binding are current. All213 previously accepted SM
files remain unchanged, as do all226 candidate046 SM files. Only propext,
Classical.choice,Quot.sound occur; no literature interface is used.
The full focused stage is still incomplete; development success is not stage acceptance.

Receipt: checks/checkpoint-047-output.json.
SHA256: b8aefcd0b4e37f9d5b4a999ef990725c8777b819b6ab2422232a90af1eed73c3.
Verification: checks/checkpoint-047-verification.json, reproducible with
python3 work/checks/verify_named_walls.py work/checks/checkpoint-047-output.json.
Declaration audit SHA256:
fdc0148fd36d9ca6ca654301300c2eeb120daa127f75e704a8a2acfca4c7dc54.
Actual type/definition/axiom trace: checks/named-walls-types.log.
Trace SHA256: e73cf9216859bba9099042fbeb07cdde2c842aac0d9224ae7b36357c97eed363.
Trace session23788 terminal0; candidate046 session32725 terminal0.

The first candidate root build session50045 failed because the new module
redeclared the existing Silent name. It was fixed by reusing unchanged
SilentCenter's exact predicate, and its log retained as
checks/checkpoint-046-initial-failure.log. All other earlier failed exploratory
logs are superseded by the successful whole audits. No build/audit is live.
Previous cumulative status is archived in checkpoints/status-through-045.md,
which preserves links to the earlier full source acceptances and archives.

## Next actual work

Execute decisions/transport-polynomials-after-walls.md for the complete original
lem:transport-polynomials, source sm-1-polygons.tex:1292–1383, then thm:relgp.
The full Δ/T irreducibility, nonassociation, coordinate-affinity, nonzero-resultant
and specialized-root clauses remain required; do not count a smaller lemma as
the original. Preserve all226 reviewed/audited SM files. The named-wall plan is
complete; do not redo it or the accepted wall-sides/cusp-sides/children proofs.

Concrete next-chain progress outside the audited project:
checks/determinant-core-candidate.lean proves irreducibility over ℝ of the actual
four-variable polynomial X(inl false)*X(inr false)-X(inl true)*X(inr true).
It uses pinned MvPolynomial.irreducible_sumSMulXSMulY with coefficients1,-1 and
proves the bilinear-expression identity. Successful session51799 terminal0;
only propext,Classical.choice,Quot.sound. Candidate source SHA256:
3c423c51057caed6ff0626ec12f5d08721b5533ee3b03ac8d2f326ee6c95e076.
Candidate log SHA256: b45c11778dbd700bb4f2fb7b42a4d22af84fd4aaa64e06d4c29bd45e3fbc3b11.
This prototype is not in the audited project and is not an accepted original
claim. Independent narrow review is assigned to review_chirotope; check
reviews/transport-determinant-core-prototype.json for completion. Next integrate
its proved algebra into new actual coordinate-polynomial modules, with explicit
geometric evaluation and invertible-coordinate-change proofs. The source Δ/H/T
irreducibility and the complete original lemma remain unproved.

The state-sum polynomial/carrier chains, all direct laws, full cusp transport/
comparison, soft theorem and unconditional R remain part of the same goal.
Original lem:shift stays locally unaccepted: the unrestricted left-count reversal
is false at zero turns. The reviewed exact quadrilateral counterexample and
explicit nonzero-turn repair remain unchanged; repairs/index.json now binds047.
This local issue does not block the next polynomial work.

## Runtime and reporting

Lake: /Users/aguevaragonzalez/.elan/bin/lake.
Lean: leanprover/lean4:v4.34.0-rc2.
Mathlib:85e3a25e006c35636f0e53b0e9296caca2685bc0.
.lake/packages uses /tmp/lean-handoff-mathlib-smoke/lean/.lake/packages with
those exact pins. Eventual delivery must not depend on this temporary cache.

python3 work/claim_progress.py reports ORIGINAL proofs; python3 tools/progress.py
--once reports the separate EXPANDED checklist. Latest checkpoint report at
23:37:45 UTC:9.85% original,15.1% expanded. User-requested hourly reporting
supersedes the ten-minute handoff default. Hourly automation remains active.
Keep one watcher: session42482 confirmed live at23:34UTC; next report00:00UTC.
Poll the actual handle before any replacement. Observation timeout is not terminal.

## Sources and autonomy

The sources addendum passes8checks,11PDF hashes and103manifest entries. Intake:
reports/sources-addendum-review.md. Existing extracts suffice to continue;
optional originals improve page/figure verification. Reidemeister proof-depth
review remains open, with Queffelec2024 already supplied. No literature interface
has been used. No author question is needed. Keep reference/provenance/blueprint,
original SM/R/BRIDGE, templates and ZIPs unchanged; implement only in work/.
