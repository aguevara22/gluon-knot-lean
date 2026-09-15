# Execution checkpoint — 2026-09-11 UTC, audit049

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

## New mathematical progress: T irreducibility and coordinate affinity

The actual concurrencePolynomial is defined as the 3×3 determinant of the source
line rows. Its evaluation equals the existing geometric concurrenceDet. The
public irreducibility/nonzero theorems require exactly n≥3 and three pairwise
remote edges. All algebraic hypotheses are proved internally. The proof uses
primitive-linear irreducibility twice, the explicit FORMAL tail/direction
specialization C=0,A=-1, degree-based nondivisibility, and the existing proved
shear to identify the free polynomial with the actual line determinant.
No Generic hypothesis, pointwise nonvanishing or new axiom is introduced.

CoordinateAffinity and ConcurrenceAffinity also prove degree at most one in
EVERY actual scalar coordinate for Δ and T. The Δ bound follows from its exact
six-term mixed-coordinate expansion. Each T line row is affine, and remote
endpoints force any scalar coordinate to affect at most one row. The six signed
determinant terms therefore retain degree at most one.

Seven new modules are compiled, independently reviewed and audited:
SM.PolynomialLinearCore, SM.LinearConcurrenceCore, SM.LinePolynomials,
SM.FirstTwoLinePolynomials, SM.ConcurrencePolynomialIrreducible,
SM.CoordinateAffinity, SM.ConcurrenceAffinity. All230 preceding SM modules stay
byte-for-byte unchanged. Keep all237 modules unchanged after this checkpoint.

These are PARTIAL SOURCE CLAUSES. The full original lem:transport-polynomials
is still pending: finite family/nonassociation, remaining-variable decomposition,
nonzero slopes/resultants and specialized-root clauses remain required.
No original proof or definition row is newly accepted at this checkpoint.

## Independent source/body review

Reviewer: review_chirotope-independent-20260910, distinct from implementation
root-implementation-20260910. Each review has its own exact23-file SM import
closure, source/pin hashes, type trace and audit049 binding; the two closures differ.

T review: reviews/transport-concurrence-partial.json.
SHA256:9f6974f7c31d7c3749b8f320dbc0bac02081e40216bf36297c4518e55cce99c8.
Independent trace session78218 terminal0,16 declaration axiom sets, log
checks/transport-concurrence-review-types.log SHA256:
6a2908a21e1828841491070f728e96afc1277649b94a92d16d62cc1f065a6e04.

Affinity review: reviews/transport-affinity-partial.json.
SHA256:6f3818388626549a2e5b64ed88b4682ba6fb991a4ea18fe20838e515cd42d9a0.
Independent trace session3488 terminal0,10 declaration axiom sets, log
checks/transport-affinity-review-types.log SHA256:
b4b3e4627d4159e164f72dd54b2c2359d05d2a0e598a8d6920e6ec7b02f57f95.
All traced dependencies are subsets of propext,Classical.choice,Quot.sound.

Successful builds:85299(PolynomialLinearCore),3196(LinePolynomials),96890
(LinearConcurrenceCore and FirstTwoLinePolynomials),39380(full T),43709(affinity),
all terminal0. Initial exploratory linear-core and mixed-coordinate-degree tactic
failures were corrected before the successful builds. No proof gap remains in
the reviewed partial scopes. No author answer is needed.

## Current whole verification: checkpoint049

Whole audit049 passed, session82997 terminal exit0. Exact current inventory:
237 SM modules,2497 local declarations,29 mapped claims,243 project files,
38 frozen files. Only seven SM files and two Supplemental root imports were
added relative to048. All230 prior SM files and all frozen files are unchanged.
All29 accepted original/support reviews and their supporting files are current.
No literature interface is used. Development success is not stage acceptance.

Receipt: checks/checkpoint-049-output.json.
SHA256:9cb9399e7808c0cf2674cca6a3ce46d4a828c7ff0cb06e1ccbfdeccf95196c79.
Declaration audit SHA256:
34c29b2a755d17a755073906441a2b7045a7a57f9992af2052fc87d4d7e0e31d.
Verification: checks/checkpoint-049-verification.json and
checks/checkpoint-049-partial-reviews-verification.json. Reproduce the current
full inventory, prior230-file comparison, all accepted review bindings and both
partial review bindings with python3 work/checks/verify_transport_checkpoint.py.
No build, audit or independent check is live.

The latest accepted original source row remains def:walls. Its exact92-file
closure and134-entry semantic hash are unchanged and reverified on049. The older
Δ/H review is also unchanged in code. Details of all preceding acceptances and
partial work are in checkpoints/status-through-048.md and its earlier archives.

## Next executable work — complete the source lemma

Execute decisions/transport-after-irreducibility-affinity.md. First isolate one
actual scalar variable by the explicit renameEquiv/optionEquivLeft algebra
isomorphism. Prove coefficient decomposition over the polynomial ring of the
remaining variables, with evaluation identities and nonzero slope under actual
variable dependence. Then finish the exact finite family/nonassociation and
resultant/root statements. The plan records candidate prime-divisor and cycle
matching propagation arguments as UNPROVED; discharge every premise in Lean.

The complete lemma is sm-1-polygons.tex:1292–1383. Only full independent review
of every clause may accept the original row. Then execute the COMPLETE thm:relgp
and all remaining polynomial/carrier, transport/comparison, wall laws, soft
theorem and unconditional R obligations. Do not replace these by smaller targets.

The original unrestricted lem:shift remains locally unaccepted: its left-count
reversal is false at a zero turn. The exact independently reviewed quadrilateral
counterexample and explicit nonzero-turn repair remain unchanged; repairs/index
binds049. This does not block the remaining polynomial work.

## Runtime, reporting and sources

Lake:/Users/aguevaragonzalez/.elan/bin/lake.
Lean:leanprover/lean4:v4.34.0-rc2.
Mathlib:85e3a25e006c35636f0e53b0e9296caca2685bc0.
.lake/packages uses the disclosed /tmp/lean-handoff-mathlib-smoke/lean/.lake/packages
cache with these pins. Eventual delivery must not depend on the temporary cache.

python3 work/claim_progress.py reports ORIGINAL proofs; python3 tools/progress.py
--once reports the separate EXPANDED checklist. Run them from the FOCUSED root,
not the parent handoff. User-requested hourly reporting supersedes ten minutes.
Hourly automation remains active. One watcher only: session42482 confirmed live
00:15UTC after its00:00:09UTC report; next report01:00UTC. Poll its actual handle
before replacement; observation timeouts are not terminal. Goal remains active.

The sources addendum previously passed8checks,11PDF hashes,103manifest entries.
Existing extracts suffice to continue; optional originals and unresolved
Reidemeister proof-depth review are disclosed in reports/sources-addendum-review.md.
No additional source request is pending. Keep reference/provenance/blueprint,
original SM/R/BRIDGE, templates and ZIPs unchanged; implement in focused work/.
