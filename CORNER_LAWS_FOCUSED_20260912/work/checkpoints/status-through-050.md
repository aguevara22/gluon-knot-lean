# Execution checkpoint — 2026-09-11 UTC, audit050

Accepted ORIGINAL source proofs: 13/132 (9.85%).
Accepted ORIGINAL checklist: 28/191 (14.66%): thirteen proofs and fifteen definitions.
Additional accepted support: lem:weak-open, absent from the frozen focused DAG.
Expanded checklist: 29/192 (15.10%; reporter rounds to 15.1%). Main targets: 0/8.
The wall laws, soft theorem and unconditional R remain incomplete; goal active.
No partial helper contributes an original proof or definition acceptance.

Original accepted proofs:
lem:chi-basic, lem:children, lem:crossing-test, lem:cusp-sides, lem:fibres,
lem:flat-sides, lem:g1, lem:rot, lem:triple-sides, lem:uniformrot,
lem:wall-segment-stability, lem:wall-sides, prop:chambers.
Accepted definitions:
def:admissible, def:chamber, def:chirotope, def:crossings, def:deletion-halves,
def:gauss, def:generic, def:germ, def:interlace, def:polygon, def:regular,
def:shift, def:visible, def:walls, def:weak.

## New verified mathematics: coefficients, resultant and specialized roots

Five new modules: CoordinateIsolation, AffineResultant, RealAffineRoots,
CoefficientSpecialization and GeometricCoordinateSpecialization.
The exact algebra equivalence isolates one actual scalar over the polynomial
ring of all remaining scalars. Slope/intercept coefficients reconstruct the
original polynomial and evaluate correctly. Degree at most one and actual
variable dependence imply a nonzero formal slope.

Irreducibility and EXPLICIT nonassociation imply a nonzero remaining-variable
resultant, using primeness and degree-based nondivisibility. This still requires
concrete family nonassociation to be proved; it is not a substitute for it.
Under the source's specialization tests, the linear polynomial has its unique
root with actual rootMultiplicity=1, and two specialized polynomials cannot have
a common root when their evaluated resultant is nonzero. The geometric wrapper
identifies evaluations with the tuple varying exactly one scalar coordinate,
including preservation of the other component of the same vertex.

Full lem:transport-polynomials remains pending its actual finite named family
and nonassociation, then full clause assembly and independent acceptance review.
No original row is newly accepted. All237 preceding SM files are unchanged;
preserve all242 current SM files for subsequent work. No literature interface
or new axiom is used. Main theorem and stage acceptance are not claimed.

## Independent review and complete audit

Reviewer: review_chirotope-independent-20260910; implementer: root-implementation-20260910.
Review: reviews/transport-coefficients-partial.json, exact28-file SM import closure.
SHA256:4c540c53be0374760517b3048b0d13751566866105f5fa536c34469f115e73a9.
Independent trace session43988 terminal0,22 declaration axiom sets, all exactly
propext,Classical.choice,Quot.sound. Trace checks/transport-coefficients-review-types.log
SHA256:e1f6a5e9db40721cb30a42923a6989d88fd73df230c96b2c4fba61249fa1d7a9.
Final module builds64921,57844,73045 all terminal0; early exploratory failures
were corrected before these successful builds.

Whole audit050 session46358 terminal exit0:242 SM modules,2554 local declarations,
29 mapped claims,248 project files,38 frozen files. All prior237 SM files and
all frozen files remain unchanged. All29 accepted review bindings are current.
Receipt: checks/checkpoint-050-output.json.
SHA256:735f7f3808637e37001a3bb2c851661b48b3aef1f6e13b557aa13e75f3f57538.
Declaration audit SHA256:3b8891f78513a32d3e9f41b743f82eddd47b4cf6146fea14d9aeb2687d72ee21.
Reproduce accepted-review and current-partial-review verification using:
python3 work/checks/verify_named_walls.py work/checks/checkpoint-050-output.json
python3 work/checks/verify_transport_coefficients_checkpoint.py
The latter checks all current/frozen hashes, previous237 files, exact28-file
closure, pins, source, trace, successful build evidence and original progress.
Its first schema attempt expected a singular build log; corrected to verify all
three logs in the independent report and reran successfully.

Earlier review and acceptance details: checkpoints/status-through-049.md and
its earlier archives. No build or audit was live when checkpoint050 was recorded. See the active continuation below.

## Next executable work

Execute decisions/transport-after-coefficients.md. Prove actual variable/vertex
supports, the finite named family, and nonassociation. The proposed diagonal-
collapse witness separates distinct edge matchings without a special n=6
classification. Independent mathematical review confirms it is valid, but its
Lean proof is still UNPROVED. The plan explicitly lists all missing premises.
The initial support draft has moved into the active theorem-library continuation.
The current project has changed since050;050 remains the last complete verified checkpoint.

Only a complete independently reviewed aggregate may accept the original lemma
(sm-1-polygons.tex:1292–1383). Then prove the full thm:relgp and all remaining
polynomial/carrier, transport/comparison, wall-law, soft-theorem and unconditional
R obligations. Keep the same goal; do not replace it by partial targets.
The original unrestricted lem:shift remains locally unaccepted, with its exact
reviewed zero-turn counterexample and explicit nonzero-turn repair unchanged.
repairs/index.json binds050. No author answer is needed.

## Runtime, reporting and sources

Lake:/Users/aguevaragonzalez/.elan/bin/lake.
Lean:leanprover/lean4:v4.34.0-rc2.
Mathlib:85e3a25e006c35636f0e53b0e9296caca2685bc0.
.lake/packages uses the disclosed /tmp/lean-handoff-mathlib-smoke/lean/.lake/packages
cache; eventual delivery must not depend on it.
Run work/claim_progress.py and tools/progress.py --once from the FOCUSED root.
User-requested hourly reporting supersedes ten minutes. Existing automation is
active. Single watcher42482 confirmed live00:33UTC; next report01:00UTC. Poll the
same handle before replacement; an observation timeout is not terminal.
The sources addendum previously passed8checks,11PDF hashes,103manifest entries.
Existing extracts suffice; optional originals and unresolved Reidemeister depth
review are disclosed in reports/sources-addendum-review.md. No source request
is pending. Keep sources, provenance, blueprint, templates and ZIPs unchanged.

