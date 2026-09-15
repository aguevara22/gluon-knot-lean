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

## Candidate checkpoint051 — 2026-09-11 00:57UTC

The entire original lem:transport-polynomials now compiles, including concrete
finite family/nonassociation and every coefficient/root clause. Exact source-facing
theorem SM.transport_polynomials: PolynomialControlsStatement n, with n≥3 and
its redundant NeZero instance. The map row is review, not accepted. All242 prior
SM files unchanged; nine new modules extend the project to251SMmodules.

Final complete build54664 terminal0: checks/transport-polynomials-assembly-build.log.
Candidate whole audit051 session58239 terminal0:2749localdeclarations,30mapped,
257projectfiles,38frozenfiles. Receipt checks/checkpoint-051-output.json SHA256:
c0b224868e17345a4cd7520f9da0d2b13460ebd49444966e61b92fcbda621a05.
Audit SHA256:e4bf115972f9fb50e708844e8a1f93ce82ef299429cc07911bca4c9ae26c332e.
Main semantic SHA256:5b75978bcaf47e7ac032c146b24a1f55726d665776ac5311b239f6a44fabedef.
The aggregate binds60semantic entries; exactSMimportclosure39files. Only the
three standard axioms occur. All29previous accepted reviews reverified.
Checks/checkpoint-051-verification.json and
checks/checkpoint-051-full-transport-verification.json reproduce these checks.

Independent reviewer review_chirotope-independent-20260910 confirms complete
source/body fidelity and is running its own final type/axiom trace. A temporary
usage-limit error prevented its first attempt, but retry resumed successfully.
Await reviews/lem-transport-polynomials.json; do not sign on behalf of reviewer.
After full independent review passes, bind the map row and run final audit052.
Current original proofs13/132(9.85%), one COMPLETE compiled proof awaiting review;
original checklist28/191, expanded29/192, main0/8. Goal remains active.

Nine new modules:
PolynomialVertexSupport, AreaPolynomialSupport, SixEndpointTuples,
ConcurrencePolynomialSupport, EndpointCollapseWitness, ConcurrenceNonassociation,
PolynomialControlFamily, PolynomialControlRepresentatives, TransportPolynomials.
All compile without proof placeholders. Early failed finite-array calculations
were replaced by direct formulas; dependent Finset rewrites and set-coercion
elaboration were corrected before the successful build. Concrete nonassociation
uses the independently vetted diagonal-collapse argument, now kernel checked.
Every differently ordered control has proved ± representative coverage.

Next after full acceptance: decisions/relative-general-position-after-polynomials.md
contains the complete thm:relgp obligations and an immediate polynomial avoidance
implementation route. Do not assume all endpoint controls nonzero or classify
inactive T roots as walls. Preserve full wall-law/soft-theorem/unconditionalRgoal.
No build/audit is live; the reviewer may have a live independent trace. Watcher42482
remains the sole progress watcher; next01:00UTC. No author answer is needed.

Next-theorem prototype checks/MultivariateAvoidance.prototype.lean compiled in
session78849 terminal0 at00:59UTC, with five printed axiom sets containing only
propext,Classical.choice,Quot.sound. It proves nonzero real multivariate evaluation,
open-set density and finite simultaneous avoidance for arbitrary scalar types.
Evidence: checks/multivariate-avoidance-prototype-result.json. It is outside the
audited theorem library and awaits independent review; it changes no source count.

Full independent review now PASSED: reviews/lem-transport-polynomials.json
SHA2568274567d955ea7337ff008a27555a4cbd198f7551d5c07342cd0e52d009a9839.
Independent trace63937 terminal0;28standard-only axiom sets and the explicit
n≥3-to-NeZero example. Review and all evidence hashes verified; map row bound
accepted. FINAL audit052 is LIVE session18417 as of01:02UTC. Last completed
whole audit is051. Await terminal052 and run both final verifiers before
reporting the final14/132 acceptance checkpoint. No Lean source changed since051.
Prototype semantic review passed; its independent trace awaits terminal052.
