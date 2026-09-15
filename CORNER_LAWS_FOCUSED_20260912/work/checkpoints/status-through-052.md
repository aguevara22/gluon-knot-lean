# Execution checkpoint — 2026-09-11 UTC, audit052

Accepted ORIGINAL source proofs: 14/132 (10.61%).
Accepted ORIGINAL checklist: 29/191 (15.18%): fourteen proofs and fifteen definitions.
Additional accepted support: lem:weak-open, absent from the frozen focused DAG.
Expanded checklist: 30/192 (15.625%; reporter rounds to15.6%). Main targets:0/8.
No complete compiled original proof awaits review. The wall laws, soft theorem
and unconditional R remain incomplete. The full goal remains active.

Original accepted proofs:
lem:chi-basic, lem:children, lem:crossing-test, lem:cusp-sides, lem:fibres,
lem:flat-sides, lem:g1, lem:rot, lem:transport-polynomials, lem:triple-sides,
lem:uniformrot, lem:wall-segment-stability, lem:wall-sides, prop:chambers.
Accepted definitions:
def:admissible, def:chamber, def:chirotope, def:crossings, def:deletion-halves,
def:gauss, def:generic, def:germ, def:interlace, def:polygon, def:regular,
def:shift, def:visible, def:walls, def:weak.

## New original acceptance: full lem:transport-polynomials

SM.transport_polynomials in SM.TransportPolynomials proves the entire transparent
PolynomialControlsStatement for the actual finite family. Source:
reference/SM/sm-1-polygons.tex:1292–1383. Main semantic hash,60entries:
5b75978bcaf47e7ac032c146b24a1f55726d665776ac5311b239f6a44fabedef.

The names are exactly all unordered three-vertex sets and unordered triples of
pairwise-remote edges. Each has one chosen ordered representative. All raw
orderings are covered up to a proved sign; the name-to-polynomial map is
injective. Actual geometric evaluation, nonzero irreducibility, distinct-name
nonassociation, separate-coordinate affinity, exact remaining-variable
coefficients, nonzero formal slopes/resultants and specialized root statements
are all included. The main theorem assumes no family nonassociation, Generic
or geometric noncollision hypothesis. Its only size restriction is n≥3; the
redundant NeZero instance is independently proved from that restriction.

Nonassociation is concrete. Actual variable supports give exactly three area
vertices or six concurrence endpoints. For distinct edge pairings on equal
supports, a proved collapsed-edge specialization makes one determinant zero and
the other nonzero for every endpoint/row order. If the two endpoints lie in one
edge pair, the cycle tail is identified; a reversed cycle edge would force n∣2,
contrary to n≥3. Thus associated polynomials have equal tail sets. This includes
the source's n=6 exceptional matchings without an unproved classification.

The coefficient/resultant theorem now receives proved concrete irreducibility
and nonassociation. It retains the source's genuine-dependence conditions.
At a specialization with nonzero slope, the unique real root has actual
rootMultiplicity=1. A nonzero evaluated resultant excludes common real roots
without extra slope assumptions. No literature interface or custom axiom is used.

Nine new modules after050:
PolynomialVertexSupport, AreaPolynomialSupport, SixEndpointTuples,
ConcurrencePolynomialSupport, EndpointCollapseWitness, ConcurrenceNonassociation,
PolynomialControlFamily, PolynomialControlRepresentatives, TransportPolynomials.
All242 preceding SM files are byte-for-byte unchanged. Preserve all251 current
SM files after this completed review; implement later work in new modules.

## Independent full review and final verification

Reviewer: review_chirotope-independent-20260910.
Implementer: root-implementation-20260910.
Review: reviews/lem-transport-polynomials.json SHA256:
8274567d955ea7337ff008a27555a4cbd198f7551d5c07342cd0e52d009a9839.
Exact39-file SM closure:9new,30inherited. All inherited support hashes match
previous independent reviews. Complete source/type/body review covers every
clause and confirms no strengthened mathematical domain.
Independent trace63937 terminal0:28axiom sets, all subsets of
propext,Classical.choice,Quot.sound. It also proves the redundant size instance.
Trace checks/transport-polynomials-review-types.log SHA256:
30db3d2c076d9cc48d3ea70acaa2cbc326c9ab578aed1766eff8e34f743c82fa.
The first reviewer attempt hit a temporary usage limit; retry resumed and
completed the full review. An unsupported pretty-printer option in its first
trace was corrected in the check file only. No author intervention was needed.

Complete implementation build54664 terminal0:
checks/transport-polynomials-assembly-build.log SHA256:
ddf7b0b3947d4d195a47cb82b2b98ddd3350ddfe4c885364ab83f5be70abf61a.
Candidate051 session58239 terminal0; final052 session18417 terminal0.
Final audit:251SMmodules,2749localdeclarations,30mappedclaims,257projectfiles,
38frozenfiles. All30accepted review bindings and all frozen hashes are current.
The only change after candidate051 is the independently justified acceptance
metadata in lean-declarations.json. All251 candidateSM files remain unchanged.
Receipt: checks/checkpoint-052-output.json SHA256:
b9cd9804c4c3f4176819cc3ec511bb6e4392ea4c67b52483bfa64cf1ff3b8f7d.
Declaration audit SHA256:
e4bf115972f9fb50e708844e8a1f93ce82ef299429cc07911bca4c9ae26c332e.

Current verifiers, both terminal0:
python3 work/checks/verify_named_walls.py work/checks/checkpoint-052-output.json
python3 work/checks/verify_transport_full_checkpoint.py work/checks/checkpoint-052-output.json
The latter checks every current/frozen hash, all242 priorSM files, the exact39-file
closure, semantic hash, full independent review, pins, trace, inherited reviews
and unchanged candidate code. Development success is not full-stage acceptance.
No build or whole audit is live. Earlier history is in
checkpoints/status-through-051.md, checkpoints/status-through-050.md and older
archives. Those retain the progressive partial work before this full acceptance.

## Next executable work: the complete thm:relgp

Execute decisions/relative-general-position-after-polynomials.md. Keep every
source requirement: fixed labelled endpoints, uniform approximation in the actual
regular locus, collision freedom, finitely many isolated simple transversal named
walls, no cusp, and all labels retained. Generic endpoint collars must allow
inactive concurrence-polynomial zeros. Such inactive roots are not wall events.
Do not replace this theorem or the full main goal with a weaker target.

The immediate joint-polynomial-avoidance prototype is already kernel compiled:
checks/MultivariateAvoidance.prototype.lean, session78849 terminal0, five
standard-only axiom traces. Evidence: checks/multivariate-avoidance-prototype-result.json.
It proves a nonzero real multivariate evaluation exists, density of nonvanishing,
and finite simultaneous nonvanishing in any nonempty open set for arbitrary
scalar-variable types. It is outside the audited theorem library and changes no
source count. Its independent prototype review is now faithful and complete for this partial
scope: reviews/multivariate-avoidance-prototype.json SHA256
d2853b0311f247589c24e7183ad6b8e38bed73e6e5ed3da8099264ee3be5c985.
Independent trace13618 terminal0, including the empty-condition-family case;
log SHA256a6165b6f7999363b358d338b9a6f391d198cdde8a041576d02b8917a2a2298e4.
Verification: checks/checkpoint-052-avoidance-prototype-verification.json checks
the exact prototype/check prefix, trace, pins, source and unchanged052 inventory.
Reproduce with python3 work/checks/verify_avoidance_prototype.py. The first ad-hoc
check used the bundle path guard on the external shared library cache; the final
verifier checks those files inside the resolved pinned Mathlib root and every
hash matches. No proof or reviewed file changed. No reviewer check is live.
Port the exact mathematical body into a new module and
prove actual joint waypoint/hybrid pullback injectivity and nonzero constraints.
No joint waypoint/path/wall conclusion is yet certified by this prototype.

The original unrestricted lem:shift remains locally unaccepted: the reviewed
regular zero-turn quadrilateral refutes its unrestricted left-count reversal.
The exact counterexample and explicit nonzero-turn repair remain unchanged;
repairs/index.json binds052. This local issue does not stop other work.

## Runtime, reporting and sources

Lake:/Users/aguevaragonzalez/.elan/bin/lake.
Lean:leanprover/lean4:v4.34.0-rc2.
Mathlib:85e3a25e006c35636f0e53b0e9296caca2685bc0.
.lake/packages uses the disclosed /tmp/lean-handoff-mathlib-smoke/lean/.lake/packages
cache; eventual delivery must not depend on this temporary cache.
Run work/claim_progress.py and tools/progress.py --once from the FOCUSED root.
User-requested hourly reporting supersedes ten minutes. Existing automation is
active. Single watcher42482 confirmed live01:00UTC; it reported the previous
13/132-era checklist at01:00:09, before final052. The new14/132,30/192 report ran
at01:02:59UTC. Next watcher report02:00UTC. Poll its actual handle before replacing;
observation timeouts are not terminal. Goal remains active; no author question.
The sources addendum previously passed8checks,11PDF hashes,103manifest entries.
Existing extracts suffice; optional originals and unresolved Reidemeister depth
review are disclosed in reports/sources-addendum-review.md. Keep frozen sources,
provenance, blueprint, templates and ZIPs unchanged.
