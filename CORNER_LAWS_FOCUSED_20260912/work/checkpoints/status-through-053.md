# Execution checkpoint — 2026-09-11 UTC, audit053

Accepted ORIGINAL source proofs:14/132 (10.61%).
Accepted ORIGINAL checklist:29/191 (15.18%):fourteen proofs and fifteen definitions.
Extra accepted support:lem:weak-open. Expanded checklist:30/192 (15.625%;15.6%).
Main targets:0/8. No complete original proof awaits review. The wall laws, soft
 theorem and unconditional R remain incomplete. Full goal remains active.

## New supporting mathematics for the complete thm:relgp

Seven new modules:MultivariateAvoidance, WaypointPullback, CoordinateWaypointLeg,
JointWaypointConstraints, WaypointOpenDomain, ScalarCoordinateTopology,
CentralLegCollision. All251 previous SM files remain byte-for-byte unchanged.
Preserve all258 now-reviewed/audited SM files; implement later work in new files.

The mathematical namespace of MultivariateAvoidance is an exact port of the
previous independently reviewed prototype. Actual joint variables are pairs of
internal waypoint labels and original scalar-coordinate labels. Every full or
remaining-coordinate hybrid selection retains the original scalar label, so
injectivity of polynomial renaming proves nonzero pullbacks. For the actual named
Δ/T family, every endpoint control, genuinely dependent slope/resultant, scalar
step and both-coordinate distinct-vertex difference is proved formally nonzero.
The finite-condition family is equivalent to the transparent JointLegConditions.

SM.exists_joint_waypoint_conditions_in_domains gives ONE common assignment for
ALL supplied finite central legs, within every supplied nonempty open internal
waypoint domain. Those domains form an actual nonempty open product. No polynomial
nonzeroness, general-position oracle, Generic or Regular premise is added. This
has not yet constructed the domains from the original path and cube overlaps.
The original fixed path endpoints remain outside these joint independent variables;
the Generic collars still need construction and must allow inactive T zeros.

SM.scalarCoordinateHomeomorph is the actual tuple/scalar homeomorphism. It does
not equate the product max norm to the Euclidean norm. The actual coordinate leg
is proved equal to the affine scalar line, hence continuous, with both exact local
labelled endpoints. SM.central_leg_collision_free proves injective vertex positions
for every real leg parameter, with no Regular premise: the unmoved Fin2 component
is fixed at every vertex and separates every distinct pair. These conditions are
already supplied by the preceding simultaneous choice, not assumed without proof.

## Independent partial reviews and complete verification

Implementer:root-implementation-20260910.
Reviewer:review_chirotope-independent-20260910; authored no implementation.
Five-module choice build64346 terminal0; two-module topology/collision build28953
terminal0. Independent choice trace62188 terminal0:23 declarations (21 use only
standard axioms;two need none). Collision trace12873 terminal0:nine standard-only
axiom sets and both exact labelled tuple endpoint examples. No literature input
or custom axiom is used. These bounded results do not accept full thm:relgp.

reviews/joint-waypoint-choice.json SHA256:
8609999cf4db4b00f221df4ac7ba0a4140eb7c81df2bdd78baa739c610d495f5.
Exact44-file closure=five new +39 accepted polynomial-controls dependencies.
reviews/central-leg-collision.json SHA256:
ba952b2e4a189cb7132b537fe584219c035ce10303d445d362ff2351bc21af35.
Exact45-file closure=two new +43 unchanged dependencies of the joint-choice review.
Both reports bind source, compiled files, pins, successful builds and independent
traces; they explicitly distinguish prior052 context from their new implementations.

Whole audit053 session41721 terminal0:258 SM modules,2878 local declarations,
30 mapped claims,264 project files,38 frozen files. All30 accepted semantic review
bindings remain current. No declaration-map entry changed; Supplemental.lean is
the sole changed prior project file, adding imports of the new supporting modules.
Receipt:checks/checkpoint-053-output.json SHA256:
834abff215428705dd60604d2a9fe5d0c364e7a435c201965e2205c32e5bc276.
Declaration audit SHA256:
52157a5766e998c371ddc3ecb04c9d6fa2f165a9739895e88b810272c54ffa22.
Do not print the raw large audit/log. Both final verifiers passed terminal0:
python3 work/checks/verify_named_walls.py work/checks/checkpoint-053-output.json
python3 work/checks/verify_joint_waypoint_checkpoint.py work/checks/checkpoint-053-output.json
Their receipts record current/frozen inventories, all251 prior SM hashes, both
new independent reviews and traces, all30 existing accepted bindings, the exact
prototype mathematical port and unchanged original proof count. Development pass
is not full-stage acceptance. No build, audit or independent review check is live.

## Next executable step

Execute decisions/relative-general-position-after-joint-choice.md. First prove
actual central-leg parameter restriction polynomials: the true parameter slope is
the evaluated coordinate slope times the nonzero scalar step; the constant is
the actual initial control value. Independent controls stay nonzero constants;
dependent ones have simple sign-changing roots. Prove no common or endpoint roots
and finite root sets over all actual finite legs/control names.

Then construct regular open boxes with the required Euclidean diameter bound,
the actual finite subdivision and nonempty overlap domains, Generic endpoint
collars, ordered coordinate-leg family and continuous piecewise-affine path with
exact fixed global labels/endpoints and uniform tolerance. Finish actual F/bothV/T/E/C
classification, inactive-T treatment, T/crossing-parameter identity and all order
sign changes, no cusps and complete occurrence tracking. Only full assembly and
independent review may accept original thm:relgp. It is not the final main goal.

Original accepted proofs:lem:chi-basic,children,crossing-test,cusp-sides,fibres,
flat-sides,g1,rot,transport-polynomials,triple-sides,uniformrot,
wall-segment-stability,wall-sides and prop:chambers.
Accepted definitions:admissible,chamber,chirotope,crossings,deletion-halves,gauss,
generic,germ,interlace,polygon,regular,shift,visible,walls,weak.
Original unrestricted lem:shift remains locally unaccepted: the independently
verified regular zero-turn counterexample and explicit nonzero-turn repair remain
unchanged. Use the reviewed repair only with its proved Generic/nonzero-turn
premises. This local source issue does not block other work. repairs/index.json
binds053. Full polynomial-controls acceptance and earlier history are preserved
in checkpoints/status-through-052.md and older archives.

## Runtime, reporting and sources

Lake:/Users/aguevaragonzalez/.elan/bin/lake.
Lean:leanprover/lean4:v4.34.0-rc2; Mathlib:85e3a25e006c35636f0e53b0e9296caca2685bc0.
The shared .lake/packages cache remains /tmp/lean-handoff-mathlib-smoke/lean/.lake/packages;
eventual delivery must not rely on that temporary cache. Frozen reference,
provenance, blueprint, templates and ZIPs stay unchanged.
Run work/claim_progress.py and tools/progress.py --once from this FOCUSED root.
User-requested hourly reporting supersedes ten minutes. Existing hourly automation
remains active. Sole watcher42482 confirmed live01:23:54UTC; next due02:00UTC.
Manual final reporters at01:23:49UTC:14/132 original proofs,29/191 original
checklist and30/192 expanded. No completed proof awaits review.
Poll its actual handle before replacement; observation timeout is not terminal.
Source addendum rechecked this turn:8 checks,11 PDF hashes,103 manifest entries
passed. No additional source is needed to continue; optional original scans and
the still-open Reidemeister proof-depth review are recorded in
reports/sources-addendum-review.md. No author question is pending.
