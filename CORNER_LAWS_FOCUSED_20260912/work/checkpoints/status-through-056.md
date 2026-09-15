# Execution checkpoint — 2026-09-11 UTC, audit056

Accepted ORIGINAL proofs: 14/132 (10.61%). ORIGINAL checklist: 29/191 (15.18%).
Extra accepted lem:weak-open; expanded checklist 30/192 (15.625%; reporter15.6%).
Main targets 0/8. No complete original proof awaits review. Full wall laws,
soft theorem and unconditional R remain active and incomplete.

## Reviewed new theorem-library work

Five modules: UniformMesh, UniformMeshCells, CurveCubeSubdivision,
CubeWaypointDomains and CubeWaypoints. Preserve all273 current SM files; all268
prior SM files remain unchanged. Only Supplemental.lean gained an import; the
declaration map is unchanged. UniformMesh is the exact reviewed prototype body.

The actual source curve now supplies a strict finite mesh with N≥3, closed-cell
coverage and adjacent-only intersections. Each closed cell's actual curve image
lies in a small Regular cube, with first/last cube closures Generic. Adjacent
cubes share the actual curve boundary point, yielding nonempty open full scalar
waypoint domains. One W satisfies every constraint on every actual central
coordinate leg. Its waypoint sequence has the fixed original labelled endpoints;
each successive pair, hybrid and coordinate leg stays in its assigned cube.

Build41387 and independent trace35387 both terminal0. Review:
reviews/curve-cubes-waypoints.json (faithful partial scope), SHA256
3376f95c779cb8c263d9f9dd37348f01f2e19824574417db9270a9d35a06eaf3.
The exact71-file closure includes66 inherited reviewed files. The trace checks
57 standard-only axiom sets and3 semantic examples, including construction from
raw source assumptions and the actual Euclidean cube bound/collision transfer.
Initial71219 failure was only Fin zero-index elaboration; corrected48124 passed.

## Whole-library evidence

Audit056 session85835 terminal0:273SMmodules,3163localdeclarations,30mappedclaims,
279projectfiles,38frozenfiles,275Leanfiles. No stage is complete.
Receipt:checks/checkpoint-056-output.json, SHA256
5c4f93ec90e4b107ffcb2366f5ac1639ef9e016713a73c30287320d03e093f66.
Declaration audit SHA256:
85517cc4c36d3a614aaec0ad1719d29000611e4b287b83324f19f19b1af1842d.
verify_named_walls.py and verify_curve_cubes_waypoints_checkpoint.py passed;
all30 accepted source/type/reviewer bindings, all268 priorSMfiles, current/frozen
inventories, exact closure, inherited reviews, pins and trace hashes are bound.

## Independently reviewed prototypes — outside the theorem library

All five prototype stages passed root and independent Lean checks. Their frozen
bodies and imported-library closures are bound by scoped evidence verifiers:

| Stage | Root / independent sessions | Scope |
| --- | --- | --- |
| TimedCoordinatePolyline | 41784 / 64205 | Continuous coordinate polyline, exact endpoints, cube retention |
| MultiCellCoordinatePolyline | 74114 / 68093 | Actual global piecewise-affine Regular path, exact labelled endpoints, synchronous Euclidean bound, collision freedom and finite nongeneric times |
| GlobalTimedGerms (including collars) | 5732 / 63151 | Positive endpoint collars, strict central-leg location and actual rescaled wall germs |
| SmoothControlGraph | 18529 / 5906 | Open C-infinity graph, smooth parametrization and inverse projection, exact ambient zero set |
| GlobalEventCertificate | 80480 / 70190 | One actual event/control/fine-cell/germ with explicit global and local path identities, nonzero derivative and same-point graph membership |

All sessions terminal0; only standard Lean axioms occur. The scoped verifiers
check exact prototype/source/review bytes, current SM import closures, pinned
library bytes, root and independent traces, and audit056 inventories. Full
original thm:relgp remains unaccepted. No declaration-map or original-count change.
The strong certificate exposes central other-control nonvanishing. It does not
expose their positive product throughout its full radius; consumers must derive
local persistence or explicitly retain the previously proved stronger patch fact.
The smooth graph is concrete ambient geometry; no separate manifold API is claimed.

## Next work and retained scope

Execute decisions/relative-general-position-timed-refinement.md. Port the exact
reviewed prototype bodies into six NEW modules; preserve all273 current SM files.
Build and obtain independent port-binding review, then a new whole-library audit.
Next derive the exhaustive F/bothV/T/E/C dictionary from actual point/concurrence
control zeros, including T crossing-parameter/order changes and cusp exclusion.
Existing uniqueness for already-simple germs does not supply this existence proof.
Only complete source assembly plus independent review accepts thm:relgp. All corner
wall laws, soft theorem and unconditional R remain required.

The original unrestricted shift remains locally unaccepted due to the reviewed
regular zero-turn counterexample. Its explicit nonzero-turn repair and Generic
consumers remain valid and unchanged; repairs/index.json now binds056. This does
not halt independent work. Source intake is unchanged: supplied PDFs/extracts
suffice to proceed; optional originals and Reidemeister proof-depth review remain.

Lake:/Users/aguevaragonzalez/.elan/bin/lake.
Lean:leanprover/lean4:v4.34.0-rc2; Mathlib:85e3a25e006c35636f0e53b0e9296caca2685bc0.
Shared .lake/packages:/tmp/lean-handoff-mathlib-smoke/lean/.lake/packages; final
delivery must not rely on that temporary cache. Frozen sources/templates/ZIPs
unchanged. Progress watcher42482 confirmedlive; last hourly02:00:09UTC, next03:00.
The existing hourly automation remains active; do not duplicate it.
