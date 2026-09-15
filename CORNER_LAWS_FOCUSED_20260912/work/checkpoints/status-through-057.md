# Execution checkpoint — 2026-09-11 UTC, audit057

Accepted ORIGINAL proofs:14/132 (10.61%). ORIGINAL checklist:29/191 (15.18%).
Extra accepted lem:weak-open; expanded checklist30/192 (15.625%; reporter15.6%).
Main targets0/8. No complete original proof awaits review. Full wall laws,
soft theorem and unconditional R remain active and incomplete.

## Current theorem library and review

Six new modules preserve the exact reviewed prototype proof bodies:
TimedCoordinatePolyline, MultiCellCoordinatePolyline, GlobalTimedCollars,
GlobalTimedGerms, SmoothControlGraph and GlobalEventCertificate.
All273 priorSM files remain unchanged; all279 currentSM modules are now frozen.
Only Supplemental.lean gained an import; the declaration map is unchanged.

The actual source curve yields one continuous piecewise-affine Regular path
with exact labelled endpoints, synchronous strict Euclidean approximation,
collision freedom and finitely many nongeneric times. Positive-width endpoint
collars are Generic. Each actual nongeneric time has a centred WallGerm with
explicit fine-cell, local/global path, selected control, nonzero time derivative
and same-point ambient smooth-graph data. The graph has an open parameter domain,
smooth parametrization and smooth inverse projection with exact zero-set equality.

Root build46292 and independent canonical-import trace39371 both terminal0.
Review reviews/global-event-port.json (faithful partial scope), SHA256
f223bcd770763aba795c8ca705971ea8432979e8f33d52bdfc3e352cdc63d2f8.
The exact89-module closure reuses83 inherited reviewed modules. The independent
trace checks26 key standard-only axiom sets, both full data structures and five
semantic examples, including raw-source construction and certificate-only links.

Whole audit057 session74390 terminal0:279SMmodules,3314localdeclarations,
30mappedclaims,285projectfiles,38frozenfiles. No stage is complete.
Receipt checks/checkpoint-057-output.json SHA256
86bd5fee9a6698dc54d6e5d0aa876b205ca3a107eefa11f76a588029c4d3a939.
Declaration audit SHA256
ab60be7a91123e7e09d4c32e32b73c514ed11cbe09a42866cf7ecd9305d11ed1.
verify_named_walls.py and verify_global_event_port_checkpoint.py passed, binding
all30 accepted reviews/types, priorSM files, exact bodies, current/frozen inventories,
inherited reviews, pins, build and independent evidence. Earlier prototype056
verifiers are historical snapshots; do not rerun them after the canonical port.

## Next classification prototype

checks/SingleControlCenters.prototype.lean passed root68224 terminal0 and is frozen
at SHA2563ef8d2306385e05ef0c91b5bbc9ead7cca869bdefcb29b74278ba5be9cb33ef0.
It derives the actual unordered point/concurrence zero sets from a sole named
control zero. In the concurrence branch it derives an active remote interior
triple from G1 and actual nongenericness, so inactive generic T zeros are not
misclassified. ControlCenterSets is only the transparent exact finite-set
conclusion. The event consumer uses explicit certificate fields.
Independent trace85577 is terminal0:10 declarations and3 examples passed against
its exact90-module closure. Review reviews/single-control-centers-prototype.json
SHA256bbb01ae7644da101ec921c163627abc1d865defae564532b4b03c9c3d1682918.
verify_single_control_centers_prototype.py passed, binding source/review/prototype,
pins, current audit inventories and root/independent traces. Its examples include
raw-source construction, certificate-only nongenericness and the inactive-root
guard. This prototype remains
outside the library; no original claim is accepted. Earlier83335/64883 runs failed
only proof elaboration; archived logs and the successful result record the fixes.

## Next executable work and limitations

Port the reviewed SingleControlCenters body unchanged into a NEW module. Execute
decisions/relative-general-position-after-event-centers.md.
The cyclic point-triple split, strict betweenness/contact branches, oriented
control sign changes, T crossing-parameter/order identities, cusp exclusion and
final source thm:relgp assembly remain. Existing uniqueness for already-simple
germs cannot prove simplicity. Frozen RegularTriangle and CuspCenter contain
reusable triangle/antiparallel obstructions; do not re-prove them from scratch.

The certificate exposes other-control nonvanishing at its centre, not a full-radius
product field. Derive local persistence or expose the existing stronger patch
result in a NEW theorem. Explicit open C-infinity graph geometry is established;
a separate manifold API is not claimed. Full thm:relgp still needs independent
source review before original acceptance; then continue all wall/soft/R targets.

The unrestricted original shift remains locally unaccepted because of a reviewed
regular zero-turn counterexample. Its explicit nonzero-turn repair and Generic
consumers remain valid. repairs/index.json binds057. This local issue does not
halt other proof work. Supplied sources suffice for continuation; optional original
literature and Reidemeister proof-depth review remain as previously recorded.

Lake:/Users/aguevaragonzalez/.elan/bin/lake.
Lean:leanprover/lean4:v4.34.0-rc2; Mathlib:85e3a25e006c35636f0e53b0e9296caca2685bc0.
Shared packages:/tmp/lean-handoff-mathlib-smoke/lean/.lake/packages; final delivery
must not depend on that temporary cache. Frozen inputs/templates/ZIPs unchanged.
Sole progress watcher42482 remains live; last hourly02:00:09UTC, next03:00UTC.
Existing hourly automation active; do not duplicate. Last manual report at checkpoint finalization 2026-09-11T02:57:16Z.

Checkpoint057 finalized 2026-09-11T02:57:16Z. No root or reviewer proof kernel is live.
