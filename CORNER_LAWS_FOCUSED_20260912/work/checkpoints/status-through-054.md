# Execution checkpoint — 2026-09-11 UTC, audit054

Accepted ORIGINAL source proofs:14/132 (10.61%).
Accepted ORIGINAL checklist:29/191 (15.18%):fourteen proofs and fifteen definitions.
Extra accepted lem:weak-open; expanded checklist30/192 (15.625%;reporter15.6%).
Main targets0/8. No complete original proof awaits review. The full wall-law,
soft-theorem and unconditional R goal remains active and incomplete.

## Actual central roots and the Generic implication

Five new modules:CentralLegPolynomial, RealAffineCrossing, CentralLegRootControls,
NonzeroControlsGeneric, CentralLegFiniteRoots. Preserve all263 current SM files;
all258 earlier SM files remain byte-for-byte unchanged.

The actual parameter polynomial has constant equal to the initial control value
and slope equal to the evaluated coordinate slope times the real scalar step.
Its evaluation equals the actual control along the leg. A factor independent of
the moving scalar is a nonzero constant; every root therefore forces genuine
coordinate dependence. Actual time slope is nonzero, rootMultiplicity is1,
HasDerivAt gives that nonzero derivative, and every pair of parameters on opposite
sides has negative product of control values. Distinct named factors cannot share
a root, neither0 nor1 is a root, and one factor has at most one root per leg.

The root sets are actual evaluation zeros, finite and isolated, with one unique
control name at each root. Finite pairs(leg label,local parameter) retain distinct
leg occurrences. Actual all-named-control-nonzero implies G1/G2 Generic through
arbitrary-order ±coverage and actual remote interior-concurrence geometry. Only
this direction is proved; inactive T roots may still be generic. Nongeneric
central parameters are therefore a subset of the finite roots, not all roots.

These are supplied individual central legs with the already constructed joint
conditions. No common neighbourhood fixing all OTHER control signs, ambient
smooth-hypersurface theorem, complete wall-germ classification, global path,
endpoint collars, regularity containment or Euclidean uniform bound is yet proved
by these five modules. Full thm:relgp remains unaccepted.

## Independent review and whole verification

Implementer:root-implementation-20260910.
Reviewer:review_chirotope-independent-20260910, with no implementation edits.
Core build20567 terminal0; derivative/root build67072 terminal0; final finite-root
build34619 terminal0. The first finite-root attempt26635 failed only because a
finite-set difference lemma's named argument selected the wrong set. The corrected
finite subset proof for S minus the root passed; its statement never changed.

Independent trace19457 terminal0:31 standard-only axiom sets, plus an explicit
kernel example deriving a nonzero actual time derivative from an actual control
evaluation zero. Exact48-file closure=five new +43 previously reviewed joint-choice
dependencies. Pinned analytic polynomial derivative proof inspected independently.
Review:reviews/central-leg-roots.json SHA256:
eb237abb2f3df42ea5484b30f3f4533e796678819e5124a3a8bf2a6308735935.
Trace source SHA256:8e7c242fd303dcab3be45ff2c4a961f7fcb2ae23ff437d43925c5ad0e99293f6.
Trace log SHA256:4d5b2efb2a3de148e59237d9edb541dbb2ea0cca78efbe30b87181b47db96557.
The review binds complete current source/type/body files and explicitly excludes
the unfinished full original statement and the separate scalar-box prototype.

Whole audit054 session35317 terminal0:263SMmodules,2928localdeclarations,
30mappedclaims,269projectfiles,38frozenfiles. Only Supplemental.lean changed among
previous project files, adding the new import; the declaration map is unchanged.
Every existing accepted semantic/type/source/support binding remains current.
Receipt:checks/checkpoint-054-output.json SHA256:
d63e3e443df5756b8120d4e5dc1f8eeacfefe86a74491436e2dcec86e72a89c7.
Declaration audit SHA256:
77980b031a9a798c1a007672c1d9d5f176785e8365c311f9185d3c57f2bd623d.
Both final verifiers passed terminal0:
python3 work/checks/verify_named_walls.py work/checks/checkpoint-054-output.json
python3 work/checks/verify_central_roots_checkpoint.py work/checks/checkpoint-054-output.json
They verify current/frozen inventories, all258 priorSM files, all30 accepted
bindings, exact48-file new review closure, pins, standard-only trace and the
inspected pinned derivative-library source. Development pass is not stage success.
No theorem-library build or whole audit is live.

## Scalar-box prototype: independent review complete

checks/ScalarBoxes.prototype.lean remains outside the theorem-library inventory.
Root kernel session10541 terminal0, six standard-only axiom traces. The first
attempt92467 had one missing implicit-index binder in convex_pi; corrected only
the prototype and reran successfully. No failed proof or sorryAx is accepted.
Prototype SHA256:ddcb19795b3abb36867aa4af7ed3d19c1c5b53f62558cb06240d976b5f9f865b.
Log SHA256:cfeb2b461072456d050bcafe20c4ab9c52de665fdc5fd0be97d9e14cb679d72b.
Evidence:checks/scalar-boxes-prototype-result.json. Independent review is complete:
reviews/scalar-boxes-prototype.json SHA256:
c2af632029508d1b7c8f860dc9e08f7608a2391038c39cc18c7ce432c278d5a5.
Independent trace8113 terminal0 checks14 standard-only axiom sets, actual tuple-box
image equality and a source n≥3 specialization. Its exact23-file supporting import
closure and all audit054 project/frozen bytes are verified by
checks/verify_scalar_boxes_prototype.py; receipt:
checks/checkpoint-054-scalar-boxes-prototype-verification.json.
No theorem-library build, audit or independent kernel trace is live. The prototype
remains outside the theorem library and does not accept the full source claim.

It defines actual scalar open/closed boxes, proves openness/closedness, closure
inclusion, convexity, coordinate-hybrid and affine-line containment and positive
closed boxes in prescribed open neighbourhoods. Actual tuple boxes have closure
inside any prescribed open tuple set S and strict Euclidean
Metric.diam(tupleCoordinates''box)<delta, plus pairwise distance<delta. A delta/4
radial margin proves true diameter≤delta/2<delta; it does not conflate product max
and Euclidean metrics. No finite subdivision, overlap assignment or whole path
has been constructed. With independent review complete, port its exact mathematical body
into new modules and use actual Regular/Generic open sets as appropriate.

## Next executable work and retained scope

Execute decisions/relative-general-position-after-central-roots.md. Finish common
root sign neighbourhoods and centred actual germs; preserve inactive T treatment.
Complete cube/subdivision/overlap/collar/ordered-coordinate-leg construction,
actual increasing time rescalings, fixed global labelled endpoints, continuity,
piecewise-affinity, regularity and the Euclidean uniform error. Then finish actual
F,bothV,T,E,C classification, the T/crossing-parameter identity and order changes,
no cusp and full occurrence-label tracking. Full source assembly and independent
review alone can accept thm:relgp. Continue main laws, soft theorem and R afterward.

Original accepted proofs:chi-basic,children,crossing-test,cusp-sides,fibres,
flat-sides,g1,rot,transport-polynomials,triple-sides,uniformrot,
wall-segment-stability,wall-sides and prop:chambers.
Accepted definitions:admissible,chamber,chirotope,crossings,deletion-halves,gauss,
generic,germ,interlace,polygon,regular,shift,visible,walls,weak.
The original unrestricted shift remains locally unaccepted due to the reviewed
regular zero-turn counterexample; its explicit nonzero-turn repair and proved
Generic consumers remain unchanged. repairs/index.json now binds054. This local
source issue does not stop independent work. Earlier full details are archived
in checkpoints/status-through-053.md and earlier status files.

## Runtime and progress

Lake:/Users/aguevaragonzalez/.elan/bin/lake.
Lean:leanprover/lean4:v4.34.0-rc2; Mathlib:85e3a25e006c35636f0e53b0e9296caca2685bc0.
Shared .lake/packages cache:/tmp/lean-handoff-mathlib-smoke/lean/.lake/packages;
eventual delivery must not depend on this temporary cache. Frozen reference,
provenance, blueprint, templates and ZIPs remain unchanged. No literature axiom
is used. The supplied source addendum is sufficient to continue; optional originals
and the unresolved Reidemeister proof-depth review stay recorded separately.

Run work/claim_progress.py and tools/progress.py --once from this FOCUSED root.
Existing hourly automation and sole watcher42482 remain in place; confirmed live
at01:24:30UTC this turn, next due02:00UTC. Observation timeout is not terminal.
Original proof count remains14/132; no author question or new global blocker.
