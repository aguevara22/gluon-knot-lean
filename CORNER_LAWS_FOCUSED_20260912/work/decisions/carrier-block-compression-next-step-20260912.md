# Actual positive block compression: next executable work

2026-09-12. Root-authored **UNPROVED PLAN** after checkpoint105 kernel checks.
The delegated planning turn failed at model capacity before producing this file;
root completed this note locally. This is not an independent proof review or a
source acceptance. No global parameter-circle map is required unless a concrete
consumer needs it.

Source `reference/SM/sm-3-statesum.tex:198–220` requires omission of unselected
marks to join positive pieces in the same original direction, then true-corner
signs, regularity and at least three corners. Do not infer image equality from
positive displacement alone.

## Derive consecutive steps of the actual block

`CarrierActualCornerBlock.body.lean` now supplies the actual rotation, first
retained block `a :: (M ++ [b])`, literal prefix of `(a :: R) ++ [a]`, exact
corner-cycle next, endpoint ownership, omitted noncorners and EqOn of the parent
list permutation with the actual smoothing successor. No block is supplied as
an assumption to the final theorem. Closing `b=a` and empty `M` remain included.

First prove a generic closed-list adjacency theorem for a Nodup `a::R` and its
own `List.formPerm`, then transport each adjacent relation through the returned
EqOn. `CarrierClosedTrace.body.lean:39` already uses the pinned
`List.formPerm_apply_getElem` to identify modular next indices. The proof for
the appended anchor must explicitly include the last-to-first case. Use the
actual block prefix to restrict this adjacency theorem.

Pinned `Mathlib/Data/List/Chain.lean` exposes `List.IsChain` (not an assumed
chain certificate): `isChain_iff_forall_rel_of_append_cons_cons` at104,
`isChain_cons_append_singleton_iff_forall₂` at121, and `IsChain.prefix` at251.
These permit the final actual block to carry the derived relation
`fun x y => smoothingSuccessor hn hP S x = y`. `Cycle.chain_coe_cons` at
`Mathlib/Data/List/Cycle.lean:825` relates cyclic chaining to the closed list.
Choose the direct indexed or IsChain proof locally; neither licenses a new
chain premise in the actual component theorem.

## Compress the actual positive parameter intervals

Each intermediate noncorner is necessarily `Sum.inr v` with `v.1 ∉ S` by the
checked exact `IsTrueCorner` definition. Apply
`smoothingSegment_unselected_join_data` to each derived incoming relation.
It supplies the same original edge, the exact common visit parameter and two
full affine formulas, with strictly increasing parameters. Induct on the
actual intermediate list to retain one original edge, increasing cuts, and the
actual first/last endpoint evaluations. Handle `M=[]` by the checked actual
smoothingSegment data. Never assume that coincident endpoints imply an edge
index match; use the actual incoming-visit position theorem.

A small generic real/affine packet should prove that the image of
`u ↦ edgePoint P i (s + u*(t-s))` for `u∈[0,1]` equals the original parameter
image for `[s,t]` when `s<t`. For the reverse inclusion choose
`u=(r-s)/(t-s)` and prove its two bounds using the strictly positive denominator.
Then prove adjacent closed parameter intervals cover their combined interval
by a membership split at their common endpoint. These give finite image-union
equality by induction, alongside telescoping endpoint displacement and its
positive scalar. Definitions and elementary real arithmetic suffice; no
unverified interval-image helper is being asserted by this plan.

The actual consumer must discharge chain, same-edge and matching-parameter
premises using the constructed block. Its conclusions must include both a
positive original-edge displacement and equality of the union of marked segment
images with the compressed segment image. This is the required omission-of-
unselected-marks step. A closed singleton retained block cannot be discarded in
advance; its impossibility must follow from the resulting positive displacement.

## Source corner polygon and later obligations

Use the actual filtered cyclic corner list for the labelled source tuple and
prove its trace equivalence. Derive incoming/outgoing true-corner directions,
nonzero determinants and original/opposite selected signs, then regularity and
the three-corner lower bound. Exact retained crossings, all-visit noncrossing,
actual coefficients/state sum, all-sector soft theorem, wall laws,
full-cusp/comparison and R/bridge remain. Stronger fidelity and controlled
canonical integration are still separate from these candidate proofs.

## Inspected snapshot

- `reference/SM/sm-3-statesum.tex`: `fa17a1b162bd5a7a9cabc65fe8f95e4fb53c7f17050bfe8008cb805aa7954af5`
- `work/checks/CarrierTrueCorners.body.lean`: `7edfbe5ae8b23e1344355a5fcdf6d77c6d2a6b44a4888e6e7175d4ada2d98209`
- `work/checks/CarrierUnselectedDirection.body.lean`: `c1b6dd77d3365caa3b72ecde90c8a76d4994a6cac40bcc68ae86df0b44e679b2`
- `work/checks/CarrierFirstCornerBlock.body.lean`: `b07bf1be7e6fa45ef48cf721828ff6100433052d8329bf91bbd6a504021cc864`
- `work/checks/CarrierActualCornerBlock.body.lean`: `5dbb9351275165b3b4eeae6d594c95a273e9545ea0ce371f8f0e45ea0d9d3b18`
- `work/checks/CarrierClosedTrace.body.lean`: `b86150ecd2e6c5de71be1275ba8d5d377c292c5d23befce5d3257489b93a1203`
