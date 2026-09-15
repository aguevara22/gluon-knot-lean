# Actual geometric carrier realization: next step

2026-09-12. Author: `/root/spanning_children`. Bounded static inventory and **UNPROVED IMPLEMENTATION PLAN**, not a candidate, kernel result, independent mathematical review, or geometry acceptance. Only this note was written. No kernel, build, audit, source edit, or candidate edit was run. Source acceptance increment0; stronger statement fidelity approval false; integration approval false.

The next missing bridge is to prove that the actual original successor bounds a positive subsegment of one original edge, then transport that segment through the selected outgoing-slot permutation. The physical equality at a selected switch is already proved. The exact component count is a separate root workstream; this note does not infer its run status.

## Source scope and existing data

`reference/SM/sm-3-statesum.tex:14–38` defines carriers as the closed polygonal curves traced by the actual reconnections and gives incoming-visit ownership. Lines54–90 state all four clauses. Lines95–112 give the finite successor construction. Lines179–201 require consecutive original marks to bound positive original subsegments and explicitly exclude inserting a zero segment between twin visits. Lines203–220 concern true corners, regularity, and the three-corner bound. Lines222–238 concern retained geometric self-intersections. The all-visits noncrossing argument at140–167 is a different obligation.

Inspected passing APIs (all in `SM.Carrier` unless stated otherwise):

- `CarrierMarks.body.lean:9–36`: `Mark P := ZMod n ⊕ Visit P`; `markPosition hn hP` for `hP : G1 P`; vertex/visit formulas; `markPosition_evaluation_vertex`, `markPosition_evaluation_visit`; `markPosition_injective hn hP` for `hP : Generic P`. At75–108, the sorted full `markList`, `markList_nodup`, `mem_markList`, `markList_sorted`, `markList_length`, and `markList_nonempty` retain every original vertex. Injectivity concerns traversal positions, **not** their plane evaluations.
- `CarrierSuccessor.body.lean:52–82`: actual `markSuccessor hn hP`, forward/backward list-index formulas; at107, `markSuccessor_no_mark_between hn hP a u`; at142, `markSuccessor_sameCycle hn hP a b` for all actual marks. These use the full marked circle, not only crossing visits.
- `CarrierVisitTwin.body.lean:8–39`: `visitTwin`, `visitTwin_crossing`, `visitTwin_ne`, `visitTwin_involutive`. At54–84, `selectedVisitTwin` and its actual crossing-membership branches/permutation.
- `CarrierSmoothing.body.lean:9–34`: `selectedMarkPerm S`, vertex/visit formulas, involution, and **already proved** `selectedMarkPerm_evaluation hn hP S a`, requiring only `hP : G1 P`. At55–74, `smoothingSuccessor hn hP S` is definitionally `markSuccessor hn hP (selectedMarkPerm S a)` on a mark, with exact selected/unselected branches. At97–134, `Component`, `owner`, `owner_eq_iff`, `owner_successor`, `owner_predecessor`, and `owner_surjective` give the actual orbit quotient.
- `CarrierFilteredCycles.body.lean:9–45`: actual `componentCycle`, literal complete-mark-list filter representative, membership iff owner equality, Nodup, and nonemptiness. `CarrierUnchangedComponent.body.lean:9–33` gives forward/inverse preservation and `smoothingSuccessor_bijOn_owner` for every support.
- `CarrierIndependentOrder.body.lean:33–60`: `independent_inheritsMarkOrder hn hP hS` and `independent_selected_pair_owners_ne hn hP hS v hvS`. `CarrierCurrentCycle.body.lean:27` gives `componentCycle_list_eqOn hn hP T hI q L hL : Set.EqOn L.formPerm (smoothingSuccessor hn hP T) {m | m ∈ L}`. These supply the actual order; it must not be assumed from filtering alone.

Useful canonical APIs:

- `SM/Polygon.lean:49–58`: `edge`, `edgePoint`, `edgeSegment`, `edgeInterior`. `SM/Traversal.lean:12–17,46–86`: half-open `TraversalPoint`, `traversalEvaluation`, `traversalKey_lt_iff`, `traversalBetween`, `traversalShift`. `SM/TraversalRelabel.lean:10,16–25,74` gives `traversalShiftEquiv`, key bounds, and `traversalBetween_shift`, including wraparound.
- `SM/GaussVisits.lean:48–68`: `visitPosition_edge`, `visitPosition_parameter`, `visitPosition_interior`, `visitPosition_evaluation`, and position injectivity. `SM/G1Consequences.lean:13–16` gives `edgePoint_zero/one`; its `g1 hn P hP` aggregate at108 gives edge nonvanishing without requiring the consumer to install extra index instances. `SM/Crossings.lean:88` gives `edgePoint_injective`; `SM/EuclideanPlane.lean:36` gives `euclideanLength_pos`.
- Pinned `Mathlib/GroupTheory/Perm/Cycle/Basic.lean:106`: `Equiv.Perm.SameCycle.eq_of_left h hx` says a fixed point's same-cycle partner equals it. Pinned `Mathlib/Data/List/Cycle.lean:625–637` has `Cycle.map` and `map_coe`; at792–825, `Cycle.Chain` and `chain_coe_cons` express the closing last/first edge. These APIs are available ingredients, not an already proved geometric trace bridge.

## Smallest first packet: actual positive outgoing segments

Suggested packet `CarrierMarkedSegments` (roughly8–10 declarations; names and signatures below are **PROPOSED AND UNCHECKED**). Keep `hn : 3 ≤ n`, `hP : Generic P`; the local construction needs no independence assumption and applies to every `S : Finset (Crossing P)`.

Use `ev a := traversalEvaluation P (markPosition hn hP.1 a)`, `rho := markSuccessor hn hP`, `sigma := selectedMarkPerm S`, and `g := smoothingSuccessor hn hP S` as notation in this plan.

1. Prove `markSuccessor_ne_self hn hP a`. If `rho a = a`, `markSuccessor_sameCycle` and `SameCycle.eq_of_left` identify `a` with each of the distinct vertex marks0 and1. Their equality contradicts `n ≥ 3`. This handles the degenerate cyclic-gap possibility before using strict order.
2. Prove `markSuccessor_position_cases`: writing `p := markPosition ... a` and `r := markPosition ... (rho a)`, either `r.1 = p.1` and `p.2.val < r.2.val`, or `rho a = Sum.inl (p.1 + 1)`. This must be derived from the actual sorted successor, not supplied as a segment premise.
3. From those cases prove `markSuccessor_subsegment_data`: there exists `t : ℝ` with `p.2.val < t`, `t ≤ 1`, and `ev (rho a) = edgePoint P p.1 t`. The same-edge branch uses `t = r.2.val`; the next-vertex branch uses `t = 1` and `edgePoint_one`. Also retain `0 ≤ p.2.val` from the actual half-open position.
4. Define the actual smoothing segment by the affine formula below, prove its endpoints and continuity, and prove the parameter formula, positive direction, and nonzero endpoint difference below.

The crucial proof for item2 is small after a change of cyclic cut. Set `i := p.1`, shift the three traversal points by `i`, and let `K` be the shifted key of `r`. The start has key `s := p.2.val` with `0 ≤ s < 1`. The original mark `Sum.inl (i+1)` shifts to vertex1, whose key is1. The no-mark-between theorem excludes `K > 1` because `s < 1 < K`; it excludes `K < s` because `K < s < 1` gives the wraparound cyclic order. Equality `K = s` is excluded by traversal-key injectivity, `traversalShiftEquiv.injective`, mark-position injectivity, and item1. Thus `s < K ≤ 1`. Since the shifted edge index is a natural-number value and its parameter lies in `[0,1)`, its index is0 with larger parameter, or index1 with parameter0. Undo the shift. In the latter case, mark-position injectivity identifies the mark with the actual next vertex. This argument also covers the original final-edge/vertex0 transition without assuming global key increase.

Define the affine segment on real parameters, then restrict to `[0,1]` as needed:

`gamma S a u := ev a + u • (ev (g a) - ev a)`.  (P1)

Apply item3 to `sigma a`, put `i := (markPosition ... (sigma a)).1`, `s := (markPosition ... (sigma a)).2.val`, and retain its actual upper parameter `t`. First use the proved `selectedMarkPerm_evaluation` to replace `ev (sigma a)` by `ev a`. Next use the definitional successor composition for the other endpoint. Affine algebra then proves:

`gamma S a u = edgePoint P i (s + u * (t - s))`, with `0 ≤ s < t ≤ 1`.  (P2)

Subtract the two endpoints in (P2); do not infer direction from plane-point ordering:

`ev (g a) - ev a = (t - s) • edge P i`, with `0 < t - s`.  (P3)

Nonvanishing follows from positive scalar and `g1` edge nonvanishing; `euclideanLength_pos` then supplies positive length if required. For `0 ≤ u ≤ 1`, the scalar parameter in (P2) lies in `[s,t] ⊆ [0,1]`, proving literal containment in `edgeSegment P i`. Continuity is the direct continuity proof of the explicit affine function (the canonical pattern is `SM/PolynomialAvoidance.lean:27–28`), not a supplied arbitrary path.

The start/end formulas must imply the exact gluing law:

`gamma S a 1 = gamma S (g a) 0`.  (P4)

This is the correct endpoint continuity at every node. At selected `a`, the segment starts at its own physical endpoint and follows the twin's positive outgoing segment; no extra segment from `a` to its twin is created. `owner_successor` proves the glued endpoint remains in the same abstract component. Shared plane points do not identify distinct component owners.

## Immediate second packet: each actual component is a closed marked trace

For an independent `S` with actual `hS : S ∈ independentSupports hn hP`, take the literal list `Lq := (markList hn hP).filter (fun a => decide (owner hn hP S a = q))`. Its equality with `componentCycle`, Nodup, and nonemptiness are already proved. Obtain `hI` from `independent_inheritsMarkOrder`, then use `componentCycle_list_eqOn` to identify the complete cyclic list action with `g` on every member. Thus the edges between consecutive entries, including last/first, are exactly (P1)–(P3), with (P4) at the joins. This is the smallest remaining actual component-trace interface, with no supplied orbit representation and no replacement of the old component by the full circle.

A rotation-independent geometric marked cycle can be defined as `(componentCycle hn hP S q).map ev`; `Cycle.map_coe` provides the literal list of plane endpoints. Keep the abstract mark cycle beside this map: plane endpoints can repeat at retained self-crossings, and distinct carriers can share a selected smoothing point. Mapping into the plane must not be used as an injective quotient or as a count of connected components of the union of images.

The unproved consumer should assert that this actual nonempty finite cyclic representative has the proved affine segment on each next edge. If a global continuous map from a parameter circle is needed, piecewise concatenate these explicit segments and separately prove continuity at finitely many joins and the closing join. Such a parameterization is not already present in the inspected carrier files. Using `orderOf g` alone would generally repeat a smaller orbit; prefer the actual Nodup component list when representing one traversal exactly once.

## Later obligations, deliberately not claimed by the first packets

- **Actual corner polygon.** The marked trace still includes unselected crossing visits. The source corners are only original vertices and selected visits. Prove that deleting the other marks concatenates successive positive pieces on the same original edge, preserves the trace, and gives nonzero corner-to-corner edges. Prove every component contains a corner; do not add a corner-nonempty premise. Only then construct the source labelled corner tuple up to cyclic shift. A marked polygon can be regular with zero turns at auxiliary unselected marks; this does not prove all source corner turns nonzero.
- **Directions, turns, regularity, at least three corners.** Prove the incoming edge at a vertex is a positive multiple of `edge P (i-1)`, and at a visit of edge `i` is a positive multiple of `edge P i`. Outgoing directions use the selected twin only at selected visits. Use `SM/Segment.lean:85` (`g1_turn_nonzero`), `SM/G1Consequences.lean:63` (`g1_remote_meeting`), `SM/Chirotope.lean:30,87` (`det_swap`, `turn_det`), and `SM/AngleScaling.lean:12,17` (`principalAngle_smul`, `regularPair_smul`). Prove opposite selected signs and absence of antiparallel corners; then closure excludes one corner and forces opposite directions in a two-corner polygon. `SM/RegularLocus.lean:12–26` is the actual target regularity interface, not a property obtained from finite-orbit count.
- **Exact intersections and retained crossings.** Prove segment coverage and disjoint interiors for distinct original parameter pieces, then classify intersections by same/adjacent/remote original edges. Relevant existing facts are `edgePoint_injective`, `g1_adjacent_intersection`, `g1_remote_meeting`, `generic_crossingPoint_injective` (`SM/Crossings.lean:113`), and `crossingPoint_ne_vertex_of_geometry` (`SM/CrossingVertexExclusion.lean:29`, with its stated geometry/exclusion premises derived from genericity). The original no-triple-interior premise is `Generic.lean:14–19`. Selected-owner separation is checked, but its interpretation as one physical passage per carrier still needs the trace correspondence. Neither evaluation injectivity nor a global embedding is available or appropriate.
- **All-visit noncrossing and unselected ownership.** These remain distinct order/ownership proofs. Source140–167 includes the incoming-side treatment of selected endpoints; source169–177 separates interlacing and noninterlacing unselected pairs. The checked inherited order and selected-owner separation alone do not establish either complete clause.
- **No downstream acceptance.** The weakly generic extension, positive lifts, carrier amplitudes, regularity-dependent rotation, retained counts, and final corner state sum require further interfaces. None is discharged by this plan or by a successful combinatorial count.

## Exact inspected snapshot and contribution disclosure

The following hashes bind the source and principal candidate bodies used for this inventory. Existing passing receipts remain the authority for kernel status. I authored portions of the mark/cycle/filtered-order/insertion infrastructure and the generic finite-fiber arithmetic packet; this is implementer planning, not independent review of that work. No source claim is accepted here.

| File | SHA256 |
| --- | --- |
| `reference/SM/sm-3-statesum.tex` | `fa17a1b162bd5a7a9cabc65fe8f95e4fb53c7f17050bfe8008cb805aa7954af5` |
| `work/checks/CarrierMarks.body.lean` | `cc66829da71fc7c7f344b03b751fc29b0778d36a53e4bca120be51e25e0549af` |
| `work/checks/CarrierSuccessor.body.lean` | `495e8f70d355ab180c182d6529925ca89279ee1ff2749a022509fca759e0ba90` |
| `work/checks/CarrierVisitTwin.body.lean` | `9f80a477adaf4a1238b58160c0ff258eebeb37a6bc0b153dd6cbb0c1bdb6d2f8` |
| `work/checks/CarrierSmoothing.body.lean` | `27ddd25cb6878afd24f7c71cfee7b003e9bd539c5dbc00eea05bc7642205c61e` |
| `work/checks/CarrierFilteredCycles.body.lean` | `17e091e45f8844dc366f67f985691accf2678d3a529692278113c3099ff2649e` |
| `work/checks/CarrierCurrentCycle.body.lean` | `c87fd76d5d9962354b4bfe9e045548874fad917be37cdc1022ee152e263edd53` |
| `work/checks/CarrierIndependentOrder.body.lean` | `b36857c20e3a5e57d46822b76ad2d237abfae2453f875ec4e9d6237f20762eb8` |
