# Actual true corners: next executable packets

2026-09-12. Author `/root/spanning_children`. **UNPROVED PLAN**, from static API/source inspection only. No Lean body, source, passing evidence, or other file was edited. No kernel/build/audit was run. Source acceptance increment0; stronger fidelity and canonical integration approvals false.

Source: `reference/SM/sm-3-statesum.tex:179–220`, especially198–201 (omit unselected marks and join positive subsegments),203–211 (corner directions/signs),213–220 (corner existence and at least three corners). The source definition at14–38 keeps original vertices and selected smoothing sites as corners and uses incoming-visit ownership. A finite marked trace still contains auxiliary unselected visits, so checkpoint104 is not yet the source true-corner regular polygon.

At inspection, passing104 receipts were observed for `CarrierAffineSegments` (root24066) and `CarrierMarkedSegments` (root4362). `CarrierSegmentGeometry` and `CarrierClosedTrace` body interfaces were inspected, but neither result receipt was present. Assemble consumers of those packets only after root seals their passing receipts. This note does not certify their proofs.

## Packet A: corner existence and the actual corner filter

Proposed definition (all names here are unimplemented): `IsTrueCorner S : Mark P → Prop`, true on `Sum.inl i`, and equal to `v.1 ∈ S` on `Sum.inr v`. It uses actual crossing membership, not a supplied corner subset.

First proposed theorem, for every support `S` and every actual `q : Component hn hP S`:

`∃ a : Mark P, owner hn hP S a = q ∧ IsTrueCorner S a`.  (C1)

No independence, inherited-order, corner-nonempty, or geometric segment premise is needed. Exact proof route:

1. Choose `m` with `owner ... m = q` by `CarrierSmoothing.body.lean:128`, `owner_surjective hn hP S q`. Let `f := smoothingSuccessor hn hP S`, `rho := markSuccessor hn hP`, and `U := {a | owner hn hP S a = q}`.
2. Under the negation of(C1), no member of `U` is a vertex or selected visit. Prove `he : Set.EqOn f rho U` by cases on the mark: the vertex branch contradicts cornerlessness; the visit branch gives `v.1 ∉ S` and uses `CarrierSmoothing.body.lean:70`, `smoothingSuccessor_visit_of_not_mem hn hP S v hv`.
3. Use `CarrierUnchangedComponent.body.lean:27`, `smoothingSuccessor_bijOn_owner hn hP S q`, as `hU`. The exact generic transport API is `CarrierAmbientTransport.body.lean:17`, `sameCycle_congr_of_eqOn_bijOn f rho U hU he m hm y : rho.SameCycle m y ↔ f.SameCycle m y`. Its other endpoint `y` is unrestricted. Apply the forward direction at vertex0 to `CarrierSuccessor.body.lean:142`, `markSuccessor_sameCycle hn hP m (Sum.inl 0)`.
4. `owner_eq_iff` at `CarrierSmoothing.body.lean:107` changes that transported relation into owner equality. Combined with `hm`, it puts vertex0 in `U`, contradicting cornerlessness. No full-circle representation of the component was assumed; it was forced only under the contradiction hypothesis.

Then define `componentCornerCycle hn hP S q := (componentCycle hn hP S q).filter (fun a => decide (IsTrueCorner S a))`. Prove its literal representative, membership iff `owner ... a = q ∧ IsTrueCorner S a`, Nodup, and nonemptiness using(C1). Existing APIs: `CarrierFilteredCycles.body.lean:15,23,29` (`componentCycle_eq_filtered_markList`, `mem_componentCycle`, `componentCycle_nodup`) and `CycleFiltering.body.lean:26–71` (`Cycle.filter_coe`, `mem_filter`, `filter_filter`, `Nodup.filter`). This should be a small first packet, roughly6–8 declarations including definitions.

The filter and its nonemptiness make sense for arbitrary `S`. Its identification with a compressed actual orbit uses the checked inherited-order theorem for independent `S`; do not silently assert that compatibility for arbitrary supports.

## Packet B: remove actual unselected blocks and preserve the trace

The missing generic list interface is a finite first-corner block, derived from a nonempty corner filter, not supplied as a new representation hypothesis. For each retained corner `a`, rotate the actual component marked list to start at `a`. In the remaining list followed by `[a]`, split at the first retained corner `b`. The intermediate block `M` consists entirely of unselected visits. Prove that the next element in the filtered cycle is exactly `b`, and that `a :: (M ++ [b])` follows consecutive actual successor steps. The closing return must be included. Do not assume `a ≠ b`, two corners, or a nonempty intermediate block; singleton filters and empty blocks must remain legal inputs until geometry excludes impossible cases.

Passing order tools: `CarrierIndependentOrder.body.lean:33`, `independent_inheritsMarkOrder hn hP hS`, and `CarrierCurrentCycle.body.lean:27`, `componentCycle_list_eqOn`. The104 interfaces `CarrierClosedTrace.body.lean:23,39` (`componentMarkList_data`, `componentMarkList_getElem_successor`) provide the literal list, positive length, and modular successor equation when their receipt passes. `CycleFiltering` proves rotation compatibility but has no filter-next/finite-block theorem; the inspected Mathlib Cycle/Concrete files did not supply that missing interface directly.

The key actual local direction lemma is also still needed. If `smoothingSuccessor ... x = Sum.inr v` and `v.1 ∉ S`, apply `markSuccessor_position_cases` to `selectedMarkPerm S x`. Its next-vertex branch contradicts `Sum.inr v = Sum.inl ...`; its same-edge branch identifies the incoming segment's original edge with `v.2.val`. The outgoing segment at `Sum.inr v` uses that same edge because the visit is unselected. Thus the two positive segments are on the same oriented original edge. This uses actual successor equality and the proved position cases, not just coincident plane endpoints.

Iterate this lemma along the derived block. Starting from the actual outgoing slot `selectedMarkPerm S a`, retain original-edge index `i` and strictly increasing cuts `s0 < ... < sk`, with `0 ≤ s0` and `sk ≤ 1`. At intermediate visits, parameter matching follows from same-edge endpoint equality and `SM/Crossings.lean:88`, `edgePoint_injective`, with nonzero original edge. The final endpoint can be the next original vertex at parameter1. The parameter and vector data come from104 `smoothingSegment_subsegment_data` and `smoothingSegment_positive_direction` (`CarrierSegmentGeometry.body.lean:9,32`) once checked.

Prove both consequences, as separate conclusions:

`ev b - ev a = (sk - s0) • edge P i`, with `0 < sk - s0`.  (C2)

The union of the block's actual segment images on `[0,1]` equals the affine segment from `ev a` to `ev b`, with inherited increasing parameter order.  (C3)

For(C2), telescope endpoint differences and preserve positivity. For(C3), first show each marked segment covers precisely its original parameter interval, then use finite adjacent-interval coverage of `[s0,sk]`. Positive total displacement alone does not prove trace equality. `CarrierAffineSegments.body.lean:8,14` supplies exact subtraction/interpolation identities. No skipped-point or same-direction premise should appear in the final actual block theorem; it must follow from the definition of consecutive retained corners. This packet may reasonably split into generic finite-block filtering and actual geometric block compression.

## Source polygon consumer and remaining work

Evaluate the actual compressed cyclic corner list to construct a labelled cyclic tuple, with its length derived from that list. Equations(C2)–(C3) prove positive edges and equivalence to the marked trace, including closure. Prove incoming/outgoing directions at true corners, their nonzero determinants, original turn signs and opposite selected signs; use `SM/AngleScaling.lean:12,17` for positive rescaling and regular pairs. Only after that can closure exclude one corner and rule out two corners by opposite segment vectors, yielding the source `n ≥ 3` polygon and `SM/RegularLocus.lean:12` regularity. Auxiliary unselected marks have zero turns and must not be counted as source corners.

A separate global continuous-circle parameterization is **optional**, not an added gate. The actual compressed cyclic corner tuple with proved edge/closure data and source-trace equivalence is an executable route to the regular polygon. Add a parameter-circle map only if a concrete downstream consumer needs it.

Exact retained crossings, no triple point, all-visit noncrossing, positive lifts and state-sum assembly remain separate obligations. Equal plane values never identify abstract mark owners; a selected smoothing point can lie on two distinct carrier images.

## Snapshot and contribution limits

I authored the marked-successor classification and earlier parts of the carrier cycle/order infrastructure. This is implementation planning, not an independent review of my work. The source hash and selected exact API bodies inspected are bound below; geometry/closed-trace hashes bind drafts at inspection, not passing status.

| File | SHA256 |
| --- | --- |
| `reference/SM/sm-3-statesum.tex` | `fa17a1b162bd5a7a9cabc65fe8f95e4fb53c7f17050bfe8008cb805aa7954af5` |
| `work/checks/CarrierAmbientTransport.body.lean` | `0239a767d840c4c3a559e76b930beafa0c797e8ebca95b2d0614356e0523cffa` |
| `work/checks/CarrierUnchangedComponent.body.lean` | `7301b73e3e90cce8a902632193a5eb25687a9f72800f7305771a404b8ae5fc66` |
| `work/checks/CarrierSmoothing.body.lean` | `27ddd25cb6878afd24f7c71cfee7b003e9bd539c5dbc00eea05bc7642205c61e` |
| `work/checks/CarrierMarkedSegments.body.lean` | `0e6444e24b4270772f3fcbf3c50bf18f75d7445c58bb52ed4e400870a17698b7` |
| `work/checks/CycleFiltering.body.lean` | `9b0aa68627a006733a347c879574724b54f833724579820e13a6fbc8f1722c5e` |
| `work/checks/CarrierSegmentGeometry.body.lean` | `1abcd4093dfacd8681e23d81227e352e0c2ed4faf6dff1139068a1cc83b6b18a` |
| `work/checks/CarrierClosedTrace.body.lean` | `45b2261d7ac41c9112a4a84667890e3cbdd6a5e635230b0100d20f8c36b761a7` |
