import SM.GeoCarrierCount

/-! # GeoCarrierOrder — the trace and the carrier specification of an independent set on the
geometric record domain (CV-DOM unit U1b, tier 0)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0, §3 rulings R1-R5, §5 row **U1b**). Intended home
`work/lean/SM/GeoCarrierOrder.lean`. Checked with
`cd work/lean && lake env lean ../drafts/cvdom/U1b/GeoCarrierOrder.lean` (no `sorry`, standard axioms).

Scope after the coordination with unit U1a (2026-09-14): `SM/GeoCarrierCount.lean` (U1a, landed) already
holds the tier-0 ports of CarrierInheritedOrder, CarrierInheritedInsert, CarrierIndependentOrder,
CarrierSameArc, CarrierMarkedArcLists (and their U1a-side prerequisites): `GeoInheritsMarkOrder`,
`geoInheritsMarkOrder_of_independent (hP) (hS)`, `geoComponentCycle`,
`geoComponentCycle_eq_filtered_markList`, `geoComponentCycle_list_nodup/_mem_iff/_eqOn`, the CV-free
geometric-interlacement lemmas `geo_*`, `GeoPendingPairsTogether`, `geoIndependent_*`. This module
imports it and adds ONLY the remaining U1b targets: the ports of CarrierAffineSegments,
CarrierSegmentGeometry and CarrierClosedTrace onto the accepted geo definitions
(`geoSmoothingSegment`, `geoComponentMarkList`, `geoComponentPlaneCycle` of SM/FlatCarriersDefs.lean),
culminating in `geoTracedSuccessor_of_independent` (`TracedSuccessor`, SM/FlatCarriers.lean:3147),
`geoCarrierSpec_of_independent` (`GeoCarrierSpec` via the accepted `GeoCarrierSpec.of_core`) and
`geo_closed_trace`; plus the §5-named alias `geoComponentCycle_eq_filter`.

No accepted `geo*` name is re-declared (ruling R3). Already accepted and only referenced here
(SM/FlatCarriers.lean): `geoSmoothingSegment_subsegment_data`, `geoSmoothingSegment_positive_direction`,
`geoSmoothingSegment_displacement_ne_zero`, `geoSmoothingSuccessor_ne_self` (all 2841-2889, with
`hn : 3 ≤ n`), and `geoSmoothingSegment_mem_edgeSegment (hP) (S) (a) (u) (hu0) (hu1)` (1466, WITHOUT `hn`
and with `u` explicit — the §5 target `geoSmoothingSegment_mem_edgeSegment (hn) (hP) (S) (a) {u} (hu0) (hu1)`
is therefore not declared: the accepted lemma is strictly stronger). Proofs are the source proofs
verbatim up to renaming. `hn : 3 ≤ n` enters exactly where the accepted geo segment lemmas consume it
(`geoSmoothingSegment_displacement_ne_zero hn`, `geoSmoothingSegment_subsegment_data hn`), hence in
`geoSmoothingSegment_length_pos`, `geoSmoothingSegment_injective`, `geoComponentTraceEdge_data`,
`geo_closed_trace`; `geoTracedSuccessor_of_independent` and `geoCarrierSpec_of_independent` carry it
only because §5 fixes their binder list (ruling R5 note; the `hn`-free content is
`geoComponentMarkList_getElem_successor`). -/

namespace SM.GeoCarrier
open Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-! ## 0. The §5-named form of the inherited cycle (alias of `geoComponentCycle_eq_filtered_markList`) -/

/-- **§5 U1b target** `geoComponentCycle_eq_filter`: the inherited cycle of a carrier is the marked
traversal circle filtered by its owner (definitional; `geoComponentCycle` is U1a's port of
`componentCycle`, SM/GeoCarrierCount.lean). -/
theorem geoComponentCycle_eq_filter {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    geoComponentCycle hP S q = (geoMarkCycle hP).filter (fun m => decide (geoOwner hP S m = q)) :=
  rfl

/-! ## 1. Port of SM/CarrierAffineSegments.lean
`edgePoint_sub_edgePoint`, `edgePoint_affine` are hypothesis-free and shared (accepted, `SM.Carrier`);
`geoSmoothingSegment` is the accepted definition (SM/FlatCarriersDefs.lean:317). -/

@[simp]
theorem geoSmoothingSegment_zero {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    geoSmoothingSegment hP S a 0 = traversalEvaluation P (geoMarkPosition hP a) := by
  simp [geoSmoothingSegment]

@[simp]
theorem geoSmoothingSegment_one {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    geoSmoothingSegment hP S a 1 =
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) := by
  simp [geoSmoothingSegment]

/-- Every constructed segment joins exactly to the next segment, including
the closing join of an actual successor orbit. -/
theorem geoSmoothingSegment_glue {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    geoSmoothingSegment hP S a 1 =
      geoSmoothingSegment hP S (geoSmoothingSuccessor hP S a) 0 := by
  rw [geoSmoothingSegment_one, geoSmoothingSegment_zero]

theorem continuous_geoSmoothingSegment {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    Continuous (geoSmoothingSegment hP S a) :=
  continuous_const.add (continuous_id.smul continuous_const)

/-! ## 2. Port of SM/CarrierSegmentGeometry.lean
Accepted already (SM/FlatCarriers.lean:2841-2889, all with `hn : 3 ≤ n`):
`geoSmoothingSegment_subsegment_data`, `geoSmoothingSegment_positive_direction`,
`geoSmoothingSegment_displacement_ne_zero`, `geoSmoothingSuccessor_ne_self`; and
`geoSmoothingSegment_mem_edgeSegment (hP) (S) (a) (u) (hu0) (hu1)` (SM/FlatCarriers.lean:1466, no
`hn`). The two remaining lemmas follow. The source's `(g1 hn P hP.1).2.1 _` (edge ≠ 0) is `hP.1 _`
(`CrossingGeometry` clause 1). -/

/-- Positive length uses the Euclidean length of the source plane, not the
product-space norm. -/
theorem geoSmoothingSegment_length_pos (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) :
    0 < euclideanLength
      (traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) -
        traversalEvaluation P (geoMarkPosition hP a)) :=
  euclideanLength_pos (geoSmoothingSegment_displacement_ne_zero hn hP S a)

/-- Each actual segment traverses its positive parameter interval without
repetition. This is local segment injectivity, not injectivity of a carrier. -/
theorem geoSmoothingSegment_injective (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) :
    Function.Injective (geoSmoothingSegment hP S a) := by
  intro u v huv
  obtain ⟨t, hst, _, _, _, hformula⟩ := geoSmoothingSegment_subsegment_data hn hP S a
  rw [hformula u, hformula v] at huv
  have hparam := edgePoint_injective
    (hP.1 (geoMarkPosition hP (selectedMarkPerm S a)).1) huv
  exact mul_right_cancel₀ (ne_of_gt (sub_pos.mpr hst)) (add_left_cancel hparam)

/-! ## 3. Port of SM/CarrierClosedTrace.lean
`geoComponentMarkList`, `geoComponentPlaneCycle` are the accepted definitions
(SM/FlatCarriersDefs.lean:290, 310); `geoComponentCycle` and its list lemmas are U1a's
(SM/GeoCarrierCount.lean). -/

/-- The constructed list is nonempty and duplicate-free as a list of marks,
represents the actual inherited component cycle, and contains exactly its owners. -/
theorem geoComponentMarkList_data {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    (geoComponentMarkList hP S q).Nodup ∧
      0 < (geoComponentMarkList hP S q).length ∧
      (geoComponentMarkList hP S q : Cycle (Mark P)) = geoComponentCycle hP S q ∧
      ∀ m : Mark P, m ∈ geoComponentMarkList hP S q ↔ geoOwner hP S m = q := by
  let L := geoComponentMarkList hP S q
  have hL : geoComponentCycle hP S q = (L : Cycle (Mark P)) :=
    geoComponentCycle_eq_filtered_markList hP S q
  have hmem := geoComponentCycle_list_mem_iff hP S q L hL
  obtain ⟨m, hm⟩ := geoOwner_surjective hP S q
  exact ⟨geoComponentCycle_list_nodup hP S q L hL,
    List.length_pos_of_mem ((hmem m).mpr hm), hL.symm, hmem⟩

/-- Independence supplies inherited order for the actual filtered list. Its
cyclic next index, including the last-to-first step, is the smoothed successor. -/
theorem geoComponentMarkList_getElem_successor {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) (i : Fin (geoComponentMarkList hP S q).length) :
    let L := geoComponentMarkList hP S q
    geoSmoothingSuccessor hP S (L[i.val]'i.isLt) =
      L[(i.val + 1) % L.length]'(Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)) := by
  let L := geoComponentMarkList hP S q
  have hdata := geoComponentMarkList_data hP S q
  have he := geoComponentCycle_list_eqOn hP S (geoInheritsMarkOrder_of_independent hP hS)
    q L hdata.2.2.1.symm
  exact (he (List.getElem_mem i.isLt)).symm.trans
    (List.formPerm_apply_getElem L hdata.1 i.val i.isLt)

set_option linter.unusedVariables false in
/-- **§5 U1b target.** The inherited-order field of `GeoCarrierSpec` at every carrier of an
independent set (`TracedSuccessor`, SM/FlatCarriers.lean:3147). `hn` is not used (§5 binder list). -/
theorem geoTracedSuccessor_of_independent (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) : TracedSuccessor hP S q :=
  fun i => geoComponentMarkList_getElem_successor hP hS q i

set_option linter.unusedVariables false in
/-- **§5 U1b target.** The full carrier specification of def:flat-carriers / def:smoothing holds at
every independent set on ANY geometric record domain: `GeoCarrierSpec.of_core` with
`traced_successor` from the inherited order and `inherited_pieces` from the accepted
`geoSmoothingSegment_mem_edgeSegment`. `hn` is not used (§5 binder list). -/
theorem geoCarrierSpec_of_independent (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    GeoCarrierSpec hP S :=
  GeoCarrierSpec.of_core hP S (fun q i => geoComponentMarkList_getElem_successor hP hS q i)
    (fun a u hu0 hu1 => geoSmoothingSegment_mem_edgeSegment hP S a u hu0 hu1)

/-- The affine edge between successive evaluated entries of the actual
component marked list. The modular index explicitly retains the closing edge. -/
def geoComponentTraceEdge {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S)
    (i : Fin (geoComponentMarkList hP S q).length) (u : ℝ) : Plane :=
  let L := geoComponentMarkList hP S q
  let j : Fin L.length :=
    ⟨(i.val + 1) % L.length, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
  traversalEvaluation P (geoMarkPosition hP (L[i.val]'i.isLt)) +
    u • (traversalEvaluation P (geoMarkPosition hP (L[j.val]'j.isLt)) -
      traversalEvaluation P (geoMarkPosition hP (L[i.val]'i.isLt)))

/-- Every edge of an independent component's actual finite trace is its
constructed smoothing segment, has positive Euclidean endpoint displacement,
and joins the next modular-index edge. Continuity is proved for each edge;
no global circle parameterization or true-corner polygon is asserted here. -/
theorem geoComponentTraceEdge_data (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) (i : Fin (geoComponentMarkList hP S q).length) :
    let L := geoComponentMarkList hP S q
    let j : Fin L.length :=
      ⟨(i.val + 1) % L.length, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
    (∀ u : ℝ, geoComponentTraceEdge hP S q i u =
      geoSmoothingSegment hP S (L[i.val]'i.isLt) u) ∧
      0 < euclideanLength
        (geoComponentTraceEdge hP S q i 1 - geoComponentTraceEdge hP S q i 0) ∧
      geoComponentTraceEdge hP S q i 1 = geoComponentTraceEdge hP S q j 0 ∧
      Continuous (geoComponentTraceEdge hP S q i) := by
  let L := geoComponentMarkList hP S q
  let j : Fin L.length :=
    ⟨(i.val + 1) % L.length, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
  have hseg (k : Fin L.length) (u : ℝ) : geoComponentTraceEdge hP S q k u =
      geoSmoothingSegment hP S (L[k.val]'k.isLt) u := by
    dsimp only [geoComponentTraceEdge, geoSmoothingSegment]
    rw [geoComponentMarkList_getElem_successor hP hS q k]
  refine ⟨hseg i, ?_, ?_, ?_⟩
  · rw [hseg i 1, hseg i 0, geoSmoothingSegment_one, geoSmoothingSegment_zero]
    exact geoSmoothingSegment_length_pos hn hP S (L[i.val]'i.isLt)
  · rw [hseg i 1, hseg j 0, geoSmoothingSegment_one, geoSmoothingSegment_zero,
      geoComponentMarkList_getElem_successor hP hS q i]
  · have he : geoComponentTraceEdge hP S q i =
        geoSmoothingSegment hP S (L[i.val]'i.isLt) := funext (hseg i)
    rw [he]
    exact continuous_geoSmoothingSegment hP S (L[i.val]'i.isLt)

/-- **§5 U1b target** `geo_closed_trace`: CarrierClosedTrace's main statement
(`componentTraceEdge_data`) on the geo layer — each carrier of an independent set is traced by a
closed chain of its inherited straight pieces, edge by edge. -/
theorem geo_closed_trace (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) (i : Fin (geoComponentMarkList hP S q).length) :
    let L := geoComponentMarkList hP S q
    let j : Fin L.length :=
      ⟨(i.val + 1) % L.length, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
    (∀ u : ℝ, geoComponentTraceEdge hP S q i u =
      geoSmoothingSegment hP S (L[i.val]'i.isLt) u) ∧
      0 < euclideanLength
        (geoComponentTraceEdge hP S q i 1 - geoComponentTraceEdge hP S q i 0) ∧
      geoComponentTraceEdge hP S q i 1 = geoComponentTraceEdge hP S q j 0 ∧
      Continuous (geoComponentTraceEdge hP S q i) :=
  geoComponentTraceEdge_data hn hP hS q i

end
end SM.GeoCarrier
