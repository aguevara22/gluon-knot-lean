import SM.GeoCarrierOrder
import SM.GeoCarrierGeometry

/-! # GeoCornerPolygon — the corner polygon of a carrier on the geometric record domain
(CV-DOM unit U2b, tiers 0 / 1 / 2)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0, §3 rulings R1-R5, §5 row **U2b**). Intended home
`work/lean/SM/GeoCornerPolygon.lean`. Checked with
`cd work/lean && lake env lean ../drafts/cvdom/U2b/GeoCornerPolygon.lean` (clean, standard axioms).

Port of SM/CarrierCornerPolygon.lean §3-§10 and SM/CarrierActualCornerBlock.lean onto the ACCEPTED
geometric carrier definitions of SM/FlatCarriersDefs.lean (`geoOwner`, `geoSmoothingSuccessor`,
`geoComponentMarkList`, `geoComponentCornerList`, `geoCornerCount`, `geoCornerMark`, `geoCornerPolygon`,
`geoCornerTurn`, `geoSmoothingSegment`, `GeoIndependent`). §0-§2 of the source and the
`TracedSuccessor`-based edge/turn lemmas are already accepted in SM/FlatCarriers.lean (`geoOutSlot`,
`geoInEdge`, `geo_block_compression`, `geo_corner_chain`, `geoCornerPolygon_edge_data`,
`geoCornerPolygon_edge`, `_edge_pred`, `_turn_det`, `_turn_eq_sign`, `_edge_ne_zero`,
`_not_antiparallel_of_det`, all with `htr : TracedSuccessor hP S q`); here `htr` is discharged by U1b's
`geoTracedSuccessor_of_independent hn hP hS q` (SM/GeoCarrierOrder.lean), so every lemma is stated on an
independent set `hS : GeoIndependent hP S` exactly as the source is stated on `S ∈ independentSupports`.

Tiers (ruling R1; R4 for the corner-polygon geometry):
* tier 0, `hP : CrossingGeometry P` — the actual corner block (§0), corner-to-corner chains (§1), the
  compressed block with its trace (§3: `geoCornerPolygon_block`, `geoCornerPolygon_edge_smul`), the
  vertex / smoothing turn signs and the two smoothing corners of a selected crossing (§4), the traced
  curve (`geoCornerPolygon_trace`, §6);
* tier 1, `hG : CarrierGeometry P` — no antiparallel corner, `geoCornerPolygon_regular`,
  `three_le_geoCornerCount` (§5): at a vertex corner the fold-back is excluded by U0's
  `CarrierGeometry.regular` (SM/GeoCarrierGeometry.lean), at a smoothing corner `det ≠ 0` is clause 2 of
  `CrossingGeometry`; the source's `k = 2` case is the antiparallel corner `edge 0 = -edge (0-1)`;
* tier 2, `hW : WeakGeneric P` — only `turn ≠ 0` at vertex corners (`hW.2.1`):
  `geoCornerPolygon_turn_ne_zero`, `geoCornerTurn_ne_zero`, and the assembled clause (ii).

The 4 `Generic` sites of the source (CarrierCornerPolygon.lean:195, 556, 567, 665) become: `hP.1 _`
(edge ≠ 0, clause 1), `hW.2.1 i` (turn ≠ 0, tier 2), `crossing_det_ne_zero_of_geometry hP` (clause 2),
`geo_selected_visits_separated hP hS` (U1a). `hn : 3 ≤ n` is kept exactly where the accepted geo lemmas
consume it (`geoSmoothingSegment_subsegment_data hn`, `geoInEdge_vertex hn`, `geoInEdge_visit hn`,
`geoTracedSuccessor_of_independent hn`); the CarrierActualCornerBlock port needs none.

No accepted `geo*` name is re-declared (ruling R3). Referenced from the library: FlatCarriersDefs
(`geoCornerMark_exists` — in its accepted owner form; the source-shaped form is
`geoCornerMark_exists_of_owner` below), FlatCarriers (`geoCornerMark_mem`, `geoCornerMark_add_one`,
`geo_corner_chain`, the `TracedSuccessor` lemmas, `geoOwner_geoCornerMark`, `isTrueCorner_geoCornerMark`,
`geoCornerMark_injective`), GeoCarrierCount (`geoComponentCornerCycle` and its lemmas,
`geoComponentCycle_list_*`, `geoInheritsMarkOrder_of_independent`, `geo_selected_visits_separated`),
GeoCarrierOrder (`geoComponentMarkList_data`, `geoTracedSuccessor_of_independent`), GeoCarrierGeometry
(`CarrierGeometry`, `.regular`, `.ofWeak`). -/

namespace SM.GeoCarrier
open Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-! ## 0. Port of SM/CarrierActualCornerBlock.lean (tier 0, no `hn`) -/

/-- Rotate the actual owner-filtered list to any mark of that owner. The anchored component
representative is constructed from its actual membership. -/
theorem geoComponentMarkList_rotate_start {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (a : Mark P) (ha : geoOwner hP S a = q) :
    ∃ k : ℕ, ∃ R : List (Mark P), (geoComponentMarkList hP S q).rotate k = a :: R := by
  have ham := ((geoComponentMarkList_data hP S q).2.2.2 a).mpr ha
  obtain ⟨L, R, he⟩ := List.mem_iff_append.mp ham
  refine ⟨L.length, R ++ L, ?_⟩
  rw [he, List.rotate_append_length_eq, List.cons_append]

/-- Every literal representative of the actual inherited component filters to the same actual corner
cycle, independently of the chosen first entry. -/
theorem geoComponentCornerCycle_eq_filter_of_list {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (L : List (Mark P))
    (hL : geoComponentCycle hP S q = (L : Cycle (Mark P))) :
    geoComponentCornerCycle hP S q =
      (L.filter (fun a => decide (IsTrueCorner S a)) : Cycle (Mark P)) := by
  unfold geoComponentCornerCycle
  rw [hL]
  rfl

/-- Starting from an actual true corner, construct the first following true corner and every omitted
intermediate mark. The closed block is an actual prefix of the rotated closed component list, whose
action is the actual successor. The endpoint may equal the anchor; no two-corner premise is used. -/
theorem geoComponent_first_trueCorner_block {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S) (a : Mark P)
    (ha : geoOwner hP S a = q) (hac : IsTrueCorner S a) :
    ∃ (k : ℕ) (R M : List (Mark P)) (b : Mark P) (B : List (Mark P)),
      (geoComponentMarkList hP S q).rotate k = a :: R ∧
      R ++ [a] = M ++ b :: B ∧
      (∀ x ∈ M, ¬ IsTrueCorner S x) ∧ IsTrueCorner S b ∧ geoOwner hP S b = q ∧
      (a :: (M ++ [b])) <+: ((a :: R) ++ [a]) ∧
      (geoComponentCornerCycle hP S q).next (geoComponentCornerCycle_nodup hP S q)
        a ((mem_geoComponentCornerCycle hP S q a).mpr ⟨ha, hac⟩) = b ∧
      Set.EqOn (a :: R).formPerm (geoSmoothingSuccessor hP S) {m | m ∈ a :: R} := by
  let p : Mark P → Bool := fun m => decide (IsTrueCorner S m)
  have hpa : p a = true := by simp only [p, hac, decide_true]
  obtain ⟨k, R, hrot⟩ := geoComponentMarkList_rotate_start hP S q a ha
  have hraw : (geoComponentMarkList hP S q : Cycle (Mark P)) = geoComponentCycle hP S q :=
    (geoComponentMarkList_data hP S q).2.2.1
  have hrotC : ((geoComponentMarkList hP S q).rotate k : Cycle (Mark P)) =
      (geoComponentMarkList hP S q : Cycle (Mark P)) :=
    Cycle.coe_eq_coe.mpr (List.IsRotated.forall _ _)
  have hL : geoComponentCycle hP S q = (a :: R : Cycle (Mark P)) :=
    hraw.symm.trans (hrotC.symm.trans (congrArg (fun L : List (Mark P) => (L : Cycle (Mark P))) hrot))
  have hN := geoComponentCycle_list_nodup hP S q (a :: R) hL
  obtain ⟨M, b, B, hsplit, hM, hb, hnext, hprefix, _, _⟩ := firstCornerBlock p a R hN hpa
  have hnot : ∀ x ∈ M, ¬ IsTrueCorner S x := by
    intro x hx hc
    have he := hM x hx
    simp [p, hc] at he
  have hbc : IsTrueCorner S b := by
    simpa only [p, decide_eq_true_eq] using hb
  have hbclosed : b ∈ R ++ [a] := by
    rw [hsplit]
    exact List.mem_append_right M (List.mem_cons_self)
  have hbL : b ∈ a :: R := by
    rcases List.mem_append.mp hbclosed with hbR | hbA
    · exact List.mem_cons_of_mem a hbR
    · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hbA))
  have hbo : geoOwner hP S b = q :=
    (geoComponentCycle_list_mem_iff hP S q (a :: R) hL b).mp hbL
  have hC : geoComponentCornerCycle hP S q = ((a :: R).filter p : Cycle (Mark P)) :=
    geoComponentCornerCycle_eq_filter_of_list hP S q (a :: R) hL
  have hNF : ((a :: R).filter p).Nodup := hN.filter p
  have haF : a ∈ (a :: R).filter p := by simp [hpa]
  have haC : a ∈ geoComponentCornerCycle hP S q :=
    (mem_geoComponentCornerCycle hP S q a).mpr ⟨ha, hac⟩
  have hpair :
      (⟨geoComponentCornerCycle hP S q, geoComponentCornerCycle_nodup hP S q, haC⟩ :
        {s : Cycle (Mark P) // s.Nodup ∧ a ∈ s}) =
      ⟨((a :: R).filter p : Cycle (Mark P)), hNF, haF⟩ := Subtype.ext hC
  have htransport := congrArg
    (fun s : {s : Cycle (Mark P) // s.Nodup ∧ a ∈ s} => s.val.next s.property.1 a s.property.2) hpair
  change (geoComponentCornerCycle hP S q).next (geoComponentCornerCycle_nodup hP S q) a haC =
    ((a :: R).filter p).next a haF at htransport
  exact ⟨k, R, M, b, B, hrot, hsplit, hnot, hbc, hbo, hprefix, htransport.trans hnext,
    geoComponentCycle_list_eqOn hP S (geoInheritsMarkOrder_of_independent hP hS) q (a :: R) hL⟩

/-! ## 1. From a true corner to the next true corner along `ρ_S` (source §3) -/

/-- **Corner-to-corner chain** (port of `ccp_corner_chain`, in the corner-CYCLE form). For a true
corner `a` of the carrier `q` (with `S` independent), the next corner of the inherited corner cycle
is reached from `a` in `m ≥ 1` steps of `ρ_S`, and every intermediate mark is not a true corner.
Derived from the first retained block of §0. (The corner-LIST form, derived from `TracedSuccessor`,
is the accepted `geo_corner_chain`, SM/FlatCarriers.lean.) -/
theorem geo_corner_chain_of_independent {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S) (a : Mark P)
    (ha : geoOwner hP S a = q) (hac : IsTrueCorner S a) :
    ∃ m : ℕ, 1 ≤ m ∧
      (geoSmoothingSuccessor hP S ^ m) a =
        (geoComponentCornerCycle hP S q).next (geoComponentCornerCycle_nodup hP S q) a
          ((mem_geoComponentCornerCycle hP S q a).mpr ⟨ha, hac⟩) ∧
      ∀ r, 1 ≤ r → r < m → ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ r) a) := by
  obtain ⟨k, R, M, b, B, hrot, hsplit, hnot, hbc, hbo, hprefix, hnext, heqOn⟩ :=
    geoComponent_first_trueCorner_block hP hS q a ha hac
  have hN : (a :: R).Nodup := by
    rw [← hrot]
    exact List.nodup_rotate.mpr (geoComponentMarkList_data hP S q).1
  have hlen : M.length + 2 ≤ R.length + 2 := by
    have := hprefix.length_le
    simp at this
    omega
  have hpow : ∀ i (hi : i < M.length + 2),
      (geoSmoothingSuccessor hP S ^ i) a = (a :: (M ++ [b]))[i]'(by simp; omega) := by
    intro i hi
    rw [ccp_pow_apply_closed_list _ a R hN heqOn i (by omega)]
    exact (hprefix.getElem (by simp; omega)).symm
  refine ⟨M.length + 1, by omega, ?_, ?_⟩
  · rw [hnext, hpow (M.length + 1) (by omega)]
    simp
  · intro r hr1 hrm
    rw [hpow r (by omega)]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hr' : r' < M.length := by omega
    rw [List.getElem_cons_succ, List.getElem_append_left hr']
    exact hnot _ (List.getElem_mem hr')

/-! ## 2. The corner list and the corner polygon (source §4; the definitions are accepted) -/

/-- The corner list is a linear representative of the corner cycle (port of `ccpCornerList_coe`). -/
theorem geoComponentCornerList_coe {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    (geoComponentCornerList hP S q : Cycle (Mark P)) = geoComponentCornerCycle hP S q := rfl

theorem geoCornerPolygon_apply {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    geoCornerPolygon hP S q k =
      traversalEvaluation P (geoMarkPosition hP (geoCornerMark hP S q k)) := rfl

theorem geoCornerMark_mem_cornerCycle {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    geoCornerMark hP S q k ∈ geoComponentCornerCycle hP S q :=
  (mem_geoComponentCornerCycle hP S q _).mpr (geoCornerMark_mem hP S q k)

/-- Every true corner owned by `q` is some corner mark `c_k` (the source shape of
`ccpCornerMark_exists`; the accepted `geoCornerMark_exists` is its `q = geoOwner a` form). -/
theorem geoCornerMark_exists_of_owner {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (a : Mark P) (ha : geoOwner hP S a = q)
    (hac : IsTrueCorner S a) : ∃ k : ZMod (geoCornerCount hP S q), geoCornerMark hP S q k = a := by
  subst ha
  exact geoCornerMark_exists hP S hac

/-! ## 3. Edges of the corner polygon and the trace of a block (source §1, §2, §5) -/

/-- `smoothingSegment_subsegment_data` restated with the outgoing slot, keeping the affine formula
(the accepted `geo_subsegment_data` drops it). -/
theorem geo_subsegment_trace_data (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) :
    ∃ t : ℝ, (geoOutSlot hP S a).2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) =
        edgePoint P (geoOutSlot hP S a).1 t ∧
      ∀ u : ℝ, geoSmoothingSegment hP S a u =
        edgePoint P (geoOutSlot hP S a).1
          ((geoOutSlot hP S a).2.val + u * (t - (geoOutSlot hP S a).2.val)) := by
  obtain ⟨t, hst, ht1, _, hend, hform⟩ := geoSmoothingSegment_subsegment_data hn hP S a
  exact ⟨t, hst, ht1, hend, hform⟩

/-- The image of the outgoing smoothing segment of `a` is the parameter interval on its edge between
its outgoing slot parameter and the endpoint parameter `t`. -/
theorem geo_smoothingSegment_image {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) {e : ZMod n} {s t : ℝ} (hst : s < t)
    (hf : ∀ u : ℝ, geoSmoothingSegment hP S a u = edgePoint P e (s + u * (t - s))) :
    geoSmoothingSegment hP S a '' Set.Icc 0 1 = edgePoint P e '' Set.Icc s t := by
  have hcomp : geoSmoothingSegment hP S a = edgePoint P e ∘ (fun u : ℝ => s + u * (t - s)) :=
    funext hf
  rw [hcomp, Set.image_comp, ccp_image_affine_unit hst]

/-- **Block compression with its trace** (full port of `ccp_block_compression`; the accepted
`geo_block_compression` is the same statement without the union clause). Let `a` be a mark and
`m ≥ 1` such that the marks `ρ_S a, …, ρ_S^{m-1} a` are not true corners (hence unselected visits).
Let `e` and `s` be the edge and parameter of the outgoing slot of `a`. Then every segment of the
block lies on the one original edge `e`, the endpoint `ρ_S^m a` is the point of parameter `t > s`
on `e`, and the union of the `m` segment images is exactly the straight segment
`edgePoint P e '' [s, t]`. -/
theorem geo_block_compression_trace (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (a : Mark P) (m : ℕ) (hm : 1 ≤ m)
    (hmid : ∀ r, 1 ≤ r → r < m → ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ r) a)) :
    (∀ r < m, (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ r) a)).1 = (geoOutSlot hP S a).1) ∧
    ∃ t : ℝ, (geoOutSlot hP S a).2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (geoMarkPosition hP ((geoSmoothingSuccessor hP S ^ m) a)) =
        edgePoint P (geoOutSlot hP S a).1 t ∧
      (⋃ r < m, geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S ^ r) a) '' Set.Icc 0 1) =
        edgePoint P (geoOutSlot hP S a).1 '' Set.Icc (geoOutSlot hP S a).2.val t := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- base case `m + 1 = 1`
      subst hm0
      obtain ⟨t, hst, ht1, hend, hform⟩ := geo_subsegment_trace_data hn hP S a
      refine ⟨?_, t, hst, ht1, ?_, ?_⟩
      · intro r hr
        have hr0 : r = 0 := by omega
        subst hr0
        rw [pow_zero, Equiv.Perm.one_apply]
      · rw [zero_add, pow_one]
        exact hend
      · have hU : (⋃ r < 0 + 1,
            geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S ^ r) a) '' Set.Icc (0:ℝ) 1) =
            geoSmoothingSegment hP S a '' Set.Icc 0 1 := by
          rw [Set.biUnion_lt_succ]
          simp
        rw [hU]
        exact geo_smoothingSegment_image hP S a hst hform
    · -- inductive step `m ≥ 1`
      have hmid' : ∀ r, 1 ≤ r → r < m →
          ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ r) a) :=
        fun r h1 h2 => hmid r h1 (by omega)
      obtain ⟨hedges, t, hst, ht1, hend, himage⟩ := ih hmpos hmid'
      have hedge : edge P (geoOutSlot hP S a).1 ≠ 0 := hP.1 _
      -- the mark `x_m = ρ_S^m a` is an unselected visit
      obtain ⟨v, hxv, hvS⟩ := ccp_not_trueCorner S (hmid m hmpos (Nat.lt_succ_self m))
      -- `ρ_S x_{m-1} = x_m`
      have hprev : geoSmoothingSuccessor hP S ((geoSmoothingSuccessor hP S ^ (m - 1)) a) =
          (geoSmoothingSuccessor hP S ^ m) a := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ']
        congr 2
        omega
      have hin := geo_incoming_visit_position hn hP S _ v (hprev.trans hxv)
      have hedge_prev : (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ (m - 1)) a)).1 =
          (geoOutSlot hP S a).1 :=
        hedges (m - 1) (by omega)
      have hev : v.2.val = (geoOutSlot hP S a).1 := hin.1.symm.trans hedge_prev
      have hslot : geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ m) a) =
          geometricVisitPosition hP v := by
        rw [hxv]
        exact geoOutSlot_unselected hP S v hvS
      -- the endpoint parameter `t` of the block so far is the visit parameter of `v`
      have hxeval : traversalEvaluation P (geoMarkPosition hP ((geoSmoothingSuccessor hP S ^ m) a)) =
          edgePoint P (geoOutSlot hP S a).1 (visitParameter v) := by
        rw [hxv, geoMarkPosition_visit]
        change edgePoint P v.2.val (visitParameter v) = _
        rw [hev]
      have htv : t = visitParameter v :=
        edgePoint_injective hedge (hend.symm.trans hxeval)
      -- the outgoing segment of `x_m`
      obtain ⟨t', hst', ht1', hend', hform'⟩ :=
        geo_subsegment_trace_data hn hP S ((geoSmoothingSuccessor hP S ^ m) a)
      have hslot1 : (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ m) a)).1 =
          (geoOutSlot hP S a).1 := by
        rw [hslot]
        exact hev
      have hslot2 : (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ m) a)).2.val = t := by
        rw [hslot, htv]
        rfl
      rw [hslot2] at hst'
      rw [hslot1] at hend'
      simp only [hslot1, hslot2] at hform'
      refine ⟨?_, t', lt_trans hst hst', ht1', ?_, ?_⟩
      · intro r hr
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr' | hr'
        · exact hedges r hr'
        · rw [hr']
          exact hslot1
      · rw [pow_succ', Equiv.Perm.mul_apply]
        exact hend'
      · rw [Set.biUnion_lt_succ, himage,
          geo_smoothingSegment_image hP S _ hst' hform', ← Set.image_union,
          Set.Icc_union_Icc_eq_Icc hst.le hst'.le]

/-- **Compressed block between consecutive corners** (port of `ccpCornerPolygon_block`). From the
corner `c_k` the corner `c_{k+1}` is reached in `m ≥ 1` steps of `ρ_S`; the intermediate marks are
unselected visits on the one original edge `e` of the outgoing slot of `c_k`, with strictly increasing
parameters; all `m` segments lie on `e`; and the union of their images is exactly the straight segment
from `c_k` to `c_{k+1}`, which is a positive multiple `c • edge P e` of the direction of `e`. Moreover
the edge `e` is the incoming edge at `c_{k+1}`. -/
theorem geoCornerPolygon_block (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    let a := geoCornerMark hP S q k
    let e := (geoOutSlot hP S a).1
    ∃ m : ℕ, 1 ≤ m ∧
      (geoSmoothingSuccessor hP S ^ m) a = geoCornerMark hP S q (k + 1) ∧
      (∀ r, 1 ≤ r → r < m → ∃ v : Visit P,
        (geoSmoothingSuccessor hP S ^ r) a = Sum.inr v ∧ v.1 ∉ S ∧ v.2.val = e) ∧
      (∀ r < m, (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ r) a)).1 = e) ∧
      (∀ r, r + 1 < m →
        (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ r) a)).2.val <
          (geoOutSlot hP S ((geoSmoothingSuccessor hP S ^ (r + 1)) a)).2.val) ∧
      (∃ c : ℝ, 0 < c ∧
        geoCornerPolygon hP S q (k + 1) - geoCornerPolygon hP S q k = c • edge P e) ∧
      e = geoInEdge hP (geoCornerMark hP S q (k + 1)) ∧
      (⋃ r < m, geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S ^ r) a) '' Set.Icc 0 1) =
        (fun u : ℝ => geoCornerPolygon hP S q k +
          u • (geoCornerPolygon hP S q (k + 1) - geoCornerPolygon hP S q k)) ''
            Set.Icc 0 1 := by
  intro a e
  have htr := geoTracedSuccessor_of_independent hn hP hS q
  obtain ⟨m, hm, hchain, hmid⟩ := geo_corner_chain hP S q htr a (geoCornerMark_mem hP S q k).1
    (geoCornerMark_mem hP S q k).2
  rw [← geoCornerMark_add_one hP S q k] at hchain
  obtain ⟨hedges, t, hst, ht1, hend, himage⟩ := geo_block_compression_trace hn hP S a m hm hmid
  have hstart : geoCornerPolygon hP S q k = edgePoint P e (geoOutSlot hP S a).2.val :=
    geo_evaluation_eq_outSlot hP S a
  have hend' : geoCornerPolygon hP S q (k + 1) = edgePoint P e t := by
    rw [geoCornerPolygon_apply, ← hchain]
    exact hend
  refine ⟨m, hm, hchain, ?_, hedges, ?_, ?_, ?_, ?_⟩
  · intro r hr1 hrm
    obtain ⟨v, hv, hvS⟩ := ccp_not_trueCorner S (hmid r hr1 hrm)
    refine ⟨v, hv, hvS, ?_⟩
    have hprev : geoSmoothingSuccessor hP S ((geoSmoothingSuccessor hP S ^ (r - 1)) a) =
        (geoSmoothingSuccessor hP S ^ r) a := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    exact (geo_incoming_visit_position hn hP S _ v (hprev.trans hv)).1.symm.trans
      (hedges (r - 1) (by omega))
  · intro r hr
    obtain ⟨v, hv, hvS⟩ := ccp_not_trueCorner S (hmid (r + 1) (by omega) hr)
    have hprev : geoSmoothingSuccessor hP S ((geoSmoothingSuccessor hP S ^ r) a) =
        (geoSmoothingSuccessor hP S ^ (r + 1)) a := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    have hlt := (geo_incoming_visit_position hn hP S _ v (hprev.trans hv)).2
    rw [hv, geoOutSlot_unselected hP S v hvS]
    exact hlt
  · refine ⟨t - (geoOutSlot hP S a).2.val, sub_pos.mpr hst, ?_⟩
    rw [hstart, hend', edgePoint_sub_edgePoint]
  · have hprev : geoSmoothingSuccessor hP S ((geoSmoothingSuccessor hP S ^ (m - 1)) a) =
        geoCornerMark hP S q (k + 1) := by
      rw [← hchain, ← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    rw [← geoOutSlot_eq_of_succ hP S hprev]
    exact (hedges (m - 1) (by omega)).symm
  · rw [himage, hstart, hend']
    have hf : (fun u : ℝ => edgePoint P e (geoOutSlot hP S a).2.val +
        u • (edgePoint P e t - edgePoint P e (geoOutSlot hP S a).2.val)) =
        edgePoint P e ∘ (fun u : ℝ => (geoOutSlot hP S a).2.val +
          u * (t - (geoOutSlot hP S a).2.val)) := by
      funext u
      exact edgePoint_affine P e _ t u
    rw [hf, Set.image_comp, ccp_image_affine_unit hst]

/-- **§5 U2b target `geoCornerPolygon_edge_smul`** (tier 0): each edge of the corner polygon of a
carrier of an independent set is a positive multiple of the direction of the original edge of the
outgoing slot of its starting corner (port of `ccpCornerPolygon_edge`; the accepted
`geoCornerPolygon_edge` takes `TracedSuccessor` instead of independence). -/
theorem geoCornerPolygon_edge_smul (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    ∃ c : ℝ, 0 < c ∧
      edge (geoCornerPolygon hP S q) k = c • edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1 :=
  geoCornerPolygon_edge hn hP S q (geoTracedSuccessor_of_independent hn hP hS q) k

/-- Port of `ccpCornerPolygon_outEdge_eq_inEdge` on an independent set. -/
theorem geoCornerPolygon_outEdge_eq_inEdge_of_independent (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    (geoOutSlot hP S (geoCornerMark hP S q k)).1 = geoInEdge hP (geoCornerMark hP S q (k + 1)) :=
  geoCornerPolygon_outEdge_eq_inEdge hn hP S q (geoTracedSuccessor_of_independent hn hP hS q) k

/-- Port of `ccpCornerPolygon_edge_pred` on an independent set: the incoming edge of the corner
polygon at `c_k` is a positive multiple of the original edge carrying the incoming segment at `c_k`. -/
theorem geoCornerPolygon_edge_pred_smul (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    ∃ c : ℝ, 0 < c ∧
      edge (geoCornerPolygon hP S q) (k - 1) = c • edge P (geoInEdge hP (geoCornerMark hP S q k)) :=
  geoCornerPolygon_edge_pred hn hP S q (geoTracedSuccessor_of_independent hn hP hS q) k

/-- **Every carrier has nonzero edges** (port of `ccpCornerPolygon_edge_ne_zero`, tier 0). -/
theorem geoCornerPolygon_edge_ne_zero_of_independent (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    edge (geoCornerPolygon hP S q) k ≠ 0 :=
  geoCornerPolygon_edge_ne_zero hn hP S q (geoTracedSuccessor_of_independent hn hP hS q) k

/-! ## 4. Corner turns: vertex sign `τ_i`, smoothing signs `sgn det(d_i, d_j)` (source §6) -/

/-- Port of `ccpCornerPolygon_turn_eq_sign` on an independent set: the corner turn sign is the sign
of the determinant of the original incoming and outgoing directions at that corner. -/
theorem geoCornerPolygon_turn_eq_sign_of_independent (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    turn (geoCornerPolygon hP S q) k =
      SignType.sign (det (edge P (geoInEdge hP (geoCornerMark hP S q k)))
        (edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1)) :=
  geoCornerPolygon_turn_eq_sign hn hP S q (geoTracedSuccessor_of_independent hn hP hS q) k

/-- **§5 U2b target `geoCornerPolygon_turn_vertex`** (tier 0): at an original vertex `i` the turn
sign of the corner polygon is `τ_i = turn P i`. -/
theorem geoCornerPolygon_turn_vertex (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) (i : ZMod n) (h : geoCornerMark hP S q k = Sum.inl i) :
    turn (geoCornerPolygon hP S q) k = turn P i := by
  rw [geoCornerPolygon_turn_eq_sign_of_independent hn hP hS q k, h, geoInEdge_vertex hn hP i,
    geoOutSlot_vertex, turn_det]

/-- **§5 U2b target `geoCornerPolygon_turn_visit`** (tier 0): at a selected crossing of `E_i, E_j`
(`i` the edge of the selected visit `v`, arrived along; `j` the edge of its twin, left along) the
smoothing corner at `v` has sign `sgn det(d_i, d_j) = crossingSign P i j`. -/
theorem geoCornerPolygon_turn_visit (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) (v : Visit P) (hv : v.1 ∈ S)
    (h : geoCornerMark hP S q k = Sum.inr v) :
    turn (geoCornerPolygon hP S q) k = crossingSign P v.2.val (visitTwin v).2.val := by
  rw [geoCornerPolygon_turn_eq_sign_of_independent hn hP hS q k, h, geoInEdge_visit hn hP v,
    geoOutSlot_selected hP S v hv]
  rfl

/-- At a selected visit the determinant of the original incoming and outgoing directions is nonzero:
transversality of the crossing, clause 2 of `CrossingGeometry` (tier 0). -/
theorem geo_visit_corner_det_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    det (edge P (geoInEdge hP (Sum.inr v))) (edge P (geoOutSlot hP S (Sum.inr v)).1) ≠ 0 := by
  rw [geoInEdge_visit hn hP v, geoOutSlot_selected hP S v hv]
  have hc : IsCrossing P {v.2.val, (visitTwin v).2.val} := by
    rw [← visit_crossing_val_eq_pair v]
    exact v.1.property
  exact crossing_det_ne_zero_of_geometry hP hc

/-- A smoothing corner has a nonzero turn (tier 0). -/
theorem geoCornerPolygon_turn_visit_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) (v : Visit P) (hv : v.1 ∈ S)
    (h : geoCornerMark hP S q k = Sum.inr v) : turn (geoCornerPolygon hP S q) k ≠ 0 := by
  rw [geoCornerPolygon_turn_eq_sign_of_independent hn hP hS q k, h]
  exact sign_ne_zero.mpr (geo_visit_corner_det_ne_zero hn hP S v hv)

/-- **§5 U2b target `geoCornerPolygon_turn_visit_twin`** (tier 0; port of
`ccp_selected_crossing_two_corners`): **the two smoothing corners of a selected crossing**, one on
each of the two carriers through the site, have signs `sgn det(d_i, d_j)` and `sgn det(d_j, d_i)`:
one left and one right. -/
theorem geoCornerPolygon_turn_visit_twin (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (v : Visit P)
    (hv : v.1 ∈ S) :
    let q := geoOwner hP S (Sum.inr v)
    let q' := geoOwner hP S (Sum.inr (visitTwin v))
    q ≠ q' ∧
    ∃ (k : ZMod (geoCornerCount hP S q)) (k' : ZMod (geoCornerCount hP S q')),
      geoCornerMark hP S q k = Sum.inr v ∧
      geoCornerMark hP S q' k' = Sum.inr (visitTwin v) ∧
      turn (geoCornerPolygon hP S q) k = crossingSign P v.2.val (visitTwin v).2.val ∧
      turn (geoCornerPolygon hP S q') k' = crossingSign P (visitTwin v).2.val v.2.val ∧
      turn (geoCornerPolygon hP S q') k' = - turn (geoCornerPolygon hP S q) k ∧
      ((turn (geoCornerPolygon hP S q) k = 1 ∧ turn (geoCornerPolygon hP S q') k' = -1) ∨
        (turn (geoCornerPolygon hP S q) k = -1 ∧ turn (geoCornerPolygon hP S q') k' = 1)) := by
  intro q q'
  have hv' : (visitTwin v).1 ∈ S := by
    rw [visitTwin_crossing]
    exact hv
  obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hP S q (Sum.inr v) rfl hv
  obtain ⟨k', hk'⟩ := geoCornerMark_exists_of_owner hP S q' (Sum.inr (visitTwin v)) rfl hv'
  have h1 := geoCornerPolygon_turn_visit hn hP hS q k v hv hk
  have h2 := geoCornerPolygon_turn_visit hn hP hS q' k' (visitTwin v) hv' hk'
  rw [visitTwin_involutive] at h2
  have hneg : turn (geoCornerPolygon hP S q') k' = - turn (geoCornerPolygon hP S q) k := by
    rw [h1, h2, crossingSign_swap]
  have hne := geoCornerPolygon_turn_visit_ne_zero hn hP hS q k v hv hk
  refine ⟨geo_selected_visits_separated hP hS v hv, k, k', hk, hk', h1, h2, hneg, ?_⟩
  rw [hneg]
  rcases SignType.trichotomy (turn (geoCornerPolygon hP S q) k) with h | h | h
  · right
    rw [h]
    exact ⟨rfl, rfl⟩
  · exact (hne h).elim
  · left
    rw [h]
    exact ⟨rfl, rfl⟩

/-- The turn of a carrier at an original vertex `i` (the accepted `geoCornerTurn`) is `turn P i`
(tier 0; the accepted `generic_geoCornerTurn_vertex` is its `Generic` special case). -/
theorem geoCornerTurn_vertex (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (i : ZMod n) :
    geoCornerTurn hP S (Sum.inl i) = turn P i := by
  unfold geoCornerTurn
  exact geoCornerPolygon_turn_vertex hn hP hS _ _ i
    (geoCornerMark_geoCornerIndex hP S (isTrueCorner_vertex S i))

/-- The turn of a carrier at a selected visit `v` is `crossingSign P v.2 (visitTwin v).2` (tier 0;
the accepted `generic_geoCornerTurn_visit` is its `Generic` special case). -/
theorem geoCornerTurn_visit (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (v : Visit P) (hv : v.1 ∈ S) :
    geoCornerTurn hP S (Sum.inr v) = crossingSign P v.2.val (visitTwin v).2.val := by
  unfold geoCornerTurn
  exact geoCornerPolygon_turn_visit hn hP hS _ _ v hv
    (geoCornerMark_geoCornerIndex hP S ((isTrueCorner_visit S v).mpr hv))

/-! ### Tier 2: nonzero turns (`WeakGeneric`, clause 2 `turn P i ≠ 0` at vertex corners) -/

/-- At an original vertex the determinant of the original incoming and outgoing directions is
nonzero: `τ_i ≠ 0` (tier 2, `hW.2.1`). -/
theorem geo_vertex_corner_det_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hW : WeakGeneric P)
    (S : Finset (Crossing P)) (i : ZMod n) :
    det (edge P (geoInEdge (weak_crossingGeometry hW) (Sum.inl i)))
      (edge P (geoOutSlot (weak_crossingGeometry hW) S (Sum.inl i)).1) ≠ 0 := by
  rw [geoInEdge_vertex hn _ i, geoOutSlot_vertex]
  have hne := hW.2.1 i
  rw [turn_det] at hne
  exact sign_ne_zero.mp hne

/-- Port of `ccp_corner_directions_det_ne_zero` (tier 2): the determinant of the original incoming
and outgoing directions at a true corner is nonzero — at a vertex by `turn P i ≠ 0`, at a selected
crossing by transversality. -/
theorem geo_corner_directions_det_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hW : WeakGeneric P)
    (S : Finset (Crossing P)) (a : Mark P) (ha : IsTrueCorner S a) :
    det (edge P (geoInEdge (weak_crossingGeometry hW) a))
      (edge P (geoOutSlot (weak_crossingGeometry hW) S a).1) ≠ 0 := by
  cases a with
  | inl i => exact geo_vertex_corner_det_ne_zero hn hW S i
  | inr v => exact geo_visit_corner_det_ne_zero hn (weak_crossingGeometry hW) S v ha

/-- Port of `ccpCornerPolygon_det_ne_zero` (tier 2). -/
theorem geoCornerPolygon_det_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hW : WeakGeneric P)
    {S : Finset (Crossing P)} (hS : GeoIndependent (weak_crossingGeometry hW) S)
    (q : GeoComponent (weak_crossingGeometry hW) S)
    (k : ZMod (geoCornerCount (weak_crossingGeometry hW) S q)) :
    det (edge (geoCornerPolygon (weak_crossingGeometry hW) S q) (k - 1))
      (edge (geoCornerPolygon (weak_crossingGeometry hW) S q) k) ≠ 0 := by
  obtain ⟨c, hc, he⟩ := geoCornerPolygon_turn_det hn (weak_crossingGeometry hW) S q
    (geoTracedSuccessor_of_independent hn _ hS q) k
  rw [he]
  exact mul_ne_zero hc.ne'
    (geo_corner_directions_det_ne_zero hn hW S _ (geoCornerMark_mem _ S q k).2)

/-- **§5 U2b target `geoCornerPolygon_turn_ne_zero`** (tier 2): all corner turns of a carrier are
nonzero. -/
theorem geoCornerPolygon_turn_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hW : WeakGeneric P)
    {S : Finset (Crossing P)} (hS : GeoIndependent (weak_crossingGeometry hW) S)
    (q : GeoComponent (weak_crossingGeometry hW) S)
    (k : ZMod (geoCornerCount (weak_crossingGeometry hW) S q)) :
    turn (geoCornerPolygon (weak_crossingGeometry hW) S q) k ≠ 0 := by
  rw [turn_det]
  exact sign_ne_zero.mpr (geoCornerPolygon_det_ne_zero hn hW hS q k)

/-- The turn of a carrier at any of its corner marks (the accepted `geoCornerTurn`) is nonzero
(tier 2). -/
theorem geoCornerTurn_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hW : WeakGeneric P)
    {S : Finset (Crossing P)} (hS : GeoIndependent (weak_crossingGeometry hW) S) (a : Mark P) :
    geoCornerTurn (weak_crossingGeometry hW) S a ≠ 0 := by
  unfold geoCornerTurn
  exact geoCornerPolygon_turn_ne_zero hn hW hS _ _

/-! ## 5. No antiparallel consecutive directions, regularity, at least three corners
(source §7-§8, at tier 1 by ruling R4) -/

/-- **No antiparallel consecutive directions** (port of `ccpCornerPolygon_not_antiparallel`, tier 1).
At a vertex corner `i` the two corner-polygon edges are positive multiples of `edge P (i-1)`,
`edge P i`, which are never antiparallel on a `CarrierGeometry` polygon (`CarrierGeometry.regular`,
the fold-back exclusion of U0); at a smoothing corner `det(in, out) ≠ 0` (clause 2 of
`CrossingGeometry`). -/
theorem geoCornerPolygon_not_antiparallel (hn : 3 ≤ n) {P : LabelledTuple n}
    (hG : CarrierGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S)
    (q : GeoComponent hG.cg S) (k : ZMod (geoCornerCount hG.cg S q)) :
    ¬ ∃ r : ℝ, r < 0 ∧
      edge (geoCornerPolygon hG.cg S q) k = r • edge (geoCornerPolygon hG.cg S q) (k - 1) := by
  have htr := geoTracedSuccessor_of_independent hn hG.cg hS q
  have hcorner := (geoCornerMark_mem hG.cg S q k).2
  cases hc : geoCornerMark hG.cg S q k with
  | inl i =>
    rintro ⟨r, hr, hre⟩
    obtain ⟨c₁, hc₁, he₁⟩ := geoCornerPolygon_edge_pred hn hG.cg S q htr k
    obtain ⟨c₂, hc₂, he₂⟩ := geoCornerPolygon_edge hn hG.cg S q htr k
    rw [hc, geoInEdge_vertex hn hG.cg i] at he₁
    rw [hc, geoOutSlot_vertex] at he₂
    have h1 : c₂ • edge P i = (r * c₁) • edge P (i - 1) := by
      rw [← he₂, hre, he₁, smul_smul]
    have h2 : edge P i = (c₂⁻¹ * (r * c₁)) • edge P (i - 1) := by
      rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hc₂.ne', one_smul]
    exact (hG.regular hn i).2.2 ⟨c₂⁻¹ * (r * c₁),
      mul_neg_of_pos_of_neg (inv_pos.mpr hc₂) (mul_neg_of_neg_of_pos hr hc₁), h2⟩
  | inr v =>
    rw [hc] at hcorner
    have hv : v.1 ∈ S := hcorner
    apply geoCornerPolygon_not_antiparallel_of_det hn hG.cg S q htr k
    rw [hc]
    exact geo_visit_corner_det_ne_zero hn hG.cg S v hv

/-- **§5 U2b target `geoCornerPolygon_regular`** (tier 1, ruling R4): every carrier of an independent
set on a `CarrierGeometry` polygon lies in the regular locus (`SM.Regular`). -/
theorem geoCornerPolygon_regular (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) :
    Regular (geoCornerPolygon hG.cg S q) := by
  rw [regular_iff_edges]
  intro k
  exact ⟨geoCornerPolygon_edge_ne_zero_of_independent hn hG.cg hS q k,
    geoCornerPolygon_not_antiparallel hn hG hS q k⟩

/-- **§5 U2b target `three_le_geoCornerCount`**, at tier 1 (the §5 row says "tier 2 as in the source;
try tier 1 first" — tier 1 suffices): **every carrier has at least three corners.** One nonzero
segment cannot close (`k = 1` would force a zero edge); a closed polygon of two nonzero segments has
antiparallel corners (`k = 2` gives `edge 0 = (-1) • edge (0 - 1)`, against
`geoCornerPolygon_not_antiparallel`). -/
theorem three_le_geoCornerCount (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S) :
    3 ≤ geoCornerCount hG.cg S q := by
  by_contra hlt
  have hpos : 0 < geoCornerCount hG.cg S q := geoComponentCornerList_length_pos hG.cg S q
  rcases (show geoCornerCount hG.cg S q = 1 ∨ geoCornerCount hG.cg S q = 2 by omega) with h1 | h2
  · -- one corner: the single edge closes, so it is zero
    have hone : ((1 : ℕ) : ZMod (geoCornerCount hG.cg S q)) = 0 :=
      (ZMod.natCast_eq_zero_iff 1 _).mpr (by rw [h1])
    have hzero : edge (geoCornerPolygon hG.cg S q) 0 = 0 := by
      have h01 : (0 : ZMod (geoCornerCount hG.cg S q)) + 1 = 0 := by
        rw [zero_add]
        exact_mod_cast hone
      simp only [edge, h01, sub_self]
    exact geoCornerPolygon_edge_ne_zero_of_independent hn hG.cg hS q 0 hzero
  · -- two corners: the two edges are opposite, an antiparallel corner
    have htwo : ((2 : ℕ) : ZMod (geoCornerCount hG.cg S q)) = 0 :=
      (ZMod.natCast_eq_zero_iff 2 _).mpr (by rw [h2])
    have h11 : (1 : ZMod (geoCornerCount hG.cg S q)) + 1 = 0 := by
      have : ((2 : ℕ) : ZMod (geoCornerCount hG.cg S q)) = 1 + 1 := by push_cast; ring
      rw [← this]
      exact htwo
    have hsucc : (0 : ZMod (geoCornerCount hG.cg S q)) + 1 = 0 - 1 := by
      rw [zero_add, zero_sub, eq_neg_iff_add_eq_zero]
      exact h11
    have hopp : edge (geoCornerPolygon hG.cg S q) 0 =
        - edge (geoCornerPolygon hG.cg S q) (0 - 1) := by
      simp only [edge, hsucc, sub_add_cancel]
      abel
    exact geoCornerPolygon_not_antiparallel hn hG hS q 0
      ⟨-1, by norm_num, by rw [hopp, neg_one_smul]⟩

/-- The §5-printed tier-2 shape of `three_le_geoCornerCount` (a corollary: `WeakGeneric →
CarrierGeometry`; the two `CrossingGeometry` proofs are identified by proof irrelevance). -/
theorem three_le_geoCornerCount_of_weak (hn : 3 ≤ n) {P : LabelledTuple n} (hW : WeakGeneric P)
    {S : Finset (Crossing P)} (hS : GeoIndependent (weak_crossingGeometry hW) S)
    (q : GeoComponent (weak_crossingGeometry hW) S) :
    3 ≤ geoCornerCount (weak_crossingGeometry hW) S q :=
  three_le_geoCornerCount hn hW.carrierGeometry hS q

/-- Tier-2 form of `geoCornerPolygon_regular` (corollary, same identification). -/
theorem geoCornerPolygon_regular_of_weakGeneric (hn : 3 ≤ n) {P : LabelledTuple n}
    (hW : WeakGeneric P) {S : Finset (Crossing P)}
    (hS : GeoIndependent (weak_crossingGeometry hW) S)
    (q : GeoComponent (weak_crossingGeometry hW) S) :
    Regular (geoCornerPolygon (weak_crossingGeometry hW) S q) :=
  geoCornerPolygon_regular hn hW.carrierGeometry hS q

/-! ## 6. The traced curve of the carrier is its corner polygon (source §9, tier 0) -/

/-- Iterates of `ρ_S` stay in the same carrier. -/
theorem geo_pow_owner {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a : Mark P) (r : ℕ) :
    geoOwner hP S ((geoSmoothingSuccessor hP S ^ r) a) = geoOwner hP S a :=
  (geoOwner_eq_iff hP S _ _).mpr (Equiv.Perm.SameCycle.symm ⟨r, by simp⟩)

/-- Every mark owned by `q` is reached from a true corner `a` owned by `q` by `r` steps of `ρ_S`
through non-corners only (the last corner before `x`). -/
theorem geo_previous_corner {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (x : Mark P) (hx : geoOwner hP S x = q) :
    ∃ (a : Mark P) (r : ℕ), geoOwner hP S a = q ∧ IsTrueCorner S a ∧
      (geoSmoothingSuccessor hP S ^ r) a = x ∧
      ∀ i, 1 ≤ i → i ≤ r → ¬ IsTrueCorner S ((geoSmoothingSuccessor hP S ^ i) a) := by
  obtain ⟨a₀, ha₀, hc₀⟩ := geoComponent_has_trueCorner hP S q
  have hsc : (geoSmoothingSuccessor hP S).SameCycle a₀ x :=
    (geoOwner_eq_iff hP S a₀ x).mp (ha₀.trans hx.symm)
  obtain ⟨N, _, hN⟩ := hsc.exists_pow_eq'
  let Pr : ℕ → Prop := fun i => IsTrueCorner S ((geoSmoothingSuccessor hP S ^ i) a₀)
  have hle : Nat.findGreatest Pr N ≤ N := Nat.findGreatest_le N
  have hPr0 : Pr 0 := by
    show IsTrueCorner S ((geoSmoothingSuccessor hP S ^ 0) a₀)
    rw [pow_zero, Equiv.Perm.one_apply]
    exact hc₀
  have hspec : Pr (Nat.findGreatest Pr N) := Nat.findGreatest_spec (Nat.zero_le N) hPr0
  refine ⟨(geoSmoothingSuccessor hP S ^ Nat.findGreatest Pr N) a₀, N - Nat.findGreatest Pr N,
    ?_, hspec, ?_, ?_⟩
  · rw [geo_pow_owner]
    exact ha₀
  · rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hle]
    exact hN
  · intro i hi1 hir
    rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm]
    exact @Nat.findGreatest_is_greatest (Nat.findGreatest Pr N + i) Pr _ N (by omega) (by omega)

/-- Each edge segment of the corner polygon is the straight segment between consecutive corners. -/
theorem geoCornerPolygon_edgeSegment {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    edgeSegment (geoCornerPolygon hP S q) k =
      (fun u : ℝ => geoCornerPolygon hP S q k +
        u • (geoCornerPolygon hP S q (k + 1) - geoCornerPolygon hP S q k)) '' Set.Icc 0 1 := by
  ext x
  simp only [edgeSegment, Set.mem_ofPred_eq, Set.mem_image, Set.mem_Icc, edgePoint, edge]
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, ⟨h0, h1⟩, rfl⟩
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    exact ⟨t, h0, h1, rfl⟩

/-- **§5 U2b target `geoCornerPolygon_trace`** (tier 0; port of `ccpCornerPolygon_trace`, sides in
the §5 order): **the carrier traced by its inherited straight subsegments is its corner polygon** —
the union of the edge segments of the corner polygon of `q` equals the union of the outgoing
segments of all marks owned by `q` (omitting the unselected marks changes no point of the traced
curve). -/
theorem geoCornerPolygon_trace (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (q : GeoComponent hP S) :
    (⋃ k, edgeSegment (geoCornerPolygon hP S q) k) =
      ⋃ a ∈ {a : Mark P | geoOwner hP S a = q}, geoSmoothingSegment hP S a '' Set.Icc 0 1 := by
  apply Set.Subset.antisymm
  · apply Set.iUnion_subset
    intro k
    obtain ⟨m, _, _, _, _, _, _, _, himage⟩ := geoCornerPolygon_block hn hP hS q k
    rw [geoCornerPolygon_edgeSegment, ← himage]
    apply Set.iUnion₂_subset
    intro r _
    apply Set.subset_biUnion_of_mem (u := fun a => geoSmoothingSegment hP S a '' Set.Icc (0:ℝ) 1)
    show geoOwner hP S _ = q
    rw [geo_pow_owner]
    exact (geoCornerMark_mem hP S q k).1
  · apply Set.iUnion₂_subset
    intro x hx
    obtain ⟨a, r, ha, hac, hrx, hmid⟩ := geo_previous_corner hP S q x hx
    obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hP S q a ha hac
    obtain ⟨m, hm, hchain, _, _, _, _, _, himage⟩ := geoCornerPolygon_block hn hP hS q k
    rw [hk] at himage hchain
    have hrm : r < m := by
      by_contra hle
      exact hmid m hm (not_lt.mp hle)
        (hchain ▸ (geoCornerMark_mem hP S q (k + 1)).2)
    refine Set.Subset.trans ?_ (Set.subset_iUnion _ k)
    rw [geoCornerPolygon_edgeSegment, ← himage, ← hrx]
    exact Set.subset_biUnion_of_mem (u := fun r =>
      geoSmoothingSegment hP S ((geoSmoothingSuccessor hP S ^ r) a) '' Set.Icc 0 1) hrm

/-! ## 7. lem:carriers clause (ii), assembled on the geo layer (source §10; tier 2 only because of
the nonzero-turn clause — every other clause is tier 0 or tier 1 above) -/

/-- **lem:carriers (ii) on the geometric carrier layer** (port of `carriers_clause_ii`). For `P`
weakly generic with `n ≥ 3`, `S` independent and every carrier `q`: the corner polygon traces the
carrier; every edge is nonzero and a positive multiple of an original edge direction; at least three
corners; no antiparallel consecutive directions (regular locus); all corner turns nonzero; at an
original vertex `i` the turn sign is `turn P i`; at a selected crossing the two smoothing corners
have opposite signs `crossingSign P i j`, `crossingSign P j i`, one left and one right. -/
theorem geo_carriers_clause_ii (hn : 3 ≤ n) {P : LabelledTuple n} (hW : WeakGeneric P)
    {S : Finset (Crossing P)} (hS : GeoIndependent (weak_crossingGeometry hW) S) :
    let hP := weak_crossingGeometry hW
    (∀ q : GeoComponent hP S,
      (⋃ k, edgeSegment (geoCornerPolygon hP S q) k) =
        ⋃ a ∈ {a : Mark P | geoOwner hP S a = q}, geoSmoothingSegment hP S a '' Set.Icc 0 1) ∧
    (∀ (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)),
      edge (geoCornerPolygon hP S q) k ≠ 0 ∧
      ∃ (c : ℝ) (e : ZMod n), 0 < c ∧ edge (geoCornerPolygon hP S q) k = c • edge P e) ∧
    (∀ q : GeoComponent hP S, 3 ≤ geoCornerCount hP S q) ∧
    (∀ (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)),
      ¬ ∃ r : ℝ, r < 0 ∧
        edge (geoCornerPolygon hP S q) k = r • edge (geoCornerPolygon hP S q) (k - 1)) ∧
    (∀ q : GeoComponent hP S, Regular (geoCornerPolygon hP S q)) ∧
    (∀ (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)),
      turn (geoCornerPolygon hP S q) k ≠ 0) ∧
    (∀ (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) (i : ZMod n),
      geoCornerMark hP S q k = Sum.inl i → turn (geoCornerPolygon hP S q) k = turn P i) ∧
    (∀ (v : Visit P), v.1 ∈ S →
      geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v)) ∧
      ∃ (k : ZMod (geoCornerCount hP S (geoOwner hP S (Sum.inr v))))
        (k' : ZMod (geoCornerCount hP S (geoOwner hP S (Sum.inr (visitTwin v))))),
        geoCornerMark hP S _ k = Sum.inr v ∧
        geoCornerMark hP S _ k' = Sum.inr (visitTwin v) ∧
        turn (geoCornerPolygon hP S _) k = crossingSign P v.2.val (visitTwin v).2.val ∧
        turn (geoCornerPolygon hP S _) k' = crossingSign P (visitTwin v).2.val v.2.val ∧
        turn (geoCornerPolygon hP S _) k' = - turn (geoCornerPolygon hP S _) k ∧
        ((turn (geoCornerPolygon hP S _) k = 1 ∧ turn (geoCornerPolygon hP S _) k' = -1) ∨
          (turn (geoCornerPolygon hP S _) k = -1 ∧ turn (geoCornerPolygon hP S _) k' = 1))) := by
  intro hP
  refine ⟨fun q => geoCornerPolygon_trace hn hP hS q,
    fun q k => ⟨geoCornerPolygon_edge_ne_zero_of_independent hn hP hS q k, ?_⟩,
    fun q => three_le_geoCornerCount_of_weak hn hW hS q,
    fun q k => geoCornerPolygon_not_antiparallel hn hW.carrierGeometry hS q k,
    fun q => geoCornerPolygon_regular_of_weakGeneric hn hW hS q,
    fun q k => geoCornerPolygon_turn_ne_zero hn hW hS q k,
    fun q k i h => geoCornerPolygon_turn_vertex hn hP hS q k i h,
    fun v hv => geoCornerPolygon_turn_visit_twin hn hP hS v hv⟩
  obtain ⟨c, hc, he⟩ := geoCornerPolygon_edge_smul hn hP hS q k
  exact ⟨c, _, hc, he⟩

end
end SM.GeoCarrier
