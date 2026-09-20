-- R174_Port_GenericSelectedUnits_draft (assembler, 2026-09-15 ≈ 22:30 UTC / 6:30pm ET): the row-174 material of
-- R174_Assembled.lean on the PORTED Wave-1 library module SM.BigonDeletion (work/lean/SM/BigonDeletion.lean,
-- ported 20:20Z 2026-09-15 from Moves_Assembled.lean) instead of the frozen skeleton copy: the two imports below +
-- Site_174.lean lines 1868-2941 (the `s174_` block) + the five unit appendices (same ranges and de-duplication as
-- R174_Assembled.lean, see assemble_R174.py) + the composition block, all verbatim.  This is the draft of the
-- library module RProof/GenericSelectedUnits.lean proposed in R174_ASSEMBLY_REPORT.md §7 (rename the module
-- docstrings before porting).  Compile: `cd work/lean && lake env lean ../drafts/moves/R174_Port_GenericSelectedUnits_draft.lean`
-- — exit 0, 0 errors, 0 `sorry` warnings; #print axioms r174_gsc_moves_of_arc_rec = propext, Classical.choice,
-- Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness (no sorryAx).
import SM.BigonDeletion
import RProof.RALedgers


/-! ## Site 174 (Wave 2, I-174): the `m`-corner bigon on the `E`-side carrier diagram

Prover of unit I-174, 2026-09-15.  Everything below is NEW (nothing above changed); names carry the
prefix `s174_`.  The plan is PLAN_FINAL.md §4.2: on `D_H := carrierDiagram hn hG' hSm' (τ qAB)` (the
positive lift of the corner polygon of the `E-b` carrier) the selected crossing `m'` is a corner of the
corner polygon, its two incident edges are the pieces of `ℓ₃`/`ℓ₁` (or `ℓ₁`/`ℓ₃`) through the adjacent
visits `w'(ℓ₃)`, `x'(ℓ₁)`, and the remote strand is the `ℓ₂`-piece through `w'(ℓ₂), x'(ℓ₂)`; `K` is the
closed contact triangle `conv{x', m', w'}`.  The site is built in two layers: a generic core
(`s174_core`, on any `CarrierGeometry` polygon, independent support, carrier and selected corner) and
the `GT_Endpoint` wrapper (`s174_site`), which derives the traversal order at the corner from the
canonical sign condition. -/

namespace SM.Link

open SM SM.GeoCarrier SM.Carrier RProof

noncomputable section

variable {n : ℕ} [NeZero n]

theorem s174_pos_over_iff {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing) {s t : Γ.Strand}
    (hx : x.val = {s, t}) (hst : s ≠ t) :
    (Γ.positiveDiagram hΓ).overStrand x = s ↔ 0 < det (Γ.dir s) (Γ.dir t) := by
  have hpos : 0 < det (Γ.dir ((Γ.positiveDiagram hΓ).overStrand x))
      (Γ.dir ((Γ.positiveDiagram hΓ).underStrand x)) := Γ.positiveDiagram_det_pos hΓ x
  have hs : s ∈ x.val := by rw [hx]; exact Finset.mem_insert_self _ _
  have ht : t ∈ x.val := by rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hmem : (Γ.positiveDiagram hΓ).overStrand x ∈ ({s, t} : Finset Γ.Strand) := by
    rw [← hx]; exact (Γ.positiveDiagram hΓ).over_mem x
  constructor
  · intro h
    have hu : (Γ.positiveDiagram hΓ).underStrand x = t :=
      ((Γ.positiveDiagram hΓ).eq_under_of_mem_of_ne x ht
        (fun heq => hst.symm (heq.trans h))).symm
    rw [h, hu] at hpos
    exact hpos
  · intro hdet
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · exfalso
      have h' : (Γ.positiveDiagram hΓ).overStrand x = t := Finset.mem_singleton.mp h
      have hu : (Γ.positiveDiagram hΓ).underStrand x = s :=
        ((Γ.positiveDiagram hΓ).eq_under_of_mem_of_ne x hs (fun heq => hst (heq.trans h'))).symm
      rw [h', hu, det_swap] at hpos
      linarith

theorem s174_switch_over_self_iff (D : Diagram) (x : D.Γ.Crossing) {s t : D.Γ.Strand}
    (hx : x.val = {s, t}) (hst : s ≠ t) :
    (D.switch x).overStrand x = s ↔ D.overStrand x = t := by
  have hs : s ∈ x.val := by rw [hx]; exact Finset.mem_insert_self _ _
  have ht : t ∈ x.val := by rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [D.switch_overStrand_self]
  constructor
  · intro h
    exact (D.eq_over_of_mem_of_ne x ht (by rw [h]; exact hst.symm)).symm
  · intro h
    exact (D.eq_under_of_mem_of_ne x hs (by rw [h]; exact hst)).symm

omit [NeZero n] in
theorem s174_exact_symm {P P' : LabelledTuple n} {e f g : ZMod n}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
    (hX : ExactTriangleVisitOrders P P' e f g hs) :
    ExactTriangleVisitOrders P' P e f g (fun s => (hs s).symm) := by
  intro v w he
  have h1 := hX ((visitTransport hs).symm w) ((visitTransport hs).symm v) he.symm
  have h2 := hX ((visitTransport hs).symm v) ((visitTransport hs).symm w) he
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1 h2
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · have hu' : ((visitTransport hs).symm w).1.val ∪ ((visitTransport hs).symm v).1.val =
        {e, f, g} := by
      rw [Finset.union_comm]; exact hu
    exact (h1.1 hu').symm
  · exact (h2.2 hu).symm

section S174Core

variable {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  (hs' : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
  {h_in h_s h_out : ZMod n}
  (hcef : IsCrossing P {h_in, h_s}) (hceg : IsCrossing P {h_in, h_out})
  (hcfg : IsCrossing P {h_s, h_out})
  {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)

omit [NeZero n] in
theorem s174_ne_of_isCrossing {i j : ZMod n} (h : IsCrossing P {i, j}) : i ≠ j :=
  P1.ne_of_isCrossing_pair h

omit [NeZero n] in
theorem s174_triple_perm_gef' : ({h_out, h_in, h_s} : Finset (ZMod n)) = {h_in, h_s, h_out} := by
  ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

omit [NeZero n] in
theorem s174_triple_perm_feg' : ({h_s, h_in, h_out} : Finset (ZMod n)) = {h_in, h_s, h_out} := by
  ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

include hcfg in
/-- adjacency of `y_in`, `c_in` on `h_in` in parameter form -/
theorem s174_adj_in (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs') (y : Visit P)
    (hy : y.2.val = (G11_vef hcef).2.val) :
    ¬ (visitParameter (G11_vef hcef) < visitParameter y ∧
        visitParameter y < visitParameter (G11_veg hceg)) ∧
    ¬ (visitParameter (G11_veg hceg) < visitParameter y ∧
        visitParameter y < visitParameter (G11_vef hcef)) :=
  G11_no_visit_between hs' (s174_ne_of_isCrossing hcef) (s174_ne_of_isCrossing hceg)
    (s174_ne_of_isCrossing hcfg) hcef hceg hX y hy

include hcef in
/-- adjacency of `c_out`, `z_out` on `h_out` -/
theorem s174_adj_out (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs') (y : Visit P)
    (hy : y.2.val = (G11_vge hceg).2.val) :
    ¬ (visitParameter (G11_vge hceg) < visitParameter y ∧
        visitParameter y < visitParameter (G11_vgf hcfg)) ∧
    ¬ (visitParameter (G11_vgf hcfg) < visitParameter y ∧
        visitParameter y < visitParameter (G11_vge hceg)) := by
  have hX' : ExactTriangleVisitOrders P P' h_out h_in h_s hs' :=
    gu2_exact_of_eq hs' s174_triple_perm_gef'.symm hX
  have h := G11_no_visit_between hs' (s174_ne_of_isCrossing hceg).symm
    (s174_ne_of_isCrossing hcfg).symm (s174_ne_of_isCrossing hcef)
    (gu2_isCrossing_comm hceg) (gu2_isCrossing_comm hcfg) hX' y hy
  have e1 : (⟨xPair (gu2_isCrossing_comm hceg), ⟨h_out, mem_pair_left _ _⟩⟩ : Visit P) =
      G11_vge hceg := gu2_visit_congr (gu2_xPair_comm hceg) _ _
  have e2 : (⟨xPair (gu2_isCrossing_comm hcfg), ⟨h_out, mem_pair_left _ _⟩⟩ : Visit P) =
      G11_vgf hcfg := gu2_visit_congr (gu2_xPair_comm hcfg) _ _
  rw [e1, e2] at h
  exact h

include hceg in
/-- adjacency of `y_s`, `z_s` on `h_s` -/
theorem s174_adj_s (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs') (y : Visit P)
    (hy : y.2.val = (G11_vfe hcef).2.val) :
    ¬ (visitParameter (G11_vfe hcef) < visitParameter y ∧
        visitParameter y < visitParameter (G11_vfg hcfg)) ∧
    ¬ (visitParameter (G11_vfg hcfg) < visitParameter y ∧
        visitParameter y < visitParameter (G11_vfe hcef)) := by
  have hX' : ExactTriangleVisitOrders P P' h_s h_in h_out hs' :=
    gu2_exact_of_eq hs' s174_triple_perm_feg'.symm hX
  have h := G11_no_visit_between hs' (s174_ne_of_isCrossing hcef).symm
    (s174_ne_of_isCrossing hcfg) (s174_ne_of_isCrossing hceg)
    (gu2_isCrossing_comm hcef) hcfg hX' y hy
  have e1 : (⟨xPair (gu2_isCrossing_comm hcef), ⟨h_s, mem_pair_left _ _⟩⟩ : Visit P) =
      G11_vfe hcef := gu2_visit_congr (gu2_xPair_comm hcef) _ _
  rw [e1] at h
  exact h

include hn hcfg in
/-- the marked-circle successor of `y_in` is `c_in` -/
theorem s174_markSucc_yin (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hord : visitParameter (G11_vef hcef) < visitParameter (G11_veg hceg)) :
    geoMarkSuccessor hG.cg (Sum.inr (G11_vef hcef)) = Sum.inr (G11_veg hceg) :=
  gu1_markSuccessor_eq_of_adjacent hn hG.cg rfl hord
    (fun y hy => (s174_adj_in hs' hcef hceg hcfg hX y hy).1)

include hn hcef in
theorem s174_markSucc_cout (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hord : visitParameter (G11_vge hceg) < visitParameter (G11_vgf hcfg)) :
    geoMarkSuccessor hG.cg (Sum.inr (G11_vge hceg)) = Sum.inr (G11_vgf hcfg) :=
  gu1_markSuccessor_eq_of_adjacent hn hG.cg rfl hord
    (fun y hy => (s174_adj_out hs' hcef hceg hcfg hX y hy).1)

include hn hcfg in
/-- `ρ_S y_in = c_in` -/
theorem s174_succ_yin (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hord : visitParameter (G11_vef hcef) < visitParameter (G11_veg hceg))
    (hy : xPair hcef ∈ geoCarrierCrossings hG.cg S q) :
    geoSmoothingSuccessor hG.cg S (Sum.inr (G11_vef hcef)) = Sum.inr (G11_veg hceg) := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hG.cg S _
    ((mem_geoCarrierCrossings hG.cg S q _).mp hy).1]
  exact s174_markSucc_yin hn hG hs' hcef hceg hcfg hX hord

include hn hcef in
/-- `ρ_S c_in = z_out` (the selected corner: leave along the twin's edge) -/
theorem s174_succ_cin (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hord : visitParameter (G11_vge hceg) < visitParameter (G11_vgf hcfg))
    (hcS : xPair hceg ∈ S) :
    geoSmoothingSuccessor hG.cg S (Sum.inr (G11_veg hceg)) = Sum.inr (G11_vgf hcfg) := by
  rw [geoSmoothingSuccessor_visit_of_mem hG.cg S _ hcS, gu2_visitTwin_veg]
  exact s174_markSucc_cout hn hG hs' hcef hceg hcfg hX hord

include hn hcef in
/-- the incoming visit of the corner is owned by `q` -/
theorem s174_owner_cin (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hord : visitParameter (G11_vge hceg) < visitParameter (G11_vgf hcfg))
    (hcS : xPair hceg ∈ S) (hz : xPair hcfg ∈ geoCarrierCrossings hG.cg S q) :
    geoOwner hG.cg S (Sum.inr (G11_veg hceg)) = q := by
  rw [← geoOwner_successor, s174_succ_cin hn hG hs' hcef hceg hcfg hX hord hcS]
  exact ((mem_geoCarrierCrossings hG.cg S q _).mp hz).2 _ rfl

/-- the corner index of the selected visit `c_in` on the carrier `q` -/
noncomputable def s174_k₀ (hown : geoOwner hG.cg S (Sum.inr (G11_veg hceg)) = q) (hcS : xPair hceg ∈ S) :
    ZMod (geoCornerCount hG.cg S q) :=
  Classical.choose (geoCornerMark_exists_of_owner hG.cg S q _ hown hcS)

theorem s174_k₀_spec (hown : geoOwner hG.cg S (Sum.inr (G11_veg hceg)) = q) (hcS : xPair hceg ∈ S) :
    geoCornerMark hG.cg S q (s174_k₀ hG hceg q hown hcS) = Sum.inr (G11_veg hceg) :=
  Classical.choose_spec (geoCornerMark_exists_of_owner hG.cg S q _ hown hcS)

/-- the corner point is the double point of `c` -/
theorem s174_cornerPolygon_k₀ (hown : geoOwner hG.cg S (Sum.inr (G11_veg hceg)) = q) (hcS : xPair hceg ∈ S) :
    geoCornerPolygon hG.cg S q (s174_k₀ hG hceg q hown hcS) = crossingPoint (xPair hceg) := by
  rw [geoCornerPolygon_apply, s174_k₀_spec, geoMarkPosition_evaluation_visit]
  rfl

include hn hcef in
/-- the carrier edge through `z_out` is the outgoing edge `k₀` of the corner -/
theorem s174_carrierEdge_zout (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hord : visitParameter (G11_vge hceg) < visitParameter (G11_vgf hcfg))
    (hcS : xPair hceg ∈ S) (hz : xPair hcfg ∈ geoCarrierCrossings hG.cg S q)
    (hown : geoOwner hG.cg S (Sum.inr (G11_veg hceg)) = q) :
    G11_carrierEdge hn hG hS q (G11_vgf hcfg) hz = s174_k₀ hG hceg q hown hcS := by
  obtain ⟨r, hr, hρ, hb, -, -⟩ := gu1_carrierEdge_block hn hG hS q (G11_vgf hcfg) hz
  have hsucc := s174_succ_cin hn hG hs' hcef hceg hcfg hX hord hcS
  have h1 : (geoSmoothingSuccessor hG.cg S ^ 1) (geoCornerMark hG.cg S q (s174_k₀ hG hceg q hown hcS)) =
      Sum.inr (G11_vgf hcfg) := by
    rw [pow_one, s174_k₀_spec]; exact hsucc
  have hb1 : GeoBlockInterior hG.cg S q (s174_k₀ hG hceg q hown hcS) 1 := by
    intro i hi1 hi
    have hi' : i = 1 := by omega
    subst hi'
    refine ⟨G11_vgf hcfg, h1, ((mem_geoCarrierCrossings hG.cg S q _).mp hz).1, ?_⟩
    rw [s174_k₀_spec, geoOutSlot_selected hG.cg S _ hcS, gu2_visitTwin_veg]
    rfl
  exact (geo_block_mark_eq hG.cg S q hb hb1 (hρ.trans h1.symm)).1

include hn hcfg in
/-- the carrier edge through `y_in` is the incoming edge `k₀ - 1` of the corner -/
theorem s174_carrierEdge_yin (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hord : visitParameter (G11_vef hcef) < visitParameter (G11_veg hceg))
    (hcS : xPair hceg ∈ S) (hy : xPair hcef ∈ geoCarrierCrossings hG.cg S q)
    (hown : geoOwner hG.cg S (Sum.inr (G11_veg hceg)) = q) :
    G11_carrierEdge hn hG hS q (G11_vef hcef) hy + 1 = s174_k₀ hG hceg q hown hcS := by
  obtain ⟨r, hr, hρ, hb, -, -⟩ := gu1_carrierEdge_block hn hG hS q (G11_vef hcef) hy
  have hsucc := s174_succ_yin hn hG hs' hcef hceg hcfg q hX hord hy
  set j := G11_carrierEdge hn hG hS q (G11_vef hcef) hy with hj
  obtain ⟨m, hm, hchain, hmid, -, -, -, -, -⟩ := geoCornerPolygon_block hn hG.cg hS q j
  have hρ1 : (geoSmoothingSuccessor hG.cg S ^ (r + 1)) (geoCornerMark hG.cg S q j) =
      Sum.inr (G11_veg hceg) := by
    rw [pow_succ', Equiv.Perm.mul_apply, hρ]; exact hsucc
  have hm_eq : m = r + 1 := by
    rcases lt_trichotomy m (r + 1) with hlt | heq | hgt
    · exfalso
      have hnc := hb.not_trueCorner hG.cg S q m hm (by omega)
      rw [hchain] at hnc
      exact hnc (isTrueCorner_geoCornerMark hG.cg S q (j + 1))
    · exact heq
    · exfalso
      obtain ⟨v, hv, hvS, -⟩ := hmid (r + 1) (by omega) hgt
      rw [hρ1] at hv
      have hv' : G11_veg hceg = v := Sum.inr.inj hv
      apply hvS
      rw [← hv']
      exact hcS
  rw [hm_eq, hρ1] at hchain
  exact geoCornerMark_injective hG.cg S q (hchain.symm.trans (s174_k₀_spec hG hceg q hown hcS).symm)


/-! ### The shadow crossings of the carrier lift at the two retained crossings -/

/-- the crossing of the carrier shadow sitting at a retained crossing `c` of the carrier -/
noncomputable def s174_lift (c : Crossing P) (hc : c ∈ geoCarrierCrossings hG.cg S q) :
    (geoCarrierShadow hn hG hS q).Crossing :=
  (geoCarrierCrossingEquiv hn hG hS q).symm ⟨c, hc⟩

theorem s174_lift_congr {c c' : Crossing P} (h : c = c') (hc : c ∈ geoCarrierCrossings hG.cg S q)
    (hc' : c' ∈ geoCarrierCrossings hG.cg S q) :
    s174_lift hn hG hS q c hc = s174_lift hn hG hS q c' hc' := by
  subst h; rfl

theorem s174_lift_crossingPoint (c : Crossing P) (hc : c ∈ geoCarrierCrossings hG.cg S q) :
    (geoCarrierShadow hn hG hS q).crossingPoint (s174_lift hn hG hS q c hc) = crossingPoint c := by
  have h := crossingPoint_geoCarrierCrossingEquiv hn hG hS q (s174_lift hn hG hS q c hc)
  rw [s174_lift, Equiv.apply_symm_apply] at h
  exact h.symm

theorem s174_lift_injective_pt {c c' : Crossing P} (hc : c ∈ geoCarrierCrossings hG.cg S q)
    (hc' : c' ∈ geoCarrierCrossings hG.cg S q) (hne : c ≠ c') :
    s174_lift hn hG hS q c hc ≠ s174_lift hn hG hS q c' hc' := by
  intro h
  apply hne
  have := congrArg (geoCarrierShadow hn hG hS q).crossingPoint h
  rw [s174_lift_crossingPoint, s174_lift_crossingPoint] at this
  exact crossingPoint_injective_of_geometry hG.cg this

/-- the strands of the lifted crossing are the two carrier edges of the visits of `v.1` -/
theorem s174_lift_val (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg S q)
    (hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg S q) :
    (s174_lift hn hG hS q v.1 hv).val =
      {(⟨0, G11_carrierEdge hn hG hS q v hv⟩ : (geoCarrierShadow hn hG hS q).Strand),
       ⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩} := by
  set Γ := geoCarrierShadow hn hG hS q with hΓ
  have hna : ¬ Γ.Adjacent ⟨0, G11_carrierEdge hn hG hS q v hv⟩
      ⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ := by
    rw [Shadow.single_adjacent_iff]
    exact gu1_carrierEdge_remote hn hG hS q v hv hv'
  have hmem1 : crossingPoint v.1 ∈ Γ.seg ⟨0, G11_carrierEdge hn hG hS q v hv⟩ :=
    (G11_carrierEdge_spec hn hG hS q v hv).1
  have hmem2 : crossingPoint v.1 ∈ Γ.seg ⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ := by
    have := (G11_carrierEdge_spec hn hG hS q (visitTwin v) hv').1
    rw [visitTwin_crossing] at this
    exact this
  let y₀ : Γ.Crossing := ⟨_, Γ.isCrossing_pair hna ⟨crossingPoint v.1, hmem1, hmem2⟩⟩
  have hpt : Γ.crossingPoint y₀ = crossingPoint v.1 := by
    symm
    apply (geoCarrierShadow_generic hn hG hS q).common_point_unique
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hmem1
    · rw [Finset.mem_singleton.mp hs]; exact hmem2
  have heq : s174_lift hn hG hS q v.1 hv = y₀ := by
    apply (geoCarrierShadow_generic hn hG hS q).crossingPoint_injective
    rw [s174_lift_crossingPoint, hpt]
  rw [heq]

/-! ### `k ≥ 4` -/

theorem s174_adjacent_zmod3 (i j : ZMod 3) : adjacent i j := by
  unfold adjacent
  have hv : ((j - i).val : ZMod 3) = j - i := ZMod.natCast_zmod_val (j - i)
  have hlt : (j - i).val < 3 := ZMod.val_lt (j - i)
  rw [← hv]
  generalize (j - i).val = d at hlt
  interval_cases d
  · right; left; rfl
  · right; right; rfl
  · left; decide

theorem s174_four_le {k : ℕ} (hk : 3 ≤ k) (h : ∃ i j : ZMod k, ¬ adjacent i j) : 4 ≤ k := by
  by_contra hlt
  have h3 : k = 3 := by omega
  subst h3
  obtain ⟨i, j, hij⟩ := h
  exact hij (s174_adjacent_zmod3 i j)

include hn hS in
theorem s174_four_le_cornerCount (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg S q)
    (hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg S q) :
    4 ≤ geoCornerCount hG.cg S q :=
  s174_four_le (three_le_geoCornerCount hn hG hS q)
    ⟨_, _, gu1_carrierEdge_remote hn hG hS q v hv hv'⟩

/-! ### sign helpers -/

omit [NeZero n] in
theorem s174_pos_iff_of_sign_eq {a b : ℝ} (h : SignType.sign a = SignType.sign b) :
    0 < a ↔ 0 < b := by
  rw [← sign_eq_one_iff, ← sign_eq_one_iff, h]

omit [NeZero n] in
theorem s174_det_ne_zero_of_isCrossing (hP : CrossingGeometry P) {i j : ZMod n}
    (h : IsCrossing P {i, j}) : det (edge P i) (edge P j) ≠ 0 :=
  (hP.2.1 i j (gu2_remote_of_isCrossing h) _ (crossingPoint_mem (xPair h) i (mem_pair_left i j))
    (crossingPoint_mem (xPair h) j (mem_pair_right i j))).2.2

omit [NeZero n] in
theorem s174_det_smul_pos_iff {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (u v : Plane) :
    0 < det (c • u) (d • v) ↔ 0 < det u v := by
  rw [gu2_det_smul_smul]
  exact ⟨fun h => pos_of_mul_pos_right h (mul_pos hc hd).le,
    fun h => mul_pos (mul_pos hc hd) h⟩


/-! ### the over strands of the positive lift at the two bigon crossings -/

include hn hS in
/-- at a lifted crossing `⟨0, j⟩, ⟨0, j'⟩` of the positive lift, the strand `⟨0, j'⟩` is over iff
`det (edge P e') (edge P e) > 0` for the original edges `e, e'` of the two visits -/
theorem s174_pos_over_lift_iff (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg S q)
    (hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg S q) :
    (geoPositiveLift hn hG hS q).overStrand (s174_lift hn hG hS q v.1 hv) =
        (⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
      0 < det (edge P (visitTwin v).2.val) (edge P v.2.val) := by
  have hval := s174_lift_val hn hG hS q v hv hv'
  rw [Finset.pair_comm] at hval
  have hne : (⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ : (geoCarrierShadow hn hG hS q).Strand) ≠
      ⟨0, G11_carrierEdge hn hG hS q v hv⟩ :=
    (geoCarrierShadow hn hG hS q).ne_of_not_adjacent
      (fun h => gu1_carrierEdge_remote hn hG hS q v hv hv'
        ((Shadow.single_adjacent_iff _ _ _).mp (Shadow.Adjacent.symm _ h)))
  refine (s174_pos_over_iff (geoCarrierShadow_generic hn hG hS q) _ hval hne).trans ?_
  obtain ⟨-, c, hc, he⟩ := G11_carrierEdge_spec hn hG hS q v hv
  obtain ⟨-, c', hc', he'⟩ := G11_carrierEdge_spec hn hG hS q (visitTwin v) hv'
  show 0 < det (edge (geoCornerPolygon hG.cg S q) _) (edge (geoCornerPolygon hG.cg S q) _) ↔ _
  rw [he, he']
  exact s174_det_smul_pos_iff hc' hc _ _


omit [NeZero n] in
theorem s174_not_pos_iff {a : ℝ} (ha : a ≠ 0) : ¬ 0 < a ↔ 0 < -a := by
  rw [not_lt, neg_pos]
  exact ⟨fun h => lt_of_le_of_ne h ha, le_of_lt⟩

omit [NeZero n] in
theorem s174_neg_pos_iff_of_sign_eq {a b : ℝ} (h : SignType.sign a = SignType.sign b) :
    0 < -a ↔ 0 < -b := by
  rw [neg_pos, neg_pos, ← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, h]

omit [NeZero n] in
/-- the over strand is the second strand iff it is not the first -/
theorem s174_over_other_iff (D : Diagram) (x : D.Γ.Crossing) {s t : D.Γ.Strand}
    (hx : x.val = {s, t}) (hst : s ≠ t) : D.overStrand x = t ↔ D.overStrand x ≠ s := by
  have hmem : D.overStrand x ∈ ({s, t} : Finset D.Γ.Strand) := by rw [← hx]; exact D.over_mem x
  constructor
  · intro h heq; exact hst (heq.symm.trans h)
  · intro h
    rcases Finset.mem_insert.mp hmem with h' | h'
    · exact absurd h' h
    · exact Finset.mem_singleton.mp h'

/-! ### the closed contact triangle and its clearance -/

/-- the closed contact triangle `conv{y, c, z}` -/
abbrev s174_K : Set Plane :=
  convexHull ℝ {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)}

include hs' in
/-- a corner of the carrier polygon inside the closed triangle is the corner `c` itself -/
theorem s174_corner_mem_K (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hK_sel : ∀ c' ∈ S, c' ≠ xPair hceg → ∃ h ∈ c'.val, h ≠ h_in ∧ h ≠ h_s ∧ h ≠ h_out)
    (i : ZMod (geoCornerCount hG.cg S q))
    (hi : geoCornerPolygon hG.cg S q i ∈ s174_K hcef hceg hcfg) :
    geoCornerPolygon hG.cg S q i = crossingPoint (xPair hceg) := by
  have hcl := gu2_clear hG hs' (s174_ne_of_isCrossing hcef) (s174_ne_of_isCrossing hceg)
    (s174_ne_of_isCrossing hcfg) hcef hceg hcfg hX
  have hcorner := isTrueCorner_geoCornerMark hG.cg S q i
  rw [geoCornerPolygon_apply] at hi ⊢
  rcases hmark : geoCornerMark hG.cg S q i with j | v
  · rw [hmark, geoMarkPosition_evaluation_vertex] at hi
    exact absurd hi (hcl.2 j)
  · rw [hmark] at hi hcorner
    rw [geoMarkPosition_evaluation_visit] at hi ⊢
    have hvS : v.1 ∈ S := hcorner
    by_cases hvc : v.1 = xPair hceg
    · rw [hvc]
    · exfalso
      obtain ⟨h, hh, h1, h2, h3⟩ := hK_sel v.1 hvS hvc
      exact gu2_clear_closed hG hs' (s174_ne_of_isCrossing hcef) (s174_ne_of_isCrossing hceg)
        (s174_ne_of_isCrossing hcfg) hcef hceg hcfg hX h h1 h2 h3 _ (crossingPoint_mem v.1 h hh) hi

include hn hs' in
/-- **clearance**: every edge of the carrier polygon other than the three local ones misses the
closed contact triangle -/
theorem s174_clear (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hcS : xPair hceg ∈ S) (hy : xPair hcef ∈ geoCarrierCrossings hG.cg S q)
    (hz : xPair hcfg ∈ geoCarrierCrossings hG.cg S q)
    (hown : geoOwner hG.cg S (Sum.inr (G11_veg hceg)) = q)
    (hK_sel : ∀ c' ∈ S, c' ≠ xPair hceg → ∃ h ∈ c'.val, h ≠ h_in ∧ h ≠ h_s ∧ h ≠ h_out)
    (hjy : G11_carrierEdge hn hG hS q (G11_vef hcef) hy + 1 = s174_k₀ hG hceg q hown hcS)
    (hjz : G11_carrierEdge hn hG hS q (G11_vgf hcfg) hz = s174_k₀ hG hceg q hown hcS)
    (hjs : G11_carrierEdge hn hG hS q (G11_vfg hcfg) hz = G11_carrierEdge hn hG hS q (G11_vfe hcef) hy)
    (h : ZMod (geoCornerCount hG.cg S q))
    (h1 : h ≠ G11_carrierEdge hn hG hS q (G11_vef hcef) hy)
    (h2 : h ≠ s174_k₀ hG hceg q hown hcS)
    (h3 : h ≠ G11_carrierEdge hn hG hS q (G11_vfe hcef) hy) :
    Disjoint (edgeSegment (geoCornerPolygon hG.cg S q) h) (s174_K hcef hceg hcfg) := by
  rw [Set.disjoint_left]
  intro x hx hxK
  have hx₀ := gu2_edgeSegment_sub hn hG hS q h hx
  obtain ⟨c₀, hc₀, hedge₀⟩ := geoCornerPolygon_edge_smul hn hG.cg hS q h
  have hcpt : geoCornerPolygon hG.cg S q (s174_k₀ hG hceg q hown hcS) = crossingPoint (xPair hceg) :=
    s174_cornerPolygon_k₀ hG hceg q hown hcS
  have hjy' : G11_carrierEdge hn hG hS q (G11_vef hcef) hy = s174_k₀ hG hceg q hown hcS - 1 :=
    eq_sub_of_add_eq hjy
  -- a corner point of the triangle on the edge `h` is impossible
  have hcorner_case : ∀ i, x = geoCornerPolygon hG.cg S q i → False := by
    intro i hi
    have hi' := s174_corner_mem_K hG hs' hcef hceg hcfg q hX hK_sel i (hi ▸ hxK)
    have hmem : geoCornerPolygon hG.cg S q (s174_k₀ hG hceg q hown hcS) ∈
        edgeSegment (geoCornerPolygon hG.cg S q) h := by
      rw [hcpt, ← hi', ← hi]; exact hx
    refine geoCornerPolygon_tail_off hn hG hS q _ h ?_ hmem
    rintro (hh | hh)
    · exact h1 (hh.trans hjy'.symm)
    · exact h2 hh
  by_cases hhe : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = h_in
  · rw [hhe] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_e_mem_segment hG hcef hceg hcfg hxK hxt
    obtain ⟨hA, c, hc, hedge⟩ := G11_carrierEdge_spec hn hG hS q (G11_vef hcef) hy
    have hB : crossingPoint (xPair hceg) ∈
        edgeSegment (geoCornerPolygon hG.cg S q) (G11_carrierEdge hn hG hS q (G11_vef hcef) hy) := by
      rw [← hcpt, ← hjy]
      exact ⟨1, zero_le_one, le_rfl, (edgePoint_one _ _).symm⟩
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hS q h1 hedge₀ hedge hx
      (gu2_edgeSegment_convex hA hB hseg)
    exact hcorner_case i hi
  by_cases hhf : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = h_s
  · rw [hhf] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_f_mem_segment hG hcef hceg hcfg hxK hxt
    obtain ⟨hA, c, hc, hedge⟩ := G11_carrierEdge_spec hn hG hS q (G11_vfe hcef) hy
    have hC : crossingPoint (xPair hcfg) ∈
        edgeSegment (geoCornerPolygon hG.cg S q) (G11_carrierEdge hn hG hS q (G11_vfe hcef) hy) := by
      rw [← hjs]
      exact (G11_carrierEdge_spec hn hG hS q (G11_vfg hcfg) hz).1
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hS q h3 hedge₀ hedge hx
      (gu2_edgeSegment_convex hA hC hseg)
    exact hcorner_case i hi
  by_cases hhg : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = h_out
  · rw [hhg] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_g_mem_segment hG hcef hceg hcfg hxK hxt
    obtain ⟨hC, c, hc, hedge⟩ := G11_carrierEdge_spec hn hG hS q (G11_vgf hcfg) hz
    rw [hjz] at hC hedge
    have hB : crossingPoint (xPair hceg) ∈
        edgeSegment (geoCornerPolygon hG.cg S q) (s174_k₀ hG hceg q hown hcS) := by
      rw [← hcpt]
      exact ⟨0, le_rfl, zero_le_one, (edgePoint_zero _ _).symm⟩
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hS q h2 hedge₀ hedge hx
      (gu2_edgeSegment_convex hB hC hseg)
    exact hcorner_case i hi
  exact gu2_clear_closed hG hs' (s174_ne_of_isCrossing hcef) (s174_ne_of_isCrossing hceg)
    (s174_ne_of_isCrossing hcfg) hcef hceg hcfg hX _ hhe hhf hhg x hx₀ hxK



omit [NeZero n] in
/-- two strands of a one-component shadow with non-adjacent labels are distinct -/
theorem s174_strand_ne_of_not_adjacent {C : PolyComp} {j j' : ZMod C.k} (h : ¬ adjacent j j') :
    (⟨0, j⟩ : (Shadow.single C).Strand) ≠ ⟨0, j'⟩ := by
  intro heq
  apply h
  have hjj : j = j' := eq_of_heq (Sigma.mk.inj heq).2
  rw [hjj]
  exact Or.inr (Or.inl (sub_self _))

include hn hs' in
/-- **The core site theorem (row 174 / 176 shape).**  On the positive lift `D₀ = geoPositiveLift` of a
carrier `q` of an independent support `S` whose corner polygon passes through the selected crossing
`c = x_{in,out}` (entering along `h_in`, leaving along `h_out`) with the retained crossings
`y = x_{in,s}` just before the corner on `h_in` and `z = x_{s,out}` just after it on `h_out`, and the
canonical sign condition, the switch of `D₀` at `y` or at `z` carries a `BigonData` whose bigon is
`{y, z}` with `K` the closed contact triangle `conv{y, c, z}`.  Inputs: the R-LOC-2 adjacency in the
form `ExactTriangleVisitOrders` (A7), the ownership of `y, z` by `q`, and the clearance of the
triangle from the other selected crossings (`hK_sel`: every other selected crossing has an edge
outside `{h_in, h_s, h_out}`; the vertices and the other edges of `P` are cleared by G11's A8
`gu2_clear_closed`). -/
theorem s174_core (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hcS : xPair hceg ∈ S) (hy : xPair hcef ∈ geoCarrierCrossings hG.cg S q)
    (hz : xPair hcfg ∈ geoCarrierCrossings hG.cg S q)
    (hK_sel : ∀ c' ∈ S, c' ≠ xPair hceg → ∃ h ∈ c'.val, h ≠ h_in ∧ h ≠ h_s ∧ h ≠ h_out)
    (hord_in : visitParameter (G11_vef hcef) < visitParameter (G11_veg hceg))
    (hord_out : visitParameter (G11_vge hceg) < visitParameter (G11_vgf hcfg))
    (hsgn : crossingSign P h_in h_s = crossingSign P h_s h_out)
    (xs : (geoCarrierShadow hn hG hS q).Crossing)
    (hxs : xs = s174_lift hn hG hS q _ hy ∨ xs = s174_lift hn hG hS q _ hz) :
    ∃ B : BigonData ((geoPositiveLift hn hG hS q).switch xs),
      B.i = ⟨0, Nat.one_pos⟩ ∧ B.y = s174_lift hn hG hS q _ hy ∧ B.z = s174_lift hn hG hS q _ hz := by
  -- the corner and the three carrier edges
  have hown := s174_owner_cin hn hG hs' hcef hceg hcfg q hX hord_out hcS hz
  have hjy := s174_carrierEdge_yin hn hG hs' hcef hceg hcfg hS q hX hord_in hcS hy hown
  have hjz := s174_carrierEdge_zout hn hG hs' hcef hceg hcfg hS q hX hord_out hcS hz hown
  have hjs : G11_carrierEdge hn hG hS q (G11_vfg hcfg) hz =
      G11_carrierEdge hn hG hS q (G11_vfe hcef) hy :=
    G11_carrierEdge_eq_of_adjacent hn hG hS q hz hy rfl
      (fun y hy' => (s174_adj_s hs' hcef hceg hcfg hX y hy').symm)
  have hcpt := s174_cornerPolygon_k₀ hG hceg q hown hcS
  set k₀ := s174_k₀ hG hceg q hown hcS with hk₀
  set jy := G11_carrierEdge hn hG hS q (G11_vef hcef) hy with hjy_def
  set js := G11_carrierEdge hn hG hS q (G11_vfe hcef) hy with hjs_def
  set ys := s174_lift hn hG hS q _ hy with hys
  set zs := s174_lift hn hG hS q _ hz with hzs
  have htwz : visitTwin (G11_vgf hcfg) = G11_vfg hcfg :=
    SEL_visitTwin_visitOn (mem_pair_left h_s h_out) (mem_pair_right h_s h_out)
      (s174_ne_of_isCrossing hcfg)
  -- the strands of the two lifted crossings
  have hyv : ys.val = {(⟨0, jy⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, js⟩} := by
    have h := s174_lift_val hn hG hS q (G11_vef hcef) hy hy
    rw [gu2_carrierEdge_congr hn hG hS q (gu2_visitTwin_vef hcef) hy hy] at h
    exact h
  have hzv : zs.val = {(⟨0, k₀⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, js⟩} := by
    have h := s174_lift_val hn hG hS q (G11_vgf hcfg) hz hz
    rw [gu2_carrierEdge_congr hn hG hS q htwz hz hz, hjs, hjz] at h
    exact h
  have hna_y : ¬ adjacent jy js := by
    have h := gu1_carrierEdge_remote hn hG hS q (G11_vef hcef) hy hy
    rw [gu2_carrierEdge_congr hn hG hS q (gu2_visitTwin_vef hcef) hy hy] at h
    exact h
  have hna_z : ¬ adjacent k₀ js := by
    have h := gu1_carrierEdge_remote hn hG hS q (G11_vgf hcfg) hz hz
    rw [gu2_carrierEdge_congr hn hG hS q htwz hz hz, hjs, hjz] at h
    exact h
  have hne_y : (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ≠ ⟨0, jy⟩ :=
    s174_strand_ne_of_not_adjacent (fun h => hna_y (by
      rcases h with h | h | h
      · exact Or.inr (Or.inr (by linear_combination -h))
      · exact Or.inr (Or.inl (by linear_combination -h))
      · exact Or.inl (by linear_combination -h)))
  have hne_z : (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ≠ ⟨0, k₀⟩ :=
    s174_strand_ne_of_not_adjacent (fun h => hna_z (by
      rcases h with h | h | h
      · exact Or.inr (Or.inr (by linear_combination -h))
      · exact Or.inr (Or.inl (by linear_combination -h))
      · exact Or.inl (by linear_combination -h)))
  have hyv' : ys.val = {(⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, jy⟩} := by rw [hyv, Finset.pair_comm]
  have hzv' : zs.val = {(⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, k₀⟩} := by rw [hzv, Finset.pair_comm]
  -- the two crossings are distinct
  have hyz_c : xPair hcef ≠ xPair hcfg := by
    intro h
    have hmem : h_in ∈ (xPair hcfg).val := by rw [← h]; exact mem_pair_left _ _
    rcases Finset.mem_insert.mp hmem with h' | h'
    · exact s174_ne_of_isCrossing hcef h'
    · exact s174_ne_of_isCrossing hceg (Finset.mem_singleton.mp h')
  have hyz : ys ≠ zs := s174_lift_injective_pt hn hG hS q hy hz hyz_c
  -- the over strands of the positive lift at `y` and `z`
  have hA := s174_det_ne_zero_of_isCrossing hG.cg hcef
  have hB := s174_det_ne_zero_of_isCrossing hG.cg hcfg
  have hoy : (geoPositiveLift hn hG hS q).overStrand ys = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
      0 < -det (edge P h_in) (edge P h_s) := by
    have h := s174_pos_over_lift_iff hn hG hS q (G11_vef hcef) hy hy
    rw [gu2_carrierEdge_congr hn hG hS q (gu2_visitTwin_vef hcef) hy hy, gu2_visitTwin_vef,
      det_swap] at h
    exact h
  have hoz : (geoPositiveLift hn hG hS q).overStrand zs = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
      0 < det (edge P h_s) (edge P h_out) := by
    have h := s174_pos_over_lift_iff hn hG hS q (G11_vgf hcfg) hz hz
    rw [gu2_carrierEdge_congr hn hG hS q htwz hz hz, hjs, htwz] at h
    exact h
  have hsign : (0 < det (edge P h_in) (edge P h_s) ↔ 0 < det (edge P h_s) (edge P h_out)) :=
    s174_pos_iff_of_sign_eq hsgn
  have hsign' : (0 < -det (edge P h_in) (edge P h_s) ↔ 0 < -det (edge P h_s) (edge P h_out)) :=
    s174_neg_pos_iff_of_sign_eq hsgn
  -- `same_over` on the switched diagram
  have hsame : (((geoPositiveLift hn hG hS q).switch xs).overStrand ys = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ∧
        ((geoPositiveLift hn hG hS q).switch xs).overStrand zs = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand)) ∨
      (((geoPositiveLift hn hG hS q).switch xs).overStrand ys ≠ (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ∧
        ((geoPositiveLift hn hG hS q).switch xs).overStrand zs ≠ (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand)) := by
    rcases hxs with rfl | rfl
    · -- the switch is at `y`
      have e1 : ((geoPositiveLift hn hG hS q).switch ys).overStrand ys = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
          0 < det (edge P h_in) (edge P h_s) := by
        refine (s174_switch_over_self_iff (geoPositiveLift hn hG hS q) ys hyv' hne_y).trans ?_
        refine (s174_over_other_iff (geoPositiveLift hn hG hS q) ys hyv' hne_y).trans ?_
        refine (not_congr hoy).trans ?_
        rw [s174_not_pos_iff (neg_ne_zero.mpr hA), neg_neg]
      have e2 : ((geoPositiveLift hn hG hS q).switch ys).overStrand zs = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
          0 < det (edge P h_s) (edge P h_out) := by
        have h := Diagram.switch_overStrand_of_ne (geoPositiveLift hn hG hS q) hyz.symm
        rw [h]
        exact hoz
      by_cases hp : 0 < det (edge P h_in) (edge P h_s)
      · exact Or.inl ⟨e1.mpr hp, e2.mpr (hsign.mp hp)⟩
      · exact Or.inr ⟨fun h => hp (e1.mp h), fun h => hp (hsign.mpr (e2.mp h))⟩
    · -- the switch is at `z`
      have e1 : ((geoPositiveLift hn hG hS q).switch zs).overStrand ys = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
          0 < -det (edge P h_in) (edge P h_s) := by
        have h := Diagram.switch_overStrand_of_ne (geoPositiveLift hn hG hS q) hyz
        rw [h]
        exact hoy
      have e2 : ((geoPositiveLift hn hG hS q).switch zs).overStrand zs = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
          0 < -det (edge P h_s) (edge P h_out) := by
        refine (s174_switch_over_self_iff (geoPositiveLift hn hG hS q) zs hzv' hne_z).trans ?_
        refine (s174_over_other_iff (geoPositiveLift hn hG hS q) zs hzv' hne_z).trans ?_
        exact (not_congr hoz).trans (s174_not_pos_iff hB)
      by_cases hp : 0 < -det (edge P h_in) (edge P h_s)
      · exact Or.inl ⟨e1.mpr hp, e2.mpr (hsign'.mp hp)⟩
      · exact Or.inr ⟨fun h => hp (e1.mp h), fun h => hp (hsign'.mpr (e2.mp h))⟩
  -- clearance
  have hclear : ∀ u : (geoCarrierShadow hn hG hS q).Strand, u ≠ ⟨0, jy⟩ → u ≠ ⟨0, jy + 1⟩ → u ≠ ⟨0, js⟩ →
      Disjoint ((geoCarrierShadow hn hG hS q).seg u) (s174_K hcef hceg hcfg) := by
    rintro ⟨i₀, h⟩ h1 h2 h3
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    have h1' : h ≠ jy := fun hh => h1 (by rw [hh])
    have h2' : h ≠ k₀ := fun hh => h2 (by rw [hh, ← hjy])
    have h3' : h ≠ js := fun hh => h3 (by rw [hh])
    exact s174_clear hn hG hs' hcef hceg hcfg hS q hX hcS hy hz hown hK_sel hjy hjz hjs h h1' h2' h3'
  have hk : 4 ≤ geoCornerCount hG.cg S q := s174_four_le_cornerCount hn hG hS q (G11_vef hcef) hy hy
  have hpy : (geoCarrierShadow hn hG hS q).crossingPoint ys = crossingPoint (xPair hcef) :=
    s174_lift_crossingPoint hn hG hS q _ hy
  have hpz : (geoCarrierShadow hn hG hS q).crossingPoint zs = crossingPoint (xPair hcfg) :=
    s174_lift_crossingPoint hn hG hS q _ hz
  have hK : convexHull ℝ {(geoCarrierShadow hn hG hS q).crossingPoint ys, geoCornerPolygon hG.cg S q (jy + 1),
      (geoCarrierShadow hn hG hS q).crossingPoint zs} = s174_K hcef hceg hcfg := by
    rw [hpy, hpz, hjy, hcpt]
  rw [← hjy] at hzv
  -- the triangle builder
  obtain ⟨B, hBi, hBy, hBz⟩ := exists_bigonData_of_triangle ((geoPositiveLift hn hG hS q).switch xs)
    ⟨0, Nat.one_pos⟩ jy hk (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ys zs hyv hzv hsame (by
      intro u h1 h2 h3
      have hK' : convexHull ℝ {((geoPositiveLift hn hG hS q).switch xs).Γ.crossingPoint ys,
          (((geoPositiveLift hn hG hS q).switch xs).Γ.comp ⟨0, Nat.one_pos⟩).P
            ((jy + 1 : ZMod (geoCornerCount hG.cg S q))),
          ((geoPositiveLift hn hG hS q).switch xs).Γ.crossingPoint zs} = s174_K hcef hceg hcfg := by
        rw [← hK]; rfl
      exact (hclear u h1 h2 h3).mono_right (le_of_eq hK'))
  exact ⟨B, hBi, hBy, hBz⟩


end S174Core

/-! ### The `GT_Endpoint` wrapper: the traversal order at the `m`-corner from the sign condition -/

section S174Site

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n}

omit [NeZero n] in
/-- the real-arithmetic core of the order lemma: from `a B = r C`, `r A = -(b B)` with `A, C` of one
sign and `B ≠ 0`, the numbers `a, b` (both nonzero) have opposite signs -/
theorem s174_order_alg {A B C a b r : ℝ} (hB : B ≠ 0) (hAC : 0 < A * C) (ha : a ≠ 0)
    (I1 : a * B = r * C) (I2 : r * A = -(b * B)) : 0 < a ↔ b < 0 := by
  have key : a * A + b * C = 0 := by
    have h3 : B * (a * A + b * C) = 0 := by linear_combination A * I1 + C * I2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hB
    · exact h
  have hC : C ≠ 0 := right_ne_zero_of_mul hAC.ne'
  have hab : a * b < 0 := by
    have h4 : a * b * C ^ 2 = -(a ^ 2 * (A * C)) := by linear_combination (a * C) * key
    have h5 : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha))
    have h6 : 0 < a ^ 2 * (A * C) := mul_pos h5 hAC
    have h7 : 0 < C ^ 2 := lt_of_le_of_ne (sq_nonneg C) (Ne.symm (pow_ne_zero 2 hC))
    by_contra hcon
    have h8 : 0 ≤ a * b := not_lt.mp hcon
    nlinarith
  rcases mul_neg_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · exact ⟨fun h => absurd h (not_lt.mpr h1.le), fun h => absurd h (not_lt.mpr h2.le)⟩

omit [NeZero n] in
theorem s174_mul_pos_of_sign_eq {a b : ℝ} (ha : a ≠ 0) (h : SignType.sign a = SignType.sign b) :
    0 < a * b := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hb : b < 0 := sign_eq_neg_one_iff.mp (h.symm.trans (sign_eq_neg_one_iff.mpr hneg))
    exact mul_pos_of_neg_of_neg hneg hb
  · have hb : 0 < b := sign_eq_one_iff.mp (h.symm.trans (sign_eq_one_iff.mpr hpos))
    exact mul_pos hpos hb

omit [NeZero n] in
theorem s174_param_congr {c c' : Crossing P} (h : c = c') {i : ZMod n} (hi : i ∈ c.val)
    (hi' : i ∈ c'.val) : crossingParameter c i hi = crossingParameter c' i hi' := by
  subst h; rfl

omit [NeZero n] in
/-- distinct crossings on one edge have distinct parameters (tier 0) -/
theorem s174_param_ne (hP : CrossingGeometry P) {ℓ : ZMod n} {c c' : Crossing P} (hne : c ≠ c')
    (hℓ : ℓ ∈ c.val) (hℓ' : ℓ ∈ c'.val) : crossingParameter c ℓ hℓ ≠ crossingParameter c' ℓ hℓ' := by
  intro h
  apply hne
  apply crossingPoint_injective_of_geometry hP
  rw [gu2_xpt c ℓ hℓ, gu2_xpt c' ℓ hℓ', h]

omit [NeZero n] in
theorem s174_xPair_ne_of_mem {a b b' : ZMod n} (h : IsCrossing P {a, b}) (h' : IsCrossing P {a, b'})
    (hbb : b ≠ b') : xPair h ≠ xPair h' := by
  intro heq
  have hmem : b ∈ (xPair h').val := by rw [← heq]; exact mem_pair_right _ _
  rcases Finset.mem_insert.mp hmem with h1 | h1
  · exact s174_ne_of_isCrossing h h1.symm
  · exact hbb (Finset.mem_singleton.mp h1)

omit [NeZero n] in
/-- **The order at the corner from the canonical sign condition.**  With `x' = x_{ℓ₁ℓ₂}`, `m' = x_{ℓ₁ℓ₃}`,
`w' = x_{ℓ₂ℓ₃}` and `sgn det(u₁,u₂) = sgn det(u₁,u₃) = sgn det(u₂,u₃)`: `m'` precedes `x'` on `ℓ₁` iff
`w'` precedes `m'` on `ℓ₃` (the corner polygon enters `m'` along `ℓ₃` and leaves along `ℓ₁`, or the
reverse). -/
theorem s174_order (hP : CrossingGeometry P) {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
    (hc12 : IsCrossing P {ℓ₁, ℓ₂}) (hc13 : IsCrossing P {ℓ₁, ℓ₃}) (hc23 : IsCrossing P {ℓ₂, ℓ₃})
    (hs12 : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hs23 : crossingSign P ℓ₂ ℓ₃ = crossingSign P ℓ₁ ℓ₃) :
    (crossingParameter (xPair hc13) ℓ₁ (mem_pair_left _ _) <
        crossingParameter (xPair hc12) ℓ₁ (mem_pair_left _ _) ↔
      crossingParameter (xPair hc23) ℓ₃ (mem_pair_right _ _) <
        crossingParameter (xPair hc13) ℓ₃ (mem_pair_right _ _)) := by
  have hne12 : xPair hc12 ≠ xPair hc13 :=
    s174_xPair_ne_of_mem hc12 hc13 (s174_ne_of_isCrossing hc23)
  have ha := sub_ne_zero.mpr (s174_param_ne hP hne12 (mem_pair_left ℓ₁ ℓ₂) (mem_pair_left ℓ₁ ℓ₃))
  have hA := s174_det_ne_zero_of_isCrossing hP hc12
  have hB := s174_det_ne_zero_of_isCrossing hP hc13
  have hAC : 0 < det (edge P ℓ₁) (edge P ℓ₂) * det (edge P ℓ₂) (edge P ℓ₃) :=
    s174_mul_pos_of_sign_eq hA (hs12.trans hs23.symm)
  have ex1 := gu2_xpt (xPair hc12) ℓ₁ (mem_pair_left _ _)
  have ex2 := gu2_xpt (xPair hc12) ℓ₂ (mem_pair_right _ _)
  have em1 := gu2_xpt (xPair hc13) ℓ₁ (mem_pair_left _ _)
  have em3 := gu2_xpt (xPair hc13) ℓ₃ (mem_pair_right _ _)
  have ew2 := gu2_xpt (xPair hc23) ℓ₂ (mem_pair_left _ _)
  have ew3 := gu2_xpt (xPair hc23) ℓ₃ (mem_pair_right _ _)
  generalize crossingParameter (xPair hc12) ℓ₁ (mem_pair_left _ _) = tx at ex1 ha ⊢
  generalize crossingParameter (xPair hc13) ℓ₁ (mem_pair_left _ _) = tm at em1 ha ⊢
  generalize crossingParameter (xPair hc13) ℓ₃ (mem_pair_right _ _) = sm at em3 ⊢
  generalize crossingParameter (xPair hc23) ℓ₃ (mem_pair_right _ _) = sw at ew3 ⊢
  generalize crossingParameter (xPair hc12) ℓ₂ (mem_pair_right _ _) = rx at ex2
  generalize crossingParameter (xPair hc23) ℓ₂ (mem_pair_left _ _) = rw at ew2
  have hvec : (tx - tm) • edge P ℓ₁ - (sw - sm) • edge P ℓ₃ = (rx - rw) • edge P ℓ₂ := by
    rw [← gu2_edgePoint_sub, ← gu2_edgePoint_sub, ← gu2_edgePoint_sub, ← ex1, ← em1, ← ew3, ← em3,
      ← ex2, ← ew2]
    abel
  have h1 := congrArg Prod.fst hvec
  have h2 := congrArg Prod.snd hvec
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
  have I1 : (tx - tm) * det (edge P ℓ₁) (edge P ℓ₃) = (rx - rw) * det (edge P ℓ₂) (edge P ℓ₃) := by
    unfold det; linear_combination (edge P ℓ₃).2 * h1 - (edge P ℓ₃).1 * h2
  have I2 : (rx - rw) * det (edge P ℓ₁) (edge P ℓ₂) = -((sw - sm) * det (edge P ℓ₁) (edge P ℓ₃)) := by
    unfold det; linear_combination (edge P ℓ₁).2 * h1 - (edge P ℓ₁).1 * h2
  have key := s174_order_alg hB hAC ha I1 I2
  rw [sub_pos, sub_neg] at key
  exact key

variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

/-- the three bundle labels of a `GT_Endpoint` configuration are `{e, f, g}` -/
theorem s174_labels_eq (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃) :
    ({ℓ₁, ℓ₂, ℓ₃} : Finset (ZMod n)) = {e, f, g} := by
  have hx := D.xT
  rw [D.xval] at hx
  have hw := D.wT
  rw [D.wval] at hw
  have hmem : ∀ a b : ZMod n, ({a, b} : Finset (ZMod n)) ∈ triangleSupports e f g →
      a ∈ ({e, f, g} : Finset (ZMod n)) ∧ b ∈ ({e, f, g} : Finset (ZMod n)) := by
    intro a b h
    unfold triangleSupports at h
    have ha : a ∈ ({a, b} : Finset (ZMod n)) := Finset.mem_insert_self _ _
    have hb : b ∈ ({a, b} : Finset (ZMod n)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h | h <;> rw [h] at ha hb <;>
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb <;> tauto
  have h12 := hmem _ _ hx
  have h23 := hmem _ _ hw
  apply Finset.eq_of_subset_of_card_le
  · intro ℓ hℓ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
    rcases hℓ with rfl | rfl | rfl
    · exact h12.1
    · exact h12.2
    · exact h23.2
  · rw [Finset.card_eq_three.mpr ⟨ℓ₁, ℓ₂, ℓ₃, D.l12, D.l13, D.l23, rfl⟩]
    exact Finset.card_le_three

/-- every selected crossing of the centre row other than `m'` has an edge outside the bundle -/
theorem s174_foreign_edge (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (c' : Crossing P') (hc' : c' ∈ transportSupport hs (Q ∪ {m}))
    (hne : c' ≠ crossingTransport hs m) :
    ∃ h ∈ c'.val, h ≠ ℓ₁ ∧ h ≠ ℓ₂ ∧ h ≠ ℓ₃ := by
  obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_map.mp hc'
  have hc₀Q : c₀ ∈ Q := by
    rcases Finset.mem_union.mp hc₀ with h | h
    · exact h
    · exact absurd (congrArg (crossingTransport hs) (Finset.mem_singleton.mp h)) hne
  have hout := D.Q_out c₀ hc₀Q
  change ∃ h ∈ c₀.val, h ≠ ℓ₁ ∧ h ≠ ℓ₂ ∧ h ≠ ℓ₃
  by_contra hcon
  apply hout
  have hlab : ∀ h ∈ c₀.val, h = e ∨ h = f ∨ h = g := by
    intro h hh
    have hℓ : h ∈ ({ℓ₁, ℓ₂, ℓ₃} : Finset (ZMod n)) := by
      by_contra hnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      exact hcon ⟨h, hh, hnot⟩
    rw [s174_labels_eq D] at hℓ
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hℓ
  obtain ⟨a, b, hab, hval⟩ := Finset.card_eq_two.mp (crossing_card_two c₀)
  have ha : a ∈ c₀.val := by rw [hval]; exact Finset.mem_insert_self _ _
  have hb : b ∈ c₀.val := by rw [hval]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [hval]
  exact gu2_pair_mem_triangleSupports hab (hlab a ha) (hlab b hb)

end S174Site

/-! ### The site theorem on a `GT_Endpoint` configuration -/

section S174SiteMain

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

/-- the tier-1 carrier geometry of the `E`-side polygon, as `CV.carrierDiagram` reads it -/
abbrev s174_cg : CarrierGeometry P' := CarrierGeometry.ofDiagrammatic (hG'.diagrammatic hn)

/-- Sanity: `carrierDiagram` is the positive lift on `s174_cg`, definitionally. -/
theorem s174_carrierDiagram_eq {S' : Finset (Crossing P')} (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry S') :
    CV.carrierDiagram hn hG' hS' q' =
      geoPositiveLift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hS') q' := rfl

/-- **The site theorem of row 174 (PLAN_FINAL §4.2).**  On a `GT_Endpoint` configuration in the canonical
sign branch, for any carrier `q'` of the transported centre row that owns the visits of `x'` and `w'`
(the residual crossings `a, c` of the `E-b` carrier `AB'`), the switch of `D_H = carrierDiagram q'` at
`x'` carries a `BigonData` with bigon `{x', w'}` and `K` the closed contact triangle `conv{x', m', w'}`:
depending on the traversal direction at the corner `m'`, `(y, z) = (w', x')` (entering along `ℓ₃`) or
`(x', w')` (entering along `ℓ₁`).  `s174_lift` is the crossing of the carrier shadow at a retained crossing. -/
theorem s174_site (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (hw' : crossingTransport hs w ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q') :
    ∃ B : BigonData ((CV.carrierDiagram hn hG' hSm' q').switch
        (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx')),
      B.i = ⟨0, Nat.one_pos⟩ ∧
      ((B.y = s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hw' ∧
        B.z = s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx') ∨
       (B.y = s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx' ∧
        B.z = s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hw')) := by
  have hs' : ∀ s, IsCrossing P' s ↔ IsCrossing P s := fun s => (hs s).symm
  have hc12 : IsCrossing P' {ℓ₁, ℓ₂} := (hs _).mp (D.xval ▸ x.property)
  have hc13 : IsCrossing P' {ℓ₁, ℓ₃} := (hs _).mp (D.mval ▸ m.property)
  have hc23 : IsCrossing P' {ℓ₂, ℓ₃} := (hs _).mp (D.wval ▸ w.property)
  have hX' : ExactTriangleVisitOrders P' P ℓ₁ ℓ₂ ℓ₃ hs' :=
    gu2_exact_of_eq hs' (s174_labels_eq D).symm (s174_exact_symm hs D.gauss)
  have hs12 : crossingSign P' ℓ₁ ℓ₂ = crossingSign P' ℓ₁ ℓ₃ := by
    rw [D.sign_eq _ _ (D.xval ▸ x.property), D.sign_eq _ _ (D.mval ▸ m.property)]
    exact hsgn
  have hs23 : crossingSign P' ℓ₂ ℓ₃ = crossingSign P' ℓ₁ ℓ₃ := by
    rw [D.sign_eq _ _ (D.wval ▸ w.property), D.sign_eq _ _ (D.mval ▸ m.property)]
    exact D.sgn
  have hxeq : crossingTransport hs x = xPair hc12 := Subtype.ext D.xval
  have hmeq : crossingTransport hs m = xPair hc13 := Subtype.ext D.mval
  have hweq : crossingTransport hs w = xPair hc23 := Subtype.ext D.wval
  have hmS : xPair hc13 ∈ transportSupport hs (Q ∪ {m}) := by
    rw [← hmeq]
    exact Finset.mem_map_of_mem _ (Finset.mem_union_right _ (Finset.mem_singleton_self m))
  have hx'' : xPair hc12 ∈ geoCarrierCrossings (s174_cg hn hG').cg (transportSupport hs (Q ∪ {m})) q' := by
    rw [← hxeq]; exact hx'
  have hw'' : xPair hc23 ∈ geoCarrierCrossings (s174_cg hn hG').cg (transportSupport hs (Q ∪ {m})) q' := by
    rw [← hweq]; exact hw'
  have hsel : ∀ c' ∈ transportSupport hs (Q ∪ {m}), c' ≠ xPair hc13 →
      ∃ h ∈ c'.val, h ≠ ℓ₁ ∧ h ≠ ℓ₂ ∧ h ≠ ℓ₃ :=
    fun c' hc' hne => s174_foreign_edge D c' hc' (by rw [hmeq]; exact hne)
  have hord := s174_order hG'.crossingGeometry hc12 hc13 hc23 hs12 hs23
  have hne_x : crossingParameter (xPair hc12) ℓ₁ (mem_pair_left _ _) ≠
      crossingParameter (xPair hc13) ℓ₁ (mem_pair_left _ _) :=
    s174_param_ne hG'.crossingGeometry (s174_xPair_ne_of_mem hc12 hc13 (s174_ne_of_isCrossing hc23)) _ _
  have hne_w : crossingParameter (xPair hc23) ℓ₃ (mem_pair_right _ _) ≠
      crossingParameter (xPair hc13) ℓ₃ (mem_pair_right _ _) := by
    refine s174_param_ne hG'.crossingGeometry ?_ _ _
    intro heq
    have hmem : ℓ₂ ∈ (xPair hc13).val := by rw [← heq]; exact mem_pair_left _ _
    rcases Finset.mem_insert.mp hmem with h1 | h1
    · exact s174_ne_of_isCrossing hc12 h1.symm
    · exact s174_ne_of_isCrossing hc23 (Finset.mem_singleton.mp h1)
  rcases lt_or_gt_of_ne hne_x with hlt | hgt
  · -- `x'` precedes `m'` on `ℓ₁`: the corner polygon enters along `ℓ₁`, leaves along `ℓ₃`; `(y, z) = (x', w')`
    have hsw : crossingParameter (xPair hc13) ℓ₃ (mem_pair_right _ _) <
        crossingParameter (xPair hc23) ℓ₃ (mem_pair_right _ _) := by
      rcases lt_or_gt_of_ne hne_w with h | h
      · exact absurd (hord.mpr h) (not_lt.mpr hlt.le)
      · exact h
    have hsgnC : crossingSign P' ℓ₁ ℓ₂ = crossingSign P' ℓ₂ ℓ₃ := hs12.trans hs23.symm
    obtain ⟨B, hBi, hBy, hBz⟩ := s174_core hn (s174_cg hn hG') hs' hc12 hc13 hc23
      (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' hX' hmS hx'' hw'' hsel hlt hsw hsgnC
      (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx')
      (Or.inl (s174_lift_congr hn _ _ q' hxeq hx' hx''))
    exact ⟨B, hBi, Or.inr ⟨hBy.trans (s174_lift_congr hn _ _ q' hxeq.symm hx'' hx'),
      hBz.trans (s174_lift_congr hn _ _ q' hweq.symm hw'' hw')⟩⟩
  · -- `m'` precedes `x'` on `ℓ₁`: the corner polygon enters along `ℓ₃`, leaves along `ℓ₁`; `(y, z) = (w', x')`
    have hsw : crossingParameter (xPair hc23) ℓ₃ (mem_pair_right _ _) <
        crossingParameter (xPair hc13) ℓ₃ (mem_pair_right _ _) := hord.mp hgt
    have hcef : IsCrossing P' {ℓ₃, ℓ₂} := gu2_isCrossing_comm hc23
    have hceg : IsCrossing P' {ℓ₃, ℓ₁} := gu2_isCrossing_comm hc13
    have hcfg : IsCrossing P' {ℓ₂, ℓ₁} := gu2_isCrossing_comm hc12
    have hXA : ExactTriangleVisitOrders P' P ℓ₃ ℓ₂ ℓ₁ hs' :=
      gu2_exact_of_eq hs' (by ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) hX'
    have e_ef : xPair hcef = xPair hc23 := gu2_xPair_comm hc23
    have e_eg : xPair hceg = xPair hc13 := gu2_xPair_comm hc13
    have e_fg : xPair hcfg = xPair hc12 := gu2_xPair_comm hc12
    have hsgnA : crossingSign P' ℓ₃ ℓ₂ = crossingSign P' ℓ₂ ℓ₁ := by
      rw [crossingSign_swap P' ℓ₂ ℓ₃, crossingSign_swap P' ℓ₁ ℓ₂, hs23, hs12]
    have hord_in : visitParameter (G11_vef hcef) < visitParameter (G11_veg hceg) := by
      have h1 : visitParameter (G11_vef hcef) = crossingParameter (xPair hc23) ℓ₃ (mem_pair_right _ _) :=
        s174_param_congr e_ef _ _
      have h2 : visitParameter (G11_veg hceg) = crossingParameter (xPair hc13) ℓ₃ (mem_pair_right _ _) :=
        s174_param_congr e_eg _ _
      rw [h1, h2]
      exact hsw
    have hord_out : visitParameter (G11_vge hceg) < visitParameter (G11_vgf hcfg) := by
      have h1 : visitParameter (G11_vge hceg) = crossingParameter (xPair hc13) ℓ₁ (mem_pair_left _ _) :=
        s174_param_congr e_eg _ _
      have h2 : visitParameter (G11_vgf hcfg) = crossingParameter (xPair hc12) ℓ₁ (mem_pair_left _ _) :=
        s174_param_congr e_fg _ _
      rw [h1, h2]
      exact hgt
    have hmS' : xPair hceg ∈ transportSupport hs (Q ∪ {m}) := by rw [e_eg]; exact hmS
    have hyA : xPair hcef ∈ geoCarrierCrossings (s174_cg hn hG').cg (transportSupport hs (Q ∪ {m})) q' := by
      rw [e_ef]; exact hw''
    have hzA : xPair hcfg ∈ geoCarrierCrossings (s174_cg hn hG').cg (transportSupport hs (Q ∪ {m})) q' := by
      rw [e_fg]; exact hx''
    have hselA : ∀ c' ∈ transportSupport hs (Q ∪ {m}), c' ≠ xPair hceg →
        ∃ h ∈ c'.val, h ≠ ℓ₃ ∧ h ≠ ℓ₂ ∧ h ≠ ℓ₁ := by
      intro c' hc' hne
      obtain ⟨h, hh, h1, h2, h3⟩ := hsel c' hc' (by rw [← e_eg]; exact hne)
      exact ⟨h, hh, h3, h2, h1⟩
    obtain ⟨B, hBi, hBy, hBz⟩ := s174_core hn (s174_cg hn hG') hs' hcef hceg hcfg
      (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' hXA hmS' hyA hzA hselA
      hord_in hord_out hsgnA
      (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx')
      (Or.inr (s174_lift_congr hn _ _ q' (hxeq.trans e_fg.symm) hx' hzA))
    exact ⟨B, hBi, Or.inl ⟨hBy.trans (s174_lift_congr hn _ _ q' (e_ef.trans hweq.symm) hyA hw'),
      hBz.trans (s174_lift_congr hn _ _ q' (e_fg.trans hxeq.symm) hzA hx')⟩⟩

end S174SiteMain

/-! ### (b) the record identification `hrec`, stated; (c) the `fulltwist` field from (a) + (b) -/

section S174Consumer

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

/-- the reduced record of a bigon site with crossings `y₀, z₀`, written without the `BigonData` -/
def s174_reducedRecordOf (D : Diagram) (y₀ z₀ : D.Γ.Crossing) : Record :=
  D.record.restrictCrossings
    {c | c ≠ D.record.crossingOf (D.overVisit y₀) ∧ c ≠ D.record.crossingOf (D.overVisit z₀)}

theorem s174_reducedRecord_eq {D : Diagram} (B : BigonData D) {y₀ z₀ : D.Γ.Crossing}
    (hy : B.y = y₀) (hz : B.z = z₀) : B.reducedRecord = s174_reducedRecordOf D y₀ z₀ := by
  unfold BigonData.reducedRecord BigonData.keep s174_reducedRecordOf
  rw [hy, hz]

/-- the reduced record does not depend on which bigon crossing is called `y` -/
theorem s174_reducedRecord_eq_swap {D : Diagram} (B : BigonData D) {y₀ z₀ : D.Γ.Crossing}
    (hy : B.y = z₀) (hz : B.z = y₀) : B.reducedRecord = s174_reducedRecordOf D y₀ z₀ := by
  unfold BigonData.reducedRecord BigonData.keep s174_reducedRecordOf
  rw [hy, hz]
  congr 1
  ext c
  exact and_comm

/-- **(b) `hrec` of PLAN_FINAL §4.2, STATED** (the wall transport of the carried marks, G11 Unit-F
pattern / `GT_owner_transport` on good marks): the record of `D_H.switch x'` with the four occurrences
of `x', w'` deleted is the record of the `P-b` lift `D_L = carrierDiagram qAB`.  Not proved here;
cost estimate in Site_174_REPORT.md. -/
def s174_hrec_prop (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (hw' : crossingTransport hs w ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q') : Prop :=
  Nonempty (RecordIso
    (s174_reducedRecordOf ((CV.carrierDiagram hn hG' hSm' q').switch
        (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx'))
      (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hw')
      (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx'))
    (CV.carrierDiagram hn hG hSm qAB).record)

/-- **(c) The `fulltwist` field of `gsc_Ledger` from (a) `s174_site` and (b) `s174_hrec_prop`**, through
the PROVED glue `gsc_fulltwist_of_bigon`: `qx` is the lifted `x'`, `D₀` the library smoothing
(`exists_smoothing`).  `gsc_fulltwist_triple` is `moves_fulltwist_triple` verbatim. -/
theorem s174_fulltwist_of_hrec
    (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (hw' : crossingTransport hs w ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (hrec : s174_hrec_prop hn hG hG' hSm hSm' qAB q' hx' hw') :
    ∃ D₀ : Diagram, gsc_fulltwist_triple (CV.carrierDiagram hn hG hSm qAB) (CV.carrierDiagram hn hG' hSm' q') D₀
      (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx') := by
  obtain ⟨B, -, hB⟩ := s174_site hn hG hG' D hsgn hSm' q' hx' hw'
  have hq : (CV.carrierDiagram hn hG' hSm' q').IsPositive
      (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx') :=
    geoPositiveLift_isPositive hn _ _ q' _
  have hrec' : Nonempty (RecordIso B.reducedRecord (CV.carrierDiagram hn hG hSm qAB).record) := by
    rcases hB with ⟨hy, hz⟩ | ⟨hy, hz⟩
    · rw [s174_reducedRecord_eq B hy hz]; exact hrec
    · rw [s174_reducedRecord_eq_swap B hy hz]; exact hrec
  exact gsc_fulltwist_of_bigon _ _ _ hq rfl rfl B hrec'

end S174Consumer

end

end SM.Link


/-! ## HREC (Wave 2, I-174 (b)): the wall record transport `hrec` of row 174 — PROVED

Prover of unit HREC, 2026-09-15.  Everything below is NEW (nothing above changed); names carry the
prefix `r174h_`.  Content: `s174_hrec_prop` (Site_174_REPORT §3) is proved for the ledger's carrier
`q' = τ qAB = GT_carrierEquiv (gsc_wall_of_endpoint …) qAB` on a `GT_Endpoint` configuration
(`r174h__s174_hrec_prop_proof`).  Route: the CV:cor:groupedknot §2 pattern `liftRestrictRecordIso`
(CV/GroupedKnot.lean, "the record of the lift of a smaller carrier is the restricted record of the
lift of a larger one") across the wall — the identity on parent visits, transported by
`visitTransport`, is a named record isomorphism from the record of the `P-b` lift `D_L` onto the
record of `D_H.switch x'` restricted to the crossings other than `x', w'`:
* the retained crossings correspond (`r174h_mem_retained'`, `r174h_retained_of_mem'`): a retained
  crossing of `AB` is outside the triangle (it lies in `U(S)`, and `x, w` interlace the selected `m`),
  so its visits are good marks and `GT_owner_transport` carries their owner to `τ qAB`; conversely a
  retained crossing of `AB'` other than `x', w'` is outside the triangle and comes from `AB`;
* the successor clause is `cycNext_unique_on` on the parent keys (`visitBetween_iff_key`,
  `arcBetween_iff_key`, `not_arcBetween_firstReturn`), the key order of outside visits being carried
  by `GT_Wall.key_lt` (no reversed pair: `r174h_cyc`);
* pairing is `liftVisit_twin` + `visitTransport_visitTwin`; the over bits are the divide signs
  `sign det(edge ℓ, edge ℓ')`, carried by `GT_Endpoint.sign_eq` (`overBit_eq_true_iff_parent`); the
  signs are all `+1` (`geoPositiveLift_sign`); the switch at `x'` touches only deleted occurrences
  (`r174h_switch_overBit_of_ne`, `switch_sign_of_ne`). -/

namespace SM.Link

open SM SM.GeoCarrier SM.Carrier RProof

noncomputable section

/-! ### Record-level helpers: a switched diagram's record has the same occurrences, successor, pairing
and arc order; the crossing of an occurrence is the crossing of `overVisit y₀` iff it visits `y₀` -/

section R174HRecord

variable (E : Diagram)

theorem r174h_switch_record_succ (x₀ : E.Γ.Crossing) (v : E.Γ.Visit) :
    (E.switch x₀).record.succ v = E.record.succ v := rfl

theorem r174h_switch_record_pair (x₀ : E.Γ.Crossing) (v : E.Γ.Visit) :
    (E.switch x₀).record.pair v = E.record.pair v := rfl

theorem r174h_switch_arcBetween (x₀ : E.Γ.Crossing) (v w u : E.Γ.Visit) :
    (E.switch x₀).record.ArcBetween v w u ↔ E.record.ArcBetween v w u := Iff.rfl

/-- The over bit of an occurrence of an unswitched crossing is unchanged by the switch. -/
theorem r174h_switch_overBit_of_ne {x₀ : E.Γ.Crossing} {v : E.Γ.Visit} (hv : v.1 ≠ x₀) :
    (E.switch x₀).overBit v = E.overBit v := by
  have h3 : (E.switch x₀).isOver v ↔ E.isOver v := by
    unfold Diagram.isOver
    rw [Diagram.switch_overStrand_of_ne E hv]
    exact Iff.rfl
  exact Bool.eq_iff_iff.mpr ((Diagram.overBit_eq_true_iff (E.switch x₀) v).trans
    (h3.trans (Diagram.overBit_eq_true_iff E v).symm))

/-- The record crossing of an occurrence is the record crossing of `overVisit y₀` iff the occurrence
visits `y₀`. -/
theorem r174h_crossingOf_overVisit_eq_iff (v : E.Γ.Visit) (y₀ : E.Γ.Crossing) :
    E.record.crossingOf v = E.record.crossingOf (E.overVisit y₀) ↔ v.1 = y₀ := by
  rw [Record.crossingOf_eq_iff]
  change v ∈ ({E.overVisit y₀, E.twin (E.overVisit y₀)} : Finset E.Γ.Visit) ↔ _
  rw [Diagram.mem_pair_twin_iff]
  exact Iff.rfl

end R174HRecord

/-! ### The configuration: the centre row `S = Q ∪ {m}`, its wall `𝑾` and the `E-b` carrier `τ qAB` -/

section R174H

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
  (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
  (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
  (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))

local notation "𝑻" => triangleCrossings P e f g
local notation "𝑺" => Q ∪ (Singleton.singleton m : Finset (Crossing P))
local notation "𝑺'" => transportSupport hs (Q ∪ (Singleton.singleton m : Finset (Crossing P)))
local notation "𝑾" => gsc_wall_of_endpoint hG hG' D hSm hSm'
local notation "qAB'" => GT_carrierEquiv (gsc_wall_of_endpoint hG hG' D hSm hSm') qAB

/-! #### The retained crossings of `AB` and of `AB' = τ AB` correspond, up to `x', w'` -/

include D hSm in
/-- A retained crossing of the carrier `AB` of the centre row is outside the triangle: it lies in
`U(S)`, while `x, w` interlace the selected `m` and `m` is selected. -/
theorem r174h_not_tri_of_retained {c : Crossing P}
    (hc : c ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) : c.val ∉ triangleSupports e f g := by
  intro hT
  have hU := geoCarrierCrossings_subset_U hG.crossingGeometry
    (CV.geoIndependent_of_mem_Ind _ hSm) qAB hc
  rw [mem_geoSupportUnselected_iff] at hU
  have hmS : m ∈ 𝑺 := Finset.mem_union_right _ (Finset.mem_singleton_self m)
  rcases D.tri_cases c hT with h | h | h
  · subst h; exact hU.2 m hmS D.hxm
  · subst h; exact hU.2 m hmS D.hwm
  · subst h; exact hU.1 hmS

include D hSm in
/-- The visits of a retained crossing of `AB` are good marks of the wall. -/
theorem r174h_good {v : Visit P} (hv : v.1 ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    GT_Good 𝑻 𝑺 (Sum.inr v) :=
  GT_good_of_not_mem _ _ (fun h => r174h_not_tri_of_retained hG hG' D hSm qAB hv
    ((F1.mem_triangleCrossings e f g v.1).mp h))

include D hSm in
theorem r174h_ne_x' {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    crossingTransport hs c ≠ crossingTransport hs x := fun h =>
  r174h_not_tri_of_retained hG hG' D hSm qAB hc (((crossingTransport hs).injective h) ▸ D.xT)

include D hSm in
theorem r174h_ne_w' {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    crossingTransport hs c ≠ crossingTransport hs w := fun h =>
  r174h_not_tri_of_retained hG hG' D hSm qAB hc (((crossingTransport hs).injective h) ▸ D.wT)

/-- The transported visit of a retained crossing of `AB` is owned by `τ AB` (`GT_owner_transport`). -/
theorem r174h_owner' {v : Visit P} (hv : v.1 ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    geoOwner hG'.crossingGeometry 𝑺' (Sum.inr (visitTransport hs v)) = qAB' := by
  rw [← markTransport_visit, GT_owner_transport 𝑾 (r174h_good hG hG' D hSm qAB hv),
    ((mem_geoCarrierCrossings _ _ _ _).mp hv).2 v rfl]

/-- A retained crossing of `AB` is transported to a retained crossing of `τ AB`. -/
theorem r174h_mem_retained' {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    crossingTransport hs c ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' qAB' := by
  rw [mem_geoCarrierCrossings]
  refine ⟨?_, fun v' hv' => ?_⟩
  · rw [mem_transportSupport_iff]
    exact ((mem_geoCarrierCrossings _ _ _ _).mp hc).1
  · obtain ⟨v, rfl⟩ := (visitTransport hs).surjective v'
    rw [visitTransport_crossing] at hv'
    have hvc : v.1 = c := (crossingTransport hs).injective hv'
    exact r174h_owner' hG hG' D hSm hSm' qAB (hvc ▸ hc)

/-- Conversely, a retained crossing of `τ AB` other than `x', w'` comes from a retained crossing of
`AB`: it is outside the triangle (not `m'`, which is selected), so its visits are good marks. -/
theorem r174h_retained_of_mem' {c : Crossing P}
    (hc : crossingTransport hs c ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' qAB')
    (hcx : crossingTransport hs c ≠ crossingTransport hs x)
    (hcw : crossingTransport hs c ≠ crossingTransport hs w) :
    c ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB := by
  rw [mem_geoCarrierCrossings] at hc ⊢
  have hcS : c ∉ 𝑺 := by rw [← mem_transportSupport_iff hs]; exact hc.1
  have hcT : c.val ∉ triangleSupports e f g := by
    intro hT
    rcases D.tri_cases c hT with h | h | h
    · exact hcx (by rw [h])
    · exact hcw (by rw [h])
    · exact hcS (by rw [h]; exact Finset.mem_union_right _ (Finset.mem_singleton_self _))
  refine ⟨hcS, fun v hv => ?_⟩
  have hgood : GT_Good 𝑻 𝑺 (Sum.inr v) :=
    GT_good_of_not_mem _ _ (fun h => hcT (by rw [← hv]; exact (F1.mem_triangleCrossings e f g v.1).mp h))
  have h1 := hc.2 (visitTransport hs v) (by rw [visitTransport_crossing, hv])
  rw [← markTransport_visit, GT_owner_transport 𝑾 hgood] at h1
  exact (GT_carrierEquiv 𝑾).injective h1

theorem r174h_retained_of_mem'' {c' : Crossing P'}
    (hc : c' ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' qAB')
    (hcx : c' ≠ crossingTransport hs x) (hcw : c' ≠ crossingTransport hs w) :
    (crossingTransport hs).symm c' ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB := by
  obtain ⟨c, rfl⟩ := (crossingTransport hs).surjective c'
  rw [Equiv.symm_apply_apply]
  exact r174h_retained_of_mem' hG hG' D hSm hSm' qAB hc hcx hcw

/-! #### The key order of the visits of retained crossings is carried across the wall -/

include D hSm hSm' in
/-- The visits of retained crossings of `AB` form no reversed pair with anything (they are outside the
triangle), so their key order is carried (`GT_Wall.key_lt`). -/
theorem r174h_key_lt {a b : Visit P} (ha : a.1 ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    geometricVisitKey hG.crossingGeometry a < geometricVisitKey hG.crossingGeometry b ↔
      geometricVisitKey hG'.crossingGeometry (visitTransport hs a) <
        geometricVisitKey hG'.crossingGeometry (visitTransport hs b) :=
  𝑾.key_lt a b (GT_not_rev_of_not_mem_left (fun h => r174h_not_tri_of_retained hG hG' D hSm qAB ha
    ((F1.mem_triangleCrossings e f g a.1).mp h)))

include D hSm hSm' in
/-- The cyclic order of three visits of retained crossings of `AB` is carried across the wall. -/
theorem r174h_cyc {a b c : Visit P} (ha : a.1 ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB)
    (hb : b.1 ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB)
    (hc : c.1 ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    cycBetween (geometricVisitKey hG.crossingGeometry a) (geometricVisitKey hG.crossingGeometry b)
        (geometricVisitKey hG.crossingGeometry c) ↔
      cycBetween (geometricVisitKey hG'.crossingGeometry (visitTransport hs a))
        (geometricVisitKey hG'.crossingGeometry (visitTransport hs b))
        (geometricVisitKey hG'.crossingGeometry (visitTransport hs c)) :=
  GT_cyc_congr_of_lt (r174h_key_lt hG hG' D hSm hSm' qAB ha) (r174h_key_lt hG hG' D hSm hSm' qAB hb)
    (r174h_key_lt hG hG' D hSm hSm' qAB hc)

/-! ### The two lifts, the switched `E`-side diagram and the keep-set

The `E-b` carrier is a variable `q'` with `hq' : q' = τ qAB`, as `s174_hrec_prop` binds it: the carrier
shadow `geoCarrierShadow … q'` is an `abbrev`, and with the compound term `τ qAB` in place of `q'` the
unifier unfolds it on every type ascription of a lifted crossing and times out; with the variable it is
stuck at once.  Every declaration of this section takes the eleven arguments
`hn hG hG' D hSm hSm' qAB q' hq' hx' hw'` in this order. -/

section R174HLift

variable (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
  (hq' : q' = GT_carrierEquiv (gsc_wall_of_endpoint hG hG' D hSm hSm') qAB)
  (hx' : crossingTransport hs x ∈
    geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
  (hw' : crossingTransport hs w ∈
    geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')

include hn hG hG' D hSm hSm' qAB q' hq' hx' hw'

set_option linter.unusedSectionVars false

local notation "hGc" => s174_cg hn hG
local notation "hGc'" => s174_cg hn hG'
local notation "hSg" => CV.geoIndependent_of_mem_Ind hG.crossingGeometry hSm
local notation "hSg'" => CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm'
/-- `D_L`, the `P-b` lift -/
local notation "𝓓L" => geoPositiveLift hn (s174_cg hn hG)
  (CV.geoIndependent_of_mem_Ind hG.crossingGeometry hSm) qAB
/-- `D_H`, the `E-b` lift -/
local notation "𝓓H" => geoPositiveLift hn (s174_cg hn hG')
  (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q'
local notation "𝓵x" => s174_lift hn (s174_cg hn hG')
  (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' (crossingTransport hs x) hx'
local notation "𝓵w" => s174_lift hn (s174_cg hn hG')
  (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' (crossingTransport hs w) hw'
/-- `D_H.switch x'` -/
local notation "𝓓sw" => Diagram.switch (geoPositiveLift hn (s174_cg hn hG')
  (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q')
  (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q'
    (crossingTransport hs x) hx')

/-- The retained crossings of `AB` are transported into those of `q' = τ AB`. -/
theorem r174h_mem_retained_q {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    crossingTransport hs c ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' q' := by
  rw [hq']
  exact r174h_mem_retained' hG hG' D hSm hSm' qAB hc

/-- A retained crossing of `q' = τ AB` other than `x', w'` comes from a retained crossing of `AB`. -/
theorem r174h_retained_of_mem_q {c' : Crossing P'}
    (hc : c' ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' q')
    (hcx : c' ≠ crossingTransport hs x) (hcw : c' ≠ crossingTransport hs w) :
    (crossingTransport hs).symm c' ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB := by
  rw [hq'] at hc
  exact r174h_retained_of_mem'' hG hG' D hSm hSm' qAB hc hcx hcw

/-- the record crossings kept by the deletion of `x', w'`: the keep-set of `s174_reducedRecordOf` -/
def r174h_keep : Set (𝓓sw).record.Crossing :=
  {c | c ≠ (𝓓sw).record.crossingOf ((𝓓sw).overVisit 𝓵w) ∧
    c ≠ (𝓓sw).record.crossingOf ((𝓓sw).overVisit 𝓵x)}

local notation "𝓚" => r174h_keep hn hG' hSm' q' hx' hw'

/-- Sanity (`rfl`): the reduced record of the site is the restriction to the keep-set. -/
theorem r174h_reducedRecordOf_eq :
    s174_reducedRecordOf 𝓓sw 𝓵w 𝓵x = (𝓓sw).record.restrictCrossings 𝓚 := rfl

theorem r174h_crossKeep_iff (v : (𝓓sw).Γ.Visit) :
    (𝓓sw).record.CrossKeep 𝓚 v ↔ v.1 ≠ 𝓵w ∧ v.1 ≠ 𝓵x := by
  change ((𝓓sw).record.crossingOf v ≠ _ ∧ (𝓓sw).record.crossingOf v ≠ _) ↔ _
  exact and_congr (not_congr (r174h_crossingOf_overVisit_eq_iff _ v _))
    (not_congr (r174h_crossingOf_overVisit_eq_iff _ v _))

/-- An occurrence of the lift sits at the lifted crossing `s174_lift c` iff its parent visit is a visit
of `c`. -/
theorem r174h_lift_eq_iff (v : (𝓓H).Γ.Visit) {c : Crossing P'}
    (hc : c ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' q') :
    v.1 = s174_lift hn hGc' hSg' q' c hc ↔ (CV.liftVisit hn hGc' hSg' q' v).1 = c := by
  rw [CV.liftVisit_fst]
  exact (Equiv.eq_symm_apply _).trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- The kept occurrences are those whose parent crossing is neither `w'` nor `x'`. -/
theorem r174h_crossKeep_iff' (v : (𝓓sw).Γ.Visit) :
    (𝓓sw).record.CrossKeep 𝓚 v ↔
      (CV.liftVisit hn hGc' hSg' q' v).1 ≠ crossingTransport hs w ∧
      (CV.liftVisit hn hGc' hSg' q' v).1 ≠ crossingTransport hs x := by
  rw [r174h_crossKeep_iff hn hG hG' D hSm hSm' qAB q' hq' hx' hw']
  exact and_congr (not_congr (r174h_lift_eq_iff hn hG hG' D hSm hSm' qAB q' hq' hx' hw' v hw'))
    (not_congr (r174h_lift_eq_iff hn hG hG' D hSm hSm' qAB q' hq' hx' hw' v hx'))

/-! ### The transfer: the identity on parent visits, transported across the wall -/

/-- The occurrence bijection: an occurrence of `D_L` (a visit of a retained crossing of `AB`) goes to
the occurrence of `D_H` at the transported visit, which is kept (`x', w'` are not transports of retained
crossings of `AB`). -/
noncomputable def r174h_transfer :
    (𝓓L).Γ.Visit ≃ {v : (𝓓sw).Γ.Visit // (𝓓sw).record.CrossKeep 𝓚 v} where
  toFun v' := ⟨(CV.liftVisitEquiv hn hGc' hSg' q').symm
      ⟨visitTransport hs (CV.liftVisit hn hGc hSg qAB v'),
        r174h_mem_retained_q hn hG hG' D hSm hSm' qAB q' hq' hx' hw'
          (CV.liftVisit_mem hn hGc hSg qAB v')⟩,
    (r174h_crossKeep_iff' hn hG hG' D hSm hSm' qAB q' hq' hx' hw' _).mpr
      ⟨by
        rw [CV.liftVisit_symm]
        exact r174h_ne_w' hG hG' D hSm qAB (CV.liftVisit_mem hn hGc hSg qAB v'),
       by
        rw [CV.liftVisit_symm]
        exact r174h_ne_x' hG hG' D hSm qAB (CV.liftVisit_mem hn hGc hSg qAB v')⟩⟩
  invFun v := (CV.liftVisitEquiv hn hGc hSg qAB).symm
    ⟨(visitTransport hs).symm (CV.liftVisit hn hGc' hSg' q' v.1),
      r174h_retained_of_mem_q hn hG hG' D hSm hSm' qAB q' hq' hx' hw'
        (CV.liftVisit_mem hn hGc' hSg' q' v.1)
        ((r174h_crossKeep_iff' hn hG hG' D hSm hSm' qAB q' hq' hx' hw' v.1).mp v.2).2
        ((r174h_crossKeep_iff' hn hG hG' D hSm hSm' qAB q' hq' hx' hw' v.1).mp v.2).1⟩
  left_inv v' := by
    apply CV.liftVisit_injective hn hGc hSg qAB
    rw [CV.liftVisit_symm]
    simp only [CV.liftVisit_symm, Equiv.symm_apply_apply]
  right_inv v := by
    apply Subtype.ext
    apply CV.liftVisit_injective hn hGc' hSg' q'
    rw [CV.liftVisit_symm]
    simp only [CV.liftVisit_symm, Equiv.apply_symm_apply]

local notation "𝚽" => r174h_transfer hn hG hG' D hSm hSm' qAB q' hq' hx' hw'

theorem r174h_liftVisit_transfer (v' : (𝓓L).Γ.Visit) :
    CV.liftVisit hn hGc' hSg' q' (r174h_transfer hn hG hG' D hSm hSm' qAB q' hq' hx' hw' v').1 =
      visitTransport hs (CV.liftVisit hn hGc hSg qAB v') := by
  show CV.liftVisit hn hGc' hSg' q' ((CV.liftVisitEquiv hn hGc' hSg' q').symm _) = _
  rw [CV.liftVisit_symm]

theorem r174h_record_componentCount : (𝓓sw).record.componentCount = 1 :=
  CV.record_componentCount_one _ (geoPositiveLift_componentCount hn hGc' hSg' q')

/-- **The successor clause**: the transfer carries the successor of `D_L` to the first-return successor
of the restricted record (both are the cyclic successor among the kept occurrences in the parent key
order, which is carried across the wall on the visits of retained crossings; `cycNext_unique_on`). -/
theorem r174h_transfer_succ (v' : (𝓓L).Γ.Visit) :
    (r174h_transfer hn hG hG' D hSm hSm' qAB q' hq' hx' hw' ((𝓓L).nextVisit v')).1 =
      (((𝓓sw).record.restrictCrossings 𝓚).succ
        (r174h_transfer hn hG hG' D hSm hSm' qAB q' hq' hx' hw' v')).1 := by
  set Φ := r174h_transfer hn hG hG' D hSm hSm' qAB q' hq' hx' hw' with hΦdef
  have hΦ : ∀ y, CV.liftVisit hn hGc' hSg' q' (Φ y).1 =
      visitTransport hs (CV.liftVisit hn hGc hSg qAB y) :=
    r174h_liftVisit_transfer hn hG hG' D hSm hSm' qAB q' hq' hx' hw'
  have h1 : (𝓓sw).record.componentCount = 1 :=
    r174h_record_componentCount hn hG hG' D hSm hSm' qAB q' hq' hx' hw'
  have hD' : (𝓓L).componentCount = 1 := geoPositiveLift_componentCount hn hGc hSg qAB
  refine cycNext_unique_on
    (p := fun u : (𝓓sw).Γ.Visit => (𝓓sw).record.CrossKeep 𝓚 u)
    (k := fun u => geometricVisitKey hG'.crossingGeometry (CV.liftVisit hn hGc' hSg' q' u))
    (fun a b _ _ hab => CV.liftVisit_injective hn hGc' hSg' q' (geometricVisitKey_injective _ hab))
    (Φ v').2 (Φ ((𝓓L).nextVisit v')).2 (((𝓓sw).record.restrictCrossings 𝓚).succ (Φ v')).2 ?_ ?_ ?_ ?_
  · intro h
    have h' := Φ.injective (Subtype.ext h)
    exact (𝓓L).nextVisit_ne_self v' ((𝓓L).twin v') (CV.compOf_eq_of_single hD' _ _)
      ((𝓓L).twin_ne v') h'
  · exact (((𝓓sw).record.restrictCrossings_succ_val_eq_iff h1 _ (Φ v').2 _).mp rfl).2.1
  · intro u hu hb
    obtain ⟨u', hu'⟩ := Φ.surjective ⟨u, hu⟩
    have hu'' : u = (Φ u').1 := by rw [hu']
    rw [hu'', hΦ, hΦ, hΦ] at hb
    have hb' := (r174h_cyc hG hG' D hSm hSm' qAB (CV.liftVisit_mem hn hGc hSg qAB v')
      (CV.liftVisit_mem hn hGc hSg qAB u') (CV.liftVisit_mem hn hGc hSg qAB _)).mpr hb
    exact (𝓓L).not_visitBetween_nextVisit v' u' (CV.compOf_eq_of_single hD' _ _)
      ((CV.visitBetween_iff_key hn hGc hSg qAB v' u' _).mpr hb')
  · intro u hu hb
    have harc := (CV.arcBetween_iff_key hn hGc' hSg' q' (Φ v').1 u _).mpr hb
    exact (𝓓sw).record.not_arcBetween_firstReturn _ h1 (Φ v') hu harc

/-- **The record of the `P-b` lift is the reduced record of the switched `E-b` lift** (the wall record
transport of row 174): the transfer is a named record isomorphism.  Clauses: successor
(`r174h_transfer_succ`), pairing (`liftVisit_twin`, `visitTransport_visitTwin`), over/under
(`overBit_eq_true_iff_parent` and the carried divide signs `GT_Endpoint.sign_eq`), signs (all `+1`,
the switch touching only the deleted occurrences of `x'`). -/
noncomputable def r174h_recordIso :
    RecordIso (𝓓L).record ((𝓓sw).record.restrictCrossings 𝓚) where
  e := finCongr (show (𝓓L).Γ.c = (𝓓sw).Γ.c from
    (geoPositiveLift_componentCount hn hGc hSg qAB).trans
      (geoPositiveLift_componentCount hn hGc' hSg' q').symm)
  Φ := r174h_transfer hn hG hG' D hSm hSm' qAB q' hq' hx' hw'
  comp_eq _ :=
    have : Subsingleton (Fin (𝓓sw).Γ.c) :=
      Fin.subsingleton_iff_le_one.mpr (le_of_eq (geoPositiveLift_componentCount hn hGc' hSg' q'))
    @Subsingleton.elim (Fin (𝓓sw).Γ.c) this _ _
  succ_eq v' := Subtype.ext (r174h_transfer_succ hn hG hG' D hSm hSm' qAB q' hq' hx' hw' v')
  pair_eq v' := by
    apply Subtype.ext
    apply CV.liftVisit_injective hn hGc' hSg' q'
    have ht : CV.liftVisit hn hGc' hSg' q' ((𝓓H).twin (𝚽 v').1) =
        visitTwin (CV.liftVisit hn hGc' hSg' q' (𝚽 v').1) :=
      CV.liftVisit_twin hn hGc' hSg' q' _
    change CV.liftVisit hn hGc' hSg' q' (𝚽 ((𝓓L).twin v')).1 =
      CV.liftVisit hn hGc' hSg' q' ((𝓓H).twin (𝚽 v').1)
    rw [ht, r174h_liftVisit_transfer, r174h_liftVisit_transfer, CV.liftVisit_twin,
      visitTransport_visitTwin]
  bit_eq v' := by
    have hne : (𝚽 v').1.1 ≠ 𝓵x :=
      ((r174h_crossKeep_iff hn hG hG' D hSm hSm' qAB q' hq' hx' hw' _).mp (𝚽 v').2).2
    have h1 : (𝓓sw).overBit (𝚽 v').1 = (𝓓H).overBit (𝚽 v').1 :=
      r174h_switch_overBit_of_ne (𝓓H) hne
    have h2 := CV.overBit_eq_true_iff_parent hn hGc' hSg' q' (𝚽 v').1
    have h3 := CV.overBit_eq_true_iff_parent hn hGc hSg qAB v'
    change (𝓓sw).overBit (𝚽 v').1 = (𝓓L).overBit v'
    rw [h1, Bool.eq_iff_iff, h2, h3, r174h_liftVisit_transfer, ← visitTransport_visitTwin,
      visitTransport_edge, visitTransport_edge]
    exact (GT_det_pos_iff_of_sign (D.sign_eq _ _ (by
      rw [← visit_crossing_val_eq_pair]
      exact (CV.liftVisit hn hGc hSg qAB v').1.property))).symm
  sgn_eq v' := by
    have hne : (𝚽 v').1.1 ≠ 𝓵x :=
      ((r174h_crossKeep_iff hn hG hG' D hSm hSm' qAB q' hq' hx' hw' _).mp (𝚽 v').2).2
    have h1 : (𝓓sw).sign (𝚽 v').1.1 = (𝓓H).sign (𝚽 v').1.1 := Diagram.switch_sign_of_ne (𝓓H) hne
    change (𝓓sw).sign (𝚽 v').1.1 = (𝓓L).sign v'.1
    exact h1.trans ((geoPositiveLift_sign hn hGc' hSg' q' (𝚽 v').1.1).trans
      (geoPositiveLift_sign hn hGc hSg qAB v'.1).symm)

/-! ### The stated Prop `s174_hrec_prop`, PROVED for the ledger's carrier `q' = τ qAB` -/

set_option linter.style.nameCheck false in
/-- **`hrec` of row 174 (PLAN_FINAL §4.2, Site_174_REPORT §3), PROVED** for the carrier
`q' = τ qAB = GT_carrierEquiv (gsc_wall_of_endpoint …) qAB` of the ledger (`gsc_wallData_of_endpoint`).
The bare Prop `s174_hrec_prop … qAB q' …` binds an arbitrary carrier `q'` of the transported centre row,
unrelated to `qAB`; it holds exactly for the wall copy of `qAB` (for another `q'` the two records have
different crossing sets in general), so the `GT_Endpoint` configuration `D` and the identification
`hq'` are the hypotheses under which the consumer `s174_fulltwist_of_hrec` is invoked (`W.τ qAB` is
`GT_carrierEquiv (gsc_wall_of_endpoint …) qAB` by `rfl`). -/
theorem r174h__s174_hrec_prop_proof : s174_hrec_prop hn hG hG' hSm hSm' qAB q' hx' hw' :=
  Nonempty.intro (r174h_recordIso hn hG hG' D hSm hSm' qAB q' hq' hx' hw').symm

/-- **The `fulltwist` field of `gsc_Ledger` for row 174**, from (a) `s174_site` and (b) `hrec` (both
PROVED): given the site inputs `hx', hw'` (the four visits of `x', w'` are owned by `τ qAB`, the
remaining consumer obligation of Site_174_REPORT §5), `gsc_fulltwist_triple` holds with `qx` the lifted
`x'` and `D₀` the library smoothing.  The realiser instantiates `q' := W.τ qAB`, `hq' := rfl`
(`gsc_wallData_of_endpoint`). -/
theorem r174h_fulltwist (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    ∃ D₀ : Diagram, gsc_fulltwist_triple (CV.carrierDiagram hn hG hSm qAB)
      (CV.carrierDiagram hn hG' hSm' q') D₀
      (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx') :=
  s174_fulltwist_of_hrec hn hG hG' D hsgn hSm hSm' qAB q' hx' hw'
    (r174h__s174_hrec_prop_proof hn hG hG' D hSm hSm' qAB q' hq' hx' hw')

end R174HLift

/-- `hrec` in the ledger's binding `q' := W.τ qAB` (`gsc_wallData_of_endpoint`): `hq'` is `rfl`. -/
theorem r174h_hrec_tau
    (hx' : crossingTransport hs x ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺'
      ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ qAB))
    (hw' : crossingTransport hs w ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺'
      ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ qAB)) :
    s174_hrec_prop hn hG hG' hSm hSm' qAB ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ qAB) hx' hw' :=
  r174h__s174_hrec_prop_proof hn hG hG' D hSm hSm' qAB _ rfl hx' hw'

end R174H

end

end SM.Link


/-! ## Unit CARRIERS (row 174, `gsc_Ledger` item 1): the carrier structure of the two supports
`Q ∪ {m}` (the centre row `P-b`) and `Q ∪ {x, w}` (the pair row `P-ac`) on the two-edge polygon `P`

Prover of unit CARRIERS, 2026-09-15.  Everything below is NEW (nothing above changed); names carry the
prefix `r174c_`.  Content (U_R174_REPORT.md §4 item 1): the carriers `qC, qAB` of `Q ∪ {m}` and
`qC', qA, qB` of `Q ∪ {x, w}`, their distinctness, the bijection `ρ` of the carriers of `Q ∪ {m}` onto
the carriers of `Q ∪ {x, w}` other than `qB` (`ρ qAB = qA`, `ρ qC = qC'`, spectators to themselves), and
the spectator reads (`weight`, `Ω₁`).  Method: the two reconnections `ρ_{Q∪{m}}` and `ρ_{Q∪{x,w}}` differ
only at the six local visits `x₁ x₂ w₂ w₃ m₁ m₃`, so a carrier avoiding them is literally the same cycle
of marks in both supports (`r174c_owner_iff_of_avoid`); the local carriers are computed from the three
adjacencies `adj1..3` of the endpoint configuration, the order at the corner (`s174_order`), and the
separation of the visits of a selected or dominated crossing. -/

namespace SM.Link

open SM SM.GeoCarrier SM.Carrier RProof

noncomputable section

/-! ### 1. Two permutations agreeing outside a set have the same cycles away from it -/

section R174CPerm

theorem r174c_pow_eq_of_agree {α : Type*} {σ σ' : Equiv.Perm α} {L : α → Prop}
    (hagree : ∀ a, ¬ L a → σ a = σ' a) {a : α} (hL : ∀ k : ℕ, ¬ L ((σ ^ k) a)) :
    ∀ k : ℕ, (σ' ^ k) a = (σ ^ k) a := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, ih, hagree _ (hL k)]

/-- If the `σ`-cycle of `a` avoids `L` and `σ, σ'` agree outside `L`, the two cycles of `a` coincide. -/
theorem r174c_sameCycle_iff_of_agree {α : Type*} [Finite α] {σ σ' : Equiv.Perm α} {L : α → Prop}
    (hagree : ∀ a, ¬ L a → σ a = σ' a) {a : α} (hL : ∀ b, σ.SameCycle a b → ¬ L b) (b : α) :
    σ.SameCycle a b ↔ σ'.SameCycle a b := by
  have hL' : ∀ k : ℕ, ¬ L ((σ ^ k) a) := fun k => hL _ ⟨k, by rw [zpow_natCast]⟩
  have hpow := r174c_pow_eq_of_agree hagree hL'
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    exact ⟨k, by rw [zpow_natCast, hpow k]; exact hk⟩
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    exact ⟨k, by rw [zpow_natCast, ← hpow k]; exact hk⟩

end R174CPerm

/-! ### 2. Two supports on one polygon: the reconnections agree away from the visits of `S ∆ T` -/

section R174CSupports

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

theorem r174c_succ_eq_of_not_local (hP : CrossingGeometry P) (S T : Finset (Crossing P)) (a : Mark P)
    (ha : ∀ v : Visit P, a = Sum.inr v → (v.1 ∈ S ↔ v.1 ∈ T)) :
    geoSmoothingSuccessor hP S a = geoSmoothingSuccessor hP T a := by
  cases a with
  | inl i => rfl
  | inr v =>
    have h := ha v rfl
    by_cases hv : v.1 ∈ S
    · rw [geoSmoothingSuccessor_visit_of_mem hP S v hv,
        geoSmoothingSuccessor_visit_of_mem hP T v (h.mp hv)]
    · rw [geoSmoothingSuccessor_visit_of_not_mem hP S v hv,
        geoSmoothingSuccessor_visit_of_not_mem hP T v (fun h' => hv (h.mpr h'))]

/-- **A carrier avoiding the visits of `S ∆ T` is the same cycle of marks for both supports.** -/
theorem r174c_owner_iff_of_avoid (hP : CrossingGeometry P) (S T : Finset (Crossing P)) {a : Mark P}
    (hL : ∀ v : Visit P, geoOwner hP S (Sum.inr v) = geoOwner hP S a → (v.1 ∈ S ↔ v.1 ∈ T))
    (b : Mark P) :
    geoOwner hP S b = geoOwner hP S a ↔ geoOwner hP T b = geoOwner hP T a := by
  rw [geoOwner_eq_iff, geoOwner_eq_iff, Equiv.Perm.sameCycle_comm,
    Equiv.Perm.sameCycle_comm (f := geoSmoothingSuccessor hP T)]
  refine r174c_sameCycle_iff_of_agree (L := fun c => ∃ v : Visit P, c = Sum.inr v ∧ ¬ (v.1 ∈ S ↔ v.1 ∈ T))
    ?_ ?_ b
  · intro c hc
    apply r174c_succ_eq_of_not_local hP S T c
    intro v hv
    by_contra hcon
    exact hc ⟨v, hv, hcon⟩
  · rintro c hc ⟨v, rfl, hv⟩
    exact hv (hL v ((geoOwner_eq_iff hP S _ _).mpr hc.symm))

/-- the successor of a visit is a visit further along its edge or the next vertex: a visit successor has
the larger parameter -/
theorem r174c_param_lt_of_succ (hn : 3 ≤ n) (hP : CrossingGeometry P) {v w : Visit P}
    (h : geoMarkSuccessor hP (Sum.inr v) = Sum.inr w) : visitParameter v < visitParameter w := by
  rcases geoMarkSuccessor_position_cases hn hP (Sum.inr v) with ⟨-, hlt⟩ | hvert
  · rw [h] at hlt; exact hlt
  · rw [h] at hvert; exact absurd hvert Sum.inr_ne_inl

theorem r174c_succ_of_adjacent_lt (hn : 3 ≤ n) (hP : CrossingGeometry P) {v w : Visit P}
    (hadj : AdjacentVisits hP v w) (hedge : v.2.val = w.2.val)
    (hlt : visitParameter v < visitParameter w) :
    geoMarkSuccessor hP (Sum.inr v) = Sum.inr w := by
  rcases GT_succ_of_adjacent hP hadj hedge with h | h
  · exact h
  · exact absurd (r174c_param_lt_of_succ hn hP h) (not_lt.mpr hlt.le)

omit [NeZero n] in
theorem r174c_adjacent_symm (hP : CrossingGeometry P) {v w : Visit P} (hadj : AdjacentVisits hP v w) :
    AdjacentVisits hP w v :=
  ⟨hadj.1.symm, hadj.2.symm⟩

omit [NeZero n] in
theorem r174c_visitParameter_visitOn {x : Crossing P} {ℓ : ZMod n} (h : ℓ ∈ x.val) :
    visitParameter (visitOn x ℓ h) = crossingParameter x ℓ h := rfl

end R174CSupports

/-! ### 3. The local carriers of the two rows on a `GT_Endpoint` configuration -/

section R174CLocal

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n}
  {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)

include D

/-! #### Membership facts -/

theorem r174c_x_not_mem_Sm : x ∉ Q ∪ {m} := by
  intro h
  rcases Finset.mem_union.mp h with h | h
  · exact D.not_mem_Q_of_mem_T D.xT h
  · exact D.xm (Finset.mem_singleton.mp h)

theorem r174c_w_not_mem_Sm : w ∉ Q ∪ {m} := by
  intro h
  rcases Finset.mem_union.mp h with h | h
  · exact D.not_mem_Q_of_mem_T D.wT h
  · exact D.wm (Finset.mem_singleton.mp h)

omit [NeZero n] D in
theorem r174c_m_mem_Sm : m ∈ Q ∪ {m} := Finset.mem_union_right _ (Finset.mem_singleton_self m)

omit [NeZero n] D in
theorem r174c_x_mem_Sxw : x ∈ Q ∪ {x, w} := Finset.mem_union_right _ (Finset.mem_insert_self x _)

omit [NeZero n] D in
theorem r174c_w_mem_Sxw : w ∈ Q ∪ {x, w} :=
  Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self w))

theorem r174c_m_not_mem_Sxw : m ∉ Q ∪ {x, w} := by
  intro h
  rcases Finset.mem_union.mp h with h | h
  · exact D.not_mem_Q_of_mem_T D.mT h
  · rcases Finset.mem_insert.mp h with h | h
    · exact D.xm h.symm
    · exact D.wm (Finset.mem_singleton.mp h).symm

theorem r174c_x_not_mem_Q : x ∉ Q := D.not_mem_Q_of_mem_T D.xT
theorem r174c_w_not_mem_Q : w ∉ Q := D.not_mem_Q_of_mem_T D.wT
theorem r174c_m_not_mem_Q : m ∉ Q := D.not_mem_Q_of_mem_T D.mT

omit [NeZero n] D in
/-- a crossing other than `x, w, m` is in `Q ∪ {m}` iff it is in `Q ∪ {x, w}` (iff it is in `Q`) -/
theorem r174c_mem_iff_of_outside {y : Crossing P} (hyx : y ≠ x) (hyw : y ≠ w) (hym : y ≠ m) :
    y ∈ Q ∪ {m} ↔ y ∈ Q ∪ {x, w} := by
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hyx, hyw, hym, or_false]

theorem r174c_x_mem_N_Sm : x ∈ CV.N hP (Q ∪ {m}) :=
  (CV.mem_N hP _ x).mpr ⟨m, r174c_m_mem_Sm, D.hxm⟩

theorem r174c_w_mem_N_Sm : w ∈ CV.N hP (Q ∪ {m}) :=
  (CV.mem_N hP _ w).mpr ⟨m, r174c_m_mem_Sm, D.hwm⟩

theorem r174c_m_mem_N_Sxw : m ∈ CV.N hP (Q ∪ {x, w}) :=
  (CV.mem_N hP _ m).mpr ⟨x, r174c_x_mem_Sxw, (CV.geometricInterlaces_comm hP x m).mp D.hxm⟩

theorem r174c_x_mem_U_Q : x ∈ CV.U hP Q :=
  (CV.mem_U_iff hP Q x).mpr ⟨r174c_x_not_mem_Q D,
    fun q hq => (CV.geometricInterlaces_comm hP x q).not.mpr (D.Q_avail q hq x D.xT)⟩

theorem r174c_w_mem_U_Q : w ∈ CV.U hP Q :=
  (CV.mem_U_iff hP Q w).mpr ⟨r174c_w_not_mem_Q D,
    fun q hq => (CV.geometricInterlaces_comm hP w q).not.mpr (D.Q_avail q hq w D.wT)⟩

theorem r174c_m_mem_U_Q : m ∈ CV.U hP Q :=
  (CV.mem_U_iff hP Q m).mpr ⟨r174c_m_not_mem_Q D,
    fun q hq => (CV.geometricInterlaces_comm hP m q).not.mpr (D.Q_avail q hq m D.mT)⟩

/-! #### Separation of the local visits -/

/-- `x` is dominated in `Q ∪ {m}`: its two visits lie on different carriers -/
theorem r174c_sep_x_Sm (hSm : Q ∪ {m} ∈ CV.Ind hP) :
    geoOwner hP (Q ∪ {m}) (Sum.inr D.x₁) ≠ geoOwner hP (Q ∪ {m}) (Sum.inr D.x₂) := by
  have h := (CV.visits_separated_iff hP hSm D.x₁).mpr (Or.inr (r174c_x_mem_N_Sm D))
  rwa [D.twin_x₁] at h

theorem r174c_sep_w_Sm (hSm : Q ∪ {m} ∈ CV.Ind hP) :
    geoOwner hP (Q ∪ {m}) (Sum.inr D.w₂) ≠ geoOwner hP (Q ∪ {m}) (Sum.inr D.w₃) := by
  have h := (CV.visits_separated_iff hP hSm D.w₂).mpr (Or.inr (r174c_w_mem_N_Sm D))
  rwa [D.twin_w₂] at h

theorem r174c_sep_m_Sm (hSm : Q ∪ {m} ∈ CV.Ind hP) :
    geoOwner hP (Q ∪ {m}) (Sum.inr D.m₁) ≠ geoOwner hP (Q ∪ {m}) (Sum.inr D.m₃) := by
  have h := (CV.visits_separated_iff hP hSm D.m₁).mpr (Or.inl r174c_m_mem_Sm)
  rwa [D.twin_m₁] at h

theorem r174c_sep_x_Sxw (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) :
    geoOwner hP (Q ∪ {x, w}) (Sum.inr D.x₁) ≠ geoOwner hP (Q ∪ {x, w}) (Sum.inr D.x₂) := by
  have h := (CV.visits_separated_iff hP hSxw D.x₁).mpr (Or.inl r174c_x_mem_Sxw)
  rwa [D.twin_x₁] at h

theorem r174c_sep_w_Sxw (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) :
    geoOwner hP (Q ∪ {x, w}) (Sum.inr D.w₂) ≠ geoOwner hP (Q ∪ {x, w}) (Sum.inr D.w₃) := by
  have h := (CV.visits_separated_iff hP hSxw D.w₂).mpr (Or.inl r174c_w_mem_Sxw)
  rwa [D.twin_w₂] at h

theorem r174c_sep_m_Sxw (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) :
    geoOwner hP (Q ∪ {x, w}) (Sum.inr D.m₁) ≠ geoOwner hP (Q ∪ {x, w}) (Sum.inr D.m₃) := by
  have h := (CV.visits_separated_iff hP hSxw D.m₁).mpr (Or.inr (r174c_m_mem_N_Sxw D))
  rwa [D.twin_m₁] at h

/-! #### The order at the corner -/

theorem r174c_param_x₁_ne_m₁ : visitParameter D.x₁ ≠ visitParameter D.m₁ :=
  s174_param_ne hP D.xm D.x1 D.m1

theorem r174c_param_x₂_ne_w₂ : visitParameter D.x₂ ≠ visitParameter D.w₂ :=
  s174_param_ne hP D.xw D.x2 D.w2

theorem r174c_param_w₃_ne_m₃ : visitParameter D.w₃ ≠ visitParameter D.m₃ :=
  s174_param_ne hP D.wm D.w3 D.m3

/-- **The two traversal directions at the corner `m`** (`s174_order` read on `P`): `x` precedes `m` on
`ℓ₁` iff `m` precedes `w` on `ℓ₃`. -/
theorem r174c_order₃ (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    visitParameter D.x₁ < visitParameter D.m₁ ↔ visitParameter D.m₃ < visitParameter D.w₃ := by
  have hc12 : IsCrossing P {ℓ₁, ℓ₂} := D.xval ▸ x.property
  have hc13 : IsCrossing P {ℓ₁, ℓ₃} := D.mval ▸ m.property
  have hc23 : IsCrossing P {ℓ₂, ℓ₃} := D.wval ▸ w.property
  have hxeq : x = xPair hc12 := Subtype.ext D.xval
  have hmeq : m = xPair hc13 := Subtype.ext D.mval
  have hweq : w = xPair hc23 := Subtype.ext D.wval
  have hord := s174_order hP hc12 hc13 hc23 hsgn D.sgn
  have e1 : visitParameter D.x₁ = crossingParameter (xPair hc12) ℓ₁ (mem_pair_left _ _) :=
    s174_param_congr hxeq _ _
  have e2 : visitParameter D.m₁ = crossingParameter (xPair hc13) ℓ₁ (mem_pair_left _ _) :=
    s174_param_congr hmeq _ _
  have e3 : visitParameter D.m₃ = crossingParameter (xPair hc13) ℓ₃ (mem_pair_right _ _) :=
    s174_param_congr hmeq _ _
  have e4 : visitParameter D.w₃ = crossingParameter (xPair hc23) ℓ₃ (mem_pair_right _ _) :=
    s174_param_congr hweq _ _
  have hne1 := r174c_param_x₁_ne_m₁ D
  have hne3 := r174c_param_w₃_ne_m₃ D
  rw [e1, e2] at hne1 ⊢
  rw [e3, e4] at hne3 ⊢
  constructor
  · intro h
    rcases lt_or_gt_of_ne hne3 with h3 | h3
    · exact absurd (hord.mpr h3) (not_lt.mpr h.le)
    · exact h3
  · intro h
    rcases lt_or_gt_of_ne hne1 with h1 | h1
    · exact h1
    · exact absurd (hord.mp h1) (not_lt.mpr h.le)


/-! #### The successors at the local visits (case A: `x` before `m` on `ℓ₁`, hence `m` before `w` on
`ℓ₃`; case B: the reverse) -/

variable (hn : 3 ≤ n)
include hn

theorem r174c_succ_x₁_A (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoMarkSuccessor hP (Sum.inr D.x₁) = Sum.inr D.m₁ :=
  r174c_succ_of_adjacent_lt hn hP D.adj1 rfl hA

theorem r174c_succ_m₃_A (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoMarkSuccessor hP (Sum.inr D.m₃) = Sum.inr D.w₃ :=
  r174c_succ_of_adjacent_lt hn hP (r174c_adjacent_symm hP D.adj3) rfl ((r174c_order₃ D hsgn).mp hA)

theorem r174c_succ_m₁_B (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoMarkSuccessor hP (Sum.inr D.m₁) = Sum.inr D.x₁ :=
  r174c_succ_of_adjacent_lt hn hP (r174c_adjacent_symm hP D.adj1) rfl hB

omit hn in
theorem r174c_order₃_B (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    visitParameter D.w₃ < visitParameter D.m₃ := by
  rcases lt_or_gt_of_ne (r174c_param_w₃_ne_m₃ D) with h | h
  · exact h
  · exact absurd ((r174c_order₃ D hsgn).mpr h) (not_lt.mpr hB.le)

theorem r174c_succ_w₃_B (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoMarkSuccessor hP (Sum.inr D.w₃) = Sum.inr D.m₃ :=
  r174c_succ_of_adjacent_lt hn hP D.adj3 rfl (r174c_order₃_B D hsgn hB)

/-! #### The centre row `Q ∪ {m}`: the carriers `C` (owning `x₁, w₃` and one visit of `m`) and `AB`
(owning `x₂, w₂` and the other visit of `m`) -/

omit hn in
/-- `C`, the carrier of `Q ∪ {m}` through the `ℓ₁`-visit of `x`. -/
def r174c_qC : GeoComponent hP (Q ∪ {m}) := geoOwner hP (Q ∪ {m}) (Sum.inr D.x₁)

omit hn in
/-- `AB`, the carrier of `Q ∪ {m}` through the `ℓ₂`-visit of `x`. -/
def r174c_qAB : GeoComponent hP (Q ∪ {m}) := geoOwner hP (Q ∪ {m}) (Sum.inr D.x₂)

omit hn in
theorem r174c_qC_x₁ : geoOwner hP (Q ∪ {m}) (Sum.inr D.x₁) = r174c_qC D := rfl
omit hn in
theorem r174c_qAB_x₂ : geoOwner hP (Q ∪ {m}) (Sum.inr D.x₂) = r174c_qAB D := rfl

omit hn in
theorem r174c_hCAB (hSm : Q ∪ {m} ∈ CV.Ind hP) : r174c_qC D ≠ r174c_qAB D :=
  r174c_sep_x_Sm D hSm

omit hn in
/-- `AB` owns `w₂` (adjacent unselected `ℓ₂`-visits). -/
theorem r174c_qAB_w₂ : geoOwner hP (Q ∪ {m}) (Sum.inr D.w₂) = r174c_qAB D :=
  (GT_owner_eq_of_adjacent hP _ D.adj2 rfl (r174c_x_not_mem_Sm D) (r174c_w_not_mem_Sm D)).symm

theorem r174c_qC_m₁_A (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoOwner hP (Q ∪ {m}) (Sum.inr D.m₁) = r174c_qC D := by
  unfold r174c_qC
  rw [← geoOwner_successor hP _ (Sum.inr D.x₁),
    geoSmoothingSuccessor_visit_of_not_mem hP _ D.x₁ (r174c_x_not_mem_Sm D), r174c_succ_x₁_A D hn hA]

theorem r174c_qC_w₃_A (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoOwner hP (Q ∪ {m}) (Sum.inr D.w₃) = r174c_qC D := by
  rw [← r174c_qC_m₁_A D hn hA, ← geoOwner_successor hP _ (Sum.inr D.m₁),
    geoSmoothingSuccessor_visit_of_mem hP (Q ∪ {m}) D.m₁ r174c_m_mem_Sm, D.twin_m₁, r174c_succ_m₃_A D hn hsgn hA]

theorem r174c_qC_m₃_B (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoOwner hP (Q ∪ {m}) (Sum.inr D.m₃) = r174c_qC D := by
  unfold r174c_qC
  rw [← geoOwner_successor hP _ (Sum.inr D.m₃),
    geoSmoothingSuccessor_visit_of_mem hP (Q ∪ {m}) D.m₃ r174c_m_mem_Sm, D.twin_m₃, r174c_succ_m₁_B D hn hB]

theorem r174c_qC_w₃_B (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoOwner hP (Q ∪ {m}) (Sum.inr D.w₃) = r174c_qC D := by
  rw [← r174c_qC_m₃_B D hn hB, ← geoOwner_successor hP _ (Sum.inr D.w₃),
    geoSmoothingSuccessor_visit_of_not_mem hP _ D.w₃ (r174c_w_not_mem_Sm D), r174c_succ_w₃_B D hn hsgn hB]

/-- `C` owns `w₃` in both cases. -/
theorem r174c_qC_w₃ (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    geoOwner hP (Q ∪ {m}) (Sum.inr D.w₃) = r174c_qC D := by
  rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with h | h
  · exact r174c_qC_w₃_A D hn hsgn h
  · exact r174c_qC_w₃_B D hn hsgn h

omit hn in
/-- **One visit of `m` lies on `AB`**: otherwise the `Q ∪ {m}`-carrier of `x₂` would avoid both
visits of `m`, hence be a carrier of `Q` as well — but on `Q` the visits `x₂, x₁, m₁` lie on one carrier
(`x ∈ U(Q)`, adjacency on `ℓ₁`). -/
theorem r174c_m_visit_qAB :
    geoOwner hP (Q ∪ {m}) (Sum.inr D.m₁) = r174c_qAB D ∨
      geoOwner hP (Q ∪ {m}) (Sum.inr D.m₃) = r174c_qAB D := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h3⟩ := hcon
  have hL : ∀ v : Visit P, geoOwner hP (Q ∪ {m}) (Sum.inr v) = geoOwner hP (Q ∪ {m}) (Sum.inr D.x₂) →
      (v.1 ∈ Q ∪ {m} ↔ v.1 ∈ Q) := by
    intro v hv
    by_cases hvm : v.1 = m
    · rcases visit_eq_or_twin D.m₁ v hvm with rfl | rfl
      · exact absurd hv h1
      · rw [D.twin_m₁] at hv
        exact absurd hv h3
    · simp only [Finset.mem_union, Finset.mem_singleton, hvm, or_false]
  have hQ : geoOwner hP Q (Sum.inr D.m₁) = geoOwner hP Q (Sum.inr D.x₂) := by
    rw [CV.owner_eq_of_mem_U hP D.Q_ind (r174c_x_mem_U_Q D) D.x₂ D.x₁ rfl rfl]
    exact (GT_owner_eq_of_adjacent hP Q D.adj1 rfl (r174c_x_not_mem_Q D) (r174c_m_not_mem_Q D)).symm
  exact h1 ((r174c_owner_iff_of_avoid hP (Q ∪ {m}) Q hL (Sum.inr D.m₁)).mpr hQ)

theorem r174c_qAB_m₃_A (hSm : Q ∪ {m} ∈ CV.Ind hP) (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoOwner hP (Q ∪ {m}) (Sum.inr D.m₃) = r174c_qAB D := by
  rcases r174c_m_visit_qAB D with h | h
  · exact absurd ((r174c_qC_m₁_A D hn hA).symm.trans h) (r174c_hCAB D hSm)
  · exact h

theorem r174c_qAB_m₁_B (hSm : Q ∪ {m} ∈ CV.Ind hP) (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoOwner hP (Q ∪ {m}) (Sum.inr D.m₁) = r174c_qAB D := by
  rcases r174c_m_visit_qAB D with h | h
  · exact h
  · exact absurd ((r174c_qC_m₃_B D hn hB).symm.trans h) (r174c_hCAB D hSm)

/-- **Every local visit lies on `C` or `AB`.** -/
theorem r174c_local_Sm (hSm : Q ∪ {m} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (v : Visit P) (hv : v.1 = x ∨ v.1 = w ∨ v.1 = m) :
    geoOwner hP (Q ∪ {m}) (Sum.inr v) = r174c_qC D ∨ geoOwner hP (Q ∪ {m}) (Sum.inr v) = r174c_qAB D := by
  rcases hv with hv | hv | hv
  · rcases visit_eq_or_twin D.x₁ v hv with rfl | rfl
    · exact Or.inl rfl
    · rw [D.twin_x₁]; exact Or.inr rfl
  · rcases visit_eq_or_twin D.w₂ v hv with rfl | rfl
    · exact Or.inr (r174c_qAB_w₂ D)
    · rw [D.twin_w₂]; exact Or.inl (r174c_qC_w₃ D hn hsgn)
  · rcases visit_eq_or_twin D.m₁ v hv with rfl | rfl
    · rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with h | h
      · exact Or.inl (r174c_qC_m₁_A D hn h)
      · exact Or.inr (r174c_qAB_m₁_B D hn hSm h)
    · rw [D.twin_m₁]
      rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with h | h
      · exact Or.inr (r174c_qAB_m₃_A D hn hSm h)
      · exact Or.inl (r174c_qC_m₃_B D hn h)

/-! #### The pair row `Q ∪ {x, w}`: the carriers `A` (through `m₁`), `B` (through `m₃`) and `C'` -/

omit hn in
/-- `A`, the carrier of `Q ∪ {x, w}` through the `ℓ₁`-visit of `m`. -/
def r174c_qA : GeoComponent hP (Q ∪ {x, w}) := geoOwner hP (Q ∪ {x, w}) (Sum.inr D.m₁)

omit hn in
/-- `B`, the carrier of `Q ∪ {x, w}` through the `ℓ₃`-visit of `m`. -/
def r174c_qB : GeoComponent hP (Q ∪ {x, w}) := geoOwner hP (Q ∪ {x, w}) (Sum.inr D.m₃)

omit hn in
open scoped Classical in
/-- `C'`, the third local carrier of `Q ∪ {x, w}`: through `x₁` (and `w₂`) when `x` precedes `m` on `ℓ₁`,
through `x₂` (and `w₃`) otherwise. -/
def r174c_qC' : GeoComponent hP (Q ∪ {x, w}) :=
  if visitParameter D.x₁ < visitParameter D.m₁ then geoOwner hP (Q ∪ {x, w}) (Sum.inr D.x₁)
  else geoOwner hP (Q ∪ {x, w}) (Sum.inr D.x₂)

omit hn in
theorem r174c_qA_m₁ : geoOwner hP (Q ∪ {x, w}) (Sum.inr D.m₁) = r174c_qA D := rfl
omit hn in
theorem r174c_qB_m₃ : geoOwner hP (Q ∪ {x, w}) (Sum.inr D.m₃) = r174c_qB D := rfl

omit hn in
theorem r174c_hAB (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) : r174c_qA D ≠ r174c_qB D :=
  r174c_sep_m_Sxw D hSxw

omit hn in
theorem r174c_qC'_A (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    r174c_qC' D = geoOwner hP (Q ∪ {x, w}) (Sum.inr D.x₁) := by
  unfold r174c_qC'; rw [ite_eq_left hA]

omit hn in
theorem r174c_qC'_B (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    r174c_qC' D = geoOwner hP (Q ∪ {x, w}) (Sum.inr D.x₂) := by
  unfold r174c_qC'; rw [ite_eq_right (not_lt.mpr hB.le)]

theorem r174c_qA_x₂_A (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoOwner hP (Q ∪ {x, w}) (Sum.inr D.x₂) = r174c_qA D := by
  unfold r174c_qA
  rw [← geoOwner_successor hP _ (Sum.inr D.x₂),
    geoSmoothingSuccessor_visit_of_mem hP (Q ∪ {x, w}) D.x₂ r174c_x_mem_Sxw, D.twin_x₂, r174c_succ_x₁_A D hn hA]

theorem r174c_qB_w₃_A (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoOwner hP (Q ∪ {x, w}) (Sum.inr D.w₃) = r174c_qB D := by
  unfold r174c_qB
  rw [← geoOwner_successor hP _ (Sum.inr D.m₃),
    geoSmoothingSuccessor_visit_of_not_mem hP _ D.m₃ (r174c_m_not_mem_Sxw D), r174c_succ_m₃_A D hn hsgn hA]

/-- In case A, `x` precedes `w` on `ℓ₂` (otherwise `w₃ → x₂ → m₁` would put `m₃` and `m₁` on one
carrier of `Q ∪ {x, w}`). -/
theorem r174c_order₂_A (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    visitParameter D.x₂ < visitParameter D.w₂ := by
  rcases lt_or_gt_of_ne (r174c_param_x₂_ne_w₂ D) with h | h
  · exact h
  · exfalso
    have hsucc : geoMarkSuccessor hP (Sum.inr D.w₂) = Sum.inr D.x₂ :=
      r174c_succ_of_adjacent_lt hn hP (r174c_adjacent_symm hP D.adj2) rfl h
    have h1 : geoOwner hP (Q ∪ {x, w}) (Sum.inr D.w₃) = geoOwner hP (Q ∪ {x, w}) (Sum.inr D.x₂) := by
      rw [← geoOwner_successor hP _ (Sum.inr D.w₃),
        geoSmoothingSuccessor_visit_of_mem hP (Q ∪ {x, w}) D.w₃ r174c_w_mem_Sxw, D.twin_w₃, hsucc]
    exact r174c_hAB D hSxw ((r174c_qA_x₂_A D hn hA).symm.trans (h1.symm.trans (r174c_qB_w₃_A D hn hsgn hA)))

theorem r174c_succ_x₂_A (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoMarkSuccessor hP (Sum.inr D.x₂) = Sum.inr D.w₂ :=
  r174c_succ_of_adjacent_lt hn hP D.adj2 rfl (r174c_order₂_A D hn hSxw hsgn hA)

theorem r174c_qC'_w₂_A (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoOwner hP (Q ∪ {x, w}) (Sum.inr D.w₂) = r174c_qC' D := by
  rw [r174c_qC'_A D hA, ← geoOwner_successor hP _ (Sum.inr D.x₁),
    geoSmoothingSuccessor_visit_of_mem hP (Q ∪ {x, w}) D.x₁ r174c_x_mem_Sxw, D.twin_x₁, r174c_succ_x₂_A D hn hSxw hsgn hA]

theorem r174c_qA_x₁_B (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoOwner hP (Q ∪ {x, w}) (Sum.inr D.x₁) = r174c_qA D := by
  unfold r174c_qA
  rw [← geoOwner_successor hP _ (Sum.inr D.m₁),
    geoSmoothingSuccessor_visit_of_not_mem hP _ D.m₁ (r174c_m_not_mem_Sxw D), r174c_succ_m₁_B D hn hB]

theorem r174c_qB_w₂_B (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoOwner hP (Q ∪ {x, w}) (Sum.inr D.w₂) = r174c_qB D := by
  unfold r174c_qB
  rw [← geoOwner_successor hP _ (Sum.inr D.w₂),
    geoSmoothingSuccessor_visit_of_mem hP (Q ∪ {x, w}) D.w₂ r174c_w_mem_Sxw, D.twin_w₂, r174c_succ_w₃_B D hn hsgn hB]

/-- In case B, `w` precedes `x` on `ℓ₂`. -/
theorem r174c_order₂_B (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    visitParameter D.w₂ < visitParameter D.x₂ := by
  rcases lt_or_gt_of_ne (r174c_param_x₂_ne_w₂ D) with h | h
  · exfalso
    have hsucc : geoMarkSuccessor hP (Sum.inr D.x₂) = Sum.inr D.w₂ :=
      r174c_succ_of_adjacent_lt hn hP D.adj2 rfl h
    have h1 : geoOwner hP (Q ∪ {x, w}) (Sum.inr D.x₁) = geoOwner hP (Q ∪ {x, w}) (Sum.inr D.w₂) := by
      rw [← geoOwner_successor hP _ (Sum.inr D.x₁),
        geoSmoothingSuccessor_visit_of_mem hP (Q ∪ {x, w}) D.x₁ r174c_x_mem_Sxw, D.twin_x₁, hsucc]
    exact r174c_hAB D hSxw ((r174c_qA_x₁_B D hn hB).symm.trans (h1.trans (r174c_qB_w₂_B D hn hsgn hB)))
  · exact h

theorem r174c_succ_w₂_B (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoMarkSuccessor hP (Sum.inr D.w₂) = Sum.inr D.x₂ :=
  r174c_succ_of_adjacent_lt hn hP (r174c_adjacent_symm hP D.adj2) rfl (r174c_order₂_B D hn hSxw hsgn hB)

theorem r174c_qC'_w₃_B (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoOwner hP (Q ∪ {x, w}) (Sum.inr D.w₃) = r174c_qC' D := by
  rw [r174c_qC'_B D hB, ← geoOwner_successor hP _ (Sum.inr D.w₃),
    geoSmoothingSuccessor_visit_of_mem hP (Q ∪ {x, w}) D.w₃ r174c_w_mem_Sxw, D.twin_w₃, r174c_succ_w₂_B D hn hSxw hsgn hB]

theorem r174c_hC'A (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) : r174c_qC' D ≠ r174c_qA D := by
  rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with h | h
  · rw [r174c_qC'_A D h, ← r174c_qA_x₂_A D hn h]
    exact r174c_sep_x_Sxw D hSxw
  · rw [r174c_qC'_B D h, ← r174c_qA_x₁_B D hn h]
    exact (r174c_sep_x_Sxw D hSxw).symm

theorem r174c_hC'B (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    r174c_qC' D ≠ r174c_qB D := by
  rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with h | h
  · rw [← r174c_qC'_w₂_A D hn hSxw hsgn h, ← r174c_qB_w₃_A D hn hsgn h]
    exact r174c_sep_w_Sxw D hSxw
  · rw [← r174c_qC'_w₃_B D hn hSxw hsgn h, ← r174c_qB_w₂_B D hn hsgn h]
    exact (r174c_sep_w_Sxw D hSxw).symm

/-- **Every local visit lies on `C'`, `A` or `B`.** -/
theorem r174c_local_Sxw (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (v : Visit P) (hv : v.1 = x ∨ v.1 = w ∨ v.1 = m) :
    geoOwner hP (Q ∪ {x, w}) (Sum.inr v) = r174c_qC' D ∨ geoOwner hP (Q ∪ {x, w}) (Sum.inr v) = r174c_qA D ∨
      geoOwner hP (Q ∪ {x, w}) (Sum.inr v) = r174c_qB D := by
  rcases hv with hv | hv | hv
  · rcases visit_eq_or_twin D.x₁ v hv with rfl | rfl
    · rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with h | h
      · exact Or.inl (r174c_qC'_A D h).symm
      · exact Or.inr (Or.inl (r174c_qA_x₁_B D hn h))
    · rw [D.twin_x₁]
      rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with h | h
      · exact Or.inr (Or.inl (r174c_qA_x₂_A D hn h))
      · exact Or.inl (r174c_qC'_B D h).symm
  · rcases visit_eq_or_twin D.w₂ v hv with rfl | rfl
    · rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with h | h
      · exact Or.inl (r174c_qC'_w₂_A D hn hSxw hsgn h)
      · exact Or.inr (Or.inr (r174c_qB_w₂_B D hn hsgn h))
    · rw [D.twin_w₂]
      rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with h | h
      · exact Or.inr (Or.inr (r174c_qB_w₃_A D hn hsgn h))
      · exact Or.inl (r174c_qC'_w₃_B D hn hSxw hsgn h)
  · rcases visit_eq_or_twin D.m₁ v hv with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · rw [D.twin_m₁]; exact Or.inr (Or.inr rfl)


/-! #### Spectators: a carrier of `Q ∪ {m}` other than `C, AB` avoids every local visit, hence is the
same cycle of marks in `Q ∪ {x, w}` (and conversely for a carrier other than `C', A, B`) -/

theorem r174c_avoid_m (hSm : Q ∪ {m} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (a : Mark P) (h1 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qAB D) (h2 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qC D)
    (v : Visit P) (hv : geoOwner hP (Q ∪ {m}) (Sum.inr v) = geoOwner hP (Q ∪ {m}) a) :
    v.1 ∈ Q ∪ {m} ↔ v.1 ∈ Q ∪ {x, w} := by
  by_cases hloc : v.1 = x ∨ v.1 = w ∨ v.1 = m
  · rcases r174c_local_Sm D hn hSm hsgn v hloc with h | h
    · exact absurd (hv.symm.trans h) h2
    · exact absurd (hv.symm.trans h) h1
  · simp only [not_or] at hloc
    exact r174c_mem_iff_of_outside hloc.1 hloc.2.1 hloc.2.2

/-- **A spectator carrier of the centre row is literally a carrier of the pair row.** -/
theorem r174c_owner_iff_m (hSm : Q ∪ {m} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (a : Mark P) (h1 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qAB D) (h2 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qC D)
    (b : Mark P) :
    geoOwner hP (Q ∪ {m}) b = geoOwner hP (Q ∪ {m}) a ↔
      geoOwner hP (Q ∪ {x, w}) b = geoOwner hP (Q ∪ {x, w}) a :=
  r174c_owner_iff_of_avoid hP _ _ (r174c_avoid_m D hn hSm hsgn a h1 h2) b

theorem r174c_avoid_xw (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (a : Mark P) (h1 : geoOwner hP (Q ∪ {x, w}) a ≠ r174c_qA D) (h2 : geoOwner hP (Q ∪ {x, w}) a ≠ r174c_qB D)
    (h3 : geoOwner hP (Q ∪ {x, w}) a ≠ r174c_qC' D)
    (v : Visit P) (hv : geoOwner hP (Q ∪ {x, w}) (Sum.inr v) = geoOwner hP (Q ∪ {x, w}) a) :
    v.1 ∈ Q ∪ {x, w} ↔ v.1 ∈ Q ∪ {m} := by
  by_cases hloc : v.1 = x ∨ v.1 = w ∨ v.1 = m
  · rcases r174c_local_Sxw D hn hSxw hsgn v hloc with h | h | h
    · exact absurd (hv.symm.trans h) h3
    · exact absurd (hv.symm.trans h) h1
    · exact absurd (hv.symm.trans h) h2
  · simp only [not_or] at hloc
    exact (r174c_mem_iff_of_outside hloc.1 hloc.2.1 hloc.2.2).symm

/-- **A spectator carrier of the pair row is literally a carrier of the centre row.** -/
theorem r174c_owner_iff_xw (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (a : Mark P) (h1 : geoOwner hP (Q ∪ {x, w}) a ≠ r174c_qA D) (h2 : geoOwner hP (Q ∪ {x, w}) a ≠ r174c_qB D)
    (h3 : geoOwner hP (Q ∪ {x, w}) a ≠ r174c_qC' D) (b : Mark P) :
    geoOwner hP (Q ∪ {x, w}) b = geoOwner hP (Q ∪ {x, w}) a ↔
      geoOwner hP (Q ∪ {m}) b = geoOwner hP (Q ∪ {m}) a :=
  r174c_owner_iff_of_avoid hP _ _ (r174c_avoid_xw D hn hSxw hsgn a h1 h2 h3) b

/-- a spectator of the centre row owns no local visit in the pair row either -/
theorem r174c_owner_xw_ne_of_spectator (hSm : Q ∪ {m} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (a : Mark P) (h1 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qAB D) (h2 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qC D)
    (v : Visit P) (hv : v.1 = x ∨ v.1 = w ∨ v.1 = m) :
    geoOwner hP (Q ∪ {x, w}) a ≠ geoOwner hP (Q ∪ {x, w}) (Sum.inr v) := by
  intro h
  have h' := (r174c_owner_iff_m D hn hSm hsgn a h1 h2 (Sum.inr v)).mpr h.symm
  rcases r174c_local_Sm D hn hSm hsgn v hv with hc | hc
  · exact h2 (h'.symm.trans hc)
  · exact h1 (h'.symm.trans hc)

/-- a spectator of the pair row owns no local visit in the centre row either -/
theorem r174c_owner_m_ne_of_spectator (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (a : Mark P) (h1 : geoOwner hP (Q ∪ {x, w}) a ≠ r174c_qA D) (h2 : geoOwner hP (Q ∪ {x, w}) a ≠ r174c_qB D)
    (h3 : geoOwner hP (Q ∪ {x, w}) a ≠ r174c_qC' D) (v : Visit P) (hv : v.1 = x ∨ v.1 = w ∨ v.1 = m) :
    geoOwner hP (Q ∪ {m}) a ≠ geoOwner hP (Q ∪ {m}) (Sum.inr v) := by
  intro h
  have h' := (r174c_owner_iff_xw D hn hSxw hsgn a h1 h2 h3 (Sum.inr v)).mpr h.symm
  rcases r174c_local_Sxw D hn hSxw hsgn v hv with hc | hc | hc
  · exact h3 (h'.symm.trans hc)
  · exact h1 (h'.symm.trans hc)
  · exact h2 (h'.symm.trans hc)

/-! #### The bijection `ρ : carriers(Q ∪ {m}) ≃ carriers(Q ∪ {x, w}) ∖ {B}` -/

omit hn in
open scoped Classical in
/-- the forward map on marks: `AB ↦ A`, `C ↦ C'`, a spectator to its own cycle -/
def r174c_fwdMark (a : Mark P) : GeoComponent hP (Q ∪ {x, w}) :=
  if geoOwner hP (Q ∪ {m}) a = r174c_qAB D then r174c_qA D
  else if geoOwner hP (Q ∪ {m}) a = r174c_qC D then r174c_qC' D
  else geoOwner hP (Q ∪ {x, w}) a

omit hn in
theorem r174c_fwdMark_of_qAB (a : Mark P) (h : geoOwner hP (Q ∪ {m}) a = r174c_qAB D) :
    r174c_fwdMark D a = r174c_qA D := by
  unfold r174c_fwdMark; rw [ite_eq_left h]

omit hn in
theorem r174c_fwdMark_of_qC (a : Mark P) (h1 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qAB D)
    (h2 : geoOwner hP (Q ∪ {m}) a = r174c_qC D) : r174c_fwdMark D a = r174c_qC' D := by
  unfold r174c_fwdMark; rw [ite_eq_right h1, ite_eq_left h2]

omit hn in
theorem r174c_fwdMark_of_ne (a : Mark P) (h1 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qAB D)
    (h2 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qC D) : r174c_fwdMark D a = geoOwner hP (Q ∪ {x, w}) a := by
  unfold r174c_fwdMark; rw [ite_eq_right h1, ite_eq_right h2]

theorem r174c_fwdMark_congr (hSm : Q ∪ {m} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (a b : Mark P) (hab : geoOwner hP (Q ∪ {m}) b = geoOwner hP (Q ∪ {m}) a) :
    r174c_fwdMark D b = r174c_fwdMark D a := by
  by_cases h1 : geoOwner hP (Q ∪ {m}) a = r174c_qAB D
  · rw [r174c_fwdMark_of_qAB D a h1, r174c_fwdMark_of_qAB D b (hab.trans h1)]
  by_cases h2 : geoOwner hP (Q ∪ {m}) a = r174c_qC D
  · rw [r174c_fwdMark_of_qC D a h1 h2, r174c_fwdMark_of_qC D b (fun h => h1 (hab.symm.trans h)) (hab.trans h2)]
  rw [r174c_fwdMark_of_ne D a h1 h2, r174c_fwdMark_of_ne D b (fun h => h1 (hab.symm.trans h))
    (fun h => h2 (hab.symm.trans h))]
  exact (r174c_owner_iff_m D hn hSm hsgn a h1 h2 b).mp hab

/-- the forward map on carriers -/
def r174c_fwd (hSm : Q ∪ {m} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    GeoComponent hP (Q ∪ {m}) → GeoComponent hP (Q ∪ {x, w}) :=
  Quotient.lift (r174c_fwdMark D) (fun a b hab =>
    r174c_fwdMark_congr D hn hSm hsgn b a ((geoOwner_eq_iff hP _ a b).mpr hab))

theorem r174c_fwd_owner (hSm : Q ∪ {m} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (a : Mark P) : r174c_fwd D hn hSm hsgn (geoOwner hP (Q ∪ {m}) a) = r174c_fwdMark D a := rfl

omit hn in
open scoped Classical in
/-- the backward map on marks: `A, B ↦ AB`, `C' ↦ C`, a spectator to its own cycle -/
def r174c_bwdMark (a : Mark P) : GeoComponent hP (Q ∪ {m}) :=
  if geoOwner hP (Q ∪ {x, w}) a = r174c_qA D ∨ geoOwner hP (Q ∪ {x, w}) a = r174c_qB D then r174c_qAB D
  else if geoOwner hP (Q ∪ {x, w}) a = r174c_qC' D then r174c_qC D
  else geoOwner hP (Q ∪ {m}) a

omit hn in
theorem r174c_bwdMark_of_AB (a : Mark P)
    (h : geoOwner hP (Q ∪ {x, w}) a = r174c_qA D ∨ geoOwner hP (Q ∪ {x, w}) a = r174c_qB D) :
    r174c_bwdMark D a = r174c_qAB D := by
  unfold r174c_bwdMark; rw [ite_eq_left h]

omit hn in
theorem r174c_bwdMark_of_C' (a : Mark P)
    (h1 : ¬ (geoOwner hP (Q ∪ {x, w}) a = r174c_qA D ∨ geoOwner hP (Q ∪ {x, w}) a = r174c_qB D))
    (h2 : geoOwner hP (Q ∪ {x, w}) a = r174c_qC' D) : r174c_bwdMark D a = r174c_qC D := by
  unfold r174c_bwdMark; rw [ite_eq_right h1, ite_eq_left h2]

omit hn in
theorem r174c_bwdMark_of_ne (a : Mark P)
    (h1 : ¬ (geoOwner hP (Q ∪ {x, w}) a = r174c_qA D ∨ geoOwner hP (Q ∪ {x, w}) a = r174c_qB D))
    (h2 : geoOwner hP (Q ∪ {x, w}) a ≠ r174c_qC' D) : r174c_bwdMark D a = geoOwner hP (Q ∪ {m}) a := by
  unfold r174c_bwdMark; rw [ite_eq_right h1, ite_eq_right h2]

theorem r174c_bwdMark_congr (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (a b : Mark P) (hab : geoOwner hP (Q ∪ {x, w}) b = geoOwner hP (Q ∪ {x, w}) a) :
    r174c_bwdMark D b = r174c_bwdMark D a := by
  by_cases h1 : geoOwner hP (Q ∪ {x, w}) a = r174c_qA D ∨ geoOwner hP (Q ∪ {x, w}) a = r174c_qB D
  · rw [r174c_bwdMark_of_AB D a h1, r174c_bwdMark_of_AB D b (by rw [hab]; exact h1)]
  by_cases h2 : geoOwner hP (Q ∪ {x, w}) a = r174c_qC' D
  · rw [r174c_bwdMark_of_C' D a h1 h2, r174c_bwdMark_of_C' D b (by rw [hab]; exact h1) (hab.trans h2)]
  rw [r174c_bwdMark_of_ne D a h1 h2, r174c_bwdMark_of_ne D b (by rw [hab]; exact h1) (fun h => h2 (hab.symm.trans h))]
  rw [not_or] at h1
  exact (r174c_owner_iff_xw D hn hSxw hsgn a h1.1 h1.2 h2 b).mp hab

/-- the backward map on carriers -/
def r174c_bwd (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    GeoComponent hP (Q ∪ {x, w}) → GeoComponent hP (Q ∪ {m}) :=
  Quotient.lift (r174c_bwdMark D) (fun a b hab =>
    r174c_bwdMark_congr D hn hSxw hsgn b a ((geoOwner_eq_iff hP _ a b).mpr hab))

theorem r174c_bwd_owner (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (a : Mark P) : r174c_bwd D hn hSxw hsgn (geoOwner hP (Q ∪ {x, w}) a) = r174c_bwdMark D a := rfl

/-- `B` is not in the image of the forward map. -/
theorem r174c_fwd_ne_qB (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (q : GeoComponent hP (Q ∪ {m})) :
    r174c_fwd D hn hSm hsgn q ≠ r174c_qB D := by
  induction q using Quotient.inductionOn with
  | h a =>
    change r174c_fwd D hn hSm hsgn (geoOwner hP (Q ∪ {m}) a) ≠ r174c_qB D
    rw [r174c_fwd_owner]
    by_cases h1 : geoOwner hP (Q ∪ {m}) a = r174c_qAB D
    · rw [r174c_fwdMark_of_qAB D a h1]; exact r174c_hAB D hSxw
    by_cases h2 : geoOwner hP (Q ∪ {m}) a = r174c_qC D
    · rw [r174c_fwdMark_of_qC D a h1 h2]; exact r174c_hC'B D hn hSxw hsgn
    rw [r174c_fwdMark_of_ne D a h1 h2]
    exact r174c_owner_xw_ne_of_spectator D hn hSm hsgn a h1 h2 D.m₃ (Or.inr (Or.inr rfl))

theorem r174c_bwd_fwd (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (q : GeoComponent hP (Q ∪ {m})) :
    r174c_bwd D hn hSxw hsgn (r174c_fwd D hn hSm hsgn q) = q := by
  induction q using Quotient.inductionOn with
  | h a =>
    change r174c_bwd D hn hSxw hsgn (r174c_fwd D hn hSm hsgn (geoOwner hP (Q ∪ {m}) a)) = geoOwner hP (Q ∪ {m}) a
    rw [r174c_fwd_owner]
    by_cases h1 : geoOwner hP (Q ∪ {m}) a = r174c_qAB D
    · rw [r174c_fwdMark_of_qAB D a h1, ← r174c_qA_m₁ D, r174c_bwd_owner,
        r174c_bwdMark_of_AB D _ (Or.inl rfl), h1]
    by_cases h2 : geoOwner hP (Q ∪ {m}) a = r174c_qC D
    · rw [r174c_fwdMark_of_qC D a h1 h2, h2]
      have hnot : ∀ c : Mark P, geoOwner hP (Q ∪ {x, w}) c = r174c_qC' D →
          ¬ (geoOwner hP (Q ∪ {x, w}) c = r174c_qA D ∨ geoOwner hP (Q ∪ {x, w}) c = r174c_qB D) := by
        intro c hc
        rw [hc, not_or]
        exact ⟨r174c_hC'A D hn hSxw, r174c_hC'B D hn hSxw hsgn⟩
      rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with hA | hB
      · rw [r174c_qC'_A D hA, r174c_bwd_owner, r174c_bwdMark_of_C' D _ (hnot _ (r174c_qC'_A D hA).symm)
          (r174c_qC'_A D hA).symm]
      · rw [r174c_qC'_B D hB, r174c_bwd_owner, r174c_bwdMark_of_C' D _ (hnot _ (r174c_qC'_B D hB).symm)
          (r174c_qC'_B D hB).symm]
    rw [r174c_fwdMark_of_ne D a h1 h2, r174c_bwd_owner, r174c_bwdMark_of_ne D a ?_ ?_]
    · rw [not_or]
      exact ⟨r174c_owner_xw_ne_of_spectator D hn hSm hsgn a h1 h2 D.m₁ (Or.inr (Or.inr rfl)),
        r174c_owner_xw_ne_of_spectator D hn hSm hsgn a h1 h2 D.m₃ (Or.inr (Or.inr rfl))⟩
    · rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with hA | hB
      · rw [r174c_qC'_A D hA]
        exact r174c_owner_xw_ne_of_spectator D hn hSm hsgn a h1 h2 D.x₁ (Or.inl rfl)
      · rw [r174c_qC'_B D hB]
        exact r174c_owner_xw_ne_of_spectator D hn hSm hsgn a h1 h2 D.x₂ (Or.inl rfl)

theorem r174c_fwd_bwd (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (q' : GeoComponent hP (Q ∪ {x, w}))
    (hq' : q' ≠ r174c_qB D) :
    r174c_fwd D hn hSm hsgn (r174c_bwd D hn hSxw hsgn q') = q' := by
  induction q' using Quotient.inductionOn with
  | h a =>
    change r174c_fwd D hn hSm hsgn (r174c_bwd D hn hSxw hsgn (geoOwner hP (Q ∪ {x, w}) a)) =
      geoOwner hP (Q ∪ {x, w}) a
    have hq'' : geoOwner hP (Q ∪ {x, w}) a ≠ r174c_qB D := hq'
    rw [r174c_bwd_owner]
    by_cases h1 : geoOwner hP (Q ∪ {x, w}) a = r174c_qA D ∨ geoOwner hP (Q ∪ {x, w}) a = r174c_qB D
    · have hA : geoOwner hP (Q ∪ {x, w}) a = r174c_qA D := by
        rcases h1 with h | h
        · exact h
        · exact absurd h hq''
      rw [r174c_bwdMark_of_AB D a h1, ← r174c_qAB_x₂ D, r174c_fwd_owner,
        r174c_fwdMark_of_qAB D _ rfl, hA]
    by_cases h2 : geoOwner hP (Q ∪ {x, w}) a = r174c_qC' D
    · rw [r174c_bwdMark_of_C' D a h1 h2, ← r174c_qC_x₁ D, r174c_fwd_owner,
        r174c_fwdMark_of_qC D _ (r174c_hCAB D hSm) rfl, h2]
    rw [not_or] at h1
    rw [r174c_bwdMark_of_ne D a (not_or.mpr h1) h2, r174c_fwd_owner, r174c_fwdMark_of_ne D a ?_ ?_]
    · exact r174c_owner_m_ne_of_spectator D hn hSxw hsgn a h1.1 h1.2 h2 D.x₂ (Or.inl rfl)
    · exact r174c_owner_m_ne_of_spectator D hn hSxw hsgn a h1.1 h1.2 h2 D.x₁ (Or.inl rfl)

/-- **The carrier bijection `ρ` of `gsc_Ledger`**: the carriers of the centre row `Q ∪ {m}` against
those of the pair row `Q ∪ {x, w}` other than `B` — `AB ↦ A`, `C ↦ C'`, every spectator to itself. -/
def r174c_ρ (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    GeoComponent hP (Q ∪ {m}) ≃ {q' : GeoComponent hP (Q ∪ {x, w}) // q' ≠ r174c_qB D} where
  toFun q := ⟨r174c_fwd D hn hSm hsgn q, r174c_fwd_ne_qB D hn hSm hSxw hsgn q⟩
  invFun q' := r174c_bwd D hn hSxw hsgn q'.1
  left_inv := r174c_bwd_fwd D hn hSm hSxw hsgn
  right_inv q' := Subtype.ext (r174c_fwd_bwd D hn hSm hSxw hsgn q'.1 q'.2)

theorem r174c_ρ_apply (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (a : Mark P) :
    (r174c_ρ D hn hSm hSxw hsgn (geoOwner hP (Q ∪ {m}) a)).1 = r174c_fwdMark D a := rfl

/-- `ρ AB = A`. -/
theorem r174c_ρ_AB (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    (r174c_ρ D hn hSm hSxw hsgn (r174c_qAB D)).1 = r174c_qA D := by
  rw [← r174c_qAB_x₂ D, r174c_ρ_apply]
  exact r174c_fwdMark_of_qAB D _ rfl

/-- `ρ C = C'`. -/
theorem r174c_ρ_C (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    (r174c_ρ D hn hSm hSxw hsgn (r174c_qC D)).1 = r174c_qC' D := by
  rw [← r174c_qC_x₁ D, r174c_ρ_apply]
  exact r174c_fwdMark_of_qC D _ (r174c_hCAB D hSm) rfl

/-- a spectator goes to its own cycle -/
theorem r174c_ρ_spectator (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (a : Mark P)
    (h1 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qAB D) (h2 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qC D) :
    (r174c_ρ D hn hSm hSxw hsgn (geoOwner hP (Q ∪ {m}) a)).1 = geoOwner hP (Q ∪ {x, w}) a := by
  rw [r174c_ρ_apply]
  exact r174c_fwdMark_of_ne D a h1 h2


/-! #### Spectator reads at the geometric level: corner list, corner polygon, selector, retained crossings -/

/-- The corners of a spectator are the same marks in the same inherited order. -/
theorem r174c_cornerList_spectator (hSm : Q ∪ {m} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (a : Mark P)
    (h1 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qAB D) (h2 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qC D) :
    geoComponentCornerList hP (Q ∪ {x, w}) (geoOwner hP (Q ∪ {x, w}) a) =
      geoComponentCornerList hP (Q ∪ {m}) (geoOwner hP (Q ∪ {m}) a) := by
  have key : ∀ b : Mark P,
      (IsTrueCorner (Q ∪ {x, w}) b ∧ geoOwner hP (Q ∪ {x, w}) b = geoOwner hP (Q ∪ {x, w}) a) ↔
        (IsTrueCorner (Q ∪ {m}) b ∧ geoOwner hP (Q ∪ {m}) b = geoOwner hP (Q ∪ {m}) a) := by
    intro b
    rw [r174c_owner_iff_m D hn hSm hsgn a h1 h2 b]
    refine and_congr_left fun hb => ?_
    cases b with
    | inl i => exact Iff.rfl
    | inr v =>
      have hv := (r174c_owner_iff_m D hn hSm hsgn a h1 h2 (Sum.inr v)).mpr hb
      exact (r174c_avoid_m D hn hSm hsgn a h1 h2 v hv).symm
  unfold geoComponentCornerList geoComponentMarkList
  rw [List.filter_filter, List.filter_filter]
  refine List.filter_congr fun b _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact key b

theorem r174c_cornerCount_spectator (hSm : Q ∪ {m} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (a : Mark P)
    (h1 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qAB D) (h2 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qC D) :
    geoCornerCount hP (Q ∪ {x, w}) (geoOwner hP (Q ∪ {x, w}) a) =
      geoCornerCount hP (Q ∪ {m}) (geoOwner hP (Q ∪ {m}) a) := by
  unfold geoCornerCount
  rw [r174c_cornerList_spectator D hn hSm hsgn a h1 h2]

/-- The corner polygon of a spectator is the same polygon (up to the recast of its size). -/
theorem r174c_cornerPolygon_spectator (hSm : Q ∪ {m} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (a : Mark P)
    (h1 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qAB D) (h2 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qC D) :
    geoCornerPolygon hP (Q ∪ {x, w}) (geoOwner hP (Q ∪ {x, w}) a) =
      geoRecast (r174c_cornerCount_spectator D hn hSm hsgn a h1 h2)
        (geoCornerPolygon hP (Q ∪ {m}) (geoOwner hP (Q ∪ {m}) a)) := by
  funext j
  rw [geoRecast_apply]
  unfold geoCornerPolygon
  have hmark : geoCornerMark hP (Q ∪ {x, w}) (geoOwner hP (Q ∪ {x, w}) a) j =
      geoCornerMark hP (Q ∪ {m}) (geoOwner hP (Q ∪ {m}) a)
        (Equiv.cast (congrArg ZMod (r174c_cornerCount_spectator D hn hSm hsgn a h1 h2)) j) := by
    unfold geoCornerMark
    exact geo_getElem_congr _ _ (r174c_cornerList_spectator D hn hSm hsgn a h1 h2) _ _ _ _
      (geo_zmod_val_cast (r174c_cornerCount_spectator D hn hSm hsgn a h1 h2) j).symm
  rw [hmark]

/-- The selector (`wt`) of a spectator is unchanged. -/
theorem r174c_selector_spectator (hSm : Q ∪ {m} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (a : Mark P)
    (h1 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qAB D) (h2 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qC D) :
    geoCarrierSelector hP (Q ∪ {x, w}) (geoOwner hP (Q ∪ {x, w}) a) =
      geoCarrierSelector hP (Q ∪ {m}) (geoOwner hP (Q ∪ {m}) a) := by
  unfold geoCarrierSelector
  rw [r174c_cornerPolygon_spectator D hn hSm hsgn a h1 h2, cornerSelector_geoRecast]

/-- The retained crossings of a spectator are unchanged. -/
theorem r174c_retained_spectator (hSm : Q ∪ {m} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (a : Mark P)
    (h1 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qAB D) (h2 : geoOwner hP (Q ∪ {m}) a ≠ r174c_qC D) :
    geoCarrierCrossings hP (Q ∪ {x, w}) (geoOwner hP (Q ∪ {x, w}) a) =
      geoCarrierCrossings hP (Q ∪ {m}) (geoOwner hP (Q ∪ {m}) a) := by
  ext c
  rw [mem_geoCarrierCrossings, mem_geoCarrierCrossings]
  constructor
  · rintro ⟨hc, hall⟩
    refine ⟨fun hcm => ?_, fun v hv => (r174c_owner_iff_m D hn hSm hsgn a h1 h2 (Sum.inr v)).mpr (hall v hv)⟩
    rcases Finset.mem_union.mp hcm with hQ | hm'
    · exact hc (Finset.mem_union_left _ hQ)
    · have hcm' : c = m := Finset.mem_singleton.mp hm'
      exact r174c_owner_xw_ne_of_spectator D hn hSm hsgn a h1 h2 D.m₁ (Or.inr (Or.inr rfl))
        (hall D.m₁ hcm'.symm).symm
  · rintro ⟨hc, hall⟩
    refine ⟨fun hcxw => ?_, fun v hv => (r174c_owner_iff_m D hn hSm hsgn a h1 h2 (Sum.inr v)).mp (hall v hv)⟩
    rcases Finset.mem_union.mp hcxw with hQ | hxw
    · exact hc (Finset.mem_union_left _ hQ)
    · rcases Finset.mem_insert.mp hxw with hcx | hcw
      · exact h2 (hall D.x₁ hcx.symm).symm
      · have hcw' : c = w := Finset.mem_singleton.mp hcw
        exact h1 ((hall D.w₂ hcw'.symm).symm.trans (r174c_qAB_w₂ D))

end R174CLocal

/-! ### 4. The spectator reads of def:X1 (`wt`, `Ω₁`) and the item-1 bundle of `gsc_Ledger` -/

section R174CReads

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

omit [NeZero n] in
theorem r174c_map_refl (X : Finset (Crossing P)) :
    X.map (crossingTransport (fun _ => Iff.rfl : ∀ s, IsCrossing P s ↔ IsCrossing P s)).toEmbedding = X := by
  ext c
  rw [Finset.mem_map_equiv]
  exact Iff.rfl

variable {P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hG.crossingGeometry hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
  (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
  (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)

include hn hG D hSm hSxw hsgn

/-- The grouped diagrams of a spectator in the two rows have the same polynomial: same retained
crossings, same visit order and same divide signs on ONE polygon (`EXT_homfly_wall` with the identity
transport, CV:ax:gausscode). -/
theorem r174c_homfly_spectator (a : Mark P)
    (h1 : geoOwner hG.crossingGeometry (Q ∪ {m}) a ≠ r174c_qAB D)
    (h2 : geoOwner hG.crossingGeometry (Q ∪ {m}) a ≠ r174c_qC D) :
    homfly (CV.carrierDiagram hn hG hSxw (geoOwner hG.crossingGeometry (Q ∪ {x, w}) a)) =
      homfly (CV.carrierDiagram hn hG hSm (geoOwner hG.crossingGeometry (Q ∪ {m}) a)) := by
  unfold CV.carrierDiagram
  refine EXT_homfly_wall hn _ _ (fun _ => Iff.rfl) _ _ _ _ ?_ ?_ ?_
  · rw [r174c_map_refl]
    exact r174c_retained_spectator D hn hSm hsgn a h1 h2
  · intro v w _ _
    exact Iff.rfl
  · intro v _
    exact Iff.rfl

theorem r174c_groupedPoly_spectator (a : Mark P)
    (h1 : geoOwner hG.crossingGeometry (Q ∪ {m}) a ≠ r174c_qAB D)
    (h2 : geoOwner hG.crossingGeometry (Q ∪ {m}) a ≠ r174c_qC D) :
    CV.groupedPoly hn hG hSxw (geoOwner hG.crossingGeometry (Q ∪ {x, w}) a) =
      CV.groupedPoly hn hG hSm (geoOwner hG.crossingGeometry (Q ∪ {m}) a) := by
  rw [GT_groupedPoly_eq_homfly, GT_groupedPoly_eq_homfly]
  exact r174c_homfly_spectator hn hG D hSm hSxw hsgn a h1 h2

theorem r174c_carrierR_spectator (a : Mark P)
    (h1 : geoOwner hG.crossingGeometry (Q ∪ {m}) a ≠ r174c_qAB D)
    (h2 : geoOwner hG.crossingGeometry (Q ∪ {m}) a ≠ r174c_qC D) :
    CV.carrierR hn hG hSxw (geoOwner hG.crossingGeometry (Q ∪ {x, w}) a) =
      CV.carrierR hn hG hSm (geoOwner hG.crossingGeometry (Q ∪ {m}) a) := by
  unfold CV.carrierR CV.rotAbs
  congr 1
  apply Int.cast_injective (α := ℝ)
  rw [CV.rot_eq_rotationNumber, CV.rot_eq_rotationNumber,
    r174c_cornerPolygon_spectator D hn hSm hsgn a h1 h2, rotationNumber_geoRecast]

theorem r174c_Omega1_spectator (a : Mark P)
    (h1 : geoOwner hG.crossingGeometry (Q ∪ {m}) a ≠ r174c_qAB D)
    (h2 : geoOwner hG.crossingGeometry (Q ∪ {m}) a ≠ r174c_qC D) :
    CV.Omega1 hn hG hSxw (geoOwner hG.crossingGeometry (Q ∪ {x, w}) a) =
      CV.Omega1 hn hG hSm (geoOwner hG.crossingGeometry (Q ∪ {m}) a) := by
  unfold CV.Omega1 CV.slot
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG hSxw,
    CV.groupedWrithe_eq_card_geoCarrierCrossings hG hSm,
    r174c_retained_spectator D hn hSm hsgn a h1 h2, r174c_carrierR_spectator hn hG D hSm hSxw hsgn a h1 h2,
    r174c_groupedPoly_spectator hn hG D hSm hSxw hsgn a h1 h2]

/-- **`gsc_Ledger.spectator_weight`** for the bijection `r174c_ρ`. -/
theorem r174c_spectator_weight (q : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (h1 : q ≠ r174c_qAB D) (h2 : q ≠ r174c_qC D) :
    CV.weight hG.crossingGeometry (Q ∪ {x, w}) (r174c_ρ D hn hSm hSxw hsgn q).1 =
      CV.weight hG.crossingGeometry (Q ∪ {m}) q := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective hG.crossingGeometry _ q
  rw [r174c_ρ_spectator D hn hSm hSxw hsgn a h1 h2]
  unfold CV.weight
  exact r174c_selector_spectator D hn hSm hsgn a h1 h2

/-- **`gsc_Ledger.spectator_omega`** for the bijection `r174c_ρ`. -/
theorem r174c_spectator_omega (q : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (h1 : q ≠ r174c_qAB D) (h2 : q ≠ r174c_qC D) :
    CV.Omega1 hn hG hSxw (r174c_ρ D hn hSm hSxw hsgn q).1 = CV.Omega1 hn hG hSm q := by
  obtain ⟨a, rfl⟩ := geoOwner_surjective hG.crossingGeometry _ q
  rw [r174c_ρ_spectator D hn hSm hSxw hsgn a h1 h2]
  exact r174c_Omega1_spectator hn hG D hSm hSxw hsgn a h1 h2

end R174CReads

/-! ### 5. The item-1 bundle: the carrier fields of `gsc_Ledger`, realised -/

section R174CBundle

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-- **The carrier fields of `gsc_Ledger` (GSC §1 (2)), as one bundle**: field for field the ledger's
`qC qAB hCAB qC' qA qB hC'A hC'B hAB ρ ρ_AB ρ_C spectator_weight spectator_omega` (same statements,
same order), on the binders of `gsc_Ledger`. -/
structure r174c_CarrierData (hn : 3 ≤ n) (hG : CV.Generic P) (Q : Finset (Crossing P)) (m x w : Crossing P)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry) where
  qC : GeoComponent hG.crossingGeometry (Q ∪ {m})
  qAB : GeoComponent hG.crossingGeometry (Q ∪ {m})
  hCAB : qC ≠ qAB
  qC' : GeoComponent hG.crossingGeometry (Q ∪ {x, w})
  qA : GeoComponent hG.crossingGeometry (Q ∪ {x, w})
  qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w})
  hC'A : qC' ≠ qA
  hC'B : qC' ≠ qB
  hAB : qA ≠ qB
  ρ : GeoComponent hG.crossingGeometry (Q ∪ {m}) ≃
    {q' : GeoComponent hG.crossingGeometry (Q ∪ {x, w}) // q' ≠ qB}
  ρ_AB : (ρ qAB).1 = qA
  ρ_C : (ρ qC).1 = qC'
  spectator_weight : ∀ q, q ≠ qAB → q ≠ qC →
    CV.weight hG.crossingGeometry (Q ∪ {x, w}) (ρ q).1 = CV.weight hG.crossingGeometry (Q ∪ {m}) q
  spectator_omega : ∀ q, q ≠ qAB → q ≠ qC → CV.Omega1 hn hG hSxw (ρ q).1 = CV.Omega1 hn hG hSm q

variable {P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

/-- **Item 1 of `gsc_Ledger` is realised** on every `GT_Endpoint` configuration in the canonical sign
branch: `qC = L(x₁) = L(w₃)`, `qAB = L(x₂) = L(w₂)` on the centre row; `qA = L(m₁)`, `qB = L(m₃)`, `qC'` the
third local carrier on the pair row; `ρ = r174c_ρ`. -/
def r174c_carrierData (D : GT_Endpoint hG.crossingGeometry hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry) :
    r174c_CarrierData hn hG Q m x w hSm hSxw where
  qC := r174c_qC D
  qAB := r174c_qAB D
  hCAB := r174c_hCAB D hSm
  qC' := r174c_qC' D
  qA := r174c_qA D
  qB := r174c_qB D
  hC'A := r174c_hC'A D hn hSxw
  hC'B := r174c_hC'B D hn hSxw hsgn
  hAB := r174c_hAB D hSxw
  ρ := r174c_ρ D hn hSm hSxw hsgn
  ρ_AB := r174c_ρ_AB D hn hSm hSxw hsgn
  ρ_C := r174c_ρ_C D hn hSm hSxw hsgn
  spectator_weight := r174c_spectator_weight hn hG D hSm hSxw hsgn
  spectator_omega := r174c_spectator_omega hn hG D hSm hSxw hsgn

end R174CBundle

end

end SM.Link

/-! ### 6. The local carriers mark by mark: `C ↔ C'` and `AB ↔ A ∪ B` on the non-local marks

A non-local mark `b` of `C` (resp. `AB`) lies on `C'` (resp. `A` or `B`), and conversely: following
`ρ_S` from `b`, the first local mark reached is entered from a non-local mark, and the two reconnections
agree up to it (`r174c_first_local`); the local marks with a non-local `ρ_S`-predecessor are `x₁, x₂, m₃`
(case A) / `w₃, w₂, m₁` (case B) on the centre row and `x₁, x₂, m₃` / `w₃, m₁, w₂` on the pair row.  These
are the facts items 2–3 of U_R174 §4 (`omega_C`, `weight_C`, `weight_AB`, `carrierR_add`, `writhe_count`)
need to compare the corner lists and retained crossings of `C, AB` with those of `C', A, B`. -/

namespace SM.Link

open SM SM.GeoCarrier SM.Carrier RProof

noncomputable section

section R174CFirstHitPerm

theorem r174c_pow_eq_of_agree_lt {α : Type*} {σ σ' : Equiv.Perm α} {L : α → Prop}
    (hagree : ∀ a, ¬ L a → σ a = σ' a) {a : α} (j : ℕ) (hL : ∀ i < j, ¬ L ((σ ^ i) a)) :
    (σ' ^ j) a = (σ ^ j) a := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply,
      ih (fun i hi => hL i (Nat.lt_succ_of_lt hi)), hagree _ (hL j (Nat.lt_succ_self j))]

/-- **The first iterate in `L`**: if some `σ`-iterate of the non-`L` point `a` lies in `L`, there is a
first one, `(σ ^ j) a`; its `σ`-predecessor `(σ ^ (j-1)) a` is not in `L`, and `σ'` (agreeing with `σ`
outside `L`) reaches the same point in `j` steps. -/
theorem r174c_exists_first {α : Type*} {σ σ' : Equiv.Perm α} {L : α → Prop}
    (hagree : ∀ a, ¬ L a → σ a = σ' a) {a : α} (ha : ¬ L a) {k : ℕ} (hk : L ((σ ^ k) a)) :
    ∃ j : ℕ, 0 < j ∧ L ((σ ^ j) a) ∧ ¬ L ((σ ^ (j - 1)) a) ∧ (σ' ^ j) a = (σ ^ j) a := by
  classical
  have hex : ∃ j, L ((σ ^ j) a) := ⟨k, hk⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · exfalso
      have := Nat.find_spec hex
      rw [h0, pow_zero, Equiv.Perm.one_apply] at this
      exact ha this
    · exact hpos
  · apply Nat.find_min hex
    have : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, pow_zero, Equiv.Perm.one_apply] at this
      exact ha this
    omega
  · exact r174c_pow_eq_of_agree_lt hagree _ fun i hi => Nat.find_min hex hi

end R174CFirstHitPerm

section R174CFirstHit

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-- the first local mark on the `ρ_S`-orbit of a non-local mark `b` whose `S`-carrier contains a local
mark `c`: a local mark `ℓ` with a non-local `ρ_S`-predecessor `p`, on the `S`-carrier of `b` AND on the
`T`-carrier of `b` -/
theorem r174c_first_local (hP : CrossingGeometry P) (S T : Finset (Crossing P)) {b : Mark P}
    (hb : ∀ v : Visit P, b = Sum.inr v → (v.1 ∈ S ↔ v.1 ∈ T)) {c : Mark P}
    (hc : geoOwner hP S c = geoOwner hP S b)
    (hcL : ∃ v : Visit P, c = Sum.inr v ∧ ¬ (v.1 ∈ S ↔ v.1 ∈ T)) :
    ∃ ℓ p : Mark P, (∃ v : Visit P, ℓ = Sum.inr v ∧ ¬ (v.1 ∈ S ↔ v.1 ∈ T)) ∧
      (∀ v : Visit P, p = Sum.inr v → (v.1 ∈ S ↔ v.1 ∈ T)) ∧
      geoSmoothingSuccessor hP S p = ℓ ∧
      geoOwner hP S ℓ = geoOwner hP S b ∧ geoOwner hP T ℓ = geoOwner hP T b := by
  have hsc : (geoSmoothingSuccessor hP S).SameCycle b c := (geoOwner_eq_iff hP S _ _).mp hc.symm
  obtain ⟨k, hk⟩ := hsc.exists_nat_pow_eq
  have hagree : ∀ a : Mark P, ¬ (∃ v : Visit P, a = Sum.inr v ∧ ¬ (v.1 ∈ S ↔ v.1 ∈ T)) →
      geoSmoothingSuccessor hP S a = geoSmoothingSuccessor hP T a := by
    intro a ha
    apply r174c_succ_eq_of_not_local hP S T a
    intro v hv
    by_contra hcon
    exact ha ⟨v, hv, hcon⟩
  have hbL : ¬ (∃ v : Visit P, b = Sum.inr v ∧ ¬ (v.1 ∈ S ↔ v.1 ∈ T)) := by
    rintro ⟨v, hv, hcon⟩
    exact hcon (hb v hv)
  have hkL : (fun a : Mark P => ∃ v : Visit P, a = Sum.inr v ∧ ¬ (v.1 ∈ S ↔ v.1 ∈ T))
      ((geoSmoothingSuccessor hP S ^ k) b) := by
    rw [hk]; exact hcL
  obtain ⟨j, hj, hjL, hjL', hj'⟩ := r174c_exists_first hagree hbL hkL
  refine ⟨(geoSmoothingSuccessor hP S ^ j) b, (geoSmoothingSuccessor hP S ^ (j - 1)) b, hjL, ?_, ?_, ?_, ?_⟩
  · intro v hv
    by_contra hcon
    exact hjL' ⟨v, hv, hcon⟩
  · rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hj]
  · exact Eq.symm ((geoOwner_eq_iff hP S _ _).mpr ⟨(j : ℤ), by rw [zpow_natCast]⟩)
  · rw [← hj']
    exact Eq.symm ((geoOwner_eq_iff hP T _ _).mpr ⟨(j : ℤ), by rw [zpow_natCast]⟩)

variable {P' : LabelledTuple n} {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃) (hn : 3 ≤ n)

include D

/-- a mark is *non-local* when it is a vertex or a visit of a crossing other than `x, w, m` -/
def r174c_NonLocal (b : Mark P) : Prop :=
  ∀ v : Visit P, b = Sum.inr v → v.1 ≠ x ∧ v.1 ≠ w ∧ v.1 ≠ m

omit [NeZero n] D in
theorem r174c_nonLocal_vertex (i : ZMod n) : r174c_NonLocal (x := x) (w := w) (m := m) (Sum.inl i) :=
  fun _ h => nomatch h

theorem r174c_nonLocal_iff (b : Mark P) :
    r174c_NonLocal (x := x) (w := w) (m := m) b ↔
      ∀ v : Visit P, b = Sum.inr v → (v.1 ∈ Q ∪ {m} ↔ v.1 ∈ Q ∪ {x, w}) := by
  constructor
  · intro h v hv
    obtain ⟨h1, h2, h3⟩ := h v hv
    exact r174c_mem_iff_of_outside h1 h2 h3
  · intro h v hv
    have hiff := h v hv
    refine ⟨fun hx => ?_, fun hw => ?_, fun hm => ?_⟩
    · exact r174c_x_not_mem_Sm D (hx ▸ hiff.mpr (hx ▸ r174c_x_mem_Sxw))
    · exact r174c_w_not_mem_Sm D (hw ▸ hiff.mpr (hw ▸ r174c_w_mem_Sxw))
    · exact r174c_m_not_mem_Sxw D (hm ▸ hiff.mp (hm ▸ r174c_m_mem_Sm))

omit [NeZero n] D in
theorem r174c_local_of_not_iff (v : Visit P) (h : ¬ (v.1 ∈ Q ∪ {m} ↔ v.1 ∈ Q ∪ {x, w})) :
    v.1 = x ∨ v.1 = w ∨ v.1 = m := by
  by_contra hcon
  simp only [not_or] at hcon
  exact h (r174c_mem_iff_of_outside hcon.1 hcon.2.1 hcon.2.2)

omit D in
theorem r174c_not_iff_of_local (v : Visit P) (hv : v.1 = x ∨ v.1 = w ∨ v.1 = m)
    (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃) :
    ¬ (v.1 ∈ Q ∪ {m} ↔ v.1 ∈ Q ∪ {x, w}) := by
  rcases hv with h | h | h
  · rw [h]; exact fun hiff => r174c_x_not_mem_Sm D (hiff.mpr r174c_x_mem_Sxw)
  · rw [h]; exact fun hiff => r174c_w_not_mem_Sm D (hiff.mpr r174c_w_mem_Sxw)
  · rw [h]; exact fun hiff => r174c_m_not_mem_Sxw D (hiff.mp r174c_m_mem_Sm)

/-- the six local visits -/
theorem r174c_local_cases (v : Visit P) (hv : v.1 = x ∨ v.1 = w ∨ v.1 = m) :
    v = D.x₁ ∨ v = D.x₂ ∨ v = D.w₂ ∨ v = D.w₃ ∨ v = D.m₁ ∨ v = D.m₃ := by
  rcases hv with h | h | h
  · rcases visit_eq_or_twin D.x₁ v h with h' | h'
    · exact Or.inl h'
    · rw [D.twin_x₁] at h'; exact Or.inr (Or.inl h')
  · rcases visit_eq_or_twin D.w₂ v h with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · rw [D.twin_w₂] at h'; exact Or.inr (Or.inr (Or.inr (Or.inl h')))
  · rcases visit_eq_or_twin D.m₁ v h with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
    · rw [D.twin_m₁] at h'; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))

include hn

/-! #### The reconnection successors at the local visits -/

theorem r174c_succSm_x₁_A (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoSmoothingSuccessor hP (Q ∪ {m}) (Sum.inr D.x₁) = Sum.inr D.m₁ := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.x₁ (r174c_x_not_mem_Sm D), r174c_succ_x₁_A D hn hA]

theorem r174c_succSm_m₁_A (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoSmoothingSuccessor hP (Q ∪ {m}) (Sum.inr D.m₁) = Sum.inr D.w₃ := by
  rw [geoSmoothingSuccessor_visit_of_mem hP (Q ∪ {m}) D.m₁ r174c_m_mem_Sm, D.twin_m₁,
    r174c_succ_m₃_A D hn hsgn hA]

theorem r174c_succSm_x₂_A (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoSmoothingSuccessor hP (Q ∪ {m}) (Sum.inr D.x₂) = Sum.inr D.w₂ := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.x₂ (r174c_x_not_mem_Sm D),
    r174c_succ_x₂_A D hn hSxw hsgn hA]

theorem r174c_succSm_w₃_B (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoSmoothingSuccessor hP (Q ∪ {m}) (Sum.inr D.w₃) = Sum.inr D.m₃ := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.w₃ (r174c_w_not_mem_Sm D), r174c_succ_w₃_B D hn hsgn hB]

theorem r174c_succSm_m₃_B (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoSmoothingSuccessor hP (Q ∪ {m}) (Sum.inr D.m₃) = Sum.inr D.x₁ := by
  rw [geoSmoothingSuccessor_visit_of_mem hP (Q ∪ {m}) D.m₃ r174c_m_mem_Sm, D.twin_m₃, r174c_succ_m₁_B D hn hB]

theorem r174c_succSm_w₂_B (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoSmoothingSuccessor hP (Q ∪ {m}) (Sum.inr D.w₂) = Sum.inr D.x₂ := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.w₂ (r174c_w_not_mem_Sm D),
    r174c_succ_w₂_B D hn hSxw hsgn hB]

theorem r174c_succSxw_x₁_A (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoSmoothingSuccessor hP (Q ∪ {x, w}) (Sum.inr D.x₁) = Sum.inr D.w₂ := by
  rw [geoSmoothingSuccessor_visit_of_mem hP (Q ∪ {x, w}) D.x₁ r174c_x_mem_Sxw, D.twin_x₁,
    r174c_succ_x₂_A D hn hSxw hsgn hA]

theorem r174c_succSxw_x₂_A (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoSmoothingSuccessor hP (Q ∪ {x, w}) (Sum.inr D.x₂) = Sum.inr D.m₁ := by
  rw [geoSmoothingSuccessor_visit_of_mem hP (Q ∪ {x, w}) D.x₂ r174c_x_mem_Sxw, D.twin_x₂,
    r174c_succ_x₁_A D hn hA]

theorem r174c_succSxw_m₃_A (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hA : visitParameter D.x₁ < visitParameter D.m₁) :
    geoSmoothingSuccessor hP (Q ∪ {x, w}) (Sum.inr D.m₃) = Sum.inr D.w₃ := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.m₃ (r174c_m_not_mem_Sxw D), r174c_succ_m₃_A D hn hsgn hA]

theorem r174c_succSxw_m₁_B (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoSmoothingSuccessor hP (Q ∪ {x, w}) (Sum.inr D.m₁) = Sum.inr D.x₁ := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.m₁ (r174c_m_not_mem_Sxw D), r174c_succ_m₁_B D hn hB]

theorem r174c_succSxw_w₂_B (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoSmoothingSuccessor hP (Q ∪ {x, w}) (Sum.inr D.w₂) = Sum.inr D.m₃ := by
  rw [geoSmoothingSuccessor_visit_of_mem hP (Q ∪ {x, w}) D.w₂ r174c_w_mem_Sxw, D.twin_w₂,
    r174c_succ_w₃_B D hn hsgn hB]

theorem r174c_succSxw_w₃_B (hSxw : Q ∪ {x, w} ∈ CV.Ind hP) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hB : visitParameter D.m₁ < visitParameter D.x₁) :
    geoSmoothingSuccessor hP (Q ∪ {x, w}) (Sum.inr D.w₃) = Sum.inr D.x₂ := by
  rw [geoSmoothingSuccessor_visit_of_mem hP (Q ∪ {x, w}) D.w₃ r174c_w_mem_Sxw, D.twin_w₃,
    r174c_succ_w₂_B D hn hSxw hsgn hB]

omit D hn in
/-- a local visit whose `ρ_S`-predecessor is a given local visit cannot be entered from a non-local mark -/
theorem r174c_not_entry {S : Finset (Crossing P)} {u v : Visit P}
    (hsucc : geoSmoothingSuccessor hP S (Sum.inr u) = Sum.inr v) (hu : u.1 = x ∨ u.1 = w ∨ u.1 = m)
    {p : Mark P} (hp : r174c_NonLocal (x := x) (w := w) (m := m) p)
    (hsp : geoSmoothingSuccessor hP S p = Sum.inr v) : False := by
  have hpu : p = Sum.inr u := (geoSmoothingSuccessor hP S).injective (hsp.trans hsucc.symm)
  obtain ⟨h1, h2, h3⟩ := hp u hpu
  rcases hu with h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h

/-! #### The entry visits of the local carriers -/

/-- **`C` is entered at `x₁` (case A) / `w₃` (case B)**: a local visit of `C` with a non-local
predecessor lies on `C'`. -/
theorem r174c_entry_qC (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (v : Visit P) (hv : v.1 = x ∨ v.1 = w ∨ v.1 = m)
    (hq : geoOwner hP (Q ∪ {m}) (Sum.inr v) = r174c_qC D) {p : Mark P}
    (hp : r174c_NonLocal (x := x) (w := w) (m := m) p)
    (hsp : geoSmoothingSuccessor hP (Q ∪ {m}) p = Sum.inr v) :
    geoOwner hP (Q ∪ {x, w}) (Sum.inr v) = r174c_qC' D := by
  have hAB : geoOwner hP (Q ∪ {m}) (Sum.inr v) ≠ r174c_qAB D := by
    rw [hq]; exact r174c_hCAB D hSm
  rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with hA | hB
  · rcases r174c_local_cases D v hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (r174c_qC'_A D hA).symm
    · exact absurd (r174c_qAB_x₂ D) hAB
    · exact absurd (r174c_qAB_w₂ D) hAB
    · exact (r174c_not_entry (r174c_succSm_m₁_A D hn hsgn hA) (Or.inr (Or.inr rfl)) hp hsp).elim
    · exact (r174c_not_entry (r174c_succSm_x₁_A D hn hA) (Or.inl rfl) hp hsp).elim
    · exact absurd (r174c_qAB_m₃_A D hn hSm hA) hAB
  · rcases r174c_local_cases D v hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (r174c_not_entry (r174c_succSm_m₃_B D hn hB) (Or.inr (Or.inr rfl)) hp hsp).elim
    · exact absurd (r174c_qAB_x₂ D) hAB
    · exact absurd (r174c_qAB_w₂ D) hAB
    · exact r174c_qC'_w₃_B D hn hSxw hsgn hB
    · exact absurd (r174c_qAB_m₁_B D hn hSm hB) hAB
    · exact (r174c_not_entry (r174c_succSm_w₃_B D hn hsgn hB) (Or.inr (Or.inl rfl)) hp hsp).elim

/-- **`AB` is entered at `x₂` or `m₃` (case A) / `w₂` or `m₁` (case B)**: a local visit of `AB` with a
non-local predecessor lies on `A` or on `B`. -/
theorem r174c_entry_qAB (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (v : Visit P) (hv : v.1 = x ∨ v.1 = w ∨ v.1 = m)
    (hq : geoOwner hP (Q ∪ {m}) (Sum.inr v) = r174c_qAB D) {p : Mark P}
    (hp : r174c_NonLocal (x := x) (w := w) (m := m) p)
    (hsp : geoSmoothingSuccessor hP (Q ∪ {m}) p = Sum.inr v) :
    geoOwner hP (Q ∪ {x, w}) (Sum.inr v) = r174c_qA D ∨ geoOwner hP (Q ∪ {x, w}) (Sum.inr v) = r174c_qB D := by
  have hC : geoOwner hP (Q ∪ {m}) (Sum.inr v) ≠ r174c_qC D := by
    rw [hq]; exact (r174c_hCAB D hSm).symm
  rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with hA | hB
  · rcases r174c_local_cases D v hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (r174c_qC_x₁ D) hC
    · exact Or.inl (r174c_qA_x₂_A D hn hA)
    · exact (r174c_not_entry (r174c_succSm_x₂_A D hn hSxw hsgn hA) (Or.inl rfl) hp hsp).elim
    · exact absurd (r174c_qC_w₃_A D hn hsgn hA) hC
    · exact absurd (r174c_qC_m₁_A D hn hA) hC
    · exact Or.inr (r174c_qB_m₃ D)
  · rcases r174c_local_cases D v hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (r174c_qC_x₁ D) hC
    · exact (r174c_not_entry (r174c_succSm_w₂_B D hn hSxw hsgn hB) (Or.inr (Or.inl rfl)) hp hsp).elim
    · exact Or.inr (r174c_qB_w₂_B D hn hsgn hB)
    · exact absurd (r174c_qC_w₃_B D hn hsgn hB) hC
    · exact Or.inl (r174c_qA_m₁ D)
    · exact absurd (r174c_qC_m₃_B D hn hB) hC

/-- **`C'` is entered at `x₁` (case A) / `w₃` (case B)**: a local visit of `C'` with a non-local
predecessor lies on `C`. -/
theorem r174c_entry_qC' (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (v : Visit P) (hv : v.1 = x ∨ v.1 = w ∨ v.1 = m)
    (hq : geoOwner hP (Q ∪ {x, w}) (Sum.inr v) = r174c_qC' D) {p : Mark P}
    (hp : r174c_NonLocal (x := x) (w := w) (m := m) p)
    (hsp : geoSmoothingSuccessor hP (Q ∪ {x, w}) p = Sum.inr v) :
    geoOwner hP (Q ∪ {m}) (Sum.inr v) = r174c_qC D := by
  have hA' : geoOwner hP (Q ∪ {x, w}) (Sum.inr v) ≠ r174c_qA D := by
    rw [hq]; exact r174c_hC'A D hn hSxw
  have hB' : geoOwner hP (Q ∪ {x, w}) (Sum.inr v) ≠ r174c_qB D := by
    rw [hq]; exact r174c_hC'B D hn hSxw hsgn
  rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with hA | hB
  · rcases r174c_local_cases D v hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact r174c_qC_x₁ D
    · exact absurd (r174c_qA_x₂_A D hn hA) hA'
    · exact (r174c_not_entry (r174c_succSxw_x₁_A D hn hSxw hsgn hA) (Or.inl rfl) hp hsp).elim
    · exact absurd (r174c_qB_w₃_A D hn hsgn hA) hB'
    · exact absurd (r174c_qA_m₁ D) hA'
    · exact absurd (r174c_qB_m₃ D) hB'
  · rcases r174c_local_cases D v hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (r174c_qA_x₁_B D hn hB) hA'
    · exact (r174c_not_entry (r174c_succSxw_w₃_B D hn hSxw hsgn hB) (Or.inr (Or.inl rfl)) hp hsp).elim
    · exact absurd (r174c_qB_w₂_B D hn hsgn hB) hB'
    · exact r174c_qC_w₃_B D hn hsgn hB
    · exact absurd (r174c_qA_m₁ D) hA'
    · exact absurd (r174c_qB_m₃ D) hB'

/-- **`A` is entered at `x₂` (case A) / `m₁` (case B)** and **`B` at `m₃` / `w₂`**: a local visit of `A`
or `B` with a non-local predecessor lies on `AB`. -/
theorem r174c_entry_qA_qB (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (v : Visit P) (hv : v.1 = x ∨ v.1 = w ∨ v.1 = m)
    (hq : geoOwner hP (Q ∪ {x, w}) (Sum.inr v) = r174c_qA D ∨ geoOwner hP (Q ∪ {x, w}) (Sum.inr v) = r174c_qB D)
    {p : Mark P} (hp : r174c_NonLocal (x := x) (w := w) (m := m) p)
    (hsp : geoSmoothingSuccessor hP (Q ∪ {x, w}) p = Sum.inr v) :
    geoOwner hP (Q ∪ {m}) (Sum.inr v) = r174c_qAB D := by
  have hC' : geoOwner hP (Q ∪ {x, w}) (Sum.inr v) ≠ r174c_qC' D := by
    rcases hq with h | h
    · rw [h]; exact (r174c_hC'A D hn hSxw).symm
    · rw [h]; exact (r174c_hC'B D hn hSxw hsgn).symm
  rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with hA | hB
  · rcases r174c_local_cases D v hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (r174c_qC'_A D hA).symm hC'
    · exact r174c_qAB_x₂ D
    · exact absurd (r174c_qC'_w₂_A D hn hSxw hsgn hA) hC'
    · exact (r174c_not_entry (r174c_succSxw_m₃_A D hn hsgn hA) (Or.inr (Or.inr rfl)) hp hsp).elim
    · exact (r174c_not_entry (r174c_succSxw_x₂_A D hn hA) (Or.inl rfl) hp hsp).elim
    · exact r174c_qAB_m₃_A D hn hSm hA
  · rcases r174c_local_cases D v hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (r174c_not_entry (r174c_succSxw_m₁_B D hn hB) (Or.inr (Or.inr rfl)) hp hsp).elim
    · exact absurd (r174c_qC'_B D hB).symm hC'
    · exact r174c_qAB_w₂ D
    · exact absurd (r174c_qC'_w₃_B D hn hSxw hsgn hB) hC'
    · exact r174c_qAB_m₁_B D hn hSm hB
    · exact (r174c_not_entry (r174c_succSxw_w₂_B D hn hsgn hB) (Or.inr (Or.inl rfl)) hp hsp).elim

/-! #### The correspondences on the non-local marks -/

/-- **A non-local mark of `C` lies on `C'`.** -/
theorem r174c_owner_xw_of_qC (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) {b : Mark P}
    (hb : r174c_NonLocal (x := x) (w := w) (m := m) b) (h : geoOwner hP (Q ∪ {m}) b = r174c_qC D) :
    geoOwner hP (Q ∪ {x, w}) b = r174c_qC' D := by
  obtain ⟨ℓ, p, ⟨v, rfl, hvL⟩, hp, hsp, hℓS, hℓT⟩ := r174c_first_local hP (Q ∪ {m}) (Q ∪ {x, w})
    ((r174c_nonLocal_iff D b).mp hb) (c := Sum.inr D.x₁) (by rw [h]; rfl)
    ⟨D.x₁, rfl, r174c_not_iff_of_local D.x₁ (Or.inl rfl) D⟩
  rw [← hℓT]
  exact r174c_entry_qC D hn hSm hSxw hsgn v (r174c_local_of_not_iff v hvL) (hℓS.trans h)
    ((r174c_nonLocal_iff D p).mpr hp) hsp

/-- **A non-local mark of `AB` lies on `A` or on `B`.** -/
theorem r174c_owner_xw_of_qAB (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) {b : Mark P}
    (hb : r174c_NonLocal (x := x) (w := w) (m := m) b) (h : geoOwner hP (Q ∪ {m}) b = r174c_qAB D) :
    geoOwner hP (Q ∪ {x, w}) b = r174c_qA D ∨ geoOwner hP (Q ∪ {x, w}) b = r174c_qB D := by
  obtain ⟨ℓ, p, ⟨v, rfl, hvL⟩, hp, hsp, hℓS, hℓT⟩ := r174c_first_local hP (Q ∪ {m}) (Q ∪ {x, w})
    ((r174c_nonLocal_iff D b).mp hb) (c := Sum.inr D.x₂) (by rw [h]; rfl)
    ⟨D.x₂, rfl, r174c_not_iff_of_local D.x₂ (Or.inl rfl) D⟩
  rw [← hℓT]
  exact r174c_entry_qAB D hn hSm hSxw hsgn v (r174c_local_of_not_iff v hvL) (hℓS.trans h)
    ((r174c_nonLocal_iff D p).mpr hp) hsp

/-- **A non-local mark of `C'` lies on `C`.** -/
theorem r174c_owner_m_of_qC' (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) {b : Mark P}
    (hb : r174c_NonLocal (x := x) (w := w) (m := m) b) (h : geoOwner hP (Q ∪ {x, w}) b = r174c_qC' D) :
    geoOwner hP (Q ∪ {m}) b = r174c_qC D := by
  have hb' : ∀ v : Visit P, b = Sum.inr v → (v.1 ∈ Q ∪ {x, w} ↔ v.1 ∈ Q ∪ {m}) :=
    fun v hv => ((r174c_nonLocal_iff D b).mp hb v hv).symm
  have hc : ∃ c : Visit P, geoOwner hP (Q ∪ {x, w}) (Sum.inr c) = r174c_qC' D ∧
      (c.1 = x ∨ c.1 = w ∨ c.1 = m) := by
    rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with hA | hB
    · exact ⟨D.x₁, (r174c_qC'_A D hA).symm, Or.inl rfl⟩
    · exact ⟨D.x₂, (r174c_qC'_B D hB).symm, Or.inl rfl⟩
  obtain ⟨c, hcq, hcL⟩ := hc
  obtain ⟨ℓ, p, ⟨v, rfl, hvL⟩, hp, hsp, hℓS, hℓT⟩ := r174c_first_local hP (Q ∪ {x, w}) (Q ∪ {m}) hb'
    (c := Sum.inr c) (hcq.trans h.symm)
    ⟨c, rfl, fun hiff => r174c_not_iff_of_local c hcL D hiff.symm⟩
  rw [← hℓT]
  exact r174c_entry_qC' D hn hSxw hsgn v (r174c_local_of_not_iff v (fun hiff => hvL hiff.symm))
    (hℓS.trans h) ((r174c_nonLocal_iff D p).mpr fun v' hv' => (hp v' hv').symm) hsp

/-- **A non-local mark of `A` or of `B` lies on `AB`.** -/
theorem r174c_owner_m_of_qA_qB (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) {b : Mark P}
    (hb : r174c_NonLocal (x := x) (w := w) (m := m) b)
    (h : geoOwner hP (Q ∪ {x, w}) b = r174c_qA D ∨ geoOwner hP (Q ∪ {x, w}) b = r174c_qB D) :
    geoOwner hP (Q ∪ {m}) b = r174c_qAB D := by
  have hb' : ∀ v : Visit P, b = Sum.inr v → (v.1 ∈ Q ∪ {x, w} ↔ v.1 ∈ Q ∪ {m}) :=
    fun v hv => ((r174c_nonLocal_iff D b).mp hb v hv).symm
  have hc : ∃ c : Visit P, geoOwner hP (Q ∪ {x, w}) (Sum.inr c) = geoOwner hP (Q ∪ {x, w}) b ∧
      (c.1 = x ∨ c.1 = w ∨ c.1 = m) := by
    rcases h with h | h
    · exact ⟨D.m₁, h.symm, Or.inr (Or.inr rfl)⟩
    · exact ⟨D.m₃, h.symm, Or.inr (Or.inr rfl)⟩
  obtain ⟨c, hcq, hcL⟩ := hc
  obtain ⟨ℓ, p, ⟨v, rfl, hvL⟩, hp, hsp, hℓS, hℓT⟩ := r174c_first_local hP (Q ∪ {x, w}) (Q ∪ {m}) hb'
    (c := Sum.inr c) hcq ⟨c, rfl, fun hiff => r174c_not_iff_of_local c hcL D hiff.symm⟩
  rw [← hℓT]
  refine r174c_entry_qA_qB D hn hSm hSxw hsgn v (r174c_local_of_not_iff v (fun hiff => hvL hiff.symm))
    ?_ ((r174c_nonLocal_iff D p).mpr fun v' hv' => (hp v' hv').symm) hsp
  rw [hℓS]; exact h

/-- **Summary: `C ↔ C'` on the non-local marks.** -/
theorem r174c_owner_qC_iff (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) {b : Mark P}
    (hb : r174c_NonLocal (x := x) (w := w) (m := m) b) :
    geoOwner hP (Q ∪ {m}) b = r174c_qC D ↔ geoOwner hP (Q ∪ {x, w}) b = r174c_qC' D :=
  ⟨r174c_owner_xw_of_qC D hn hSm hSxw hsgn hb, r174c_owner_m_of_qC' D hn hSxw hsgn hb⟩

/-- **Summary: `AB ↔ A ∪ B` on the non-local marks.** -/
theorem r174c_owner_qAB_iff (hSm : Q ∪ {m} ∈ CV.Ind hP) (hSxw : Q ∪ {x, w} ∈ CV.Ind hP)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) {b : Mark P}
    (hb : r174c_NonLocal (x := x) (w := w) (m := m) b) :
    geoOwner hP (Q ∪ {m}) b = r174c_qAB D ↔
      (geoOwner hP (Q ∪ {x, w}) b = r174c_qA D ∨ geoOwner hP (Q ∪ {x, w}) b = r174c_qB D) :=
  ⟨r174c_owner_xw_of_qAB D hn hSm hSxw hsgn hb, r174c_owner_m_of_qA_qB D hn hSm hSxw hsgn hb⟩

end R174CFirstHit

end

end SM.Link


/-! ## Unit SITEIN (row 174): the two site inputs `hx'`, `hw'` of Site 174 — the transported crossings
`x' = crossingTransport hs x`, `w' = crossingTransport hs w` are RETAINED crossings of the `E`-side carrier
`τ qAB = GT_carrierEquiv (gsc_wall_of_endpoint hG hG' D hSm hSm') (r174c_qAB D)` of the transported centre
row `S' = transportSupport hs (Q ∪ {m})`

Prover of unit SITEIN, 2026-09-15.  Everything below is NEW (nothing above changed); names carry the prefix
`r174x_`.  Route (shorter than the arc route sketched in Site_174_REPORT §5): the `ℓ₂`-visits `x₂, w₂` of
`x, w` are GOOD marks of the wall of the centre row (`GT_Good`): a reversed partner of a visit on `ℓ₂` is a
triangle crossing on `ℓ₂`, i.e. `x` or `w`, and neither is selected in `Q ∪ {m}` (`m` does not use `ℓ₂`).
So `GT_owner_transport` carries their owner `qAB = L_m(x₂) = L_m(w₂)` (`r174c_qAB`, `r174c_qAB_w₂`) to
`τ qAB` on the `E` side.  On the `E` side `x'`, `w'` lie in `U(S')` (`x'`, `w'` do not interlace `m'` by
`GT_Endpoint.compl`, nor any transported `Q`-crossing by `toggle` + `Q_avail`), so ALL visits of `x'`
(resp. `w'`) lie on one carrier (`CV.owner_eq_of_mem_U`), namely `τ qAB`. -/

namespace SM.Link

open SM SM.GeoCarrier SM.Carrier RProof

noncomputable section

/-! ### 1. The `E`-side membership facts, at the `CrossingGeometry` level -/

section R174XLocal

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n}
  {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)

include D

/-- `x'` is not selected in the transported centre row. -/
theorem r174x_x'_not_mem_Sm' : crossingTransport hs x ∉ transportSupport hs (Q ∪ {m}) := by
  rw [mem_transportSupport_iff]
  exact r174c_x_not_mem_Sm D

/-- `w'` is not selected in the transported centre row. -/
theorem r174x_w'_not_mem_Sm' : crossingTransport hs w ∉ transportSupport hs (Q ∪ {m}) := by
  rw [mem_transportSupport_iff]
  exact r174c_w_not_mem_Sm D

/-- On the `E` side `x'` interlaces no crossing of `S' = Q' ∪ {m'}`: not `m'` (`compl`: `x, m` interlace on
`P`, so `x', m'` do not), and no `Q'`-crossing (`toggle` + `Q_avail`). -/
theorem r174x_x'_mem_U : crossingTransport hs x ∈ CV.U hP' (transportSupport hs (Q ∪ {m})) := by
  rw [CV.mem_U_iff]
  refine ⟨r174x_x'_not_mem_Sm' D, fun s' hs' => ?_⟩
  obtain ⟨s, rfl⟩ := (crossingTransport hs).surjective s'
  rw [mem_transportSupport_iff] at hs'
  rcases Finset.mem_union.mp hs' with hsQ | hsm
  · rw [D.toggle x s (fun h => D.Q_out s hsQ h.2)]
    exact fun h => D.Q_avail s hsQ x D.xT (geometricInterlaces_symm hP h)
  · rw [Finset.mem_singleton.mp hsm, D.compl x m D.xT D.mT D.xm]
    exact fun h => h D.hxm

/-- The same for `w'`. -/
theorem r174x_w'_mem_U : crossingTransport hs w ∈ CV.U hP' (transportSupport hs (Q ∪ {m})) := by
  rw [CV.mem_U_iff]
  refine ⟨r174x_w'_not_mem_Sm' D, fun s' hs' => ?_⟩
  obtain ⟨s, rfl⟩ := (crossingTransport hs).surjective s'
  rw [mem_transportSupport_iff] at hs'
  rcases Finset.mem_union.mp hs' with hsQ | hsm
  · rw [D.toggle w s (fun h => D.Q_out s hsQ h.2)]
    exact fun h => D.Q_avail s hsQ w D.wT (geometricInterlaces_symm hP h)
  · rw [Finset.mem_singleton.mp hsm, D.compl w m D.wT D.mT D.wm]
    exact fun h => h D.hwm

/-- **A visit on the edge `ℓ₂` is a good mark of the wall of the centre row** `Q ∪ {m}`: a reversed
partner `u` of `v` is a triangle crossing on `ℓ₂`; it is not in `Q` (`Q_out`), and it is not `m`
(`ℓ₂ ∉ m.val`), so it is not a corner of `Q ∪ {m}`. -/
theorem r174x_good_of_edge₂ {v : Visit P} (hv : v.2.val = ℓ₂) :
    GT_Good (triangleCrossings P e f g) (Q ∪ {m}) (Sum.inr v) := by
  intro v' hv' u hrev hu
  obtain rfl := Sum.inr.inj hv'
  have huS : u.1 ∈ Q ∪ {m} := hu
  have huT : u.1.val ∈ triangleSupports e f g := (F1.mem_triangleCrossings e f g u.1).mp hrev.2.1
  rcases Finset.mem_union.mp huS with hQ | hm
  · exact D.Q_out u.1 hQ huT
  · have hum : u.1 = m := Finset.mem_singleton.mp hm
    apply D.l2_not_mem_m
    rw [← hv, hrev.2.2.2, ← hum]
    exact u.2.property

/-- `x₂` is a good mark of the wall of the centre row. -/
theorem r174x_good_x₂ : GT_Good (triangleCrossings P e f g) (Q ∪ {m}) (Sum.inr D.x₂) :=
  r174x_good_of_edge₂ D (v := D.x₂) rfl

/-- `w₂` is a good mark of the wall of the centre row. -/
theorem r174x_good_w₂ : GT_Good (triangleCrossings P e f g) (Q ∪ {m}) (Sum.inr D.w₂) :=
  r174x_good_of_edge₂ D (v := D.w₂) rfl

end R174XLocal

/-! ### 2. The site inputs on the ledger's binders -/

section R174XMain

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
  (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
  (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)

local notation "𝑺'" => transportSupport hs (Q ∪ (Singleton.singleton m : Finset (Crossing P)))
local notation "𝑾" => gsc_wall_of_endpoint hG hG' D hSm hSm'

include hG hG' D hSm hSm'

/-- **The `ℓ₂`-visit of `x'` lies on the wall copy of the carrier of `x₂`** (`GT_owner_transport` on the
good mark `x₂`). -/
theorem r174x_owner'_x₂ (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqAB : geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) = qAB) :
    geoOwner hG'.crossingGeometry 𝑺' (Sum.inr (visitTransport hs D.x₂)) = GT_carrierEquiv 𝑾 qAB := by
  rw [← markTransport_visit, GT_owner_transport 𝑾 (r174x_good_x₂ D), hqAB]

/-- **The `ℓ₂`-visit of `w'` lies on the wall copy of the carrier of `w₂`**. -/
theorem r174x_owner'_w₂ (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqAB : geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.w₂) = qAB) :
    geoOwner hG'.crossingGeometry 𝑺' (Sum.inr (visitTransport hs D.w₂)) = GT_carrierEquiv 𝑾 qAB := by
  rw [← markTransport_visit, GT_owner_transport 𝑾 (r174x_good_w₂ D), hqAB]

/-- **The site input `hx'` at a general carrier**: if `qAB` owns `x₂` on `P`, then `x'` is a retained
crossing of `τ qAB` on `P'` (all visits of `x' ∈ U(S')` lie on the carrier of `x₂'`). -/
theorem r174x_hx'_of_owner (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqAB : geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) = qAB) :
    crossingTransport hs x ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' (GT_carrierEquiv 𝑾 qAB) := by
  rw [mem_geoCarrierCrossings]
  refine ⟨r174x_x'_not_mem_Sm' D, fun v' hv' => ?_⟩
  rw [CV.owner_eq_of_mem_U hG'.crossingGeometry hSm' (r174x_x'_mem_U D) v' (visitTransport hs D.x₂) hv' rfl]
  exact r174x_owner'_x₂ hG hG' D hSm hSm' qAB hqAB

/-- **The site input `hw'` at a general carrier**: if `qAB` owns `w₂` on `P`, then `w'` is a retained
crossing of `τ qAB` on `P'`. -/
theorem r174x_hw'_of_owner (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqAB : geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.w₂) = qAB) :
    crossingTransport hs w ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' (GT_carrierEquiv 𝑾 qAB) := by
  rw [mem_geoCarrierCrossings]
  refine ⟨r174x_w'_not_mem_Sm' D, fun v' hv' => ?_⟩
  rw [CV.owner_eq_of_mem_U hG'.crossingGeometry hSm' (r174x_w'_mem_U D) v' (visitTransport hs D.w₂) hv' rfl]
  exact r174x_owner'_w₂ hG hG' D hSm hSm' qAB hqAB

/-- **`hx'` on the binders of `r174h__s174_hrec_prop_proof` / `r174h_fulltwist`** (`qAB`, `q'`, and
`hq' : q' = GT_carrierEquiv (gsc_wall_of_endpoint hG hG' D hSm hSm') qAB`), for the ledger's carrier
`qAB = r174c_qAB D` (`hqAB`; `rfl` for `r174c_qAB D`, `r174x_carrierData_qAB` for the bundle's field). -/
theorem r174x_hx' (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m})) (hqAB : qAB = r174c_qAB D)
    (q' : GeoComponent hG'.crossingGeometry 𝑺') (hq' : q' = GT_carrierEquiv 𝑾 qAB) :
    crossingTransport hs x ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' q' := by
  subst hq'
  exact r174x_hx'_of_owner hG hG' D hSm hSm' qAB (hqAB ▸ r174c_qAB_x₂ D)

/-- **`hw'` on the binders of `r174h__s174_hrec_prop_proof` / `r174h_fulltwist`**. -/
theorem r174x_hw' (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m})) (hqAB : qAB = r174c_qAB D)
    (q' : GeoComponent hG'.crossingGeometry 𝑺') (hq' : q' = GT_carrierEquiv 𝑾 qAB) :
    crossingTransport hs w ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' q' := by
  subst hq'
  exact r174x_hw'_of_owner hG hG' D hSm hSm' qAB (hqAB ▸ r174c_qAB_w₂ D)

/-- Both site inputs at once. -/
theorem r174x_site_inputs (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m})) (hqAB : qAB = r174c_qAB D)
    (q' : GeoComponent hG'.crossingGeometry 𝑺') (hq' : q' = GT_carrierEquiv 𝑾 qAB) :
    crossingTransport hs x ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' q' ∧
      crossingTransport hs w ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' q' :=
  ⟨r174x_hx' hG hG' D hSm hSm' qAB hqAB q' hq', r174x_hw' hG hG' D hSm hSm' qAB hqAB q' hq'⟩

/-- `hx'` in the ledger's binding `q' := (gsc_wallData_of_endpoint …).τ (r174c_qAB D)` (`τ` is
`GT_carrierEquiv (gsc_wall_of_endpoint …)` by `rfl`), the form `r174h_hrec_tau` consumes. -/
theorem r174x_hx'_tau (hn : 3 ≤ n) :
    crossingTransport hs x ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺'
      ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ (r174c_qAB D)) :=
  r174x_hx'_of_owner hG hG' D hSm hSm' (r174c_qAB D) (r174c_qAB_x₂ D)

/-- `hw'` in the ledger's binding `q' := (gsc_wallData_of_endpoint …).τ (r174c_qAB D)`. -/
theorem r174x_hw'_tau (hn : 3 ≤ n) :
    crossingTransport hs w ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺'
      ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ (r174c_qAB D)) :=
  r174x_hw'_of_owner hG hG' D hSm hSm' (r174c_qAB D) (r174c_qAB_w₂ D)

omit hSm' in
/-- The bundle's `qAB` field is `r174c_qAB D` (definitional), so `hqAB := r174x_carrierData_qAB …` in
`r174x_hx'`/`r174x_hw'` when the realiser reads `qAB` off `r174c_carrierData`. -/
theorem r174x_carrierData_qAB (hn : 3 ≤ n) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry) :
    (r174c_carrierData hn hG D hsgn hSm hSxw).qAB = r174c_qAB D := rfl

end R174XMain

end

end SM.Link



/-! ## R174 WALL (unit WALL of row 174, Wave 2): `gsc_Ledger` items 2–3

Prover of unit WALL, 2026-09-15.  Everything below is NEW (nothing above changed); names carry the prefix
`r174w_`.  Contents (see `R174_WALL_REPORT.md`):
* **Part A — item 2 (the wall)**: the retained-crossing correspondence of the centre row `Q ∪ {m}` across the
  RIII wall (`r174w_retained_eq_of_ne`, `r174w_retained_qAB`: every carrier keeps its retained crossings
  transported, `AB` gains exactly `x', w'`), hence `writhe_wall` (`r174w_writhe_wall_ledger`) and `omega_wall`
  (`r174w_omega_wall_ledger`, through `EXT_homfly_wall`).  `qAB` is the carrier of the `ℓ₂`-visit `x₂`.
* **Part B — the corner-mark reformulation** of the selector `wt` and of `2π·rot` of a carrier (sums and
  quantifiers over the set of corner marks, with the intrinsic turn sign `r174w_tau` and principal turn
  `r174w_theta` of a mark), the angle identity of a triangle of directions (`r174w_angle_add_of_pos/neg`), the
  selector algebra on split corner sets (`r174w_F_split`, `r174w_F_two`) and the rotation sums
  (`r174w_rot_add`, `r174w_rot_eq_two`, `r174w_carrierR_add_of`).
* **Part C — the carrier structure of the two rows on the two-edge side** (`Q ∪ {m}` and `Q ∪ {x, w}`) from the
  geo layer's insertion data (`geoSmoothingSuccessor_insert_child_data`, `geoOwner_insert_iff_of_unaffected`),
  in both traversal orientations (`r174w_split_caseB` = the printed word `a b A a c B b c C`, `r174w_split_caseA`
  = the reversed traversal): the distribution of the six local visits over `A, B, C'` and `AB, C`, and the
  three regular containments (`r174w_Split`).
* **Part D — item 3**: `weight_AB` (`r174w_weight_AB`), `weight_C` (`r174w_weight_C`), `carrierR_add`
  (`r174w_carrierR_add`), `hσ` (`r174w_hsigma`) with the canonical sign `r174w_sigma` (which is
  `crossingSign ℓ₁ ℓ₂` in the printed orientation and its NEGATIVE in the reversed one — the ledger's `σ` is a
  free field, so this is not a defect of the ledger, but the realiser must choose `σ` this way), and the bonus
  `omega_C` (`r174w_omega_C`: `C` and `C'` retain the same crossings, `r174w_retained_C`). -/

namespace SM.Link

open SM SM.GeoCarrier SM.Carrier RProof

noncomputable section

section R174W_Wall

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
  (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
  (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)

omit [NeZero n] in
theorem r174w_mem_Sm_iff (y : Crossing P) : y ∈ Q ∪ {m} ↔ y ∈ Q ∨ y = m := by
  simp only [Finset.mem_union, Finset.mem_singleton]

include D in
theorem r174w_x_not_mem_Sm : x ∉ Q ∪ {m} := by
  rw [r174w_mem_Sm_iff]
  rintro (h | h)
  · exact D.Q_out x h D.xT
  · exact D.xm h

include D in
theorem r174w_w_not_mem_Sm : w ∉ Q ∪ {m} := by
  rw [r174w_mem_Sm_iff]
  rintro (h | h)
  · exact D.Q_out w h D.wT
  · exact D.wm h

omit [NeZero n] in
theorem r174w_m_mem_Sm : m ∈ Q ∪ {m} := (r174w_mem_Sm_iff m).mpr (Or.inr rfl)

include D in
/-- `x` is a neighbour of the selected centre `m`: not in `U(Q ∪ {m})`. -/
theorem r174w_x_not_mem_U : x ∉ CV.U hG.crossingGeometry (Q ∪ {m}) := by
  rw [CV.mem_U_iff]
  rintro ⟨-, h⟩
  exact h m r174w_m_mem_Sm D.hxm

include D in
theorem r174w_w_not_mem_U : w ∉ CV.U hG.crossingGeometry (Q ∪ {m}) := by
  rw [CV.mem_U_iff]
  rintro ⟨-, h⟩
  exact h m r174w_m_mem_Sm D.hwm

include D in
/-- On the one-edge side `x'` no longer interlaces `m'`: `x' ∈ U(Q' ∪ {m'})`. -/
theorem r174w_x'_mem_U' :
    crossingTransport hs x ∈ CV.U hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) := by
  rw [CV.mem_U_iff]
  refine ⟨fun h => r174w_x_not_mem_Sm hG hG' D ((mem_transportSupport_iff hs _ x).mp h), fun s' hs' => ?_⟩
  obtain ⟨s, rfl⟩ := (crossingTransport hs).surjective s'
  rw [mem_transportSupport_iff] at hs'
  rcases (r174w_mem_Sm_iff s).mp hs' with h | rfl
  · rw [D.toggle x s (fun h' => D.Q_out s h h'.2)]
    exact fun h' => D.Q_avail s h x D.xT (geometricInterlaces_symm _ h')
  · rw [D.compl x s D.xT D.mT D.xm]
    exact fun h' => h' D.hxm

include D in
theorem r174w_w'_mem_U' :
    crossingTransport hs w ∈ CV.U hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) := by
  rw [CV.mem_U_iff]
  refine ⟨fun h => r174w_w_not_mem_Sm hG hG' D ((mem_transportSupport_iff hs _ w).mp h), fun s' hs' => ?_⟩
  obtain ⟨s, rfl⟩ := (crossingTransport hs).surjective s'
  rw [mem_transportSupport_iff] at hs'
  rcases (r174w_mem_Sm_iff s).mp hs' with h | rfl
  · rw [D.toggle w s (fun h' => D.Q_out s h h'.2)]
    exact fun h' => D.Q_avail s h w D.wT (geometricInterlaces_symm _ h')
  · rw [D.compl w s D.wT D.mT D.wm]
    exact fun h' => h' D.hwm

include D in
/-- The `ℓ₂`-visits of `x` and `w` are adjacent unselected visits of the centre row: one carrier (`AB`). -/
theorem r174w_owner_x₂_eq_w₂ :
    geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) =
      geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.w₂) :=
  GT_owner_eq_of_adjacent hG.crossingGeometry _ D.adj2 rfl (r174w_x_not_mem_Sm hG hG' D) (r174w_w_not_mem_Sm hG hG' D)

include D in
/-- `x₂` is a good mark of the centre row: its only reversed partner is `w₂`, and `w` is not selected. -/
theorem r174w_good_x₂ : GT_Good (triangleCrossings P e f g) (Q ∪ {m}) (Sum.inr D.x₂) := by
  intro v hv u hrev hu
  obtain rfl := Sum.inr.inj hv
  have huS : u.1 ∈ Q ∪ {m} := hu
  have huT : u.1.val ∈ triangleSupports e f g := (F1.mem_triangleCrossings e f g u.1).mp hrev.2.1
  have hum : u.1 = m := by
    rcases (r174w_mem_Sm_iff u.1).mp huS with h | h
    · exact absurd huT (D.Q_out u.1 h)
    · exact h
  apply D.l2_not_mem_m
  have h2 : u.2.val = ℓ₂ := hrev.2.2.2.symm
  rw [← h2, ← hum]
  exact u.2.property

include D in
theorem r174w_good_w₂ : GT_Good (triangleCrossings P e f g) (Q ∪ {m}) (Sum.inr D.w₂) := by
  intro v hv u hrev hu
  obtain rfl := Sum.inr.inj hv
  have huS : u.1 ∈ Q ∪ {m} := hu
  have huT : u.1.val ∈ triangleSupports e f g := (F1.mem_triangleCrossings e f g u.1).mp hrev.2.1
  have hum : u.1 = m := by
    rcases (r174w_mem_Sm_iff u.1).mp huS with h | h
    · exact absurd huT (D.Q_out u.1 h)
    · exact h
  apply D.l2_not_mem_m
  have h2 : u.2.val = ℓ₂ := hrev.2.2.2.symm
  rw [← h2, ← hum]
  exact u.2.property

/-- The carrier `AB` of the centre row: the owner of the `ℓ₂`-visits of `x, w` (item 1's `qAB`). -/
abbrev r174w_qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}) :=
  geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂)

/-- The wall of the centre row (the ledger's `W`). -/
abbrev r174w_W : GT_Wall hG.crossingGeometry hG'.crossingGeometry hs (triangleCrossings P e f g) (Q ∪ {m}) :=
  gsc_wall_of_endpoint hG hG' D hSm hSm'

/-- The carrier bijection `τ` of the ledger. -/
abbrev r174w_τ : GeoComponent hG.crossingGeometry (Q ∪ {m}) ≃
    GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) :=
  GT_carrierEquiv (r174w_W hG hG' D hSm hSm')

theorem r174w_τ_eq : (gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ = r174w_τ hG hG' D hSm hSm' := rfl

/-- **The `ℓ₂`-visit of `x'` lies on the copy of `AB`** (ownership transport of the good mark `x₂`). -/
theorem r174w_owner'_x₂' :
    geoOwner hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) (Sum.inr (visitTransport hs D.x₂)) =
      r174w_τ hG hG' D hSm hSm' (r174w_qAB hG hG' D) := by
  rw [← markTransport_visit]
  exact GT_owner_transport (r174w_W hG hG' D hSm hSm') (r174w_good_x₂ hG hG' D)

theorem r174w_owner'_w₂' :
    geoOwner hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) (Sum.inr (visitTransport hs D.w₂)) =
      r174w_τ hG hG' D hSm hSm' (r174w_qAB hG hG' D) := by
  rw [← markTransport_visit, GT_owner_transport (r174w_W hG hG' D hSm hSm') (r174w_good_w₂ hG hG' D)]
  unfold r174w_qAB
  rw [r174w_owner_x₂_eq_w₂ hG hG' D]

/-- **`x'` is a retained crossing of `AB'`** (the ledger's residual crossing `a` of `D_H`). -/
theorem r174w_x'_mem_retained :
    crossingTransport hs x ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))
      (r174w_τ hG hG' D hSm hSm' (r174w_qAB hG hG' D)) := by
  rw [mem_geoCarrierCrossings]
  refine ⟨fun h => r174w_x_not_mem_Sm hG hG' D ((mem_transportSupport_iff hs _ x).mp h), fun v hv => ?_⟩
  rw [CV.owner_eq_of_mem_U hG'.crossingGeometry hSm' (r174w_x'_mem_U' hG hG' D) v (visitTransport hs D.x₂) hv rfl]
  exact r174w_owner'_x₂' hG hG' D hSm hSm'

theorem r174w_w'_mem_retained :
    crossingTransport hs w ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))
      (r174w_τ hG hG' D hSm hSm' (r174w_qAB hG hG' D)) := by
  rw [mem_geoCarrierCrossings]
  refine ⟨fun h => r174w_w_not_mem_Sm hG hG' D ((mem_transportSupport_iff hs _ w).mp h), fun v hv => ?_⟩
  rw [CV.owner_eq_of_mem_U hG'.crossingGeometry hSm' (r174w_w'_mem_U' hG hG' D) v (visitTransport hs D.w₂) hv rfl]
  exact r174w_owner'_w₂' hG hG' D hSm hSm'

include D hSm in
theorem r174w_x_not_retained (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) :
    x ∉ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) q :=
  GT_retained_of_not_mem_U (CV.geoIndependent_of_mem_Ind _ hSm) (r174w_x_not_mem_U hG hG' D) q

include D hSm in
theorem r174w_w_not_retained (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) :
    w ∉ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) q :=
  GT_retained_of_not_mem_U (CV.geoIndependent_of_mem_Ind _ hSm) (r174w_w_not_mem_U hG hG' D) q

theorem r174w_m_not_retained (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) :
    m ∉ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) q := fun h =>
  ((mem_geoCarrierCrossings _ _ q m).mp h).1 r174w_m_mem_Sm

theorem r174w_m'_not_retained (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))) :
    crossingTransport hs m ∉ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q' :=
  fun h => ((mem_geoCarrierCrossings _ _ q' _).mp h).1
    ((mem_transportSupport_iff hs _ m).mpr r174w_m_mem_Sm)

include D hSm in
/-- A retained crossing of a carrier of the centre row is an outside crossing. -/
theorem r174w_outside_of_retained {q : GeoComponent hG.crossingGeometry (Q ∪ {m})} {y : Crossing P}
    (hy : y ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) q) :
    y.val ∉ triangleSupports e f g :=
  D.outside_of_ne (fun h => r174w_x_not_retained hG hG' D hSm q (h ▸ hy))
    (fun h => r174w_w_not_retained hG hG' D hSm q (h ▸ hy)) (fun h => r174w_m_not_retained hG q (h ▸ hy))

/-- Retained outside crossings are carried (their visits are good marks). -/
theorem r174w_retained_iff_of_outside (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) {y : Crossing P}
    (hy : y.val ∉ triangleSupports e f g) :
    crossingTransport hs y ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))
        (r174w_τ hG hG' D hSm hSm' q) ↔
      y ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) q := by
  have hgood : ∀ v : Visit P, v.1 = y → GT_Good (triangleCrossings P e f g) (Q ∪ {m}) (Sum.inr v) :=
    fun v hv => GT_good_of_not_mem _ _ (fun h => hy ((F1.mem_triangleCrossings e f g v.1).mp (hv ▸ h) |>
      fun h' => by rw [hv] at h'; exact h'))
  rw [mem_geoCarrierCrossings, mem_geoCarrierCrossings, mem_transportSupport_iff]
  apply and_congr Iff.rfl
  constructor
  · intro hall v hv
    have := hall (visitTransport hs v) (by rw [visitTransport_crossing, hv])
    rw [← markTransport_visit, GT_owner_transport (r174w_W hG hG' D hSm hSm') (hgood v hv)] at this
    exact (GT_carrierEquiv _).injective this
  · intro hall v' hv'
    obtain ⟨v, rfl⟩ := (visitTransport hs).surjective v'
    rw [visitTransport_crossing] at hv'
    have hv : v.1 = y := (crossingTransport hs).injective hv'
    rw [← markTransport_visit, GT_owner_transport (r174w_W hG hG' D hSm hSm') (hgood v hv), hall v hv]

/-- `x'` is retained exactly by the copy of `AB`. -/
theorem r174w_x'_retained_iff (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) :
    crossingTransport hs x ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))
        (r174w_τ hG hG' D hSm hSm' q) ↔ q = r174w_qAB hG hG' D := by
  constructor
  · intro h
    have h1 := ((mem_geoCarrierCrossings _ _ _ _).mp h).2 (visitTransport hs D.x₂) rfl
    have h2 := ((mem_geoCarrierCrossings _ _ _ _).mp
      (r174w_x'_mem_retained hG hG' D hSm hSm')).2 (visitTransport hs D.x₂) rfl
    exact (GT_carrierEquiv _).injective (h1.symm.trans h2)
  · rintro rfl
    exact r174w_x'_mem_retained hG hG' D hSm hSm'

theorem r174w_w'_retained_iff (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) :
    crossingTransport hs w ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))
        (r174w_τ hG hG' D hSm hSm' q) ↔ q = r174w_qAB hG hG' D := by
  constructor
  · intro h
    have h1 := ((mem_geoCarrierCrossings _ _ _ _).mp h).2 (visitTransport hs D.w₂) rfl
    have h2 := ((mem_geoCarrierCrossings _ _ _ _).mp
      (r174w_w'_mem_retained hG hG' D hSm hSm')).2 (visitTransport hs D.w₂) rfl
    exact (GT_carrierEquiv _).injective (h1.symm.trans h2)
  · rintro rfl
    exact r174w_w'_mem_retained hG hG' D hSm hSm'

/-- **Retained crossings of a spectator (or of `C`) are carried across the wall.** -/
theorem r174w_retained_eq_of_ne (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) (hq : q ≠ r174w_qAB hG hG' D) :
    geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) (r174w_τ hG hG' D hSm hSm' q) =
      (geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) q).map (crossingTransport hs).toEmbedding := by
  classical
  ext y'
  obtain ⟨y, rfl⟩ := (crossingTransport hs).surjective y'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  by_cases hyx : y = x
  · subst hyx
    exact iff_of_false (fun h => hq ((r174w_x'_retained_iff hG hG' D hSm hSm' q).mp h))
      (r174w_x_not_retained hG hG' D hSm q)
  by_cases hyw : y = w
  · subst hyw
    exact iff_of_false (fun h => hq ((r174w_w'_retained_iff hG hG' D hSm hSm' q).mp h))
      (r174w_w_not_retained hG hG' D hSm q)
  by_cases hym : y = m
  · subst hym
    exact iff_of_false (r174w_m'_not_retained hG' _) (r174w_m_not_retained hG q)
  exact r174w_retained_iff_of_outside hG hG' D hSm hSm' q (D.outside_of_ne hyx hyw hym)

/-- **Retained crossings of `AB'`: those of `AB`, transported, plus `x'` and `w'`.** -/
theorem r174w_retained_qAB :
    geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))
        (r174w_τ hG hG' D hSm hSm' (r174w_qAB hG hG' D)) =
      insert (crossingTransport hs x) (insert (crossingTransport hs w)
        ((geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) (r174w_qAB hG hG' D)).map
          (crossingTransport hs).toEmbedding)) := by
  classical
  ext y'
  obtain ⟨y, rfl⟩ := (crossingTransport hs).surjective y'
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  by_cases hyx : y = x
  · subst hyx
    exact iff_of_true (r174w_x'_mem_retained hG hG' D hSm hSm') (Or.inl rfl)
  by_cases hyw : y = w
  · subst hyw
    exact iff_of_true (r174w_w'_mem_retained hG hG' D hSm hSm') (Or.inr (Or.inl rfl))
  have hne1 : crossingTransport hs y ≠ crossingTransport hs x := (crossingTransport hs).injective.ne hyx
  have hne2 : crossingTransport hs y ≠ crossingTransport hs w := (crossingTransport hs).injective.ne hyw
  simp only [hne1, hne2, false_or]
  by_cases hym : y = m
  · subst hym
    exact iff_of_false (r174w_m'_not_retained hG' _) (r174w_m_not_retained hG _)
  exact r174w_retained_iff_of_outside hG hG' D hSm hSm' _ (D.outside_of_ne hyx hyw hym)

/-- **`writhe_wall` (GSC (9)): `w_H = w_L + 2`.** -/
theorem r174w_writhe_wall :
    CV.groupedWrithe hG' (r174w_τ hG hG' D hSm hSm' (r174w_qAB hG hG' D)) =
      CV.groupedWrithe hG (r174w_qAB hG hG' D) + 2 := by
  classical
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG' hSm',
    CV.groupedWrithe_eq_card_geoCarrierCrossings hG hSm, r174w_retained_qAB hG hG' D hSm hSm']
  have hwm : crossingTransport hs w ∉ (geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) (r174w_qAB hG hG' D)).map
      (crossingTransport hs).toEmbedding := by
    rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
    exact r174w_w_not_retained hG hG' D hSm _
  have hxm : crossingTransport hs x ∉ insert (crossingTransport hs w)
      ((geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) (r174w_qAB hG hG' D)).map
        (crossingTransport hs).toEmbedding) := by
    rw [Finset.mem_insert, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    rintro (h | h)
    · exact D.xw ((crossingTransport hs).injective h)
    · exact r174w_x_not_retained hG hG' D hSm _ h
  rw [Finset.card_insert_of_notMem hxm, Finset.card_insert_of_notMem hwm, Finset.card_map]
  push_cast
  ring

/-- **The grouped polynomial of every carrier but `AB` is carried across the wall** (record isomorphism
of the two positive lifts, `EXT_homfly_wall`: retained crossings correspond, key orders of their visits
are carried — no reversed pair among outside crossings — and the divide signs agree). -/
theorem r174w_groupedPoly_wall (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) (hq : q ≠ r174w_qAB hG hG' D) :
    CV.groupedPoly hn hG' hSm' (r174w_τ hG hG' D hSm hSm' q) = CV.groupedPoly hn hG hSm q := by
  have hX := r174w_retained_eq_of_ne hG hG' D hSm hSm' q hq
  rw [GT_groupedPoly_eq_homfly, GT_groupedPoly_eq_homfly]
  unfold CV.carrierDiagram
  refine EXT_homfly_wall hn _ _ hs _ _ q _ hX ?_ ?_
  · intro v u hv hu
    have hvT : v.1.val ∉ triangleSupports e f g := r174w_outside_of_retained hG hG' D hSm hv
    exact (r174w_W hG hG' D hSm hSm').key_lt v u (GT_not_rev_of_not_mem_left
      (fun h => hvT ((F1.mem_triangleCrossings e f g v.1).mp h)))
  · intro v _
    exact GT_det_pos_iff_of_sign (D.sign_eq _ _ (by rw [← visit_crossing_val_eq_pair v]; exact v.1.property))

/-- **`omega_wall`: every carrier but `AB` keeps its read `Ω₁` across the wall.** -/
theorem r174w_omega_wall (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) (hq : q ≠ r174w_qAB hG hG' D) :
    CV.Omega1 hn hG' hSm' (r174w_τ hG hG' D hSm hSm' q) = CV.Omega1 hn hG hSm q := by
  unfold CV.Omega1 CV.slot
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG' hSm', CV.groupedWrithe_eq_card_geoCarrierCrossings hG hSm,
    r174w_retained_eq_of_ne hG hG' D hSm hSm' q hq, Finset.card_map,
    GT_carrierR_eq hn hG hG' (r174w_W hG hG' D hSm hSm') hSm hSm' q, r174w_groupedPoly_wall hn hG hG' D hSm hSm' q hq]

/-- The carrier `AB` also keeps its grouped writhe transported set-wise: `w_{AB'} = w_{AB} + 2`, in the
ledger's own `W.τ` form. -/
theorem r174w_writhe_wall_ledger (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqAB : geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) = qAB) :
    CV.groupedWrithe hG' ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ qAB) =
      CV.groupedWrithe hG qAB + 2 := by
  subst hqAB
  exact r174w_writhe_wall hG hG' D hSm hSm'

/-- `omega_wall` in the ledger's own `W.τ` form. -/
theorem r174w_omega_wall_ledger (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqAB : geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) = qAB) :
    ∀ q, q ≠ qAB → CV.Omega1 hn hG' hSm' ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ q) =
      CV.Omega1 hn hG hSm q := by
  subst hqAB
  intro q hq
  exact r174w_omega_wall hn hG hG' D hSm hSm' q hq

end R174W_Wall


/-- Classical equality on crossings, aligned with the geo layer's `insert` (`SM/GeoCarrierCount.lean` reads
`insert v.1 S` with `Classical.propDecidable`); activated locally where `insert`/`Finset (Mark P)` appear. -/
@[instance_reducible] def r174w_decEqCrossing {n : ℕ} {P : LabelledTuple n} : DecidableEq (Crossing P) :=
  fun a b => Classical.propDecidable (a = b)

/-! ### B2. The angle identity at a triangle of directions -/

section R174W_Angle

/-- For three directions with `det(u₁,u₂), det(u₁,u₃), det(u₂,u₃) > 0` the principal angles add:
`∠(u₁,u₂) + ∠(u₂,u₃) = ∠(u₁,u₃)` (all three lie in `(0, π)`; the identity holds mod `2π` by
`arg (zw) = arg z + arg w`, and the bounds pin the integer). -/
theorem r174w_angle_add_of_pos {u₁ u₂ u₃ : Plane} (h12 : 0 < det u₁ u₂) (h13 : 0 < det u₁ u₃)
    (h23 : 0 < det u₂ u₃) :
    principalAngle u₁ u₂ + principalAngle u₂ u₃ = principalAngle u₁ u₃ := by
  have hp12 := CV.regularPair_of_det_ne_zero h12.ne'
  have hp13 := CV.regularPair_of_det_ne_zero h13.ne'
  have hp23 := CV.regularPair_of_det_ne_zero h23.ne'
  have hu1 : u₁ ≠ 0 := hp12.1
  have hu2 : u₂ ≠ 0 := hp12.2.1
  have hu3 : u₃ ≠ 0 := hp13.2.1
  have a12 := (CV.principalAngle_pos_iff hp12).mpr h12
  have a13 := (CV.principalAngle_pos_iff hp13).mpr h13
  have a23 := (CV.principalAngle_pos_iff hp23).mpr h23
  have b12 := (principalAngle_bounds hp12).2
  have b13 := (principalAngle_bounds hp13).2
  have b23 := (principalAngle_bounds hp23).2
  have hprod : cornerRotor u₁ u₂ * cornerRotor u₂ u₃ =
      ((Complex.normSq (planeComplex u₂) : ℝ) : ℂ) * cornerRotor u₁ u₃ := by
    apply Complex.ext
    · simp only [cornerRotor, planeComplex, Complex.mul_re, Complex.mul_im, Complex.star_def,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
      ring
    · simp only [cornerRotor, planeComplex, Complex.mul_re, Complex.mul_im, Complex.star_def,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
      ring
  have key : ((principalAngle u₁ u₂ + principalAngle u₂ u₃ : ℝ) : Real.Angle) =
      (principalAngle u₁ u₃ : Real.Angle) := by
    unfold principalAngle
    rw [Real.Angle.coe_add, ← Complex.arg_mul_coe_angle (cornerRotor_ne_zero hu1 hu2)
      (cornerRotor_ne_zero hu2 hu3), hprod,
      Complex.arg_real_mul _ (Complex.normSq_pos.mpr (planeComplex_ne_zero hu2))]
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at key
  obtain ⟨k, hk⟩ := key
  have hpi := Real.pi_pos
  have hk1 : (k : ℝ) < 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hk2 : (-1 : ℝ) < k := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hk1' : k < 1 := by exact_mod_cast hk1
  have hk2' : -1 < k := by exact_mod_cast hk2
  have hk0 : k = 0 := by omega
  subst hk0
  simp only [Int.cast_zero, mul_zero] at hk
  linarith

/-- The same with all three determinants negative (angles in `(−π, 0)`). -/
theorem r174w_angle_add_of_neg {u₁ u₂ u₃ : Plane} (h12 : det u₁ u₂ < 0) (h13 : det u₁ u₃ < 0)
    (h23 : det u₂ u₃ < 0) :
    principalAngle u₁ u₂ + principalAngle u₂ u₃ = principalAngle u₁ u₃ := by
  have hp12 := CV.regularPair_of_det_ne_zero h12.ne
  have hp13 := CV.regularPair_of_det_ne_zero h13.ne
  have hp23 := CV.regularPair_of_det_ne_zero h23.ne
  have hu1 : u₁ ≠ 0 := hp12.1
  have hu2 : u₂ ≠ 0 := hp12.2.1
  have hu3 : u₃ ≠ 0 := hp13.2.1
  have a12 := (principalAngle_neg_iff u₁ u₂).mpr h12
  have a13 := (principalAngle_neg_iff u₁ u₃).mpr h13
  have a23 := (principalAngle_neg_iff u₂ u₃).mpr h23
  have b12 := (principalAngle_bounds hp12).1
  have b13 := (principalAngle_bounds hp13).1
  have b23 := (principalAngle_bounds hp23).1
  have hprod : cornerRotor u₁ u₂ * cornerRotor u₂ u₃ =
      ((Complex.normSq (planeComplex u₂) : ℝ) : ℂ) * cornerRotor u₁ u₃ := by
    apply Complex.ext
    · simp only [cornerRotor, planeComplex, Complex.mul_re, Complex.mul_im, Complex.star_def,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
      ring
    · simp only [cornerRotor, planeComplex, Complex.mul_re, Complex.mul_im, Complex.star_def,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
      ring
  have key : ((principalAngle u₁ u₂ + principalAngle u₂ u₃ : ℝ) : Real.Angle) =
      (principalAngle u₁ u₃ : Real.Angle) := by
    unfold principalAngle
    rw [Real.Angle.coe_add, ← Complex.arg_mul_coe_angle (cornerRotor_ne_zero hu1 hu2)
      (cornerRotor_ne_zero hu2 hu3), hprod,
      Complex.arg_real_mul _ (Complex.normSq_pos.mpr (planeComplex_ne_zero hu2))]
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at key
  obtain ⟨k, hk⟩ := key
  have hpi := Real.pi_pos
  have hk1 : (k : ℝ) < 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hk2 : (-1 : ℝ) < k := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hk1' : k < 1 := by exact_mod_cast hk1
  have hk2' : -1 < k := by exact_mod_cast hk2
  have hk0 : k = 0 := by omega
  subst hk0
  simp only [Int.cast_zero, mul_zero] at hk
  linarith

end R174W_Angle

/-! ### B1. The weight and the rotation of a carrier through its corner marks -/

section R174W_Corners

attribute [local instance] Classical.propDecidable
attribute [local instance high] r174w_decEqCrossing

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-- The intrinsic turn sign of a corner mark: `turn P i` at a vertex, the crossing sign
`sgn det(edge of v, edge of twin v)` at a (selected) visit. -/
def r174w_tau (P : LabelledTuple n) : Mark P → SignType
  | Sum.inl i => turn P i
  | Sum.inr v => crossingSign P v.2.val (visitTwin v).2.val

/-- The intrinsic principal turn of a corner mark. -/
noncomputable def r174w_theta (P : LabelledTuple n) : Mark P → ℝ
  | Sum.inl i => principalAngle (edge P (i - 1)) (edge P i)
  | Sum.inr v => principalAngle (edge P v.2.val) (edge P (visitTwin v).2.val)

omit [NeZero n] in
theorem r174w_tau_vertex (i : ZMod n) : r174w_tau P (Sum.inl i) = turn P i := rfl
omit [NeZero n] in
theorem r174w_tau_visit (v : Visit P) :
    r174w_tau P (Sum.inr v) = crossingSign P v.2.val (visitTwin v).2.val := rfl
omit [NeZero n] in
theorem r174w_theta_vertex (i : ZMod n) :
    r174w_theta P (Sum.inl i) = principalAngle (edge P (i - 1)) (edge P i) := rfl
omit [NeZero n] in
theorem r174w_theta_visit (v : Visit P) :
    r174w_theta P (Sum.inr v) = principalAngle (edge P v.2.val) (edge P (visitTwin v).2.val) := rfl

omit [NeZero n] in
/-- The sign of the principal turn is the turn sign (when nonzero). -/
theorem r174w_sign_theta (a : Mark P) (h : r174w_tau P a ≠ 0) :
    SignType.sign (r174w_theta P a) = r174w_tau P a := by
  cases a with
  | inl i =>
    rw [r174w_tau_vertex, turn_det] at h ⊢
    exact principalAngle_sign (CV.regularPair_of_det_ne_zero (sign_ne_zero.mp h))
  | inr v =>
    rw [r174w_tau_visit] at h ⊢
    unfold crossingSign at h ⊢
    exact principalAngle_sign (CV.regularPair_of_det_ne_zero (sign_ne_zero.mp h))

/-- The corner marks of a carrier `q` of `S`: the owned original vertices and selected visits. -/
noncomputable def r174w_corners (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : Finset (Mark P) :=
  Finset.univ.filter (fun a => geoOwner hP S a = q ∧ IsTrueCorner S a)

theorem r174w_mem_corners (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S)
    (a : Mark P) : a ∈ r174w_corners hP S q ↔ geoOwner hP S a = q ∧ IsTrueCorner S a := by
  unfold r174w_corners
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem r174w_corners_eq_image (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) :
    r174w_corners hP S q = Finset.univ.image (geoCornerMark hP S q) := by
  classical
  ext a
  rw [r174w_mem_corners, Finset.mem_image]
  constructor
  · rintro ⟨hq, hc⟩
    obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hP S q a hq hc
    exact ⟨k, Finset.mem_univ _, hk⟩
  · rintro ⟨k, -, rfl⟩
    exact geoCornerMark_mem hP S q k

theorem r174w_card_corners (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : (r174w_corners hP S q).card = geoCornerCount hP S q := by
  classical
  rw [r174w_corners_eq_image, Finset.card_image_of_injective _ (geoCornerMark_injective hP S q),
    Finset.card_univ, ZMod.card]

/-- The turn of the corner polygon at `c_k` is the intrinsic turn sign of the corner mark `c_k`. -/
theorem r174w_turn_eq (hn : 3 ≤ n) (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : GeoIndependent hP S) (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    turn (geoCornerPolygon hP S q) k = r174w_tau P (geoCornerMark hP S q k) := by
  have hc := isTrueCorner_geoCornerMark hP S q k
  cases hm : geoCornerMark hP S q k with
  | inl i =>
    rw [geoCornerPolygon_turn_vertex hn hP hS q k i hm]
    rfl
  | inr v =>
    rw [hm] at hc
    exact geoCornerPolygon_turn_visit hn hP hS q k v hc hm

/-- The principal turn of the corner polygon at `c_k` is the intrinsic principal turn of `c_k`
(the two incident edges are positive multiples of the original in/out edges). -/
theorem r174w_principalTurn_eq (hn : 3 ≤ n) (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : GeoIndependent hP S) (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    CV.principalTurn (geoCornerPolygon hP S q) k = r174w_theta P (geoCornerMark hP S q k) := by
  obtain ⟨c, hc, he⟩ := geoCornerPolygon_edge_pred_smul hn hP hS q k
  obtain ⟨c', hc', he'⟩ := geoCornerPolygon_edge_smul hn hP hS q k
  unfold CV.principalTurn
  rw [he, he', principalAngle_smul hc hc']
  have hcorner := isTrueCorner_geoCornerMark hP S q k
  cases hm : geoCornerMark hP S q k with
  | inl i =>
    rw [geoInEdge_vertex hn hP i, geoOutSlot_vertex]
    rfl
  | inr v =>
    rw [hm] at hcorner
    rw [geoInEdge_visit hn hP v, geoOutSlot_selected hP S v hcorner]
    rfl

open Classical in
/-- The selector read on a set of corner marks: `1` if all right turns, `(−1)^|C|` if all left, else `0`. -/
noncomputable def r174w_F (P : LabelledTuple n) (C : Finset (Mark P)) : ℤ :=
  if (∀ a ∈ C, r174w_tau P a = -1) then 1
  else if (∀ a ∈ C, r174w_tau P a = 1) then (-1) ^ C.card else 0

/-- `wt(q)` is `F` of the corner-mark set. -/
theorem r174w_weight_eq (hn : 3 ≤ n) (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : GeoIndependent hP S) (q : GeoComponent hP S) :
    CV.weight hP S q = r174w_F P (r174w_corners hP S q) := by
  classical
  have h1 : (∀ i, turn (geoCornerPolygon hP S q) i = -1) ↔
      (∀ a ∈ r174w_corners hP S q, r174w_tau P a = -1) := by
    rw [r174w_corners_eq_image]
    constructor
    · intro h a ha
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
      rw [← r174w_turn_eq hn hP hS q k]
      exact h k
    · intro h k
      rw [r174w_turn_eq hn hP hS q k]
      exact h _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  have h2 : (∀ i, turn (geoCornerPolygon hP S q) i = 1) ↔
      (∀ a ∈ r174w_corners hP S q, r174w_tau P a = 1) := by
    rw [r174w_corners_eq_image]
    constructor
    · intro h a ha
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
      rw [← r174w_turn_eq hn hP hS q k]
      exact h k
    · intro h k
      rw [r174w_turn_eq hn hP hS q k]
      exact h _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  unfold CV.weight geoCarrierSelector cornerSelector r174w_F
  by_cases hA : ∀ i, turn (geoCornerPolygon hP S q) i = -1
  · rw [ite_eq_left hA, ite_eq_left (h1.mp hA)]
  · rw [ite_eq_right hA, ite_eq_right (fun h => hA (h1.mpr h))]
    by_cases hB : ∀ i, turn (geoCornerPolygon hP S q) i = 1
    · rw [ite_eq_left hB, ite_eq_left (h2.mp hB), r174w_card_corners]
    · rw [ite_eq_right hB, ite_eq_right (fun h => hB (h2.mpr h))]

/-- `2π · rot(q) = Σ_{corner marks a of q} θ(a)` (CV:lem:turnlift (ii) read on the corner marks). -/
theorem r174w_two_pi_rot (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    2 * Real.pi * (CV.rot (geoCornerPolygon hG.crossingGeometry S q) (CV.carrierPolygon_cvRegular hn hG hS q) : ℝ) =
      ∑ a ∈ r174w_corners hG.crossingGeometry S q, r174w_theta P a := by
  classical
  rw [CV.two_pi_mul_rot, r174w_corners_eq_image,
    Finset.sum_image (fun a _ b _ h => geoCornerMark_injective hG.crossingGeometry S q h)]
  exact Finset.sum_congr rfl fun k _ =>
    r174w_principalTurn_eq hn _ (CV.geoIndependent_of_mem_Ind _ hS) q k

/-- `R(q)` as an integer is `|rot|` of the corner polygon. -/
theorem r174w_carrierR_cast (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    (CV.carrierR hn hG hS q : ℤ) =
      |CV.rot (geoCornerPolygon hG.crossingGeometry S q) (CV.carrierPolygon_cvRegular hn hG hS q)| :=
  CV.carrierR_cast hn hG hS q

/-- Under a nonzero selector every corner turn of `q` is the common sign `s = ±1`. -/
theorem r174w_uniform_of_weight_ne_zero (hn : 3 ≤ n) (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : GeoIndependent hP S) (q : GeoComponent hP S) (h : CV.weight hP S q ≠ 0) :
    (∀ a ∈ r174w_corners hP S q, r174w_tau P a = -1) ∨ (∀ a ∈ r174w_corners hP S q, r174w_tau P a = 1) := by
  classical
  rw [r174w_weight_eq hn hP hS q] at h
  unfold r174w_F at h
  by_cases hA : ∀ a ∈ r174w_corners hP S q, r174w_tau P a = -1
  · exact Or.inl hA
  · right
    rw [ite_eq_right hA] at h
    by_contra hB
    rw [ite_eq_right hB] at h
    exact h rfl

/-- All corner turns `= 1` gives `rot ≥ 1`; all `= −1` gives `rot ≤ −1` (CV:lem:uniformrot (i)). -/
theorem r174w_rot_of_uniform (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (hu : (∀ a ∈ r174w_corners hG.crossingGeometry S q, r174w_tau P a = -1) ∨
      (∀ a ∈ r174w_corners hG.crossingGeometry S q, r174w_tau P a = 1)) :
    (CV.rot (geoCornerPolygon hG.crossingGeometry S q) (CV.carrierPolygon_cvRegular hn hG hS q) ≤ -1 ∧
        ∀ a ∈ r174w_corners hG.crossingGeometry S q, r174w_tau P a = -1) ∨
    (1 ≤ CV.rot (geoCornerPolygon hG.crossingGeometry S q) (CV.carrierPolygon_cvRegular hn hG hS q) ∧
        ∀ a ∈ r174w_corners hG.crossingGeometry S q, r174w_tau P a = 1) := by
  have hSi := CV.geoIndependent_of_mem_Ind _ hS
  rcases hu with hu | hu
  · left
    refine ⟨CV.uniformrot.neg_le_neg_one _ _ _ fun k => ?_, hu⟩
    rw [r174w_principalTurn_eq hn _ hSi q k]
    have hk := hu _ ((r174w_mem_corners _ _ q _).mpr (geoCornerMark_mem _ S q k))
    have hs := r174w_sign_theta (P := P) (geoCornerMark hG.crossingGeometry S q k) (by rw [hk]; decide)
    rw [hk] at hs
    exact sign_eq_neg_one_iff.mp hs
  · right
    refine ⟨CV.uniformrot.pos_ge_one _ _ _ fun k => ?_, hu⟩
    rw [r174w_principalTurn_eq hn _ hSi q k]
    have hk := hu _ ((r174w_mem_corners _ _ q _).mpr (geoCornerMark_mem _ S q k))
    have hs := r174w_sign_theta (P := P) (geoCornerMark hG.crossingGeometry S q k) (by rw [hk]; decide)
    rw [hk] at hs
    exact sign_eq_one_iff.mp hs

/-! #### The selector on split corner sets, and the rotation sum -/

/-- `F` on `insert a C₁`, `insert b C₂` against `insert c (C₁ ∪ C₂)` with `τ(a) = τ(b) = τ(c) = τ ≠ 0`:
`F(A) F(B) = −τ F(AB)`. -/
theorem r174w_F_split (C₁ C₂ : Finset (Mark P)) (hdisj : Disjoint C₁ C₂) (a b c : Mark P)
    (ha : a ∉ C₁) (hb : b ∉ C₂) (hc : c ∉ C₁ ∪ C₂) (τ : SignType) (hτ : τ ≠ 0)
    (hta : r174w_tau P a = τ) (htb : r174w_tau P b = τ) (htc : r174w_tau P c = τ) :
    r174w_F P (insert a C₁) * r174w_F P (insert b C₂) = -(τ : ℤ) * r174w_F P (insert c (C₁ ∪ C₂)) := by
  unfold r174w_F
  simp only [Finset.forall_mem_insert, Finset.forall_mem_union, hta, htb, htc,
    Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb, Finset.card_insert_of_notMem hc,
    Finset.card_union_of_disjoint hdisj]
  rcases τ with _ | _ | _
  · exact absurd rfl hτ
  · have e1 : ((SignType.neg : SignType) = -1) := rfl
    have e2 : ¬ ((-1 : SignType) = 1) := by decide
    have hneg : ((-1 : SignType) : ℤ) = -1 := rfl
    simp only [e1, e2, true_and, false_and, ↓reduceIte, hneg]
    by_cases h1 : ∀ x ∈ C₁, r174w_tau P x = -1 <;> by_cases h2 : ∀ x ∈ C₂, r174w_tau P x = -1
    · simp only [eq_true h1, eq_true h2, and_self, ↓reduceIte]; norm_num
    · simp only [eq_true h1, eq_false h2, and_false, ↓reduceIte]; norm_num
    · simp only [eq_false h1, eq_true h2, false_and, ↓reduceIte]; norm_num
    · simp only [eq_false h1, eq_false h2, and_self, ↓reduceIte]; norm_num
  · have e1 : ¬ ((1 : SignType) = -1) := by decide
    have e2 : ((SignType.pos : SignType) = 1) := rfl
    have hpos : ((1 : SignType) : ℤ) = 1 := rfl
    simp only [e2, e1, true_and, false_and, ↓reduceIte, hpos]
    by_cases h1 : ∀ x ∈ C₁, r174w_tau P x = 1 <;> by_cases h2 : ∀ x ∈ C₂, r174w_tau P x = 1
    · simp only [eq_true h1, eq_true h2, and_self, ↓reduceIte]; ring
    · simp only [eq_true h1, eq_false h2, and_false, ↓reduceIte]; ring
    · simp only [eq_false h1, eq_true h2, false_and, ↓reduceIte]; ring
    · simp only [eq_false h1, eq_false h2, and_self, ↓reduceIte]; ring

/-- `F` on `insert a (insert b C)` against `insert c C` with `τ(a) = τ(b) = τ(c) = τ ≠ 0`: `F(C') = −τ F(C)`. -/
theorem r174w_F_two (C : Finset (Mark P)) (a b c : Mark P) (ha : a ∉ insert b C) (hb : b ∉ C) (hc : c ∉ C)
    (τ : SignType) (hτ : τ ≠ 0) (hta : r174w_tau P a = τ) (htb : r174w_tau P b = τ) (htc : r174w_tau P c = τ) :
    r174w_F P (insert a (insert b C)) = -(τ : ℤ) * r174w_F P (insert c C) := by
  unfold r174w_F
  simp only [Finset.forall_mem_insert, hta, htb, htc, Finset.card_insert_of_notMem ha,
    Finset.card_insert_of_notMem hb, Finset.card_insert_of_notMem hc]
  rcases τ with _ | _ | _
  · exact absurd rfl hτ
  · have e1 : ((SignType.neg : SignType) = -1) := rfl
    have e2 : ¬ ((-1 : SignType) = 1) := by decide
    have hneg : ((-1 : SignType) : ℤ) = -1 := rfl
    simp only [e1, e2, true_and, false_and, ↓reduceIte, hneg]
    by_cases h1 : ∀ x ∈ C, r174w_tau P x = -1
    · simp only [eq_true h1, ↓reduceIte]; norm_num
    · simp only [eq_false h1, ↓reduceIte]; norm_num
  · have e1 : ¬ ((1 : SignType) = -1) := by decide
    have e2 : ((SignType.pos : SignType) = 1) := rfl
    have hpos : ((1 : SignType) : ℤ) = 1 := rfl
    simp only [e2, e1, true_and, false_and, ↓reduceIte, hpos]
    by_cases h1 : ∀ x ∈ C, r174w_tau P x = 1
    · simp only [eq_true h1, ↓reduceIte]; ring
    · simp only [eq_false h1, ↓reduceIte]; ring

/-- **The rotations add** when the corner sets split as `insert c (RA ∪ RB)` against `insert a RA`,
`insert b RB` with `θ(a) + θ(b) = θ(c)`. -/
theorem r174w_rot_add (hn : 3 ≤ n) (hG : CV.Generic P) {S₁ S₂ : Finset (Crossing P)}
    (hS₁ : S₁ ∈ CV.Ind hG.crossingGeometry) (hS₂ : S₂ ∈ CV.Ind hG.crossingGeometry)
    (qAB : GeoComponent hG.crossingGeometry S₁) (qA qB : GeoComponent hG.crossingGeometry S₂)
    (RA RB : Finset (Mark P)) (hdisj : Disjoint RA RB) (a b c : Mark P)
    (ha : a ∉ RA) (hb : b ∉ RB) (hc : c ∉ RA ∪ RB)
    (hA : r174w_corners hG.crossingGeometry S₂ qA = insert a RA)
    (hB : r174w_corners hG.crossingGeometry S₂ qB = insert b RB)
    (hAB : r174w_corners hG.crossingGeometry S₁ qAB = insert c (RA ∪ RB))
    (hθ : r174w_theta P a + r174w_theta P b = r174w_theta P c) :
    CV.rot (geoCornerPolygon hG.crossingGeometry S₁ qAB) (CV.carrierPolygon_cvRegular hn hG hS₁ qAB) =
      CV.rot (geoCornerPolygon hG.crossingGeometry S₂ qA) (CV.carrierPolygon_cvRegular hn hG hS₂ qA) +
        CV.rot (geoCornerPolygon hG.crossingGeometry S₂ qB) (CV.carrierPolygon_cvRegular hn hG hS₂ qB) := by
  classical
  have h1 := r174w_two_pi_rot hn hG hS₁ qAB
  have h2 := r174w_two_pi_rot hn hG hS₂ qA
  have h3 := r174w_two_pi_rot hn hG hS₂ qB
  rw [hAB, Finset.sum_insert hc, Finset.sum_union hdisj] at h1
  rw [hA, Finset.sum_insert ha] at h2
  rw [hB, Finset.sum_insert hb] at h3
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  apply Int.cast_injective (α := ℝ)
  apply mul_left_cancel₀ hpi
  rw [Int.cast_add, mul_add, h1, h2, h3, ← hθ]
  ring

/-- The same with `insert a (insert b RC)` against `insert c RC`: the rotations agree. -/
theorem r174w_rot_eq_two (hn : 3 ≤ n) (hG : CV.Generic P) {S₁ S₂ : Finset (Crossing P)}
    (hS₁ : S₁ ∈ CV.Ind hG.crossingGeometry) (hS₂ : S₂ ∈ CV.Ind hG.crossingGeometry)
    (qC : GeoComponent hG.crossingGeometry S₁) (qC' : GeoComponent hG.crossingGeometry S₂)
    (RC : Finset (Mark P)) (a b c : Mark P) (ha : a ∉ insert b RC) (hb : b ∉ RC) (hc : c ∉ RC)
    (hC' : r174w_corners hG.crossingGeometry S₂ qC' = insert a (insert b RC))
    (hC : r174w_corners hG.crossingGeometry S₁ qC = insert c RC)
    (hθ : r174w_theta P a + r174w_theta P b = r174w_theta P c) :
    CV.rot (geoCornerPolygon hG.crossingGeometry S₂ qC') (CV.carrierPolygon_cvRegular hn hG hS₂ qC') =
      CV.rot (geoCornerPolygon hG.crossingGeometry S₁ qC) (CV.carrierPolygon_cvRegular hn hG hS₁ qC) := by
  classical
  have h1 := r174w_two_pi_rot hn hG hS₁ qC
  have h2 := r174w_two_pi_rot hn hG hS₂ qC'
  rw [hC, Finset.sum_insert hc] at h1
  rw [hC', Finset.sum_insert ha, Finset.sum_insert hb] at h2
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  apply Int.cast_injective (α := ℝ)
  apply mul_left_cancel₀ hpi
  rw [h1, h2, ← hθ]
  ring

/-- `R(AB) = R(A) + R(B)` under a nonzero selector of `AB` (the split of `r174w_rot_add`, with
`τ(a) = τ(b) = τ(c)`: `A`, `B` inherit the uniform sign, so the rotations have one sign and the
absolute values add). -/
theorem r174w_carrierR_add_of (hn : 3 ≤ n) (hG : CV.Generic P) {S₁ S₂ : Finset (Crossing P)}
    (hS₁ : S₁ ∈ CV.Ind hG.crossingGeometry) (hS₂ : S₂ ∈ CV.Ind hG.crossingGeometry)
    (qAB : GeoComponent hG.crossingGeometry S₁) (qA qB : GeoComponent hG.crossingGeometry S₂)
    (RA RB : Finset (Mark P)) (hdisj : Disjoint RA RB) (a b c : Mark P)
    (ha : a ∉ RA) (hb : b ∉ RB) (hc : c ∉ RA ∪ RB)
    (hA : r174w_corners hG.crossingGeometry S₂ qA = insert a RA)
    (hB : r174w_corners hG.crossingGeometry S₂ qB = insert b RB)
    (hAB : r174w_corners hG.crossingGeometry S₁ qAB = insert c (RA ∪ RB))
    (hθ : r174w_theta P a + r174w_theta P b = r174w_theta P c)
    (hτa : r174w_tau P a = r174w_tau P c) (hτb : r174w_tau P b = r174w_tau P c)
    (hw : CV.weight hG.crossingGeometry S₁ qAB ≠ 0) :
    CV.carrierR hn hG hS₁ qAB = CV.carrierR hn hG hS₂ qA + CV.carrierR hn hG hS₂ qB := by
  classical
  have hrot := r174w_rot_add hn hG hS₁ hS₂ qAB qA qB RA RB hdisj a b c ha hb hc hA hB hAB hθ
  have hcAB : c ∈ r174w_corners hG.crossingGeometry S₁ qAB := by rw [hAB]; exact Finset.mem_insert_self _ _
  have hRA : ∀ z ∈ RA, z ∈ r174w_corners hG.crossingGeometry S₁ qAB := fun z hz => by
    rw [hAB]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hz)
  have hRB : ∀ z ∈ RB, z ∈ r174w_corners hG.crossingGeometry S₁ qAB := fun z hz => by
    rw [hAB]; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hz)
  have hu := r174w_uniform_of_weight_ne_zero hn hG.crossingGeometry (CV.geoIndependent_of_mem_Ind _ hS₁) qAB hw
  -- `A` and `B` inherit the uniform sign
  have huA : (∀ z ∈ r174w_corners hG.crossingGeometry S₂ qA, r174w_tau P z = -1) ∨
      (∀ z ∈ r174w_corners hG.crossingGeometry S₂ qA, r174w_tau P z = 1) := by
    rw [hA]
    rcases hu with hu | hu
    · left; rw [Finset.forall_mem_insert]; exact ⟨hτa.trans (hu c hcAB), fun z hz => hu z (hRA z hz)⟩
    · right; rw [Finset.forall_mem_insert]; exact ⟨hτa.trans (hu c hcAB), fun z hz => hu z (hRA z hz)⟩
  have huB : (∀ z ∈ r174w_corners hG.crossingGeometry S₂ qB, r174w_tau P z = -1) ∨
      (∀ z ∈ r174w_corners hG.crossingGeometry S₂ qB, r174w_tau P z = 1) := by
    rw [hB]
    rcases hu with hu | hu
    · left; rw [Finset.forall_mem_insert]; exact ⟨hτb.trans (hu c hcAB), fun z hz => hu z (hRB z hz)⟩
    · right; rw [Finset.forall_mem_insert]; exact ⟨hτb.trans (hu c hcAB), fun z hz => hu z (hRB z hz)⟩
  have hsA := r174w_rot_of_uniform hn hG hS₂ qA huA
  have hsB := r174w_rot_of_uniform hn hG hS₂ qB huB
  unfold CV.carrierR CV.rotAbs
  rw [hrot]
  rcases hsA with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩ <;> rcases hsB with ⟨hB1, hB2⟩ | ⟨hB1, hB2⟩
  · exact Int.natAbs_add_of_nonpos (by omega) (by omega)
  · exfalso
    -- mixed signs: `c` would have both turn signs
    have h1 := hA2 a (by rw [hA]; exact Finset.mem_insert_self _ _)
    have h2 := hB2 b (by rw [hB]; exact Finset.mem_insert_self _ _)
    rw [hτa] at h1; rw [hτb] at h2; rw [h1] at h2; exact absurd h2 (by decide)
  · exfalso
    have h1 := hA2 a (by rw [hA]; exact Finset.mem_insert_self _ _)
    have h2 := hB2 b (by rw [hB]; exact Finset.mem_insert_self _ _)
    rw [hτa] at h1; rw [hτb] at h2; rw [h1] at h2; exact absurd h2 (by decide)
  · exact Int.natAbs_add_of_nonneg (by omega) (by omega)

end R174W_Corners


/-! ### C0. Real cyclic-order helpers -/

section R174W_Cyc

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem r174w_cyc_trans_left {a u v w : ℝ} (h1 : cycBetween a u v) (h2 : cycBetween a v w) :
    cycBetween a u w := by
  unfold cycBetween at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    | (exfalso; linarith)

theorem r174w_cyc_trans_right {a u v w : ℝ} (h1 : cycBetween a v w) (h2 : cycBetween v u w) :
    cycBetween a u w := by
  unfold cycBetween at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    | (exfalso; linarith)

/-- Two points of the arc `(a, w)` are ordered: `u` before `v` or after. -/
theorem r174w_cyc_split {a u v w : ℝ} (h1 : cycBetween a u w) (h2 : cycBetween a v w) (huv : u ≠ v) :
    cycBetween a u v ∨ cycBetween v u w := by
  rcases lt_or_gt_of_ne huv with h | h
  · unfold cycBetween at *
    rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
      first
      | exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
      | exact Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
      | exact Or.inl (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
      | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
      | (exfalso; linarith)
  · unfold cycBetween at *
    rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
      first
      | exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
      | exact Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
      | exact Or.inl (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
      | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
      | (exfalso; linarith)

/-- The arcs `(a, v)` and `(v, a)` are disjoint. -/
theorem r174w_cyc_asymm {a u v : ℝ} (h1 : cycBetween a u v) (h2 : cycBetween v u a) : False := by
  unfold cycBetween at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

/-- `u ∈ (a, v)`, `v ∈ (a, w)` give `v ∈ (u, w)`. -/
theorem r174w_cyc_mid {a u v w : ℝ} (h1 : cycBetween a u v) (h2 : cycBetween a v w) :
    cycBetween u v w := by
  unfold cycBetween at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    | (exfalso; linarith)

/-- `u ∈ (a, w)`, `v ∈ (u, w)` give `w ∈ (v, u)` (wrapping through `a`). -/
theorem r174w_cyc_wrap {a u v w : ℝ} (h1 : cycBetween a u w) (h2 : cycBetween u v w) :
    cycBetween v w u := by
  unfold cycBetween at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    | (exfalso; linarith)

theorem r174w_cyc_ne_left {a u v : ℝ} (h : cycBetween a u v) : a ≠ u := by
  rintro rfl; exact not_cycBetween_self_left _ _ h

theorem r174w_cyc_ne_right {a u v : ℝ} (h : cycBetween a u v) : u ≠ v := by
  rintro rfl; exact not_cycBetween_self_mid _ _ h

end R174W_Cyc

/-! ### C1–C4. The configuration on the two-edge side: supports, owners, child data -/

section R174W_Config

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)

attribute [local instance] Classical.propDecidable
attribute [local instance high] r174w_decEqCrossing

/-- The child data of one insertion, read on the mark keys: the new carrier of `v` is `v` together with
the marks of the old carrier strictly between `twin v` and `v`; the new carrier of `twin v` is `twin v`
with the marks strictly between `v` and `twin v`. -/
theorem r174w_child (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T) (v : Visit P)
    (hv : v.1 ∉ T) (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v))) :
    (∀ z : Mark P, geoOwner hP (insert v.1 T) z = geoOwner hP (insert v.1 T) (Sum.inr v) ↔
      z = Sum.inr v ∨ (cycBetween (geoMarkKey hP (Sum.inr (visitTwin v))) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr v)) ∧ geoOwner hP T z = geoOwner hP T (Sum.inr v))) ∧
    (∀ z : Mark P, geoOwner hP (insert v.1 T) z = geoOwner hP (insert v.1 T) (Sum.inr (visitTwin v)) ↔
      z = Sum.inr (visitTwin v) ∨ (cycBetween (geoMarkKey hP (Sum.inr v)) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr (visitTwin v))) ∧ geoOwner hP T z = geoOwner hP T (Sum.inr v))) := by
  obtain ⟨k, A, B, hrot, -, -, -, hL, hR, -, -⟩ :=
    geoSmoothingSuccessor_insert_child_data hP T hI v hv hc
  refine ⟨fun z => ?_, fun z => ?_⟩
  · rw [hL z, List.mem_cons, geoMarkList_filter_right_iff hP T _ k _ _ A B hrot z]
    exact Iff.rfl
  · rw [hR z, List.mem_cons, geoMarkList_filter_left_iff hP T _ k _ _ A B hrot z]
    exact Iff.rfl

include D


theorem r174w_Q_indep : GeoIndependent hP Q := CV.geoIndependent_of_mem_Ind hP D.Q_ind

/-- `Q ∪ {y}` is independent for every triangle crossing `y` (full availability). -/
theorem r174w_insert_indep {y : Crossing P} (hy : y.val ∈ triangleSupports e f g) :
    GeoIndependent hP (insert y Q) := by
  intro a ha b hb hab
  rw [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact absurd rfl hab
  · exact fun h => D.Q_avail b hb a hy (geometricInterlaces_symm hP h)
  · exact D.Q_avail a ha b hy
  · exact r174w_Q_indep D a ha b hb hab

theorem r174w_Sx_indep : GeoIndependent hP (insert x Q) := r174w_insert_indep D D.xT
theorem r174w_Sm_indep : GeoIndependent hP (insert m Q) := r174w_insert_indep D D.mT

theorem r174w_Sxw_indep : GeoIndependent hP (insert w (insert x Q)) := by
  intro a ha b hb hab
  rw [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact absurd rfl hab
  · rw [Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · exact fun h => D.hxw (geometricInterlaces_symm hP h)
    · exact fun h => D.Q_avail b hb a D.wT (geometricInterlaces_symm hP h)
  · rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · exact D.hxw
    · exact D.Q_avail a ha b D.wT
  · exact r174w_Sx_indep D a ha b hb hab

theorem r174w_w_not_mem_Sx : w ∉ insert x Q := by
  rw [Finset.mem_insert]
  rintro (h | h)
  · exact D.xw h.symm
  · exact r174c_w_not_mem_Q D h

theorem r174w_m_not_mem_Sx : m ∉ insert x Q := by
  rw [Finset.mem_insert]
  rintro (h | h)
  · exact D.xm h.symm
  · exact r174c_m_not_mem_Q D h

theorem r174w_m_not_mem_Sxw : m ∉ insert w (insert x Q) := by
  rw [Finset.mem_insert]
  rintro (h | h)
  · exact D.wm h.symm
  · exact r174w_m_not_mem_Sx D h

theorem r174w_x_not_mem_Sm' : x ∉ insert m Q := by
  rw [Finset.mem_insert]
  rintro (h | h)
  · exact D.xm h
  · exact r174c_x_not_mem_Q D h

theorem r174w_w_not_mem_Sm' : w ∉ insert m Q := by
  rw [Finset.mem_insert]
  rintro (h | h)
  · exact D.wm h
  · exact r174c_w_not_mem_Q D h

/-! #### Pair owners (both visits of an unselected non-neighbour on one carrier) -/

theorem r174w_ownerQ_m : geoOwner hP Q (Sum.inr D.m₁) = geoOwner hP Q (Sum.inr D.m₃) := by
  have h := geoIndependent_remaining_pair_owners hP (r174w_Sm_indep D) Q (Finset.subset_insert _ _)
    D.m₁ (Finset.mem_insert_self _ _) (r174c_m_not_mem_Q D)
  rwa [D.twin_m₁] at h

theorem r174w_ownerQ_x : geoOwner hP Q (Sum.inr D.x₁) = geoOwner hP Q (Sum.inr D.x₂) := by
  have h := geoIndependent_remaining_pair_owners hP (r174w_Sx_indep D) Q (Finset.subset_insert _ _)
    D.x₁ (Finset.mem_insert_self _ _) (r174c_x_not_mem_Q D)
  rwa [D.twin_x₁] at h

theorem r174w_ownerx_w :
    geoOwner hP (insert x Q) (Sum.inr D.w₂) = geoOwner hP (insert x Q) (Sum.inr D.w₃) := by
  have h := geoIndependent_remaining_pair_owners hP (r174w_Sxw_indep D) (insert x Q)
    (Finset.subset_insert _ _) D.w₂ (Finset.mem_insert_self _ _) (r174w_w_not_mem_Sx D)
  rwa [D.twin_w₂] at h

/-! #### Separations: the two visits of a selected crossing, or of a neighbour, lie on different carriers -/

theorem r174w_sep_m_Sm : geoOwner hP (insert m Q) (Sum.inr D.m₁) ≠ geoOwner hP (insert m Q) (Sum.inr D.m₃) := by
  have h := geo_selected_visits_separated hP (r174w_Sm_indep D) D.m₁ (Finset.mem_insert_self _ _)
  rwa [D.twin_m₁] at h

theorem r174w_sep_x_Sx : geoOwner hP (insert x Q) (Sum.inr D.x₁) ≠ geoOwner hP (insert x Q) (Sum.inr D.x₂) := by
  have h := geo_selected_visits_separated hP (r174w_Sx_indep D) D.x₁ (Finset.mem_insert_self _ _)
  rwa [D.twin_x₁] at h

theorem r174w_sep_x_Sxw :
    geoOwner hP (insert w (insert x Q)) (Sum.inr D.x₁) ≠ geoOwner hP (insert w (insert x Q)) (Sum.inr D.x₂) := by
  have h := geo_selected_visits_separated hP (r174w_Sxw_indep D) D.x₁
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  rwa [D.twin_x₁] at h

theorem r174w_sep_w_Sxw :
    geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₂) ≠ geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₃) := by
  have h := geo_selected_visits_separated hP (r174w_Sxw_indep D) D.w₂ (Finset.mem_insert_self _ _)
  rwa [D.twin_w₂] at h

omit D in
/-- A neighbour of a selected crossing has its two visits on different carriers. -/
theorem r174w_sep_of_neighbor {S : Finset (Crossing P)} (hS : GeoIndependent hP S) {y s : Crossing P}
    (hsS : s ∈ S) (hys : GeometricInterlaces hP y s) (v : Visit P) (hv : v.1 = y) :
    geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v)) :=
  geo_neighbor_visit_owners_ne hP hS ((mem_geoSupportNeighbors hP S y).mpr ⟨s, hsS, hys⟩) v hv

theorem r174w_sep_x_Sm : geoOwner hP (insert m Q) (Sum.inr D.x₁) ≠ geoOwner hP (insert m Q) (Sum.inr D.x₂) := by
  have h := r174w_sep_of_neighbor (r174w_Sm_indep D) (Finset.mem_insert_self m Q) D.hxm D.x₁ rfl
  rwa [D.twin_x₁] at h

theorem r174w_sep_w_Sm : geoOwner hP (insert m Q) (Sum.inr D.w₂) ≠ geoOwner hP (insert m Q) (Sum.inr D.w₃) := by
  have h := r174w_sep_of_neighbor (r174w_Sm_indep D) (Finset.mem_insert_self m Q) D.hwm D.w₂ rfl
  rwa [D.twin_w₂] at h

theorem r174w_sep_m_Sx : geoOwner hP (insert x Q) (Sum.inr D.m₁) ≠ geoOwner hP (insert x Q) (Sum.inr D.m₃) := by
  have h := r174w_sep_of_neighbor (r174w_Sx_indep D) (Finset.mem_insert_self x Q)
    (geometricInterlaces_symm hP D.hxm) D.m₁ rfl
  rwa [D.twin_m₁] at h

theorem r174w_sep_m_Sxw :
    geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁) ≠ geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃) := by
  have h := r174w_sep_of_neighbor (r174w_Sxw_indep D) (Finset.mem_insert_self w _)
    (geometricInterlaces_symm hP D.hwm) D.m₁ rfl
  rwa [D.twin_m₁] at h

/-! #### Adjacent unselected visits share a carrier -/

theorem r174w_ownerQ_x₁_m₁ : geoOwner hP Q (Sum.inr D.x₁) = geoOwner hP Q (Sum.inr D.m₁) :=
  GT_owner_eq_of_adjacent hP Q D.adj1 rfl (r174c_x_not_mem_Q D) (r174c_m_not_mem_Q D)

theorem r174w_ownerQ_x₂_w₂ : geoOwner hP Q (Sum.inr D.x₂) = geoOwner hP Q (Sum.inr D.w₂) :=
  GT_owner_eq_of_adjacent hP Q D.adj2 rfl (r174c_x_not_mem_Q D) (r174c_w_not_mem_Q D)

theorem r174w_ownerQ_w₃_m₃ : geoOwner hP Q (Sum.inr D.w₃) = geoOwner hP Q (Sum.inr D.m₃) :=
  GT_owner_eq_of_adjacent hP Q D.adj3 rfl (r174c_w_not_mem_Q D) (r174c_m_not_mem_Q D)

theorem r174w_ownerx_w₃_m₃ :
    geoOwner hP (insert x Q) (Sum.inr D.w₃) = geoOwner hP (insert x Q) (Sum.inr D.m₃) :=
  GT_owner_eq_of_adjacent hP _ D.adj3 rfl (r174w_w_not_mem_Sx D) (r174w_m_not_mem_Sx D)

theorem r174w_ownerm_x₂_w₂ :
    geoOwner hP (insert m Q) (Sum.inr D.x₂) = geoOwner hP (insert m Q) (Sum.inr D.w₂) :=
  GT_owner_eq_of_adjacent hP _ D.adj2 rfl (r174w_x_not_mem_Sm' D) (r174w_w_not_mem_Sm' D)

/-- All six local visits lie on one carrier `q₀` of `Q`. -/
theorem r174w_ownerQ_w₂ : geoOwner hP Q (Sum.inr D.w₂) = geoOwner hP Q (Sum.inr D.m₁) := by
  rw [← r174w_ownerQ_x₂_w₂ D, ← r174w_ownerQ_x D, r174w_ownerQ_x₁_m₁ D]
theorem r174w_ownerQ_x₂' : geoOwner hP Q (Sum.inr D.x₂) = geoOwner hP Q (Sum.inr D.m₁) := by
  rw [← r174w_ownerQ_x D, r174w_ownerQ_x₁_m₁ D]
theorem r174w_ownerQ_w₃ : geoOwner hP Q (Sum.inr D.w₃) = geoOwner hP Q (Sum.inr D.m₁) := by
  rw [r174w_ownerQ_w₃_m₃ D, ← r174w_ownerQ_m D]
theorem r174w_ownerQ_m₃' : geoOwner hP Q (Sum.inr D.m₃) = geoOwner hP Q (Sum.inr D.m₁) :=
  (r174w_ownerQ_m D).symm

/-! #### The three splits, in key form -/

/-- Split `m` (`Q → Q ∪ {m}`). -/
theorem r174w_split_m :
    (∀ z : Mark P, geoOwner hP (insert m Q) z = geoOwner hP (insert m Q) (Sum.inr D.m₁) ↔
      z = Sum.inr D.m₁ ∨ (cycBetween (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr D.m₁)) ∧ geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁))) ∧
    (∀ z : Mark P, geoOwner hP (insert m Q) z = geoOwner hP (insert m Q) (Sum.inr D.m₃) ↔
      z = Sum.inr D.m₃ ∨ (cycBetween (geoMarkKey hP (Sum.inr D.m₁)) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr D.m₃)) ∧ geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁))) := by
  have h := r174w_child (hP := hP) Q (geoIndependent_inheritsMarkOrder hP (r174w_Q_indep D)) D.m₁
    (r174c_m_not_mem_Q D) (by rw [D.twin_m₁]; exact r174w_ownerQ_m D)
  rw [D.twin_m₁] at h
  exact h

/-- Split `x` (`Q → Q ∪ {x}`). -/
theorem r174w_split_x :
    (∀ z : Mark P, geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.x₁) ↔
      z = Sum.inr D.x₁ ∨ (cycBetween (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr D.x₁)) ∧ geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁))) ∧
    (∀ z : Mark P, geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.x₂) ↔
      z = Sum.inr D.x₂ ∨ (cycBetween (geoMarkKey hP (Sum.inr D.x₁)) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr D.x₂)) ∧ geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁))) := by
  have h := r174w_child (hP := hP) Q (geoIndependent_inheritsMarkOrder hP (r174w_Q_indep D)) D.x₁
    (r174c_x_not_mem_Q D) (by rw [D.twin_x₁]; exact r174w_ownerQ_x D)
  rw [D.twin_x₁, r174w_ownerQ_x₁_m₁ D] at h
  exact h

/-- Split `w` (`Q ∪ {x} → Q ∪ {x, w}`). -/
theorem r174w_split_w :
    (∀ z : Mark P, geoOwner hP (insert w (insert x Q)) z = geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₂) ↔
      z = Sum.inr D.w₂ ∨ (cycBetween (geoMarkKey hP (Sum.inr D.w₃)) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr D.w₂)) ∧ geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.w₂))) ∧
    (∀ z : Mark P, geoOwner hP (insert w (insert x Q)) z = geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₃) ↔
      z = Sum.inr D.w₃ ∨ (cycBetween (geoMarkKey hP (Sum.inr D.w₂)) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr D.w₃)) ∧ geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.w₂))) := by
  have h := r174w_child (hP := hP) (insert x Q) (geoIndependent_inheritsMarkOrder hP (r174w_Sx_indep D)) D.w₂
    (r174w_w_not_mem_Sx D) (by rw [D.twin_w₂]; exact r174w_ownerx_w D)
  rw [D.twin_w₂] at h
  exact h

/-- Unaffected carriers of the `w`-split: a carrier of `Q ∪ {x}` not through `w₂` is a carrier of
`Q ∪ {x, w}`. -/
theorem r174w_unaffected_w (z : Mark P)
    (hz : geoOwner hP (insert x Q) z ≠ geoOwner hP (insert x Q) (Sum.inr D.w₂)) (z' : Mark P) :
    geoOwner hP (insert w (insert x Q)) z' = geoOwner hP (insert w (insert x Q)) z ↔
      geoOwner hP (insert x Q) z' = geoOwner hP (insert x Q) z := by
  have h := geoOwner_insert_iff_of_unaffected hP (insert x Q) D.w₂ (r174w_w_not_mem_Sx D)
    (by rw [D.twin_w₂]; exact r174w_ownerx_w D) (geoOwner hP (insert x Q) z) hz z rfl z'
  exact h

/-! #### Partition: every mark of `q₀` lands in one of the two children -/

omit D in
theorem r174w_key_ne {a b : Mark P} (h : a ≠ b) : geoMarkKey hP a ≠ geoMarkKey hP b :=
  fun h' => h (geoMarkKey_injective hP h')

omit [NeZero n] D in
theorem r174w_inr_ne {v u : Visit P} (h : v ≠ u) : (Sum.inr v : Mark P) ≠ Sum.inr u :=
  fun h' => h (Sum.inr.inj h')

theorem r174w_part_m (z : Mark P) (hz : geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁)) :
    geoOwner hP (insert m Q) z = geoOwner hP (insert m Q) (Sum.inr D.m₁) ∨
      geoOwner hP (insert m Q) z = geoOwner hP (insert m Q) (Sum.inr D.m₃) := by
  obtain ⟨h1, h3⟩ := r174w_split_m D
  by_cases hz1 : z = Sum.inr D.m₁
  · exact Or.inl ((h1 z).mpr (Or.inl hz1))
  by_cases hz3 : z = Sum.inr D.m₃
  · exact Or.inr ((h3 z).mpr (Or.inl hz3))
  rcases GT_cyc_total (r174w_key_ne (Ne.symm hz1)) (r174w_key_ne (r174w_inr_ne D.m₁_ne_m₃))
    (r174w_key_ne hz3) with h | h
  · exact Or.inr ((h3 z).mpr (Or.inr ⟨h, hz⟩))
  · exact Or.inl ((h1 z).mpr (Or.inr ⟨GT_cyc_rotate.mp h, hz⟩))

theorem r174w_part_x (z : Mark P) (hz : geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁)) :
    geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.x₁) ∨
      geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.x₂) := by
  obtain ⟨h1, h2⟩ := r174w_split_x D
  by_cases hz1 : z = Sum.inr D.x₁
  · exact Or.inl ((h1 z).mpr (Or.inl hz1))
  by_cases hz2 : z = Sum.inr D.x₂
  · exact Or.inr ((h2 z).mpr (Or.inl hz2))
  rcases GT_cyc_total (r174w_key_ne (Ne.symm hz1)) (r174w_key_ne (r174w_inr_ne D.x₁_ne_x₂))
    (r174w_key_ne hz2) with h | h
  · exact Or.inr ((h2 z).mpr (Or.inr ⟨h, hz⟩))
  · exact Or.inl ((h1 z).mpr (Or.inr ⟨GT_cyc_rotate.mp h, hz⟩))

theorem r174w_part_w (z : Mark P)
    (hz : geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.w₂)) :
    geoOwner hP (insert w (insert x Q)) z = geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₂) ∨
      geoOwner hP (insert w (insert x Q)) z = geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₃) := by
  obtain ⟨h2, h3⟩ := r174w_split_w D
  by_cases hz2 : z = Sum.inr D.w₂
  · exact Or.inl ((h2 z).mpr (Or.inl hz2))
  by_cases hz3 : z = Sum.inr D.w₃
  · exact Or.inr ((h3 z).mpr (Or.inl hz3))
  rcases GT_cyc_total (r174w_key_ne (Ne.symm hz2)) (r174w_key_ne (r174w_inr_ne D.w₂_ne_w₃))
    (r174w_key_ne hz3) with h | h
  · exact Or.inr ((h3 z).mpr (Or.inr ⟨h, hz⟩))
  · exact Or.inl ((h2 z).mpr (Or.inr ⟨GT_cyc_rotate.mp h, hz⟩))

/-- A mark of a child of `q₀` lies on `q₀`. -/
theorem r174w_onZ_of_m₁ (z : Mark P) (hz : z ≠ Sum.inr D.m₁)
    (h : geoOwner hP (insert m Q) z = geoOwner hP (insert m Q) (Sum.inr D.m₁)) :
    geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁) := by
  rcases ((r174w_split_m D).1 z).mp h with h' | h'
  · exact absurd h' hz
  · exact h'.2

theorem r174w_onZ_of_m₃ (z : Mark P) (hz : z ≠ Sum.inr D.m₃)
    (h : geoOwner hP (insert m Q) z = geoOwner hP (insert m Q) (Sum.inr D.m₃)) :
    geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁) := by
  rcases ((r174w_split_m D).2 z).mp h with h' | h'
  · exact absurd h' hz
  · exact h'.2

theorem r174w_onZ_of_x₁ (z : Mark P) (hz : z ≠ Sum.inr D.x₁)
    (h : geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.x₁)) :
    geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁) := by
  rcases ((r174w_split_x D).1 z).mp h with h' | h'
  · exact absurd h' hz
  · exact h'.2

theorem r174w_onZ_of_x₂ (z : Mark P) (hz : z ≠ Sum.inr D.x₂)
    (h : geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.x₂)) :
    geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁) := by
  rcases ((r174w_split_x D).2 z).mp h with h' | h'
  · exact absurd h' hz
  · exact h'.2

omit D in
/-- The mark immediately after `a` in the traversal: no mark strictly between. -/
theorem r174w_no_between {a b : Mark P} (h : geoMarkSuccessor hP a = b) (u : Mark P) :
    ¬ cycBetween (geoMarkKey hP a) (geoMarkKey hP u) (geoMarkKey hP b) := by
  have h' : (geoMarkSuccessor hP).symm b = a := (Equiv.symm_apply_eq _).mpr h.symm
  have := geoMarkSuccessor_prev_no_mark_between hP b u
  rw [h'] at this
  exact this

/-! #### C5. The case split -/

omit D in
theorem r174w_owner_eq_of_succ {S : Finset (Crossing P)} {a b : Mark P}
    (h : geoSmoothingSuccessor hP S a = b) : geoOwner hP S b = geoOwner hP S a := by
  rw [← h]; exact geoOwner_successor hP S a

/-- A mark is *nonspecial* if it is none of the six local visits. -/
def r174w_Nonspecial (a : Mark P) : Prop :=
  a ≠ Sum.inr D.x₁ ∧ a ≠ Sum.inr D.x₂ ∧ a ≠ Sum.inr D.w₂ ∧ a ≠ Sum.inr D.w₃ ∧
    a ≠ Sum.inr D.m₁ ∧ a ≠ Sum.inr D.m₃

/-- **The outcome of the orientation case analysis**: the local visit `xA` of `x` and `m₁` lie on one
carrier `A` of `Q ∪ {x, w}`; `wB` (of `w`) and `m₃` on `B`; the other two local visits `xC, wC` on `C'`;
on `Q ∪ {m}`, `mAB` (of `m`) lies with `x₂, w₂` on `AB` and `mC` with `x₁` on `C`; and every
nonspecial mark of `A` or `B` lies on `AB`, every nonspecial mark of `C'` on `C`. -/
structure r174w_Split where
  xA : Visit P
  wB : Visit P
  mAB : Visit P
  hxA : xA.1 = x
  hwB : wB.1 = w
  hmAB : mAB.1 = m
  hcase : (xA = D.x₂ ∧ wB = D.w₃ ∧ mAB = D.m₃) ∨ (xA = D.x₁ ∧ wB = D.w₂ ∧ mAB = D.m₁)
  oA : geoOwner hP (insert w (insert x Q)) (Sum.inr xA) = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁)
  oB : geoOwner hP (insert w (insert x Q)) (Sum.inr wB) = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃)
  oC' : geoOwner hP (insert w (insert x Q)) (Sum.inr (visitTwin xA)) =
    geoOwner hP (insert w (insert x Q)) (Sum.inr (visitTwin wB))
  oAB : geoOwner hP (insert m Q) (Sum.inr mAB) = geoOwner hP (insert m Q) (Sum.inr D.x₂)
  oC : geoOwner hP (insert m Q) (Sum.inr (visitTwin mAB)) = geoOwner hP (insert m Q) (Sum.inr D.x₁)
  P1 : ∀ a : Mark P, r174w_Nonspecial D a →
    geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁) →
    geoOwner hP (insert m Q) a = geoOwner hP (insert m Q) (Sum.inr D.x₂)
  P2 : ∀ a : Mark P, r174w_Nonspecial D a →
    geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃) →
    geoOwner hP (insert m Q) a = geoOwner hP (insert m Q) (Sum.inr D.x₂)
  P3 : ∀ a : Mark P, r174w_Nonspecial D a →
    geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr (visitTwin xA)) →
    geoOwner hP (insert m Q) a = geoOwner hP (insert m Q) (Sum.inr D.x₁)
  onZ_A : ∀ a : Mark P, geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁) →
    geoOwner hP Q a = geoOwner hP Q (Sum.inr D.m₁)
  onZ_B : ∀ a : Mark P, geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃) →
    geoOwner hP Q a = geoOwner hP Q (Sum.inr D.m₁)
  onZ_C' : ∀ a : Mark P,
    geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr (visitTwin xA)) →
    geoOwner hP Q a = geoOwner hP Q (Sum.inr D.m₁)
  onZ_AB : ∀ a : Mark P, geoOwner hP (insert m Q) a = geoOwner hP (insert m Q) (Sum.inr D.x₂) →
    geoOwner hP Q a = geoOwner hP Q (Sum.inr D.m₁)
  onZ_C : ∀ a : Mark P, geoOwner hP (insert m Q) a = geoOwner hP (insert m Q) (Sum.inr D.x₁) →
    geoOwner hP Q a = geoOwner hP Q (Sum.inr D.m₁)
  triZ : ∀ a : Mark P, geoOwner hP Q a = geoOwner hP Q (Sum.inr D.m₁) →
    geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁) ∨
    geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃) ∨
    geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr (visitTwin xA))

theorem r174w_x₂_ne_m₃ : D.x₂ ≠ D.m₃ := fun h => D.xm (congrArg Sigma.fst h)
theorem r174w_x₂_ne_m₁ : D.x₂ ≠ D.m₁ := fun h => D.xm (congrArg Sigma.fst h)
theorem r174w_x₁_ne_m₁ : D.x₁ ≠ D.m₁ := fun h => D.xm (congrArg Sigma.fst h)
theorem r174w_x₁_ne_m₃ : D.x₁ ≠ D.m₃ := fun h => D.xm (congrArg Sigma.fst h)
theorem r174w_x₁_ne_w₂ : D.x₁ ≠ D.w₂ := fun h => D.xw (congrArg Sigma.fst h)
theorem r174w_x₂_ne_w₂ : D.x₂ ≠ D.w₂ := fun h => D.xw (congrArg Sigma.fst h)
theorem r174w_x₂_ne_w₃ : D.x₂ ≠ D.w₃ := fun h => D.xw (congrArg Sigma.fst h)

/-- **Case B** (`x₁` immediately before `m₁` on `ℓ₁`; the printed word `a b A a c B b c C`). -/
def r174w_split_caseB (hB : geoMarkSuccessor hP (Sum.inr D.x₁) = Sum.inr D.m₁) : r174w_Split D := by
  have hxSx : x ∈ insert x Q := Finset.mem_insert_self x Q
  have hxSxw : x ∈ insert w (insert x Q) := Finset.mem_insert_of_mem hxSx
  have hwSxw : w ∈ insert w (insert x Q) := Finset.mem_insert_self w _
  have hmSm : m ∈ insert m Q := Finset.mem_insert_self m Q
  -- (B1) `C = owner_m x₁ ∋ m₁`
  have hB1 : geoOwner hP (insert m Q) (Sum.inr D.m₁) = geoOwner hP (insert m Q) (Sum.inr D.x₁) :=
    r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.x₁ (r174w_x_not_mem_Sm' D)]; exact hB)
  -- (B2) in `Q ∪ {x}`: `m₁` on the carrier of `x₂`
  have hB2 : geoOwner hP (insert x Q) (Sum.inr D.m₁) = geoOwner hP (insert x Q) (Sum.inr D.x₂) :=
    r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_mem hP _ D.x₂ hxSx, D.twin_x₂]; exact hB)
  -- (B3) `m₃`, `w₂`, `w₃` on the carrier of `x₁`
  have hB3 : geoOwner hP (insert x Q) (Sum.inr D.m₃) = geoOwner hP (insert x Q) (Sum.inr D.x₁) := by
    rcases r174w_part_x D (Sum.inr D.m₃) (r174w_ownerQ_m₃' D) with h | h
    · exact h
    · exact absurd (hB2.trans h.symm) (r174w_sep_m_Sx D)
  have hB3w : geoOwner hP (insert x Q) (Sum.inr D.w₂) = geoOwner hP (insert x Q) (Sum.inr D.x₁) := by
    rw [r174w_ownerx_w D, r174w_ownerx_w₃_m₃ D, hB3]
  -- (B4) `x₂` immediately before `w₂`
  have hB4 : geoMarkSuccessor hP (Sum.inr D.x₂) = Sum.inr D.w₂ := by
    rcases GT_succ_of_adjacent hP D.adj2 rfl with h | h
    · exact h
    · exfalso
      have h' : geoOwner hP (insert x Q) (Sum.inr D.x₂) = geoOwner hP (insert x Q) (Sum.inr D.w₂) :=
        r174w_owner_eq_of_succ (by
          rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.w₂ (r174w_w_not_mem_Sx D)]; exact h)
      exact r174w_sep_x_Sx D (hB3w.symm.trans h'.symm)
  -- (B5) `m₃` immediately before `w₃`
  have hB5 : geoMarkSuccessor hP (Sum.inr D.m₃) = Sum.inr D.w₃ := by
    rcases GT_succ_of_adjacent hP D.adj3 rfl with h | h
    · exfalso
      have h' : geoOwner hP (insert m Q) (Sum.inr D.m₃) = geoOwner hP (insert m Q) (Sum.inr D.w₃) :=
        r174w_owner_eq_of_succ (by
          rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.w₃ (r174w_w_not_mem_Sm' D)]; exact h)
      have hne : geoOwner hP (insert m Q) (Sum.inr D.x₂) ≠ geoOwner hP (insert m Q) (Sum.inr D.m₃) := by
        rw [r174w_ownerm_x₂_w₂ D, h']; exact r174w_sep_w_Sm D
      rcases r174w_part_m D (Sum.inr D.x₂) (r174w_ownerQ_x₂' D) with h2 | h2
      · exact r174w_sep_x_Sm D (h2.trans hB1).symm
      · exact hne h2
    · exact h
  -- (B6) `AB = owner_m x₂ ∋ m₃`
  have hAB : geoOwner hP (insert m Q) (Sum.inr D.m₃) = geoOwner hP (insert m Q) (Sum.inr D.x₂) := by
    rcases r174w_part_m D (Sum.inr D.x₂) (r174w_ownerQ_x₂' D) with h | h
    · exact absurd (h.trans hB1).symm (r174w_sep_x_Sm D)
    · exact h.symm
  have hABw : geoOwner hP (insert m Q) (Sum.inr D.w₂) = geoOwner hP (insert m Q) (Sum.inr D.m₃) := by
    rw [hAB, r174w_ownerm_x₂_w₂ D]
  have hCw : geoOwner hP (insert m Q) (Sum.inr D.w₃) = geoOwner hP (insert m Q) (Sum.inr D.m₁) := by
    rcases r174w_part_m D (Sum.inr D.w₃) (r174w_ownerQ_w₃ D) with h | h
    · exact h
    · exact absurd (hABw.trans h.symm) (r174w_sep_w_Sm D)
  -- (B7) the carriers of `Q ∪ {x, w}`
  have hne_m₁w₂ : geoOwner hP (insert x Q) (Sum.inr D.m₁) ≠ geoOwner hP (insert x Q) (Sum.inr D.w₂) := by
    rw [hB2, hB3w]; exact (r174w_sep_x_Sx D).symm
  have hqA : geoOwner hP (insert w (insert x Q)) (Sum.inr D.x₂) =
      geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁) :=
    (r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ (Sum.inr D.x₂)).mpr hB2.symm
  have hqB : geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₃) =
      geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃) :=
    r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.m₃ (r174w_m_not_mem_Sxw D)]; exact hB5)
  have hqC' : geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₂) =
      geoOwner hP (insert w (insert x Q)) (Sum.inr D.x₁) :=
    r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_mem hP _ D.x₁ hxSxw, D.twin_x₁]; exact hB4)
  -- (B8) key facts
  have K1 := r174w_no_between (hP := hP) hB
  have K2 := r174w_no_between (hP := hP) hB4
  have K3 := r174w_no_between (hP := hP) hB5
  obtain ⟨Sm1, Sm3⟩ := r174w_split_m D
  obtain ⟨Sx1, Sx2⟩ := r174w_split_x D
  obtain ⟨Sw2, Sw3⟩ := r174w_split_w D
  have c1 : cycBetween (geoMarkKey hP (Sum.inr D.m₁)) (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP (Sum.inr D.m₃)) :=
    (((Sm3 _).mp hAB.symm).resolve_left (r174w_inr_ne (r174w_x₂_ne_m₃ D))).1
  have c2 : cycBetween (geoMarkKey hP (Sum.inr D.m₁)) (geoMarkKey hP (Sum.inr D.w₂)) (geoMarkKey hP (Sum.inr D.m₃)) :=
    (((Sm3 _).mp hABw).resolve_left (r174w_inr_ne D.w₂_ne_m₃)).1
  have c3 : cycBetween (geoMarkKey hP (Sum.inr D.x₁)) (geoMarkKey hP (Sum.inr D.m₁)) (geoMarkKey hP (Sum.inr D.x₂)) :=
    (((Sx2 _).mp hB2).resolve_left (r174w_inr_ne (r174w_x₂_ne_m₁ D).symm)).1
  have c4 : cycBetween (geoMarkKey hP (Sum.inr D.w₂)) (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.w₃)) :=
    (((Sw3 _).mp hqB.symm).resolve_left (r174w_inr_ne D.w₃_ne_m₃.symm)).1
  have c5 : cycBetween (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.x₁)) :=
    (((Sx1 _).mp hB3).resolve_left (r174w_inr_ne (r174w_x₁_ne_m₃ D).symm)).1
  have c8 : cycBetween (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.x₁)) (geoMarkKey hP (Sum.inr D.m₁)) :=
    (((Sm1 _).mp hB1.symm).resolve_left (r174w_inr_ne (r174w_x₁_ne_m₁ D))).1
  -- `x₂` before `w₂` inside `(m₁, m₃)`: else `m₃ ∈ (x₂, w₂)`
  have c9 : cycBetween (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP (Sum.inr D.w₂)) (geoMarkKey hP (Sum.inr D.m₃)) := by
    rcases r174w_cyc_split c1 c2 (r174w_key_ne (r174w_inr_ne (r174w_x₂_ne_w₂ D))) with h | h
    · exact r174w_cyc_mid h c2
    · exact absurd (r174w_cyc_wrap c2 h) (K2 _)
  refine ⟨D.x₂, D.w₃, D.m₃, rfl, rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩, hqA, hqB, ?_, hAB, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [D.twin_x₂, D.twin_w₃]; exact hqC'.symm
  · rw [D.twin_m₃]; exact hB1
  · -- P1
    intro a ha h
    have h1 : geoOwner hP (insert x Q) a = geoOwner hP (insert x Q) (Sum.inr D.x₂) :=
      ((r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ a).mp h).trans hB2
    obtain ⟨h2, hZ⟩ := ((Sx2 a).mp h1).resolve_left ha.2.1
    have h3 : cycBetween (geoMarkKey hP (Sum.inr D.m₁)) (geoMarkKey hP a) (geoMarkKey hP (Sum.inr D.x₂)) := by
      rcases r174w_cyc_split h2 c3 (r174w_key_ne ha.2.2.2.2.1) with h' | h'
      · exact absurd h' (K1 a)
      · exact h'
    rw [← hAB]
    exact (Sm3 a).mpr (Or.inr ⟨r174w_cyc_trans_left h3 c1, hZ⟩)
  · -- P2
    intro a ha h
    rw [← hqB] at h
    obtain ⟨h2, hx⟩ := ((Sw3 a).mp h).resolve_left ha.2.2.2.1
    rw [hB3w] at hx
    have hZ := r174w_onZ_of_x₁ D a ha.1 hx
    have h3 : cycBetween (geoMarkKey hP (Sum.inr D.w₂)) (geoMarkKey hP a) (geoMarkKey hP (Sum.inr D.m₃)) := by
      rcases r174w_cyc_split h2 c4 (r174w_key_ne ha.2.2.2.2.2) with h' | h'
      · exact h'
      · exact absurd h' (K3 a)
    rw [← hAB]
    exact (Sm3 a).mpr (Or.inr ⟨r174w_cyc_trans_right c2 h3, hZ⟩)
  · -- P3
    intro a ha h
    rw [D.twin_x₂, ← hqC'] at h
    obtain ⟨h1, hx⟩ := ((Sw2 a).mp h).resolve_left ha.2.2.1
    rw [hB3w] at hx
    obtain ⟨h2, hZ⟩ := ((Sx1 a).mp hx).resolve_left ha.1
    rcases r174w_cyc_split h2 c5 (r174w_key_ne ha.2.2.2.2.2) with h' | h'
    · exfalso
      rcases r174w_cyc_split h' c9 (r174w_key_ne ha.2.2.1) with h'' | h''
      · exact K2 a h''
      · exact r174w_cyc_asymm (r174w_cyc_trans_left h'' c4) h1
    · rw [← hB1]
      exact (Sm1 a).mpr (Or.inr ⟨r174w_cyc_trans_left h' c8, hZ⟩)
  · -- onZ_A
    intro a h
    have h1 : geoOwner hP (insert x Q) a = geoOwner hP (insert x Q) (Sum.inr D.x₂) :=
      ((r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ a).mp h).trans hB2
    by_cases ha : a = Sum.inr D.x₂
    · rw [ha]; exact r174w_ownerQ_x₂' D
    · exact r174w_onZ_of_x₂ D a ha h1
  · -- onZ_B
    intro a h
    rw [← hqB] at h
    rcases (Sw3 a).mp h with rfl | ⟨-, hx⟩
    · exact r174w_ownerQ_w₃ D
    · rw [hB3w] at hx
      by_cases ha : a = Sum.inr D.x₁
      · rw [ha]; exact r174w_ownerQ_x₁_m₁ D
      · exact r174w_onZ_of_x₁ D a ha hx
  · -- onZ_C'
    intro a h
    rw [D.twin_x₂, ← hqC'] at h
    rcases (Sw2 a).mp h with rfl | ⟨-, hx⟩
    · exact r174w_ownerQ_w₂ D
    · rw [hB3w] at hx
      by_cases ha : a = Sum.inr D.x₁
      · rw [ha]; exact r174w_ownerQ_x₁_m₁ D
      · exact r174w_onZ_of_x₁ D a ha hx
  · -- onZ_AB
    intro a h
    rw [← hAB] at h
    by_cases ha : a = Sum.inr D.m₃
    · rw [ha]; exact r174w_ownerQ_m₃' D
    · exact r174w_onZ_of_m₃ D a ha h
  · -- onZ_C
    intro a h
    rw [← hB1] at h
    by_cases ha : a = Sum.inr D.m₁
    · rw [ha]
    · exact r174w_onZ_of_m₁ D a ha h
  · -- triZ
    intro a hZ
    rcases r174w_part_x D a hZ with h | h
    · rw [← hB3w] at h
      rcases r174w_part_w D a h with h' | h'
      · right; right; rw [D.twin_x₂, ← hqC']; exact h'
      · right; left; rw [← hqB]; exact h'
    · left; exact (r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ a).mpr (h.trans hB2.symm)

/-- **Case A** (`m₁` immediately before `x₁` on `ℓ₁`; the reversed traversal). -/
def r174w_split_caseA (hA : geoMarkSuccessor hP (Sum.inr D.m₁) = Sum.inr D.x₁) : r174w_Split D := by
  have hxSx : x ∈ insert x Q := Finset.mem_insert_self x Q
  have hxSxw : x ∈ insert w (insert x Q) := Finset.mem_insert_of_mem hxSx
  have hwSxw : w ∈ insert w (insert x Q) := Finset.mem_insert_self w _
  have hmSm : m ∈ insert m Q := Finset.mem_insert_self m Q
  -- (A1) `C = owner_m x₁ ∋ m₃`
  have hA1 : geoOwner hP (insert m Q) (Sum.inr D.x₁) = geoOwner hP (insert m Q) (Sum.inr D.m₃) :=
    r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_mem hP _ D.m₃ hmSm, D.twin_m₃]; exact hA)
  -- (A2) in `Q ∪ {x}`: `m₁` on the carrier of `x₁`
  have hA2 : geoOwner hP (insert x Q) (Sum.inr D.x₁) = geoOwner hP (insert x Q) (Sum.inr D.m₁) :=
    r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.m₁ (r174w_m_not_mem_Sx D)]; exact hA)
  -- (A3) `m₃`, `w₂`, `w₃` on the carrier of `x₂`
  have hA3 : geoOwner hP (insert x Q) (Sum.inr D.m₃) = geoOwner hP (insert x Q) (Sum.inr D.x₂) := by
    rcases r174w_part_x D (Sum.inr D.m₃) (r174w_ownerQ_m₃' D) with h | h
    · exact absurd (hA2.symm.trans h.symm) (r174w_sep_m_Sx D)
    · exact h
  have hA3w : geoOwner hP (insert x Q) (Sum.inr D.w₂) = geoOwner hP (insert x Q) (Sum.inr D.x₂) := by
    rw [r174w_ownerx_w D, r174w_ownerx_w₃_m₃ D, hA3]
  -- (A4) `w₂` immediately before `x₂`
  have hA4 : geoMarkSuccessor hP (Sum.inr D.w₂) = Sum.inr D.x₂ := by
    rcases GT_succ_of_adjacent hP D.adj2 rfl with h | h
    · exfalso
      have h' : geoOwner hP (insert x Q) (Sum.inr D.w₂) = geoOwner hP (insert x Q) (Sum.inr D.x₁) :=
        r174w_owner_eq_of_succ (by
          rw [geoSmoothingSuccessor_visit_of_mem hP _ D.x₁ hxSx, D.twin_x₁]; exact h)
      exact r174w_sep_x_Sx D (h'.symm.trans hA3w)
    · exact h
  -- (A5) `w₃` immediately before `m₃`
  have hA5 : geoMarkSuccessor hP (Sum.inr D.w₃) = Sum.inr D.m₃ := by
    rcases GT_succ_of_adjacent hP D.adj3 rfl with h | h
    · exact h
    · exfalso
      have h' : geoOwner hP (insert m Q) (Sum.inr D.w₃) = geoOwner hP (insert m Q) (Sum.inr D.m₁) :=
        r174w_owner_eq_of_succ (by
          rw [geoSmoothingSuccessor_visit_of_mem hP _ D.m₁ hmSm, D.twin_m₁]; exact h)
      have hne : geoOwner hP (insert m Q) (Sum.inr D.x₂) ≠ geoOwner hP (insert m Q) (Sum.inr D.m₁) := by
        rw [r174w_ownerm_x₂_w₂ D, ← h']; exact r174w_sep_w_Sm D
      rcases r174w_part_m D (Sum.inr D.x₂) (r174w_ownerQ_x₂' D) with h2 | h2
      · exact hne h2
      · exact r174w_sep_x_Sm D (hA1.trans h2.symm)
  -- (A6) `AB = owner_m x₂ ∋ m₁`
  have hAB : geoOwner hP (insert m Q) (Sum.inr D.m₁) = geoOwner hP (insert m Q) (Sum.inr D.x₂) := by
    rcases r174w_part_m D (Sum.inr D.x₂) (r174w_ownerQ_x₂' D) with h | h
    · exact h.symm
    · exact absurd (hA1.trans h.symm) (r174w_sep_x_Sm D)
  have hABw : geoOwner hP (insert m Q) (Sum.inr D.w₂) = geoOwner hP (insert m Q) (Sum.inr D.m₁) :=
    (r174w_ownerm_x₂_w₂ D).symm.trans hAB.symm
  have hCw : geoOwner hP (insert m Q) (Sum.inr D.w₃) = geoOwner hP (insert m Q) (Sum.inr D.m₃) :=
    (r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.w₃ (r174w_w_not_mem_Sm' D)]; exact hA5)).symm
  -- (A7) the carriers of `Q ∪ {x, w}`
  have hne_m₁w₂ : geoOwner hP (insert x Q) (Sum.inr D.m₁) ≠ geoOwner hP (insert x Q) (Sum.inr D.w₂) := by
    rw [← hA2, hA3w]; exact r174w_sep_x_Sx D
  have hqA : geoOwner hP (insert w (insert x Q)) (Sum.inr D.x₁) =
      geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁) :=
    (r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ (Sum.inr D.x₁)).mpr hA2
  have hqB : geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₂) =
      geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃) :=
    (r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_mem hP _ D.w₂ hwSxw, D.twin_w₂]; exact hA5)).symm
  have hqC' : geoOwner hP (insert w (insert x Q)) (Sum.inr D.x₂) =
      geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₃) :=
    r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_mem hP _ D.w₃ hwSxw, D.twin_w₃]; exact hA4)
  -- (A8) key facts
  have K1 := r174w_no_between (hP := hP) hA
  have K2 := r174w_no_between (hP := hP) hA4
  have K3 := r174w_no_between (hP := hP) hA5
  obtain ⟨Sm1, Sm3⟩ := r174w_split_m D
  obtain ⟨Sx1, Sx2⟩ := r174w_split_x D
  obtain ⟨Sw2, Sw3⟩ := r174w_split_w D
  have c1 : cycBetween (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP (Sum.inr D.m₁)) :=
    (((Sm1 _).mp hAB.symm).resolve_left (r174w_inr_ne (r174w_x₂_ne_m₁ D))).1
  have c2 : cycBetween (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.w₂)) (geoMarkKey hP (Sum.inr D.m₁)) :=
    (((Sm1 _).mp hABw).resolve_left (r174w_inr_ne D.w₂_ne_m₁)).1
  have c3 : cycBetween (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP (Sum.inr D.m₁)) (geoMarkKey hP (Sum.inr D.x₁)) :=
    (((Sx1 _).mp hA2.symm).resolve_left (r174w_inr_ne (r174w_x₁_ne_m₁ D).symm)).1
  have c4 : cycBetween (geoMarkKey hP (Sum.inr D.w₃)) (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.w₂)) :=
    (((Sw2 _).mp hqB.symm).resolve_left (r174w_inr_ne D.w₂_ne_m₃.symm)).1
  have c5 : cycBetween (geoMarkKey hP (Sum.inr D.x₁)) (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.x₂)) :=
    (((Sx2 _).mp hA3).resolve_left (r174w_inr_ne (r174w_x₂_ne_m₃ D).symm)).1
  have c8 : cycBetween (geoMarkKey hP (Sum.inr D.m₁)) (geoMarkKey hP (Sum.inr D.x₁)) (geoMarkKey hP (Sum.inr D.m₃)) :=
    (((Sm3 _).mp hA1).resolve_left (r174w_inr_ne (r174w_x₁_ne_m₃ D))).1
  -- `w₂` before `x₂` inside `(m₃, m₁)`: else `m₁ ∈ (w₂, x₂)`
  have c9 : cycBetween (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.w₂)) (geoMarkKey hP (Sum.inr D.x₂)) := by
    rcases r174w_cyc_split c2 c1 (r174w_key_ne (r174w_inr_ne (r174w_x₂_ne_w₂ D).symm)) with h | h
    · exact h
    · exact absurd (r174w_cyc_wrap c1 h) (K2 _)
  refine ⟨D.x₁, D.w₂, D.m₁, rfl, rfl, rfl, Or.inr ⟨rfl, rfl, rfl⟩, hqA, hqB, ?_, hAB, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [D.twin_x₁, D.twin_w₂]; exact hqC'
  · rw [D.twin_m₁]; exact hA1.symm
  · -- P1
    intro a ha h
    have h1 : geoOwner hP (insert x Q) a = geoOwner hP (insert x Q) (Sum.inr D.x₁) :=
      ((r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ a).mp h).trans hA2.symm
    obtain ⟨h2, hZ⟩ := ((Sx1 a).mp h1).resolve_left ha.1
    have h3 : cycBetween (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP a) (geoMarkKey hP (Sum.inr D.m₁)) := by
      rcases r174w_cyc_split h2 c3 (r174w_key_ne ha.2.2.2.2.1) with h' | h'
      · exact h'
      · exact absurd h' (K1 a)
    rw [← hAB]
    exact (Sm1 a).mpr (Or.inr ⟨r174w_cyc_trans_right c1 h3, hZ⟩)
  · -- P2
    intro a ha h
    rw [← hqB] at h
    obtain ⟨h2, hx⟩ := ((Sw2 a).mp h).resolve_left ha.2.2.1
    rw [hA3w] at hx
    have hZ := r174w_onZ_of_x₂ D a ha.2.1 hx
    have h3 : cycBetween (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP a) (geoMarkKey hP (Sum.inr D.w₂)) := by
      rcases r174w_cyc_split h2 c4 (r174w_key_ne ha.2.2.2.2.2) with h' | h'
      · exact absurd h' (K3 a)
      · exact h'
    rw [← hAB]
    exact (Sm1 a).mpr (Or.inr ⟨r174w_cyc_trans_left h3 c2, hZ⟩)
  · -- P3
    intro a ha h
    rw [D.twin_x₁, hqC'] at h
    obtain ⟨h1, hx⟩ := ((Sw3 a).mp h).resolve_left ha.2.2.2.1
    rw [hA3w] at hx
    obtain ⟨h2, hZ⟩ := ((Sx2 a).mp hx).resolve_left ha.2.1
    rcases r174w_cyc_split h2 c5 (r174w_key_ne ha.2.2.2.2.2) with h' | h'
    · rw [hA1]
      exact (Sm3 a).mpr (Or.inr ⟨r174w_cyc_trans_right c8 h', hZ⟩)
    · exfalso
      rcases r174w_cyc_split h' c9 (r174w_key_ne ha.2.2.1) with h'' | h''
      · exact r174w_cyc_asymm h1 (r174w_cyc_trans_right c4 h'')
      · exact K2 a h''
  · -- onZ_A
    intro a h
    have h1 : geoOwner hP (insert x Q) a = geoOwner hP (insert x Q) (Sum.inr D.x₁) :=
      ((r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ a).mp h).trans hA2.symm
    by_cases ha : a = Sum.inr D.x₁
    · rw [ha]; exact r174w_ownerQ_x₁_m₁ D
    · exact r174w_onZ_of_x₁ D a ha h1
  · -- onZ_B
    intro a h
    rw [← hqB] at h
    rcases (Sw2 a).mp h with rfl | ⟨-, hx⟩
    · exact r174w_ownerQ_w₂ D
    · rw [hA3w] at hx
      by_cases ha : a = Sum.inr D.x₂
      · rw [ha]; exact r174w_ownerQ_x₂' D
      · exact r174w_onZ_of_x₂ D a ha hx
  · -- onZ_C'
    intro a h
    rw [D.twin_x₁, hqC'] at h
    rcases (Sw3 a).mp h with rfl | ⟨-, hx⟩
    · exact r174w_ownerQ_w₃ D
    · rw [hA3w] at hx
      by_cases ha : a = Sum.inr D.x₂
      · rw [ha]; exact r174w_ownerQ_x₂' D
      · exact r174w_onZ_of_x₂ D a ha hx
  · -- onZ_AB
    intro a h
    rw [← hAB] at h
    by_cases ha : a = Sum.inr D.m₁
    · rw [ha]
    · exact r174w_onZ_of_m₁ D a ha h
  · -- onZ_C
    intro a h
    rw [hA1] at h
    by_cases ha : a = Sum.inr D.m₃
    · rw [ha]; exact r174w_ownerQ_m₃' D
    · exact r174w_onZ_of_m₃ D a ha h
  · -- triZ
    intro a hZ
    rcases r174w_part_x D a hZ with h | h
    · left; exact (r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ a).mpr (h.trans hA2)
    · rw [← hA3w] at h
      rcases r174w_part_w D a h with h' | h'
      · right; left; rw [← hqB]; exact h'
      · right; right; rw [D.twin_x₁, hqC']; exact h'

/-- The case analysis: one of the two orientations occurs. -/
theorem r174w_split_exists : Nonempty (r174w_Split D) := by
  rcases GT_succ_of_adjacent hP D.adj1 rfl with h | h
  · exact ⟨r174w_split_caseB D h⟩
  · exact ⟨r174w_split_caseA D h⟩

/-! #### D1. The five carriers and the corner-set decompositions -/

omit [NeZero n] D in
theorem r174w_x_mem_Sxw : x ∈ insert w (insert x Q) := Finset.mem_insert_of_mem (Finset.mem_insert_self x Q)
omit [NeZero n] D in
theorem r174w_w_mem_Sxw : w ∈ insert w (insert x Q) := Finset.mem_insert_self w _
omit [NeZero n] D in
theorem r174w_m_mem_Smi : m ∈ insert m Q := Finset.mem_insert_self m Q

variable (sp : r174w_Split D)

/-- `A`: the carrier of `Q ∪ {x, w}` through `m₁`. -/
abbrev r174w_qA : GeoComponent hP (insert w (insert x Q)) := geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁)
/-- `B`: the carrier of `Q ∪ {x, w}` through `m₃`. -/
abbrev r174w_qB : GeoComponent hP (insert w (insert x Q)) := geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃)
/-- `C'`: the carrier of `Q ∪ {x, w}` through the other visit of `x`. -/
abbrev r174w_qCp : GeoComponent hP (insert w (insert x Q)) :=
  geoOwner hP (insert w (insert x Q)) (Sum.inr (visitTwin sp.xA))
/-- `AB`: the carrier of `Q ∪ {m}` through `x₂`. -/
abbrev r174w_qABi : GeoComponent hP (insert m Q) := geoOwner hP (insert m Q) (Sum.inr D.x₂)
/-- `C`: the carrier of `Q ∪ {m}` through `x₁`. -/
abbrev r174w_qCi : GeoComponent hP (insert m Q) := geoOwner hP (insert m Q) (Sum.inr D.x₁)

theorem r174w_qA_ne_qB : r174w_qA D ≠ r174w_qB D := r174w_sep_m_Sxw D

theorem r174w_qA_ne_qCp : r174w_qA D ≠ r174w_qCp D sp := by
  show geoOwner hP _ (Sum.inr D.m₁) ≠ geoOwner hP _ (Sum.inr (visitTwin sp.xA))
  rw [← sp.oA]
  exact geo_selected_visits_separated hP (r174w_Sxw_indep D) sp.xA (by rw [sp.hxA]; exact r174w_x_mem_Sxw)

theorem r174w_qB_ne_qCp : r174w_qB D ≠ r174w_qCp D sp := by
  show geoOwner hP _ (Sum.inr D.m₃) ≠ geoOwner hP _ (Sum.inr (visitTwin sp.xA))
  rw [← sp.oB, sp.oC']
  exact geo_selected_visits_separated hP (r174w_Sxw_indep D) sp.wB (by rw [sp.hwB]; exact r174w_w_mem_Sxw)

theorem r174w_qABi_ne_qCi : r174w_qABi D ≠ r174w_qCi D := (r174w_sep_x_Sm D).symm

theorem r174w_nonspecial_inl (i : ZMod n) : r174w_Nonspecial D (Sum.inl i) :=
  ⟨Sum.inl_ne_inr, Sum.inl_ne_inr, Sum.inl_ne_inr, Sum.inl_ne_inr, Sum.inl_ne_inr, Sum.inl_ne_inr⟩

theorem r174w_nonspecial_of_mem_Q (v : Visit P) (hv : v.1 ∈ Q) : r174w_Nonspecial D (Sum.inr v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> obtain rfl := Sum.inr.inj h
  · exact r174c_x_not_mem_Q D hv
  · exact r174c_x_not_mem_Q D hv
  · exact r174c_w_not_mem_Q D hv
  · exact r174c_w_not_mem_Q D hv
  · exact r174c_m_not_mem_Q D hv
  · exact r174c_m_not_mem_Q D hv

/-- For a nonspecial mark, being a corner of `Q ∪ {m}` and of `Q ∪ {x, w}` are the same
(both mean: a vertex, or a visit of a crossing of `Q`). -/
theorem r174w_corner_iff (a : Mark P) (hns : r174w_Nonspecial D a) :
    IsTrueCorner (insert m Q) a ↔ IsTrueCorner (insert w (insert x Q)) a := by
  cases a with
  | inl i => exact iff_of_true trivial trivial
  | inr v =>
    change v.1 ∈ insert m Q ↔ v.1 ∈ insert w (insert x Q)
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exfalso
        rcases D.eq_m₁_or_m₃ h with rfl | rfl
        · exact hns.2.2.2.2.1 rfl
        · exact hns.2.2.2.2.2 rfl
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exfalso
        rcases D.eq_w₂_or_w₃ h with rfl | rfl
        · exact hns.2.2.1 rfl
        · exact hns.2.2.2.1 rfl
      · exfalso
        rcases visit_eq_or_twin D.x₁ v h with rfl | h'
        · exact hns.1 rfl
        · rw [D.twin_x₁] at h'
          subst h'
          exact hns.2.1 rfl
      · exact Or.inr h

theorem r174w_not_nonspecial_xA : ¬ r174w_Nonspecial D (Sum.inr sp.xA) := by
  rcases sp.hcase with ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> rw [h] <;> intro hns
  · exact hns.2.1 rfl
  · exact hns.1 rfl
theorem r174w_not_nonspecial_wB : ¬ r174w_Nonspecial D (Sum.inr sp.wB) := by
  rcases sp.hcase with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> rw [h] <;> intro hns
  · exact hns.2.2.2.1 rfl
  · exact hns.2.2.1 rfl
theorem r174w_not_nonspecial_mAB : ¬ r174w_Nonspecial D (Sum.inr sp.mAB) := by
  rcases sp.hcase with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> intro hns
  · exact hns.2.2.2.2.2 rfl
  · exact hns.2.2.2.2.1 rfl
theorem r174w_not_nonspecial_xC : ¬ r174w_Nonspecial D (Sum.inr (visitTwin sp.xA)) := by
  rcases sp.hcase with ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> rw [h] <;> intro hns
  · rw [D.twin_x₂] at hns; exact hns.1 rfl
  · rw [D.twin_x₁] at hns; exact hns.2.1 rfl
theorem r174w_not_nonspecial_wC : ¬ r174w_Nonspecial D (Sum.inr (visitTwin sp.wB)) := by
  rcases sp.hcase with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> rw [h] <;> intro hns
  · rw [D.twin_w₃] at hns; exact hns.2.2.1 rfl
  · rw [D.twin_w₂] at hns; exact hns.2.2.2.1 rfl
theorem r174w_not_nonspecial_mC : ¬ r174w_Nonspecial D (Sum.inr (visitTwin sp.mAB)) := by
  rcases sp.hcase with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> intro hns
  · rw [D.twin_m₃] at hns; exact hns.2.2.2.2.1 rfl
  · rw [D.twin_m₁] at hns; exact hns.2.2.2.2.2 rfl

theorem r174w_xC_ne_wC : (Sum.inr (visitTwin sp.xA) : Mark P) ≠ Sum.inr (visitTwin sp.wB) := by
  intro h
  have := congrArg (fun a : Visit P => a.1) (Sum.inr.inj h)
  simp only [visitTwin_crossing, sp.hxA, sp.hwB] at this
  exact D.xw this

theorem r174w_corners_eq_insert_filter {S : Finset (Crossing P)} (q : GeoComponent hP S) (a₀ : Mark P)
    (h₀ : a₀ ∈ r174w_corners hP S q)
    (hothers : ∀ a ∈ r174w_corners hP S q, a ≠ a₀ → r174w_Nonspecial D a) :
    r174w_corners hP S q = insert a₀ ((r174w_corners hP S q).filter (r174w_Nonspecial D)) := by
  ext a
  rw [Finset.mem_insert, Finset.mem_filter]
  constructor
  · intro h
    by_cases ha : a = a₀
    · exact Or.inl ha
    · exact Or.inr ⟨h, hothers a h ha⟩
  · rintro (rfl | ⟨h, -⟩)
    · exact h₀
    · exact h

theorem r174w_corners_eq_insert2_filter {S : Finset (Crossing P)} (q : GeoComponent hP S) (a₀ a₁ : Mark P)
    (h₀ : a₀ ∈ r174w_corners hP S q) (h₁ : a₁ ∈ r174w_corners hP S q)
    (hothers : ∀ a ∈ r174w_corners hP S q, a ≠ a₀ → a ≠ a₁ → r174w_Nonspecial D a) :
    r174w_corners hP S q = insert a₀ (insert a₁ ((r174w_corners hP S q).filter (r174w_Nonspecial D))) := by
  ext a
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_filter]
  constructor
  · intro h
    by_cases ha : a = a₀
    · exact Or.inl ha
    by_cases ha' : a = a₁
    · exact Or.inr (Or.inl ha')
    · exact Or.inr (Or.inr ⟨h, hothers a h ha ha'⟩)
  · rintro (rfl | rfl | ⟨h, -⟩)
    · exact h₀
    · exact h₁
    · exact h

/-- The corners of `A`: `xA` and nonspecial corners. -/
theorem r174w_corners_A :
    r174w_corners hP (insert w (insert x Q)) (r174w_qA D) =
      insert (Sum.inr sp.xA) ((r174w_corners hP (insert w (insert x Q)) (r174w_qA D)).filter (r174w_Nonspecial D)) := by
  apply r174w_corners_eq_insert_filter
  · rw [r174w_mem_corners]
    exact ⟨sp.oA, by change sp.xA.1 ∈ _; rw [sp.hxA]; exact r174w_x_mem_Sxw⟩
  · intro a ha hne
    rw [r174w_mem_corners] at ha
    obtain ⟨hq, hc⟩ := ha
    cases a with
    | inl i => exact r174w_nonspecial_inl D i
    | inr v =>
      have hv : v.1 ∈ insert w (insert x Q) := hc
      rw [Finset.mem_insert, Finset.mem_insert] at hv
      rcases hv with hv | hv | hv
      · exfalso
        rcases visit_eq_or_twin sp.wB v (hv.trans sp.hwB.symm) with rfl | rfl
        · exact r174w_qA_ne_qB D (hq.symm.trans sp.oB)
        · exact r174w_qA_ne_qCp D sp (hq.symm.trans sp.oC'.symm)
      · exfalso
        rcases visit_eq_or_twin sp.xA v (hv.trans sp.hxA.symm) with rfl | rfl
        · exact hne rfl
        · exact r174w_qA_ne_qCp D sp hq.symm
      · exact r174w_nonspecial_of_mem_Q D v hv

/-- The corners of `B`: `wB` and nonspecial corners. -/
theorem r174w_corners_B :
    r174w_corners hP (insert w (insert x Q)) (r174w_qB D) =
      insert (Sum.inr sp.wB) ((r174w_corners hP (insert w (insert x Q)) (r174w_qB D)).filter (r174w_Nonspecial D)) := by
  apply r174w_corners_eq_insert_filter
  · rw [r174w_mem_corners]
    exact ⟨sp.oB, by change sp.wB.1 ∈ _; rw [sp.hwB]; exact r174w_w_mem_Sxw⟩
  · intro a ha hne
    rw [r174w_mem_corners] at ha
    obtain ⟨hq, hc⟩ := ha
    cases a with
    | inl i => exact r174w_nonspecial_inl D i
    | inr v =>
      have hv : v.1 ∈ insert w (insert x Q) := hc
      rw [Finset.mem_insert, Finset.mem_insert] at hv
      rcases hv with hv | hv | hv
      · exfalso
        rcases visit_eq_or_twin sp.wB v (hv.trans sp.hwB.symm) with rfl | rfl
        · exact hne rfl
        · exact r174w_qB_ne_qCp D sp (hq.symm.trans sp.oC'.symm)
      · exfalso
        rcases visit_eq_or_twin sp.xA v (hv.trans sp.hxA.symm) with rfl | rfl
        · exact r174w_qA_ne_qB D (sp.oA.symm.trans hq)
        · exact r174w_qB_ne_qCp D sp hq.symm
      · exact r174w_nonspecial_of_mem_Q D v hv

/-- The corners of `C'`: the two other local visits and nonspecial corners. -/
theorem r174w_corners_Cp :
    r174w_corners hP (insert w (insert x Q)) (r174w_qCp D sp) =
      insert (Sum.inr (visitTwin sp.xA)) (insert (Sum.inr (visitTwin sp.wB))
        ((r174w_corners hP (insert w (insert x Q)) (r174w_qCp D sp)).filter (r174w_Nonspecial D))) := by
  apply r174w_corners_eq_insert2_filter
  · rw [r174w_mem_corners]
    exact ⟨rfl, by change (visitTwin sp.xA).1 ∈ _; rw [visitTwin_crossing, sp.hxA]; exact r174w_x_mem_Sxw⟩
  · rw [r174w_mem_corners]
    exact ⟨sp.oC'.symm, by change (visitTwin sp.wB).1 ∈ _; rw [visitTwin_crossing, sp.hwB]; exact r174w_w_mem_Sxw⟩
  · intro a ha hne1 hne2
    rw [r174w_mem_corners] at ha
    obtain ⟨hq, hc⟩ := ha
    cases a with
    | inl i => exact r174w_nonspecial_inl D i
    | inr v =>
      have hv : v.1 ∈ insert w (insert x Q) := hc
      rw [Finset.mem_insert, Finset.mem_insert] at hv
      rcases hv with hv | hv | hv
      · exfalso
        rcases visit_eq_or_twin sp.wB v (hv.trans sp.hwB.symm) with rfl | rfl
        · exact r174w_qB_ne_qCp D sp (sp.oB.symm.trans hq)
        · exact hne2 rfl
      · exfalso
        rcases visit_eq_or_twin sp.xA v (hv.trans sp.hxA.symm) with rfl | rfl
        · exact r174w_qA_ne_qCp D sp (sp.oA.symm.trans hq)
        · exact hne1 rfl
      · exact r174w_nonspecial_of_mem_Q D v hv

/-- The corners of `AB`: `mAB` and nonspecial corners. -/
theorem r174w_corners_AB :
    r174w_corners hP (insert m Q) (r174w_qABi D) =
      insert (Sum.inr sp.mAB) ((r174w_corners hP (insert m Q) (r174w_qABi D)).filter (r174w_Nonspecial D)) := by
  apply r174w_corners_eq_insert_filter
  · rw [r174w_mem_corners]
    exact ⟨sp.oAB, by change sp.mAB.1 ∈ _; rw [sp.hmAB]; exact r174w_m_mem_Smi⟩
  · intro a ha hne
    rw [r174w_mem_corners] at ha
    obtain ⟨hq, hc⟩ := ha
    cases a with
    | inl i => exact r174w_nonspecial_inl D i
    | inr v =>
      have hv : v.1 ∈ insert m Q := hc
      rw [Finset.mem_insert] at hv
      rcases hv with hv | hv
      · exfalso
        rcases visit_eq_or_twin sp.mAB v (hv.trans sp.hmAB.symm) with rfl | rfl
        · exact hne rfl
        · exact r174w_qABi_ne_qCi D (hq.symm.trans sp.oC)
      · exact r174w_nonspecial_of_mem_Q D v hv

/-- The corners of `C`: the other visit of `m` and nonspecial corners. -/
theorem r174w_corners_C :
    r174w_corners hP (insert m Q) (r174w_qCi D) =
      insert (Sum.inr (visitTwin sp.mAB)) ((r174w_corners hP (insert m Q) (r174w_qCi D)).filter (r174w_Nonspecial D)) := by
  apply r174w_corners_eq_insert_filter
  · rw [r174w_mem_corners]
    exact ⟨sp.oC, by change (visitTwin sp.mAB).1 ∈ _; rw [visitTwin_crossing, sp.hmAB]; exact r174w_m_mem_Smi⟩
  · intro a ha hne
    rw [r174w_mem_corners] at ha
    obtain ⟨hq, hc⟩ := ha
    cases a with
    | inl i => exact r174w_nonspecial_inl D i
    | inr v =>
      have hv : v.1 ∈ insert m Q := hc
      rw [Finset.mem_insert] at hv
      rcases hv with hv | hv
      · exfalso
        rcases visit_eq_or_twin sp.mAB v (hv.trans sp.hmAB.symm) with rfl | rfl
        · exact r174w_qABi_ne_qCi D (sp.oAB.symm.trans hq)
        · exact hne rfl
      · exact r174w_nonspecial_of_mem_Q D v hv

include sp in
/-- **The nonspecial corners of `AB` are those of `A` and `B`.** -/
theorem r174w_reg_AB :
    (r174w_corners hP (insert m Q) (r174w_qABi D)).filter (r174w_Nonspecial D) =
      (r174w_corners hP (insert w (insert x Q)) (r174w_qA D)).filter (r174w_Nonspecial D) ∪
        (r174w_corners hP (insert w (insert x Q)) (r174w_qB D)).filter (r174w_Nonspecial D) := by
  ext a
  simp only [Finset.mem_union, Finset.mem_filter, r174w_mem_corners]
  constructor
  · rintro ⟨⟨h1, hc⟩, hns⟩
    have hc' := (r174w_corner_iff D a hns).mp hc
    rcases sp.triZ a (sp.onZ_AB a h1) with hA | hB | hC
    · exact Or.inl ⟨⟨hA, hc'⟩, hns⟩
    · exact Or.inr ⟨⟨hB, hc'⟩, hns⟩
    · exact absurd (h1.symm.trans (sp.P3 a hns hC)) (r174w_qABi_ne_qCi D)
  · rintro (⟨⟨hA, hc'⟩, hns⟩ | ⟨⟨hB, hc'⟩, hns⟩)
    · exact ⟨⟨sp.P1 a hns hA, (r174w_corner_iff D a hns).mpr hc'⟩, hns⟩
    · exact ⟨⟨sp.P2 a hns hB, (r174w_corner_iff D a hns).mpr hc'⟩, hns⟩

theorem r174w_reg_disj :
    Disjoint ((r174w_corners hP (insert w (insert x Q)) (r174w_qA D)).filter (r174w_Nonspecial D))
      ((r174w_corners hP (insert w (insert x Q)) (r174w_qB D)).filter (r174w_Nonspecial D)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rw [Finset.mem_filter, r174w_mem_corners] at ha hb
  exact r174w_qA_ne_qB D (ha.1.1.symm.trans hb.1.1)

/-- **The nonspecial corners of `C` are those of `C'`.** -/
theorem r174w_reg_C :
    (r174w_corners hP (insert m Q) (r174w_qCi D)).filter (r174w_Nonspecial D) =
      (r174w_corners hP (insert w (insert x Q)) (r174w_qCp D sp)).filter (r174w_Nonspecial D) := by
  ext a
  simp only [Finset.mem_filter, r174w_mem_corners]
  constructor
  · rintro ⟨⟨h1, hc⟩, hns⟩
    have hc' := (r174w_corner_iff D a hns).mp hc
    rcases sp.triZ a (sp.onZ_C a h1) with hA | hB | hC
    · exact absurd ((sp.P1 a hns hA).symm.trans h1) (r174w_qABi_ne_qCi D)
    · exact absurd ((sp.P2 a hns hB).symm.trans h1) (r174w_qABi_ne_qCi D)
    · exact ⟨⟨hC, hc'⟩, hns⟩
  · rintro ⟨⟨hC, hc'⟩, hns⟩
    exact ⟨⟨sp.P3 a hns hC, (r174w_corner_iff D a hns).mpr hc'⟩, hns⟩

theorem r174w_not_mem_filter {C : Finset (Mark P)} {a : Mark P} (h : ¬ r174w_Nonspecial D a) :
    a ∉ C.filter (r174w_Nonspecial D) := fun h' => h (Finset.mem_filter.mp h').2

/-! #### D3. The turn signs and principal turns at the six local corners (the sign condition) -/

/-- The two angle identities of the triangle of directions `u₁, u₂, u₃` under the canonical sign
condition: `∠(u₁,u₂) + ∠(u₂,u₃) = ∠(u₁,u₃)` and `∠(u₂,u₁) + ∠(u₃,u₂) = ∠(u₃,u₁)`. -/
theorem r174w_angle_identities (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    principalAngle (edge P ℓ₁) (edge P ℓ₂) + principalAngle (edge P ℓ₂) (edge P ℓ₃) =
        principalAngle (edge P ℓ₁) (edge P ℓ₃) ∧
    principalAngle (edge P ℓ₂) (edge P ℓ₁) + principalAngle (edge P ℓ₃) (edge P ℓ₂) =
        principalAngle (edge P ℓ₃) (edge P ℓ₁) := by
  have hm : IsCrossing P {ℓ₁, ℓ₃} := by rw [← D.mval]; exact m.property
  have hne : det (edge P ℓ₁) (edge P ℓ₃) ≠ 0 := crossing_det_ne_zero_of_geometry hP hm
  have h1 := hsgn
  have h2 := D.sgn
  unfold crossingSign at h1 h2
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have s13 := sign_eq_neg_one_iff.mpr hneg
    have s12 : det (edge P ℓ₁) (edge P ℓ₂) < 0 := sign_eq_neg_one_iff.mp (h1.trans s13)
    have s23 : det (edge P ℓ₂) (edge P ℓ₃) < 0 := sign_eq_neg_one_iff.mp (h2.trans s13)
    refine ⟨r174w_angle_add_of_neg s12 hneg s23, ?_⟩
    have := r174w_angle_add_of_pos (u₁ := edge P ℓ₃) (u₂ := edge P ℓ₂) (u₃ := edge P ℓ₁)
      (by rw [det_swap]; linarith) (by rw [det_swap]; linarith) (by rw [det_swap]; linarith)
    rw [add_comm]; exact this
  · have s13 := sign_eq_one_iff.mpr hpos
    have s12 : 0 < det (edge P ℓ₁) (edge P ℓ₂) := sign_eq_one_iff.mp (h1.trans s13)
    have s23 : 0 < det (edge P ℓ₂) (edge P ℓ₃) := sign_eq_one_iff.mp (h2.trans s13)
    refine ⟨r174w_angle_add_of_pos s12 hpos s23, ?_⟩
    have := r174w_angle_add_of_neg (u₁ := edge P ℓ₃) (u₂ := edge P ℓ₂) (u₃ := edge P ℓ₁)
      (by rw [det_swap]; linarith) (by rw [det_swap]; linarith) (by rw [det_swap]; linarith)
    rw [add_comm]; exact this

theorem r174w_sign13_ne_zero : crossingSign P ℓ₁ ℓ₃ ≠ 0 := by
  have hm : IsCrossing P {ℓ₁, ℓ₃} := by rw [← D.mval]; exact m.property
  unfold crossingSign
  exact sign_ne_zero.mpr (crossing_det_ne_zero_of_geometry hP hm)

/-- **The turn data at the six local corners**: the corners of `A`, `B`, `AB` turn the same way `τ`,
the corners of `C'`, `C` turn the opposite way, and the principal turns add. -/
theorem r174w_turn_data (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    r174w_tau P (Sum.inr sp.xA) = r174w_tau P (Sum.inr sp.mAB) ∧
    r174w_tau P (Sum.inr sp.wB) = r174w_tau P (Sum.inr sp.mAB) ∧
    r174w_tau P (Sum.inr (visitTwin sp.mAB)) = -r174w_tau P (Sum.inr sp.mAB) ∧
    r174w_tau P (Sum.inr (visitTwin sp.xA)) = -r174w_tau P (Sum.inr sp.mAB) ∧
    r174w_tau P (Sum.inr (visitTwin sp.wB)) = -r174w_tau P (Sum.inr sp.mAB) ∧
    r174w_tau P (Sum.inr sp.mAB) ≠ 0 ∧
    r174w_theta P (Sum.inr sp.xA) + r174w_theta P (Sum.inr sp.wB) = r174w_theta P (Sum.inr sp.mAB) ∧
    r174w_theta P (Sum.inr (visitTwin sp.xA)) + r174w_theta P (Sum.inr (visitTwin sp.wB)) =
      r174w_theta P (Sum.inr (visitTwin sp.mAB)) := by
  obtain ⟨I1, I2⟩ := r174w_angle_identities D hsgn
  have hs13 := r174w_sign13_ne_zero D
  have h23 := D.sgn
  rcases sp.hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [h1, h2, h3, D.twin_x₂, D.twin_w₃, D.twin_m₃]
    simp only [r174w_tau_visit, r174w_theta_visit]
    rw [D.twin_x₁, D.twin_x₂, D.twin_w₂, D.twin_w₃, D.twin_m₁, D.twin_m₃]
    simp only [D.x₁_edge, D.x₂_edge, D.w₂_edge, D.w₃_edge, D.m₁_edge, D.m₃_edge]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [crossingSign_swap P ℓ₁ ℓ₂, crossingSign_swap P ℓ₁ ℓ₃, hsgn]
    · rw [crossingSign_swap P ℓ₂ ℓ₃, crossingSign_swap P ℓ₁ ℓ₃, h23]
    · rw [crossingSign_swap P ℓ₃ ℓ₁]
    · rw [hsgn, crossingSign_swap P ℓ₃ ℓ₁]
    · rw [h23, crossingSign_swap P ℓ₃ ℓ₁]
    · rw [crossingSign_swap P ℓ₁ ℓ₃]
      revert hs13
      cases crossingSign P ℓ₁ ℓ₃ <;> decide
    · exact I2
    · exact I1
  · rw [h1, h2, h3, D.twin_x₁, D.twin_w₂, D.twin_m₁]
    simp only [r174w_tau_visit, r174w_theta_visit]
    rw [D.twin_x₁, D.twin_x₂, D.twin_w₂, D.twin_w₃, D.twin_m₁, D.twin_m₃]
    simp only [D.x₁_edge, D.x₂_edge, D.w₂_edge, D.w₃_edge, D.m₁_edge, D.m₃_edge]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsgn
    · exact h23
    · rw [crossingSign_swap P ℓ₁ ℓ₃]
    · rw [crossingSign_swap P ℓ₁ ℓ₂, hsgn]
    · rw [crossingSign_swap P ℓ₂ ℓ₃, h23]
    · exact hs13
    · exact I1
    · exact I2

/-! #### D4. The selector and rotation identities on the `insert` supports, exported through a
support equation (so that the ledger's `Q ∪ {m}`, `Q ∪ {x, w}` can be substituted) -/

omit D in
theorem r174w_signType_cast_neg (s : SignType) : ((-s : SignType) : ℤ) = -((s : SignType) : ℤ) := by
  cases s <;> rfl

/-- `wt(A) wt(B) = −τ wt(AB)` with `τ` the common turn of the three smoothing corners. -/
theorem r174w_weight_AB_of_split (hn : 3 ≤ n) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (Sm Sxw : Finset (Crossing P)) (hSm_eq : Sm = insert m Q) (hSxw_eq : Sxw = insert w (insert x Q)) :
    CV.weight hP Sxw (geoOwner hP Sxw (Sum.inr D.m₁)) * CV.weight hP Sxw (geoOwner hP Sxw (Sum.inr D.m₃)) =
      -((r174w_tau P (Sum.inr sp.mAB) : SignType) : ℤ) * CV.weight hP Sm (geoOwner hP Sm (Sum.inr D.x₂)) := by
  subst hSm_eq hSxw_eq
  obtain ⟨hta, htb, -, -, -, hτ, -, -⟩ := r174w_turn_data D sp hsgn
  rw [r174w_weight_eq hn hP (r174w_Sxw_indep D), r174w_weight_eq hn hP (r174w_Sxw_indep D),
    r174w_weight_eq hn hP (r174w_Sm_indep D)]
  rw [r174w_corners_A D sp, r174w_corners_B D sp, r174w_corners_AB D sp, r174w_reg_AB D sp]
  exact r174w_F_split _ _ (r174w_reg_disj D) _ _ _ (r174w_not_mem_filter D (r174w_not_nonspecial_xA D sp))
    (r174w_not_mem_filter D (r174w_not_nonspecial_wB D sp))
    (by rw [← r174w_reg_AB D sp]; exact r174w_not_mem_filter D (r174w_not_nonspecial_mAB D sp))
    _ hτ hta htb rfl

/-- `wt(C') = −τ' wt(C)` with `τ' = −τ` the common turn of the smoothing corners of `C`, `C'`. -/
theorem r174w_weight_C_of_split (hn : 3 ≤ n) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (Sm Sxw : Finset (Crossing P)) (hSm_eq : Sm = insert m Q) (hSxw_eq : Sxw = insert w (insert x Q)) :
    CV.weight hP Sxw (geoOwner hP Sxw (Sum.inr (visitTwin sp.xA))) =
      ((r174w_tau P (Sum.inr sp.mAB) : SignType) : ℤ) * CV.weight hP Sm (geoOwner hP Sm (Sum.inr D.x₁)) := by
  subst hSm_eq hSxw_eq
  obtain ⟨-, -, htc, hta, htb, hτ, -, -⟩ := r174w_turn_data D sp hsgn
  rw [r174w_weight_eq hn hP (r174w_Sxw_indep D), r174w_weight_eq hn hP (r174w_Sm_indep D)]
  rw [r174w_corners_Cp D sp, r174w_corners_C D sp, r174w_reg_C D sp]
  have hτ' : -r174w_tau P (Sum.inr sp.mAB) ≠ 0 := by
    intro h; apply hτ
    have := congrArg (fun t : SignType => -t) h
    simpa using this
  have key := r174w_F_two ((r174w_corners hP (insert w (insert x Q)) (r174w_qCp D sp)).filter (r174w_Nonspecial D))
    (Sum.inr (visitTwin sp.xA)) (Sum.inr (visitTwin sp.wB)) (Sum.inr (visitTwin sp.mAB))
    (by
      rw [Finset.mem_insert, not_or]
      exact ⟨r174w_xC_ne_wC D sp, r174w_not_mem_filter D (r174w_not_nonspecial_xC D sp)⟩)
    (r174w_not_mem_filter D (r174w_not_nonspecial_wC D sp))
    (by rw [← r174w_reg_C D sp]; exact r174w_not_mem_filter D (r174w_not_nonspecial_mC D sp))
    _ hτ' hta htb htc
  rw [key, r174w_signType_cast_neg, neg_neg]

include sp in
/-- `R(AB) = R(A) + R(B)` under `wt(AB) ≠ 0`. -/
theorem r174w_carrierR_add_of_split (hn : 3 ≤ n) (hG : CV.Generic P)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (Sm Sxw : Finset (Crossing P)) (hSm_eq : Sm = insert m Q) (hSxw_eq : Sxw = insert w (insert x Q))
    (hSm : Sm ∈ CV.Ind hG.crossingGeometry) (hSxw : Sxw ∈ CV.Ind hG.crossingGeometry)
    (hw : CV.weight hP Sm (geoOwner hP Sm (Sum.inr D.x₂)) ≠ 0) :
    CV.carrierR hn hG hSm (geoOwner hP Sm (Sum.inr D.x₂)) =
      CV.carrierR hn hG hSxw (geoOwner hP Sxw (Sum.inr D.m₁)) +
        CV.carrierR hn hG hSxw (geoOwner hP Sxw (Sum.inr D.m₃)) := by
  subst hSm_eq hSxw_eq
  obtain ⟨hta, htb, -, -, -, -, hθ, -⟩ := r174w_turn_data D sp hsgn
  exact r174w_carrierR_add_of hn hG hSm hSxw _ _ _ _ _ (r174w_reg_disj D) _ _ _
    (r174w_not_mem_filter D (r174w_not_nonspecial_xA D sp))
    (r174w_not_mem_filter D (r174w_not_nonspecial_wB D sp))
    (by rw [← r174w_reg_AB D sp]; exact r174w_not_mem_filter D (r174w_not_nonspecial_mAB D sp))
    (r174w_corners_A D sp) (r174w_corners_B D sp)
    (by rw [r174w_corners_AB D sp, r174w_reg_AB D sp]) hθ hta htb hw

/-- `rot(C') = rot(C)`, hence `R(C') = R(C)`. -/
theorem r174w_carrierR_C_of_split (hn : 3 ≤ n) (hG : CV.Generic P)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (Sm Sxw : Finset (Crossing P)) (hSm_eq : Sm = insert m Q) (hSxw_eq : Sxw = insert w (insert x Q))
    (hSm : Sm ∈ CV.Ind hG.crossingGeometry) (hSxw : Sxw ∈ CV.Ind hG.crossingGeometry) :
    CV.carrierR hn hG hSxw (geoOwner hP Sxw (Sum.inr (visitTwin sp.xA))) =
      CV.carrierR hn hG hSm (geoOwner hP Sm (Sum.inr D.x₁)) := by
  subst hSm_eq hSxw_eq
  obtain ⟨-, -, -, -, -, -, -, hθ⟩ := r174w_turn_data D sp hsgn
  unfold CV.carrierR CV.rotAbs
  rw [r174w_rot_eq_two hn hG hSm hSxw _ _
    ((r174w_corners hP (insert w (insert x Q)) (r174w_qCp D sp)).filter (r174w_Nonspecial D))
    (Sum.inr (visitTwin sp.xA)) (Sum.inr (visitTwin sp.wB)) (Sum.inr (visitTwin sp.mAB))
    (by
      rw [Finset.mem_insert, not_or]
      exact ⟨r174w_xC_ne_wC D sp, r174w_not_mem_filter D (r174w_not_nonspecial_xC D sp)⟩)
    (r174w_not_mem_filter D (r174w_not_nonspecial_wC D sp))
    (by rw [← r174w_reg_C D sp]; exact r174w_not_mem_filter D (r174w_not_nonspecial_mC D sp))
    (r174w_corners_Cp D sp) (by rw [r174w_corners_C D sp, r174w_reg_C D sp]) hθ]

/-- The carrier `C'` is the one carrying a visit of `x` and a visit of `w` (uniqueness). -/
theorem r174w_qCp_unique (Sxw : Finset (Crossing P)) (hSxw_eq : Sxw = insert w (insert x Q))
    (q' : GeoComponent hP Sxw) (v u : Visit P) (hv : v.1 = x) (hu : u.1 = w)
    (h1 : geoOwner hP Sxw (Sum.inr v) = q') (h2 : geoOwner hP Sxw (Sum.inr u) = q') :
    q' = geoOwner hP Sxw (Sum.inr (visitTwin sp.xA)) := by
  subst hSxw_eq
  rcases visit_eq_or_twin sp.xA v (hv.trans sp.hxA.symm) with rfl | rfl
  · exfalso
    rcases visit_eq_or_twin sp.wB u (hu.trans sp.hwB.symm) with rfl | rfl
    · exact r174w_qA_ne_qB D ((sp.oA.symm.trans h1).trans (h2.symm.trans sp.oB))
    · exact r174w_qA_ne_qCp D sp ((sp.oA.symm.trans h1).trans (h2.symm.trans sp.oC'.symm))
  · exact h1.symm

theorem r174w_qCp_owns (Sxw : Finset (Crossing P)) (hSxw_eq : Sxw = insert w (insert x Q)) :
    ∃ v u : Visit P, v.1 = x ∧ u.1 = w ∧
      geoOwner hP Sxw (Sum.inr v) = geoOwner hP Sxw (Sum.inr (visitTwin sp.xA)) ∧
      geoOwner hP Sxw (Sum.inr u) = geoOwner hP Sxw (Sum.inr (visitTwin sp.xA)) := by
  subst hSxw_eq
  exact ⟨visitTwin sp.xA, visitTwin sp.wB, by rw [visitTwin_crossing, sp.hxA], by rw [visitTwin_crossing, sp.hwB],
    rfl, sp.oC'.symm⟩

theorem r174w_qA_ne_qCp_export (Sxw : Finset (Crossing P)) (hSxw_eq : Sxw = insert w (insert x Q)) :
    geoOwner hP Sxw (Sum.inr D.m₁) ≠ geoOwner hP Sxw (Sum.inr (visitTwin sp.xA)) := by
  subst hSxw_eq; exact r174w_qA_ne_qCp D sp
theorem r174w_qB_ne_qCp_export (Sxw : Finset (Crossing P)) (hSxw_eq : Sxw = insert w (insert x Q)) :
    geoOwner hP Sxw (Sum.inr D.m₃) ≠ geoOwner hP Sxw (Sum.inr (visitTwin sp.xA)) := by
  subst hSxw_eq; exact r174w_qB_ne_qCp D sp
theorem r174w_qA_ne_qB_export (Sxw : Finset (Crossing P)) (hSxw_eq : Sxw = insert w (insert x Q)) :
    geoOwner hP Sxw (Sum.inr D.m₁) ≠ geoOwner hP Sxw (Sum.inr D.m₃) := by
  subst hSxw_eq; exact r174w_qA_ne_qB D
theorem r174w_qAB_ne_qC_export (Sm : Finset (Crossing P)) (hSm_eq : Sm = insert m Q) :
    geoOwner hP Sm (Sum.inr D.x₂) ≠ geoOwner hP Sm (Sum.inr D.x₁) := by
  subst hSm_eq; exact r174w_qABi_ne_qCi D

/-- The visit of `m` carried by `AB`, and the one carried by `C`. -/
theorem r174w_mAB_export (Sm : Finset (Crossing P)) (hSm_eq : Sm = insert m Q) :
    geoOwner hP Sm (Sum.inr sp.mAB) = geoOwner hP Sm (Sum.inr D.x₂) ∧
    geoOwner hP Sm (Sum.inr (visitTwin sp.mAB)) = geoOwner hP Sm (Sum.inr D.x₁) := by
  subst hSm_eq; exact ⟨sp.oAB, sp.oC⟩

/-- The canonical sign as the ledger needs it: `σ = −τ(mAB)`, with `σ = crossingSign ℓ₁ ℓ₂` exactly when
`AB` carries `m₃` (the printed orientation) and `σ = −crossingSign ℓ₁ ℓ₂` when it carries `m₁`. -/
theorem r174w_sigma_cases (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    (sp.mAB = D.m₃ ∧ -((r174w_tau P (Sum.inr sp.mAB) : SignType) : ℤ) = ((crossingSign P ℓ₁ ℓ₂ : SignType) : ℤ)) ∨
    (sp.mAB = D.m₁ ∧ -((r174w_tau P (Sum.inr sp.mAB) : SignType) : ℤ) = -((crossingSign P ℓ₁ ℓ₂ : SignType) : ℤ)) := by
  rcases sp.hcase with ⟨-, -, h3⟩ | ⟨-, -, h3⟩
  · left
    refine ⟨h3, ?_⟩
    rw [h3, r174w_tau_visit, D.twin_m₃, D.m₃_edge, D.m₁_edge, crossingSign_swap P ℓ₁ ℓ₃,
      r174w_signType_cast_neg, neg_neg, hsgn]
  · right
    refine ⟨h3, ?_⟩
    rw [h3, r174w_tau_visit, D.twin_m₁, D.m₁_edge, D.m₃_edge, hsgn]

/-! #### D5. `C` and `C'` retain the same crossings -/

theorem r174w_nonspecial_of_outside (v : Visit P) (hx : v.1 ≠ x) (hw : v.1 ≠ w) (hm : v.1 ≠ m) :
    r174w_Nonspecial D (Sum.inr v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> obtain rfl := Sum.inr.inj h
  · exact hx rfl
  · exact hx rfl
  · exact hw rfl
  · exact hw rfl
  · exact hm rfl
  · exact hm rfl

/-- For a nonspecial mark: on `C'` iff on `C`. -/
theorem r174w_owner_C_iff (a : Mark P) (hns : r174w_Nonspecial D a) :
    geoOwner hP (insert w (insert x Q)) a = r174w_qCp D sp ↔ geoOwner hP (insert m Q) a = r174w_qCi D := by
  constructor
  · intro h; exact sp.P3 a hns h
  · intro h1
    rcases sp.triZ a (sp.onZ_C a h1) with hA | hB | hC
    · exact absurd ((sp.P1 a hns hA).symm.trans h1) (r174w_qABi_ne_qCi D)
    · exact absurd ((sp.P2 a hns hB).symm.trans h1) (r174w_qABi_ne_qCi D)
    · exact hC

/-- **`C` and `C'` have the same retained crossings.** -/
theorem r174w_retained_C_eq :
    geoCarrierCrossings hP (insert w (insert x Q)) (r174w_qCp D sp) =
      geoCarrierCrossings hP (insert m Q) (r174w_qCi D) := by
  ext c
  rw [mem_geoCarrierCrossings, mem_geoCarrierCrossings]
  by_cases hcQ : c ∈ Q
  · exact iff_of_false (fun h => h.1 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hcQ)))
      (fun h => h.1 (Finset.mem_insert_of_mem hcQ))
  by_cases hcx : c = x
  · subst hcx
    exact iff_of_false (fun h => h.1 r174w_x_mem_Sxw)
      (fun h => r174w_qABi_ne_qCi D (h.2 D.x₂ rfl))
  by_cases hcw : c = w
  · subst hcw
    refine iff_of_false (fun h => h.1 r174w_w_mem_Sxw) (fun h => r174w_qABi_ne_qCi D ?_)
    have := h.2 D.w₂ rfl
    rw [← r174w_ownerm_x₂_w₂ D] at this
    exact this
  by_cases hcm : c = m
  · subst hcm
    exact iff_of_false (fun h => r174w_qA_ne_qCp D sp (h.2 D.m₁ rfl)) (fun h => h.1 r174w_m_mem_Smi)
  have hcSxw : c ∉ insert w (insert x Q) := by
    rw [Finset.mem_insert, Finset.mem_insert]; tauto
  have hcSm : c ∉ insert m Q := by
    rw [Finset.mem_insert]; tauto
  refine iff_of_eq (congrArg₂ And (propext (iff_of_true hcSxw hcSm)) ?_)
  apply propext
  constructor
  · intro h v hv
    exact (r174w_owner_C_iff D sp (Sum.inr v) (r174w_nonspecial_of_outside D v (hv ▸ hcx) (hv ▸ hcw) (hv ▸ hcm))).mp (h v hv)
  · intro h v hv
    exact (r174w_owner_C_iff D sp (Sum.inr v) (r174w_nonspecial_of_outside D v (hv ▸ hcx) (hv ▸ hcw) (hv ▸ hcm))).mpr (h v hv)

theorem r174w_retained_C_export (Sm Sxw : Finset (Crossing P)) (hSm_eq : Sm = insert m Q)
    (hSxw_eq : Sxw = insert w (insert x Q)) :
    geoCarrierCrossings hP Sxw (geoOwner hP Sxw (Sum.inr (visitTwin sp.xA))) =
      geoCarrierCrossings hP Sm (geoOwner hP Sm (Sum.inr D.x₁)) := by
  subst hSm_eq hSxw_eq
  exact r174w_retained_C_eq D sp

end R174W_Config

/-! ### D6. The ledger fields `weight_C`, `weight_AB`, `carrierR_add` (and `hσ`) on the ledger's own
supports `Q ∪ {m}`, `Q ∪ {x, w}` -/

section R174W_Ledger

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)

/-- A fixed outcome of the orientation case analysis. -/
noncomputable def r174w_sp : r174w_Split D := Classical.choice (r174w_split_exists D)

/-- **The canonical sign `σ` of the ledger**: minus the common turn of the smoothing corners of `A`, `B`,
`AB` (`= crossingSign ℓ₁ ℓ₂` in the printed orientation, its negative in the reversed one). -/
noncomputable def r174w_sigma : ℤ := -((r174w_tau P (Sum.inr (r174w_sp hG hG' D).mAB) : SignType) : ℤ)

/-- The carrier `C'` of the pair row: through the visit of `x` not carried by `A`. -/
noncomputable abbrev r174w_qC' : GeoComponent hG.crossingGeometry (Q ∪ {x, w}) :=
  geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr (visitTwin (r174w_sp hG hG' D).xA))

/-- **`hσ`**: `σ = ±1`. -/
theorem r174w_hsigma (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    r174w_sigma hG hG' D = 1 ∨ r174w_sigma hG hG' D = -1 := by
  obtain ⟨-, -, -, -, -, hτ, -, -⟩ := r174w_turn_data D (r174w_sp hG hG' D) hsgn
  unfold r174w_sigma
  revert hτ
  cases r174w_tau P (Sum.inr (r174w_sp hG hG' D).mAB) <;> decide

include hn in
/-- **`weight_AB` (GSC (5))**: `wt(A) wt(B) = σ wt(AB)` for `qAB` the carrier of `x₂` in the centre row and
`qA, qB` the carriers of `m₁, m₃` in the pair row. -/
theorem r174w_weight_AB (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqAB : qAB = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂))
    (qA qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w}))
    (hqA : qA = geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₁))
    (hqB : qB = geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₃)) :
    CV.weight hG.crossingGeometry (Q ∪ {x, w}) qA * CV.weight hG.crossingGeometry (Q ∪ {x, w}) qB =
      r174w_sigma hG hG' D * CV.weight hG.crossingGeometry (Q ∪ {m}) qAB := by
  subst hqAB hqA hqB
  exact r174w_weight_AB_of_split D (r174w_sp hG hG' D) hn hsgn (Q ∪ {m}) (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)

include hn in
/-- **`weight_C` (GSC (5))**: `wt(C') = −σ wt(C)` for `qC` the carrier of `x₁` in the centre row. -/
theorem r174w_weight_C (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (qC : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqC : qC = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₁)) :
    CV.weight hG.crossingGeometry (Q ∪ {x, w}) (r174w_qC' hG hG' D) =
      -r174w_sigma hG hG' D * CV.weight hG.crossingGeometry (Q ∪ {m}) qC := by
  subst hqC
  unfold r174w_sigma
  rw [neg_neg]
  exact r174w_weight_C_of_split D (r174w_sp hG hG' D) hn hsgn (Q ∪ {m}) (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)

/-- **`carrierR_add` (GSC (8))**: `R(AB) = R(A) + R(B)` under `wt(AB) ≠ 0`. -/
theorem r174w_carrierR_add (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqAB : qAB = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂))
    (qA qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w}))
    (hqA : qA = geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₁))
    (hqB : qB = geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₃)) :
    CV.weight hG.crossingGeometry (Q ∪ {m}) qAB ≠ 0 →
      CV.carrierR hn hG hSm qAB = CV.carrierR hn hG hSxw qA + CV.carrierR hn hG hSxw qB := by
  subst hqAB hqA hqB
  exact r174w_carrierR_add_of_split D (r174w_sp hG hG' D) hn hG hsgn (Q ∪ {m}) (Q ∪ {x, w})
    (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)
    (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto) hSm hSxw

/-- `R(C') = R(C)`. -/
theorem r174w_carrierR_C (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (qC : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqC : qC = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₁)) :
    CV.carrierR hn hG hSxw (r174w_qC' hG hG' D) = CV.carrierR hn hG hSm qC := by
  subst hqC
  exact r174w_carrierR_C_of_split D (r174w_sp hG hG' D) hn hG hsgn (Q ∪ {m}) (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)
    (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto) hSm hSxw

/-- Characterisation of `qC'` for the assembler: it is the carrier of the pair row carrying a visit of `x`
and a visit of `w`, and any such carrier is `qC'`. -/
theorem r174w_qC'_owns :
    ∃ v u : Visit P, v.1 = x ∧ u.1 = w ∧
      geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr v) = r174w_qC' hG hG' D ∧
      geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr u) = r174w_qC' hG hG' D :=
  r174w_qCp_owns D (r174w_sp hG hG' D) (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)

theorem r174w_qC'_unique (q' : GeoComponent hG.crossingGeometry (Q ∪ {x, w})) (v u : Visit P)
    (hv : v.1 = x) (hu : u.1 = w)
    (h1 : geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr v) = q')
    (h2 : geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr u) = q') : q' = r174w_qC' hG hG' D :=
  r174w_qCp_unique D (r174w_sp hG hG' D) (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto) q' v u hv hu h1 h2

theorem r174w_qA_ne_qC' :
    geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₁) ≠ r174w_qC' hG hG' D :=
  r174w_qA_ne_qCp_export D (r174w_sp hG hG' D) (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)
theorem r174w_qB_ne_qC' :
    geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₃) ≠ r174w_qC' hG hG' D :=
  r174w_qB_ne_qCp_export D (r174w_sp hG hG' D) (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)
theorem r174w_qA_ne_qB' :
    geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₁) ≠ geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₃) :=
  r174w_qA_ne_qB_export D (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)
theorem r174w_qAB_ne_qC :
    geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) ≠ geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₁) :=
  r174w_qAB_ne_qC_export D (Q ∪ {m}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)

/-- `σ` against `crossingSign ℓ₁ ℓ₂`: equal in the printed orientation (`AB ∋ m₃`), negated in the other. -/
theorem r174w_sigma_vs_crossingSign (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    (geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.m₃) = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) ∧
        r174w_sigma hG hG' D = ((crossingSign P ℓ₁ ℓ₂ : SignType) : ℤ)) ∨
    (geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.m₁) = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) ∧
        r174w_sigma hG hG' D = -((crossingSign P ℓ₁ ℓ₂ : SignType) : ℤ)) := by
  have hm := (r174w_mAB_export D (r174w_sp hG hG' D) (Q ∪ {m}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)).1
  rcases r174w_sigma_cases D (r174w_sp hG hG' D) hsgn with ⟨h3, hσ⟩ | ⟨h3, hσ⟩
  · left; rw [h3] at hm; exact ⟨hm, hσ⟩
  · right; rw [h3] at hm; exact ⟨hm, hσ⟩

/-- **`C` and `C'` retain the same crossings** (ledger supports). -/
theorem r174w_retained_C (qC : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqC : qC = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₁)) :
    geoCarrierCrossings hG.crossingGeometry (Q ∪ {x, w}) (r174w_qC' hG hG' D) =
      geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) qC := by
  subst hqC
  exact r174w_retained_C_export D (r174w_sp hG hG' D) (Q ∪ {m}) (Q ∪ {x, w})
    (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)
    (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)

/-- **The grouped polynomials of `C` and `C'` agree**: same retained crossings on the same polygon, so
the two positive lifts have isomorphic records (`GT_homfly_wall_gen` with the identity on visits). -/
theorem r174w_groupedPoly_C (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (qC : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqC : qC = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₁)) :
    CV.groupedPoly hn hG hSxw (r174w_qC' hG hG' D) = CV.groupedPoly hn hG hSm qC := by
  have hX := r174w_retained_C hG hG' D qC hqC
  have hX' : ∀ v : Visit P, v.1 ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) qC ↔
      v.1 ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {x, w}) (r174w_qC' hG hG' D) := fun v => by rw [hX]
  -- the identity on visits, with its value equation kept explicit: the kernel must never be asked to
  -- compare `Subtype.val` terms over the two different retained sets by unfolding
  obtain ⟨ψ, hψ'⟩ : ∃ ψ : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) qC} ≃
      {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {x, w}) (r174w_qC' hG hG' D)},
      ∀ z, ψ z = ⟨z.1, (hX' z.1).mp z.2⟩ := ⟨Equiv.subtypeEquivRight hX', fun z => rfl⟩
  have e : ∀ z, (ψ z).1 = z.1 := fun z => (congrArg Subtype.val (hψ' z)).trans (Subtype.coe_mk z.1 _)
  rw [GT_groupedPoly_eq_homfly, GT_groupedPoly_eq_homfly]
  unfold CV.carrierDiagram
  refine GT_homfly_wall_gen hn _ _ _ _ qC (r174w_qC' hG hG' D) ψ ?_ ?_ ?_
  · intro v hv; rw [e, e]
  · intro u v w h; rw [e, e, e]; exact h
  · intro v; rw [e]

/-- **`omega_C`**: `Ω₁(C') = Ω₁(C)` (same retained record, writhe, rotation, slot, read). -/
theorem r174w_omega_C (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (qC : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqC : qC = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₁)) :
    CV.Omega1 hn hG hSxw (r174w_qC' hG hG' D) = CV.Omega1 hn hG hSm qC := by
  unfold CV.Omega1 CV.slot
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG hSxw, CV.groupedWrithe_eq_card_geoCarrierCrossings hG hSm,
    r174w_retained_C hG hG' D qC hqC, r174w_carrierR_C hn hG hG' D hsgn hSm hSxw qC hqC,
    r174w_groupedPoly_C hn hG hG' D hSm hSxw qC hqC]

end R174W_Ledger

end

end SM.Link



/-! ## Unit SMOOTH (Wave 2, R174_SMOOTH): the oriented smoothing `D₀` of the `E`-side lift at `x'` and the
ledger fields `D₀, qx, fulltwist, i, j, ℓ, smoothing, writhe_count` (U_R174_REPORT §4 items 5–6,
`gsc_smoothing_split`)

Prover of unit SMOOTH, 2026-09-15.  Everything below is NEW (nothing above changed); names carry the prefix
`r174s_`.  Plan: `D₀ := r174s_D₀ D_H qx` is the library smoothing `smoothDiagram` (the `D₀` of
`exists_smoothing`, so the SAME `D₀` as `gsc_fulltwist_of_bigon` / `s174_fulltwist_of_hrec` produce), with
its record clause `D₀.record ≅ D_H.record.smooth (overVisit qx)`.  Since `D_H` has one circle, `qx` is a
self crossing and the smoothing has two circles, the `s₁`-cycles of the two occurrences of `qx`; the
occurrences on each circle are exactly the occurrences strictly inside one of the two open arcs of
`D_H.record` cut at the two occurrences of `qx` (B).  The knot restriction of `D₀` to a circle has the
record `D₀.record.restrict {i}` (`restrict_record`), which is `(D_H.record.smooth v).restrict {circle}`
along the record clause (`RecordIso.restrict`), and that is `D_H.record.restrictCrossings K` for `K` the
crossings of `D_H` internal to the arc (B: the first-return successor along `s₁ = s ∘ swap(v, τ v)` on the
arc-internal occurrences is the first return along `s`, `r174s_firstReturn_reconnect_eq`).  The geometric
content — that these two arc records are the `P-ac` records of `A` and `B` — is the wall/ownership
transport of U_R174 §4 items 1–2 and is the one BLACK BOX here (`r174s_arc_rec_prop`, §D).  From it and
ax:gausscode: `componentCount = 2`, `i ≠ j`, `homfly (knotRestrict i/j) = Q_A / Q_B`, the linking number
(`exists_linkingNumber`), and the writhe count `w_H − 1 = w(D₀) = w_A + w_B + 2ℓ` (all crossings positive;
`writhe_wall` turns it into (10)). -/

namespace SM.Link

open SM SM.GeoCarrier SM.Carrier RProof

noncomputable section

namespace Record

variable (ρ : Record)

/-- The crossings both of whose occurrences lie strictly inside the forward arc from `u` to `τ u`
(the "`A`-string" of the smoothing at the crossing of `u`). -/
def r174s_KeepArc (u : ρ.M) : Set ρ.Crossing :=
  {c | ∀ w ∈ c.1, ρ.ArcBetween u w (ρ.pair u)}

theorem r174s_crossKeep_keepArc_iff (u w : ρ.M) :
    ρ.CrossKeep (ρ.r174s_KeepArc u) w ↔
      ρ.ArcBetween u w (ρ.pair u) ∧ ρ.ArcBetween u (ρ.pair w) (ρ.pair u) := by
  show (∀ z ∈ ({w, ρ.pair w} : Finset ρ.M), ρ.ArcBetween u z (ρ.pair u)) ↔ _
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]

/-- The circle of the smoothing at `u` carrying the open arc `(a, τ a)` (`a ∈ {u, τ u}`): the
`s₁`-cycle of `τ a`. -/
def r174s_arcComp (u a : ρ.M) : (ρ.smooth u).comps :=
  Sum.inl (Quotient.mk (Equiv.Perm.SameCycle.setoid (ρ.reconnect u)) (ρ.pair a))

section OneCircle

variable (h1 : ρ.componentCount = 1)
include h1

/-- On one circle every crossing is a self crossing. -/
theorem r174s_isSelfCrossing (u : ρ.M) : ρ.IsSelfCrossing u :=
  ρ.comp_eq_of_one_circle h1 u (ρ.pair u)

theorem r174s_arcBetween_pair_iff (u w : ρ.M) :
    ρ.ArcBetween u w (ρ.pair u) ↔ 0 < ρ.steps u w ∧ ρ.steps u w < ρ.steps u (ρ.pair u) := by
  rw [ρ.arcBetween_iff_posBetween h1 u, ρ.steps_self]
  unfold PosBetween
  omega

/-- An occurrence of the open arc `(u, τ u)` lies on the `s₁`-cycle of `τ u` ("(x A y B) ↦ (x B), (y A)":
the cycle `(y A)`). -/
theorem r174s_reconnect_sameCycle_pair_of_arc {u w : ρ.M} (hw : ρ.ArcBetween u w (ρ.pair u)) :
    (ρ.reconnect u).SameCycle w (ρ.pair u) := by
  obtain ⟨hpos, hlt⟩ := (ρ.r174s_arcBetween_pair_iff h1 u w).mp hw
  have hwk : (ρ.succ ^ ρ.steps u w) u = w := ρ.pow_steps h1 u w
  have hpL : (ρ.succ ^ ρ.steps u (ρ.pair u)) u = ρ.pair u := ρ.pow_steps h1 u (ρ.pair u)
  have hcard : ρ.steps u (ρ.pair u) < Fintype.card ρ.M := ρ.steps_lt_card h1 u (ρ.pair u)
  have avoid : ∀ j, j < ρ.steps u (ρ.pair u) - ρ.steps u w →
      (ρ.succ ^ j) w ≠ u ∧ (ρ.succ ^ j) w ≠ ρ.pair u := by
    intro j hj
    have e : (ρ.succ ^ j) w = (ρ.succ ^ (j + ρ.steps u w)) u := by
      rw [pow_add, Equiv.Perm.mul_apply, hwk]
    rw [e]
    constructor
    · intro h
      have h0 : (ρ.succ ^ (j + ρ.steps u w)) u = (ρ.succ ^ 0) u := by
        rw [h, pow_zero, Equiv.Perm.one_apply]
      have := (ρ.pow_apply_eq_pow_apply_iff h1 u (by omega) (by omega)).mp h0
      omega
    · intro h
      have := ρ.steps_le_of_pow h
      omega
  have key : (ρ.succ ^ (ρ.steps u (ρ.pair u) - ρ.steps u w)) w = ρ.pair u := by
    calc (ρ.succ ^ (ρ.steps u (ρ.pair u) - ρ.steps u w)) w
        = (ρ.succ ^ (ρ.steps u (ρ.pair u) - ρ.steps u w)) ((ρ.succ ^ ρ.steps u w) u) := by rw [hwk]
      _ = (ρ.succ ^ (ρ.steps u (ρ.pair u) - ρ.steps u w + ρ.steps u w)) u := by
          rw [pow_add, Equiv.Perm.mul_apply]
      _ = ρ.pair u := by rw [Nat.sub_add_cancel hlt.le, hpL]
  refine ⟨((ρ.steps u (ρ.pair u) - ρ.steps u w : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast]
  show ((ρ.succ * Equiv.swap u (ρ.pair u)) ^ (ρ.steps u (ρ.pair u) - ρ.steps u w)) w = ρ.pair u
  rw [mul_swap_pow_apply_of_forall_ne ρ.succ u (ρ.pair u) w _ avoid, key]

theorem r174s_reconnect_sameCycle_self_of_arc {u w : ρ.M} (hw : ρ.ArcBetween (ρ.pair u) w u) :
    (ρ.reconnect u).SameCycle w u := by
  have := ρ.r174s_reconnect_sameCycle_pair_of_arc h1 (u := ρ.pair u) (w := w)
    (by rw [ρ.pair_invol]; exact hw)
  rw [ρ.reconnect_pair, ρ.pair_invol] at this
  exact this

/-- For a retained occurrence: on the `s₁`-cycle of `τ u` iff strictly inside the arc `(u, τ u)`. -/
theorem r174s_reconnect_sameCycle_pair_iff {u w : ρ.M} (hw : ρ.SmoothKeep u w) :
    (ρ.reconnect u).SameCycle w (ρ.pair u) ↔ ρ.ArcBetween u w (ρ.pair u) := by
  obtain ⟨hwu, hwp⟩ := (ρ.smoothKeep_iff u w).mp hw
  refine ⟨fun h => ?_, ρ.r174s_reconnect_sameCycle_pair_of_arc h1⟩
  rcases ρ.arcBetween_or_arcBetween h1 (Ne.symm hwu) (ρ.ne_pair u) hwp with h' | h'
  · exact h'
  · exfalso
    have h2 : (ρ.reconnect u).SameCycle w u :=
      ρ.r174s_reconnect_sameCycle_self_of_arc h1 ((ρ.arcBetween_rotate h1 u (ρ.pair u) w).mp h')
    exact ρ.not_reconnect_sameCycle_pair_of_self u (ρ.r174s_isSelfCrossing h1 u) (h2.symm.trans h)

/-- The circle of a retained occurrence of the smoothing at `u` is the arc circle of `a ∈ {u, τ u}`
exactly when the occurrence lies strictly inside the arc `(a, τ a)`. -/
theorem r174s_smooth_comp_eq_iff {u a : ρ.M} (ha : a = u ∨ a = ρ.pair u) (w : (ρ.smooth u).M) :
    (ρ.smooth u).comp w = ρ.r174s_arcComp u a ↔ ρ.ArcBetween a w.1 (ρ.pair a) := by
  have hr : ρ.reconnect a = ρ.reconnect u := by
    rcases ha with rfl | rfl
    · rfl
    · exact ρ.reconnect_pair u
  have hk : ρ.SmoothKeep a w.1 := by
    rcases ha with rfl | rfl
    · exact w.2
    · exact (ρ.smoothKeep_pair_eq u w.1).mpr w.2
  rw [ρ.smooth_comp]
  unfold r174s_arcComp
  constructor
  · intro h
    have h' : (ρ.reconnect u).SameCycle w.1 (ρ.pair a) := Quotient.exact (Sum.inl.inj h)
    rw [← hr] at h'
    exact (ρ.r174s_reconnect_sameCycle_pair_iff h1 hk).mp h'
  · intro h
    have h' := (ρ.r174s_reconnect_sameCycle_pair_iff h1 hk).mpr h
    rw [hr] at h'
    exact congrArg Sum.inl (Quotient.sound h')

/-- The two arc circles are distinct. -/
theorem r174s_arcComp_ne (u : ρ.M) : ρ.r174s_arcComp u u ≠ ρ.r174s_arcComp u (ρ.pair u) := by
  unfold r174s_arcComp
  rw [ρ.pair_invol]
  exact (ρ.smooth_comps_ne_of_self u (ρ.r174s_isSelfCrossing h1 u)).symm

end OneCircle

end Record

/-- **First return after swapping a non-retained point with its non-retained predecessor.**  If `g b = a`
with `a, b` outside the retained set `p`, the permutation `g * swap a b` (which fixes `a` and sends `b`
to `g a`) has the same first return to `p` as `g`: both first returns to `(· ≠ a)` agree pointwise
(`firstReturn_apply_of_mem` / `_of_not_mem`), and the first return to `p` factors through it
(`firstReturn_firstReturn`). -/
theorem r174s_firstReturn_mul_swap_of_apply_eq {β : Type*} [Fintype β] [DecidableEq β]
    (g : Equiv.Perm β) (p : β → Prop) [DecidablePred p] {a b : β} (hgb : g b = a) (hab : a ≠ b)
    (ha : ¬ p a) :
    firstReturn (g * Equiv.swap a b) p = firstReturn g p := by
  have hga : g a ≠ a := fun h => hab (g.injective (h.trans hgb.symm))
  have hq : ∀ m, p m → m ≠ a := fun m hm h => ha (h ▸ hm)
  have key : firstReturn (g * Equiv.swap a b) (fun m => m ≠ a) = firstReturn g (fun m => m ≠ a) := by
    refine Equiv.ext fun m => Subtype.ext ?_
    by_cases hmb : m.1 = b
    · rw [firstReturn_apply_of_mem (g * Equiv.swap a b) _ m
          (by rw [Equiv.Perm.mul_apply, hmb, Equiv.swap_apply_right]; exact hga),
        firstReturn_apply_of_not_mem g _ m (by rw [hmb, hgb]; exact not_not.mpr rfl)
          (by rw [hmb, hgb]; exact hga),
        Equiv.Perm.mul_apply, hmb, Equiv.swap_apply_right, hgb]
    · have hsw : (g * Equiv.swap a b) m.1 = g m.1 := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne m.2 hmb]
      have hgm : g m.1 ≠ a := fun h => hmb (g.injective (h.trans hgb.symm))
      rw [firstReturn_apply_of_mem _ _ m (by rw [hsw]; exact hgm),
        firstReturn_apply_of_mem g _ m hgm, hsw]
  refine Equiv.ext fun m => Subtype.ext ?_
  have hand : ∀ z, p z ↔ (z ≠ a ∧ p z) := fun z => ⟨fun h => ⟨hq z h, h⟩, fun h => h.2⟩
  have c1 : (firstReturn (g * Equiv.swap a b) p m).1 =
      (firstReturn (g * Equiv.swap a b) (fun z => z ≠ a ∧ p z) ⟨m.1, (hand _).mp m.2⟩).1 :=
    firstReturn_val_congr _ _ _ _ hand m (fun _ => rfl)
  have c2 : (firstReturn g p m).1 =
      (firstReturn g (fun z => z ≠ a ∧ p z) ⟨m.1, (hand _).mp m.2⟩).1 :=
    firstReturn_val_congr _ _ _ _ hand m (fun _ => rfl)
  have e1 := firstReturn_firstReturn (g * Equiv.swap a b) (fun z => z ≠ a) p ⟨⟨m.1, hq _ m.2⟩, m.2⟩
  have e2 := firstReturn_firstReturn g (fun z => z ≠ a) p ⟨⟨m.1, hq _ m.2⟩, m.2⟩
  rw [c1, c2, ← e1, ← e2, key]

namespace Record

variable (ρ : Record) (h1 : ρ.componentCount = 1)
include h1

/-- **The first return to the arc-internal crossings is the same for `s` and for `s₁ = s ∘ swap(u, τ u)`.**
Through the retained set `P⁺ = P ∪ {u, τ u}`: `firstReturn s₁ P⁺ = firstReturn s P⁺ * swap u (τ u)`
(`firstReturn_mul_swap`), the `P⁺`-first return of `τ u` along `s` is `u` (no `P`-point on the other arc),
so the swap is harmless (`r174s_firstReturn_mul_swap_of_apply_eq`), and both first returns to `P` factor
through `P⁺` (`firstReturn_firstReturn`). -/
theorem r174s_firstReturn_reconnect_eq (u : ρ.M) (P : ρ.M → Prop) [DecidablePred P]
    (hP : ∀ m, P m ↔ ρ.CrossKeep (ρ.r174s_KeepArc u) m) (w : {m // P m}) :
    (firstReturn (ρ.reconnect u) P w).1 = (firstReturn ρ.succ P w).1 := by
  classical
  have hPu : ¬ P u := by
    intro h
    have h' := ((ρ.r174s_crossKeep_keepArc_iff u u).mp ((hP u).mp h)).1
    rw [ArcBetween, ρ.steps_self] at h'
    exact lt_irrefl 0 h'.1
  have hPp : ¬ P (ρ.pair u) := by
    intro h
    exact lt_irrefl _ ((ρ.r174s_crossKeep_keepArc_iff u _).mp ((hP _).mp h)).1.2
  let Pp : ρ.M → Prop := fun m => P m ∨ m = u ∨ m = ρ.pair u
  have hPpu : Pp u := Or.inr (Or.inl rfl)
  have hPpp : Pp (ρ.pair u) := Or.inr (Or.inr rfl)
  have hsub : ∀ m, P m → Pp m := fun m h => Or.inl h
  have hand : ∀ m, P m ↔ (Pp m ∧ P m) := fun m => ⟨fun h => ⟨Or.inl h, h⟩, fun h => h.2⟩
  have hL : 0 < ρ.steps u (ρ.pair u) := (ρ.steps_pos_iff h1 u _).mpr (ρ.ne_pair u)
  have hcard := ρ.steps_lt_card h1 u (ρ.pair u)
  -- the `P⁺`-first return of `τ u` is `u`
  have hg : firstReturn ρ.succ Pp ⟨ρ.pair u, hPpp⟩ = ⟨u, hPpu⟩ := by
    apply Subtype.ext
    show (firstReturn ρ.succ Pp ⟨ρ.pair u, hPpp⟩).1 = u
    rw [ρ.firstReturn_val_eq_iff Pp h1 ⟨ρ.pair u, hPpp⟩ ⟨u, hPpu, ρ.ne_pair u⟩ u]
    refine ⟨hPpu, ρ.ne_pair u, fun k hk hku => ?_⟩
    rcases hk with hk | rfl | rfl
    · have hk' := (ρ.r174s_arcBetween_pair_iff h1 u k).mp
        ((ρ.r174s_crossKeep_keepArc_iff u k).mp ((hP k).mp hk)).1
      rw [ρ.steps_eq_of_base h1 u (ρ.pair u) u, ρ.steps_eq_of_base h1 u (ρ.pair u) k, ρ.steps_self]
      split_ifs <;> omega
    · exact le_refl _
    · exact absurd rfl hku
  have e1 : (firstReturn (ρ.reconnect u) P w).1 =
      ((firstReturn (firstReturn (ρ.reconnect u) Pp) (fun m => P m.1))
        ⟨⟨w.1, hsub _ w.2⟩, w.2⟩).1.1 := by
    rw [firstReturn_firstReturn]
    exact firstReturn_val_congr _ _ P (fun m => Pp m ∧ P m) hand w (fun _ => rfl)
  have e2 : (firstReturn ρ.succ P w).1 =
      ((firstReturn (firstReturn ρ.succ Pp) (fun m => P m.1)) ⟨⟨w.1, hsub _ w.2⟩, w.2⟩).1.1 := by
    rw [firstReturn_firstReturn]
    exact firstReturn_val_congr _ _ P (fun m => Pp m ∧ P m) hand w (fun _ => rfl)
  have e3 : firstReturn (ρ.reconnect u) Pp =
      firstReturn ρ.succ Pp * Equiv.swap ⟨u, hPpu⟩ ⟨ρ.pair u, hPpp⟩ :=
    firstReturn_mul_swap ρ.succ Pp u (ρ.pair u) hPpu hPpp
  have e4 : firstReturn (firstReturn ρ.succ Pp * Equiv.swap ⟨u, hPpu⟩ ⟨ρ.pair u, hPpp⟩)
      (fun m => P m.1) = firstReturn (firstReturn ρ.succ Pp) (fun m => P m.1) :=
    r174s_firstReturn_mul_swap_of_apply_eq (firstReturn ρ.succ Pp) (fun m => P m.1) hg
      (fun h => ρ.ne_pair u (congrArg Subtype.val h)) hPu
  rw [e1, e2, e3, e4]

/-- **Restricting the smoothing at `u` to an arc circle is the arc-internal crossing record**:
`(ρ.smooth u).restrict {arc circle of a} ≅ ρ.restrictCrossings (r174s_KeepArc a)` for `a ∈ {u, τ u}`
(occurrences: `r174s_smooth_comp_eq_iff`; successor: `firstReturn_firstReturn` and
`r174s_firstReturn_reconnect_eq`; both records have one circle). -/
theorem r174s_restrict_smooth_iso {u a : ρ.M} (ha : a = u ∨ a = ρ.pair u) :
    Nonempty (RecordIso ((ρ.smooth u).restrict {ρ.r174s_arcComp u a})
      (ρ.restrictCrossings (ρ.r174s_KeepArc a))) := by
  classical
  have hr : ρ.reconnect a = ρ.reconnect u := by
    rcases ha with rfl | rfl
    · rfl
    · exact ρ.reconnect_pair u
  have hk : ∀ m, ρ.SmoothKeep u m ↔ ρ.SmoothKeep a m := by
    intro m
    rcases ha with rfl | rfl
    · exact Iff.rfl
    · exact (ρ.smoothKeep_pair_eq u m).symm
  have hkeep : ∀ w : (ρ.smooth u).M,
      (ρ.smooth u).RestrictKeep {ρ.r174s_arcComp u a} w ↔ ρ.CrossKeep (ρ.r174s_KeepArc a) w.1 := by
    intro w
    rw [ρ.r174s_crossKeep_keepArc_iff]
    show ((ρ.smooth u).comp w ∈ ({ρ.r174s_arcComp u a} : Finset _) ∧
      (ρ.smooth u).comp ((ρ.smooth u).pair w) ∈ ({ρ.r174s_arcComp u a} : Finset _)) ↔ _
    rw [Finset.mem_singleton, Finset.mem_singleton, ρ.r174s_smooth_comp_eq_iff h1 ha,
      ρ.r174s_smooth_comp_eq_iff h1 ha]
    exact Iff.rfl
  have hsk : ∀ m, ρ.CrossKeep (ρ.r174s_KeepArc a) m → ρ.SmoothKeep u m := by
    intro m hm
    rw [hk, ρ.smoothKeep_iff]
    obtain ⟨h1', -⟩ := (ρ.r174s_crossKeep_keepArc_iff a m).mp hm
    obtain ⟨hpos, hlt⟩ := (ρ.r174s_arcBetween_pair_iff h1 a m).mp h1'
    constructor
    · rintro rfl
      rw [ρ.steps_self] at hpos
      exact lt_irrefl _ hpos
    · rintro rfl
      exact lt_irrefl _ hlt
  let Φ : ((ρ.smooth u).restrict {ρ.r174s_arcComp u a}).M ≃
      (ρ.restrictCrossings (ρ.r174s_KeepArc a)).M :=
    { toFun := fun w => ⟨w.1.1, (hkeep w.1).mp w.2⟩
      invFun := fun m => ⟨⟨m.1, hsk m.1 m.2⟩, (hkeep ⟨m.1, hsk m.1 m.2⟩).mpr m.2⟩
      left_inv := fun w => rfl
      right_inv := fun m => rfl }
  refine ⟨RecordIso.ofOccOfCard Φ ?_ (fun w => rfl) (fun w => rfl) (fun w => rfl) ?_⟩
  · intro w
    apply Subtype.ext
    have s1 : (((ρ.smooth u).restrict {ρ.r174s_arcComp u a}).succ w).1.1 =
        (firstReturn (ρ.reconnect u) (fun m => ρ.SmoothKeep u m ∧ ρ.CrossKeep (ρ.r174s_KeepArc a) m)
          ⟨w.1.1, w.1.2, (hkeep w.1).mp w.2⟩).1 := by
      refine Eq.trans ?_ (firstReturn_firstReturn (ρ.reconnect u) (ρ.SmoothKeep u)
        (ρ.CrossKeep (ρ.r174s_KeepArc a)) ⟨w.1, (hkeep w.1).mp w.2⟩)
      exact congrArg Subtype.val (firstReturn_val_congr _ _ _ _ hkeep w (fun _ => rfl))
    have s2 : (firstReturn (ρ.reconnect u)
        (fun m => ρ.SmoothKeep u m ∧ ρ.CrossKeep (ρ.r174s_KeepArc a) m)
          ⟨w.1.1, w.1.2, (hkeep w.1).mp w.2⟩).1 =
        (firstReturn (ρ.reconnect a) (ρ.CrossKeep (ρ.r174s_KeepArc a))
          ⟨w.1.1, (hkeep w.1).mp w.2⟩).1 :=
      firstReturn_val_congr _ _ _ _ (fun m => ⟨fun h => h.2, fun h => ⟨hsk m h, h⟩⟩) _
        (fun n => by rw [hr])
    have s3 := ρ.r174s_firstReturn_reconnect_eq h1 a (ρ.CrossKeep (ρ.r174s_KeepArc a))
      (fun _ => Iff.rfl) ⟨w.1.1, (hkeep w.1).mp w.2⟩
    exact s1.trans (s2.trans s3)
  · show ((ρ.smooth u).restrict {ρ.r174s_arcComp u a}).componentCount =
      (ρ.restrictCrossings (ρ.r174s_KeepArc a)).componentCount
    rw [ρ.componentCount_restrictCrossings, h1, (ρ.smooth u).componentCount_restrict,
      Finset.card_singleton]

end Record

/-! ## C. Diagram level: the library smoothing `D₀`, its two components and their knot restrictions

The counting lemmas `r174s_writhe_restrict … r174s_writhe_two_component` and `r174s_record_writhe_smooth`
are the U110-H lemmas `s7h_*` of SM/CornerChainUnits.lean (accepted library material not in this file's
import chain), reproduced verbatim under the `r174s_` prefix. -/

/-- The writhe of a block restriction is the sum of the signs of the internal crossings of the block
(`Shadow.restrictCrossingEquiv`, `Diagram.restrict_sign`). -/
theorem r174s_writhe_restrict (D : Diagram) (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty) :
    (D.restrict B hB).writhe =
      ∑ x : {x : D.Γ.Crossing // ∀ s ∈ x.val, s.1 ∈ B}, (D.sign x.1 : ℤ) := by
  unfold Diagram.writhe
  exact Fintype.sum_equiv (D.Γ.restrictCrossingEquiv B hB) _ _
    (fun y => by rw [D.restrict_sign B hB y]; rfl)

/-- The self crossings of the component `i`: both strands on `i` (`val_eq_pair`). -/
theorem r174s_self_iff (D : Diagram) (i : Fin D.Γ.c) (x : D.Γ.Crossing) :
    (∀ s ∈ x.val, s.1 ∈ ({i} : Finset (Fin D.Γ.c))) ↔
      (D.overStrand x).1 = i ∧ (D.underStrand x).1 = i := by
  rw [D.val_eq_pair x]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]

/-- "their actual knot restrictions" (mp:lowest): the writhe of `D.knotRestrict i` is the sum of the
signs of the self crossings of component `i` (eq. s7c:crossing-partition, first two rows). -/
theorem r174s_writhe_knotRestrict (D : Diagram) (i : Fin D.Γ.c) :
    (D.knotRestrict i).writhe =
      ∑ x ∈ Finset.univ.filter
        (fun x : D.Γ.Crossing => (D.overStrand x).1 = i ∧ (D.underStrand x).1 = i),
        (D.sign x : ℤ) := by
  unfold Diagram.knotRestrict
  rw [r174s_writhe_restrict]
  have hfilt : Finset.univ.filter
      (fun x : D.Γ.Crossing => (D.overStrand x).1 = i ∧ (D.underStrand x).1 = i) =
      Finset.univ.filter
        (fun x : D.Γ.Crossing => ∀ s ∈ x.val, s.1 ∈ ({i} : Finset (Fin D.Γ.c))) :=
    Finset.filter_congr fun x _ => (r174s_self_iff D i x).symm
  rw [hfilt]
  exact (Finset.sum_subtype (Finset.univ.filter
    (fun x : D.Γ.Crossing => ∀ s ∈ x.val, s.1 ∈ ({i} : Finset (Fin D.Γ.c))))
    (fun x => by simp) (fun x => (D.sign x : ℤ))).symm

/-- `2ℓ_ij` as a sum over the mixed crossings (each mixed crossing is exactly one ordered strand pair
`(s, t)` with `s` on `i`, `t` on `j`; eq. s7c:crossing-partition, third row). -/
theorem r174s_mixedSignSum_eq (D : Diagram) (i j : Fin D.Γ.c) (hij : i ≠ j) :
    mixedSignSum D i j =
      ∑ x ∈ Finset.univ.filter (fun x : D.Γ.Crossing =>
        ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∨
        ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i)), (D.sign x : ℤ) := by
  classical
  unfold mixedSignSum
  rw [← Finset.sum_product' Finset.univ Finset.univ (fun s t : D.Γ.Strand =>
    if h : D.Γ.MixedPair i j s t then ((D.sign ⟨{s, t}, h.2.2⟩ : SignType) : ℤ) else 0)]
  -- the term of an ordered pair is nonzero only when it is a mixed pair
  have hmp : ∀ p : D.Γ.Strand × D.Γ.Strand,
      (if h : D.Γ.MixedPair i j p.1 p.2 then ((D.sign ⟨{p.1, p.2}, h.2.2⟩ : SignType) : ℤ) else 0) ≠ 0 →
      D.Γ.MixedPair i j p.1 p.2 := by
    intro p hne
    by_contra hm
    exact hne (dite_eq_right hm)
  refine Finset.sum_bij_ne_zero (fun p _ hne => ⟨{p.1, p.2}, (hmp p hne).2.2⟩) ?_ ?_ ?_ ?_
  · -- lands in the mixed crossings
    intro p _ hne
    have hm := hmp p hne
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases D.eq_over_under_of_crossing_eq hm.2.2 rfl with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · left; exact ⟨by rw [← hs]; exact hm.1, by rw [← ht]; exact hm.2.1⟩
    · right; exact ⟨by rw [← ht]; exact hm.2.1, by rw [← hs]; exact hm.1⟩
  · -- injective: the pair is recovered from the crossing by the components
    intro p₁ _ hne₁ p₂ _ hne₂ e
    have hm₁ := hmp p₁ hne₁
    have hm₂ := hmp p₂ hne₂
    have e' : ({p₁.1, p₁.2} : Finset D.Γ.Strand) = {p₂.1, p₂.2} := congrArg Subtype.val e
    have hs : p₁.1 ∈ ({p₂.1, p₂.2} : Finset D.Γ.Strand) := by
      rw [← e']; exact Finset.mem_insert_self _ _
    have ht : p₁.2 ∈ ({p₂.1, p₂.2} : Finset D.Γ.Strand) := by
      rw [← e']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [Finset.mem_insert, Finset.mem_singleton] at hs ht
    refine Prod.ext ?_ ?_
    · exact hs.resolve_right fun h => hij (by rw [← hm₁.1, h, hm₂.2.1])
    · exact ht.resolve_left fun h => hij (by rw [← hm₂.1, ← h, hm₁.2.1])
  · -- surjective onto the mixed crossings
    intro x hx _
    have hx' := (Finset.mem_filter.mp hx).2
    have hsgn : ((D.sign x : SignType) : ℤ) ≠ 0 := by
      rcases D.sign_eq_one_or_neg_one x with h | h <;> rw [h] <;> decide
    rcases hx' with ⟨ho, hu⟩ | ⟨ho, hu⟩
    · have hm : D.Γ.MixedPair i j (D.overStrand x) (D.underStrand x) :=
        ⟨ho, hu, by rw [← D.val_eq_pair x]; exact x.2⟩
      refine ⟨(D.overStrand x, D.underStrand x), Finset.mem_univ _, ?_, ?_⟩
      · rw [dite_eq_left hm]
        have e : (⟨{D.overStrand x, D.underStrand x}, hm.2.2⟩ : D.Γ.Crossing) = x :=
          Subtype.ext (D.val_eq_pair x).symm
        rw [e]; exact hsgn
      · exact Subtype.ext (D.val_eq_pair x).symm
    · have hm : D.Γ.MixedPair i j (D.underStrand x) (D.overStrand x) :=
        ⟨hu, ho, by rw [Finset.pair_comm, ← D.val_eq_pair x]; exact x.2⟩
      refine ⟨(D.underStrand x, D.overStrand x), Finset.mem_univ _, ?_, ?_⟩
      · rw [dite_eq_left hm]
        have e : (⟨{D.underStrand x, D.overStrand x}, hm.2.2⟩ : D.Γ.Crossing) = x :=
          Subtype.ext ((Finset.pair_comm _ _).trans (D.val_eq_pair x).symm)
        rw [e]; exact hsgn
      · exact Subtype.ext ((Finset.pair_comm _ _).trans (D.val_eq_pair x).symm)
  · -- the terms agree
    intro p _ hne
    rw [dite_eq_left (hmp p hne)]

/-- With two components `i ≠ j`, every component is `i` or `j`. -/
theorem r174s_comp_eq_or (D : Diagram) {i j : Fin D.Γ.c} (h2 : D.componentCount = 2) (hij : i ≠ j)
    (c : Fin D.Γ.c) : c = i ∨ c = j := by
  have huniv : ({i, j} : Finset (Fin D.Γ.c)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_pair hij, Finset.card_univ, Fintype.card_fin]
    exact h2.le
  have hc : c ∈ ({i, j} : Finset (Fin D.Γ.c)) := by rw [huniv]; exact Finset.mem_univ c
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hc

/-- A two-component diagram has two distinct component indices. -/
theorem r174s_exists_two_components (D : Diagram) (h2 : D.componentCount = 2) :
    ∃ i j : Fin D.Γ.c, i ≠ j := by
  unfold Diagram.componentCount at h2
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
  intro h
  have := congrArg Fin.val h
  simp at this

/-- **eq. s7c:crossing-partition as a writhe identity**: for a two-component diagram the writhe is the
sum of the writhes of the two knot restrictions plus `2ℓ` ("the self crossings contribute `w₁ + w₂`,
the mixed crossings of `D_A` contribute `2ℓ`", sm-4:649-651). -/
theorem r174s_writhe_two_component (D : Diagram) (i j : Fin D.Γ.c) (h2 : D.componentCount = 2)
    (hij : i ≠ j) :
    D.writhe = (D.knotRestrict i).writhe + (D.knotRestrict j).writhe + twoLinking D i j := by
  have key : ∀ x : D.Γ.Crossing, (D.sign x : ℤ) =
      (if (D.overStrand x).1 = i ∧ (D.underStrand x).1 = i then (D.sign x : ℤ) else 0) +
      (if (D.overStrand x).1 = j ∧ (D.underStrand x).1 = j then (D.sign x : ℤ) else 0) +
      (if ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∨
          ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i) then (D.sign x : ℤ) else 0) := by
    intro x
    have hji : j ≠ i := hij.symm
    rcases r174s_comp_eq_or D h2 hij (D.overStrand x).1 with ho | ho <;>
      rcases r174s_comp_eq_or D h2 hij (D.underStrand x).1 with hu | hu <;>
      simp [ho, hu, hij, hji]
  rw [r174s_writhe_knotRestrict, r174s_writhe_knotRestrict, twoLinking, r174s_mixedSignSum_eq D i j hij]
  unfold Diagram.writhe
  rw [Finset.sum_congr rfl (fun x _ => key x), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]


/-- The record-level smoothing drops the writhe by the sign of the smoothed crossing (the two erased
occurrences carry that sign; `smooth_sgn`, `sgn_pair`). -/
theorem r174s_record_writhe_smooth (ρ : Record) (v : ρ.M) :
    (ρ.smooth v).writhe = ρ.writhe - (ρ.sgn v : ℤ) := by
  have h2 := ρ.two_mul_writhe
  -- the retained occurrences: the sum over the smoothing's occurrence set is the filtered sum
  have h1 : 2 * (ρ.smooth v).writhe = ∑ w ∈ Finset.univ.filter (ρ.SmoothKeep v), (ρ.sgn w : ℤ) := by
    rw [Record.two_mul_writhe]
    refine (Fintype.sum_equiv
      (Equiv.refl _ : (ρ.smooth v).M ≃ {w : ρ.M // ρ.SmoothKeep v w}) _
      (fun w => (ρ.sgn w.1 : ℤ)) (fun w => rfl)).trans ?_
    exact (Finset.sum_subtype (Finset.univ.filter (ρ.SmoothKeep v)) (fun w => by simp)
      (fun w => (ρ.sgn w : ℤ))).symm
  -- the two erased occurrences carry the sign of `v`
  have h4 : ∑ w ∈ Finset.univ.filter (fun w => ¬ ρ.SmoothKeep v w), (ρ.sgn w : ℤ) =
      2 * (ρ.sgn v : ℤ) := by
    have hf : Finset.univ.filter (fun w => ¬ ρ.SmoothKeep v w) = {v, ρ.pair v} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Record.SmoothKeep, not_not]
    rw [hf, Finset.sum_pair (ρ.pair_ne v).symm, ρ.sgn_pair]
    ring
  have h5 : ∑ w ∈ Finset.univ.filter (ρ.SmoothKeep v), (ρ.sgn w : ℤ) +
      ∑ w ∈ Finset.univ.filter (fun w => ¬ ρ.SmoothKeep v w), (ρ.sgn w : ℤ) =
      ∑ w, (ρ.sgn w : ℤ) :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (ρ.SmoothKeep v) (fun w => (ρ.sgn w : ℤ))
  omega



/-- A diagram with the record of the smoothing of a one-component diagram has two components
("A self crossing splits one parameter circle into two"; `componentCount_smooth_of_self`). -/
theorem r174s_componentCount_of_smooth_iso (D D₀ : Diagram) (hD : D.componentCount = 1)
    (v : D.Γ.Visit) (h : Nonempty (RecordIso D₀.record (D.record.smooth v))) :
    D₀.componentCount = 2 := by
  obtain ⟨ι⟩ := h
  have h1 : D.record.componentCount = 1 := by rw [D.record_componentCount]; exact hD
  rw [← D₀.record_componentCount, ι.componentCount_eq,
    D.record.componentCount_smooth_of_self v (D.record.r174s_isSelfCrossing h1 v), h1]

/-- Any diagram with the record of the smoothing of `D` at `v` has writhe `w(D) − σ(v)`. -/
theorem r174s_writhe_of_smooth_iso (D D₀ : Diagram) (v : D.Γ.Visit)
    (h : Nonempty (RecordIso D₀.record (D.record.smooth v))) :
    D₀.writhe = D.writhe - (D.sign v.1 : ℤ) := by
  obtain ⟨ι⟩ := h
  rw [← D₀.record_writhe, ι.writhe_eq, r174s_record_writhe_smooth, D.record_writhe, D.record_sgn]

/-- **The knot restriction of a smoothing to an arc circle is the arc-internal crossing record of the
parent** (`restrict_record` → `RecordIso.restrict` along the smoothing clause → `r174s_restrict_smooth_iso`). -/
theorem r174s_knotRestrict_record_iso (D₀ D : Diagram) (hD : D.componentCount = 1) (v : D.Γ.Visit)
    (ι : RecordIso D₀.record (D.record.smooth v)) {a : D.Γ.Visit} (ha : a = v ∨ a = D.record.pair v)
    (i : Fin D₀.Γ.c) (hi : ι.e i = D.record.r174s_arcComp v a) :
    Nonempty (RecordIso (D₀.knotRestrict i).record
      (D.record.restrictCrossings (D.record.r174s_KeepArc a))) := by
  have h1 : D.record.componentCount = 1 := by rw [D.record_componentCount]; exact hD
  have e1 : RecordIso (D₀.knotRestrict i).record (D₀.record.restrict {i}) :=
    D₀.restrictRecordIso {i} (Finset.singleton_nonempty i)
  have e2 : RecordIso (D₀.record.restrict {i})
      ((D.record.smooth v).restrict {D.record.r174s_arcComp v a}) :=
    ι.restrict {i} {D.record.r174s_arcComp v a} (fun c => by
      rw [Finset.mem_singleton, Finset.mem_singleton, ← hi]
      exact ι.e.injective.eq_iff)
  obtain ⟨e3⟩ := D.record.r174s_restrict_smooth_iso h1 (u := v) (a := a) ha
  exact ⟨e1.trans (e2.trans e3)⟩

/-- `gsc_smoothing_split` is symmetric in the two components (`mixedSignSum_comm`). -/
theorem r174s_smoothing_split_swap {D₀ : Diagram} {i j : Fin D₀.Γ.c} {QA QB : R} {ℓ : ℤ}
    (h : gsc_smoothing_split D₀ i j QA QB ℓ) : gsc_smoothing_split D₀ j i QB QA ℓ := by
  obtain ⟨h2, hij, hA, hB, hℓ⟩ := h
  refine ⟨h2, hij.symm, hB, hA, ?_⟩
  unfold CV.IsLinkingNumber at hℓ ⊢
  rw [mixedSignSum_comm]
  exact hℓ

/-- **The smoothing split from the two arc records.**  If `D₀` has the record of the smoothing of the
one-component `D` at `v`, and the arc-internal crossing records of the two arcs of `v` are the records of
the one-component diagrams `K₁`, `K₂`, then `D₀` has two components `i ≠ j` whose knot restrictions have
the polynomials of `K₁`, `K₂` (ax:gausscode), with the linking number `ℓ` and the writhe count
`w(D₀) = w(K₁) + w(K₂) + 2ℓ`. -/
theorem r174s_split_of_arc_isos (D₀ D : Diagram) (hD : D.componentCount = 1) (v : D.Γ.Visit)
    (hι : Nonempty (RecordIso D₀.record (D.record.smooth v)))
    (K₁ K₂ : Diagram) (h₁ : K₁.componentCount = 1) (h₂ : K₂.componentCount = 1)
    (hA : Nonempty (RecordIso (D.record.restrictCrossings (D.record.r174s_KeepArc v)) K₁.record))
    (hB : Nonempty (RecordIso (D.record.restrictCrossings
      (D.record.r174s_KeepArc (D.record.pair v))) K₂.record)) :
    ∃ (i j : Fin D₀.Γ.c) (ℓ : ℤ), gsc_smoothing_split D₀ i j (homfly K₁) (homfly K₂) ℓ ∧
      D₀.writhe = K₁.writhe + K₂.writhe + 2 * ℓ := by
  obtain ⟨ι⟩ := hι
  obtain ⟨κ₁⟩ := hA
  obtain ⟨κ₂⟩ := hB
  have h1 : D.record.componentCount = 1 := by rw [D.record_componentCount]; exact hD
  have h2 : D₀.componentCount = 2 := r174s_componentCount_of_smooth_iso D D₀ hD v ⟨ι⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin D₀.Γ.c, ι.e i = D.record.r174s_arcComp v v :=
    ⟨ι.e.symm _, ι.e.apply_symm_apply _⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin D₀.Γ.c, ι.e j = D.record.r174s_arcComp v (D.record.pair v) :=
    ⟨ι.e.symm _, ι.e.apply_symm_apply _⟩
  have hij : i ≠ j := by
    intro h
    apply D.record.r174s_arcComp_ne h1 v
    rw [← hi, ← hj, h]
  obtain ⟨ε₁⟩ := r174s_knotRestrict_record_iso D₀ D hD v ι (Or.inl rfl) i hi
  obtain ⟨ε₂⟩ := r174s_knotRestrict_record_iso D₀ D hD v ι (Or.inr rfl) j hj
  obtain ⟨ℓ, hℓ⟩ := CV.exists_linkingNumber D₀ i j hij
  refine ⟨i, j, ℓ, ⟨h2, hij, ?_, ?_, hℓ⟩, ?_⟩
  · exact CV.gausscode_polynomial _ _ (D₀.knotRestrict_componentCount i) h₁ (ε₁.trans κ₁)
  · exact CV.gausscode_polynomial _ _ (D₀.knotRestrict_componentCount j) h₂ (ε₂.trans κ₂)
  · rw [r174s_writhe_two_component D₀ i j h2 hij, hℓ.twoLinking_eq,
      ← (D₀.knotRestrict i).record_writhe, (ε₁.trans κ₁).writhe_eq, K₁.record_writhe,
      ← (D₀.knotRestrict j).record_writhe, (ε₂.trans κ₂).writhe_eq, K₂.record_writhe]

/-! ## A. The library smoothing `D₀ := smoothDiagram` at `qx`, with its record clause -/

/-- **The oriented smoothing `D₀` of the ledger** (GSC §3 "let `D_0` be its oriented smoothing"): the
library construction `smoothDiagram` at the crossing `qx` (the `D₀` of `exists_smoothing`,
`exists_smoothing_record_visit`, `exists_smoothing_counts`). -/
def r174s_D₀ (D_H : Diagram) (qx : D_H.Γ.Crossing) : Diagram :=
  Smoothing.smoothDiagram D_H qx (Smoothing.eps D_H qx) (Smoothing.eps_small D_H qx)

theorem r174s_D₀_isOrientedSmoothing (D_H : Diagram) (qx : D_H.Γ.Crossing) :
    IsOrientedSmoothing D_H qx (r174s_D₀ D_H qx) :=
  Smoothing.isOrientedSmoothing_smoothDiagram D_H qx _ (Smoothing.eps_small D_H qx)

/-- The record clause of the library smoothing (`smoothDiagram_record`). -/
theorem r174s_D₀_record (D_H : Diagram) (qx : D_H.Γ.Crossing) :
    Nonempty (RecordIso (r174s_D₀ D_H qx).record (D_H.record.smooth (D_H.overVisit qx))) :=
  Smoothing.smoothDiagram_record D_H qx _ (Smoothing.eps_small D_H qx)

theorem r174s_D₀_componentCount (D_H : Diagram) (hH : D_H.componentCount = 1) (qx : D_H.Γ.Crossing) :
    (r174s_D₀ D_H qx).componentCount = 2 :=
  r174s_componentCount_of_smooth_iso D_H _ hH _ (r174s_D₀_record D_H qx)

/-- The writhe of the smoothing at a positive crossing: `w(D₀) = w(D_H) − 1`. -/
theorem r174s_D₀_writhe (D_H : Diagram) (qx : D_H.Γ.Crossing) (hpos : D_H.IsPositive qx) :
    (r174s_D₀ D_H qx).writhe = D_H.writhe - 1 := by
  rw [r174s_writhe_of_smooth_iso D_H _ _ (r174s_D₀_record D_H qx), D_H.overVisit_fst,
    (D_H.isPositive_iff_sign_eq_one qx).mp hpos]
  rfl

/-- **The smoothing split of `D₀ = r174s_D₀ D_H qx` from an arc-record identification**: if for one of
the two occurrences `u` of `qx` the arc-internal crossing records of the arcs `(u, τ u)`, `(τ u, u)` of
`D_H.record` are the records of the one-component diagrams `K₁`, `K₂`, then `D₀` splits with the
polynomials of `K₁`, `K₂` and `w(D_H) = w(K₁) + w(K₂) + 2ℓ + 1`. -/
theorem r174s_split_of_arc_prop (D_H : Diagram) (hH : D_H.componentCount = 1) (qx : D_H.Γ.Crossing)
    (hpos : D_H.IsPositive qx) (K₁ K₂ : Diagram) (h₁ : K₁.componentCount = 1)
    (h₂ : K₂.componentCount = 1)
    (hsplit : ∃ u : D_H.Γ.Visit, u.1 = qx ∧
      Nonempty (RecordIso (D_H.record.restrictCrossings (D_H.record.r174s_KeepArc u)) K₁.record) ∧
      Nonempty (RecordIso (D_H.record.restrictCrossings
        (D_H.record.r174s_KeepArc (D_H.record.pair u))) K₂.record)) :
    ∃ (i j : Fin (r174s_D₀ D_H qx).Γ.c) (ℓ : ℤ),
      gsc_smoothing_split (r174s_D₀ D_H qx) i j (homfly K₁) (homfly K₂) ℓ ∧
      D_H.writhe = K₁.writhe + K₂.writhe + 2 * ℓ + 1 := by
  obtain ⟨u, hu, hA, hB⟩ := hsplit
  have hrec := r174s_D₀_record D_H qx
  have hw := r174s_D₀_writhe D_H qx hpos
  rcases D_H.visit_eq_over_or_under u with huv | huv
  · rw [hu] at huv
    subst huv
    obtain ⟨i, j, ℓ, hs, hw'⟩ := r174s_split_of_arc_isos (r174s_D₀ D_H qx) D_H hH
      (D_H.overVisit qx) hrec K₁ K₂ h₁ h₂ hA hB
    exact ⟨i, j, ℓ, hs, by omega⟩
  · rw [hu] at huv
    subst huv
    have hp : D_H.record.pair (D_H.overVisit qx) = D_H.underVisit qx := D_H.twin_overVisit qx
    have hpp : D_H.record.pair (D_H.underVisit qx) = D_H.overVisit qx := by
      rw [← hp, D_H.record.pair_invol]
    rw [hpp] at hB
    rw [← hp] at hA
    obtain ⟨i, j, ℓ, hs, hw'⟩ := r174s_split_of_arc_isos (r174s_D₀ D_H qx) D_H hH
      (D_H.overVisit qx) hrec K₂ K₁ h₂ h₁ hB hA
    exact ⟨j, i, ℓ, r174s_smoothing_split_swap hs, by omega⟩

/-! ## D. The ledger fields of row 174: `D₀`, `qx`, `fulltwist`, `i`, `j`, `ℓ`, `smoothing`, `writhe_count` -/

/-- `gsc_fulltwist_of_bigon` with the smoothing pinned to `r174s_D₀` (the same proof: the `D₀` of
`exists_smoothing` IS `r174s_D₀ D_H q`). -/
theorem r174s_fulltwist_triple_of_bigon (D_L D_H : Diagram) (q : D_H.Γ.Crossing) (hq : D_H.IsPositive q)
    (hH : D_H.componentCount = 1) (hL : D_L.componentCount = 1) (B : BigonData (D_H.switch q))
    (hrec : Nonempty (RecordIso B.reducedRecord D_L.record)) :
    gsc_fulltwist_triple D_L D_H (r174s_D₀ D_H q) q := by
  obtain ⟨D', hR, hc, ⟨ι⟩⟩ := exists_rii_deletion _ B
  obtain ⟨κ⟩ := hrec
  exact ⟨hq, r174s_D₀_isOrientedSmoothing D_H q, D', Relation.ReflTransGen.single hR.symm,
    CV.gausscode_polynomial D' D_L (hc.trans hH) hL (ι.trans κ)⟩

section R174SConsumer

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

/-- The positive crossing `a = x'` of `D_H = carrierDiagram q'` — the ledger's `qx`: the lifted `x'`
(`s174_lift`), as in `s174_site` and `s174_fulltwist_of_hrec`. -/
abbrev r174s_qx (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q') :
    (CV.carrierDiagram hn hG' hSm' q').Γ.Crossing :=
  s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx'

/-- **(c′) The `fulltwist` field with `D₀ := r174s_D₀`** — `s174_fulltwist_of_hrec` with the smoothing
named (no existential): from (a) `s174_site` and (b) `s174_hrec_prop`. -/
theorem r174s_fulltwist_of_hrec
    (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (hw' : crossingTransport hs w ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (hrec : s174_hrec_prop hn hG hG' hSm hSm' qAB q' hx' hw') :
    gsc_fulltwist_triple (CV.carrierDiagram hn hG hSm qAB) (CV.carrierDiagram hn hG' hSm' q')
      (r174s_D₀ _ (r174s_qx hn hG' hSm' q' hx')) (r174s_qx hn hG' hSm' q' hx') := by
  obtain ⟨B, -, hB⟩ := s174_site hn hG hG' D hsgn hSm' q' hx' hw'
  have hq : (CV.carrierDiagram hn hG' hSm' q').IsPositive (r174s_qx hn hG' hSm' q' hx') :=
    geoPositiveLift_isPositive hn _ _ q' _
  have hrec' : Nonempty (RecordIso B.reducedRecord (CV.carrierDiagram hn hG hSm qAB).record) := by
    rcases hB with ⟨hy, hz⟩ | ⟨hy, hz⟩
    · rw [s174_reducedRecord_eq B hy hz]; exact hrec
    · rw [s174_reducedRecord_eq_swap B hy hz]; exact hrec
  exact r174s_fulltwist_triple_of_bigon _ _ _ hq rfl rfl B hrec'

/-- **BLACK BOX (consumer obligation — U_R174_REPORT §4 items 1–2 in arc form; STATED, not proved):
the two arcs of `x'` on the `E`-side lift carry the `P-ac` records of `A` and `B`.**  For one of the two
occurrences `u` of `x'` on `D_H = carrierDiagram q'` (`q' = τ qAB`), the crossings of `D_H` internal to
the open arc `(u, τ u)` — the residual crossings of the `A`-string, GSC masks (9a) "a mask-zero survivor
is a residual crossing of the corresponding `P-ac` carrier, a mask-`xw` survivor is a mixed crossing" —
form, with the first-return cyclic order, bits and signs, the record of the `P-ac` lift of `A`
(`carrierDiagram hn hG hSxw qA`), and those internal to the other arc the record of the lift of `B`.
Content: `E = b a A c a B c b C`; the carrier `AB'` of `E-b` reads `x'(ℓ₁) [A] w'(ℓ₂) x'(ℓ₂) [B] w'(ℓ₃)`
(lem:carrierword: on the independent support the carrier inherits the order of `P'`, `arcBetween_iff_key`),
the `P-ac` carriers `A = (m(ℓ₁) [A])`, `B = ([B] m(ℓ₃))` read the same strings on `P` (A7 exactness of the
non-triangle visits, `D.gauss`; `D.sign_eq` for the divide bits; both lifts positive).  Route:
`GT_owner_transport` on good marks for the crossing correspondence, `GT_homfly_wall_gen`-shaped visit
bijections (twin-, key-order- and sign-compatible) → `CV.recordIsoOfData`; estimate 1.5–2.5k lines
(Site_174_REPORT §3 route, steps 2–5, applied to both arcs).  Consumed only as a hypothesis. -/
def r174s_arc_rec_prop (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (qA qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w})) : Prop :=
  ∃ u : (CV.carrierDiagram hn hG' hSm' q').Γ.Visit, u.1 = r174s_qx hn hG' hSm' q' hx' ∧
    Nonempty (RecordIso ((CV.carrierDiagram hn hG' hSm' q').record.restrictCrossings
        ((CV.carrierDiagram hn hG' hSm' q').record.r174s_KeepArc u))
      (CV.carrierDiagram hn hG hSxw qA).record) ∧
    Nonempty (RecordIso ((CV.carrierDiagram hn hG' hSm' q').record.restrictCrossings
        ((CV.carrierDiagram hn hG' hSm' q').record.r174s_KeepArc
          ((CV.carrierDiagram hn hG' hSm' q').record.pair u)))
      (CV.carrierDiagram hn hG hSxw qB).record)

/-- **Items 5–6 of U_R174 §4 on the `GT_Endpoint` configuration**: from the arc-record black box, the
library smoothing `D₀ = r174s_D₀ D_H qx` of `D_H = carrierDiagram q'` at `qx = x'` has two components
`i ≠ j` with `homfly (D₀.knotRestrict i) = Q_A`, `homfly (D₀.knotRestrict j) = Q_B` (the pair-row
grouped polynomials, `GT_groupedPoly_eq_homfly`), the linking number `ℓ`, and the writhe count
`w_H = w_A + w_B + 2ℓ + 1` (all crossings positive: `w(D₀) = w_H − 1 = w_A + w_B + 2ℓ`). -/
theorem r174s_smoothing_split_of_arc (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (qA qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w}))
    (hsplit : r174s_arc_rec_prop hn hG hG' hSxw hSm' q' hx' qA qB) :
    ∃ (i j : Fin (r174s_D₀ (CV.carrierDiagram hn hG' hSm' q') (r174s_qx hn hG' hSm' q' hx')).Γ.c)
      (ℓ : ℤ),
      gsc_smoothing_split (r174s_D₀ (CV.carrierDiagram hn hG' hSm' q') (r174s_qx hn hG' hSm' q' hx'))
        i j (CV.groupedPoly hn hG hSxw qA) (CV.groupedPoly hn hG hSxw qB) ℓ ∧
      CV.groupedWrithe hG' q' = CV.groupedWrithe hG qA + CV.groupedWrithe hG qB + 2 * ℓ + 1 := by
  obtain ⟨i, j, ℓ, hs, hw⟩ := r174s_split_of_arc_prop (CV.carrierDiagram hn hG' hSm' q')
    (gsc_carrierDiagram_componentCount hn hG' hSm' q') (r174s_qx hn hG' hSm' q' hx')
    (geoPositiveLift_isPositive hn _ _ q' _)
    (CV.carrierDiagram hn hG hSxw qA) (CV.carrierDiagram hn hG hSxw qB)
    (gsc_carrierDiagram_componentCount hn hG hSxw qA) (gsc_carrierDiagram_componentCount hn hG hSxw qB)
    hsplit
  refine ⟨i, j, ℓ, ?_, ?_⟩
  · rw [GT_groupedPoly_eq_homfly hn hG hSxw qA, GT_groupedPoly_eq_homfly hn hG hSxw qB]
    exact hs
  · rw [← gsc_carrierDiagram_writhe hn hG' hSm' q', ← gsc_carrierDiagram_writhe hn hG hSxw qA,
      ← gsc_carrierDiagram_writhe hn hG hSxw qB]
    exact hw

/-- **The ledger fields `D₀, qx, fulltwist, i, j, ℓ, smoothing, writhe_count` of `gsc_Ledger`**, from the
site (`s174_site`), the two record black boxes (`s174_hrec_prop`, `r174s_arc_rec_prop`) and the wall count
`writhe_wall` (U_R174 §4 item 2, `w_H = w_L + 2`, a hypothesis here): with `q' := W.τ qAB` these are exactly
the fields, `D₀ := r174s_D₀`, `qx := r174s_qx`; (10) `w_L = w_A + w_B + 2ℓ − 1` is `w_H − 1 = w_A + w_B + 2ℓ`
read through (9). -/
theorem r174s_ledger_fields
    (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (hw' : crossingTransport hs w ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (qA qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w}))
    (hrec : s174_hrec_prop hn hG hG' hSm hSm' qAB q' hx' hw')
    (hsplit : r174s_arc_rec_prop hn hG hG' hSxw hSm' q' hx' qA qB)
    (hwall : CV.groupedWrithe hG' q' = CV.groupedWrithe hG qAB + 2) :
    ∃ (D₀ : Diagram) (qx : (CV.carrierDiagram hn hG' hSm' q').Γ.Crossing) (i j : Fin D₀.Γ.c) (ℓ : ℤ),
      gsc_fulltwist_triple (CV.carrierDiagram hn hG hSm qAB) (CV.carrierDiagram hn hG' hSm' q') D₀ qx ∧
      gsc_smoothing_split D₀ i j (CV.groupedPoly hn hG hSxw qA) (CV.groupedPoly hn hG hSxw qB) ℓ ∧
      CV.groupedWrithe hG qAB = CV.groupedWrithe hG qA + CV.groupedWrithe hG qB + 2 * ℓ - 1 := by
  obtain ⟨i, j, ℓ, hs, hw⟩ := r174s_smoothing_split_of_arc hn hG hG' hSxw hSm' q' hx' qA qB hsplit
  exact ⟨_, _, i, j, ℓ, r174s_fulltwist_of_hrec hn hG hG' D hsgn hSm hSm' qAB q' hx' hw' hrec, hs,
    by omega⟩

end R174SConsumer

/-! ## E. The arc record from visit-level transport data (the `GT_homfly_wall_gen` shape)

The black box `r174s_arc_rec_prop` asks for record isomorphisms; here it is reduced to a VISIT-level
datum: a bijection `ψ` from the retained visits of a carrier `q` (on `P`) onto the retained visits of a
carrier `q'` (on `P'`) lying strictly inside an open arc `(u₀, twin u₀)` of the traversal order of `P'`
together with their twins, compatible with twins, with the cyclic key order and with the divide signs —
exactly the shape of the hypotheses of `GT_homfly_wall_gen` (`GT_owner_transport` output).  Then the
arc-internal crossing record of the lift of `q'` is the record of the lift of `q`
(`r174s_recordIso_of_arcVisitData`): occurrences by `liftVisitEquiv` on both sides, twins by
`liftVisit_twin`, bits by `overBit_eq_true_iff_parent`, signs `+1` on both positive lifts, and the
first-return successor by the uniqueness of the cyclic successor (`cycNext_unique`): no retained
occurrence lies strictly inside a gap (`not_arcBetween_firstReturn`, read through `arcBetween_iff_key`
and `ψ`), and no occurrence lies strictly between a visit and its successor on the lift of `q`
(`record_succ_no_between`, `visitBetween_iff_key`). -/

section R174SArcData

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n}

/-- `v` lies strictly inside the open arc from `u₀` to `twin u₀` in the traversal-key order of `P'`. -/
def r174s_InArc (hP' : CrossingGeometry P') (u₀ v : Visit P') : Prop :=
  cycBetween (geometricVisitKey hP' u₀) (geometricVisitKey hP' v)
    (geometricVisitKey hP' (visitTwin u₀))

variable (hn : 3 ≤ n) (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
  {T : Finset (Crossing P)} {T' : Finset (Crossing P')}
  (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T')
  (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')

/-- **The visit-level transport datum of an arc record.**  `ψ` maps the retained visits of `q` onto the
retained visits of `q'` that lie, with their twins, strictly inside the arc `(u₀, twin u₀)`; it is
compatible with twins, with the cyclic key order and with the divide signs. -/
structure r174s_ArcVisitData (u₀ : Visit P') where
  ψ : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.cg T q} ≃
    {v : Visit P' // v.1 ∈ geoCarrierCrossings hG'.cg T' q' ∧
      (r174s_InArc hG'.cg u₀ v ∧ r174s_InArc hG'.cg u₀ (visitTwin v))}
  twin : ∀ (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q),
    (ψ ⟨visitTwin v, by rw [visitTwin_crossing]; exact hv⟩).1 = visitTwin (ψ ⟨v, hv⟩).1
  cyc : ∀ a b c : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.cg T q},
    cycBetween (geometricVisitKey hG.cg a.1) (geometricVisitKey hG.cg b.1)
      (geometricVisitKey hG.cg c.1) →
    cycBetween (geometricVisitKey hG'.cg (ψ a).1) (geometricVisitKey hG'.cg (ψ b).1)
      (geometricVisitKey hG'.cg (ψ c).1)
  det : ∀ v : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.cg T q},
    (0 < det (edge P v.1.2.val) (edge P (visitTwin v.1).2.val) ↔
      0 < det (edge P' (ψ v).1.2.val) (edge P' (visitTwin (ψ v).1).2.val))

/-- **The arc-internal crossing record of the lift of `q'` is the record of the lift of `q`**, from the
visit-level datum at `u₀ = liftVisit u`. -/
theorem r174s_recordIso_of_arcVisitData (u : (geoPositiveLift hn hG' hT' q').Γ.Visit)
    (A : r174s_ArcVisitData hG hG' q q' (CV.liftVisit hn hG' hT' q' u)) :
    Nonempty (RecordIso ((geoPositiveLift hn hG' hT' q').record.restrictCrossings
        ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u))
      (geoPositiveLift hn hG hT q).record) := by
  have h1 : (geoPositiveLift hn hG' hT' q').record.componentCount = 1 := by
    rw [Diagram.record_componentCount]; exact geoPositiveLift_componentCount hn hG' hT' q'
  have hK1 : (geoPositiveLift hn hG hT q).record.componentCount = 1 := by
    rw [Diagram.record_componentCount]; exact geoPositiveLift_componentCount hn hG hT q
  have hsub : ∀ a b : Fin (geoPositiveLift hn hG hT q).Γ.c, a = b := by
    intro a b
    have hc : (geoPositiveLift hn hG hT q).Γ.c = 1 := geoPositiveLift_componentCount hn hG hT q
    apply Fin.ext
    have := a.2
    have := b.2
    omega
  -- the arc condition, read on the parent visits
  have hkeep : ∀ vh : (geoPositiveLift hn hG' hT' q').Γ.Visit,
      (geoPositiveLift hn hG' hT' q').record.CrossKeep
        ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u) vh ↔
      (r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) (CV.liftVisit hn hG' hT' q' vh) ∧
        r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u)
          (visitTwin (CV.liftVisit hn hG' hT' q' vh))) := by
    intro vh
    rw [Record.r174s_crossKeep_keepArc_iff, CV.arcBetween_iff_key, CV.arcBetween_iff_key,
      Diagram.record_pair_apply, Diagram.record_pair_apply, CV.liftVisit_twin, CV.liftVisit_twin]
    exact Iff.rfl
  -- the codomain of `ψ` is closed under twins
  have hcod : ∀ b : {v : Visit P' // v.1 ∈ geoCarrierCrossings hG'.cg T' q' ∧
      (r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) v ∧
        r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) (visitTwin v))},
      (visitTwin b.1).1 ∈ geoCarrierCrossings hG'.cg T' q' ∧
      (r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) (visitTwin b.1) ∧
        r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) (visitTwin (visitTwin b.1))) := by
    intro b
    refine ⟨by rw [visitTwin_crossing]; exact b.2.1, b.2.2.2, ?_⟩
    rw [visitTwin_involutive]; exact b.2.2.1
  -- `ψ⁻¹` commutes with twins
  have hpsymm : ∀ b : {v : Visit P' // v.1 ∈ geoCarrierCrossings hG'.cg T' q' ∧
      (r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) v ∧
        r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) (visitTwin v))},
      (A.ψ.symm ⟨visitTwin b.1, hcod b⟩).1 = visitTwin (A.ψ.symm b).1 := by
    intro b
    have h := A.twin (A.ψ.symm b).1 (A.ψ.symm b).2
    rw [Equiv.apply_symm_apply] at h
    have h' : A.ψ ⟨visitTwin (A.ψ.symm b).1, by rw [visitTwin_crossing]; exact (A.ψ.symm b).2⟩ =
        ⟨visitTwin b.1, hcod b⟩ := Subtype.ext h
    exact congrArg Subtype.val ((Equiv.symm_apply_eq A.ψ).mpr h'.symm)
  -- the occurrence bijection
  let e₁ : {vh : (geoPositiveLift hn hG' hT' q').Γ.Visit //
      (geoPositiveLift hn hG' hT' q').record.CrossKeep
        ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u) vh} ≃
      {b : {v : Visit P' // v.1 ∈ geoCarrierCrossings hG'.cg T' q'} //
        r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) b.1 ∧
          r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) (visitTwin b.1)} :=
    Equiv.subtypeEquiv (CV.liftVisitEquiv hn hG' hT' q') (fun vh => hkeep vh)
  let e₂ := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun v : Visit P' => v.1 ∈ geoCarrierCrossings hG'.cg T' q')
    (fun v : Visit P' => r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) v ∧
      r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) (visitTwin v))
  let Φ : ((geoPositiveLift hn hG' hT' q').record.restrictCrossings
      ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u)).M ≃
      (geoPositiveLift hn hG hT q).Γ.Visit :=
    e₁.trans (e₂.trans (A.ψ.symm.trans (CV.liftVisitEquiv hn hG hT q).symm))
  have hlv : ∀ vh, CV.liftVisit hn hG hT q (Φ vh) = (A.ψ.symm (e₂ (e₁ vh))).1 :=
    fun vh => CV.liftVisit_symm hn hG hT q _
  have hΦ : ∀ vh, (A.ψ (CV.liftVisitEquiv hn hG hT q (Φ vh))).1 = CV.liftVisit hn hG' hT' q' vh.1 := by
    intro vh
    show (A.ψ (CV.liftVisitEquiv hn hG hT q
      ((CV.liftVisitEquiv hn hG hT q).symm (A.ψ.symm (e₂ (e₁ vh)))))).1 = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  -- assembly
  refine ⟨RecordIso.ofOccOfCard Φ ?_ ?_ ?_ ?_ ?_⟩
  · -- successor: uniqueness of the cyclic successor on the lift of `q`
    intro vh
    have hk : Function.Injective
        (fun z : (geoPositiveLift hn hG hT q).Γ.Visit =>
          geometricVisitKey hG.cg (CV.liftVisit hn hG hT q z)) :=
      (geometricVisitKey_injective hG.cg).comp (CV.liftVisit_injective hn hG hT q)
    have hpk : (geoPositiveLift hn hG' hT' q').record.CrossKeep
        ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u)
        ((geoPositiveLift hn hG' hT' q').record.pair vh.1) :=
      ((geoPositiveLift hn hG' hT' q').record.crossKeep_pair_iff _ _).mpr vh.2
    refine cycNext_unique hk (v := Φ vh) ?_ ?_ ?_ ?_
    · intro h
      have h' := congrArg Subtype.val (Φ.injective h)
      exact (geoPositiveLift hn hG' hT' q').record.firstReturn_val_ne _ h1 vh hpk
        ((geoPositiveLift hn hG' hT' q').record.pair_ne vh.1) h'
    · intro h
      have h' := ((geoPositiveLift hn hG hT q).record_succ_eq_self_iff (Φ vh)).mp h
        ((geoPositiveLift hn hG hT q).twin (Φ vh)) (hsub _ _)
      exact (geoPositiveLift hn hG hT q).twin_ne (Φ vh) h'
    · intro z hz
      have hc := A.cyc (CV.liftVisitEquiv hn hG hT q (Φ vh)) (CV.liftVisitEquiv hn hG hT q z)
        (CV.liftVisitEquiv hn hG hT q
          (Φ (((geoPositiveLift hn hG' hT' q').record.restrictCrossings
            ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u)).succ vh))) hz
      rw [hΦ, hΦ] at hc
      set b := A.ψ (CV.liftVisitEquiv hn hG hT q z) with hb
      let zh : (geoPositiveLift hn hG' hT' q').Γ.Visit :=
        (CV.liftVisitEquiv hn hG' hT' q').symm ⟨b.1, b.2.1⟩
      have hzh : CV.liftVisit hn hG' hT' q' zh = b.1 := CV.liftVisit_symm hn hG' hT' q' _
      have hzk : (geoPositiveLift hn hG' hT' q').record.CrossKeep
          ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u) zh := by
        rw [hkeep, hzh]; exact b.2.2
      have harc : (geoPositiveLift hn hG' hT' q').record.ArcBetween vh.1 zh
          (((geoPositiveLift hn hG' hT' q').record.restrictCrossings
            ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u)).succ vh).1 := by
        rw [CV.arcBetween_iff_key, hzh]; exact hc
      exact (geoPositiveLift hn hG' hT' q').record.not_arcBetween_firstReturn _ h1 vh hzk harc
    · intro z hz
      exact (geoPositiveLift hn hG hT q).record_succ_no_between (Φ vh) z (hsub _ _)
        ((CV.visitBetween_iff_key hn hG hT q _ _ _).mpr hz)
  · -- pairing
    intro vh
    apply CV.liftVisit_injective hn hG hT q
    rw [Diagram.record_pair_apply, CV.liftVisit_twin, hlv, hlv]
    have e : e₂ (e₁ (((geoPositiveLift hn hG' hT' q').record.restrictCrossings
        ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u)).pair vh)) =
        ⟨visitTwin (CV.liftVisit hn hG' hT' q' vh.1), hcod (e₂ (e₁ vh))⟩ :=
      Subtype.ext (CV.liftVisit_twin hn hG' hT' q' vh.1)
    rw [e]
    exact hpsymm (e₂ (e₁ vh))
  · -- bits
    intro vh
    show (geoPositiveLift hn hG hT q).overBit (Φ vh) = (geoPositiveLift hn hG' hT' q').overBit vh.1
    rw [Bool.eq_iff_iff, CV.overBit_eq_true_iff_parent, CV.overBit_eq_true_iff_parent, hlv]
    have h := A.det (A.ψ.symm (e₂ (e₁ vh)))
    rw [Equiv.apply_symm_apply] at h
    exact h
  · -- signs: both lifts are positive
    intro vh
    show (geoPositiveLift hn hG hT q).sign (Φ vh).1 = (geoPositiveLift hn hG' hT' q').sign vh.1.1
    rw [geoPositiveLift_sign, geoPositiveLift_sign]
  · -- circles
    show ((geoPositiveLift hn hG' hT' q').record.restrictCrossings _).componentCount =
      (geoPositiveLift hn hG hT q).record.componentCount
    rw [Record.componentCount_restrictCrossings, h1, hK1]

end R174SArcData

section R174SArcInstance

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {Q : Finset (Crossing P)} {x w m : Crossing P}

/-- **The black box `r174s_arc_rec_prop` from visit-level transport data**: two data `A`, `B`
(`r174s_ArcVisitData`) for the arcs `(u, τ u)` and `(τ u, u)` of an occurrence `u` of `x'` on
`D_H = carrierDiagram q'` — `ψ_A` from the retained visits of the `P-ac` carrier `qA` onto the retained
visits of `AB'` inside the `A`-arc, `ψ_B` likewise for `qB` and the `B`-arc, both twin-, key-order- and
sign-compatible — give the two record isomorphisms.  What remains for the realiser of items 1–2 is exactly
these visit bijections (ownership transport, `GT_owner_transport`; A7 exactness for the key order,
`GT_Endpoint.sign_eq` for the signs). -/
theorem r174s_arc_rec_of_visitData (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (qA qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w}))
    (u : (CV.carrierDiagram hn hG' hSm' q').Γ.Visit) (hu : u.1 = r174s_qx hn hG' hSm' q' hx')
    (A : r174s_ArcVisitData (s174_cg hn hG) (s174_cg hn hG') qA q'
      (CV.liftVisit hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' u))
    (B : r174s_ArcVisitData (s174_cg hn hG) (s174_cg hn hG') qB q'
      (CV.liftVisit hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q'
        ((CV.carrierDiagram hn hG' hSm' q').record.pair u))) :
    r174s_arc_rec_prop hn hG hG' hSxw hSm' q' hx' qA qB :=
  ⟨u, hu,
    r174s_recordIso_of_arcVisitData hn (s174_cg hn hG) (s174_cg hn hG')
      (CV.geoIndependent_of_mem_Ind hG.crossingGeometry hSxw)
      (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') qA q' u A,
    r174s_recordIso_of_arcVisitData hn (s174_cg hn hG) (s174_cg hn hG')
      (CV.geoIndependent_of_mem_Ind hG.crossingGeometry hSxw)
      (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') qB q' _ B⟩

end R174SArcInstance

end

end SM.Link


/-! ## R174 ASSEMBLY (assembler, 2026-09-15): the composition of the five units into `gsc_Ledger`,
`gsc_moves` and the row leaf `RProof.generic_selected`

Everything below is NEW (nothing above changed); names carry the prefix `r174_`.  The five unit
appendices (`r174h_` HREC, `r174c_` CARRIERS, `r174x_` SITEIN, `r174w_` WALL, `r174s_` SMOOTH) are
concatenated verbatim above this block; this block only WIRES them:
* `r174_qC'_eq` — the one glue lemma: CARRIERS' case-defined `r174c_qC'` and WALL's `r174w_qC'` are the
  same carrier of the pair row (both carry a visit of `x` and a visit of `w`; `r174w_qC'_unique`);
* `r174_arc_rec` — the ONE still-open Prop of row 174, `r174s_arc_rec_prop` at the ledger's binding
  (`q' := W.τ (r174c_qAB D)`, `hx' := r174x_hx'_tau`, `qA qB := r174c_qA D, r174c_qB D`);
* `r174_ledger_nonempty` — `gsc_Ledger` on every `GT_Endpoint` configuration from `r174_arc_rec`;
* `r174_arc_rec_moves` / `r174_gsc_moves_of_arc_rec` — `gsc_moves` from the open Prop quantified as
  `gsc_moves` quantifies its configuration;
* `r174_generic_selected_of_arc_rec` — the row leaf in the FIXED signature of `RProof.generic_selected`
  (`gsc_generic_selected_of_moves` at the carrier floor `CV.carrierSlotFloor`). -/

namespace SM.Link

open SM SM.GeoCarrier SM.Carrier RProof

noncomputable section

section R174Compose

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
  (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
  (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
  (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)

include hn hsgn hSxw in
/-- **Glue: the two units' `C'` agree.**  CARRIERS defines `qC'` by the `ℓ₁`-order (`r174c_qC'`: through
`x₁, w₂` when `x` precedes `m` on `ℓ₁`, through `x₂, w₃` otherwise); WALL defines it as the carrier through
the visit of `x` not carried by `A` (`r174w_qC'`) and proves that ANY carrier of the pair row carrying a
visit of `x` and a visit of `w` is that one (`r174w_qC'_unique`). -/
theorem r174_qC'_eq : r174c_qC' D = r174w_qC' hG hG' D := by
  rcases lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D) with h | h
  · exact r174w_qC'_unique hG hG' D (r174c_qC' D) D.x₁ D.w₂ rfl rfl (r174c_qC'_A D h).symm
      (r174c_qC'_w₂_A D hn hSxw hsgn h)
  · exact r174w_qC'_unique hG hG' D (r174c_qC' D) D.x₂ D.w₃ rfl rfl (r174c_qC'_B D h).symm
      (r174c_qC'_w₃_B D hn hSxw hsgn h)

/-- **The ONE still-open Prop of row 174** (SMOOTH's black box `r174s_arc_rec_prop`, U_R174 §4 items 1–2 in
arc form: the two arcs of `x'` on the `E`-side lift of `τ qAB` carry the `P-ac` records of `A` and `B`), at
the ledger's binding: `q' := W.τ (r174c_qAB D)` with `W := gsc_wallData_of_endpoint`, the site input
`hx' := r174x_hx'_tau` (PROVED), `qA := r174c_qA D = L_xw(m₁)`, `qB := r174c_qB D = L_xw(m₃)`.  Reduced by
`r174s_arc_rec_of_visitData` to two visit bijections `ψ_A, ψ_B` (`r174s_ArcVisitData`). -/
abbrev r174_arc_rec : Prop :=
  r174s_arc_rec_prop hn hG hG' hSxw hSm'
    ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ (r174c_qAB D))
    (r174x_hx'_tau hG hG' D hSm hSm' hn) (r174c_qA D) (r174c_qB D)

include hsgn in
/-- **`gsc_Ledger` on a `GT_Endpoint` configuration from the open Prop**: every field of the ledger is
one of the units' theorems —
item 1 (`qC qAB hCAB qC' qA qB hC'A hC'B hAB ρ ρ_AB ρ_C spectator_weight spectator_omega`): CARRIERS;
item 2 (`omega_wall`, `writhe_wall`): WALL Part A; item 3 (`σ hσ weight_C weight_AB carrierR_add`) and
`omega_C`: WALL Part D (through `r174_qC'_eq`); the site inputs `hx' hw'`: SITEIN; `hrec`: HREC;
items 4–6 (`D₀ qx fulltwist i j ℓ smoothing writhe_count`): SMOOTH's `r174s_ledger_fields` from `hrec`,
`writhe_wall` and the open `r174_arc_rec`. -/
theorem r174_ledger_nonempty (hsplit : r174_arc_rec hn hG hG' D hSm hSxw hSm') :
    Nonempty (gsc_Ledger hn hG hG' hs Q m x w hSm hSxw hSm'
      (gsc_wallData_of_endpoint hn hG hG' D hSm hSm')) := by
  have hx' := r174x_hx'_tau hG hG' D hSm hSm' hn
  have hw' := r174x_hw'_tau hG hG' D hSm hSm' hn
  have hrec := r174h_hrec_tau hn hG hG' D hSm hSm' (r174c_qAB D) hx' hw'
  have hwall := r174w_writhe_wall_ledger hn hG hG' D hSm hSm' (r174c_qAB D) (r174c_qAB_x₂ D)
  obtain ⟨D₀, qx, i, j, ℓ, hft, hsp, hwc⟩ :=
    r174s_ledger_fields hn hG hG' D hsgn hSm hSxw hSm' (r174c_qAB D) _ hx' hw' (r174c_qA D) (r174c_qB D)
      hrec hsplit hwall
  have hqC' := r174_qC'_eq hn hG hG' D hsgn hSxw
  exact ⟨{ σ := r174w_sigma hG hG' D
           hσ := r174w_hsigma hG hG' D hsgn
           qC := r174c_qC D
           qAB := r174c_qAB D
           hCAB := r174c_hCAB D hSm
           qC' := r174c_qC' D
           qA := r174c_qA D
           qB := r174c_qB D
           hC'A := r174c_hC'A D hn hSxw
           hC'B := r174c_hC'B D hn hSxw hsgn
           hAB := r174c_hAB D hSxw
           omega_wall := r174w_omega_wall_ledger hn hG hG' D hSm hSm' (r174c_qAB D) (r174c_qAB_x₂ D)
           writhe_wall := hwall
           ρ := r174c_ρ D hn hSm hSxw hsgn
           ρ_AB := r174c_ρ_AB D hn hSm hSxw hsgn
           ρ_C := r174c_ρ_C D hn hSm hSxw hsgn
           spectator_weight := r174c_spectator_weight hn hG D hSm hSxw hsgn
           spectator_omega := r174c_spectator_omega hn hG D hSm hSxw hsgn
           omega_C := by
             rw [hqC']
             exact r174w_omega_C hn hG hG' D hsgn hSm hSxw (r174c_qC D) (r174c_qC_x₁ D).symm
           weight_C := by
             rw [hqC']
             exact r174w_weight_C hn hG hG' D hsgn (r174c_qC D) (r174c_qC_x₁ D).symm
           weight_AB := r174w_weight_AB hn hG hG' D hsgn (r174c_qAB D) (r174c_qAB_x₂ D).symm
             (r174c_qA D) (r174c_qB D) (r174c_qA_m₁ D).symm (r174c_qB_m₃ D).symm
           carrierR_add := r174w_carrierR_add hn hG hG' D hsgn hSm hSxw (r174c_qAB D) (r174c_qAB_x₂ D).symm
             (r174c_qA D) (r174c_qB D) (r174c_qA_m₁ D).symm (r174c_qB_m₃ D).symm
           D₀ := D₀
           qx := qx
           fulltwist := hft
           i := i
           j := j
           ℓ := ℓ
           smoothing := hsp
           writhe_count := hwc }⟩

end R174Compose

section R174Moves

/-- **The open obligation of row 174 at the level of `gsc_moves`**: `r174_arc_rec` on every configuration
`gsc_moves` quantifies over (same binders, same order). -/
def r174_arc_rec_moves : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (e f g : ZMod n) (Q : Finset (Crossing P))
    (x w m : Crossing P) (ℓ₁ ℓ₂ ℓ₃ : ZMod n)
    (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃),
    crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃ →
    ∀ (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
      (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry),
      r174_arc_rec hn hG hG' D hSm hSxw hSm'

/-- **`gsc_moves` from the open Prop** — the composition theorem of row 174: the interface Prop of
RALedgers is realised on every configuration once the arc records of `x'` are identified. -/
theorem r174_gsc_moves_of_arc_rec (harc : r174_arc_rec_moves) : gsc_moves := by
  intro n _ hn P P' hG hG' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃ D hsgn hSm hSxw hSm'
  exact r174_ledger_nonempty hn hG hG' D hsgn hSm hSxw hSm'
    (harc n hn hG hG' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃ D hsgn hSm hSxw hSm')

variable {n : ℕ} [NeZero n]

/-- **Row 174 in the FIXED signature of `RProof.generic_selected`**, from the open Prop: the composition
`gsc_generic_selected_of_moves (r174_gsc_moves_of_arc_rec harc) CV.carrierSlotFloor` the ledger expects
(RALedgers.lean, docstring of `gsc_generic_selected_of_moves`; `CV.carrierSlotFloor =
carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC`).  Once `r174_arc_rec_moves` is proved,
`RProof.generic_selected := r174_generic_selected_of_arc_rec <that proof>`. -/
theorem r174_generic_selected_of_arc_rec (harc : r174_arc_rec_moves)
    (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ :=
  gsc_generic_selected_of_moves (r174_gsc_moves_of_arc_rec harc) CV.carrierSlotFloor hn E e f g
    h3 h4e h4f h4g hE

end R174Moves

/-! ## R174 ARCV (Route V — visit data; prover, 2026-09-15): `ψ_A`, `ψ_B` and the proof of the open Prop
`r174_arc_rec_moves`

Everything below is NEW (nothing above changed); names carry the prefix `r174v_`.
* **V0** — `GeometricInterlaces` read on visit keys (`r174v_interlaces_keys`, `r174v_not_both_inArc`): both
  visits of `y` cannot lie in one open arc `(a, twin a)` of a visit `a` of a crossing `x` interlacing `y`.
* **V1** — the pair-row arcs on `P`, from WALL's `r174w_split_x` / `r174w_unaffected_w` / `r174w_part_x` and
  the orientation record `r174w_Split` (`xA` = the visit of `x` carried by `A`): `A` is the child of the
  `x`-split untouched by the `w`-split (`r174v_xA_not_w`), so `A ∖ {xA}` lies strictly inside `(twin xA, xA)`
  (`r174v_arcA_of_owner`) and `B` strictly inside `(xA, twin xA)` (`r174v_arcB_of_owner`), on the mark keys.
* **V2** — across the wall: `r174v_cyc_transport` (`𝑾.key_lt` on the three pairs of an `x`-arc test, none
  reversed), `r174v_retained_qAB_of_xw` (`retained_xw(q₀) ⊆ retained_m(AB)` via `r174c_owner_qAB_iff`), the
  generic arc datum `r174v_arcData` (`ψ := visitTransport hs` restricted; inverse through
  `r174h_retained_of_mem_q` and the arc characterisation; `x'` excluded by strictness of the arc, `w'` by
  `D.compl` through V0; twins by `visitTransport_visitTwin`, key order by `r174h_cyc`, bits by
  `GT_Endpoint.sign_eq`), and its two instances `r174v_dataA` (`qA`, arc `(τ (twin xA), τ xA)`) and
  `r174v_dataB` (`qB`, arc `(τ xA, τ (twin xA))`).
* **V3** — the occurrence `u` of `x'` at the parent visit `τ (twin xA)`, `r174v_arc_rec_at` (at a variable `q'`
  with `hq'`, HREC pitfall 1), **`r174v_arc_rec_moves_proof : r174_arc_rec_moves`**, and the closed row:
  `r174v_gsc_moves : gsc_moves`, `r174v_generic_selected` (the FIXED signature of `RProof.generic_selected`). -/

/-! ### V0. Interlacing on the visit keys -/

section R174VCyc

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

omit [NeZero n] in
/-- `GeometricInterlaces` on the visit keys: a visit `a` of `x` and visits `b₀, b₁` of `y` with
`b₀ ∈ (a, twin a)` and `b₁ ∈ (twin a, a)`. -/
theorem r174v_interlaces_keys (hP : CrossingGeometry P) {x y : Crossing P}
    (h : GeometricInterlaces hP x y) :
    ∃ a b₀ b₁ : Visit P, a.1 = x ∧ b₀.1 = y ∧ b₁.1 = y ∧
      cycBetween (geometricVisitKey hP a) (geometricVisitKey hP b₀)
        (geometricVisitKey hP (visitTwin a)) ∧
      cycBetween (geometricVisitKey hP (visitTwin a)) (geometricVisitKey hP b₁)
        (geometricVisitKey hP a) := by
  obtain ⟨-, x₀, x₁, y₀, y₁, hx, -, h₀, h₁⟩ := h
  have hx1 : (⟨x, x₁⟩ : Visit P) = visitTwin ⟨x, x₀⟩ := by
    rcases visit_eq_or_twin ⟨x, x₀⟩ ⟨x, x₁⟩ rfl with h | h
    · have h' : x₁ = x₀ := Subtype.ext (congrArg (fun v : Visit P => v.2.val) h)
      exact absurd h'.symm hx
    · exact h
  refine ⟨⟨x, x₀⟩, ⟨y, y₀⟩, ⟨y, y₁⟩, rfl, rfl, rfl, ?_, ?_⟩
  · rw [← hx1]
    exact (traversalBetween_iff_cycBetween _ _ _).mp h₀
  · rw [← hx1]
    exact (traversalBetween_iff_cycBetween _ _ _).mp h₁

omit [NeZero n] in
/-- Both visits of `y` inside one open arc `(a, twin a)` of a visit `a` of `x` contradicts `x, y`
interlacing. -/
theorem r174v_not_both_inArc (hP : CrossingGeometry P) {x y : Crossing P}
    (h : GeometricInterlaces hP x y) (a : Visit P) (ha : a.1 = x)
    (hall : ∀ b : Visit P, b.1 = y →
      cycBetween (geometricVisitKey hP a) (geometricVisitKey hP b)
        (geometricVisitKey hP (visitTwin a))) :
    False := by
  obtain ⟨a', b₀, b₁, ha', hb₀, hb₁, h₀, h₁⟩ := r174v_interlaces_keys hP h
  rcases visit_eq_or_twin a a' (ha'.trans ha.symm) with h2 | h2
  · rw [h2] at h₁
    exact cycBetween_asymm' (hall b₁ hb₁) h₁
  · rw [h2, visitTwin_involutive] at h₀
    exact cycBetween_asymm' (hall b₀ hb₀) h₀

end R174VCyc

/-! ### V1. The pair-row arcs on `P` -/

section R174VArcP

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃) (sp : r174w_Split D)

-- the instance hygiene of WALL Part C (R174_WALL_REPORT §6.2): its `insert` terms use `r174w_decEqCrossing`
attribute [local instance] Classical.propDecidable
attribute [local instance high] r174w_decEqCrossing

/-- `A` is the child of the `x`-split not touched by the `w`-split: `xA` is not on the `Q ∪ {x}`-carrier of
`w₂` (else `xA` would land on `L_xw w₂` or `L_xw w₃`, i.e. on `B` or `C'`). -/
theorem r174v_xA_not_w :
    geoOwner hP (insert x Q) (Sum.inr sp.xA) ≠ geoOwner hP (insert x Q) (Sum.inr D.w₂) := by
  intro h
  have hA := sp.oA
  have hB := sp.oB
  have hC' := sp.oC'
  have hAB := r174w_sep_m_Sxw D
  have hxx := r174w_sep_x_Sxw D
  rcases r174w_part_w D (Sum.inr sp.xA) h with h2 | h2
  · rcases sp.hcase with ⟨hxA, hwB, -⟩ | ⟨hxA, hwB, -⟩
    · rw [hxA, hwB, D.twin_w₃, D.twin_x₂] at hC'
      rw [hxA] at h2
      exact hxx (hC'.trans h2.symm)
    · rw [hxA] at h2 hA
      rw [hwB] at hB
      exact hAB (hA.symm.trans (h2.trans hB))
  · rcases sp.hcase with ⟨hxA, hwB, -⟩ | ⟨hxA, hwB, -⟩
    · rw [hxA] at h2 hA
      rw [hwB] at hB
      exact hAB (hA.symm.trans (h2.trans hB))
    · rw [hxA, hwB, D.twin_w₂, D.twin_x₁] at hC'
      rw [hxA] at h2
      exact hxx (h2.trans hC'.symm)

/-- **The `A`-arc on `P`**: a mark of `A = L_xw(m₁)` other than `xA` lies strictly inside `(twin xA, xA)`. -/
theorem r174v_arcA_of_owner (T : Finset (Crossing P)) (hT : T = insert w (insert x Q))
    (z : Mark P) (hz : z ≠ Sum.inr sp.xA)
    (h : geoOwner hP T z = geoOwner hP T (Sum.inr D.m₁)) :
    cycBetween (geoMarkKey hP (Sum.inr (visitTwin sp.xA))) (geoMarkKey hP z)
      (geoMarkKey hP (Sum.inr sp.xA)) := by
  subst hT
  have h1 : geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr sp.xA) :=
    (r174w_unaffected_w D (Sum.inr sp.xA) (r174v_xA_not_w D sp) z).mp (h.trans sp.oA.symm)
  rcases sp.hcase with ⟨hxA, -, -⟩ | ⟨hxA, -, -⟩
  · rw [hxA] at h1 hz ⊢
    rw [D.twin_x₂]
    rcases ((r174w_split_x D).2 z).mp h1 with h' | h'
    · exact absurd h' hz
    · exact h'.1
  · rw [hxA] at h1 hz ⊢
    rw [D.twin_x₁]
    rcases ((r174w_split_x D).1 z).mp h1 with h' | h'
    · exact absurd h' hz
    · exact h'.1

/-- **The `B`-arc on `P`**: a mark of `B = L_xw(m₃)` other than `twin xA` lies strictly inside
`(xA, twin xA)`. -/
theorem r174v_arcB_of_owner (T : Finset (Crossing P)) (hT : T = insert w (insert x Q))
    (z : Mark P) (hz : z ≠ Sum.inr (visitTwin sp.xA))
    (h : geoOwner hP T z = geoOwner hP T (Sum.inr D.m₃)) :
    cycBetween (geoMarkKey hP (Sum.inr sp.xA)) (geoMarkKey hP z)
      (geoMarkKey hP (Sum.inr (visitTwin sp.xA))) := by
  subst hT
  have hQ : geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁) := sp.onZ_B z h
  have hne : geoOwner hP (insert x Q) z ≠ geoOwner hP (insert x Q) (Sum.inr sp.xA) := by
    intro h1
    have h2 := (r174w_unaffected_w D (Sum.inr sp.xA) (r174v_xA_not_w D sp) z).mpr h1
    rw [sp.oA] at h2
    exact r174w_sep_m_Sxw D (h2.symm.trans h)
  rcases sp.hcase with ⟨hxA, -, -⟩ | ⟨hxA, -, -⟩
  · rw [hxA] at hne hz ⊢
    rw [D.twin_x₂] at hz ⊢
    rcases r174w_part_x D z hQ with h1 | h1
    · rcases ((r174w_split_x D).1 z).mp h1 with h' | h'
      · exact absurd h' hz
      · exact h'.1
    · exact absurd h1 hne
  · rw [hxA] at hne hz ⊢
    rw [D.twin_x₁] at hz ⊢
    rcases r174w_part_x D z hQ with h1 | h1
    · exact absurd h1 hne
    · rcases ((r174w_split_x D).2 z).mp h1 with h' | h'
      · exact absurd h' hz
      · exact h'.1

end R174VArcP

/-! ### V2. Across the wall: transport, the retained-crossing inclusion, the generic arc datum -/

section R174VData

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
  (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
  (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)

include hn hG hG' D hSm hSm'

set_option linter.unusedSectionVars false

/-- A visit of a crossing outside the triangle is a non-local mark. -/
theorem r174v_nonLocal_of_not_tri {v : Visit P} (hv : v.1.val ∉ triangleSupports e f g) :
    r174c_NonLocal (x := x) (w := w) (m := m) (Sum.inr v) := by
  intro v' hv'
  obtain rfl := Sum.inr.inj hv'
  exact ⟨fun h => hv (by rw [h]; exact D.xT), fun h => hv (by rw [h]; exact D.wT),
    fun h => hv (by rw [h]; exact D.mT)⟩

/-- **Transport of an arc test across the wall**: for any visit `a` and a visit `v` of a crossing outside the
triangle, `v ∈ (a, twin a)` on `P` iff `τ v ∈ (τ a, τ (twin a))` on `P'` — `𝑾.key_lt` on the three pairs:
`(a, v)` and `(v, twin a)` have a non-triangle member, `(twin a, a)` lie on different edges. -/
theorem r174v_cyc_transport {a v : Visit P} (hv : v.1.val ∉ triangleSupports e f g) :
    cycBetween (geometricVisitKey hG.crossingGeometry a) (geometricVisitKey hG.crossingGeometry v)
        (geometricVisitKey hG.crossingGeometry (visitTwin a)) ↔
      cycBetween (geometricVisitKey hG'.crossingGeometry (visitTransport hs a))
        (geometricVisitKey hG'.crossingGeometry (visitTransport hs v))
        (geometricVisitKey hG'.crossingGeometry (visitTransport hs (visitTwin a))) := by
  have hvT : v.1 ∉ triangleCrossings P e f g :=
    fun h => hv ((F1.mem_triangleCrossings e f g v.1).mp h)
  exact GT_cyc_congr_of_lt
    ((gsc_wall_of_endpoint hG hG' D hSm hSm').key_lt a v (GT_not_rev_of_not_mem_right hvT))
    ((gsc_wall_of_endpoint hG hG' D hSm hSm').key_lt v (visitTwin a) (GT_not_rev_of_not_mem_left hvT))
    ((gsc_wall_of_endpoint hG hG' D hSm hSm').key_lt (visitTwin a) a
      (GT_not_rev_of_edge_ne (visitTwin_edge_ne a)))

/-- `retained_xw(q₀) ⊆ retained_m(AB)` for a pair-row carrier `q₀` not retaining `m` whose non-local visits
are visits of `AB`. -/
theorem r174v_retained_qAB_of_xw {q₀ : GeoComponent hG.crossingGeometry (Q ∪ {x, w})}
    (hm : m ∉ geoCarrierCrossings hG.crossingGeometry (Q ∪ {x, w}) q₀)
    (hown : ∀ v : Visit P, r174c_NonLocal (x := x) (w := w) (m := m) (Sum.inr v) →
      geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr v) = q₀ →
      geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr v) = r174c_qAB D)
    {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {x, w}) q₀) :
    c ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) (r174c_qAB D) := by
  rw [mem_geoCarrierCrossings] at hc hm ⊢
  have hcm : c ≠ m := fun h => hm (h ▸ hc)
  have hcS := hc.1
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hcS
  obtain ⟨hcQ, hcx, hcw⟩ := hcS
  refine ⟨?_, fun v hv => ?_⟩
  · simp only [Finset.mem_union, Finset.mem_singleton, not_or]
    exact ⟨hcQ, hcm⟩
  · refine hown v ?_ (hc.2 v hv)
    intro v' hv'
    obtain rfl := Sum.inr.inj hv'
    rw [hv]
    exact ⟨hcx, hcw, hcm⟩

section R174VArcData

variable (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
  (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
  (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
  (hq' : q' = GT_carrierEquiv (gsc_wall_of_endpoint hG hG' D hSm hSm') (r174c_qAB D))
  (hx' : crossingTransport hs x ∈
    geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
  (hw' : crossingTransport hs w ∈
    geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')

include hsgn hSxw q' hq' hx' hw'

/-- **The generic arc datum**: `ψ := visitTransport hs` restricted to the retained visits of a pair-row carrier
`q₀`, onto the retained visits of `q' = τ AB` lying with their twins strictly inside `(τ a, τ (twin a))`, for a
visit `a` of `x`.  Hypotheses: `m` is not retained by `q₀`; non-local visits of `q₀` are visits of `AB`
(`hown`); the non-local visits of `q₀` lie in `(a, twin a)` (`H1`); a non-local visit of `AB` in `(a, twin a)`
is a visit of `q₀` (`H2`). -/
noncomputable def r174v_arcData (q₀ : GeoComponent hG.crossingGeometry (Q ∪ {x, w}))
    (hm : m ∉ geoCarrierCrossings hG.crossingGeometry (Q ∪ {x, w}) q₀)
    (hown : ∀ v : Visit P, r174c_NonLocal (x := x) (w := w) (m := m) (Sum.inr v) →
      geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr v) = q₀ →
      geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr v) = r174c_qAB D)
    (a : Visit P) (ha : a.1 = x)
    (H1 : ∀ v : Visit P, v.1.val ∉ triangleSupports e f g →
      geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr v) = q₀ →
      cycBetween (geometricVisitKey hG.crossingGeometry a) (geometricVisitKey hG.crossingGeometry v)
        (geometricVisitKey hG.crossingGeometry (visitTwin a)))
    (H2 : ∀ v : Visit P, v.1.val ∉ triangleSupports e f g →
      geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr v) = r174c_qAB D →
      cycBetween (geometricVisitKey hG.crossingGeometry a) (geometricVisitKey hG.crossingGeometry v)
        (geometricVisitKey hG.crossingGeometry (visitTwin a)) →
      geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr v) = q₀)
    (u₀ : Visit P') (hu₀ : u₀ = visitTransport hs a) :
    r174s_ArcVisitData (s174_cg hn hG) (s174_cg hn hG') q₀ q' u₀ := by
  subst hu₀
  have hT : ∀ {c : Crossing P}, c ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) (r174c_qAB D) →
      c.val ∉ triangleSupports e f g :=
    fun hc => r174h_not_tri_of_retained hG hG' D hSm (r174c_qAB D) hc
  have hL1 : ∀ {c : Crossing P}, c ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {x, w}) q₀ →
      c ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) (r174c_qAB D) :=
    fun hc => r174v_retained_qAB_of_xw hn hG hG' D hSm hSm' hm hown hc
  -- forward membership: a retained visit of `q₀` goes to a retained visit of `q'` inside the arc, with its twin
  have hfwd : ∀ v : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {x, w}) q₀},
      (visitTransport hs v.1).1 ∈
          geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q' ∧
        (r174s_InArc hG'.crossingGeometry (visitTransport hs a) (visitTransport hs v.1) ∧
          r174s_InArc hG'.crossingGeometry (visitTransport hs a) (visitTwin (visitTransport hs v.1))) := by
    intro v
    have hc := hL1 v.2
    have hv1 : v.1.1.val ∉ triangleSupports e f g := hT hc
    have hv2 : (visitTwin v.1).1.val ∉ triangleSupports e f g := by
      rw [visitTwin_crossing]; exact hv1
    have hown1 := ((mem_geoCarrierCrossings _ _ _ _).mp v.2).2
    refine ⟨?_, ?_, ?_⟩
    · rw [visitTransport_crossing]
      exact r174h_mem_retained_q hn hG hG' D hSm hSm' (r174c_qAB D) q' hq' hx' hw' hc
    · unfold r174s_InArc
      rw [← visitTransport_visitTwin]
      exact (r174v_cyc_transport hn hG hG' D hSm hSm' hv1).mp (H1 v.1 hv1 (hown1 v.1 rfl))
    · unfold r174s_InArc
      rw [← visitTransport_visitTwin, ← visitTransport_visitTwin]
      exact (r174v_cyc_transport hn hG hG' D hSm hSm' hv2).mp
        (H1 (visitTwin v.1) hv2 (hown1 (visitTwin v.1) (visitTwin_crossing _)))
  -- backward membership: a retained visit of `q'` inside the arc with its twin comes from a retained visit of `q₀`
  have hbwd : ∀ v' : {v : Visit P' //
      v.1 ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q' ∧
        (r174s_InArc hG'.crossingGeometry (visitTransport hs a) v ∧
          r174s_InArc hG'.crossingGeometry (visitTransport hs a) (visitTwin v))},
      ((visitTransport hs).symm v'.1).1 ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {x, w}) q₀ := by
    rintro ⟨v', hmem, hin, hin'⟩
    obtain ⟨v, rfl⟩ := (visitTransport hs).surjective v'
    show ((visitTransport hs).symm (visitTransport hs v)).1 ∈ _
    rw [Equiv.symm_apply_apply]
    -- every visit of the crossing of `τ v` lies in the arc
    have hall : ∀ b : Visit P', b.1 = (visitTransport hs v).1 →
        r174s_InArc hG'.crossingGeometry (visitTransport hs a) b := by
      intro b hb
      rcases visit_eq_or_twin (visitTransport hs v) b hb with h | h
      · rw [h]; exact hin
      · rw [h]; exact hin'
    -- not `x'`: the arc is open at `τ a` and `τ (twin a)`
    have hvx : v.1 ≠ x := by
      intro h
      rcases visit_eq_or_twin a v (h.trans ha.symm) with h2 | h2
      · rw [h2] at hin
        unfold r174s_InArc at hin
        exact r174w_cyc_ne_left hin rfl
      · rw [h2, visitTransport_visitTwin] at hin
        unfold r174s_InArc at hin
        exact r174w_cyc_ne_right hin rfl
    -- not `w'`: `x'` and `w'` interlace on `P'` (`D.compl`), so `w'` has a visit on each side
    have hvw : v.1 ≠ w := by
      intro h
      have hint : GeometricInterlaces hG'.crossingGeometry (crossingTransport hs x)
          (crossingTransport hs w) :=
        (D.compl x w D.xT D.wT D.xw).mpr D.hxw
      refine r174v_not_both_inArc hG'.crossingGeometry hint (visitTransport hs a)
        (by rw [visitTransport_crossing, ha]) (fun b hb => hall b ?_)
      rw [hb, visitTransport_crossing, h]
    -- hence a retained crossing of `AB`
    have hcAB : v.1 ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) (r174c_qAB D) := by
      have hx1 : (visitTransport hs v).1 ≠ crossingTransport hs x := by
        rw [visitTransport_crossing]
        exact fun h => hvx ((crossingTransport hs).injective h)
      have hw1 : (visitTransport hs v).1 ≠ crossingTransport hs w := by
        rw [visitTransport_crossing]
        exact fun h => hvw ((crossingTransport hs).injective h)
      have h := r174h_retained_of_mem_q hn hG hG' D hSm hSm' (r174c_qAB D) q' hq' hx' hw' hmem hx1 hw1
      rwa [visitTransport_crossing, Equiv.symm_apply_apply] at h
    have hvT : v.1.val ∉ triangleSupports e f g := hT hcAB
    rw [mem_geoCarrierCrossings] at hcAB ⊢
    refine ⟨?_, fun b hb => ?_⟩
    · have h1 : v.1 ∉ Q := fun h => hcAB.1 (Finset.mem_union_left _ h)
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1, hvx, hvw⟩
    · have hbT : b.1.val ∉ triangleSupports e f g := by rw [hb]; exact hvT
      refine H2 b hbT (hcAB.2 b hb) ?_
      rw [r174v_cyc_transport hn hG hG' D hSm hSm' hbT]
      have h := hall (visitTransport hs b)
        (by rw [visitTransport_crossing, visitTransport_crossing, hb])
      unfold r174s_InArc at h
      rwa [← visitTransport_visitTwin] at h
  exact
    { ψ :=
        { toFun := fun v => ⟨visitTransport hs v.1, hfwd v⟩
          invFun := fun v' => ⟨(visitTransport hs).symm v'.1, hbwd v'⟩
          left_inv := fun v => Subtype.ext (Equiv.symm_apply_apply _ _)
          right_inv := fun v' => Subtype.ext (Equiv.apply_symm_apply _ _) }
      twin := fun v hv => visitTransport_visitTwin hs v
      cyc := fun a₁ b₁ c₁ h =>
        (r174h_cyc hG hG' D hSm hSm' (r174c_qAB D) (hL1 a₁.2) (hL1 b₁.2) (hL1 c₁.2)).mp h
      det := fun v => by
        show 0 < det (edge P v.1.2.val) (edge P (visitTwin v.1).2.val) ↔
          0 < det (edge P' (visitTransport hs v.1).2.val)
            (edge P' (visitTwin (visitTransport hs v.1)).2.val)
        rw [← visitTransport_visitTwin, visitTransport_edge, visitTransport_edge]
        exact GT_det_pos_iff_of_sign (D.sign_eq _ _ (by
          rw [← visit_crossing_val_eq_pair]; exact v.1.1.property)) }

/-- **`ψ_A`**: the datum for `qA = L_xw(m₁)` on the arc `(τ (twin xA), τ xA)`. -/
noncomputable def r174v_dataA (sp : r174w_Split D) (u₀ : Visit P')
    (hu₀ : u₀ = visitTransport hs (visitTwin sp.xA)) :
    r174s_ArcVisitData (s174_cg hn hG) (s174_cg hn hG') (r174c_qA D) q' u₀ :=
  r174v_arcData hn hG hG' D hSm hSm' q' hq' hx' hw' (r174c_qA D)
    (fun h => r174c_hAB D hSxw (((mem_geoCarrierCrossings _ _ _ _).mp h).2 D.m₃ rfl).symm)
    (fun _ hnl h => (r174c_owner_qAB_iff D hn hSm hSxw hsgn hnl).mpr (Or.inl h))
    (visitTwin sp.xA) (by rw [visitTwin_crossing, sp.hxA])
    (fun v hvT h => by
      have hz : (Sum.inr v : Mark P) ≠ Sum.inr sp.xA := fun h' => by
        apply hvT; rw [Sum.inr.inj h', sp.hxA]; exact D.xT
      have h1 := r174v_arcA_of_owner D sp (Q ∪ {x, w}) (by
        ext c; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto)
        (Sum.inr v) hz h
      simp only [geoMarkKey_visit] at h1
      rw [visitTwin_involutive]
      exact h1)
    (fun v hvT hAB hcyc => by
      rcases (r174c_owner_qAB_iff D hn hSm hSxw hsgn
        (r174v_nonLocal_of_not_tri hn hG hG' D hSm hSm' hvT)).mp hAB with h | h
      · exact h
      · exfalso
        have hz : (Sum.inr v : Mark P) ≠ Sum.inr (visitTwin sp.xA) := fun h' => by
          apply hvT; rw [Sum.inr.inj h', visitTwin_crossing, sp.hxA]; exact D.xT
        have h1 := r174v_arcB_of_owner D sp (Q ∪ {x, w}) (by
          ext c; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto)
          (Sum.inr v) hz h
        simp only [geoMarkKey_visit] at h1
        rw [visitTwin_involutive] at hcyc
        exact r174w_cyc_asymm hcyc h1)
    u₀ hu₀

/-- **`ψ_B`**: the datum for `qB = L_xw(m₃)` on the arc `(τ xA, τ (twin xA))`. -/
noncomputable def r174v_dataB (sp : r174w_Split D) (u₀ : Visit P')
    (hu₀ : u₀ = visitTransport hs sp.xA) :
    r174s_ArcVisitData (s174_cg hn hG) (s174_cg hn hG') (r174c_qB D) q' u₀ :=
  r174v_arcData hn hG hG' D hSm hSm' q' hq' hx' hw' (r174c_qB D)
    (fun h => r174c_hAB D hSxw (((mem_geoCarrierCrossings _ _ _ _).mp h).2 D.m₁ rfl))
    (fun _ hnl h => (r174c_owner_qAB_iff D hn hSm hSxw hsgn hnl).mpr (Or.inr h))
    sp.xA sp.hxA
    (fun v hvT h => by
      have hz : (Sum.inr v : Mark P) ≠ Sum.inr (visitTwin sp.xA) := fun h' => by
        apply hvT; rw [Sum.inr.inj h', visitTwin_crossing, sp.hxA]; exact D.xT
      exact r174v_arcB_of_owner D sp (Q ∪ {x, w}) (by
        ext c; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto)
        (Sum.inr v) hz h)
    (fun v hvT hAB hcyc => by
      rcases (r174c_owner_qAB_iff D hn hSm hSxw hsgn
        (r174v_nonLocal_of_not_tri hn hG hG' D hSm hSm' hvT)).mp hAB with h | h
      · exfalso
        have hz : (Sum.inr v : Mark P) ≠ Sum.inr sp.xA := fun h' => by
          apply hvT; rw [Sum.inr.inj h', sp.hxA]; exact D.xT
        exact r174w_cyc_asymm (r174v_arcA_of_owner D sp (Q ∪ {x, w}) (by
          ext c; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto)
          (Sum.inr v) hz h) hcyc
      · exact h)
    u₀ hu₀

/-! ### V3. The occurrence `u` of `x'` and the open Prop -/

/-- **The open Prop at a variable `q'` with `hq'`** (HREC pitfall 1): the occurrence `u` of `x'` on `D_H` at
the parent visit `τ (twin xA)`, `ψ_A` on the arc `(u, τ u)` and `ψ_B` on `(τ u, u)`. -/
theorem r174v_arc_rec_at (sp : r174w_Split D) :
    r174s_arc_rec_prop hn hG hG' hSxw hSm' q' hx' (r174c_qA D) (r174c_qB D) := by
  have hmem : (visitTransport hs (visitTwin sp.xA)).1 ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q' := by
    rw [visitTransport_crossing, visitTwin_crossing, sp.hxA]; exact hx'
  let u : (CV.carrierDiagram hn hG' hSm' q').Γ.Visit :=
    (CV.liftVisitEquiv hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm')
      q').symm ⟨visitTransport hs (visitTwin sp.xA), hmem⟩
  have hu1 : CV.liftVisit hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm')
      q' u = visitTransport hs (visitTwin sp.xA) :=
    CV.liftVisit_symm hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _
  have hu : u.1 = r174s_qx hn hG' hSm' q' hx' :=
    (r174h_lift_eq_iff hn hG hG' D hSm hSm' (r174c_qAB D) q' hq' hx' hw' u hx').mpr
      (by rw [hu1, visitTransport_crossing, visitTwin_crossing, sp.hxA])
  have hu2 : CV.liftVisit hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm')
      q' ((CV.carrierDiagram hn hG' hSm' q').record.pair u) = visitTransport hs sp.xA := by
    rw [Diagram.record_pair_apply, CV.liftVisit_twin, hu1, ← visitTransport_visitTwin,
      visitTwin_involutive]
  exact r174s_arc_rec_of_visitData hn hG hG' hSxw hSm' q' hx' (r174c_qA D) (r174c_qB D) u hu
    (r174v_dataA hn hG hG' D hSm hSm' hsgn hSxw q' hq' hx' hw' sp _ hu1)
    (r174v_dataB hn hG hG' D hSm hSm' hsgn hSxw q' hq' hx' hw' sp _ hu2)

end R174VArcData

end R174VData

section R174VMoves

/-- **The open Prop of row 174 is PROVED**: `r174_arc_rec_moves`, the hypothesis of
`r174_gsc_moves_of_arc_rec` and `r174_generic_selected_of_arc_rec` — at the ledger's binding
`q' := W.τ (r174c_qAB D)` (`hq' := rfl`), the site inputs `r174x_hx'_tau`, `r174x_hw'_tau` and the orientation
record `r174w_sp`. -/
theorem r174v_arc_rec_moves_proof : r174_arc_rec_moves := by
  intro n _ hn P P' hG hG' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃ D hsgn hSm hSxw hSm'
  exact r174v_arc_rec_at hn hG hG' D hSm hSm' hsgn hSxw _ rfl
    (r174x_hx'_tau hG hG' D hSm hSm' hn) (r174x_hw'_tau hG hG' D hSm hSm' hn) (r174w_sp hG hG' D)

/-- **Row 174 closed: `gsc_moves`** (the interface Prop of RALedgers). -/
theorem r174v_gsc_moves : gsc_moves := r174_gsc_moves_of_arc_rec r174v_arc_rec_moves_proof

variable {n : ℕ} [NeZero n]

/-- **Row 174 closed in the FIXED signature of `RProof.generic_selected`**
(`gsc_generic_selected_of_moves r174v_gsc_moves CV.carrierSlotFloor`). -/
theorem r174v_generic_selected (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ :=
  r174_generic_selected_of_arc_rec r174v_arc_rec_moves_proof hn E e f g h3 h4e h4f h4g hE

end R174VMoves

end

end SM.Link
