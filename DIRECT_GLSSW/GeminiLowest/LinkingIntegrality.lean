import GeminiLowest.ComponentExtraction

set_option autoImplicit false
noncomputable section

namespace GeminiLowest

open DirectGLSSW
open DirectGLSSW.PermutationOrbits
open DirectGLSSW.HOMFLY
open DirectGLSSW.HOMFLY.Coefficients
open DirectGLSSW.HOMFLY.Gemini
open DirectGLSSW.HOMFLY.LowestRowContract
open scoped BigOperators

attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : Fintype (diagramComponent D) :=
  PermutationOrbits.componentFintype D.continuation

theorem fin2_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  fin_cases b <;> simp

/-! ### Part 1: Pair Crossings, Over-Pair Crossings, and `overWrithe` -/

abbrev isPairCrossing (D : PLLinkDiagram) (C E : diagramComponent D) (c : Fin D.nCrossing) : Prop :=
  C ≠ E ∧
    ((componentOf D.continuation (D.incoming c 0) = C ∧
      componentOf D.continuation (D.incoming c 1) = E) ∨
     (componentOf D.continuation (D.incoming c 0) = E ∧
      componentOf D.continuation (D.incoming c 1) = C))

def isOverPairCrossing (D : PLLinkDiagram) (C E : diagramComponent D) (c : Fin D.nCrossing) : Prop :=
  C ≠ E ∧
    componentOf D.continuation (D.incoming c (D.overBranch c)) = C ∧
    componentOf D.continuation (D.incoming c (otherBranch (D.overBranch c))) = E

def overWrithe (D : PLLinkDiagram) (C E : diagramComponent D) : ℤ :=
  ∑ c : Fin D.nCrossing, if isOverPairCrossing D C E c then writheSign D c else 0

theorem otherBranch_ne_self (j : Fin 2) : otherBranch j ≠ j := by
  fin_cases j <;> decide

theorem isOverPairCrossing_irrefl (D : PLLinkDiagram) (C : diagramComponent D)
    (c : Fin D.nCrossing) : ¬ isOverPairCrossing D C C c :=
  fun h => h.1 rfl

@[simp] theorem overWrithe_self (D : PLLinkDiagram) (C : diagramComponent D) :
    overWrithe D C C = 0 := by
  unfold overWrithe
  apply Finset.sum_eq_zero
  intro c _
  rw [if_neg (isOverPairCrossing_irrefl D C c)]

theorem isOverPairCrossing_disjoint (D : PLLinkDiagram) (C E : diagramComponent D)
    (c : Fin D.nCrossing) :
    ¬ (isOverPairCrossing D C E c ∧ isOverPairCrossing D E C c) := by
  rintro ⟨⟨hCE, h1, _⟩, ⟨_, h2, _⟩⟩
  exact hCE (h1.symm.trans h2)

theorem isPairCrossing_iff_overPairCrossing (D : PLLinkDiagram) (C E : diagramComponent D)
    (c : Fin D.nCrossing) :
    isPairCrossing D C E c ↔ isOverPairCrossing D C E c ∨ isOverPairCrossing D E C c := by
  unfold isPairCrossing isOverPairCrossing
  rcases fin2_cases (D.overBranch c) with hb | hb
  · rw [hb, otherBranch_zero]
    constructor
    · rintro ⟨hCE, h01 | h10⟩
      · exact Or.inl ⟨hCE, h01.1, h01.2⟩
      · exact Or.inr ⟨hCE.symm, h10.1, h10.2⟩
    · rintro (⟨hCE, h0, h1⟩ | ⟨hEC, h0, h1⟩)
      · exact ⟨hCE, Or.inl ⟨h0, h1⟩⟩
      · exact ⟨hEC.symm, Or.inr ⟨h0, h1⟩⟩
  · rw [hb, otherBranch_one]
    constructor
    · rintro ⟨hCE, h01 | h10⟩
      · exact Or.inr ⟨hCE.symm, h01.2, h01.1⟩
      · exact Or.inl ⟨hCE, h10.2, h10.1⟩
    · rintro (⟨hCE, h1, h0⟩ | ⟨hEC, h1, h0⟩)
      · exact ⟨hCE, Or.inr ⟨h0, h1⟩⟩
      · exact ⟨hEC.symm, Or.inl ⟨h0, h1⟩⟩

theorem pairWrithe_eq_add_overWrithe (D : PLLinkDiagram) (C E : diagramComponent D) :
    pairWrithe D C E = overWrithe D C E + overWrithe D E C := by
  unfold pairWrithe overWrithe
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  change (if isPairCrossing D C E c then writheSign D c else 0) =
    (if isOverPairCrossing D C E c then writheSign D c else 0) +
    (if isOverPairCrossing D E C c then writheSign D c else 0)
  have hiff := isPairCrossing_iff_overPairCrossing D C E c
  have hdisj := isOverPairCrossing_disjoint D C E c
  by_cases h1 : isOverPairCrossing D C E c <;> by_cases h2 : isOverPairCrossing D E C c
  · exact False.elim (hdisj ⟨h1, h2⟩)
  · have hp : isPairCrossing D C E c := hiff.mpr (Or.inl h1)
    simp [hp, h1, h2]
  · have hp : isPairCrossing D C E c := hiff.mpr (Or.inr h2)
    simp [hp, h1, h2]
  · have hp : ¬ isPairCrossing D C E c := by
      intro h
      rcases hiff.mp h with h1' | h2'
      · exact h1 h1'
      · exact h2 h2'
    simp [hp, h1, h2]

/-! ### Part 2: General 4-Arc Crossing Quadruple and Symmetry of `overWrithe` -/

def branchQuadruple (D : PLLinkDiagram) (c : Fin D.nCrossing) (jA : Fin 2) :
    Finset (Fin D.nArc × Fin D.nArc) :=
  let jB := otherBranch jA
  let e_in := D.incoming c jA
  let e_out := D.continuation e_in
  let f_in := D.incoming c jB
  let f_out := D.continuation f_in
  ({e_in, e_out} : Finset (Fin D.nArc)) ×ˢ ({f_in, f_out} : Finset (Fin D.nArc))

theorem sum_branchQuadruple_paraPsi (D : PLLinkDiagram) (c : Fin D.nCrossing) (jA : Fin 2) :
    (∑ p ∈ branchQuadruple D c jA,
      paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
        (arcStartPoint D p.2) (arcEndPoint D p.2)) =
      if jA = D.overBranch c then -writheSign D c else writheSign D c := by
  let jB := otherBranch jA
  let e_in := D.incoming c jA
  let e_out := D.continuation e_in
  let f_in := D.incoming c jB
  let f_out := D.continuation f_in
  have he_ne : e_in ≠ e_out := incoming_ne_continuation_incoming D c jA
  have hf_ne : f_in ≠ f_out := incoming_ne_continuation_incoming D c jB
  change (∑ p ∈ ({e_in, e_out} : Finset (Fin D.nArc)) ×ˢ ({f_in, f_out} : Finset (Fin D.nArc)),
    paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
      (arcStartPoint D p.2) (arcEndPoint D p.2)) =
    if jA = D.overBranch c then -writheSign D c else writheSign D c
  rw [Finset.sum_product, Finset.sum_pair he_ne, Finset.sum_pair hf_ne, Finset.sum_pair hf_ne]
  let p_minus := arcStartPoint D e_in
  let v_c := D.vertexPoint (D.crossingVertex c)
  let p_plus := arcEndPoint D e_out
  let q_minus := arcStartPoint D f_in
  let q_plus := arcEndPoint D f_out
  have he_in_end : arcEndPoint D e_in = v_c :=
    congrArg D.vertexPoint (D.incoming_target c jA)
  have he_out_start : arcStartPoint D e_out = v_c :=
    (arcEndPoint_eq_arcStartPoint_continuation D e_in).symm.trans he_in_end
  have hf_in_end : arcEndPoint D f_in = v_c :=
    congrArg D.vertexPoint (D.incoming_target c jB)
  have hf_out_start : arcStartPoint D f_out = v_c :=
    (arcEndPoint_eq_arcStartPoint_continuation D f_in).symm.trans hf_in_end
  change (paraPsi p_minus (arcEndPoint D e_in) q_minus (arcEndPoint D f_in) +
      paraPsi p_minus (arcEndPoint D e_in) (arcStartPoint D f_out) q_plus) +
    (paraPsi (arcStartPoint D e_out) p_plus q_minus (arcEndPoint D f_in) +
      paraPsi (arcStartPoint D e_out) p_plus (arcStartPoint D f_out) q_plus) =
    if jA = D.overBranch c then -writheSign D c else writheSign D c
  rw [he_in_end, he_out_start, hf_in_end, hf_out_start]
  obtain ⟨sA, hsA0, hsA1, hv_A, μA, hμA_pos, htanA⟩ := through_collinear_affinePoint D c jA
  obtain ⟨tB, htB0, htB1, hv_B, μB, hμB_pos, htanB⟩ := through_collinear_affinePoint D c jB
  have hv_A_symm : affinePoint p_minus p_plus sA = v_c := hv_A.symm
  have hv_B_symm : affinePoint q_minus q_plus tB = v_c := hv_B.symm
  have hcol_B1 : paraPsi p_minus v_c q_minus v_c + paraPsi p_minus v_c v_c q_plus =
      paraPsi p_minus v_c q_minus q_plus := by
    simpa only [hv_B_symm] using
      paraPsi_collinear_right p_minus v_c q_minus q_plus tB htB0 htB1
  have hcol_B2 : paraPsi v_c p_plus q_minus v_c + paraPsi v_c p_plus v_c q_plus =
      paraPsi v_c p_plus q_minus q_plus := by
    simpa only [hv_B_symm] using
      paraPsi_collinear_right v_c p_plus q_minus q_plus tB htB0 htB1
  have hcol_A : paraPsi p_minus v_c q_minus q_plus + paraPsi v_c p_plus q_minus q_plus =
      paraPsi p_minus p_plus q_minus q_plus := by
    simpa only [hv_A_symm] using
      paraPsi_collinear_left p_minus p_plus q_minus q_plus sA hsA0 hsA1
  rw [hcol_B1, hcol_B2, hcol_A]
  have hμAB_pos : 0 < μA * μB := mul_pos hμA_pos hμB_pos
  by_cases hover : jA = D.overBranch c
  · rw [if_pos hover]
    have hdet_scale : planarDet (p_plus - p_minus) (q_plus - q_minus) =
        (μA * μB) * crossingDet D c := by
      unfold crossingDet
      rw [← hover, htanA, htanB]
      dsimp [planarDet, jB]
      ring
    have hdet_nz : planarDet (p_plus - p_minus) (q_plus - q_minus) ≠ 0 := by
      rw [hdet_scale]
      exact mul_ne_zero (ne_of_gt hμAB_pos) (selectedDet_ne_zero D c)
    rw [paraPsi_eq_of_interior_intersection p_minus p_plus q_minus q_plus
      sA tB hsA0 hsA1 htB0 htB1 (hv_A.symm.trans hv_B) hdet_nz]
    have hsign_iff : 0 < planarDet (p_plus - p_minus) (q_plus - q_minus) ↔
        0 < crossingDet D c := by
      rw [hdet_scale]
      exact mul_pos_iff_of_pos_left hμAB_pos
    simp only [hsign_iff]
    unfold writheSign crossingSign nonzeroScalarSign
    by_cases hneg : crossingDet D c < 0
    · have hn : ¬ 0 < crossingDet D c := not_lt_of_gt hneg
      simp [hneg, hn]
    · have hp : 0 < crossingDet D c :=
        lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm (selectedDet_ne_zero D c))
      simp [hneg, hp]
  · rw [if_neg hover]
    have hjA_other : jA = otherBranch (D.overBranch c) :=
      eq_otherBranch_of_ne jA (D.overBranch c) hover
    have hjB_over : jB = D.overBranch c := by
      dsimp [jB]
      rw [hjA_other, otherBranch_involutive]
    have hdet_scale : planarDet (p_plus - p_minus) (q_plus - q_minus) =
        -(μA * μB) * crossingDet D c := by
      unfold crossingDet
      rw [htanA, htanB, hjB_over, ← hjA_other]
      dsimp [planarDet]
      ring
    have hdet_nz : planarDet (p_plus - p_minus) (q_plus - q_minus) ≠ 0 := by
      rw [hdet_scale]
      exact mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hμAB_pos)) (selectedDet_ne_zero D c)
    rw [paraPsi_eq_of_interior_intersection p_minus p_plus q_minus q_plus
      sA tB hsA0 hsA1 htB0 htB1 (hv_A.symm.trans hv_B) hdet_nz]
    have hsign_iff : 0 < planarDet (p_plus - p_minus) (q_plus - q_minus) ↔
        crossingDet D c < 0 := by
      rw [hdet_scale]
      constructor <;> intro h <;> nlinarith
    simp only [hsign_iff]
    unfold writheSign crossingSign nonzeroScalarSign
    by_cases hneg : crossingDet D c < 0 <;> simp [hneg]

def pairBranch (D : PLLinkDiagram) (C : diagramComponent D) (c : Fin D.nCrossing) : Fin 2 :=
  if componentOf D.continuation (D.incoming c (D.overBranch c)) = C then
    D.overBranch c
  else
    otherBranch (D.overBranch c)

theorem pairBranch_components_of_isPairCrossing (D : PLLinkDiagram) (C E : diagramComponent D)
    (c : Fin D.nCrossing) (hc : isPairCrossing D C E c) :
    componentOf D.continuation (D.incoming c (pairBranch D C c)) = C ∧
    componentOf D.continuation (D.incoming c (otherBranch (pairBranch D C c))) = E := by
  unfold pairBranch
  rcases (isPairCrossing_iff_overPairCrossing D C E c).mp hc with ⟨_, hC, hE⟩ | ⟨hEC, hE, hC⟩
  · rw [if_pos hC]
    exact ⟨hC, hE⟩
  · have hne : componentOf D.continuation (D.incoming c (D.overBranch c)) ≠ C := by
      rw [hE]
      exact hEC
    rw [if_neg hne, otherBranch_involutive]
    exact ⟨hC, hE⟩

theorem mem_branchQuadruple_endpoints (D : PLLinkDiagram) (c : Fin D.nCrossing) (jA : Fin 2)
    {p : Fin D.nArc × Fin D.nArc} (hp : p ∈ branchQuadruple D c jA) :
    (D.arcSource p.1 = D.crossingVertex c ∨ D.arcTarget p.1 = D.crossingVertex c) ∧
    (D.arcSource p.2 = D.crossingVertex c ∨ D.arcTarget p.2 = D.crossingVertex c) := by
  simp only [branchQuadruple, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with ⟨he | he, hf | hf⟩
  · refine ⟨Or.inr (he ▸ D.incoming_target c _), Or.inr (hf ▸ D.incoming_target c _)⟩
  · refine ⟨Or.inr (he ▸ D.incoming_target c _), Or.inl ?_⟩
    rw [hf, D.continuation_crossing]
    exact D.outgoing_source c _
  · refine ⟨Or.inl ?_, Or.inr (hf ▸ D.incoming_target c _)⟩
    rw [he, D.continuation_crossing]
    exact D.outgoing_source c _
  · refine ⟨Or.inl ?_, Or.inl ?_⟩
    · rw [he, D.continuation_crossing]; exact D.outgoing_source c _
    · rw [hf, D.continuation_crossing]; exact D.outgoing_source c _

theorem branchQuadruple_subset_components (D : PLLinkDiagram) (C E : diagramComponent D)
    (c : Fin D.nCrossing) (hc : isPairCrossing D C E c) :
    branchQuadruple D c (pairBranch D C c) ⊆
      componentArcFinset D C ×ˢ componentArcFinset D E := by
  intro p hp
  obtain ⟨hC, hE⟩ := pairBranch_components_of_isPairCrossing D C E c hc
  simp only [branchQuadruple, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hp
  simp only [Finset.mem_product, mem_componentArcFinset_iff]
  constructor
  · rcases hp.1 with h | h
    · rw [h]; exact hC
    · rw [h, componentOf_apply]; exact hC
  · rcases hp.2 with h | h
    · rw [h]; exact hE
    · rw [h, componentOf_apply]; exact hE

theorem branchQuadruple_disjoint (D : PLLinkDiagram) (C E : diagramComponent D)
    {c1 c2 : Fin D.nCrossing} (hc1 : isPairCrossing D C E c1) (h12 : c1 ≠ c2) :
    Disjoint (branchQuadruple D c1 (pairBranch D C c1))
      (branchQuadruple D c2 (pairBranch D C c2)) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  have hsub := branchQuadruple_subset_components D C E c1 hc1 hp1
  simp only [Finset.mem_product, mem_componentArcFinset_iff] at hsub
  have hef : p.1 ≠ p.2 := by
    intro hEq
    apply hc1.1
    rw [← hsub.1, ← hsub.2, hEq]
  have hv12 : D.crossingVertex c1 ≠ D.crossingVertex c2 :=
    fun h => h12 (D.crossingVertex_injective h)
  obtain ⟨he1, hf1⟩ := mem_branchQuadruple_endpoints D c1 (pairBranch D C c1) hp1
  obtain ⟨he2, hf2⟩ := mem_branchQuadruple_endpoints D c2 (pairBranch D C c2) hp2
  exact distinct_arcs_not_same_endpoints D p.1 p.2 hef
    (D.crossingVertex c1) (D.crossingVertex c2) hv12 he1 he2 hf1 hf2

theorem incident_crossing_mem_pairCrossing_and_quadruple
    (D : PLLinkDiagram) (C E : diagramComponent D) (hCE : C ≠ E)
    (c : Fin D.nCrossing) (e f : Fin D.nArc)
    (heC : (componentOf D.continuation e : diagramComponent D) = C)
    (hfE : (componentOf D.continuation f : diagramComponent D) = E)
    (he_inc : D.arcSource e = D.crossingVertex c ∨ D.arcTarget e = D.crossingVertex c)
    (hf_inc : D.arcSource f = D.crossingVertex c ∨ D.arcTarget f = D.crossingVertex c) :
    isPairCrossing D C E c ∧ (e, f) ∈ branchQuadruple D c (pairBranch D C c) := by
  have h_port_comp : ∀ b : Fin D.nArc,
      (b = D.incoming c 0 ∨ b = D.incoming c 1 ∨ b = D.outgoing c 0 ∨ b = D.outgoing c 1) →
      ∃ j : Fin 2, (b = D.incoming c j ∨ b = D.continuation (D.incoming c j)) ∧
        componentOf D.continuation b = componentOf D.continuation (D.incoming c j) := by
    rintro b (rfl | rfl | rfl | rfl)
    · exact ⟨0, Or.inl rfl, rfl⟩
    · exact ⟨1, Or.inl rfl, rfl⟩
    · refine ⟨(D.through c).symm 0, Or.inr ?_, ?_⟩
      · rw [D.continuation_crossing, Equiv.apply_symm_apply]
      · have h := componentOf_apply D.continuation (D.incoming c ((D.through c).symm 0))
        rw [D.continuation_crossing, Equiv.apply_symm_apply] at h
        exact h
    · refine ⟨(D.through c).symm 1, Or.inr ?_, ?_⟩
      · rw [D.continuation_crossing, Equiv.apply_symm_apply]
      · have h := componentOf_apply D.continuation (D.incoming c ((D.through c).symm 1))
        rw [D.continuation_crossing, Equiv.apply_symm_apply] at h
        exact h
  obtain ⟨je, hje_mem, hje_comp⟩ := h_port_comp e ((D.crossing_incidence_complete c e).mp he_inc)
  obtain ⟨jf, hjf_mem, hjf_comp⟩ := h_port_comp f ((D.crossing_incidence_complete c f).mp hf_inc)
  have hje_C : (componentOf D.continuation (D.incoming c je) : diagramComponent D) = C :=
    hje_comp.symm.trans heC
  have hjf_E : (componentOf D.continuation (D.incoming c jf) : diagramComponent D) = E :=
    hjf_comp.symm.trans hfE
  have hje_ne_jf : je ≠ jf := by
    intro hEq
    subst hEq
    exact hCE (hje_C.symm.trans hjf_E)
  have hc_pair : isPairCrossing D C E c := by
    refine ⟨hCE, ?_⟩
    have hje01 : je = 0 ∨ je = 1 := by fin_cases je <;> simp
    have hjf01 : jf = 0 ∨ jf = 1 := by fin_cases jf <;> simp
    rcases hje01 with rfl | rfl <;> rcases hjf01 with rfl | rfl
    · exact False.elim (hje_ne_jf rfl)
    · exact Or.inl ⟨hje_C, hjf_E⟩
    · exact Or.inr ⟨hjf_E, hje_C⟩
    · exact False.elim (hje_ne_jf rfl)
  obtain ⟨_, hpb_E⟩ := pairBranch_components_of_isPairCrossing D C E c hc_pair
  have hje_eq_pb : je = pairBranch D C c := by
    by_contra hne
    have hje_other : je = otherBranch (pairBranch D C c) :=
      eq_otherBranch_of_ne je (pairBranch D C c) hne
    rw [hje_other] at hje_C
    exact hCE (hje_C.symm.trans hpb_E)
  have hjf_eq_other : jf = otherBranch (pairBranch D C c) := by
    rw [← hje_eq_pb]
    exact eq_otherBranch_of_ne jf je hje_ne_jf.symm
  refine ⟨hc_pair, ?_⟩
  simp only [branchQuadruple, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
  rw [← hjf_eq_other, ← hje_eq_pb]
  exact ⟨hje_mem, hjf_mem⟩

theorem paraPsi_eq_zero_of_not_in_pairQuadruples
    (D : PLLinkDiagram) (C E : diagramComponent D) (hCE : C ≠ E)
    {p : Fin D.nArc × Fin D.nArc}
    (hpCE : p ∈ componentArcFinset D C ×ˢ componentArcFinset D E)
    (hp_not : p ∉ (Finset.univ.filter (isPairCrossing D C E)).biUnion
      (fun c => branchQuadruple D c (pairBranch D C c))) :
    paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
      (arcStartPoint D p.2) (arcEndPoint D p.2) = 0 := by
  simp only [Finset.mem_product, mem_componentArcFinset_iff] at hpCE
  apply paraPsi_eq_zero_of_disjoint
  intro s t hs0 hs1 ht0 ht1 heq
  have hef : p.1 ≠ p.2 := by
    intro hEq
    exact hCE (hpCE.1.symm.trans (hEq ▸ hpCE.2))
  obtain ⟨v, he_v, hf_v⟩ :=
    arc_segments_intersect_shared_vertex D p.1 p.2 hef s t hs0 hs1 ht0 ht1 heq
  by_cases hc : ∃ c : Fin D.nCrossing, D.crossingVertex c = v
  · obtain ⟨c, rfl⟩ := hc
    obtain ⟨hc_pair, hp_mem⟩ := incident_crossing_mem_pairCrossing_and_quadruple
      D C E hCE c p.1 p.2 hpCE.1 hpCE.2 he_v hf_v
    apply hp_not
    rw [Finset.mem_biUnion]
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc_pair⟩, hp_mem⟩
  · push_neg at hc
    have hsame := regular_vertex_incident_same_component' D v hc p.1 p.2 he_v hf_v
    exact hCE (hpCE.1.symm.trans (hsame.trans hpCE.2))

theorem overWrithe_symm (D : PLLinkDiagram) (C E : diagramComponent D) :
    overWrithe D C E = overWrithe D E C := by
  by_cases hCE : C = E
  · subst hCE
    rfl
  · let M := Finset.univ.filter (isPairCrossing D C E)
    let U := M.biUnion (fun c => branchQuadruple D c (pairBranch D C c))
    have hU_sub : U ⊆ componentArcFinset D C ×ˢ componentArcFinset D E := by
      intro p hp
      rw [Finset.mem_biUnion] at hp
      obtain ⟨c, hcM, hpc⟩ := hp
      exact branchQuadruple_subset_components D C E c (Finset.mem_filter.mp hcM).2 hpc
    have htotal : (∑ p ∈ componentArcFinset D C ×ˢ componentArcFinset D E,
        paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
          (arcStartPoint D p.2) (arcEndPoint D p.2)) = 0 := by
      rw [Finset.sum_product]
      exact sum_paraPsi_component_left_eq_zero D C E
    have hsum_U : (∑ p ∈ U,
        paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
          (arcStartPoint D p.2) (arcEndPoint D p.2)) = 0 := by
      rw [← htotal]
      apply Finset.sum_subset hU_sub
      intro p hpCE hp_not
      exact paraPsi_eq_zero_of_not_in_pairQuadruples D C E hCE hpCE hp_not
    have hbiUnion : (∑ p ∈ U,
        paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
          (arcStartPoint D p.2) (arcEndPoint D p.2)) =
        ∑ c ∈ M, ∑ p ∈ branchQuadruple D c (pairBranch D C c),
          paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
            (arcStartPoint D p.2) (arcEndPoint D p.2) := by
      apply Finset.sum_biUnion
      intro c1 hc1 c2 _ h12
      exact branchQuadruple_disjoint D C E (Finset.mem_filter.mp hc1).2 h12
    rw [hbiUnion] at hsum_U
    have hterm : ∀ c : Fin D.nCrossing,
        (if isPairCrossing D C E c then
          ∑ p ∈ branchQuadruple D c (pairBranch D C c),
            paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
              (arcStartPoint D p.2) (arcEndPoint D p.2)
        else 0) =
        (if isOverPairCrossing D E C c then writheSign D c else 0) -
        (if isOverPairCrossing D C E c then writheSign D c else 0) := by
      intro c
      have hiff := isPairCrossing_iff_overPairCrossing D C E c
      have hdisj := isOverPairCrossing_disjoint D C E c
      by_cases h1 : isOverPairCrossing D C E c <;> by_cases h2 : isOverPairCrossing D E C c
      · exact False.elim (hdisj ⟨h1, h2⟩)
      · have hp : isPairCrossing D C E c := hiff.mpr (Or.inl h1)
        rw [if_pos hp, if_pos h1, if_neg h2, zero_sub]
        rw [sum_branchQuadruple_paraPsi]
        have hpb : pairBranch D C c = D.overBranch c := by
          unfold pairBranch
          exact if_pos h1.2.1
        rw [if_pos hpb]
      · have hp : isPairCrossing D C E c := hiff.mpr (Or.inr h2)
        rw [if_pos hp, if_neg h1, if_pos h2, sub_zero]
        rw [sum_branchQuadruple_paraPsi]
        have hne : componentOf D.continuation (D.incoming c (D.overBranch c)) ≠ C := by
          rw [h2.2.1]
          exact h2.1
        have hpb : pairBranch D C c ≠ D.overBranch c := by
          unfold pairBranch
          rw [if_neg hne]
          exact otherBranch_ne_self (D.overBranch c)
        rw [if_neg hpb]
      · have hp : ¬ isPairCrossing D C E c := by
          intro h
          rcases hiff.mp h with h1' | h2'
          · exact h1 h1'
          · exact h2 h2'
        simp [hp, h1, h2]
    have hdiff : overWrithe D E C - overWrithe D C E = 0 := by
      unfold overWrithe
      rw [← Finset.sum_sub_distrib]
      calc
        (∑ c : Fin D.nCrossing,
          ((if isOverPairCrossing D E C c then writheSign D c else 0) -
           (if isOverPairCrossing D C E c then writheSign D c else 0))) =
          ∑ c : Fin D.nCrossing,
            if isPairCrossing D C E c then
              ∑ p ∈ branchQuadruple D c (pairBranch D C c),
                paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
                  (arcStartPoint D p.2) (arcEndPoint D p.2)
            else 0 := by
          apply Finset.sum_congr rfl
          intro c _
          exact (hterm c).symm
        _ = ∑ c ∈ M, ∑ p ∈ branchQuadruple D c (pairBranch D C c),
              paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
                (arcStartPoint D p.2) (arcEndPoint D p.2) := by
          rw [Finset.sum_filter]
        _ = 0 := hsum_U
    omega

/-! ### Part 3: Linking Numbers, Total Linking `Λ`, and `mixedWrithe` -/

def linking (D : PLLinkDiagram) (C E : diagramComponent D) : ℤ :=
  overWrithe D C E

theorem two_mul_linking_eq_pairWrithe (D : PLLinkDiagram) (C E : diagramComponent D) :
    2 * linking D C E = pairWrithe D C E := by
  unfold linking
  rw [pairWrithe_eq_add_overWrithe D C E, ← overWrithe_symm D C E]
  ring

theorem linking_symm (D : PLLinkDiagram) (C E : diagramComponent D) :
    linking D C E = linking D E C :=
  overWrithe_symm D C E

@[simp] theorem linking_self (D : PLLinkDiagram) (C : diagramComponent D) :
    linking D C C = 0 :=
  overWrithe_self D C

theorem isMixed_iff_overUnder_ne (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    IsMixed D c ↔
      componentOf D.continuation (D.incoming c (D.overBranch c)) ≠
        componentOf D.continuation (D.incoming c (otherBranch (D.overBranch c))) := by
  unfold IsMixed
  rcases fin2_cases (D.overBranch c) with hb | hb
  · rw [hb, otherBranch_zero]
  · rw [hb, otherBranch_one, ne_comm]

theorem totalOrderedPairSum_linking_eq_mixedWrithe (D : PLLinkDiagram) :
    totalOrderedPairSum D (linking D) = mixedWrithe D := by
  unfold totalOrderedPairSum linking overWrithe mixedWrithe
  conv_lhs =>
    arg 2
    ext C
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  letI : DecidableEq (diagramComponent D) := Classical.decEq _
  let C₀ : diagramComponent D := componentOf D.continuation (D.incoming c (D.overBranch c))
  let E₀ : diagramComponent D := componentOf D.continuation (D.incoming c (otherBranch (D.overBranch c)))
  have hsingle : (∑ C : diagramComponent D, ∑ E : diagramComponent D,
      if isOverPairCrossing D C E c then writheSign D c else 0) =
      if isOverPairCrossing D C₀ E₀ c then writheSign D c else 0 := by
    rw [Finset.sum_eq_single C₀]
    · rw [Finset.sum_eq_single E₀]
      · intro E _ hE
        have hnot : ¬ isOverPairCrossing D C₀ E c := fun h => hE h.2.2.symm
        rw [if_neg hnot]
      · intro hE₀
        exact False.elim (hE₀ (Finset.mem_univ E₀))
    · intro C _ hC
      apply Finset.sum_eq_zero
      intro E _
      have hnot : ¬ isOverPairCrossing D C E c := fun h => hC h.2.1.symm
      rw [if_neg hnot]
    · intro hC₀
      exact False.elim (hC₀ (Finset.mem_univ C₀))
  rw [hsingle]
  have hiff : isOverPairCrossing D C₀ E₀ c ↔ IsMixed D c := by
    unfold isOverPairCrossing
    rw [isMixed_iff_overUnder_ne]
    exact ⟨fun h => h.1, fun h => ⟨h, rfl, rfl⟩⟩
  by_cases hm : IsMixed D c
  · rw [if_pos (hiff.mpr hm), if_pos hm]
  · rw [if_neg (mt hiff.mp hm), if_neg hm]

def totalLinking (D : PLLinkDiagram) : ℤ :=
  let idx := Fintype.equivFin (diagramComponent D)
  ∑ C : diagramComponent D, ∑ E : diagramComponent D,
    if idx C < idx E then linking D C E else 0

theorem two_mul_totalLinking_eq_totalOrderedPairSum (D : PLLinkDiagram) :
    2 * totalLinking D = totalOrderedPairSum D (linking D) := by
  let idx := Fintype.equivFin (diagramComponent D)
  unfold totalLinking totalOrderedPairSum
  have h2 : 2 * (∑ C : diagramComponent D, ∑ E : diagramComponent D,
      if idx C < idx E then linking D C E else 0) =
      (∑ C : diagramComponent D, ∑ E : diagramComponent D,
        if idx C < idx E then linking D C E else 0) +
      (∑ C : diagramComponent D, ∑ E : diagramComponent D,
        if idx C < idx E then linking D C E else 0) := by ring
  rw [h2]
  have hswap : (∑ C : diagramComponent D, ∑ E : diagramComponent D,
      if idx C < idx E then linking D C E else 0) =
      ∑ C : diagramComponent D, ∑ E : diagramComponent D,
        if idx E < idx C then linking D C E else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro C _
    apply Finset.sum_congr rfl
    intro E _
    rw [linking_symm D E C]
  conv_lhs =>
    rhs
    rw [hswap]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro C _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E _
  by_cases hlt : idx C < idx E
  · have hgt : ¬ idx E < idx C := not_lt_of_gt hlt
    simp [hlt, hgt]
  · by_cases hgt : idx E < idx C
    · simp [hlt, hgt]
    · have hEq : idx C = idx E := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
      have hCE : C = E := idx.injective hEq
      subst hCE
      simp [hlt]

theorem two_mul_totalLinking_eq_mixedWrithe (D : PLLinkDiagram) :
    2 * totalLinking D = mixedWrithe D :=
  (two_mul_totalLinking_eq_totalOrderedPairSum D).trans
    (totalOrderedPairSum_linking_eq_mixedWrithe D)

/-! ### Part 4: Behavior of `mixedWrithe` Under Mixed Crossing Switch and Layered Traversals -/

theorem isMixed_switchCrossing_iff (D : PLLinkDiagram) (c d : Fin D.nCrossing) :
    IsMixed (switchCrossing D c) d ↔ IsMixed D d := Iff.rfl

theorem writheSign_switchCrossing_self (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    writheSign (switchCrossing D c) c = -writheSign D c := by
  unfold writheSign
  rw [crossingSign_switchCrossing]
  cases crossingSign D c <;> rfl

theorem writheSign_switchCrossing_of_ne (D : PLLinkDiagram) (c d : Fin D.nCrossing)
    (hd : d ≠ c) :
    writheSign (switchCrossing D c) d = writheSign D d := by
  unfold writheSign
  rw [crossingSign_switchCrossing_of_ne D c d hd]

theorem mixedWrithe_switchCrossing_of_mixed (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hc : IsMixed D c) :
    mixedWrithe (switchCrossing D c) = mixedWrithe D - 2 * writheSign D c := by
  have hdiff : mixedWrithe (switchCrossing D c) - mixedWrithe D = - 2 * writheSign D c := by
    unfold mixedWrithe
    change (∑ d : Fin D.nCrossing,
        if IsMixed (switchCrossing D c) d then writheSign (switchCrossing D c) d else 0) -
      (∑ d : Fin D.nCrossing, if IsMixed D d then writheSign D d else 0) = - 2 * writheSign D c
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single c]
    · simp only [isMixed_switchCrossing_iff, if_pos hc, writheSign_switchCrossing_self]
      ring
    · intro d _ hdc
      rw [isMixed_switchCrossing_iff, writheSign_switchCrossing_of_ne D c d hdc, sub_self]
    · intro hc_univ
      exact False.elim (hc_univ (Finset.mem_univ c))
  omega

theorem mixedWrithe_switchCrossing_of_self (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hc : ¬ IsMixed D c) :
    mixedWrithe (switchCrossing D c) = mixedWrithe D := by
  unfold mixedWrithe
  apply Finset.sum_congr rfl
  intro d _
  by_cases hdc : d = c
  · subst d
    rw [isMixed_switchCrossing_iff, if_neg hc, if_neg hc]
  · rw [isMixed_switchCrossing_iff, writheSign_switchCrossing_of_ne D c d hdc]

theorem badAt_of_isOverPairCrossing_of_lt {D : PLLinkDiagram} (T : BasedTraversal D)
    {C E : diagramComponent D} (hlt : T.componentIndex C < T.componentIndex E)
    {c : Fin D.nCrossing} (hc : isOverPairCrossing D E C c) :
    badAt T c := by
  unfold badAt
  intro hfb_eq
  have hfirst := firstVisitedBranch_is_first T c
  rw [hfb_eq] at hfirst
  have h1 : (visitRank T (D.incoming c (D.overBranch c))).1 = T.componentIndex E := by
    dsimp [visitRank]
    rw [hc.2.1]
  have h2 : (visitRank T (D.incoming c (otherBranch (D.overBranch c)))).1 = T.componentIndex C := by
    dsimp [visitRank]
    rw [hc.2.2]
  unfold rankBefore at hfirst
  rw [h1, h2] at hfirst
  rcases hfirst with hlt' | ⟨heq, _⟩
  · exact not_lt_of_gt hlt hlt'
  · exact (ne_of_lt hlt) heq.symm

theorem overWrithe_eq_zero_of_no_mixed_bad {D : PLLinkDiagram} (T : BasedTraversal D)
    (hNoMixedBad : ∀ c : Fin D.nCrossing, IsMixed D c → ¬ badAt T c)
    (C E : diagramComponent D) :
    overWrithe D C E = 0 := by
  have h_of_lt : ∀ A B : diagramComponent D,
      T.componentIndex A < T.componentIndex B → overWrithe D B A = 0 := by
    intro A B hlt
    unfold overWrithe
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : isOverPairCrossing D B A c
    · exfalso
      have hm : IsMixed D c := by
        rw [isMixed_iff_overUnder_ne]
        rw [hc.2.1, hc.2.2]
        exact hc.1
      exact hNoMixedBad c hm (badAt_of_isOverPairCrossing_of_lt T hlt hc)
    · rw [if_neg hc]
  by_cases hlt : T.componentIndex C < T.componentIndex E
  · rw [overWrithe_symm D C E]
    exact h_of_lt C E hlt
  · by_cases hgt : T.componentIndex E < T.componentIndex C
    · exact h_of_lt E C hgt
    · have hEq : T.componentIndex C = T.componentIndex E :=
        le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
      have hCE : C = E := T.componentIndex.injective hEq
      subst hCE
      exact overWrithe_self D C

theorem mixedWrithe_eq_zero_of_no_mixed_bad {D : PLLinkDiagram} (T : BasedTraversal D)
    (hNoMixedBad : ∀ c : Fin D.nCrossing, IsMixed D c → ¬ badAt T c) :
    mixedWrithe D = 0 := by
  rw [← totalOrderedPairSum_linking_eq_mixedWrithe]
  unfold totalOrderedPairSum linking
  apply Finset.sum_eq_zero
  intro C _
  apply Finset.sum_eq_zero
  intro E _
  exact overWrithe_eq_zero_of_no_mixed_bad T hNoMixedBad C E

end GeminiLowest
