import RoundingCrossingIntersection
import RetainedRoundingIntersections

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Aggregate Gate4: actual transverse strand lines have only zero equal coefficients. -/
theorem crossing_strand_coefficients_zero (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i j : Fin 2) (hij : i ≠ j) (q r : ℝ)
    (hp : q • strandTangent D c i = r • strandTangent D c j) : q = 0 ∧ r = 0 := by
  have h01 : ∀ q r : ℝ, q • strandTangent D c 0 = r • strandTangent D c 1 → q = 0 ∧ r = 0 := by
    intro q r h
    have hd := congrArg (fun w : PlanarPoint ℝ => planarDet w (strandTangent D c 1)) h
    dsimp only at hd
    have hl : planarDet (q • strandTangent D c 0) (strandTangent D c 1) =
        q * planarDet (strandTangent D c 0) (strandTangent D c 1) := by
      simp [planarDet,smul_eq_mul]
      ring
    have hr0 : planarDet (r • strandTangent D c 1) (strandTangent D c 1) = 0 := by
      simp [planarDet,smul_eq_mul]
      ring
    rw [hl,hr0] at hd
    have hdet : planarDet (strandTangent D c 0) (strandTangent D c 1) ≠ 0 := D.crossing_transverse c
    have hq : q = 0 := (mul_eq_zero.mp hd).resolve_right hdet
    have hv : strandTangent D c 1 ≠ 0 := by
      intro hz
      apply hdet
      rw [hz]
      simp [planarDet]
    have hrsmul : r • strandTangent D c 1 = 0 := by simpa only [hq,zero_smul] using h.symm
    have hr : r = 0 := (smul_eq_zero.mp hrsmul).resolve_right hv
    exact ⟨hq,hr⟩
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact h01 q r hp
  · have h := h01 r q hp.symm
    exact ⟨h.2,h.1⟩
  · exact False.elim (hij rfl)

theorem roundedCorner_crossing_planar_on_line (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) (δ s : ℝ) : ∃ q : ℝ,
    Complex.equivRealProd (roundedCorner D (D.incoming c i) δ s) =
      D.vertexPoint (D.crossingVertex c) + q • strandTangent D c i := by
  obtain ⟨q,hq⟩ := roundedCorner_crossing_on_line D c i δ s
  refine ⟨q,?_⟩
  rw [hq]
  apply Prod.ext <;> simp [Complex.equivRealProd_apply,Complex.real_smul,
    cornerCenter,arcVector,strandTangent,D.incoming_target]

/-- The other retained incoming branch cannot meet an actual corner branch. -/
theorem roundedCorner_ne_other_retained_incoming (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i j : Fin 2) (hij : i ≠ j) (δ : RoundingFraction) (s t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    Complex.equivRealProd (roundedCorner D (D.incoming c i) δ.val s) ≠
      retainedArcPoint D (D.incoming c j) δ t := by
  let α : ℝ := δ.val + (1 - 2 * δ.val) * t
  have hα := retainedArc_parameter_interior δ t ht
  obtain ⟨q,hq⟩ := roundedCorner_crossing_planar_on_line D c i δ.val s
  have hray : retainedArcPoint D (D.incoming c j) δ t =
      D.vertexPoint (D.crossingVertex c) + (α - 1) • strandTangent D c j := by
    apply Prod.ext <;> simp [retainedArcPoint,affinePoint,α,strandTangent,
      D.incoming_target,smul_eq_mul] <;> ring
  intro heq
  rw [hq,hray] at heq
  have hp := add_left_cancel heq
  have hz := (crossing_strand_coefficients_zero D c i j hij q (α - 1) hp).2
  dsimp only [α] at hz
  linarith [hα.2]

/-- The other retained outgoing through branch cannot meet an actual corner branch. -/
theorem roundedCorner_ne_other_retained_outgoing (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i j : Fin 2) (hij : i ≠ j) (δ : RoundingFraction) (s t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    Complex.equivRealProd (roundedCorner D (D.incoming c i) δ.val s) ≠
      retainedArcPoint D (D.continuation (D.incoming c j)) δ t := by
  let α : ℝ := δ.val + (1 - 2 * δ.val) * t
  have hα := retainedArc_parameter_interior δ t ht
  obtain ⟨q,hq⟩ := roundedCorner_crossing_planar_on_line D c i δ.val s
  obtain ⟨a,ha,hv⟩ := D.through_tangents_positive_collinear c j
  change strandTangent D c j = a •
    (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c j))) - D.vertexPoint (D.crossingVertex c)) at hv
  have hray : retainedArcPoint D (D.continuation (D.incoming c j)) δ t =
      D.vertexPoint (D.crossingVertex c) + (α / a) • strandTangent D c j := by
    rw [hv]
    simp only [smul_smul,div_mul_cancel₀ _ (ne_of_gt ha)]
    apply Prod.ext <;> simp [retainedArcPoint,affinePoint,α,D.continuation_crossing,
      D.outgoing_source,smul_eq_mul] <;> ring
  intro heq
  rw [hq,hray] at heq
  have hp := add_left_cancel heq
  have hz := (crossing_strand_coefficients_zero D c i j hij q (α / a) hp).2
  have hpos : 0 < α / a := div_pos hα.1 ha
  exact (ne_of_gt hpos) hz

/-- Completeness of actual crossing ports enumerates every incident retained label. -/
theorem crossing_incident_arc_label (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (f : Fin D.nArc) (hf : D.arcSource f = D.crossingVertex c ∨ D.arcTarget f = D.crossingVertex c) :
    ∃ j : Fin 2, f = D.incoming c j ∨ f = D.continuation (D.incoming c j) := by
  rcases (D.crossing_incidence_complete c f).mp hf with h | h | h | h
  · exact ⟨0,Or.inl h⟩
  · exact ⟨1,Or.inl h⟩
  · refine ⟨(D.through c).symm 0,Or.inr ?_⟩
    rw [D.continuation_crossing,Equiv.apply_symm_apply]
    exact h
  · refine ⟨(D.through c).symm 1,Or.inr ?_⟩
    rw [D.continuation_crossing,Equiv.apply_symm_apply]
    exact h

/-- An arc ending at a crossing is an actual incoming port, never an outgoing one. -/
theorem crossing_incoming_arc_label (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : Fin D.nArc) (he : D.arcTarget e = D.crossingVertex c) :
    ∃ i : Fin 2, e = D.incoming c i := by
  rcases (D.crossing_incidence_complete c e).mp (Or.inr he) with h | h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · subst e
    exact False.elim (D.arc_endpoints_distinct _ ((D.outgoing_source c 0).trans he.symm))
  · subst e
    exact False.elim (D.arc_endpoints_distinct _ ((D.outgoing_source c 1).trans he.symm))

end DirectGLSSW.HOMFLY.PrincipalTurning






