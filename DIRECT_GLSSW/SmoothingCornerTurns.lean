import SmoothingCornerVectors
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

/-- The literal determinant at the end of an arc, using actual continuation. -/
def turnDet (D : PLLinkDiagram) (e : Fin D.nArc) : ℝ :=
  planarDet (arcVector D e) (arcVector D (D.continuation e))

/-- Both new corner determinants have the same sign as the ordered incoming
strand determinant, with strictly positive, derived geometric factors. -/
theorem connector_turn_factors (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      turnDet (smoothCrossing D c) (smoothArcEquiv D (Sum.inl (D.incoming c i))) =
        a * planarDet (strandTangent D c i) (strandTangent D c (otherBranch i)) ∧
      turnDet (smoothCrossing D c) (smoothArcEquiv D (Sum.inr i)) =
        b * planarDet (strandTangent D c i) (strandTangent D c (otherBranch i)) := by
  obtain ⟨s,hs,hv⟩ := outgoing_vector D c (otherBranch i)
  have he := smoothEpsilon_pos D c
  have hbound := crossingCutoff_parameters D c he
    (lt_of_lt_of_le (smoothEpsilon_lt_radius D c) (smoothRadius_le_cutoff D c)) i
  refine ⟨(1-smoothEpsilon D c)*smoothEpsilon D c,smoothEpsilon D c*s,
    mul_pos hbound.1 he,mul_pos he hs,?_,?_⟩
  · rw [turnDet,Gemini.smooth_step_incoming,incoming_vector,connector_vector]
    simp [planarDet,smul_eq_mul]
    ring
  · rw [turnDet,Gemini.smooth_step_connector,D.continuation_crossing,hv,connector_vector]
    simp [planarDet,smul_eq_mul]
    ring

/-- At a positive first-under crossing, the actual detached-child bevel has
left turns at BOTH endpoints. The actual parent connector has right turns. -/
theorem first_under_connector_turns (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing) (hc : badAt T c) (hpos : crossingSign D c = Sign.pos) :
    (0 < turnDet (smoothCrossing D c)
      (smoothArcEquiv D (Sum.inl (D.incoming c (otherBranch (firstVisitedBranch T c))))) ∧
     0 < turnDet (smoothCrossing D c)
      (smoothArcEquiv D (Sum.inr (otherBranch (firstVisitedBranch T c))))) ∧
    (turnDet (smoothCrossing D c)
      (smoothArcEquiv D (Sum.inl (D.incoming c (firstVisitedBranch T c)))) < 0 ∧
     turnDet (smoothCrossing D c)
      (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))) < 0) := by
  have hbranch : otherBranch (firstVisitedBranch T c) = D.overBranch c := by
    have hne : firstVisitedBranch T c ≠ D.overBranch c := hc
    by_contra h
    have hh : D.overBranch c ≠ otherBranch (firstVisitedBranch T c) := Ne.symm h
    exact (neq_otherBranch_iff _ _).mp hh hne.symm
  have hdet : 0 < crossingDet D c := by
    apply (nonzeroScalarSign_value_pos_iff (crossingDet D c) (selectedDet_ne_zero D c)).mp
    change (crossingSign D c).value = 1
    rw [hpos]
    rfl
  have hdchild : 0 < planarDet (strandTangent D c (otherBranch (firstVisitedBranch T c)))
      (strandTangent D c (otherBranch (otherBranch (firstVisitedBranch T c)))) := by
    simpa only [hbranch] using hdet
  have hdparent : planarDet (strandTangent D c (firstVisitedBranch T c))
      (strandTangent D c (otherBranch (firstVisitedBranch T c))) < 0 := by
    rw [otherBranch_involutive] at hdchild
    rw [planarDet_swap] at hdchild
    linarith
  obtain ⟨a,b,ha,hb,hleft,hright⟩ := connector_turn_factors D c
    (otherBranch (firstVisitedBranch T c))
  obtain ⟨a',b',ha',hb',hleft',hright'⟩ := connector_turn_factors D c
    (firstVisitedBranch T c)
  rw [hleft,hright,hleft',hright']
  exact ⟨⟨mul_pos ha hdchild,mul_pos hb hdchild⟩,
    ⟨mul_neg_of_pos_of_neg ha' hdparent,mul_neg_of_pos_of_neg hb' hdparent⟩⟩

end DirectGLSSW.HOMFLY.SmoothingCornerGeometry
