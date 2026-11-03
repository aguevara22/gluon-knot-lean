import SmoothingOldArcVectors
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

theorem old_arc_continuation (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : Fin D.nArc) (he : ∀ i : Fin 2, e ≠ D.incoming c i) :
    (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl e)) =
      smoothArcEquiv D (Sum.inl (D.continuation e)) := by
  rw [← smoothCode_actual_step D c (Sum.inl e),smoothCode_old_step D c e he]
  simp only [cutContinuation,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne (he 0) (he 1)]

/-- Every retained old turn, including a straight crossing subdivision, is scaled
by a positive factor. The two cut incoming ends are precisely the new corners. -/
theorem old_turn_positive_multiple (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : Fin D.nArc) (he : ∀ i : Fin 2, e ≠ D.incoming c i) :
    ∃ a : ℝ, 0 < a ∧
      turnDet (smoothCrossing D c) (smoothArcEquiv D (Sum.inl e)) = a * turnDet D e := by
  obtain ⟨a,ha,hva⟩ := old_arc_vector_positive_multiple D c e
  obtain ⟨b,hb,hvb⟩ := old_arc_vector_positive_multiple D c (D.continuation e)
  refine ⟨a*b,mul_pos ha hb,?_⟩
  rw [turnDet,old_arc_continuation D c e he,hva,hvb,turnDet]
  simp only [planarDet,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

/-- No new right turn is created at an old retained corner. -/
theorem old_turn_nonnegative_iff (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : Fin D.nArc) (he : ∀ i : Fin 2, e ≠ D.incoming c i) :
    0 ≤ turnDet (smoothCrossing D c) (smoothArcEquiv D (Sum.inl e)) ↔
      0 ≤ turnDet D e := by
  obtain ⟨a,ha,h⟩ := old_turn_positive_multiple D c e he
  rw [h]
  exact mul_nonneg_iff_of_pos_left ha

/-- Straight subdivisions remain straight, and old genuine left turns remain left. -/
theorem old_turn_positive_iff (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : Fin D.nArc) (he : ∀ i : Fin 2, e ≠ D.incoming c i) :
    0 < turnDet (smoothCrossing D c) (smoothArcEquiv D (Sum.inl e)) ↔
      0 < turnDet D e := by
  obtain ⟨a,ha,h⟩ := old_turn_positive_multiple D c e he
  rw [h]
  exact mul_pos_iff_of_pos_left ha

end DirectGLSSW.HOMFLY.SmoothingCornerGeometry
