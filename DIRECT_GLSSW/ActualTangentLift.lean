import NormalizedCellAngle
import AngleLiftUniqueness

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open DirectGLSSW.PermutationOrbits

noncomputable def orbitArcAngle (D : PLLinkDiagram) (e : Fin D.nArc) (k : ℤ) : ℝ :=
  (arcVector D e).arg + orbitTurningPrimitive D e k

theorem orbitArcAngle_coe (D : PLLinkDiagram) (e : Fin D.nArc) (k : ℤ) :
    (orbitArcAngle D e k : Real.Angle) =
      ((arcVector D ((D.continuation ^ k) e)).arg : Real.Angle) := by
  refine Int.inductionOn' k 0 ?_ ?_ ?_
  · simp [orbitArcAngle, orbitTurningPrimitive_zero]
  · intro j hj ih
    have hs : orbitArcAngle D e (j + 1) =
        orbitArcAngle D e j + turn D ((D.continuation ^ j) e) := by
      unfold orbitArcAngle
      rw [orbitTurningPrimitive_succ]
      ring
    have hc : D.continuation ((D.continuation ^ j) e) = (D.continuation ^ (j + 1)) e := by
      simpa only [add_sub_cancel_right] using continuation_previous_integer D e (j + 1)
    have ht := turn_coe_angle D ((D.continuation ^ j) e)
    rw [hc] at ht
    rw [hs, Real.Angle.coe_add, ih, ht]
    abel
  · intro j hj ih
    have hs : orbitArcAngle D e (j - 1) =
        orbitArcAngle D e j - turn D ((D.continuation ^ (j - 1)) e) := by
      unfold orbitArcAngle
      rw [orbitTurningPrimitive_pred D e j hj]
      ring
    have ht := turn_coe_angle D ((D.continuation ^ (j - 1)) e)
    rw [continuation_previous_integer] at ht
    rw [hs, Real.Angle.coe_sub, ih, ht]
    abel

/-- Literal unwrapped angle of the actual global rounded tangent. -/
noncomputable def actualTangentLift (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) : ℝ :=
  orbitArcAngle D e (Int.floor t) +
    normalizedCellAngle D ((D.continuation ^ Int.floor t) e) δ (Int.fract t)

theorem actualTangentLift_continuous (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) : Continuous (actualTangentLift D e δ) := by
  apply continuous_integer_cells
    (fun k t => orbitArcAngle D e k + normalizedCellAngle D ((D.continuation ^ k) e) δ t)
  · intro k
    exact continuous_const.add (normalizedCellAngle_continuous D _ δ)
  · intro k
    rw [(normalizedCellAngle_endpoints D _ δ).2, (normalizedCellAngle_endpoints D _ δ).1, add_zero]
    have h := orbitTurningPrimitive_succ D e (k - 1)
    simp only [sub_add_cancel] at h
    unfold orbitArcAngle
    linarith

theorem actualTangentLift_coe (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) :
    (actualTangentLift D e δ t : Real.Angle) =
      ((roundedComponentVelocity D e δ t).arg : Real.Angle) := by
  rw [actualTangentLift, Real.Angle.coe_add, orbitArcAngle_coe]
  exact normalizedCellAngle_actual_tangent D _ δ _
    ⟨Int.fract_nonneg t,(Int.fract_lt_one t).le⟩

theorem actualTangentLift_int (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (k : ℤ) :
    actualTangentLift D e δ k = orbitArcAngle D e k := by
  simp only [actualTangentLift, Int.floor_intCast, Int.fract_intCast,
    (normalizedCellAngle_endpoints D _ δ).1, add_zero]

theorem actualTangentLift_period_increment (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) :
    actualTangentLift D e δ (componentArcLength D e) - actualTangentLift D e δ 0 =
      componentTotalTurn D (componentOf D.continuation e) := by
  have hn := actualTangentLift_int D e δ (componentArcLength D e : ℤ)
  have h0 := actualTangentLift_int D e δ 0
  simp only [Int.cast_zero] at h0
  rw [Int.cast_natCast] at hn
  rw [hn, h0, orbitArcAngle, orbitArcAngle, orbitTurningPrimitive_zero]
  simpa only [add_zero, add_sub_cancel_left] using orbitTurningPrimitive_component_period D e

/-- The increment is independent of the chosen continuous actual tangent lift. -/
theorem any_actual_tangent_lift_increment (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (f : ℝ → ℝ) (hf : Continuous f)
    (hangle : ∀ t, (f t : Real.Angle) = ((roundedComponentVelocity D e δ t).arg : Real.Angle)) :
    f (componentArcLength D e) - f 0 = componentTotalTurn D (componentOf D.continuation e) := by
  have heq : ∀ t, (f t : Real.Angle) = (actualTangentLift D e δ t : Real.Angle) :=
    fun t => (hangle t).trans (actualTangentLift_coe D e δ t).symm
  have h := continuous_angle_lifts_same_increment f (actualTangentLift D e δ) hf
    (actualTangentLift_continuous D e δ) heq 0 (componentArcLength D e)
  simp only [zero_add] at h
  exact h.trans (actualTangentLift_period_increment D e δ)

/-- The actual rounded tangent has a unique integer degree, obtained from
continuous lifts of its literal nonzero derivative, not an assumed rotation. -/
theorem actualTangentDegree_existsUnique (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) :
    ∃! r : ℤ, ∃ f : ℝ → ℝ, Continuous f ∧
      (∀ t, (f t : Real.Angle) = ((roundedComponentVelocity D e δ t).arg : Real.Angle)) ∧
      f (componentArcLength D e) - f 0 = (r : ℝ) * (2 * Real.pi) := by
  refine ⟨componentTurnInteger D (componentOf D.continuation e), ?_, ?_⟩
  · refine ⟨actualTangentLift D e δ, actualTangentLift_continuous D e δ,
      actualTangentLift_coe D e δ, ?_⟩
    rw [actualTangentLift_period_increment, componentTotalTurn_eq_integer]
  · intro r hr
    obtain ⟨f,hf,ha,hi⟩ := hr
    have h := any_actual_tangent_lift_increment D e δ f hf ha
    have hs : componentTotalTurn D (componentOf D.continuation e) =
        (r : ℝ) * (2 * Real.pi) := h.symm.trans hi
    exact (Classical.choose_spec (existsUnique_componentTurnInteger D (componentOf D.continuation e))).2 r hs

end DirectGLSSW.HOMFLY.PrincipalTurning






