import ImmersedTurnPrimitive
import ImmersedCellAngle

set_option autoImplicit false
namespace DirectGLSSW.ImmersedGlobalRounding
open DirectGLSSW.HOMFLY.PrincipalTurning DirectGLSSW.HOMFLY.PolygonDrawingBridge

noncomputable def arcAngle {n : ℕ} (q : Fin n → PlanarPoint ℝ) (base : Fin n) (k : ℤ) : ℝ :=
  (incoming q base).arg + turnPrimitive q base k

theorem incoming_phase_succ {n : ℕ} (q : Fin n → PlanarPoint ℝ) (base : Fin n) (k : ℤ) :
    incoming q (phase base (k+1)) = polygonEdgeVector q (phase base k) := by
  rw [phase_succ]
  simp only [incoming,Equiv.symm_apply_apply]

theorem cornerTurn_coe {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0) (i : Fin n) :
    (originalCornerTurn q i : Real.Angle) =
      ((polygonEdgeVector q i).arg : Real.Angle) - ((incoming q i).arg : Real.Angle) :=
  Complex.arg_div_coe_angle (hedge _) (hedge _)

theorem arcAngle_succ {n : ℕ} (q : Fin n → PlanarPoint ℝ) (base : Fin n) (k : ℤ) :
    arcAngle q base (k+1) = arcAngle q base k + originalCornerTurn q (phase base k) := by
  unfold arcAngle
  rw [turnPrimitive_succ]
  ring

theorem arcAngle_coe {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0) (base : Fin n) (k : ℤ) :
    (arcAngle q base k : Real.Angle) = ((incoming q (phase base k)).arg : Real.Angle) := by
  refine Int.inductionOn' k 0 ?_ ?_ ?_
  · simp [arcAngle,turnPrimitive_zero,phase]
  · intro j hj ih
    rw [arcAngle_succ,Real.Angle.coe_add,ih,cornerTurn_coe q hedge,incoming_phase_succ]
    abel
  · intro j hj ih
    have hs : arcAngle q base (j-1) = arcAngle q base j - originalCornerTurn q (phase base (j-1)) := by
      have h := arcAngle_succ q base (j-1)
      simp only [sub_add_cancel] at h
      linarith
    have hout : polygonEdgeVector q (phase base (j-1)) = incoming q (phase base j) := by
      simpa using (incoming_phase_succ q base (j-1)).symm
    rw [hs,Real.Angle.coe_sub,ih,cornerTurn_coe q hedge,hout]
    abel

noncomputable def tangentLift {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (base : Fin n) (δ : RoundingFraction) (t : ℝ) : ℝ :=
  arcAngle q base (Int.floor t) + cellAngle (incoming q (phase base (Int.floor t)))
    (polygonEdgeVector q (phase base (Int.floor t))) δ (Int.fract t)

theorem tangentLift_continuous {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hshort : ∀ i, polygonEdgeVector q i / incoming q i ∈ Complex.slitPlane)
    (base : Fin n) (δ : RoundingFraction) : Continuous (tangentLift q base δ) := by
  apply continuous_integer_cells (fun k t => arcAngle q base k +
    cellAngle (incoming q (phase base k)) (polygonEdgeVector q (phase base k)) δ t)
  · intro k
    exact continuous_const.add (cellAngle_continuous _ _ (hshort _) δ)
  · intro k
    rw [(cellAngle_endpoints _ _ δ).2,(cellAngle_endpoints _ _ δ).1,add_zero]
    have h := arcAngle_succ q base (k-1)
    simp only [sub_add_cancel] at h
    exact h.symm

theorem tangentLift_coe {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i / incoming q i ∈ Complex.slitPlane)
    (base : Fin n) (δ : RoundingFraction) (t : ℝ) :
    (tangentLift q base δ t : Real.Angle) = ((curveVelocity q base δ t).arg : Real.Angle) := by
  rw [tangentLift,Real.Angle.coe_add,arcAngle_coe q hedge]
  exact cellAngle_velocity _ _ (hedge _) (hedge _) (hshort _) δ _
    ⟨Int.fract_nonneg t,(Int.fract_lt_one t).le⟩

theorem tangentLift_int {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (base : Fin n) (δ : RoundingFraction) (k : ℤ) :
    tangentLift q base δ k = arcAngle q base k := by
  simp only [tangentLift,Int.floor_intCast,Int.fract_intCast,
    (cellAngle_endpoints _ _ δ).1,add_zero]

theorem tangentLift_period_increment {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (base : Fin n) (δ : RoundingFraction) :
    tangentLift q base δ n - tangentLift q base δ 0 = originalCornerTotalTurn q := by
  have hn := tangentLift_int q base δ (n:ℤ)
  have h0 := tangentLift_int q base δ 0
  simp only [Int.cast_natCast] at hn
  simp only [Int.cast_zero] at h0
  rw [hn,h0,arcAngle,arcAngle,turnPrimitive_zero,turnPrimitive_period]
  ring

theorem tangentLift_shift {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i / incoming q i ∈ Complex.slitPlane)
    (base : Fin n) (δ : RoundingFraction) (t : ℝ) :
    tangentLift q base δ (t+n) - tangentLift q base δ t = originalCornerTotalTurn q := by
  have hc := tangentLift_continuous q hshort base δ
  have hf := hc.comp (continuous_id.add (continuous_const : Continuous (fun _ : ℝ => (n:ℝ))))
  have heq : ∀ x : ℝ, (tangentLift q base δ (x+n) : Real.Angle) =
      (tangentLift q base δ x : Real.Angle) := by
    intro x
    rw [tangentLift_coe q hedge hshort,tangentLift_coe q hedge hshort,
      curveVelocity_periodic q base δ x]
  have h := continuous_angle_lifts_sub_constant
    (fun x : ℝ => tangentLift q base δ (x+n)) (tangentLift q base δ) hf hc heq t 0
  simp only [zero_add] at h
  exact h.trans (tangentLift_period_increment q base δ)

theorem any_tangent_lift_increment {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i / incoming q i ∈ Complex.slitPlane)
    (base : Fin n) (δ : RoundingFraction)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hangle : ∀ t, (f t : Real.Angle) = ((curveVelocity q base δ t).arg : Real.Angle)) :
    f n - f 0 = originalCornerTotalTurn q := by
  have heq : ∀ t, (f t : Real.Angle) = (tangentLift q base δ t : Real.Angle) := by
    intro t
    rw [hangle t,tangentLift_coe q hedge hshort]
  have h := continuous_angle_lifts_sub_constant f (tangentLift q base δ) hf
    (tangentLift_continuous q hshort base δ) heq n 0
  have hinc := tangentLift_period_increment q base δ
  linarith

end DirectGLSSW.ImmersedGlobalRounding




