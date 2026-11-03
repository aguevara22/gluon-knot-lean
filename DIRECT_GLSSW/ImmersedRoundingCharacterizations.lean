import ImmersedTangentLift

set_option autoImplicit false
namespace DirectGLSSW.ImmersedGlobalRounding
open DirectGLSSW.HOMFLY.PrincipalTurning DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.ImmersedPolygonRotation

theorem cell_formula (c v w : ℂ) (δ : RoundingFraction) (t : ℝ) :
    cell c v w δ t = if t ≤ 2*δ.val then
      c + δ.val • ((-((1-t/(2*δ.val))^2)) • v + (t/(2*δ.val))^2 • w)
    else c+(t-δ.val) • w := by
  have hp : 0 < 2*δ.val := mul_pos (by norm_num) δ.property.1
  have hiff : t/(2*δ.val) ≤ 1 ↔ t ≤ 2*δ.val := by
    rw [div_le_iff₀ hp,one_mul]
  unfold cell step
  simp only [hiff]
  split_ifs
  · rfl
  · unfold straight
    rw [smul_smul,add_assoc,← add_smul]
    have h : δ.val+(t/(2*δ.val)-1)*(2*δ.val) = t-δ.val := by
      field_simp [ne_of_gt δ.property.1]
      <;> ring
    rw [h]

theorem velocity_formula (v w : ℂ) (δ : RoundingFraction) (t : ℝ) :
    velocity v w δ t = if t ≤ 2*δ.val then
      (1-t/(2*δ.val)) • v + (t/(2*δ.val)) • w else w := by
  have hp : 0 < 2*δ.val := mul_pos (by norm_num) δ.property.1
  have hiff : t/(2*δ.val) ≤ 1 ↔ t ≤ 2*δ.val := by rw [div_le_iff₀ hp,one_mul]
  have hc : (1/(2*δ.val))*(2*δ.val)=1 := by field_simp
  unfold velocity stepVelocity
  simp only [hiff]
  split_ifs <;> simp only [cornerVelocity,smul_smul,hc,one_smul]

theorem cellAngle_mem_open_semicircle (v w : ℂ)
    (hshort : w/v ∈ Complex.slitPlane) (δ : RoundingFraction) (t : ℝ) :
    -Real.pi < cellAngle v w δ t ∧ cellAngle v w δ t < Real.pi := by
  have h := relative_tangent_mem_slitPlane _ hshort (min 1 (max 0 (t/(2*δ.val))))
    ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩
  exact ⟨Complex.neg_pi_lt_arg _,lt_of_le_of_ne (Complex.arg_le_pi _)
    (Complex.slitPlane_arg_ne_pi h)⟩

theorem originalCornerTurn_mem_open_semicircle {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hshort : ∀ i, polygonEdgeVector q i / incoming q i ∈ Complex.slitPlane) (i : Fin n) :
    -Real.pi < originalCornerTurn q i ∧ originalCornerTurn q i < Real.pi :=
  ⟨Complex.neg_pi_lt_arg _,lt_of_le_of_ne (Complex.arg_le_pi _)
    (Complex.slitPlane_arg_ne_pi (hshort i))⟩

end DirectGLSSW.ImmersedGlobalRounding




