import DirectGLSSW.RealPolygons
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DirectGLSSW.TruncationRescaling

open DirectGLSSW

theorem previous_point_rescaling (A P : PlanarPoint ℝ) (α ε : ℝ) (hα : α ≠ 0) :
    A + (ε / α) • (A + α • (P - A) - A) = A + ε • (P - A) := by
  ext <;> simp [smul_eq_mul] <;> field_simp [hα] <;> ring

theorem next_point_rescaling (A N : PlanarPoint ℝ) (α β scale ε : ℝ)
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    A + ((ε / α) * (scale * α / β)) • (A + β • (N - A) - A) =
      A + (ε * scale) • (N - A) := by
  ext <;> simp [smul_eq_mul] <;> field_simp [hα, hβ] <;> ring

theorem daughter_direction_rescaling (A P N : PlanarPoint ℝ) (α β scale : ℝ)
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    (scale * α / β) • (A + β • (N - A) - A) - (A + α • (P - A) - A) =
      α • (scale • (N - A) - (P - A)) := by
  ext <;> simp [smul_eq_mul] <;> field_simp [hβ] <;> ring

theorem daughter_turn_positive (A P N : PlanarPoint ℝ) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hturn : 0 < planarDet (A - P) (N - A)) :
    0 < planarDet
      (A - (A + α • (P - A)))
      ((A + β • (N - A)) - A) := by
  have hdet : planarDet (A - (A + α • (P - A))) ((A + β • (N - A)) - A) =
      (α * β) * planarDet (A - P) (N - A) := by
    simp [planarDet, smul_eq_mul]
    ring
  rw [hdet]
  exact mul_pos (mul_pos hα hβ) hturn

theorem daughter_direction_det_ne_zero (A P N X : PlanarPoint ℝ)
    (α β scale : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hdet : planarDet (scale • (N - A) - (P - A)) (X - A) ≠ 0) :
    planarDet
      ((scale * α / β) • (A + β • (N - A) - A) - (A + α • (P - A) - A))
      (X - A) ≠ 0 := by
  rw [daughter_direction_rescaling A P N α β scale hα hβ]
  have hscale : planarDet (α • (scale • (N - A) - (P - A))) (X - A) =
      α * planarDet (scale • (N - A) - (P - A)) (X - A) := by
    simp [planarDet, smul_eq_mul]
    ring
  rw [hscale]
  exact mul_ne_zero hα hdet

end DirectGLSSW.TruncationRescaling
