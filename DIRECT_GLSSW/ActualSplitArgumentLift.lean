import ClampedSimilarityData
import UnitLoopLiftExistence
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY

theorem exists_actual_split_argument_lift (D : PLLinkDiagram) (e : Fin D.nArc) :
    ∃ θ : C(unitInterval,ℝ), θ 0 = (clampedDifference D e 0).arg ∧
      (∀ t, (θ t : Real.Angle) = ((clampedDifference D e t).arg : Real.Angle)) ∧
      ∀ t : unitInterval, 0 < t.val → t.val < 1 →
        (θ t : Real.Angle) = ((splitMainComplex D e t - splitBeta D e t).arg : Real.Angle) := by
  obtain ⟨θ,hθ,hunique⟩ := PositionalIndex.existsUnique_unit_positional_lift
    (clampedDifference D e) 0 (clampedDifference_ne_zero D e)
  simp only [sub_zero] at hθ
  refine ⟨θ,hθ.1,hθ.2,?_⟩
  intro t ht0 ht1
  rw [clamped_difference_arg_eq D e t ht0 ht1]
  exact hθ.2 t

end DirectGLSSW.DescendingSpatial

