import DirectGLSSW.HOMFLY.HOMFLYSkeinPivotAlgebra
import DirectGLSSW.HOMFLY.HOMFLYSkeinEvaluator
import SmoothingComponentCount

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

open Coefficients

/-- The two source-convention pivot coefficients cancel against one extra
unlink component. -/
theorem pivot_unlink_factor (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    pivotSwitchFactor D c + pivotSmoothFactor D c * unlinkFactor = 1 := by
  have hskein : aMonomial * 1 - aInvMonomial * 1 = zMonomial * unlinkFactor := by
    rw [mul_one, mul_one, unlinkFactor]
    calc
      aMonomial - aInvMonomial = (aMonomial - aInvMonomial) * 1 := by rw [mul_one]
      _ = (aMonomial - aInvMonomial) * (zMonomial * zInvMonomial) := by
        rw [zMonomial_mul_zInvMonomial]
      _ = zMonomial * ((aMonomial - aInvMonomial) * zInvMonomial) := by ac_rfl
  cases hs : crossingSign D c with
  | pos =>
      have h := positive_skein_solve (1 : HOMFLYCoeff) 1 unlinkFactor hskein
      simpa [pivotSwitchFactor, pivotSmoothFactor, hs] using h.symm
  | neg =>
      have h := negative_skein_solve (1 : HOMFLYCoeff) 1 unlinkFactor hskein
      simpa [pivotSwitchFactor, pivotSmoothFactor, hs, sub_eq_add_neg, neg_mul] using h.symm

/-- At a self-smoothing, the two terminal unlink branches sum to the parent
unlink value. -/
theorem descendingUnlinkValue_self_pivot (D : PLLinkDiagram)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) :
    pivotSwitchFactor D c * descendingUnlinkValue (switchCrossing D c) +
      pivotSmoothFactor D c * descendingUnlinkValue (smoothCrossing D c) =
        descendingUnlinkValue D := by
  have hD : 0 < diagramComponentCount D := by
    unfold diagramComponentCount
    exact Fintype.card_pos_iff.mpr ⟨Quotient.mk _ (D.incoming c 0)⟩
  have hswitch : 0 < diagramComponentCount (switchCrossing D c) := by
    rw [switch_componentCount]
    exact hD
  have hSmoothCount := smooth_componentCount_self D c hself
  have hsmooth : 0 < diagramComponentCount (smoothCrossing D c) := by
    omega
  rw [descendingUnlinkValue_of_nonempty_components (switchCrossing D c) hswitch,
      descendingUnlinkValue_of_nonempty_components (smoothCrossing D c) hsmooth,
      descendingUnlinkValue_of_nonempty_components D hD,
      switch_componentCount, hSmoothCount]
  have hSmoothExponent : diagramComponentCount D + 1 - 1 = diagramComponentCount D := by omega
  rw [hSmoothExponent]
  have hParentExponent : diagramComponentCount D = (diagramComponentCount D - 1) + 1 := by
    omega
  rw [hParentExponent, pow_succ]
  calc
    pivotSwitchFactor D c * unlinkFactor ^ (diagramComponentCount D - 1) +
        pivotSmoothFactor D c * (unlinkFactor ^ (diagramComponentCount D - 1) * unlinkFactor) =
      (pivotSwitchFactor D c + pivotSmoothFactor D c * unlinkFactor) *
        unlinkFactor ^ (diagramComponentCount D - 1) := by ring
    _ = unlinkFactor ^ (diagramComponentCount D - 1) := by
      rw [pivot_unlink_factor]
      ring




end DirectGLSSW.HOMFLY
