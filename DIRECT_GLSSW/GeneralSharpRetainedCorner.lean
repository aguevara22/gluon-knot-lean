import GeneralSharpRetainedEvaluator
import SharpRetainedTurn
import SharpDaughterRotationInteger
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.GeneralSharpRetained
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge DaughterFirstReturn
  PrincipalTurning Coefficients
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
  (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
  (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
  (hroot : retainedCorner q S root)
  (hP : CyclicGeneric (daughterVertex q hq.g2 S root))

include hroot in
theorem turnInteger_eq :
    turnInteger (sharpDiagram q hq S root hNA) =
    turnInteger (retainedDiagram q hq S root hP) := by
  apply turnInteger_unique
  rw [sharpDaughter_totalTurn_eq_retainedPolygon q hq S hNA root hroot hP]
  exact totalTurn_eq_turnInteger _

include hroot in
theorem rotationInteger_eq :
    SharpDaughterRotation.sharpDaughterRotationInteger q hq S
      (componentOf (smoothingDartPermutation q hq.g2 S) root) hNA =
    turnInteger (retainedDiagram q hq S root hP) :=
  (SharpDaughterRotation.sharpDaughterRotationInteger_eq_turnInteger q hq S _ hNA).trans
    (turnInteger_eq q hq S root hNA hroot hP)

include hroot in
/-- The prescribed sharp corner coefficient equals the coefficient of the actual
retained polygon at the identical integer degree. No uniformity or RI premise. -/
theorem corner_coefficient
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H) :
    coeff (H (sharpDiagram q hq S root hNA) (SharpDaughter.arc_count_pos q hq S _ hNA))
      (1 - (sharpDiagram q hq S root hNA).nCrossing -
        |SharpDaughterRotation.sharpDaughterRotationInteger q hq S
          (componentOf (smoothingDartPermutation q hq.g2 S) root) hNA|) 0 =
    coeff (H (retainedDiagram q hq S root hP) (positivePolygonEventDiagram_nArc_pos _ hP))
      (1 - (retainedDiagram q hq S root hP).nCrossing -
        |turnInteger (retainedDiagram q hq S root hP)|) 0 := by
  rw [evaluator_eq q hq S root hNA hroot hP H hH,
    rotationInteger_eq q hq S root hNA hroot hP,
    crossing_count q hq S root hNA hroot hP]




end DirectGLSSW.HOMFLY.GeneralSharpRetained
