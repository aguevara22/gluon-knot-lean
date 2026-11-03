import ReversalContract.Contract
import UniformLeftIdentity
import TurnSignLiteralBridge
import UniformCornerReconstruction

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.GeminiReversalConsumerPrep
open DirectGLSSW GeometricSmoothingWeights PolygonUniformity
  GeminiReversalContract PhysicalCursorComparison
  SmoothingTurnCount UniformCornerReconstruction Coefficients Gemini
  PolygonDrawingBridge PrincipalTurning
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Accepted left identity plus the exact raw reversal reduction prove the
ordinary-polygon gate for every PolygonUniform polygon. -/
theorem polygon_uniform_identity_of_right_reduction
    (hRI : GLSSWRootIndependence)
    (hRightReduction : ∀ (hRI : GLSSWRootIndependence) {n : ℕ}
      (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (hAux : auxiliaryGenericity q hq) (hRight : StrictRight q)
      (hLeftIdentity : ∀ (p : Fin n → PlanarPoint ℝ) (hp : CyclicGeneric p)
        (hAuxP : auxiliaryGenericity p hp), StrictLeft p →
          normalizedPrimitive p hp hAuxP = (prescribedCorner p hp : ℚ)),
      normalizedPrimitive q hq hAux = (prescribedCorner q hq : ℚ)) :
    ∀ {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (hAux : auxiliaryGenericity q hq), PolygonUniform q →
      (-1 : ℚ) ^ SmoothingTurnCount.leftTurnCount q *
        separatingSmoothingSum q hq hAux =
          (coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
            (positivePolygonEventDiagram_nArc_pos q hq))
            (1 - (positivePolygonEventDiagram q hq).nCrossing -
              |turnInteger (positivePolygonEventDiagram q hq)|) 0 : ℚ) := by
  intro n q hq hAux hUniform
  have hLeftIdentity : ∀ {m : ℕ} (p : Fin m → PlanarPoint ℝ) (hp : CyclicGeneric p)
      (hAuxP : auxiliaryGenericity p hp), StrictLeft p →
        normalizedPrimitive p hp hAuxP = (prescribedCorner p hp : ℚ) := by
    intro m p hp hAuxP hleft
    have h := PhysicalCursorComparison.uniform_left_primitive_corner_identity
      hRI p hp hleft hAuxP
    simpa [GeminiReversalContract.normalizedPrimitive, GeminiReversalContract.leftCount,
      GeminiReversalContract.prescribedCorner] using h
  rcases hUniform with hleft | hright
  · have hstrict : StrictLeft q := by
      intro e
      simpa only [PolygonUniformity.turnDet_successor] using hleft (cyclicSuccessor e)
    have h := hLeftIdentity q hq hAux hstrict
    simpa [GeminiReversalContract.normalizedPrimitive, GeminiReversalContract.leftCount,
      GeminiReversalContract.prescribedCorner,
      ← SmoothingTurnCount.leftTurnCount_eq_literal_filter_card q] using h
  · have hstrict : StrictRight q := by
      intro e
      simpa only [PolygonUniformity.turnDet_successor] using hright (cyclicSuccessor e)
    have h := hRightReduction hRI q hq hAux hstrict hLeftIdentity
    simpa [GeminiReversalContract.normalizedPrimitive, GeminiReversalContract.leftCount,
      GeminiReversalContract.prescribedCorner,
      ← SmoothingTurnCount.leftTurnCount_eq_literal_filter_card q] using h

/-- Exact final assembly application with the raw reversal obligation exposed
as the only remaining input. -/
theorem candidate_corner_state_sum_of_right_reduction
    (hRI : GLSSWRootIndependence)
    (hRightReduction : ∀ (hRI : GLSSWRootIndependence) {n : ℕ}
      (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (hAux : auxiliaryGenericity q hq) (hRight : StrictRight q)
      (hLeftIdentity : ∀ (p : Fin n → PlanarPoint ℝ) (hp : CyclicGeneric p)
        (hAuxP : auxiliaryGenericity p hp), StrictLeft p →
          normalizedPrimitive p hp hAuxP = (prescribedCorner p hp : ℚ)),
      normalizedPrimitive q hq hAux = (prescribedCorner q hq : ℚ))
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    polygonAmplitude q hq =
      (CornerStateSumLocality.cornerStateSum Gemini.candidateEvaluator q hq : ℚ) := by
  exact UniformCornerReconstruction.candidate_corner_state_sum_of_uniform_identity
    hRI (polygon_uniform_identity_of_right_reduction hRI hRightReduction) q hq



end DirectGLSSW.HOMFLY.GeminiReversalConsumerPrep
