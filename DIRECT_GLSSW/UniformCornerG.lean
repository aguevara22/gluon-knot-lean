import UniformMarkedTracePolynomial
import MarkedGRecursion

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY
open Coefficients LowestRowContract PrincipalTurning PermutationOrbits FramedPolynomial
open GeometricSmoothingWeights SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

namespace PolygonDrawingBridge

/-- The full initial lowest-row conclusion, with the polynomial witness,
positive crossing signs and nonnegative rotation all proved internally. -/
theorem uniform_polygon_corner_evaluation
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i)
      (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq) :
    ∃ F : Polynomial ℤ,
      framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos q hq)
        (componentOf (positivePolygonEventDiagram q hq).continuation
          ⟨0,positivePolygonEventDiagram_nArc_pos q hq⟩) = framedVariable * polynomialValue F ∧
      aPower (((positivePolygonEventDiagram q hq).nCrossing : ℤ) +
        |turnInteger (positivePolygonEventDiagram q hq)| - 1) *
        zRow (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
          (positivePolygonEventDiagram_nArc_pos q hq)) 0 = polynomialValue F ∧
      (∀ i : ℤ, i < 1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
        |turnInteger (positivePolygonEventDiagram q hq)| →
        coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
          (positivePolygonEventDiagram_nArc_pos q hq)) i 0 = 0) ∧
      coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos q hq))
        (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
          |turnInteger (positivePolygonEventDiagram q hq)|) 0 = F.eval (-1) ∧
      -coeff (framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos q hq)
        (componentOf (positivePolygonEventDiagram q hq).continuation
          ⟨0,positivePolygonEventDiagram_nArc_pos q hq⟩)) 0 0 = F.eval (-1) := by
  obtain ⟨F,hF⟩ := uniform_polygon_framed_polynomial hRI q hq hleft hAux
  let D := positivePolygonEventDiagram q hq
  let e : Fin D.nArc := ⟨0,positivePolygonEventDiagram_nArc_pos q hq⟩
  let C := componentOf D.continuation e
  have hr := componentTurnInteger_nonneg_of_turnDet D
    (positivePolygonEventDiagram_turn_nonneg_of_uniform_left q hq hleft) C
  have htotal : componentTotalTurn D C = totalTurn D :=
    (positivePolygonEventDiagram_componentTotalTurn q hq e).trans
      (positivePolygonEventDiagram_totalTurn q hq).symm
  have hi : componentTurnInteger D C = turnInteger D := by
    apply (turnInteger_unique D _ _).symm
    rw [← htotal,componentTotalTurn_eq_integer]
  have hw : diagramWrithe D = (D.nCrossing : ℤ) := by
    simp [diagramWrithe,writheSign,D,positivePolygonEventDiagram_crossingSign]
  have ha : |turnInteger D| = componentTurnInteger D C := by
    rw [← hi,abs_of_nonneg hr]
  have hs := (framedKnotRow_polynomialWitness_corner
    Gemini.candidateEvaluator D (positivePolygonEventDiagram_nArc_pos q hq) C F hF).1
  have hc := positivePolygon_polynomialWitness_corner q hq hleft F hF
  refine ⟨F,hF,?_,hc.1,hc.2,negative_constant_of_polynomialWitness _ F hF⟩
  rw [hw,← ha] at hs
  exact hs

end PolygonDrawingBridge

namespace MarkedG
open PolygonDrawingBridge

/-- The actual subtraction recurrence after discharging the entire detached
polynomial induction. The explicit first-bad domain is the source traversal. -/
theorem uniform_recurrence
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i)
      (cyclicTangent q (cyclicSuccessor i)))
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : auxiliaryGenericity q hq)
    (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) (hgood : GoodBefore t c) :
    value t (MarkedPolynomial.trace_nonempty h (positivePolygonEventDiagram_nArc_pos q hq)) =
      value (switchedState t c hc hgood)
        (MarkedPolynomial.trace_nonempty (t := t) h (positivePolygonEventDiagram_nArc_pos q hq)) -
      value (continuingState t c hc hgood) (continuingRestriction t c).nonempty *
        detachedValue t c :=
  recurrence_of_detached_polynomials q hq he
    (uniform_detached_framed_polynomial hRI q hq hleft he hAux) t h c hc hgood

/-- Initial marked value is the literal prescribed corner without a supplied
polynomial witness or a detached-child induction premise. -/
theorem uniform_initial_value_eq_corner
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i)
      (cyclicTangent q (cyclicSuccessor i)))
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : auxiliaryGenericity q hq) :
    value (positivePolygonMarkedState q hq (initialAnchorTraversal q hq))
      (positivePolygonEventDiagram_nArc_pos q hq) =
    coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
      (positivePolygonEventDiagram_nArc_pos q hq))
      (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
        |turnInteger (positivePolygonEventDiagram q hq)|) 0 :=
  initial_value_eq_corner q hq he
    (uniform_detached_framed_polynomial hRI q hq hleft he hAux) hleft

end MarkedG



end DirectGLSSW.HOMFLY
