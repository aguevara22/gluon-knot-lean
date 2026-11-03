import UniformPolygonPolynomial
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open PermutationOrbits LowestRowContract FramedPolynomial Coefficients PrincipalTurning
open GeometricSmoothingWeights ProcessedExposedChild SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

/-- Every actual detached state in the processed history has its polynomial
witness. No detached-child induction premise remains. -/
theorem uniform_detached_framed_polynomial
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : auxiliaryGenericity q hq)
    (u : MarkedParentState)
    (hu : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) u)
    (c : Fin u.1.nCrossing) (hc : badAt u.2.1 c) :
    ∃ F : Polynomial ℤ,
      framedKnotRow Gemini.candidateEvaluator (MarkedPolynomial.detached u c).diagram
        (MarkedPolynomial.detached u c).nonempty
        (componentOf (MarkedPolynomial.detached u c).diagram.continuation
          ⟨0,(MarkedPolynomial.detached u c).nonempty⟩) = framedVariable * polynomialValue F := by
  have hA := ActiveArc.ExposedChart.closedAuxiliary_of_parent q 0 hq he hAux
  let R := canonicalDetachedRestriction u c
  let Q := historicalSharpPolygon q hq hu c hc R
  obtain ⟨hQ,hlQ,hcount,heval,hrow⟩ := canonical_actual_recursive_child q hq hu c hc hleft he hA
  have hAuxQ : auxiliaryGenericity Q hQ := canonical_historical_child_auxiliaryGenericity q hq hu c hc he hA
  obtain ⟨F,hF⟩ := uniform_polygon_framed_polynomial hRI Q hQ hlQ hAuxQ
  exact ⟨F,hrow.trans hF⟩

/-- Actual parent polynomial along every finite source history, now with the
smaller-child induction discharged by the global polygon theorem. -/
theorem uniform_polygon_trace_polynomial
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : auxiliaryGenericity q hq)
    (u : MarkedParentState)
    (hu : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) u) :
    ∃ F : Polynomial ℤ,
      MarkedPolynomial.row u (MarkedPolynomial.trace_nonempty hu (positivePolygonEventDiagram_nArc_pos q hq)) =
        framedVariable * polynomialValue F :=
  MarkedPolynomial.exists_polynomial_of_detached_witnesses q hq he
    (uniform_detached_framed_polynomial hRI q hq hleft he hAux) u hu
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
