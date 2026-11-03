import UniformPolynomialSetup
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open PermutationOrbits LowestRowContract FramedPolynomial Coefficients PrincipalTurning ProcessedExposedChild
open GeometricSmoothingWeights SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

/-- The outer induction hypothesis is consumed only on actual smaller canonical
retained children; every child geometry and AUX premise is produced. -/
theorem exposed_uniform_polynomial_of_smaller
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : auxiliaryGenericity q hq)
    (ih : ∀ {m : ℕ} (Q : Fin m → PlanarPoint ℝ) (hQ : CyclicGeneric Q),
      (∀ i, 0 < planarDet (cyclicTangent Q i) (cyclicTangent Q (cyclicSuccessor i))) →
      auxiliaryGenericity Q hQ →
      (positivePolygonEventDiagram Q hQ).nCrossing < (positivePolygonEventDiagram q hq).nCrossing →
      ∃ F : Polynomial ℤ,
        framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram Q hQ)
          (positivePolygonEventDiagram_nArc_pos _ _)
          (componentOf (positivePolygonEventDiagram Q hQ).continuation ⟨0,positivePolygonEventDiagram_nArc_pos _ _⟩) =
        framedVariable * polynomialValue F) :
    ∃ F : Polynomial ℤ,
      framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos _ _)
        (componentOf (positivePolygonEventDiagram q hq).continuation ⟨0,positivePolygonEventDiagram_nArc_pos _ _⟩) =
      framedVariable * polynomialValue F := by
  have hA := ActiveArc.ExposedChart.closedAuxiliary_of_parent q 0 hq he hAux
  have hchild : ∀ (u : MarkedParentState)
      (hu : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) u)
      (c : Fin u.1.nCrossing), badAt u.2.1 c →
      ∃ F : Polynomial ℤ,
        framedKnotRow Gemini.candidateEvaluator (MarkedPolynomial.detached u c).diagram
          (MarkedPolynomial.detached u c).nonempty
          (componentOf (MarkedPolynomial.detached u c).diagram.continuation
            ⟨0,(MarkedPolynomial.detached u c).nonempty⟩) = framedVariable * polynomialValue F := by
    intro u hu c hc
    let R := canonicalDetachedRestriction u c
    let Q := historicalSharpPolygon q hq hu c hc R
    obtain ⟨hQ,hleftQ,hcount,heval,hrow⟩ := canonical_actual_recursive_child q hq hu c hc hleft he hA
    have hAuxQ : auxiliaryGenericity Q hQ :=
      canonical_historical_child_auxiliaryGenericity q hq hu c hc he hA
    have hdrop : (positivePolygonEventDiagram Q hQ).nCrossing < (positivePolygonEventDiagram q hq).nCrossing :=
      lt_of_lt_of_le hcount hu.nCrossing_le
    obtain ⟨F,hF⟩ := ih Q hQ hleftQ hAuxQ hdrop
    refine ⟨F,?_⟩
    exact hrow.trans hF
  obtain ⟨F,hF,hfloor,hcorner⟩ := exposedPolygon_corner_of_detached_polynomials q hq hleft he hchild
  exact ⟨F,hF⟩
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
