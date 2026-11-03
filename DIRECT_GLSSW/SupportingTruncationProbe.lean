import SupportingTruncationAuxiliary
set_option autoImplicit false
set_option pp.all true
set_option pp.proofs true
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open TruncationDirection ExposedOpenPrimitive Coefficients GeometricSmoothingWeights
attribute [local instance] Classical.propDecidable
theorem actual_supporting_truncation_application
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq) :
    ∃ a p : Fin n, cyclicSuccessor p = a ∧ ∃ scale : ℝ, 0 < scale ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        ε < 1 ∧ ε * scale < 1 ∧
        ∃ hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε),
        ∃ hAuxQ : auxiliaryGenericity (truncateCyclicCorner q a p scale ε) hQ,
          (∀ i, 0 < planarDet (cyclicTangent (truncateCyclicCorner q a p scale ε) i)
            (cyclicTangent (truncateCyclicCorner q a p scale ε) (cyclicSuccessor i))) ∧
          LeftExposed (truncateCyclicCorner q a p scale ε) a.castSucc ∧
          polygonAmplitude (truncateCyclicCorner q a p scale ε) hQ = -polygonAmplitude q hq ∧
          separatingSmoothingSum (truncateCyclicCorner q a p scale ε) hQ hAuxQ =
            -separatingSmoothingSum q hq hAux ∧
          (-1 : ℚ)^(n+1) * separatingSmoothingSum (truncateCyclicCorner q a p scale ε) hQ hAuxQ =
            (-1 : ℚ)^n * separatingSmoothingSum q hq hAux ∧
          (positivePolygonEventDiagram q hq).nCrossing =
            (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ).nCrossing ∧
          PrincipalTurning.totalTurn
            (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ) =
            PrincipalTurning.totalTurn (positivePolygonEventDiagram q hq) ∧
          PrincipalTurning.turnInteger
            (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ) =
            PrincipalTurning.turnInteger (positivePolygonEventDiagram q hq) ∧
          Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
              (positivePolygonEventDiagram_nArc_pos q hq) =
            Gemini.candidateEvaluator (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ)
              (positivePolygonEventDiagram_nArc_pos _ hQ) ∧
          coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
              (positivePolygonEventDiagram_nArc_pos q hq))
              (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
                |PrincipalTurning.turnInteger (positivePolygonEventDiagram q hq)|) 0 =
            coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ)
              (positivePolygonEventDiagram_nArc_pos _ hQ))
              (1-((positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ).nCrossing : ℤ)-
                |PrincipalTurning.turnInteger (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ)|) 0 := by
  exact exists_supporting_truncation_preserves_nu_and_corner hRI q hq hleft hAux

#check @DirectGLSSW.TruncationDirection.exists_strict_support_vertex
#check @DirectGLSSW.TruncationDirection.positive_scale_of_strict_support
#check @DirectGLSSW.TruncationDirection.exists_supporting_left_corner_scale
#check @DirectGLSSW.TruncationDirection.exists_small_truncation_leftExposed
#check @DirectGLSSW.TruncationDirection.strict_support_event_avoidance
#check @DirectGLSSW.TruncationDaughterUniform.exists_fixedScale_truncation_all_affected_amplitudes
#check @DirectGLSSW.HOMFLY.PolygonDrawingBridge.exists_supporting_truncation_knot_family
#check @DirectGLSSW.HOMFLY.PolygonDrawingBridge.exists_supporting_truncation_preserves_nu_and_corner
#check @DirectGLSSW.HOMFLY.PolygonDrawingBridge.actual_supporting_truncation_application
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
