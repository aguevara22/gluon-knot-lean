import PolygonPolynomialCorner
import MarkedParentPolynomial

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open PermutationOrbits LowestRowContract FramedPolynomial Coefficients PrincipalTurning

/-- The actual parent recursion supplies the polynomial witness needed by the
literal prescribed coefficient calculation. Only its smaller detached-child
induction premise remains. -/
theorem exposedPolygon_corner_of_detached_polynomials
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ e : Fin (n+2), 0 < planarDet (cyclicTangent q e)
      (cyclicTangent q (cyclicSuccessor e)))
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hchild : ∀ (u : MarkedParentState)
      (hu : MarkedParentTrace ⟨positivePolygonEventDiagram q hq,initialAnchorTraversal q hq,
        ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩ u)
      (c : Fin u.1.nCrossing), badAt u.2.1 c →
      ∃ F : Polynomial ℤ,
        framedKnotRow Gemini.candidateEvaluator (MarkedPolynomial.detached u c).diagram
          (MarkedPolynomial.detached u c).nonempty
          (componentOf (MarkedPolynomial.detached u c).diagram.continuation
            ⟨0,(MarkedPolynomial.detached u c).nonempty⟩) = framedVariable * polynomialValue F) :
    ∃ F : Polynomial ℤ,
      framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos q hq)
        (componentOf (positivePolygonEventDiagram q hq).continuation
          ⟨0,positivePolygonEventDiagram_nArc_pos q hq⟩) = framedVariable * polynomialValue F ∧
      (∀ i : ℤ, i < 1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
        |turnInteger (positivePolygonEventDiagram q hq)| →
        coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
          (positivePolygonEventDiagram_nArc_pos q hq)) i 0 = 0) ∧
      coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos q hq))
        (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
          |turnInteger (positivePolygonEventDiagram q hq)|) 0 = F.eval (-1) := by
  let s : MarkedParentState := ⟨positivePolygonEventDiagram q hq,initialAnchorTraversal q hq,
    ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩
  obtain ⟨F,hF⟩ := MarkedPolynomial.exists_polynomial_of_detached_witnesses
    q hq he hchild s (.nil s)
  change framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
    (positivePolygonEventDiagram_nArc_pos q hq)
    (componentOf (positivePolygonEventDiagram q hq).continuation
      ⟨0,positivePolygonEventDiagram_nArc_pos q hq⟩) = framedVariable * polynomialValue F at hF
  exact ⟨F,hF,positivePolygon_polynomialWitness_corner q hq hleft F hF⟩

#check @positivePolygon_polynomialWitness_corner
#check @exposedPolygon_corner_of_detached_polynomials

end DirectGLSSW.HOMFLY.PolygonDrawingBridge
