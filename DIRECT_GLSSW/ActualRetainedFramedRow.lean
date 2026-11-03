import SharpRetainedNext
import SharpRetainedFramedRow
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge
  SmoothingCornerGeometry Coefficients PrincipalTurning
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))

/-- The actual geometric incoming order discharges the last comparison input.
The empty crossing case is included in the evaluator comparison. -/
theorem sharp_retained_evaluator_eq
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H) :
    H (historicalSharpDiagram q hq h c hc R)
        (historicalSharpDiagram_nArc_pos q hq h c hc R) =
      H (historicalRetainedDiagram q hq h c hc R he hAux)
        (historicalRetainedDiagram_nArc_pos q hq he h c hc R hAux) :=
  sharp_retained_evaluator_eq_of_next q hq he h c hc R hAux H hH
    (historicalSharpRetainedIncoming_next_eq q hq h c hc R he hAux)

/-- Exact evaluator comparison for the detached component after an arbitrary
marked parent history and the literal retained polygon. -/
theorem detached_retained_evaluator_eq
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H) :
    H R.diagram R.nonempty =
      H (historicalRetainedDiagram q hq h c hc R he hAux)
        (historicalRetainedDiagram_nArc_pos q hq he h c hc R hAux) :=
  (historicalSharpEvaluator_eq q hq h c hc R H hH).trans
    (sharp_retained_evaluator_eq q hq he h c hc R hAux H hH)

theorem detached_retained_candidateEvaluator_eq :
    Gemini.candidateEvaluator R.diagram R.nonempty =
      Gemini.candidateEvaluator (historicalRetainedDiagram q hq h c hc R he hAux)
        (historicalRetainedDiagram_nArc_pos q hq he h c hc R hAux) :=
  detached_retained_evaluator_eq q hq he h c hc R hAux Gemini.candidateEvaluator
    (Gemini.candidateEvaluator_isNormalized Gemini.all_lowerCrossingEvaluatorSkeinIH)

/-- The existing framed row of the actual detached component equals that of
its retained polygon, including its original signed writhe and rotation. -/
theorem detached_retained_framedRow_eq (C : diagramComponent R.diagram)
    (E : diagramComponent (historicalRetainedDiagram q hq h c hc R he hAux)) :
    framedKnotRow Gemini.candidateEvaluator R.diagram R.nonempty C =
      framedKnotRow Gemini.candidateEvaluator (historicalRetainedDiagram q hq h c hc R he hAux)
        (historicalRetainedDiagram_nArc_pos q hq he h c hc R hAux) E :=
  detached_retained_framedRow_of_evaluator_eq q hq he h c hc R hAux Gemini.candidateEvaluator
    (detached_retained_candidateEvaluator_eq q hq he h c hc R hAux) C E

/-- Concrete nonempty component labels are produced, not required from the caller. -/
theorem detached_retained_framedRow_actual :
    framedKnotRow Gemini.candidateEvaluator R.diagram R.nonempty
      (componentOf R.diagram.continuation ⟨0,R.nonempty⟩) =
      framedKnotRow Gemini.candidateEvaluator (historicalRetainedDiagram q hq h c hc R he hAux)
        (historicalRetainedDiagram_nArc_pos q hq he h c hc R hAux)
        (componentOf (historicalRetainedDiagram q hq h c hc R he hAux).continuation
          ⟨0,historicalRetainedDiagram_nArc_pos q hq he h c hc R hAux⟩) :=
  detached_retained_framedRow_eq q hq he h c hc R hAux _ _

#check @detached_retained_evaluator_eq
#check @detached_retained_framedRow_actual





end DirectGLSSW.HOMFLY.ProcessedExposedChild
