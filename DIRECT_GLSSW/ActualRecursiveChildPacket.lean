import HistoricalRetainedUniformLeft
import RetainedPolygonCrossingDescent
import ActualRetainedFramedRow

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.HOMFLY.ProcessedExposedChild

open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge
  SmoothingCornerGeometry Coefficients DaughterFirstReturn

attribute [local instance] Classical.propDecidable

variable {n : ℕ} (q : Fin (n + 2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace
      (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

/-- Actual recursive-child data for the same retained sharp polygon: its
genericity and strict turns, crossing descent, evaluator, and existing framed
row. The actual component restriction remains explicit. -/
theorem actual_recursive_child_packet
    (hleft : ∀ i : Fin (n + 2),
      0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary
      (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq)) :
    ∃ hQ : CyclicGeneric (historicalSharpPolygon q hq h c hc R),
      (∀ i : Fin (Fintype.card (CornerCoord q hq.g2 (sharpSupport q hq h c)
        (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩))),
        0 < planarDet
          (cyclicTangent (historicalSharpPolygon q hq h c hc R) i)
          (cyclicTangent (historicalSharpPolygon q hq h c hc R)
            (cyclicSuccessor i))) ∧
      Fintype.card (PolygonCrossing (historicalSharpPolygon q hq h c hc R)) <
        t.1.nCrossing ∧
      Gemini.candidateEvaluator R.diagram R.nonempty =
        Gemini.candidateEvaluator
          (positivePolygonEventDiagram (historicalSharpPolygon q hq h c hc R) hQ)
          (positivePolygonEventDiagram_nArc_pos _ hQ) ∧
      framedKnotRow Gemini.candidateEvaluator R.diagram R.nonempty
        (componentOf R.diagram.continuation ⟨0, R.nonempty⟩) =
      framedKnotRow Gemini.candidateEvaluator
        (positivePolygonEventDiagram (historicalSharpPolygon q hq h c hc R) hQ)
        (positivePolygonEventDiagram_nArc_pos _ hQ)
        (componentOf
          (positivePolygonEventDiagram (historicalSharpPolygon q hq h c hc R) hQ).continuation
          ⟨0, positivePolygonEventDiagram_nArc_pos _ hQ⟩) := by
  let hQ := originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux
  refine ⟨hQ, ?_⟩
  constructor
  · exact historicalSharpPolygon_uniform_left q hq h c hc R hleft he hAux
  constructor
  · exact historicalSharpPolygon_crossing_count_lt_parent q hq h c hc R he hAux
  constructor
  · simpa [historicalRetainedDiagram, hQ] using
      detached_retained_candidateEvaluator_eq q hq he h c hc R hAux
  · simpa [historicalRetainedDiagram, hQ] using
      detached_retained_framedRow_actual q hq he h c hc R hAux

#check @actual_recursive_child_packet


end DirectGLSSW.HOMFLY.ProcessedExposedChild
