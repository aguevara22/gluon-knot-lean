import ActualRecursiveChildPacket
import GeminiLowest.ComponentExtraction
import ProcessedConnectorCorners
import ProcessedCrossingSigns
import PositivePolygonInitialGeometryProbe
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge
  SmoothingCornerGeometry Coefficients DaughterFirstReturn
attribute [local instance] Classical.propDecidable

/-- The actual detached component is extracted by the proved canonical geometric constructor. -/
def canonicalDetachedRestriction (t : MarkedParentState) (c : Fin t.1.nCrossing) :
    ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)) :=
  GeminiLowest.canonicalComponentRestriction _ _

variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)

/-- No component-extraction witness is assumed. The literal retained polygon,
its evaluator and canonical framed row are the previously proved actual ones. -/
theorem canonical_actual_recursive_child
    (hleft : ∀ i : Fin (n+2), 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq)) :
    let R := canonicalDetachedRestriction t c
    ∃ hQ : CyclicGeneric (historicalSharpPolygon q hq h c hc R),
      (∀ i, 0 < planarDet (cyclicTangent (historicalSharpPolygon q hq h c hc R) i)
        (cyclicTangent (historicalSharpPolygon q hq h c hc R) (cyclicSuccessor i))) ∧
      Fintype.card (PolygonCrossing (historicalSharpPolygon q hq h c hc R)) < t.1.nCrossing ∧
      Gemini.candidateEvaluator R.diagram R.nonempty =
        Gemini.candidateEvaluator (positivePolygonEventDiagram (historicalSharpPolygon q hq h c hc R) hQ)
          (positivePolygonEventDiagram_nArc_pos _ hQ) ∧
      framedKnotRow Gemini.candidateEvaluator R.diagram R.nonempty
        (componentOf R.diagram.continuation ⟨0,R.nonempty⟩) =
      framedKnotRow Gemini.candidateEvaluator
        (positivePolygonEventDiagram (historicalSharpPolygon q hq h c hc R) hQ)
        (positivePolygonEventDiagram_nArc_pos _ hQ)
        (componentOf (positivePolygonEventDiagram (historicalSharpPolygon q hq h c hc R) hQ).continuation
          ⟨0,positivePolygonEventDiagram_nArc_pos _ hQ⟩) :=
  actual_recursive_child_packet q hq h c hc (canonicalDetachedRestriction t c) hleft he hAux

include h hc in
theorem canonical_detached_crossings_positive :
    ∀ d : Fin (canonicalDetachedRestriction t c).diagram.nCrossing,
      crossingSign (canonicalDetachedRestriction t c).diagram d = Sign.pos := by
  apply h.detached_crossings_positive _ c hc (canonicalDetachedRestriction t c)
  intro d
  exact Or.inl (positivePolygonEventDiagram_crossingSign q hq d)

theorem canonical_detached_original_root_excluded
    (i : Fin (detachedOrbitSize t c (canonicalDetachedRestriction t c)-1)) :
    h.detachedOriginalArc c hc (canonicalDetachedRestriction t c) i ≠
      ((initialAnchorTraversal q hq).baseArc
        (componentOf (positivePolygonEventDiagram q hq).continuation
          ((positivePolygonEventDiagram q hq).incoming (h.crossingOrigin c) 0))).val :=
  h.detachedOriginalArc_ne_baseArc c hc (canonicalDetachedRestriction t c) i

include hc in
/-- All actual processed tags stay outside this child, including tags born by
switches and earlier smoothing steps. -/
theorem canonical_detached_processed_mark_excluded (x : StateMarks t) :
    componentOf (smoothCrossing t.1 c).continuation (smoothArcEquiv t.1 (Sum.inl x.val)) ≠
      rootSelfCutComponents t.1 c (t.2.2.connected _ _) (firstVisitedBranch t.2.1 c) (Sum.inl true) :=
  (MarkedParentTrace.nil t).historical_mark_not_detached c hc x

include hc in
/-- Both endpoints of every earlier artificial connector are absent from the
actual detached component's vertex carrier. -/
theorem canonical_detached_born_corners_excluded (x : StateMarks t)
    (hx : (ProcessedMarkKind.connector,x) ∈ h.bornTags) :
    (¬ ∃ a : ComponentArc (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _) (firstVisitedBranch t.2.1 c) (Sum.inl true)),
      (smoothCrossing t.1 c).arcSource a.val =
        (smoothCrossing t.1 c).arcSource (smoothArcEquiv t.1 (Sum.inl x.val))) ∧
    (¬ ∃ a : ComponentArc (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _) (firstVisitedBranch t.2.1 c) (Sum.inl true)),
      (smoothCrossing t.1 c).arcSource a.val =
        (smoothCrossing t.1 c).arcTarget (smoothArcEquiv t.1 (Sum.inl x.val))) :=
  h.born_connector_corners_not_detached x hx c hc

include h in
/-- The actual parent's stored oriented exposed root remains the original root. -/
theorem actual_parent_original_supporting_root
    (he : ExposedOpenPrimitive.LeftExposed q 0) :
    SupportingRootGeometry t
      ((positivePolygonEventDiagram q hq).vertexPoint
        ((positivePolygonEventDiagram q hq).arcSource (eventFin q (initialAnchor q hq))))
      ((positivePolygonEventDiagram q hq).vertexPoint
        ((positivePolygonEventDiagram q hq).arcTarget (eventFin q (initialAnchor q hq)))) :=
  positivePolygon_history_supporting_root q hq he t h
end DirectGLSSW.HOMFLY.ProcessedExposedChild
