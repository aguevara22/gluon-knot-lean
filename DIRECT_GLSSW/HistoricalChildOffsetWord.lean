import PhysicalClosedSingletonRoot
import ProcessedSharpPolygonCrossings
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive ActiveArc.PhysicalKnotSplit
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q 0) {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

/-- Literal historical sharp child is the original crossing and precisely the
original polygon anchors between its two active carriers, up to cyclic root. -/
theorem historicalSharpPolygon_offset_word :
    let d := openingCrossing q hq he h c
    List.ofFn (historicalSharpPolygon q hq h c hc R) ~r
      ActiveArc.crossingPoint (cutArc q 0) d ::
        List.ofFn (fun i : Fin (d.val.2.val-d.val.1.val) =>
          cutArc q 0 ⟨d.val.1.val+i.val+1,by have := d.val.2.isLt;omega⟩) := by
  dsimp only
  change DaughterFirstReturn.daughterPointList q hq.g2
    {(crossingFin q).symm (h.crossingOrigin c)}
    ((eventFin q).symm (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)) ~r _
  rw [originalSingleton_daughterPointList_eq q hq he h c hc R]
  exact closed_singleton_word_offset_isRotated (a:=n) (b:=0)
    (cutArc q 0) (cutArc_regular q 0 hq) (openingCrossing q hq he h c)
    (openingRoot q hq he h c hc R) (opening_component_ne_open q hq he h c hc R)
end DirectGLSSW.HOMFLY.ProcessedExposedChild

namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive ActiveArc.PhysicalKnotSplit
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q 0) {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

theorem historicalSharpPolygon_head :
    (List.ofFn (historicalSharpPolygon q hq h c hc R)).head? =
      some (ActiveArc.crossingPoint (cutArc q 0) (openingCrossing q hq he h c)) := by
  change (DaughterFirstReturn.daughterPointList q hq.g2 (sharpSupport q hq h c)
    (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)).head? = _
  rw [DaughterFirstReturn.daughterPointList_head _ _ _ _
    (sharpInterval_root_retained q hq h c hc R)]
  unfold sharpIntervalEvent
  rw [h.detachedOriginalArc_first c hc R]
  change some (polygonEventPoint q ((eventFin q).symm
    ((positivePolygonEventDiagram q hq).outgoing (h.crossingOrigin c)
      ((positivePolygonEventDiagram q hq).through (h.crossingOrigin c)
        (firstVisitedBranch t.2.1 c))))) = _
  rw [SharpDaughter.outgoing_event]
  have hp := crossingEquiv_point q 0 hq (openingCrossing q hq he h c)
  have heq : (crossingEquiv q 0 hq (openingCrossing q hq he h c)).val =
      (crossingFin q).symm (h.crossingOrigin c) := by
    change exposedCrossingEquiv q 0 hq he (openingCrossing q hq he h c) = _
    simp only [openingCrossing,Equiv.apply_symm_apply]
  rw [heq] at hp
  generalize firstVisitedBranch t.2.1 c = i
  fin_cases i <;> simpa only [PolygonDrawing.visit,Fin.isValue,Fin.reduceEq,if_true,if_false,
    polygonEventPoint,crossingVisitPoint] using congrArg some hp

/-- The root is already the actual cut point, so auxiliary G1 upgrades the
cyclic relation to literal point-list equality, with no rebase hypothesis. -/
theorem historicalSharpPolygon_offset_word_eq
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (cutArc q 0) (cutArc_regular q 0 hq)) :
    let d := openingCrossing q hq he h c
    List.ofFn (historicalSharpPolygon q hq h c hc R) =
      ActiveArc.crossingPoint (cutArc q 0) d ::
        List.ofFn (fun i : Fin (d.val.2.val-d.val.1.val) =>
          cutArc q 0 ⟨d.val.1.val+i.val+1,by have := d.val.2.isLt;omega⟩) := by
  dsimp only
  have hg := originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux
  apply ActiveArc.SingletonWords.nodup_rotated_eq_of_head
  · apply List.nodup_ofFn_ofInjective
    exact cyclicNoncollinear_injective hg.size_ge_three _ hg.g1
  · exact historicalSharpPolygon_offset_word q hq he h c hc R
  · exact historicalSharpPolygon_head q hq he h c hc R
end DirectGLSSW.HOMFLY.ProcessedExposedChild
