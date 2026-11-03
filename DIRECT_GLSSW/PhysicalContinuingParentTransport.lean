import PhysicalContinuingParentComparison
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalParentHistory
open PermutationOrbits LowestRowContract ProcessedParentMarks MarkedG
open SmoothingCornerGeometry PolygonDrawingBridge PolygonDrawing ActiveArc ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable
variable {a b : Nat} (q : Fin (a+b+2) → PlanarPoint Real)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) (hgood : GoodBefore t c)
    (hcut : (selectedOriginalOpenCrossing q hq he h c).val.2.val=a)

/-- Actual origin equation of the constructed physical-parent crossing equivalence. -/
theorem physicalContinuingParentCrossing_origin
    (d : Crossing (Split.parent (cutArc q 0) (selectedOriginalOpenCrossing q hq he h c) hcut)) :
    (continuingTrace h c hc hgood).crossingOrigin
      ((physicalContinuingParentCrossingEquiv q hq he h c hc hgood hcut) d).val =
    crossingFin q (exposedCrossingEquiv q 0 hq he
      (Split.parentCrossingToOriginal (cutArc q 0) (selectedOriginalOpenCrossing q hq he h c) hcut d)) := by
  have H := (continuingFutureCrossingEquiv h c hc hgood).apply_symm_apply
    ⟨crossingFin q (exposedCrossingEquiv q 0 hq he
      (Split.parentCrossingToOriginal (cutArc q 0) (selectedOriginalOpenCrossing q hq he h c) hcut d)),by
        have hm := (exposed_parent_filter q hq he (selectedOriginalOpenCrossing q hq he h c) _ hcut).mp
          (Split.parentCrossingToOriginal_inParent _ (cutArc_regular q 0 hq)
            (selectedOriginalOpenCrossing q hq he h c) hcut d)
        rw [selectedOriginalOpenCrossing_origin] at hm
        simpa only [history_selected_branch_zero q hq h c hc,otherBranch,Fin.isValue,ite_true] using hm⟩
  have HH := congrArg Subtype.val H
  simpa only [physicalContinuingParentCrossingEquiv,Equiv.trans_apply,
    continuingFutureCrossingEquiv,exposedParentFutureEquiv,Equiv.ofBijective_apply] using HH

/-- Every incoming-port order is transported through the actual physical match. -/
theorem physicalContinuingParentCrossing_incoming_order
    (d e : Crossing (Split.parent (cutArc q 0) (selectedOriginalOpenCrossing q hq he h c) hcut))
    (i j : Fin 2) :
    visitPosition (continuingState t c hc hgood).2.1
      ((continuingState t c hc hgood).1.incoming
        ((physicalContinuingParentCrossingEquiv q hq he h c hc hgood hcut) d).val i) <
    visitPosition (continuingState t c hc hgood).2.1
      ((continuingState t c hc hgood).1.incoming
        ((physicalContinuingParentCrossingEquiv q hq he h c hc hgood hcut) e).val j) ↔
    visitPosition (initialAnchorTraversal q hq)
      ((positivePolygonEventDiagram q hq).incoming
        (crossingFin q (exposedCrossingEquiv q 0 hq he
          (Split.parentCrossingToOriginal (cutArc q 0) (selectedOriginalOpenCrossing q hq he h c) hcut d))) i) <
    visitPosition (initialAnchorTraversal q hq)
      ((positivePolygonEventDiagram q hq).incoming
        (crossingFin q (exposedCrossingEquiv q 0 hq he
          (Split.parentCrossingToOriginal (cutArc q 0) (selectedOriginalOpenCrossing q hq he h c) hcut e))) j) := by
  have H := continuingFutureCrossing_incoming_order h c hc hgood
    ((physicalContinuingParentCrossingEquiv q hq he h c hc hgood hcut) d)
    ((physicalContinuingParentCrossingEquiv q hq he h c hc hgood hcut) e) i j
  change _ ↔ visitPosition (initialAnchorTraversal q hq)
    ((positivePolygonEventDiagram q hq).incoming ((continuingTrace h c hc hgood).crossingOrigin _) i) <
    visitPosition (initialAnchorTraversal q hq)
    ((positivePolygonEventDiagram q hq).incoming ((continuingTrace h c hc hgood).crossingOrigin _) j) at H
  rw [physicalContinuingParentCrossing_origin,physicalContinuingParentCrossing_origin] at H
  exact H
end DirectGLSSW.HOMFLY.PhysicalParentHistory
