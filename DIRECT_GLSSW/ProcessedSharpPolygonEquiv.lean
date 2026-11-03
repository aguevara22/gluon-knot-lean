import ProcessedSharpPolygonRange
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

/-- The exact retained sharp polygon and its historical event subdivision
have the same complete crossing carrier on the original opening AUX domain. -/
def historicalSharpPolygonCrossingEquiv
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq)) :
    PolygonCrossing (historicalSharpPolygon q hq h c hc R) ≃
      SharpDaughter.Crossing q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R) := by
  apply Equiv.ofBijective (historicalSharpPolygonToCrossing q hq h c hc R)
  constructor
  · intro a b hab
    apply historicalSharpPolygonCrossingMap_injective q hq h c hc R he hAux
    exact (crossingFin q).injective (congrArg Subtype.val hab)
  · intro d
    obtain ⟨z,hz⟩ := historicalSharp_crossing_has_polygon_preimage q hq h c hc R he hAux d
    refine ⟨z,Subtype.ext ?_⟩
    change crossingFin q (historicalSharpPolygonCrossingMap q hq h c hc R z)=d.val
    rw [hz,Equiv.apply_symm_apply]

theorem historicalSharpPolygonCrossingEquiv_val
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) :
    (historicalSharpPolygonCrossingEquiv q hq h c hc R he hAux d).val =
      crossingFin q (historicalSharpPolygonCrossingMap q hq h c hc R d) := rfl

/-- A complete actual extracted-child/sharp-polygon crossing equivalence;
no crossing correspondence is supplied by the caller. -/
def detachedSharpPolygonCrossingEquiv
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq)) :
    Fin R.diagram.nCrossing ≃ PolygonCrossing (historicalSharpPolygon q hq h c hc R) :=
  (h.detachedCrossingEquiv c hc R).trans
    ((sharpCrossingIntervalEquiv q hq h c hc R).symm.trans
      (historicalSharpPolygonCrossingEquiv q hq h c hc R he hAux).symm)

theorem detachedSharpPolygonCrossingEquiv_origin
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))
    (d : Fin R.diagram.nCrossing) :
    crossingFin q (historicalSharpPolygonCrossingMap q hq h c hc R
      (detachedSharpPolygonCrossingEquiv q hq h c hc R he hAux d)) =
        h.detachedCrossingOrigin c R d := by
  let ds := (sharpCrossingIntervalEquiv q hq h c hc R).symm (h.detachedCrossingEquiv c hc R d)
  have hv := historicalSharpPolygonCrossingEquiv_val q hq h c hc R he hAux
    ((historicalSharpPolygonCrossingEquiv q hq h c hc R he hAux).symm ds)
  rw [Equiv.apply_symm_apply] at hv
  exact hv.symm
end DirectGLSSW.HOMFLY.ProcessedExposedChild
