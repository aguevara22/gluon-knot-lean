import SharpLocalCrossings
import ProcessedRetainedEventOrder
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
open ActualLocalSupports
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))



def historicalIncomingComponent :=
  (smoothingComponentEquiv q hq.g2 (sharpSupport q hq h c)).symm
    (sharpIntervalComponent q hq h c hc R)

def historicalChildLocalCrossingEquiv
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq)) :
    PolygonCrossing (historicalSharpPolygon q hq h c hc R) ≃
      LocalCrossing q (smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c))
        (sharpSupport q hq h c) (historicalIncomingComponent q hq h c hc R) :=
  (historicalSharpPolygonCrossingEquiv q hq h c hc R he hAux).trans
    ((SharpDaughter.crossingLocalDartEquiv q hq (sharpSupport q hq h c)
      (sharpIntervalComponent q hq h c hc R)).trans
      (SharpDaughter.localDartIncomingEquiv q hq (sharpSupport q hq h c)
        (sharpIntervalComponent q hq h c hc R)))

theorem historicalChildLocalCrossingEquiv_val
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) :
    (historicalChildLocalCrossingEquiv q hq h c hc R he hAux d).val =
      historicalSharpPolygonCrossingMap q hq h c hc R d := by
  change (crossingFin q).symm (crossingFin q (historicalSharpPolygonCrossingMap q hq h c hc R d)) = _
  exact (crossingFin q).symm_apply_apply _

def historicalChildLift (S : Finset (PolygonCrossing (historicalSharpPolygon q hq h c hc R))) :
    Finset (PolygonCrossing q) := S.image (historicalSharpPolygonCrossingMap q hq h c hc R)

variable (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))
    (S : Finset (PolygonCrossing (historicalSharpPolygon q hq h c hc R)))

include he hAux in
theorem historicalChildLift_membership (d : PolygonCrossing q)
    (hd : d ∈ historicalChildLift q hq h c hc R S) :
    d ∉ sharpSupport q hq h c ∧
      componentOf (smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c)) (Sum.inr (d,false)) =
        historicalIncomingComponent q hq h c hc R ∧
      componentOf (smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c)) (Sum.inr (d,true)) =
        historicalIncomingComponent q hq h c hc R := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hd
  have hm := (historicalChildLocalCrossingEquiv q hq h c hc R he hAux x).property
  simpa only [historicalChildLocalCrossingEquiv_val] using hm

include he hAux in
theorem historicalChildLift_eligible :
    EligibleSupport q (smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c))
      (sharpSupport q hq h c) (historicalChildLift q hq h c hc R S) := by
  intro d hd
  have hm := historicalChildLift_membership q hq h c hc R he hAux S d hd
  exact ⟨hm.1,hm.2.1.trans hm.2.2.symm⟩

include he hAux in
theorem historicalChildLift_disjoint :
    Disjoint (sharpSupport q hq h c) (historicalChildLift q hq h c hc R S) := by
  apply Finset.disjoint_left.mpr
  intro d hd hD
  exact (historicalChildLift_membership q hq h c hc R he hAux S d hD).1 hd

include he hAux in
theorem historicalChildLift_card :
    (historicalChildLift q hq h c hc R S).card = S.card := by
  exact Finset.card_image_iff.mpr (fun x hx y hy hxy =>
    historicalSharpPolygonCrossingMap_injective q hq h c hc R he hAux hxy)

/-- The actual lifted support is assigned to the canonical old incoming
components, with no arbitrary family supplied by the caller. -/
def historicalChildLocalFamily :
    LocalSupports q (smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c))
      (sharpSupport q hq h c) :=
  filterByLabel q (smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c))
    (sharpSupport q hq h c) (historicalChildLift q hq h c hc R S)

include he hAux in
theorem historicalChildLocalFamily_union :
    unionLocal q (smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c))
      (sharpSupport q hq h c) (historicalChildLocalFamily q hq h c hc R S) =
        historicalChildLift q hq h c hc R S :=
  unionLocal_filterByLabel q (smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c))
    (sharpSupport q hq h c) (historicalChildLift q hq h c hc R S)
    (historicalChildLift_eligible q hq h c hc R he hAux S)

end DirectGLSSW.HOMFLY.ProcessedExposedChild
