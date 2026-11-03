import HistoricalChildSupportLift
import RootedCoordinateTransport
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
open ActualLocalSupports LocalCoordinates DaughterFirstReturn
attribute [local instance] Classical.propDecidable
private theorem orbitPosition_congr_root {α : Type*} [Fintype α]
    (p : Equiv.Perm α) {r s : α} (hrs : r=s)
    (x : Fibre p (componentOf p r)) (y : Fibre p (componentOf p s))
    (hxy : x.val=y.val) :
    ((orbitEnumeration p r).symm x).val = ((orbitEnumeration p s).symm y).val := by
  subst s
  have he : x=y := Subtype.ext hxy
  rw [he]

variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))




def historicalIncomingRoot :
    Fibre (smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c))
      (historicalIncomingComponent q hq h c hc R) :=
  ⟨smoothingPairing q (sharpSupport q hq h c)
    (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩),by
    apply (smoothingComponentEquiv q hq.g2 (sharpSupport q hq h c)).injective
    rw [smoothingComponentEquiv_componentOf]
    change componentOf (smoothingDartPermutation q hq.g2 (sharpSupport q hq h c))
      (smoothingPairing q (sharpSupport q hq h c)
        (smoothingPairing q (sharpSupport q hq h c) _)) =
      (smoothingComponentEquiv q hq.g2 (sharpSupport q hq h c))
        ((smoothingComponentEquiv q hq.g2 (sharpSupport q hq h c)).symm _)
    rw [Equiv.apply_symm_apply]
    congr 1
    exact (smoothingPairing q (sharpSupport q hq h c)).apply_symm_apply _⟩

theorem historicalIncomingRoot_pair :
    smoothingPairing q (sharpSupport q hq h c) (historicalIncomingRoot q hq h c hc R).val =
      sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩ :=
  (smoothingPairing q (sharpSupport q hq h c)).apply_symm_apply _

variable (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))

theorem historicalChildLocalEndpoint_position
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) (b : Bool) :
    (localEndpoint q (smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c))
      (sharpSupport q hq h c) (historicalIncomingComponent q hq h c hc R)
      (historicalIncomingRoot q hq h c hc R)
      (historicalChildLocalCrossingEquiv q hq h c hc R he hAux d,b)).val =
    (retainedEventCoordinate q hq h c hc R
      (PolygonDrawing.visit _ d (historicalSharpBranchPermutation q hq h c hc R d
        (if b then 1 else 0)))).val := by
  let I := smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c)
  let D := smoothingDartPermutation q hq.g2 (sharpSupport q hq h c)
  let E := smoothingPairing q (sharpSupport q hq h c)
  let root := historicalIncomingRoot q hq h c hc R
  let x := localVisitLift q I (sharpSupport q hq h c)
    (historicalIncomingComponent q hq h c hc R)
    (historicalChildLocalCrossingEquiv q hq h c hc R he hAux d) b
  have hh := rootedEnumeration_position_embedding I D E E.injective
    (fun z => (smoothingPermutation_intertwine q hq.g2 (sharpSupport q hq h c) z).symm)
    _ root x
  have hroot : E root.val = sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩ :=
    historicalIncomingRoot_pair q hq h c hc R
  have hval : E x.val = retainedEventMap q hq h c hc R
      (PolygonDrawing.visit _ d (historicalSharpBranchPermutation q hq h c hc R d (if b then 1 else 0))) := by
    rw [retainedEventMap_matched_visit]
    have hd := (historicalChildLocalCrossingEquiv q hq h c hc R he hAux d).property.1
    rw [historicalChildLocalCrossingEquiv_val] at hd
    cases b <;> change E (Sum.inr (_, _)) = _ <;>
      simp only [E,smoothingPairing_apply,smoothingPairingMap,historicalChildLocalCrossingEquiv_val,
        if_neg hd,PolygonDrawing.visit,ite_true,ite_false] <;> norm_num
  change ((rootedEnumeration I root).symm x).val = _
  apply hh.symm.trans
  exact orbitPosition_congr_root D hroot _ _ hval
end DirectGLSSW.HOMFLY.ProcessedExposedChild
