import HistoricalChildEndpointOrder
import OrderCoordinateFirstReturn
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
open ActualLocalSupports LocalCoordinates DaughterFirstReturn
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))




variable (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))


include he hAux in
theorem retainedEventMap_injective :
    Function.Injective (retainedEventMap q hq h c hc R) := by
  let Q := historicalSharpPolygon q hq h c hc R
  let hQ := originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux
  letI : LinearOrder (PolygonEvent Q) := polygonEventOrder Q hQ.g2
  have hm : StrictMono (retainedEventCoordinate q hq h c hc R) := by
    intro x y hxy
    exact (retainedEventCoordinate_order q hq h c hc R x y).mpr
      ((polygonEvent_lt_iff Q hQ.g2 x y).mp hxy)
  intro x y hxy
  apply hm.injective
  unfold retainedEventCoordinate
  congr 1
  exact Subtype.ext hxy

theorem retainedEventMap_firstReturn
    (x : PolygonEvent (historicalSharpPolygon q hq h c hc R)) :
    ∃d : ℕ, 0<d ∧
      (smoothingDartPermutation q hq.g2 (sharpSupport q hq h c)^d)
        (retainedEventMap q hq h c hc R x) =
      retainedEventMap q hq h c hc R
        (polygonEventSuccessor _ (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2 x) ∧
      ∀k : ℕ, 0<k → k<d →
        (smoothingDartPermutation q hq.g2 (sharpSupport q hq h c)^k)
          (retainedEventMap q hq h c hc R x) ∉ Set.range (retainedEventMap q hq h c hc R) := by
  let Q := historicalSharpPolygon q hq h c hc R
  let hQ := originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux
  letI : LinearOrder (PolygonEvent Q) := polygonEventOrder Q hQ.g2
  exact OrderCoordinateFirstReturn.firstReturn_of_coordinate_order
    (smoothingDartPermutation q hq.g2 (sharpSupport q hq h c))
    (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)
    (retainedEventMap q hq h c hc R) (retainedEventMap_mem q hq h c hc R)
    (fun x y => (retainedEventCoordinate_order q hq h c hc R x y).trans
      (polygonEvent_lt_iff Q hQ.g2 x y).symm) x

/-- Every old retained corner of the actual singleton component is represented
by an anchor of the literal retained polygon. -/
theorem retainedEventMap_oldCorner_preimage
    (x : PolygonEvent q)
    (hx : componentOf (smoothingDartPermutation q hq.g2 (sharpSupport q hq h c)) x =
      sharpIntervalComponent q hq h c hc R)
    (hr : retainedCorner q (sharpSupport q hq h c) x) :
    ∃ i, retainedEventMap q hq h c hc R (Sum.inl i)=x := by
  let root := sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩
  let E := orbitEnumeration (smoothingDartPermutation q hq.g2 (sharpSupport q hq h c)) root
  let j := E.symm ⟨x,hx⟩
  have hej : orbitEventAt q hq.g2 (sharpSupport q hq h c) root j=x :=
    congrArg Subtype.val (E.apply_symm_apply _)
  let z : CornerCoord q hq.g2 (sharpSupport q hq h c) root := ⟨j,by rw [hej]; exact hr⟩
  refine ⟨(cornerEnumeration q hq.g2 (sharpSupport q hq h c) root).symm z,?_⟩
  change orbitEventAt q hq.g2 (sharpSupport q hq h c) root
    ((cornerEnumeration q hq.g2 (sharpSupport q hq h c) root)
      ((cornerEnumeration q hq.g2 (sharpSupport q hq h c) root).symm z)).val=x
  rw [OrderIso.apply_symm_apply]
  exact hej
end DirectGLSSW.HOMFLY.ProcessedExposedChild
