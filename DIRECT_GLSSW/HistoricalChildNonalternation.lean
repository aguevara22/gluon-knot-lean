import HistoricalChildLocalFamily
import HistoricalChildEndpointOrder
import NonalternatingBranchOrder
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
open ActualLocalSupports LocalCoordinates
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
    (S : Finset (PolygonCrossing (historicalSharpPolygon q hq h c hc R)))


theorem historicalChildLift_nonalternating
    (hS : PolygonNonalternation.polygonNonalternating _
      (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2 S) :
    PolygonNonalternation.polygonNonalternating q hq.g2
      (sharpSupport q hq h c ∪ historicalChildLift q hq h c hc R S) := by
  classical
  let I := smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c)
  let C := historicalIncomingComponent q hq h c hc R
  let root := historicalIncomingRoot q hq h c hc R
  let g := historicalChildLocalCrossingEquiv q hq h c hc R he hAux
  let family := historicalChildLocalFamily q hq h c hc R S
  let roots : ComponentRoots I := fun A => Classical.choice inferInstance
  have hs := (PolygonNonalternation.polygonNonalternating_iff_abstract _
    (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2 S).mp hS
  have hlocal : ChordNonalternation.Nonalternating
      (localEndpoint q I (sharpSupport q hq h c) C root) (family C) := by
    change ChordNonalternation.Nonalternating _
      (historicalChildLocalFamily q hq h c hc R S (historicalIncomingComponent q hq h c hc R))
    rw [historicalChildLocalFamily_main q hq h c hc R he hAux S]
    exact (ChordNonalternation.nonalternating_order_relabel_iff
      (PolygonNonalternation.actualEndpoint _
        (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2)
      (PolygonNonalternation.actualEndpoint_injective _ _)
      (localEndpoint q I (sharpSupport q hq h c) C root)
      (localEndpoint_injective q I (sharpSupport q hq h c) C root)
      g (historicalChildBranchBool q hq h c hc R)
      (historicalChildLocalEndpoint_order q hq h c hc R he hAux) S).mp hs
  have hfamily : TwoStageRefinement.LocalNonalternating q hq.g2
      (sharpSupport q hq h c) roots family := by
    intro A
    by_cases hA : A=C
    · subst A
      exact (local_nonalternating_root_independent q I (sharpSupport q hq h c)
        family C root (roots C)).mp hlocal
    · have hempty := historicalChildLocalFamily_other_empty q hq h c hc R he hAux S A hA
      change ChordNonalternation.Nonalternating _ (family A)
      rw [show family A=∅ from hempty]
      intro d hd
      exact (Finset.not_mem_empty d hd).elim
  have hglobal := (TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
    hq.size_ge_three (sharpSupport q hq h c) (sharpSupport_nonalternating q hq h c)
    roots family).mpr hfamily
  dsimp only [family] at hglobal
  rw [historicalChildLocalFamily_union q hq h c hc R he hAux S] at hglobal
  exact hglobal
end DirectGLSSW.HOMFLY.ProcessedExposedChild
