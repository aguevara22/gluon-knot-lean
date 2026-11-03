import HistoricalChildSupportLift
set_option autoImplicit false
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

include he hAux in
theorem historicalChildLocalFamily_other_empty
    (A : Component (smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c)))
    (hA : A ≠ historicalIncomingComponent q hq h c hc R) :
    historicalChildLocalFamily q hq h c hc R S A = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro d hd
  have hm : d.val ∈ historicalChildLift q hq h c hc R S := (Finset.mem_filter.mp hd).2
  have hi := (historicalChildLift_membership q hq h c hc R he hAux S d.val hm).2.1
  exact hA (d.property.2.1.symm.trans hi)

theorem historicalChildLocalFamily_main :
    historicalChildLocalFamily q hq h c hc R S (historicalIncomingComponent q hq h c hc R) =
      S.map (historicalChildLocalCrossingEquiv q hq h c hc R he hAux).toEmbedding := by
  ext d
  constructor
  · intro hd
    have hm : d.val ∈ historicalChildLift q hq h c hc R S := (Finset.mem_filter.mp hd).2
    obtain ⟨e,heS,hed⟩ := Finset.mem_image.mp hm
    refine Finset.mem_map.mpr ⟨e,heS,?_⟩
    apply Subtype.ext
    exact (historicalChildLocalCrossingEquiv_val q hq h c hc R he hAux e).trans hed
  · intro hd
    obtain ⟨e,heS,rfl⟩ := Finset.mem_map.mp hd
    have hm : (historicalChildLocalCrossingEquiv q hq h c hc R he hAux e).val ∈
        historicalChildLift q hq h c hc R S :=
      Finset.mem_image.mpr ⟨e,heS,(historicalChildLocalCrossingEquiv_val q hq h c hc R he hAux e).symm⟩
    simpa only [historicalChildLocalFamily,filterByLabel,Finset.mem_filter,Finset.mem_univ,true_and] using hm
end DirectGLSSW.HOMFLY.ProcessedExposedChild
