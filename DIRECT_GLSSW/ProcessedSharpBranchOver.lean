import ProcessedSharpBranchCarriers
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

variable (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))

/-- The actual retained polygon drawing, whose genericity is produced from
the original fixed-opening AUX certificate. -/
def historicalRetainedDiagram : PLLinkDiagram :=
  positivePolygonEventDiagram (historicalSharpPolygon q hq h c hc R)
    (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux)

theorem historicalSharpBranchPermutation_over
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) :
    historicalSharpBranchPermutation q hq h c hc R d
      ((positivePolygonEventDiagram q hq).overBranch
        (crossingFin q (historicalSharpPolygonCrossingMap q hq h c hc R d))) =
    (historicalRetainedDiagram q hq h c hc R he hAux).overBranch
      (crossingFin (historicalSharpPolygon q hq h c hc R) d) := by
  let Q := historicalSharpPolygon q hq h c hc R
  let z := historicalSharpPolygonCrossingMap q hq h c hc R d
  let β := historicalSharpBranchPermutation q hq h c hc R d
  have hne := crossing_transverse hq.size_ge_three q hq.g1 z
  obtain ⟨a,ha,h0⟩ := historicalSharpBranchPermutation_tangent q hq h c hc R d 0
  obtain ⟨b,hb,h1⟩ := historicalSharpBranchPermutation_tangent q hq h c hc R d 1
  change β ((positivePolygonEventDiagram q hq).overBranch (crossingFin q z)) =
    (positivePolygonEventDiagram Q _).overBranch (crossingFin Q d)
  rw [positivePolygonEventDiagram_overBranch,positivePolygonEventDiagram_overBranch]
  by_cases halign : z.val.1 = DaughterFirstReturn.daughterCarrier q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) d.val.1
  · have hβ : β=Equiv.refl _ := by unfold β historicalSharpBranchPermutation;rw [if_pos halign]
    have hh0 : cyclicTangent Q d.val.1 = a • cyclicTangent q z.val.1 := by
      simpa only [←show β=historicalSharpBranchPermutation q hq h c hc R d from rfl,hβ,
        Equiv.refl_apply,PolygonDrawing.visit,ite_true,polygonEventEdge,crossingVisitEdge,Bool.false_eq_true,ite_false] using h0
    have hh1 : cyclicTangent Q d.val.2 = b • cyclicTangent q z.val.2 := by
      simpa [←show β=historicalSharpBranchPermutation q hq h c hc R d from rfl,hβ,
        PolygonDrawing.visit,polygonEventEdge,crossingVisitEdge] using h1
    have hdet : planarDet (cyclicTangent Q d.val.1) (cyclicTangent Q d.val.2) =
        (a*b)*planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2) := by
      rw [hh0,hh1];simp [planarDet];ring
    have hiff : 0<(a*b)*planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2) ↔
        0<planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2) :=
      mul_pos_iff_of_pos_left (mul_pos ha hb)
    have hiffQ : 0<planarDet (cyclicTangent Q d.val.1) (cyclicTangent Q d.val.2) ↔
        0<planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2) := by rw [hdet];exact hiff
    by_cases hp : 0<planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2)
    · simp only [hβ,if_pos hp,if_pos (hiffQ.mpr hp),Equiv.refl_apply]
    · simp only [hβ,if_neg hp,if_neg (fun hh => hp (hiffQ.mp hh)),Equiv.refl_apply]
  · have hβ : β=Equiv.swap 0 1 := by unfold β historicalSharpBranchPermutation;rw [if_neg halign]
    have hh0 : cyclicTangent Q d.val.2 = a • cyclicTangent q z.val.1 := by
      simpa [←show β=historicalSharpBranchPermutation q hq h c hc R d from rfl,hβ,
        PolygonDrawing.visit,polygonEventEdge,crossingVisitEdge] using h0
    have hh1 : cyclicTangent Q d.val.1 = b • cyclicTangent q z.val.2 := by
      simpa [←show β=historicalSharpBranchPermutation q hq h c hc R d from rfl,hβ,
        PolygonDrawing.visit,polygonEventEdge,crossingVisitEdge] using h1
    have hdet : planarDet (cyclicTangent Q d.val.1) (cyclicTangent Q d.val.2) =
        -(a*b)*planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2) := by
      rw [hh0,hh1];simp [planarDet];ring
    have hab : 0<a*b := mul_pos ha hb
    by_cases hp : 0<planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2)
    · have hnp : ¬0<planarDet (cyclicTangent Q d.val.1) (cyclicTangent Q d.val.2) := by rw [hdet];nlinarith
      simp [hβ,hp,hnp]
    · have hneg : planarDet (cyclicTangent q z.val.1) (cyclicTangent q z.val.2)<0 := lt_of_le_of_ne (le_of_not_gt hp) hne
      have hpos : 0<planarDet (cyclicTangent Q d.val.1) (cyclicTangent Q d.val.2) := by rw [hdet];nlinarith
      simp [hβ,hp,hpos]
end DirectGLSSW.HOMFLY.ProcessedExposedChild
