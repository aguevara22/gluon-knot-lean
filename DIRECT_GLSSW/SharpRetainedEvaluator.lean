import ProcessedSharpBranchData
import BranchMarkedIncomingComparison
import HistoricalSharpNextRoot
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge
  SmoothingCornerGeometry Coefficients
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))

theorem historicalRetainedDiagram_nArc_pos :
    0 < (historicalRetainedDiagram q hq h c hc R he hAux).nArc :=
  positivePolygonEventDiagram_nArc_pos _ _

/-- The empty crossing case uses connected unlink normalization, with no
nonempty crossing carrier or next-mark comparison. -/
theorem sharp_retained_evaluator_eq_of_zero
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (hz : (historicalSharpDiagram q hq h c hc R).nCrossing = 0) :
    H (historicalSharpDiagram q hq h c hc R)
        (historicalSharpDiagram_nArc_pos q hq h c hc R) =
      H (historicalRetainedDiagram q hq h c hc R he hAux)
        (historicalRetainedDiagram_nArc_pos q hq he h c hc R hAux) := by
  have hcq := Fintype.card_congr
    ((historicalSharpPolygonIndexEquiv q hq h c hc R he hAux).symm.trans
      (crossingFin (historicalSharpPolygon q hq h c hc R)))
  simp only [Fintype.card_fin] at hcq
  have hzq : (historicalRetainedDiagram q hq h c hc R he hAux).nCrossing = 0 :=
    hcq.symm.trans hz
  exact (normalizedEvaluator_eq_one_of_zero_crossings H hH _
    (historicalSharpDiagram_nArc_pos q hq h c hc R) hz
    (historicalSharpDiagram_componentCount q hq h c hc R)).trans
    (normalizedEvaluator_eq_one_of_zero_crossings H hH _
      (historicalRetainedDiagram_nArc_pos q hq he h c hc R hAux) hzq
      (positivePolygonEventDiagram_componentCount _ _)).symm

/-- Actual crossing data and connectedness are produced internally. Only the
marked cyclic order comparison remains an explicit input to this helper. -/
theorem sharp_retained_evaluator_eq_of_next
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (hnext :
      MarkedCycleGaps.next (historicalSharpDiagram q hq h c hc R).continuation
        (fun m : PolygonCrossing (historicalSharpPolygon q hq h c hc R) × Fin 2 =>
          (historicalSharpDiagram q hq h c hc R).incoming
            (historicalSharpPolygonIndexEquiv q hq h c hc R he hAux m.1) m.2)
        (labelledIncoming_injective _ _) =
      MarkedCycleGaps.next (historicalRetainedDiagram q hq h c hc R he hAux).continuation
        (fun m : PolygonCrossing (historicalSharpPolygon q hq h c hc R) × Fin 2 =>
          (historicalRetainedDiagram q hq h c hc R he hAux).incoming (crossingFin _ m.1)
            (historicalSharpBranchPermutation q hq h c hc R m.1 m.2))
        (branchLabelledIncoming_injective _ _ _)) :
    H (historicalSharpDiagram q hq h c hc R)
        (historicalSharpDiagram_nArc_pos q hq h c hc R) =
      H (historicalRetainedDiagram q hq h c hc R he hAux)
        (historicalRetainedDiagram_nArc_pos q hq he h c hc R hAux) := by
  by_cases hz : (historicalSharpDiagram q hq h c hc R).nCrossing = 0
  · exact sharp_retained_evaluator_eq_of_zero q hq he h c hc R hAux H hH hz
  let d : Fin (historicalSharpDiagram q hq h c hc R).nCrossing := ⟨0, Nat.pos_of_ne_zero hz⟩
  letI : Nonempty (PolygonCrossing (historicalSharpPolygon q hq h c hc R)) :=
    ⟨(historicalSharpPolygonIndexEquiv q hq h c hc R he hAux).symm d⟩
  exact normalizedEvaluator_eq_of_branch_matching_incoming H hH _ _
    (historicalSharpDiagram_nArc_pos q hq h c hc R)
    (historicalRetainedDiagram_nArc_pos q hq he h c hc R hAux)
    (historicalSharpPolygonIndexEquiv q hq h c hc R he hAux)
    (crossingFin (historicalSharpPolygon q hq h c hc R))
    (historicalSharpBranchPermutation q hq h c hc R)
    (historicalSharpDiagram_isCycleOn q hq h c hc R)
    (polygonEventDiagram_isCycleOn _ _) hnext
    (fun j => (historicalSharpPolygon_branch_data q hq h c hc R he hAux j).1)
    (fun j => (historicalSharpPolygon_branch_data q hq h c hc R he hAux j).2.1)
    (fun j => (historicalSharpPolygon_branch_data q hq h c hc R he hAux j).2.2)

#check @sharp_retained_evaluator_eq_of_next



end DirectGLSSW.HOMFLY.ProcessedExposedChild
