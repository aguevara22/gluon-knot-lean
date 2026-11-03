import ProcessedSharpCrossingComparison
import MarkedIncomingEvaluatorComparison
import FirstChildEvaluatorZero
import ActualTerminalFramedValue
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge
  SmoothingCornerGeometry Coefficients
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

theorem historicalSharpDiagram_nArc_pos :
    0 < (historicalSharpDiagram q hq h c hc R).nArc :=
  SharpDaughter.arc_count_pos q hq (sharpSupport q hq h c)
    (sharpIntervalComponent q hq h c hc R) (sharpSupport_nonalternating q hq h c)

theorem historicalSharpDiagram_isCycleOn :
    (historicalSharpDiagram q hq h c hc R).continuation.IsCycleOn Set.univ :=
  SharpDaughter.next_isCycleOn q hq (sharpSupport q hq h c)
    (sharpIntervalComponent q hq h c hc R)

theorem historicalSharpDiagram_componentCount :
    diagramComponentCount (historicalSharpDiagram q hq h c hc R) = 1 :=
  SharpDaughter.sharpDaughterDiagram_componentCount q hq (sharpSupport q hq h c)
    (sharpIntervalComponent q hq h c hc R) (sharpSupport_nonalternating q hq h c)

/-- The bijection is sign preserving, so it preserves the actual signed writhe. -/
theorem historicalSharpDiagram_writhe :
    diagramWrithe R.diagram = diagramWrithe (historicalSharpDiagram q hq h c hc R) := by
  unfold diagramWrithe
  apply Fintype.sum_equiv (historicalSharpCrossingEquiv q hq h c hc R)
  intro d
  unfold writheSign
  rw [(historicalSharpCrossingEquiv_data q hq h c hc R d).2.2]

/-- The zero-crossing historical child and its exact sharp subdivision are both
connected descending unlinks, including when no incoming mark exists. -/
theorem historicalSharpEvaluator_eq_of_zero
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (hz : R.diagram.nCrossing = 0) :
    H R.diagram R.nonempty =
      H (historicalSharpDiagram q hq h c hc R)
        (historicalSharpDiagram_nArc_pos q hq h c hc R) := by
  have hcard := Fintype.card_congr (historicalSharpCrossingEquiv q hq h c hc R)
  simp only [Fintype.card_fin] at hcard
  have hez : (historicalSharpDiagram q hq h c hc R).nCrossing = 0 := hcard.symm.trans hz
  exact (normalizedEvaluator_eq_one_of_zero_crossings H hH R.diagram R.nonempty
    hz R.diagramComponentCount_eq_one).trans
    (normalizedEvaluator_eq_one_of_zero_crossings H hH _
      (historicalSharpDiagram_nArc_pos q hq h c hc R) hez
      (historicalSharpDiagram_componentCount q hq h c hc R)).symm






end DirectGLSSW.HOMFLY.ProcessedExposedChild
