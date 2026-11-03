import HistoricalSharpEvaluatorBase
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge
  SmoothingCornerGeometry Coefficients MarkedCycleGaps
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

/-- Conditional composition engine. The actual next equality is a separate
proved geometry input, to be discharged by the public historical consumer. -/
theorem historicalSharpEvaluator_eq_of_next
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (hn : next R.diagram.continuation
        (fun m : Fin R.diagram.nCrossing × Fin 2 => R.diagram.incoming m.1 m.2)
        (@incomingMark_injective R.diagram) =
      next (historicalSharpDiagram q hq h c hc R).continuation
        (fun m : Fin R.diagram.nCrossing × Fin 2 =>
          (historicalSharpDiagram q hq h c hc R).incoming
            (historicalSharpCrossingEquiv q hq h c hc R m.1) m.2)
        (labelledIncoming_injective _ (historicalSharpCrossingEquiv q hq h c hc R))) :
    H R.diagram R.nonempty =
      H (historicalSharpDiagram q hq h c hc R)
        (historicalSharpDiagram_nArc_pos q hq h c hc R) := by
  by_cases hz : R.diagram.nCrossing = 0
  · exact historicalSharpEvaluator_eq_of_zero q hq h c hc R H hH hz
  · have hp : 0 < R.diagram.nCrossing := Nat.pos_of_ne_zero hz
    letI : Nonempty (Fin R.diagram.nCrossing) := ⟨⟨0,hp⟩⟩
    have hcyc : R.diagram.continuation.IsCycleOn Set.univ :=
      ⟨R.diagram.continuation.bijOn (fun _ => Iff.rfl),
        fun x _ y _ => R.continuation_sameCycle x y⟩
    apply normalizedEvaluator_eq_of_matching_incoming H hH R.diagram
      (historicalSharpDiagram q hq h c hc R) R.nonempty
      (historicalSharpDiagram_nArc_pos q hq h c hc R) (Equiv.refl _)
      (historicalSharpCrossingEquiv q hq h c hc R) hcyc
      (historicalSharpDiagram_isCycleOn q hq h c hc R)
    · exact hn
    · intro d
      exact (historicalSharpCrossingEquiv_data q hq h c hc R d).1
    · intro d
      exact (historicalSharpCrossingEquiv_data q hq h c hc R d).2.1
    · intro d
      exact (historicalSharpCrossingEquiv_data q hq h c hc R d).2.2


end DirectGLSSW.HOMFLY.ProcessedExposedChild
