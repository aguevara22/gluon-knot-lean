import ProcessedSharpBranchOver
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

/-- Common crossing index for the historical subdivision and exact retained
polygon; the polygon crossing itself is the common label. -/
def historicalSharpPolygonIndexEquiv :
    PolygonCrossing (historicalSharpPolygon q hq h c hc R) ≃
      Fin (historicalSharpDiagram q hq h c hc R).nCrossing :=
  (historicalSharpPolygonCrossingEquiv q hq h c hc R he hAux).trans
    (SharpDaughter.crossingEquiv q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R)).symm

theorem historicalSharpPolygonIndexEquiv_old
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) :
    SharpDaughter.oldCrossing q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R)
      (historicalSharpPolygonIndexEquiv q hq h c hc R he hAux d) =
        crossingFin q (historicalSharpPolygonCrossingMap q hq h c hc R d) := by
  exact (congrArg Subtype.val
    ((SharpDaughter.crossingEquiv q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R)).apply_symm_apply
      (historicalSharpPolygonCrossingEquiv q hq h c hc R he hAux d))).trans
    (historicalSharpPolygonCrossingEquiv_val q hq h c hc R he hAux d)

/-- All signed crossing data needed by the branch-aware evaluator bridge.
The branch permutation is produced by the actual carrier geometry. -/
theorem historicalSharpPolygon_branch_data
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) :
    (∀ i : Fin 2, historicalSharpBranchPermutation q hq h c hc R d
      ((historicalSharpDiagram q hq h c hc R).through
        (historicalSharpPolygonIndexEquiv q hq h c hc R he hAux d) i) =
      (historicalRetainedDiagram q hq h c hc R he hAux).through (crossingFin _ d)
        (historicalSharpBranchPermutation q hq h c hc R d i)) ∧
    historicalSharpBranchPermutation q hq h c hc R d
      ((historicalSharpDiagram q hq h c hc R).overBranch
        (historicalSharpPolygonIndexEquiv q hq h c hc R he hAux d)) =
      (historicalRetainedDiagram q hq h c hc R he hAux).overBranch (crossingFin _ d) ∧
    crossingSign (historicalSharpDiagram q hq h c hc R)
      (historicalSharpPolygonIndexEquiv q hq h c hc R he hAux d) =
      crossingSign (historicalRetainedDiagram q hq h c hc R he hAux) (crossingFin _ d) := by
  refine ⟨fun _ => rfl,?_,?_⟩
  · change historicalSharpBranchPermutation q hq h c hc R d
      ((positivePolygonEventDiagram q hq).overBranch
        (SharpDaughter.oldCrossing q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R)
          (historicalSharpPolygonIndexEquiv q hq h c hc R he hAux d))) = _
    rw [historicalSharpPolygonIndexEquiv_old]
    exact historicalSharpBranchPermutation_over q hq h c hc R he hAux d
  · exact (SharpDaughter.sharpDaughterDiagram_crossingSign q hq (sharpSupport q hq h c)
      (sharpIntervalComponent q hq h c hc R) (sharpSupport_nonalternating q hq h c) _).trans
      (positivePolygonEventDiagram_crossingSign _
        (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux) _).symm
end DirectGLSSW.HOMFLY.ProcessedExposedChild
