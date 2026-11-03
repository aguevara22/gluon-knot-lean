import ProcessedSharpPolygonEquiv
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

/-- Original/sharp branch to retained-polygon branch. Both possible carrier
orders are retained literally. -/
def historicalSharpBranchPermutation
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) : Equiv.Perm (Fin 2) :=
  if (historicalSharpPolygonCrossingMap q hq h c hc R d).val.1 =
      DaughterFirstReturn.daughterCarrier q hq.g2 (sharpSupport q hq h c)
        (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) d.val.1
  then Equiv.refl _ else Equiv.swap 0 1

/-- The local branch permutation matches the literal physical carrier. -/
theorem historicalSharpBranchPermutation_carrier
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) (i : Fin 2) :
    DaughterFirstReturn.daughterCarrier q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)
      (polygonEventEdge (historicalSharpPolygon q hq h c hc R)
        (PolygonDrawing.visit _ d (historicalSharpBranchPermutation q hq h c hc R d i))) =
    polygonEventEdge q (PolygonDrawing.visit q (historicalSharpPolygonCrossingMap q hq h c hc R d) i) := by
  let f := DaughterFirstReturn.daughterCarrier q hq.g2 (sharpSupport q hq h c)
    (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)
  rcases historicalSharpPolygonCrossingMap_carriers q hq h c hc R d with hp | hp
  · have hb : historicalSharpBranchPermutation q hq h c hc R d = Equiv.refl _ := by
      simp only [historicalSharpBranchPermutation,if_pos hp.1]
    rw [hb]
    fin_cases i <;> simp [PolygonDrawing.visit,polygonEventEdge,crossingVisitEdge,hp.1,hp.2]
  · have hn : (historicalSharpPolygonCrossingMap q hq h c hc R d).val.1 ≠ f d.val.1 := by
      intro hh
      exact crossing_edges_ne _ (historicalSharpPolygonCrossingMap q hq h c hc R d) (hh.trans hp.2.symm)
    dsimp only [f] at hn
    have hb : historicalSharpBranchPermutation q hq h c hc R d = Equiv.swap 0 1 := by
      simp only [historicalSharpBranchPermutation,if_neg hn]
    rw [hb]
    fin_cases i <;> simp [PolygonDrawing.visit,polygonEventEdge,crossingVisitEdge,hp.1,hp.2]

/-- Actual daughter tangents have positive scale relative to the matched
original branch; no tangent relation is supplied as a premise. -/
theorem historicalSharpBranchPermutation_tangent
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) (i : Fin 2) :
    ∃ a : ℝ, 0<a ∧
      cyclicTangent (historicalSharpPolygon q hq h c hc R)
        (polygonEventEdge _ (PolygonDrawing.visit _ d (historicalSharpBranchPermutation q hq h c hc R d i))) =
      a • cyclicTangent q
        (polygonEventEdge q (PolygonDrawing.visit q (historicalSharpPolygonCrossingMap q hq h c hc R d) i)) := by
  obtain ⟨a,ha,hv⟩ := historicalSharpPolygon_tangent_positive q hq h c hc R
    (polygonEventEdge _ (PolygonDrawing.visit _ d (historicalSharpBranchPermutation q hq h c hc R d i)))
  exact ⟨a,ha,by rw [historicalSharpBranchPermutation_carrier] at hv;exact hv⟩
end DirectGLSSW.HOMFLY.ProcessedExposedChild
