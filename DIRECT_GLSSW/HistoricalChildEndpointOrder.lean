import HistoricalChildLocalCoordinates
set_option autoImplicit false
set_option maxHeartbeats 1000000
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

/-- Literal false/true to 0/1 branch convention. -/
def historicalBoolFin : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := decide (i=1)
  left_inv b := by cases b <;> decide
  right_inv i := by fin_cases i <;> decide

/-- Child branch labels converted back to the corresponding original branches. -/
def historicalChildBranchBool
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) : Equiv.Perm Bool :=
  historicalBoolFin.trans ((historicalSharpBranchPermutation q hq h c hc R d).symm.trans
    historicalBoolFin.symm)

theorem historicalChildBranchBool_fin
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) (b : Bool) :
    historicalSharpBranchPermutation q hq h c hc R d
      (if historicalChildBranchBool q hq h c hc R d b then 1 else 0) =
      (if b then 1 else 0) := by
  change historicalSharpBranchPermutation q hq h c hc R d
    (historicalBoolFin (historicalChildBranchBool q hq h c hc R d b)) = historicalBoolFin b
  simp only [historicalChildBranchBool,Equiv.trans_apply,Equiv.apply_symm_apply]

theorem historicalChildLocalEndpoint_order
    (x y : PolygonCrossing (historicalSharpPolygon q hq h c hc R) × Bool) :
    PolygonNonalternation.actualEndpoint _
      (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2 x <
    PolygonNonalternation.actualEndpoint _
      (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2 y ↔
    localEndpoint q (smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c))
      (sharpSupport q hq h c) (historicalIncomingComponent q hq h c hc R)
      (historicalIncomingRoot q hq h c hc R)
      (historicalChildLocalCrossingEquiv q hq h c hc R he hAux x.1,
       historicalChildBranchBool q hq h c hc R x.1 x.2) <
    localEndpoint q (smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c))
      (sharpSupport q hq h c) (historicalIncomingComponent q hq h c hc R)
      (historicalIncomingRoot q hq h c hc R)
      (historicalChildLocalCrossingEquiv q hq h c hc R he hAux y.1,
       historicalChildBranchBool q hq h c hc R y.1 y.2) := by
  let Q := historicalSharpPolygon q hq h c hc R
  let hQ := originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux
  have hp (z : PolygonCrossing Q × Bool) :
      (localEndpoint q (smoothingIncomingPermutation q hq.g2 (sharpSupport q hq h c))
        (sharpSupport q hq h c) (historicalIncomingComponent q hq h c hc R)
        (historicalIncomingRoot q hq h c hc R)
        (historicalChildLocalCrossingEquiv q hq h c hc R he hAux z.1,
         historicalChildBranchBool q hq h c hc R z.1 z.2)).val =
      (retainedEventCoordinate q hq h c hc R (Sum.inr z)).val := by
    rw [historicalChildLocalEndpoint_position,historicalChildBranchBool_fin]
    congr 2
    rcases z with ⟨d,b⟩
    cases b <;> simp only [PolygonDrawing.visit,ite_true,ite_false] <;> norm_num
  change _ < _ ↔ (_ : Fin _).val < (_ : Fin _).val
  rw [hp x,hp y]
  change _ ↔ retainedEventCoordinate q hq h c hc R (Sum.inr x) <
    retainedEventCoordinate q hq h c hc R (Sum.inr y)
  rw [retainedEventCoordinate_order]
  letI : LinearOrder (PolygonEvent Q) := polygonEventOrder Q hQ.g2
  change (polygonEventEnumeration Q hQ.g2).symm (Sum.inr x) <
    (polygonEventEnumeration Q hQ.g2).symm (Sum.inr y) ↔ _
  exact (OrderIso.lt_iff_lt (polygonEventEnumeration Q hQ.g2).symm).trans
    (polygonEvent_lt_iff Q hQ.g2 _ _)
end DirectGLSSW.HOMFLY.ProcessedExposedChild
