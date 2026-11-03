import PhysicalContinuingTailCrossings
import FirstChildPhysicalVisitOrder
import ExposedCursorFilter
import FirstPhysicalEvent
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalParentHistory
open PermutationOrbits LowestRowContract ProcessedParentMarks MarkedG
open PolygonDrawingBridge PolygonDrawing ActiveArc ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

/-- The stored original traversal realizes the full physical incoming visit order. -/
theorem initial_incoming_strict_order {n : Nat} (q : Fin n → PlanarPoint Real)
    (hq : CyclicGeneric q) (c d : PolygonCrossing q) (i j : Fin 2) :
    visitPosition (initialAnchorTraversal q hq)
      ((positivePolygonEventDiagram q hq).incoming (crossingFin q c) i) <
    visitPosition (initialAnchorTraversal q hq)
      ((positivePolygonEventDiagram q hq).incoming (crossingFin q d) j) ↔
    (polygonEventOrder q hq.g2).lt (visit q c i) (visit q d j) := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  have hin (c : PolygonCrossing q) (i : Fin 2) :
      (positivePolygonEventDiagram q hq).incoming (crossingFin q c) i =
        eventFin q (PolygonDrawing.incoming q hq c i) := by
    simp only [positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram,
      incomingIndex,Equiv.symm_apply_apply]
  rw [hin,hin,initialAnchorTraversal_visitPosition,initialAnchorTraversal_visitPosition]
  change ((polygonEventEnumeration q hq.g2).symm (PolygonDrawing.incoming q hq c i) <
    (polygonEventEnumeration q hq.g2).symm (PolygonDrawing.incoming q hq d j)) ↔ _
  rw [OrderIso.lt_iff_lt]
  exact polygon_incoming_lt_iff_visit_lt q hq c d i j

/-- The upper cut visit keeps its literal right carrier and parameter after opening at zero. -/
theorem exposed_upper_visit {n : Nat} (q : Fin (n+2) → PlanarPoint Real)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) (z : Crossing (cutArc q 0)) :
    polygonEventEdge q (visit q (exposedCrossingEquiv q 0 hq he z) 1) = edgeLabel 0 z.val.2 ∧
    polygonEventParameter q (visit q (exposedCrossingEquiv q 0 hq he z) 1) =
      rightParameter (cutArc q 0) z := by
  let b := visitBoolEquiv q 0 hq he z true
  let j : Fin 2 := if b then 1 else 0
  have hv : visit q (exposedCrossingEquiv q 0 hq he z) j =
      Sum.inr (visitEquiv q 0 hq he (z,true)) := by
    cases b <;> simp [j,b,visit,visitEquiv,visitBoolEquiv]
  have hedge : polygonEventEdge q (visit q (exposedCrossingEquiv q 0 hq he z) j) =
      edgeLabel 0 z.val.2 := by
    rw [hv]
    change crossingVisitEdge q (visitEquiv q 0 hq he (z,true)) = _
    rw [visitEquiv_edge]
    rfl
  have hj : j=1 := by
    by_cases hj0 : j=0
    · have hval := congrArg Fin.val hedge
      rw [hj0] at hval
      simp only [visit,Fin.isValue,ite_true,polygonEventEdge,crossingVisitEdge,Bool.false_eq_true,ite_false] at hval
      rw [exposedCrossing_firstEdge q hq he z,zero_edgeLabel_val] at hval
      have hz := z.property.1
      change z.val.1.val<z.val.2.val at hz
      omega
    · apply Fin.ext
      have hnot : j.val ≠ 0 := fun hh => hj0 (Fin.ext hh)
      have hbnd := j.isLt
      change j.val=1
      omega
  refine ⟨hj ▸ hedge,?_⟩
  rw [← hj,hv]
  change crossingVisitParameter q (visitEquiv q 0 hq he (z,true)) = _
  rw [visitEquiv_parameter]
  rfl
end DirectGLSSW.HOMFLY.PhysicalParentHistory

namespace DirectGLSSW.HOMFLY.PhysicalParentHistory
open PermutationOrbits LowestRowContract ProcessedParentMarks MarkedG
open PolygonDrawingBridge PolygonDrawing ActiveArc ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

/-- Literal parent membership is exactly the strict original future of the upper cut port. -/
theorem exposed_parent_filter {a b : Nat} (q : Fin (a+b+2) → PlanarPoint Real)
    (hq : CyclicGeneric q) (he : LeftExposed q 0)
    (z w : Crossing (cutArc q 0)) (hcut : z.val.2.val=a) :
    Split.InParent (a:=a) (b:=b) (cutArc q 0) z w ↔
      ∀ i : Fin 2, visitPosition (initialAnchorTraversal q hq)
        ((positivePolygonEventDiagram q hq).incoming (crossingFin q (exposedCrossingEquiv q 0 hq he z)) 1) <
        visitPosition (initialAnchorTraversal q hq)
        ((positivePolygonEventDiagram q hq).incoming (crossingFin q (exposedCrossingEquiv q 0 hq he w)) i) := by
  have hz := exposed_upper_visit q hq he z
  have H (i : Fin 2) :
      visitPosition (initialAnchorTraversal q hq)
        ((positivePolygonEventDiagram q hq).incoming (crossingFin q (exposedCrossingEquiv q 0 hq he z)) 1) <
      visitPosition (initialAnchorTraversal q hq)
        ((positivePolygonEventDiagram q hq).incoming (crossingFin q (exposedCrossingEquiv q 0 hq he w)) i) ↔
      a+1 < (crossingVisitEdge q (exposedCrossingEquiv q 0 hq he w,if i=0 then false else true)).val ∨
        (a+1 = (crossingVisitEdge q (exposedCrossingEquiv q 0 hq he w,if i=0 then false else true)).val ∧
          rightParameter (cutArc q 0) z < crossingVisitParameter q
            (exposedCrossingEquiv q 0 hq he w,if i=0 then false else true)) := by
    rw [initial_incoming_strict_order,polygonEvent_lt_iff]
    rw [hz.1,hz.2]
    change (edgeLabel 0 z.val.2 < crossingVisitEdge q
        (exposedCrossingEquiv q 0 hq he w,if i=0 then false else true) ∨
      edgeLabel 0 z.val.2 = crossingVisitEdge q
        (exposedCrossingEquiv q 0 hq he w,if i=0 then false else true) ∧ _) ↔ _
    simp only [Fin.lt_iff_val_lt_val,Fin.ext_iff,zero_edgeLabel_val,hcut,
      visit,polygonEventParameter]
  change (a≤w.val.1.val ∧ (w.val.1.val=a → _)) ↔ _
  rw [exposed_crossing_cursor_filter q hq he a (rightParameter (cutArc q 0) z) w]
  constructor
  · intro hh i
    exact (H i).mpr (hh _)
  · intro hh v
    cases v
    · exact (H 0).mp (hh 0)
    · exact (H 1).mp (hh 1)
end DirectGLSSW.HOMFLY.PhysicalParentHistory
