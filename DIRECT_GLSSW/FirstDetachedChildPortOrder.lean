import SmoothedChildOrbitOrder
import FirstChildPhysicalVisitOrder

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open HOMFLY HOMFLY.PolygonDrawingBridge PermutationOrbits Equiv
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hQ : CyclicGeneric q) (hR : Regular q)
variable (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)

private theorem smoothed_incoming (d : PolygonCrossing q) (hd : d≠polygonCrossingOfArc q c) (i : Fin 2) :
    (smoothCrossing (positivePolygonEventDiagram q hQ) (crossingFin q (polygonCrossingOfArc q c))).incoming
      (positiveSmoothedCrossing q hQ (polygonCrossingOfArc q c) d hd) i =
      smoothArcEquiv (positivePolygonEventDiagram q hQ) (Sum.inl (eventFin q (PolygonDrawing.incoming q hQ d i))) := by
  change smoothIncoming (positivePolygonEventDiagram q hQ) (crossingFin q (polygonCrossingOfArc q c))
    (positiveSmoothedCrossing q hQ (polygonCrossingOfArc q c) d hd) i = _
  simp only [positiveSmoothedCrossing,smoothIncoming,Equiv.symm_apply_apply]
  simp only [positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram,
    incomingIndex,Equiv.symm_apply_apply]

/-- The actual incoming port is in the actual first detached component. -/
def firstDetachedChildIncomingFibre (d : PolygonCrossing (child q hR c hfirst hcut)) (i : Fin 2) :
    Fibre (smoothCrossing (positivePolygonEventDiagram q hQ) (crossingFin q (polygonCrossingOfArc q c))).continuation
      (positiveSmoothedChildComponent q hQ (polygonCrossingOfArc q c)) :=
  ⟨(smoothCrossing (positivePolygonEventDiagram q hQ) (crossingFin q (polygonCrossingOfArc q c))).incoming
      (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut d).val i,
    (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut d).property i⟩

/-- The corresponding original event lies in the proved half-open cut component. -/
def firstDetachedChildEventFibre (d : PolygonCrossing (child q hR c hfirst hcut)) (i : Fin 2) :
    ChildEventFibre q hQ (polygonCrossingOfArc q c) := by
  letI := polygonEventOrder q hQ.g2
  let x:=PolygonDrawing.incoming q hQ (polygonCrossingOfArc q (childCrossingToOriginal q hR c hfirst hcut d)) i
  have hm:=(firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut d).property i
  change componentOf _ ((smoothCrossing _ _).incoming
    (positiveSmoothedCrossing q hQ (polygonCrossingOfArc q c)
      (polygonCrossingOfArc q (childCrossingToOriginal q hR c hfirst hcut d))
      (childCrossingToOriginal_ne_cut q hR c hfirst hcut d)) i)=_ at hm
  rw [smoothed_incoming] at hm
  have hi := (smooth_child_component_old_arc_iff q hQ (polygonCrossingOfArc q c) x).mp hm
  exact ⟨x,(componentOf_eq_iff _ _ _).mpr
    ((orderedCut_sameCycle_right_iff _ _ x (polygon_incoming_zero_lt_one q hQ (polygonCrossingOfArc q c))).mpr hi).symm⟩

theorem firstDetachedChildEventFibre_ne_root (d : PolygonCrossing (child q hR c hfirst hcut)) (i : Fin 2) :
    (firstDetachedChildEventFibre q hQ hR c hfirst hcut d i).val≠PolygonDrawing.incoming q hQ (polygonCrossingOfArc q c) 1 := by
  intro h
  have he:=congrArg (polygonEventSuccessor q hQ.g2) h
  change polygonEventSuccessor q hQ.g2 (PolygonDrawing.incoming q hQ
    (polygonCrossingOfArc q (childCrossingToOriginal q hR c hfirst hcut d)) i)=_ at he
  simp only [PolygonDrawing.incoming_successor] at he
  exact childCrossingToOriginal_ne_cut q hR c hfirst hcut d (congrArg Prod.fst (Sum.inr.inj he))

theorem firstDetachedChildEventFibre_smoothed (d : PolygonCrossing (child q hR c hfirst hcut)) (i : Fin 2) :
    childEventSmoothedFibre q hQ (polygonCrossingOfArc q c)
      (firstDetachedChildEventFibre q hQ hR c hfirst hcut d i) =
    firstDetachedChildIncomingFibre q hQ hR c hfirst hcut d i := by
  apply Subtype.ext
  exact (smoothed_incoming q hQ c
    (polygonCrossingOfArc q (childCrossingToOriginal q hR c hfirst hcut d))
    (childCrossingToOriginal_ne_cut q hR c hfirst hcut d) i).symm

/-- Actual smoothed first-child incoming ports, rooted at connector 1, have
exactly the sharp child's physical crossing-visit order. All membership data
are constructed from the real first-child crossing correspondence. -/
theorem firstDetachedChild_incoming_orbitPosition_lt_iff
    (d e : PolygonCrossing (child q hR c hfirst hcut)) (i j : Fin 2) :
    ((orbitEnumeration (smoothCrossing (positivePolygonEventDiagram q hQ) (crossingFin q (polygonCrossingOfArc q c))).continuation
      (smoothArcEquiv (positivePolygonEventDiagram q hQ) (Sum.inr (1 : Fin 2)))).symm
      (firstDetachedChildIncomingFibre q hQ hR c hfirst hcut d i)).val <
    ((orbitEnumeration (smoothCrossing (positivePolygonEventDiagram q hQ) (crossingFin q (polygonCrossingOfArc q c))).continuation
      (smoothArcEquiv (positivePolygonEventDiagram q hQ) (Sum.inr (1 : Fin 2)))).symm
      (firstDetachedChildIncomingFibre q hQ hR c hfirst hcut e j)).val ↔
    (polygonEventOrder (child q hR c hfirst hcut) (child_noTriple q hR c hfirst hcut)).lt
      (PolygonDrawing.visit (child q hR c hfirst hcut) d i) (PolygonDrawing.visit (child q hR c hfirst hcut) e j) := by
  have h := childEventSmoothedFibre_orbitPosition_lt_iff q hQ (polygonCrossingOfArc q c)
    (firstDetachedChildEventFibre q hQ hR c hfirst hcut d i)
    (firstDetachedChildEventFibre q hQ hR c hfirst hcut e j)
    (firstDetachedChildEventFibre_ne_root q hQ hR c hfirst hcut d i)
    (firstDetachedChildEventFibre_ne_root q hQ hR c hfirst hcut e j)
  rw [firstDetachedChildEventFibre_smoothed,firstDetachedChildEventFibre_smoothed] at h
  exact h.trans (child_original_incoming_lt_iff q hQ hR c hfirst hcut d e i j)
end DirectGLSSW.ActiveArc.Split
