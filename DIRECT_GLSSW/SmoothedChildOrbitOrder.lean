import OrderedCutOrbitOrder
import PositivePolygonChildCrossings

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW PermutationOrbits PolygonDrawing Equiv
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

private theorem orbitPosition_root_eq {α : Type*} [Fintype α] (p : Perm α)
    (r s : α) (hrs : r=s) (x : Fibre p (componentOf p r)) (y : Fibre p (componentOf p s))
    (hxy : x.val=y.val) : ((orbitEnumeration p r).symm x).val=((orbitEnumeration p s).symm y).val := by
  subst s
  have h : x=y := Subtype.ext hxy
  subst y
  rfl

private theorem incoming_rep (c : PolygonCrossing q) (i : Fin 2) :
    (positivePolygonEventDiagram q hq).incoming (crossingFin q c) i = eventFin q (incoming q hq c i) := by
  simp only [positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram,incomingIndex,Equiv.symm_apply_apply]

private theorem eventFin_cut_step (c : PolygonCrossing q) (x : PolygonEvent q) :
    eventFin q ((polygonEventSuccessor q hq.g2 * swap (incoming q hq c 0) (incoming q hq c 1)) x) =
      cutContinuation (positivePolygonEventDiagram q hq) (crossingFin q c) (eventFin q x) := by
  simp only [Perm.mul_apply,cutContinuation,incoming_rep]
  change eventFin q (polygonEventSuccessor q hq.g2 _) = (polygonEventDiagram q hq).continuation _
  rw [←polygonEventDiagram_continuation]
  exact congrArg (polygonEventDiagram q hq).continuation
    ((eventFin q).injective.map_swap (incoming q hq c 0) (incoming q hq c 1) x)

/-- The actual event-labelled middle cut component. -/
abbrev ChildEventFibre (c : PolygonCrossing q) :=
  Fibre (polygonEventSuccessor q hq.g2 * swap (incoming q hq c 0) (incoming q hq c 1))
    (componentOf (polygonEventSuccessor q hq.g2 * swap (incoming q hq c 0) (incoming q hq c 1))
      (incoming q hq c 1))

/-- Reindex an actual event cut-fibre into the actual diagram's cut continuation. -/
def childEventCutFibre (c : PolygonCrossing q) (x : ChildEventFibre q hq c) :
    Fibre (cutContinuation (positivePolygonEventDiagram q hq) (crossingFin q c))
      (componentOf (cutContinuation (positivePolygonEventDiagram q hq) (crossingFin q c))
        ((positivePolygonEventDiagram q hq).incoming (crossingFin q c) 1)) :=
  ⟨eventFin q x.val,by
    rw [incoming_rep]
    exact (orbitFibreEquivOfEmbedding _ _ (eventFin q) (eventFin q).injective
      (eventFin_cut_step q hq c) (incoming q hq c 1) x).property⟩

/-- The same actual old arc in the geometric component rooted at connector 1. -/
def childEventSmoothedFibre (c : PolygonCrossing q) (x : ChildEventFibre q hq c) :
    Fibre (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).continuation
      (positiveSmoothedChildComponent q hq c) :=
  ⟨smoothArcEquiv (positivePolygonEventDiagram q hq) (Sum.inl (eventFin q x.val)),by
    change _=componentOf _ (smoothArcEquiv (positivePolygonEventDiagram q hq) (Sum.inr (1 : Fin 2)))
    rw [←smoothCutComponentEquiv_old,←smoothCutComponentEquiv_connector]
    exact congrArg (smoothCutComponentEquiv (positivePolygonEventDiagram q hq) (crossingFin q c))
      (childEventCutFibre q hq c x).property⟩

/-- Physical smoothing inserts the connector without changing any nonroot old-port rank. -/
theorem childEventSmoothedFibre_orbitPosition (c : PolygonCrossing q) (x : ChildEventFibre q hq c)
    (hx : x.val≠incoming q hq c 1) :
    ((orbitEnumeration (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).continuation
      (smoothArcEquiv (positivePolygonEventDiagram q hq) (Sum.inr (1 : Fin 2)))).symm
      (childEventSmoothedFibre q hq c x)).val =
    ((orbitEnumeration (polygonEventSuccessor q hq.g2 * swap (incoming q hq c 0) (incoming q hq c 1))
      (incoming q hq c 1)).symm x).val := by
  let D:=positivePolygonEventDiagram q hq
  have hself : D.continuation.SameCycle (D.incoming (crossingFin q c) 0) (D.incoming (crossingFin q c) 1) :=
    (polygonEventDiagram_isCycleOn q hq).2 (Set.mem_univ _) (Set.mem_univ _)
  have hx' : (childEventCutFibre q hq c x).val≠D.incoming (crossingFin q c) 1 := by
    change eventFin q x.val≠(positivePolygonEventDiagram q hq).incoming (crossingFin q c) 1
    rw [incoming_rep]
    exact fun h=>hx ((eventFin q).injective h)
  have hs:=smoothConnector_actual_orbitPosition D (crossingFin q c) hself 1 (childEventCutFibre q hq c x) hx'
  have hs' :
      ((orbitEnumeration (smoothCrossing D (crossingFin q c)).continuation (smoothArcEquiv D (Sum.inr (1 : Fin 2)))).symm
        (childEventSmoothedFibre q hq c x)).val =
      ((orbitEnumeration (cutContinuation D (crossingFin q c)) (D.incoming (crossingFin q c) 1)).symm
        (childEventCutFibre q hq c x)).val := hs
  rw [hs']
  have he:=orbitPosition_embedding
    (polygonEventSuccessor q hq.g2 * swap (incoming q hq c 0) (incoming q hq c 1))
    (cutContinuation D (crossingFin q c)) (eventFin q) (eventFin q).injective
    (eventFin_cut_step q hq c) (incoming q hq c 1) x
  refine (orbitPosition_root_eq (cutContinuation D (crossingFin q c))
    (D.incoming (crossingFin q c) 1) (eventFin q (incoming q hq c 1))
    (incoming_rep q hq c 1) (childEventCutFibre q hq c x)
    (orbitFibreEquivOfEmbedding _ _ (eventFin q) (eventFin q).injective
      (eventFin_cut_step q hq c) (incoming q hq c 1) x) rfl).trans he

/-- Actual smoothed child old-port rank order is exactly the physical event order. -/
theorem childEventSmoothedFibre_orbitPosition_lt_iff (c : PolygonCrossing q)
    (x y : ChildEventFibre q hq c) (hx : x.val≠incoming q hq c 1) (hy : y.val≠incoming q hq c 1) :
    letI := polygonEventOrder q hq.g2
    ((orbitEnumeration (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).continuation
      (smoothArcEquiv (positivePolygonEventDiagram q hq) (Sum.inr (1 : Fin 2)))).symm (childEventSmoothedFibre q hq c x)).val <
    ((orbitEnumeration (smoothCrossing (positivePolygonEventDiagram q hq) (crossingFin q c)).continuation
      (smoothArcEquiv (positivePolygonEventDiagram q hq) (Sum.inr (1 : Fin 2)))).symm (childEventSmoothedFibre q hq c y)).val ↔ x.val<y.val := by
  letI := polygonEventOrder q hq.g2
  rw [childEventSmoothedFibre_orbitPosition q hq c x hx,childEventSmoothedFibre_orbitPosition q hq c y hy]
  exact orderedCut_orbitPosition_lt_iff (incoming q hq c 0) (incoming q hq c 1)
    (polygon_incoming_zero_lt_one q hq c) x y hx hy
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
