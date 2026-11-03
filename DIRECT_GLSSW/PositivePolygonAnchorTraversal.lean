import PositiveLiftFirstEncounter
import HOMFLYOrbitTraversalCoordinates
import DirectGLSSW.FiniteFirstReturn

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

/-- The original zero anchor, without moving the basepoint to a cut connector. -/
def initialAnchor : PolygonEvent q := Sum.inl ⟨0,by have := hq.size_ge_three;omega⟩

private theorem component_eq_anchor (C : diagramComponent (positivePolygonEventDiagram q hq)) :
    componentOf (positivePolygonEventDiagram q hq).continuation (eventFin q (initialAnchor q hq))=C := by
  induction C using Quotient.inductionOn with | h x =>
    apply (componentOf_eq_iff _ _ _).mpr
    exact (polygonEventDiagram_isCycleOn q hq).2 (Set.mem_univ _) (Set.mem_univ _)

/-- The actual initial based traversal, retaining the original polygon anchor. -/
def initialAnchorTraversal : BasedTraversal (positivePolygonEventDiagram q hq) where
  componentIndex := (chooseBasedTraversal (positivePolygonEventDiagram q hq)).componentIndex
  baseArc C := ⟨eventFin q (initialAnchor q hq),component_eq_anchor q hq C⟩

theorem initialAnchorTraversal_baseArc (C : diagramComponent (positivePolygonEventDiagram q hq)) :
    ((initialAnchorTraversal q hq).baseArc C).val=eventFin q (initialAnchor q hq) := rfl

private theorem initialAnchor_le (x : PolygonEvent q) :
    letI := polygonEventOrder q hq.g2
    initialAnchor q hq ≤ x := by
  letI := polygonEventOrder q hq.g2
  cases x with
  | inl i =>
    by_cases h : i.val=0
    · have hi : i=⟨0,by have := hq.size_ge_three;omega⟩ := Fin.ext h
      rw [hi];exact le_rfl
    · apply le_of_lt
      exact (polygonEvent_anchor_lt_iff q hq.g2 ⟨0,by have := hq.size_ge_three;omega⟩ i).mpr (Fin.lt_iff_val_lt_val.mpr (Nat.pos_of_ne_zero h))
  | inr v =>
    apply le_of_lt
    apply (polygonEvent_lt_iff q hq.g2 _ _).mpr
    by_cases h : (crossingVisitEdge q v).val=0
    · right
      refine ⟨Fin.ext (by simpa [initialAnchor,polygonEventEdge] using h.symm),?_⟩
      exact (crossingVisitParameter_spec q v).1
    · left;change 0<(crossingVisitEdge q v).val;omega

private def zeroEventIndex : Fin (Fintype.card (PolygonEvent q)) :=
  ⟨0,Fintype.card_pos_iff.mpr ⟨initialAnchor q hq⟩⟩

private theorem initialAnchor_index_zero :
    letI := polygonEventOrder q hq.g2
    (polygonEventEnumeration q hq.g2).symm (initialAnchor q hq)=zeroEventIndex q hq := by
  letI := polygonEventOrder q hq.g2
  apply Fin.ext
  have h := (polygonEventEnumeration q hq.g2).symm.monotone
    (initialAnchor_le q hq (polygonEventEnumeration q hq.g2 (zeroEventIndex q hq)))
  simp only [OrderIso.symm_apply_apply] at h
  exact Nat.eq_zero_of_le_zero (show _≤0 from h)

private theorem initialAnchor_pow (k : Fin (Fintype.card (PolygonEvent q))) :
    (polygonEventSuccessor q hq.g2 ^ k.val) (initialAnchor q hq)=
      polygonEventEnumeration q hq.g2 k := by
  letI := polygonEventOrder q hq.g2
  change (orderedCyclicSuccessor (PolygonEvent q)^k.val) _ = _
  rw [orderedCyclicSuccessor_pow_apply]
  change polygonEventEnumeration q hq.g2
    ((cyclicSuccessorPerm (Fintype.card (PolygonEvent q))^k.val)
      ((polygonEventEnumeration q hq.g2).symm (initialAnchor q hq))) = _
  rw [initialAnchor_index_zero]
  congr 1
  apply Fin.ext
  simpa [zeroEventIndex,k.isLt] using
    (FiniteFirstReturn.cyclicSuccessorPerm_pow_val_of_lt (zeroEventIndex q hq) (k := k.val) k.isLt)

private theorem initial_fibre_card :
    Fintype.card (Fibre (positivePolygonEventDiagram q hq).continuation
      (componentOf (positivePolygonEventDiagram q hq).continuation
        (eventFin q (initialAnchor q hq)))) = Fintype.card (PolygonEvent q) := by
  let E : Fibre (positivePolygonEventDiagram q hq).continuation
      (componentOf (positivePolygonEventDiagram q hq).continuation (eventFin q (initialAnchor q hq))) ≃
      Fin (positivePolygonEventDiagram q hq).nArc := {
    toFun := Subtype.val
    invFun := fun x => ⟨x,(component_eq_anchor q hq (componentOf _ x)).symm⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Fintype.card_congr E).trans (Fintype.card_congr (eventFin q).symm)

/-- Exact actual arc visit positions are the original physical event coordinates. -/
theorem initialAnchorTraversal_visitPosition (x : PolygonEvent q) :
    letI := polygonEventOrder q hq.g2
    visitPosition (initialAnchorTraversal q hq) (eventFin q x)=
      ((polygonEventEnumeration q hq.g2).symm x).val := by
  letI := polygonEventOrder q hq.g2
  let k := (polygonEventEnumeration q hq.g2).symm x
  let j : Fin (Fintype.card (Fibre (positivePolygonEventDiagram q hq).continuation
      (componentOf (positivePolygonEventDiagram q hq).continuation
        (eventFin q (initialAnchor q hq))))) := ⟨k.val,by rw [initial_fibre_card];exact k.isLt⟩
  have he : (orbitEnumeration (positivePolygonEventDiagram q hq).continuation
      (eventFin q (initialAnchor q hq)) j).val = eventFin q x := by
    rw [orbitEnumeration_apply_val]
    change ((polygonEventDiagram q hq).continuation ^ k.val) (eventFin q (initialAnchor q hq))= _
    rw [polygonEventDiagram_continuation_pow,initialAnchor_pow]
    exact congrArg (eventFin q) ((polygonEventEnumeration q hq.g2).apply_symm_apply x)
  have hp := visitPosition_orbitEnumeration (initialAnchorTraversal q hq)
    (eventFin q (initialAnchor q hq)) (by rfl) j
  rw [he] at hp
  exact hp

end DirectGLSSW.HOMFLY.PolygonDrawingBridge
