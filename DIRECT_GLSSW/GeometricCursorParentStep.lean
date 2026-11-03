import GeometricCursorBoundary
import GeometricCursorCrossingEquiv
import PhysicalParentOriginalSuffix
import PhysicalContinuingTailEndpoints
import PhysicalParentFutureFilter
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PermutationOrbits PolygonDrawingBridge PolygonDrawing SmoothingCornerGeometry EventSegmentGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive PhysicalParentHistory
attribute [local instance] Classical.propDecidable

private theorem original_incoming_successor {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (d : PolygonCrossing q) (i : Fin 2) :
    (positivePolygonEventDiagram q hq).continuation
      ((positivePolygonEventDiagram q hq).incoming (crossingFin q d) i)=eventFin q (visit q d i) := by
  change (polygonEventDiagram q hq).continuation (incomingIndex q hq (crossingFin q d) i)=_
  simp only [incomingIndex,Equiv.symm_apply_apply]
  rw [polygonEventDiagram_continuation,incoming_successor]

private theorem original_visit_positive {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (d : PolygonCrossing q) :
    0<visitPosition (initialAnchorTraversal q hq) (eventFin q (visit q d 1)) := by
  letI : LinearOrder (Fin (n+2) ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  have hx : (Sum.inl (0 : Fin (n+2)) : PolygonEvent q)<visit q d 1 := by
    apply (polygonEvent_lt_iff q hq.g2 _ _).mpr
    left
    change (0 : ℕ)<d.val.2.val
    have hh := d.property.1
    change d.val.1.val<d.val.2.val at hh
    omega
  have hh := (polygonEventEnumeration q hq.g2).symm.strictMono hx
  rw [initialAnchorTraversal_visitPosition]
  exact lt_of_le_of_lt (Nat.zero_le _) hh

/-- The actual continuing parent starts at the original upper-visit source,
with the stored root, framing and processed history retained. -/
theorem exists_parent_cursor {n a b : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) (p : Fin (a+b+2) → PlanarPoint ℝ)
    (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (C : GeometricCursor q hq p t h) (c : ActiveArc.Crossing p) (hcut : c.val.2.val=a)
    (hb : badAt t.2.1 ((C.crossingEquiv he) c).val)
    (hg : MarkedG.GoodBefore t ((C.crossingEquiv he) c).val) :
    Nonempty (GeometricCursor q hq (ActiveArc.Split.parent p c hcut)
      (MarkedG.continuingState t ((C.crossingEquiv he) c).val hb hg)
      (continuingTrace h ((C.crossingEquiv he) c).val hb hg)) := by
  rcases C with ⟨a0,B,A,hs,θ,hθ0,hθ1,hcarrier,hlo,hhi,rfl⟩
  subst n
  let s := positivePolygonMarkedState q hq (initialAnchorTraversal q hq)
  let F := boundaryPhysicalCrossingEquiv q hq he h a0 B A (a+b) rfl θ hcarrier hlo hhi
  change badAt t.2.1 (F c).val at hb
  change MarkedG.GoodBefore t (F c).val at hg
  let selected := (F c).val
  let u := MarkedG.continuingState t selected hb hg
  let H := continuingTrace h selected hb hg
  let z := (ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq)
    A (a+b) rfl θ hθ0 hθ1 c).val
  let d := exposedCrossingEquiv q 0 hq he z
  let x := visit q d 1
  let e : Fin u.1.nArc := u.1.continuation (connector t selected)
  have horigin : h.crossingOrigin selected=crossingFin q d :=
    boundaryPhysicalCrossingEquiv_origin q hq he h a0 B A (a+b) rfl θ hcarrier hlo hhi c
  have hbranch : firstVisitedBranch t.2.1 selected=0 := history_selected_branch_zero q hq h selected hb
  have heorigin : H.arcOrigin e=some (eventFin q x) := by
    have hh := connector_successor_origin h selected hb hg
    rw [hbranch] at hh
    change H.arcOrigin e=some (s.1.continuation (s.1.incoming (h.crossingOrigin selected) 1)) at hh
    rw [horigin] at hh
    change H.arcOrigin e=some ((positivePolygonEventDiagram q hq).continuation
      ((positivePolygonEventDiagram q hq).incoming (crossingFin q d) 1)) at hh
    rw [original_incoming_successor] at hh
    exact hh
  have hne : e≠markedOrbitRoot u (connector t selected) := by
    intro heq
    have hr := continuingTrace_root_origin h selected hb hg
    change H.arcOrigin (markedOrbitRoot u (connector t selected))=_ at hr
    rw [heq,hr] at heorigin
    have hh := Option.some.inj heorigin
    have hp := congrArg (visitPosition s.2.1) hh
    rw [markedOrbitRoot_visitPosition] at hp
    have hpos := original_visit_positive q hq d
    change 0=visitPosition (initialAnchorTraversal q hq) (eventFin q x) at hp
    change 0<visitPosition (initialAnchorTraversal q hq) (eventFin q x) at hpos
    exact (ne_of_gt hpos) hp.symm
  have hepos : visitPosition u.2.1 e=visitPosition u.2.1 (connector t selected)+1 :=
    visitPosition_continuation_of_ne_root u.1 u.2.1 (connector t selected) hne
  have B' : CursorBoundary u (visitPosition u.2.1 e) := by
    rw [hepos]
    exact continuing_cursorBoundary t selected hb hg
  have hOrigin : H.boundaryOrigin e B'=eventFin q x :=
    Option.some.inj ((H.boundaryOrigin_spec e B').symm.trans heorigin)
  have ho : originalEvent q hq H e B'=x := by
    unfold originalEvent
    rw [hOrigin]
    exact (eventFin q).symm_apply_apply _
  have hup := exposed_upper_visit q hq he z
  have hright := ActiveArc.Split.suffixWordCrossingEquiv_right_label
    (cutArc q 0) (cutArc_regular q 0 hq) A (a+b) rfl θ hθ0 hθ1 c
  change z.val.2.val=A+c.val.2.val at hright
  rw [hcut] at hright
  change Nonempty (GeometricCursor q hq (ActiveArc.Split.parent _ c hcut) u H)
  refine ⟨⟨e,B',A+a,by omega,ActiveArc.rightParameter (cutArc q 0) z,
    (ActiveArc.rightParameter_spec (cutArc q 0) z).1.le,
    (ActiveArc.rightParameter_spec (cutArc q 0) z).2.1,?_,?_,?_,?_⟩⟩
  · rw [ho,hup.1,zero_edgeLabel_val,hright]
  · rw [ho,hup.2]
  · rw [ho,← hup.2]
    exact (polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three x).1
  · exact ActiveArc.Split.physical_parent_eq_original_suffix (cutArc q 0) (cutArc_regular q 0 hq)
      θ hθ0 hθ1 c hcut
end DirectGLSSW.HOMFLY.PhysicalCursorComparison
