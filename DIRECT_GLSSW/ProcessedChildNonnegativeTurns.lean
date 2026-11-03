import ProcessedNegativeTurns
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SmoothingCornerGeometry
open PermutationOrbits LowestRowContract ProcessedParentMarks
attribute [local instance] Classical.propDecidable

/-- The initial invariant has no marks and follows directly from the actual
initial diagram's nonnegative turns. -/
theorem negativeTurnsMarked_initial (D : PLLinkDiagram) (T : BasedTraversal D)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (hturn : ∀ e : Fin D.nArc, 0 ≤ turnDet D e) :
    NegativeTurnsMarked ⟨D,T,ProcessedParentMarks.initial D T hconn⟩ := by
  intro e he
  exact ((not_lt_of_ge (hturn e)) he).elim

/-- A next actual detached child contains no negative turn. Old negative turn
endpoints are excluded by the real regular-mark geometry; the two new child
corners are positive. No turn or word assertion about the child is assumed. -/
theorem detached_child_turns_nonnegative (s : MarkedParentState)
    (hs : NegativeTurnsMarked s) (hp : PositiveOrMarked s)
    (c : Fin s.1.nCrossing) (hc : badAt s.2.1 c)
    (R : ComponentRestriction (smoothCrossing s.1 c)
      (rootSelfCutComponents s.1 c (s.2.2.connected _ _)
        (firstVisitedBranch s.2.1 c) (Sum.inl true))) :
    ∀ a : Fin R.diagram.nArc, 0 ≤ turnDet R.diagram a := by
  let E := smoothCrossing s.1 c
  let C := rootSelfCutComponents s.1 c (s.2.2.connected _ _)
    (firstVisitedBranch s.2.1 c) (Sum.inl true)
  have hparent : componentOf E.continuation
      (smoothArcEquiv s.1 (Sum.inr (firstVisitedBranch s.2.1 c))) ≠ C := by
    rw [← rootSelfCutComponents_false s.1 c (s.2.2.connected _ _)
      (firstVisitedBranch s.2.1 c)]
    intro h
    have h' := (rootSelfCutComponents s.1 c (s.2.2.connected _ _)
      (firstVisitedBranch s.2.1 c)).injective h
    cases h'
  intro a
  by_contra hnon
  have hneg : turnDet E (R.arcEquiv a).val < 0 := by
    rw [← restriction_turnDet]
    exact lt_of_not_ge hnon
  have hmem : componentOf E.continuation (R.arcEquiv a).val = C := (R.arcEquiv a).property
  rcases negative_smoothing_turn_origin s.1 s.2.1 c hc (hp.bad_crossing_positive c hc)
    (R.arcEquiv a).val hneg with ⟨e,hmap,_,hold⟩ | hmap | hmap
  · obtain ⟨x,hx,hinc⟩ := hs e hold
    have hno := s.2.2.regular_mark_endpoints_not_detached c hc x hx.1 hx.2
    have hends := old_target_at_regular_mark s.1 c e x.val hx.1 hx.2 hinc
    let z : ComponentArc E C := ⟨E.continuation (R.arcEquiv a).val,
      (componentOf_apply E.continuation (R.arcEquiv a).val).trans hmem⟩
    have hz : E.arcSource z.val = E.arcTarget (smoothArcEquiv s.1 (Sum.inl e)) := by
      change E.arcSource (E.continuation (R.arcEquiv a).val) = _
      rw [← E.continuation_incidence,hmap]
    rcases hends with hh | hh
    · exact hno.1 ⟨z,hz.trans hh⟩
    · exact hno.2 ⟨z,hz.trans hh⟩
  · apply hparent
    rw [hmap] at hmem
    have hh := componentOf_apply E.continuation
      (smoothArcEquiv s.1 (Sum.inl (s.1.incoming c (firstVisitedBranch s.2.1 c))))
    change componentOf E.continuation ((smoothCrossing s.1 c).continuation _) = _ at hh
    rw [Gemini.smooth_step_incoming] at hh
    exact hh.trans hmem
  · exact hparent (hmap ▸ hmem)

/-- From a genuine initial diagram with nonnegative turns, every child after any
actual history has nonnegative turns. The initial point-polygon producer is a
separate concrete geometry lemma, not a child-geometry hypothesis. -/
theorem actual_history_child_turns_nonnegative (D : PLLinkDiagram) (T : BasedTraversal D)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (hpos : ∀ d : Fin D.nCrossing, crossingSign D d = Sign.pos)
    (hturn : ∀ e : Fin D.nArc, 0 ≤ turnDet D e)
    (t : MarkedParentState)
    (h : MarkedParentTrace ⟨D,T,ProcessedParentMarks.initial D T hconn⟩ t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true))) :
    ∀ a : Fin R.diagram.nArc, 0 ≤ turnDet R.diagram a := by
  have hp : PositiveOrMarked ⟨D,T,ProcessedParentMarks.initial D T hconn⟩ :=
    fun d => Or.inl (hpos d)
  exact detached_child_turns_nonnegative t
    (negativeTurnsMarked_trace h (negativeTurnsMarked_initial D T hconn hturn) hp)
    (h.positiveOrMarked hp) c hc R

end DirectGLSSW.HOMFLY.SmoothingCornerGeometry
