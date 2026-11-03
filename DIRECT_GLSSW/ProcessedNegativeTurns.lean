import SmoothingNegativeTurnOrigins
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SmoothingCornerGeometry
open PermutationOrbits LowestRowContract ProcessedParentMarks
attribute [local instance] Classical.propDecidable

/-- Literal inductive geometric state: every right turn is at an endpoint of
a processed physical arc whose endpoints are regular. Initial empty marks force
all turns to be nonnegative; this property is proved through actual operations. -/
def NegativeTurnsMarked (s : MarkedParentState) : Prop :=
  ∀ e : Fin s.1.nArc, turnDet s.1 e < 0 →
    ∃ x : StateMarks s, RegularStateMark s x ∧
      (s.1.arcTarget e = s.1.arcSource x.val ∨ s.1.arcTarget e = s.1.arcTarget x.val)

/-- Endpoint incidence pulls back through the exact extraction maps. -/
theorem restriction_target_at_mark {D : PLLinkDiagram} {C : Component D.continuation}
    (R : ComponentRestriction D C) (a b : Fin R.diagram.nArc)
    (h : D.arcTarget (R.arcEquiv a).val = D.arcSource (R.arcEquiv b).val ∨
      D.arcTarget (R.arcEquiv a).val = D.arcTarget (R.arcEquiv b).val) :
    R.diagram.arcTarget a = R.diagram.arcSource b ∨
      R.diagram.arcTarget a = R.diagram.arcTarget b := by
  rcases h with h | h
  · left
    apply R.vertexEquiv.injective
    apply Subtype.ext
    rw [R.target_eq,R.source_eq]
    exact h
  · right
    apply R.vertexEquiv.injective
    apply Subtype.ext
    rw [R.target_eq,R.target_eq]
    exact h

/-- The state is preserved by the actual first-under operations; selected
positivity is derived from the independently preserved sign/mark state. -/
theorem negativeTurnsMarked_step {s t : MarkedParentState} (step : MarkedParentStep s t)
    (hs : NegativeTurnsMarked s) (hp : PositiveOrMarked s) : NegativeTurnsMarked t := by
  cases step with
  | @switched D T S c hc hgood =>
    intro e he
    obtain ⟨x,hx,hinc⟩ := hs e he
    let st := MarkedParentStep.switched S c hc hgood
    exact ⟨st.markEmbedding x,st.markEmbedding_regular x hx,hinc⟩
  | @smoothed D T S c hc hgood R =>
    let st := MarkedParentStep.smoothed S c hc hgood R
    intro a hneg
    have hnegE : turnDet (smoothCrossing D c) (R.arcEquiv a).val < 0 := by
      rw [← restriction_turnDet]
      exact hneg
    have hcut := hp.bad_crossing_positive c hc
    rcases negative_smoothing_turn_origin D T c hc hcut (R.arcEquiv a).val hnegE with
      ⟨e,hmap,_,hold⟩ | hmap | hmap
    · obtain ⟨x,hx,hinc⟩ := hs e hold
      let y := st.markEmbedding x
      have hmy : (R.arcEquiv y.val).val = smoothArcEquiv D (Sum.inl x.val) :=
        S.liftOldMark_map c hc R x
      refine ⟨y,st.markEmbedding_regular x hx,?_⟩
      apply restriction_target_at_mark R a y.val
      rw [hmap,hmy]
      exact old_target_at_regular_mark D c e x.val hx.1 hx.2 hinc
    · let y := st.freshTag.2
      have hmy : (R.arcEquiv y.val).val =
          smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)) :=
        liftConnector_map D T c R
      refine ⟨y,st.connector_freshTag_regular rfl,?_⟩
      apply restriction_target_at_mark R a y.val
      rw [hmap,hmy]
      left
      have hi := (smoothCrossing D c).continuation_incidence
        (smoothArcEquiv D (Sum.inl (D.incoming c (firstVisitedBranch T c))))
      rw [Gemini.smooth_step_incoming] at hi
      exact hi
    · let y := st.freshTag.2
      have hmy : (R.arcEquiv y.val).val =
          smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)) :=
        liftConnector_map D T c R
      refine ⟨y,st.connector_freshTag_regular rfl,?_⟩
      apply restriction_target_at_mark R a y.val
      rw [hmap,hmy]
      exact Or.inr rfl

/-- Finite actual histories preserve the negative-turn endpoint invariant. -/
theorem negativeTurnsMarked_trace {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (hs : NegativeTurnsMarked s) (hp : PositiveOrMarked s) : NegativeTurnsMarked t := by
  induction h with
  | nil s => exact hs
  | cons step tail ih =>
    exact ih (negativeTurnsMarked_step step hs hp) (step.positiveOrMarked hp)

end DirectGLSSW.HOMFLY.SmoothingCornerGeometry
