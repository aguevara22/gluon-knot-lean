import ProcessedParentHistory
import ProcessedRegularMarkExclusion
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract ProcessedParentMarks

/-- Actual endpoint regularity of a marked physical arc. -/
def RegularStateMark (s : MarkedParentState) (x : StateMarks s) : Prop :=
  (∀ d : Fin s.1.nCrossing, s.1.crossingVertex d ≠ s.1.arcSource x.val) ∧
  (∀ d : Fin s.1.nCrossing, s.1.crossingVertex d ≠ s.1.arcTarget x.val)

namespace MarkedParentStep

theorem markEmbedding_regular {s t : MarkedParentState} (h : MarkedParentStep s t)
    (x : StateMarks s) (hx : RegularStateMark s x) :
    RegularStateMark t (h.markEmbedding x) := by
  cases h with
  | switched S c hc hgood => exact hx
  | @smoothed D T S c hc hgood R =>
    change (∀ d : Fin R.diagram.nCrossing, R.diagram.crossingVertex d ≠
      R.diagram.arcSource (S.liftOldMark c hc R x)) ∧
      (∀ d : Fin R.diagram.nCrossing, R.diagram.crossingVertex d ≠
        R.diagram.arcTarget (S.liftOldMark c hc R x))
    have hreg := smooth_old_arc_regular_endpoints D c x.val hx.1 hx.2
    apply R.regular_arc_endpoints
    · rw [S.liftOldMark_map]
      exact hreg.1
    · rw [S.liftOldMark_map]
      exact hreg.2

theorem connector_freshTag_regular {s t : MarkedParentState} (h : MarkedParentStep s t)
    (hk : h.freshTag.1 = ProcessedMarkKind.connector) :
    RegularStateMark t h.freshTag.2 := by
  cases h with
  | switched S c hc hgood => cases hk
  | @smoothed D T S c hc hgood R =>
    change (∀ d : Fin R.diagram.nCrossing, R.diagram.crossingVertex d ≠
      R.diagram.arcSource (liftConnector D T c R)) ∧
      (∀ d : Fin R.diagram.nCrossing, R.diagram.crossingVertex d ≠
        R.diagram.arcTarget (liftConnector D T c R))
    apply R.regular_arc_endpoints
    · rw [liftConnector_map]
      exact smooth_connector_source_regular D c (firstVisitedBranch T c)
    · rw [liftConnector_map]
      exact smooth_connector_target_regular D c (firstVisitedBranch T c)
end MarkedParentStep

namespace MarkedParentTrace

theorem markEmbedding_regular {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (x : StateMarks s) (hx : RegularStateMark s x) :
    RegularStateMark t (h.markEmbedding x) := by
  induction h with
  | nil s => exact hx
  | cons step tail ih => exact ih (step.markEmbedding x) (step.markEmbedding_regular x hx)

theorem born_connector_regular {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (x : StateMarks t) (hx : (ProcessedMarkKind.connector, x) ∈ h.bornTags) :
    RegularStateMark t x := by
  induction h with
  | nil s => simp [bornTags] at hx
  | cons step tail ih =>
    change (ProcessedMarkKind.connector, x) ∈
      (step.freshTag.1, tail.markEmbedding step.freshTag.2) :: tail.bornTags at hx
    rcases List.mem_cons.mp hx with he | he
    · have hk := congrArg Prod.fst he
      have hxe := congrArg Prod.snd he
      dsimp at hk hxe
      rw [hxe]
      exact tail.markEmbedding_regular _ (step.connector_freshTag_regular hk.symm)
    · exact ih x he

/-- Every connector born in the literal history has both corners outside the next actual child. -/
theorem born_connector_corners_not_detached {s t : MarkedParentState}
    (h : MarkedParentTrace s t) (x : StateMarks t)
    (hx : (ProcessedMarkKind.connector, x) ∈ h.bornTags)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) :
    (¬ ∃ a : ComponentArc (smoothCrossing t.1 c)
        (rootSelfCutComponents t.1 c (t.2.2.connected _ _) (firstVisitedBranch t.2.1 c) (Sum.inl true)),
      (smoothCrossing t.1 c).arcSource a.val =
        (smoothCrossing t.1 c).arcSource (smoothArcEquiv t.1 (Sum.inl x.val))) ∧
    (¬ ∃ a : ComponentArc (smoothCrossing t.1 c)
        (rootSelfCutComponents t.1 c (t.2.2.connected _ _) (firstVisitedBranch t.2.1 c) (Sum.inl true)),
      (smoothCrossing t.1 c).arcSource a.val =
        (smoothCrossing t.1 c).arcTarget (smoothArcEquiv t.1 (Sum.inl x.val))) := by
  have hreg := h.born_connector_regular x hx
  exact t.2.2.regular_mark_endpoints_not_detached c hc x hreg.1 hreg.2

end MarkedParentTrace
end DirectGLSSW.HOMFLY
