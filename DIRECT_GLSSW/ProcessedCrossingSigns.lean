import ProcessedParentHistory
import ComponentRestrictionSigns
import DirectGLSSW.HOMFLY.HOMFLYSwitchChoiceFacts
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract ProcessedParentMarks

/-- Every nonpositive crossing has a genuinely processed incoming arc. -/
def PositiveOrMarked (s : MarkedParentState) : Prop :=
  ∀ d : Fin s.1.nCrossing, crossingSign s.1 d = Sign.pos ∨
    ∃ i : Fin 2, s.1.incoming d i ∈ s.2.2.marks

namespace MarkedParentStep

theorem positiveOrMarked {s t : MarkedParentState} (h : MarkedParentStep s t)
    (hs : PositiveOrMarked s) : PositiveOrMarked t := by
  cases h with
  | @switched D T S c hc hgood =>
    intro d
    by_cases hd : d = c
    · subst d
      right
      exact ⟨firstVisitedBranch T c, Finset.mem_insert_self _ _⟩
    · rcases hs d with hp | ⟨i,hi⟩
      · left
        exact (crossingSign_switchCrossing_of_ne D c d hd).trans hp
      · right
        exact ⟨i, Finset.mem_insert_of_mem hi⟩
  | @smoothed D T S c hc hgood R =>
    intro d
    let old := (smoothCrossingEquiv D c).symm (R.crossingEquiv d).val
    have he : smoothCrossingEquiv D c old = (R.crossingEquiv d).val :=
      (smoothCrossingEquiv D c).apply_symm_apply _
    rcases hs old.val with hp | ⟨i,hi⟩
    · left
      rw [R.crossingSign_eq, ← he, crossingSign_smoothRetained]
      exact hp
    · right
      refine ⟨i, ?_⟩
      let x : {x : Fin D.nArc // x ∈ S.marks} := ⟨D.incoming old.val i,hi⟩
      have hlift : S.liftOldMark c hc R x = R.diagram.incoming d i := by
        apply R.arcEquiv.injective
        apply Subtype.ext
        rw [S.liftOldMark_map, R.incoming_eq, ← he, parentRoot_retained_incoming]
      rw [← hlift]
      exact S.liftOldMark_mem_smoothStep c hc hgood R x
end MarkedParentStep

namespace MarkedParentTrace

theorem positiveOrMarked {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (hs : PositiveOrMarked s) : PositiveOrMarked t := by
  induction h with
  | nil s => exact hs
  | cons step tail ih => exact ih (step.positiveOrMarked hs)

/-- Every retained self-crossing of the next actual detached child is positive. -/
theorem detached_crossings_positive {s t : MarkedParentState}
    (h : MarkedParentTrace s t) (hs : PositiveOrMarked s)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _) (firstVisitedBranch t.2.1 c) (Sum.inl true))) :
    ∀ d : Fin R.diagram.nCrossing, crossingSign R.diagram d = Sign.pos := by
  intro d
  let old := (smoothCrossingEquiv t.1 c).symm (R.crossingEquiv d).val
  have he : smoothCrossingEquiv t.1 c old = (R.crossingEquiv d).val :=
    (smoothCrossingEquiv t.1 c).apply_symm_apply _
  rcases h.positiveOrMarked hs old.val with hp | ⟨i,hi⟩
  · rw [R.crossingSign_eq, ← he, crossingSign_smoothRetained]
    exact hp
  · let x : StateMarks t := ⟨t.1.incoming old.val i,hi⟩
    have hne := t.2.2.mark_not_detached c hc x
    have hp := (R.crossingEquiv d).property i
    rw [← he, parentRoot_retained_incoming] at hp
    exact (hne hp).elim
end MarkedParentTrace
end DirectGLSSW.HOMFLY
