import PLMarkedRefinementState
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
open Equiv MarkedCycleGaps
attribute [local instance] Classical.propDecidable
variable {ι : Type*} (D : PLLinkDiagram) (mark : ι → Fin D.nArc)

/-- The unchanged crossing labels, tracked through the actual finite subdivisions. -/
def markedRefinementCrossingEquiv : (l : List ι) → Fin D.nCrossing ≃ Fin (markedRefinementState D mark l).1.nCrossing
  | [] => Equiv.refl _
  | _ :: l => markedRefinementCrossingEquiv l

/-- Track the terminal half of every original incoming arc through the actual subdivisions. -/
def markedRefinementArcLift : (l : List ι) → Fin D.nArc → Fin (markedRefinementState D mark l).1.nArc
  | [], a => a
  | sel :: l, a => markedArcLift (markedRefinementState D mark l).1
      ((markedRefinementState D mark l).2 sel) (markedRefinementArcLift l a)

theorem markedRefinementArcLift_injective (l : List ι) :
    Function.Injective (markedRefinementArcLift D mark l) := by
  induction l with
  | nil => exact Function.injective_id
  | cons sel l ih => exact (markedArcLift_injective (markedRefinementState D mark l).1
      ((markedRefinementState D mark l).2 sel)).comp ih

theorem markedRefinement_mark (l : List ι) (j : ι) :
    (markedRefinementState D mark l).2 j = markedRefinementArcLift D mark l (mark j) := by
  induction l with
  | nil => rfl
  | cons sel l ih => exact congrArg (markedArcLift (markedRefinementState D mark l).1
      ((markedRefinementState D mark l).2 sel)) ih

theorem markedRefinement_incoming (l : List ι) (c : Fin D.nCrossing) (i : Fin 2) :
    (markedRefinementState D mark l).1.incoming (markedRefinementCrossingEquiv D mark l c) i =
      markedRefinementArcLift D mark l (D.incoming c i) := by
  induction l with
  | nil => rfl
  | cons sel l ih =>
    change incoming (markedRefinementState D mark l).1 ((markedRefinementState D mark l).2 sel)
      (markedRefinementCrossingEquiv D mark l c) i = _
    rw [← markedArcLift_incoming,ih]
    rfl

theorem markedRefinement_through (l : List ι) (c : Fin D.nCrossing) :
    (markedRefinementState D mark l).1.through (markedRefinementCrossingEquiv D mark l c) = D.through c := by
  induction l with
  | nil => rfl
  | cons sel l ih => exact ih

theorem markedRefinement_overBranch (l : List ι) (c : Fin D.nCrossing) :
    (markedRefinementState D mark l).1.overBranch (markedRefinementCrossingEquiv D mark l c) = D.overBranch c := by
  induction l with
  | nil => rfl
  | cons sel l ih => exact ih

theorem markedRefinement_crossingSign (l : List ι) (c : Fin D.nCrossing) :
    crossingSign (markedRefinementState D mark l).1 (markedRefinementCrossingEquiv D mark l c) = crossingSign D c := by
  induction l with
  | nil => rfl
  | cons sel l ih =>
    exact (subdivideArc_crossingSign (markedRefinementState D mark l).1
      ((markedRefinementState D mark l).2 sel) (1/2:ℝ) (by norm_num) (by norm_num)
      (markedRefinementCrossingEquiv D mark l c)).trans ih

end DirectGLSSW.HOMFLY.ArcSubdivision
