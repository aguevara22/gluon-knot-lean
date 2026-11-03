import PLSubdivisionGapLength
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
open Equiv MarkedCycleGaps
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

/-- A literal finite sequence of valid midpoint subdivisions at the named incoming marks. -/
def markedRefinementState (D : PLLinkDiagram) (mark : ι → Fin D.nArc) :
    List ι → Σ E : PLLinkDiagram, ι → Fin E.nArc
  | [] => ⟨D,mark⟩
  | sel :: l =>
    let s := markedRefinementState D mark l
    ⟨subdivideArc s.1 (s.2 sel) (1/2:ℝ) (by norm_num) (by norm_num),
      fun j=>markedArcLift s.1 (s.2 sel) (s.2 j)⟩

variable (D : PLLinkDiagram) (mark : ι → Fin D.nArc) (hinj : Function.Injective mark)

include hinj in
theorem markedRefinement_injective (l : List ι) :
    Function.Injective (markedRefinementState D mark l).2 := by
  induction l with
  | nil => exact hinj
  | cons sel l ih => exact (markedArcLift_injective (markedRefinementState D mark l).1
      ((markedRefinementState D mark l).2 sel)).comp ih

theorem markedRefinement_nextLabel (l : List ι) (m : ι) :
    nextLabel (markedRefinementState D mark l).1.continuation (markedRefinementState D mark l).2
      (markedRefinement_injective D mark hinj l) m = nextLabel D.continuation mark hinj m := by
  induction l with
  | nil => rfl
  | cons sel l ih =>
    exact (subdivision_nextLabel (markedRefinementState D mark l).1
      (markedRefinementState D mark l).2 (markedRefinement_injective D mark hinj l) sel m).trans ih

theorem markedRefinement_gapLength (l : List ι) (m : ι) :
    gapLength (markedRefinementState D mark l).1.continuation (markedRefinementState D mark l).2 m =
      gapLength D.continuation mark m + l.count (nextLabel D.continuation mark hinj m) := by
  induction l with
  | nil => rfl
  | cons sel l ih =>
    have hs := subdivision_gapLength (markedRefinementState D mark l).1
      (markedRefinementState D mark l).2 (markedRefinement_injective D mark hinj l) sel m
    change gapLength (continuation (markedRefinementState D mark l).1 ((markedRefinementState D mark l).2 sel))
      (fun j=>markedArcLift (markedRefinementState D mark l).1 ((markedRefinementState D mark l).2 sel)
        ((markedRefinementState D mark l).2 j)) m = _
    rw [hs,ih,markedRefinement_nextLabel D mark hinj l m]
    by_cases he : nextLabel D.continuation mark hinj m = sel
    · simp only [List.count_cons,he,eq_self_iff_true,ite_true,beq_self_eq_true,Nat.add_assoc]
    · have hrev : sel ≠ nextLabel D.continuation mark hinj m := Ne.symm he
      simp [List.count_cons,he,hrev]

theorem markedRefinement_nCrossing (l : List ι) :
    (markedRefinementState D mark l).1.nCrossing = D.nCrossing := by
  induction l with
  | nil => rfl
  | cons sel l ih => exact ih

theorem markedRefinement_nArc (l : List ι) :
    (markedRefinementState D mark l).1.nArc = D.nArc + l.length := by
  induction l with
  | nil => rfl
  | cons sel l ih =>
    change (markedRefinementState D mark l).1.nArc+1 = D.nArc+(l.length+1)
    rw [ih,Nat.add_assoc]

theorem markedRefinement_normalizedEvaluator_eq
    (H : (E : PLLinkDiagram) → 0 < E.nArc → Coefficients.HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H) (l : List ι) (hD : 0 < D.nArc) :
    H (markedRefinementState D mark l).1 (by rw [markedRefinement_nArc];omega) = H D hD := by
  induction l with
  | nil => rfl
  | cons sel l ih =>
    exact (SignedArcContraction.normalizedEvaluator_eq H hH
      (subdivideArc_contraction (markedRefinementState D mark l).1
        ((markedRefinementState D mark l).2 sel) (1/2:ℝ) (by norm_num) (by norm_num)) _ _).trans ih

end DirectGLSSW.HOMFLY.ArcSubdivision
