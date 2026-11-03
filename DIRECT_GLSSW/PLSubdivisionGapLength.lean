import PLSubdivisionMarkedPowers
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
open Equiv MarkedCycleGaps
attribute [local instance] Classical.propDecidable
variable {ι : Type*} (D : PLLinkDiagram) (mark : ι → Fin D.nArc)
    (hinj : Function.Injective mark) (sel m : ι)

theorem marked_gap_prefix_not_marked (n : ℕ) (hn0 : 0 < n)
    (hn : n < gapLength D.continuation mark m) :
    ¬ ∃ j : ι, (continuation D (mark sel) ^ n)
        (markedArcLift D (mark sel) (mark m)) = markedArcLift D (mark sel) (mark j) := by
  rintro ⟨j,hj⟩
  rw [marked_gap_prefix D mark sel m n hn] at hj
  exact gapLength_minimal D.continuation mark m n hn0 hn
    ⟨j,markedArcLift_injective D (mark sel) hj⟩

/-- Subdividing a marked incoming port increases exactly the gap ending at that mark. -/
theorem subdivision_gapLength :
    gapLength (continuation D (mark sel)) (fun j=>markedArcLift D (mark sel) (mark j)) m =
      gapLength D.continuation mark m +
        if nextLabel D.continuation mark hinj m = sel then 1 else 0 := by
  let d := gapLength D.continuation mark m
  have hd : 0 < d := gapLength_pos D.continuation mark m
  by_cases hnext : nextLabel D.continuation mark hinj m = sel
  · rw [if_pos hnext]
    apply Eq.symm
    apply (gapLength_characterization _ _ m _).mpr
    refine ⟨by omega,?_,?_⟩
    · refine ⟨sel,?_⟩
      rw [pow_succ',Perm.mul_apply,marked_gap_end D mark sel m hinj,hnext,
        continuation_selected_first]
      simp only [markedArcLift,eq_self_iff_true,ite_true]
    · intro n hn hnlt
      by_cases hnd : n < d
      · exact marked_gap_prefix_not_marked D mark sel m n hn hnd
      · have he : n=d := by omega
        subst n
        rintro ⟨j,hj⟩
        rw [marked_gap_end D mark sel m hinj,hnext] at hj
        exact markedArcLift_ne_first D (mark sel) (mark j) hj.symm
  · simp only [if_neg hnext,Nat.add_zero]
    apply Eq.symm
    apply (gapLength_characterization _ _ m _).mpr
    refine ⟨hd,?_,fun n hn hnlt=>marked_gap_prefix_not_marked D mark sel m n hn hnlt⟩
    refine ⟨nextLabel D.continuation mark hinj m,?_⟩
    rw [marked_gap_end D mark sel m hinj]
    have he : mark (nextLabel D.continuation mark hinj m) ≠ mark sel := fun he=>hnext (hinj he)
    exact (if_neg he).symm

/-- The new first return reaches the same actual marked label. -/
theorem subdivision_gapReturn :
    (continuation D (mark sel) ^ gapLength (continuation D (mark sel))
      (fun j=>markedArcLift D (mark sel) (mark j)) m)
      (markedArcLift D (mark sel) (mark m)) =
      markedArcLift D (mark sel) (mark (nextLabel D.continuation mark hinj m)) := by
  rw [subdivision_gapLength D mark hinj sel m]
  by_cases hnext : nextLabel D.continuation mark hinj m = sel
  · rw [if_pos hnext,pow_succ',Perm.mul_apply,marked_gap_end D mark sel m hinj,hnext,
      continuation_selected_first]
    simp only [markedArcLift,eq_self_iff_true,ite_true]
  · simp only [if_neg hnext,Nat.add_zero]
    rw [marked_gap_end D mark sel m hinj]
    have he : mark (nextLabel D.continuation mark hinj m) ≠ mark sel := fun he=>hnext (hinj he)
    exact (if_neg he).symm

theorem subdivision_nextLabel :
    nextLabel (continuation D (mark sel)) (fun j=>markedArcLift D (mark sel) (mark j))
      ((markedArcLift_injective D (mark sel)).comp hinj) m =
      nextLabel D.continuation mark hinj m := by
  apply hinj
  apply markedArcLift_injective D (mark sel)
  exact (nextLabel_spec (continuation D (mark sel)) _
    ((markedArcLift_injective D (mark sel)).comp hinj) m).symm.trans
    (subdivision_gapReturn D mark hinj sel m)

theorem subdivision_next [Fintype ι] :
    next (continuation D (mark sel)) (fun j=>markedArcLift D (mark sel) (mark j))
      ((markedArcLift_injective D (mark sel)).comp hinj) = next D.continuation mark hinj := by
  ext j
  exact subdivision_nextLabel D mark hinj sel j

end DirectGLSSW.HOMFLY.ArcSubdivision
