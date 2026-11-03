import PLSubdivisionMarkedArcs
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
open Equiv MarkedCycleGaps
attribute [local instance] Classical.propDecidable
variable (D : PLLinkDiagram) (e : Fin D.nArc)

theorem markedArcLift_ne_first (a : Fin D.nArc) :
    markedArcLift D e a ≠ e.castSucc := by
  by_cases h : a=e
  · rw [markedArcLift,if_pos h]
    exact Ne.symm (Fin.ne_of_lt (Fin.castSucc_lt_last e))
  · rw [markedArcLift,if_neg h]
    exact fun he=>h (Fin.ext (congrArg (fun x : Fin (D.nArc+1)=>x.val) he))

/-- Before the selected arc is encountered, all marked-terminal coordinates agree literally. -/
theorem pow_markedArcLift (a : Fin D.nArc) (n : ℕ)
    (ha : ∀ j : ℕ, 0 < j → j ≤ n → (D.continuation ^ j) a ≠ e) :
    (continuation D e ^ n) (markedArcLift D e a) =
      markedArcLift D e ((D.continuation ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',Perm.mul_apply,ih (fun j hj hjn=>ha j hj (by omega))]
    rw [continuation_markedArcLift]
    have hne : D.continuation ((D.continuation ^ n) a) ≠ e := by
      simpa only [pow_succ',Perm.mul_apply] using ha (n+1) (by omega) (by omega)
    rw [pow_succ',Perm.mul_apply,markedArcLift,if_neg hne]

variable {ι : Type*} (mark : ι → Fin D.nArc) (sel m : ι)

/-- All proper positive prefixes of an original marked gap avoid the selected incoming mark. -/
theorem marked_gap_prefix (n : ℕ) (hn : n < gapLength D.continuation mark m) :
    (continuation D (mark sel) ^ n) (markedArcLift D (mark sel) (mark m)) =
      markedArcLift D (mark sel) ((D.continuation ^ n) (mark m)) := by
  apply pow_markedArcLift
  intro j hj hjn he
  exact gapLength_minimal D.continuation mark m j hj (by omega) ⟨sel,he⟩

/-- At the old gap length the subdivision has reached the first half of the old target arc. -/
theorem marked_gap_end (hinj : Function.Injective mark) :
    (continuation D (mark sel) ^ gapLength D.continuation mark m)
      (markedArcLift D (mark sel) (mark m)) =
      (mark (nextLabel D.continuation mark hinj m)).castSucc := by
  let d := gapLength D.continuation mark m
  have hd : 0 < d := gapLength_pos D.continuation mark m
  have hsplit : d = (d-1)+1 := (Nat.sub_add_cancel hd).symm
  change (continuation D (mark sel) ^ d) _ = _
  rw [hsplit,pow_succ',Perm.mul_apply,marked_gap_prefix D mark sel m (d-1) (by change d-1<d;omega),continuation_markedArcLift]
  have he : D.continuation ((D.continuation ^ (d-1)) (mark m)) =
      mark (nextLabel D.continuation mark hinj m) := by
    rw [← Perm.mul_apply,← pow_succ',← hsplit]
    exact nextLabel_spec D.continuation mark hinj m
  rw [he]

end DirectGLSSW.HOMFLY.ArcSubdivision
