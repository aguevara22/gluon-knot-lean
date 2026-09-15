namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- On the actual two-visit fiber, selecting this crossing is exactly the
transposition of its constructed pair; all other crossing fibers are fixed. -/
theorem selectedVisitTwin_singleton {P : LabelledTuple n} (v w : Visit P) :
    selectedVisitTwin {v.1} w = Equiv.swap v (visitTwin v) w := by
  by_cases hc : w.1 = v.1
  · rcases visit_eq_or_twin v w hc with hw | hw
    · subst w
      simp [selectedVisitTwin]
    · subst w
      simp [selectedVisitTwin]
  · have hwv : w ≠ v := fun h => hc (congrArg (fun x : Visit P => x.1) h)
    have hwt : w ≠ visitTwin v := by
      intro h
      apply hc
      rw [h, visitTwin_crossing]
    rw [Equiv.swap_apply_of_ne_of_ne hwv hwt]
    simp [selectedVisitTwin, hc]

theorem selectedVisitTwinPerm_singleton {P : LabelledTuple n} (v : Visit P) :
    selectedVisitTwinPerm {v.1} = Equiv.swap v (visitTwin v) := by
  ext w
  exact selectedVisitTwin_singleton v w

/-- The full marked permutation fixes original vertices and exchanges exactly
the two distinct actual marks of this crossing. -/
theorem selectedMarkPerm_singleton {P : LabelledTuple n} (v : Visit P) :
    selectedMarkPerm {v.1} =
      Equiv.swap (Sum.inr v : Mark P) (Sum.inr (visitTwin v)) := by
  rw [selectedMarkPerm, selectedVisitTwinPerm_singleton]
  exact Equiv.Perm.sumCongr_refl_swap v (visitTwin v)

/-- Adding an unselected actual crossing swaps its two outgoing slots in the
current successor. Right multiplication applies that transposition first. -/
theorem smoothingSuccessor_insert (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    smoothingSuccessor hn hP (insert v.1 S) =
      smoothingSuccessor hn hP S *
        Equiv.swap (Sum.inr v : Mark P) (Sum.inr (visitTwin v)) := by
  have hS : insert v.1 S = S ∪ {v.1} := by
    ext c
    simp [or_comm]
  rw [hS, smoothingSuccessor_union_of_disjoint hn hP S {v.1}
    (Finset.disjoint_singleton_right.mpr hv), selectedMarkPerm_singleton]
  rfl

theorem smoothingSuccessor_insert_visit (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    smoothingSuccessor hn hP (insert v.1 S) (Sum.inr v) =
      smoothingSuccessor hn hP S (Sum.inr (visitTwin v)) := by
  rw [smoothingSuccessor_insert hn hP S v hv, Equiv.Perm.mul_apply,
    Equiv.swap_apply_left]

theorem smoothingSuccessor_insert_twin (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    smoothingSuccessor hn hP (insert v.1 S) (Sum.inr (visitTwin v)) =
      smoothingSuccessor hn hP S (Sum.inr v) := by
  rw [smoothingSuccessor_insert hn hP S v hv, Equiv.Perm.mul_apply,
    Equiv.swap_apply_right]

/-- Every other marked outgoing slot is unchanged by this one reconnection. -/
theorem smoothingSuccessor_insert_other (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (a : Mark P) (hav : a ≠ Sum.inr v) (hat : a ≠ Sum.inr (visitTwin v)) :
    smoothingSuccessor hn hP (insert v.1 S) a = smoothingSuccessor hn hP S a := by
  rw [smoothingSuccessor_insert hn hP S v hv, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hav hat]

end
end SM.Carrier
