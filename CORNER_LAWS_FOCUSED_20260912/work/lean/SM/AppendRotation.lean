import SM.InsertedTuple
import SM.InsertionSum
import SM.RotationNumber

/-! Actual insertion preserves every old principal turn and adds one zero
turn. All turns are independently computed from the constructed new tuple. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem regularPair_appendVertex_old {P : LabelledTuple n} (h : Regular P) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (i : ZMod n) :
    RegularPair (edge (appendVertex P t) (insertIndex i - 1))
      (edge (appendVertex P t) (insertIndex i)) := by
  rw [incoming_appendVertex_old_scaled, edge_appendVertex_old_scaled]
  exact regularPair_smul (by split_ifs <;> linarith) (by split_ifs <;> linarith) (h i)

theorem regularPair_appendVertex_new {P : LabelledTuple n} (h : Regular P) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    RegularPair (edge (appendVertex P t) (insertedIndex n - 1))
      (edge (appendVertex P t) (insertedIndex n)) := by
  rw [insertedIndex_prev, edge_appendVertex_last, edge_appendVertex_new]
  exact regularPair_smul ht0 (sub_pos.mpr ht1) (regularPair_self (h (-1)).2.1)

theorem regular_appendVertex {P : LabelledTuple n} (h : Regular P) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : Regular (appendVertex P t) := by
  intro j
  rcases insertion_indices_exhaust j with rfl | ⟨i, rfl⟩
  · exact regularPair_appendVertex_new h ht0 ht1
  · exact regularPair_appendVertex_old h ht0 ht1 i

theorem principalTurn_appendVertex_old (P : LabelledTuple n) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (i : ZMod n) :
    principalTurn (appendVertex P t) (insertIndex i) = principalTurn P i := by
  unfold principalTurn
  rw [incoming_appendVertex_old_scaled, edge_appendVertex_old_scaled]
  exact principalAngle_smul (by split_ifs <;> linarith) (by split_ifs <;> linarith) _ _

theorem principalTurn_appendVertex_new {P : LabelledTuple n} (h : Regular P) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    principalTurn (appendVertex P t) (insertedIndex n) = 0 := by
  rw [principalTurn, insertedIndex_prev, edge_appendVertex_last, edge_appendVertex_new,
    principalAngle_smul ht0 (sub_pos.mpr ht1), principalAngle_self (h (-1)).2.1]

theorem sum_principalTurn_appendVertex {P : LabelledTuple n} (h : Regular P) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    (∑ j : ZMod (n + 1), principalTurn (appendVertex P t) j) =
      ∑ i : ZMod n, principalTurn P i := by
  rw [sum_insertion_indices]
  simp_rw [principalTurn_appendVertex_old P ht0 ht1]
  rw [principalTurn_appendVertex_new h ht0 ht1, add_zero]

theorem rotationNumber_appendVertex {P : LabelledTuple n} (h : Regular P) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : rotationNumber (appendVertex P t) = rotationNumber P := by
  unfold rotationNumber
  rw [sum_principalTurn_appendVertex h ht0 ht1]

end SM
