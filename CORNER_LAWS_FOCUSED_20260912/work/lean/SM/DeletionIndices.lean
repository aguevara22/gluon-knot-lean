import SM.InsertionIndices
import Mathlib.Tactic.LinearCombination

/-! The induced cyclic index set after deleting vertex j. The child cut begins
at the old successor of j; its last vertex is the old predecessor of j. -/

namespace SM

variable {n : ℕ} [NeZero n]

def deletionIndex (j : ZMod (n + 1)) (i : ZMod n) : ZMod (n + 1) :=
  insertIndex i + (j + 1)

theorem deletionIndex_injective (j : ZMod (n + 1)) :
    Function.Injective (deletionIndex j) := by
  intro a b hab
  exact insertIndex_injective (add_right_cancel hab)

theorem deletionIndex_ne_deleted (j : ZMod (n + 1)) (i : ZMod n) :
    deletionIndex j i ≠ j := by
  intro he
  apply insertIndex_ne_inserted i
  rw [insertedIndex_eq_neg_one]
  dsimp [deletionIndex] at he
  linear_combination he

theorem deletionIndex_exhaust (j : ZMod (n + 1)) {k : ZMod (n + 1)}
    (hk : k ≠ j) : ∃ i : ZMod n, deletionIndex j i = k := by
  rcases insertion_indices_exhaust (k - (j + 1)) with he | ⟨i, he⟩
  · rw [insertedIndex_eq_neg_one] at he
    exact (hk (by linear_combination he)).elim
  · refine ⟨i, ?_⟩
    dsimp [deletionIndex]
    linear_combination -he

theorem deletionIndex_zero (j : ZMod (n + 1)) :
    deletionIndex j (0 : ZMod n) = j + 1 := by
  simp [deletionIndex, insertIndex_zero]

theorem deletionIndex_last (j : ZMod (n + 1)) :
    deletionIndex j (-1 : ZMod n) = j - 1 := by
  have he := insertIndex_last_add_one (n := n)
  rw [insertedIndex_eq_neg_one] at he
  dsimp [deletionIndex]
  linear_combination he

theorem deletionIndex_next (j : ZMod (n + 1)) {i : ZMod n} (hi : i ≠ -1) :
    deletionIndex j (i + 1) = deletionIndex j i + 1 := by
  simp only [deletionIndex, insertIndex_next hi]
  ring

theorem deletionIndex_ne_prev (j : ZMod (n + 1)) {i : ZMod n} (hi : i ≠ -1) :
    deletionIndex j i ≠ j - 1 := by
  rw [← deletionIndex_last j]
  exact fun he => hi (deletionIndex_injective j he)

theorem deletionIndex_not_incident (j : ZMod (n + 1)) {i : ZMod n} (hi : i ≠ -1) :
    ¬ incident j (deletionIndex j i) := by
  rintro (he | he)
  · exact deletionIndex_ne_prev j hi he
  · exact deletionIndex_ne_deleted j i he

end SM
