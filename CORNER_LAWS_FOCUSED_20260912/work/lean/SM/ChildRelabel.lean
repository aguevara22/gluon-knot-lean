import SM.ContactHalfInteriors
import SM.DeletedTuple

/-! Cyclic parent relabelling leaves the actual canonically cut children
unchanged. Heterogeneous equality only transports the proved equal half sizes. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem deleteVertex_relabel (P : LabelledTuple (n + 1)) (j r : ZMod (n + 1)) :
    deleteVertex (shift r P) (j - r) = deleteVertex P j := by
  funext i
  simp only [deleteVertex, shift, deletionIndex]
  congr 1
  ring

theorem firstHalf_relabel (P : LabelledTuple n) (M a r : ZMod n) :
    HEq (firstHalf (shift r P) (M - r) (a - r)) (firstHalf P M a) := by
  have he : a - r - (M - r) = a - M := by ring
  change HEq
    (fun i : ZMod ((a - r - (M - r)).val + 1) => P ((M - r + (i.val : ZMod n)) + r))
    (fun i : ZMod ((a - M).val + 1) => P (M + (i.val : ZMod n)))
  rw [he]
  apply heq_of_eq
  funext i
  congr 1
  ring

theorem secondHalf_relabel (P : LabelledTuple n) (M a r : ZMod n) :
    HEq (secondHalf (shift r P) (M - r) (a - r)) (secondHalf P M a) := by
  have he : a - r - (M - r) = a - M := by ring
  change HEq
    (fun i : ZMod (n - (a - r - (M - r)).val) =>
      P ((if i = 0 then M - r else a - r + (i.val : ZMod n)) + r))
    (fun i : ZMod (n - (a - M).val) => P (if i = 0 then M else a + (i.val : ZMod n)))
  rw [he]
  apply heq_of_eq
  funext i
  by_cases hi : i = 0
  · simp only [hi, ↓reduceIte, shift, sub_add_cancel]
  · simp only [hi, ↓reduceIte, shift]
    congr 1
    ring

end SM
