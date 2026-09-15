import SM.Polygon
import Lean.Elab.Tactic.Omega

/-! Concrete indices for appending one vertex at the cyclic cut. Old labels
keep their natural representatives; the new label has representative n. -/

namespace SM

variable {n : ℕ} [NeZero n]

def insertIndex (i : ZMod n) : ZMod (n + 1) := (i.val : ZMod (n + 1))

def insertedIndex (n : ℕ) : ZMod (n + 1) := (n : ZMod (n + 1))

theorem insertIndex_val (i : ZMod n) : (insertIndex i).val = i.val :=
  ZMod.val_natCast_of_lt (lt_trans i.val_lt (Nat.lt_succ_self n))

theorem insertedIndex_val (n : ℕ) : (insertedIndex n).val = n :=
  ZMod.val_natCast_of_lt (Nat.lt_succ_self n)

theorem insertIndex_injective : Function.Injective (insertIndex (n := n)) := by
  intro i j hij
  apply ZMod.val_injective n
  simpa only [insertIndex_val] using congrArg ZMod.val hij

theorem insertIndex_ne_inserted (i : ZMod n) : insertIndex i ≠ insertedIndex n := by
  intro he
  have hv := congrArg ZMod.val he
  rw [insertIndex_val, insertedIndex_val] at hv
  exact i.val_lt.ne hv

theorem insertIndex_zero : insertIndex (0 : ZMod n) = 0 := by simp [insertIndex]

theorem insertedIndex_add_one : insertedIndex n + 1 = 0 := by
  change (n : ZMod (n + 1)) + 1 = 0
  calc
    (n : ZMod (n + 1)) + 1 = ((n + 1 : ℕ) : ZMod (n + 1)) := by simp
    _ = 0 := ZMod.natCast_self _

theorem insertedIndex_eq_neg_one : insertedIndex n = -1 :=
  eq_neg_iff_add_eq_zero.mpr insertedIndex_add_one

theorem insertion_indices_exhaust (j : ZMod (n + 1)) :
    j = insertedIndex n ∨ ∃ i : ZMod n, j = insertIndex i := by
  by_cases hj : j.val < n
  · right
    refine ⟨(j.val : ZMod n), ?_⟩
    apply ZMod.val_injective (n + 1)
    rw [insertIndex_val, ZMod.val_natCast_of_lt hj]
  · left
    apply ZMod.val_injective (n + 1)
    rw [insertedIndex_val]
    have hv := j.val_lt
    omega

theorem last_index_val_succ : (-1 : ZMod n).val + 1 = n := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => simp only [ZMod.val_neg_one]

theorem insertIndex_last_add_one : insertIndex (-1 : ZMod n) + 1 = insertedIndex n := by
  change (((-1 : ZMod n).val : ℕ) : ZMod (n + 1)) + 1 = (n : ZMod (n + 1))
  simpa only [Nat.cast_add, Nat.cast_one] using
    congrArg (fun k : ℕ => (k : ZMod (n + 1))) (last_index_val_succ (n := n))

theorem insertIndex_next {i : ZMod n} (hi : i ≠ -1) :
    insertIndex (i + 1) = insertIndex i + 1 := by
  have hlt : i.val + 1 < n := by
    have hv := i.val_lt
    by_contra hn
    have he : i.val + 1 = n := by omega
    apply hi
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val, ZMod.natCast_self] using
      congrArg (fun k : ℕ => (k : ZMod n)) he
  have hv : (i + 1).val = i.val + 1 := by
    have he : i + 1 = ((i.val + 1 : ℕ) : ZMod n) := by
      simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    exact (congrArg ZMod.val he).trans (ZMod.val_natCast_of_lt hlt)
  simp only [insertIndex, hv, Nat.cast_add, Nat.cast_one]

theorem insertIndex_prev {i : ZMod n} (hi : i ≠ 0) :
    insertIndex i - 1 = insertIndex (i - 1) := by
  have hp : i - 1 ≠ -1 := by
    intro he
    apply hi
    simpa only [sub_add_cancel, neg_add_cancel] using
      congrArg (fun j : ZMod n => j + 1) he
  have he := insertIndex_next hp
  rw [sub_add_cancel] at he
  rw [he, add_sub_cancel_right]

theorem insertIndex_zero_prev : insertIndex (0 : ZMod n) - 1 = insertedIndex n := by
  rw [insertIndex_zero, zero_sub, insertedIndex_eq_neg_one]

theorem insertedIndex_prev : insertedIndex n - 1 = insertIndex (-1 : ZMod n) := by
  rw [← insertIndex_last_add_one, add_sub_cancel_right]

end SM
