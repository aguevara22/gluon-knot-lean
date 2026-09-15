import SM.InsertionIndices
import Mathlib.Tactic.LinearCombination

/-! An actual consecutive range of parent labels, retaining the child's
cyclic cut. Injectivity is proved from the size bound, not supplied as data. -/

namespace SM

variable {n k : ℕ} [NeZero n] [NeZero k]

def cyclicRangeIndex (s : ZMod n) (i : ZMod k) : ZMod n := s + (i.val : ZMod n)

theorem cyclicRangeIndex_injective (hk : k ≤ n) (s : ZMod n) :
    Function.Injective (cyclicRangeIndex (k := k) s) := by
  intro i j he
  have hh := add_left_cancel he
  have hv := congrArg ZMod.val hh
  rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le i.val_lt hk),
    ZMod.val_natCast_of_lt (lt_of_lt_of_le j.val_lt hk)] at hv
  exact ZMod.val_injective k hv

theorem cyclicRangeIndex_zero (s : ZMod n) : cyclicRangeIndex (k := k) s 0 = s := by
  simp [cyclicRangeIndex]

theorem zmod_val_next_of_ne_last {i : ZMod k} (hi : i ≠ -1) : (i + 1).val = i.val + 1 := by
  have hlt : i.val + 1 < k := by
    have hv := i.val_lt
    by_contra hn
    have he : i.val + 1 = k := by omega
    apply hi
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val, ZMod.natCast_self] using
      congrArg (fun j : ℕ => (j : ZMod k)) he
  have he : i + 1 = ((i.val + 1 : ℕ) : ZMod k) := by
    simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  exact (congrArg ZMod.val he).trans (ZMod.val_natCast_of_lt hlt)

theorem cyclicRangeIndex_next (s : ZMod n) {i : ZMod k} (hi : i ≠ -1) :
    cyclicRangeIndex s (i + 1) = cyclicRangeIndex s i + 1 := by
  simp only [cyclicRangeIndex, zmod_val_next_of_ne_last hi, Nat.cast_add, Nat.cast_one]
  ring

theorem cyclicRangeIndex_last (s : ZMod n) :
    cyclicRangeIndex (k := k) s (-1) = s + (k : ZMod n) - 1 := by
  have he := congrArg (fun j : ℕ => (j : ZMod n)) (last_index_val_succ (n := k))
  simp only [Nat.cast_add, Nat.cast_one] at he
  dsimp [cyclicRangeIndex]
  linear_combination he

theorem cyclicRangeIndex_offset (hk : k ≤ n) (s : ZMod n) (i : ZMod k) :
    (cyclicRangeIndex s i - s).val = i.val := by
  simp only [cyclicRangeIndex, add_sub_cancel_left]
  exact ZMod.val_natCast_of_lt (lt_of_lt_of_le i.val_lt hk)

end SM
