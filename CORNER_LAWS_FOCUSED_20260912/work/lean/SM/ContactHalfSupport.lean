import SM.ContactHalfIndices

/-! Exact inherited vertex ranges and the missing contact endpoint on each
half. These exclude the parent's only collinear triple in the child G1 proof. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem cyclicRangeIndex_range {k : ℕ} [NeZero k] (hk : k ≤ n) (s x : ZMod n) :
    (∃ i : ZMod k, cyclicRangeIndex s i = x) ↔ (x - s).val < k := by
  constructor
  · rintro ⟨i, rfl⟩
    rw [cyclicRangeIndex_offset hk]
    exact i.val_lt
  · intro hx
    refine ⟨((x - s).val : ZMod k), ?_⟩
    simp only [cyclicRangeIndex, ZMod.val_natCast_of_lt hx, ZMod.natCast_zmod_val]
    ring

theorem firstHalfIndex_range (M a x : ZMod n) :
    (∃ i, firstHalfIndex M a i = x) ↔ (x - M).val < firstHalfSize M a :=
  cyclicRangeIndex_range (firstHalfSize_le M a) M x

theorem secondHalfIndex_range_iff (M a x : ZMod n) :
    (∃ i, secondHalfIndex M a i = x) ↔ (x - (a + 1)).val < secondHalfSize M a := by
  rw [← cyclicRangeIndex_range (secondHalfSize_le M a) (a + 1) x]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i - 1, (secondHalfIndex_range M a i).symm.trans hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨i + 1, ?_⟩
    rw [secondHalfIndex_range, add_sub_cancel_right]
    exact hi

theorem firstHalfIndex_ne_base_successor (hn : 3 ≤ n) {M a : ZMod n}
    (h : ContactSeparated M a) (i : ZMod (firstHalfSize M a)) : firstHalfIndex M a i ≠ a + 1 := by
  intro he
  have hr := (firstHalfIndex_range M a (a + 1)).mp ⟨i, he⟩
  have hb := contactHalfSizes_bounds hn h
  have hsize : firstHalfSize M a < n := by omega
  have hcast : (a + 1 - M) = (firstHalfSize M a : ZMod n) := by
    rw [firstHalfSize, Nat.cast_add, Nat.cast_one, contactDistance_cast]
    ring
  rw [hcast, ZMod.val_natCast_of_lt hsize] at hr
  exact lt_irrefl _ hr

theorem secondHalfIndex_ne_base (hn : 3 ≤ n) {M a : ZMod n}
    (h : ContactSeparated M a) (i : ZMod (secondHalfSize M a)) : secondHalfIndex M a i ≠ a := by
  intro he
  have hr := (secondHalfIndex_range_iff M a a).mp ⟨i, he⟩
  have hb := contactHalfSizes_bounds hn h
  have hv := last_index_val_succ (n := n)
  have he' : a - (a + 1) = (-1 : ZMod n) := by ring
  rw [he'] at hr
  omega

end SM
