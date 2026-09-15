namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem canonicalPosition_val_zero : (canonicalPosition (0 : ZMod n)).val = n - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  simp [canonicalPosition]

theorem canonicalPosition_val_nonzero (k : ZMod n) (hk : k ≠ 0) :
    (canonicalPosition k).val = k.val - 1 := by
  have hp := ZMod.val_pos.mpr hk
  have hn := ZMod.val_lt k
  haveI : Fact (1 < n) := ⟨by omega⟩
  change (k - 1).val = k.val - 1
  rw [ZMod.val_sub (by rw [ZMod.val_one]; omega), ZMod.val_one]

/-- Exact numerical label formula for the corresponding parent edge. The
return edge, rather than the soft edge, inherits the parent label's place
in the traversal order, including parent label zero. -/
theorem softParentEdge_natCast (j k : ZMod n) :
    softParentEdge j k = if j = 0 ∨ k.val < j.val then (k.val : ZMod (n + 1))
      else ((k.val + 1 : ℕ) : ZMod (n + 1)) := by
  have hn := NeZero.pos n
  have hkn := ZMod.val_lt k
  have hjn := ZMod.val_lt j
  by_cases hj : j = 0
  · subst j
    simp only [true_or, ite_true]
    by_cases hk : k = 0
    · subst k
      rw [softParentEdge_at_attachment, softNewIndex_physical, canonicalPosition_val_zero]
      have he : n - 1 + 2 = n + 1 := by omega
      rw [he, ZMod.natCast_self, ZMod.val_zero, Nat.cast_zero]
    · rw [softParentEdge_of_ne 0 k hk]
      have hp := ZMod.val_pos.mpr hk
      have he := softOldIndex_physical (0 : ZMod n) (canonicalPosition k)
      rw [boundaryIndex_canonicalPosition, canonicalPosition_val_nonzero k hk,
        canonicalPosition_val_zero] at he
      have hle : k.val - 1 ≤ n - 1 := by omega
      rw [if_pos hle] at he
      have hv : k.val - 1 + 1 = k.val := by omega
      simpa only [hv] using he
  · have hjp := ZMod.val_pos.mpr hj
    by_cases hkj : k = j
    · subst k
      simp only [hj, false_or, lt_self_iff_false, ite_false]
      rw [softParentEdge_at_attachment, softNewIndex_physical, canonicalPosition_val_nonzero j hj]
      have hv : j.val - 1 + 2 = j.val + 1 := by omega
      rw [hv]
    · rw [softParentEdge_of_ne j k hkj]
      have he := softOldIndex_physical j (canonicalPosition k)
      rw [boundaryIndex_canonicalPosition, canonicalPosition_val_nonzero j hj] at he
      by_cases hk : k = 0
      · subst k
        rw [canonicalPosition_val_zero] at he
        have hgt : ¬ n - 1 ≤ j.val - 1 := by omega
        rw [if_neg hgt] at he
        have hv : n - 1 + 2 = n + 1 := by omega
        simp only [hv, ZMod.natCast_self] at he
        simp only [hj, false_or, ZMod.val_zero, hjp, ite_true, Nat.cast_zero]
        exact he
      · have hkp := ZMod.val_pos.mpr hk
        have hne : k.val ≠ j.val := fun h => hkj (ZMod.val_injective n h)
        rw [canonicalPosition_val_nonzero k hk] at he
        by_cases hlt : k.val < j.val
        · have hle : k.val - 1 ≤ j.val - 1 := by omega
          have hv : k.val - 1 + 1 = k.val := by omega
          simpa only [hj, false_or, hlt, ite_true, hle, hv] using he
        · have hgt : ¬ k.val - 1 ≤ j.val - 1 := by omega
          have hv : k.val - 1 + 2 = k.val + 1 := by omega
          simpa only [hj, false_or, hlt, ite_false, hgt, hv] using he

theorem softParentEdge_val (j k : ZMod n) :
    (softParentEdge j k).val = if j = 0 ∨ k.val < j.val then k.val else k.val + 1 := by
  rw [softParentEdge_natCast]
  split_ifs
  · exact ZMod.val_natCast_of_lt (by have := ZMod.val_lt k; omega)
  · exact ZMod.val_natCast_of_lt (by have := ZMod.val_lt k; omega)

/-- Unlike a general cyclic relabelling, this parent-edge correspondence
preserves the actual numerical traversal cut, even when inserting after
source label n. This supports equality of inherited sorted visit lists. -/
theorem softParentEdge_val_lt_iff (j k l : ZMod n) :
    (softParentEdge j k).val < (softParentEdge j l).val ↔ k.val < l.val := by
  rw [softParentEdge_val, softParentEdge_val]
  by_cases hj : j = 0
  · simp only [hj, true_or, ite_true]
  · simp only [hj, false_or]
    split_ifs <;> omega

theorem softParentEdge_val_le_iff (j k l : ZMod n) :
    (softParentEdge j k).val ≤ (softParentEdge j l).val ↔ k.val ≤ l.val := by
  simpa only [not_lt] using not_congr (softParentEdge_val_lt_iff j l k)

theorem softParentEdge_zero (j : ZMod n) : softParentEdge j 0 = 0 := by
  apply ZMod.val_injective
  rw [softParentEdge_val, ZMod.val_zero]
  by_cases hj : j = 0
  · simp only [hj, true_or, ite_true, ZMod.val_zero]
  · have hp := ZMod.val_pos.mpr hj
    simp only [hj, false_or, ZMod.val_zero, hp, ite_true]

end
end SM
