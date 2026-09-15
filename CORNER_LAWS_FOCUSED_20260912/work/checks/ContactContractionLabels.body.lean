namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Every vertex surviving the first-arc contraction has its exact first-half
label. The natural cut calculation includes local label zero and root M. -/
theorem contactFirstArc_contracted_labels (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a)
    (i : ZMod (contactFirstArcTriple g M a hn hc hu).contractedSize) :
    contractedVertexIndex g (contactFirstArcTriple g M a hn hc hu) i =
      firstHalfIndex M a
        (ZMod.ringEquivCongr (contactFirstArcTriple_contractedSize g M a hn hc hu) i +
          ((g - M).val : ZMod (firstHalfSize M a))) := by
  let t := contactFirstArcTriple g M a hn hc hu
  let e := ZMod.ringEquivCongr (contactFirstArcTriple_contractedSize g M a hn hc hu)
  have hd := contactDistance_bounds hn hc
  have huN : (g - M).val < n := ZMod.val_lt _
  have hv : (i - 1).val = (e i - 1).val := by
    have hh := ZMod.ringEquivCongr_val (contactFirstArcTriple_contractedSize g M a hn hc hu) (i - 1)
    simpa only [map_sub, map_one] using hh.symm
  have hrel : ((g - M).val : ZMod (firstHalfSize M a)) +
      ((contactDistance M a - (g - M).val + 1 : ℕ) : ZMod (firstHalfSize M a)) = 0 := by
    rw [← Nat.cast_add]
    have he : (g - M).val + (contactDistance M a - (g - M).val + 1) = firstHalfSize M a := by
      unfold firstHalfSize
      omega
    rw [he, ZMod.natCast_self]
  have hcut := zmod_cut_shift_val (contactDistance M a - (g - M).val)
    (by unfold firstHalfSize; omega : contactDistance M a - (g - M).val < firstHalfSize M a)
    (e i) ((g - M).val : ZMod (firstHalfSize M a)) hrel
  have hlower : t.lower.val = contactDistance M a - (g - M).val - 1 := rfl
  have herase : t.erasedInteriorCount = n - contactDistance M a - 1 := by
    dsimp [t, IncreasingBoundaryTriple.erasedInteriorCount, contactFirstArcTriple]
    omega
  have huZ : ((g - M).val : ZMod n) = g - M := ZMod.natCast_zmod_val _
  change g + ((t.expandPosition ⟨(i - 1).val, ZMod.val_lt _⟩).val : ZMod n) + 1 =
    M + ((e i + ((g - M).val : ZMod (firstHalfSize M a))).val : ZMod n)
  rw [IncreasingBoundaryTriple.expandPosition_val]
  change g + ((if (i - 1).val ≤ t.lower.val then (i - 1).val
      else (i - 1).val + t.erasedInteriorCount : ℕ) : ZMod n) + 1 =
    M + ((e i + ((g - M).val : ZMod (firstHalfSize M a))).val : ZMod n)
  rw [hlower, herase, hv, hcut]
  by_cases hk : (e i - 1).val < contactDistance M a - (g - M).val
  · rw [if_pos hk, if_pos (by omega : (e i - 1).val ≤ contactDistance M a - (g - M).val - 1)]
    have he : (e i - 1).val + firstHalfSize M a - (contactDistance M a - (g - M).val) =
        (e i - 1).val + (g - M).val + 1 := by
      unfold firstHalfSize
      omega
    rw [he, Nat.cast_add, Nat.cast_add, Nat.cast_one, huZ]
    ring
  · rw [if_neg hk, if_neg (by omega : ¬ (e i - 1).val ≤ contactDistance M a - (g - M).val - 1)]
    rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ n - contactDistance M a),
      Nat.cast_sub (by omega : contactDistance M a ≤ n), Nat.cast_one, ZMod.natCast_self,
      Nat.cast_sub (by omega : contactDistance M a - (g - M).val ≤ (e i - 1).val),
      Nat.cast_sub (by omega : (g - M).val ≤ contactDistance M a), huZ]
    ring

/-- Every surviving vertex of the second-arc contraction agrees with the
second half at its inherited root; the canonical range formula handles zero. -/
theorem contactSecondArc_contracted_labels (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val)
    (i : ZMod (contactSecondArcTriple g M a hn hc hu).contractedSize) :
    contractedVertexIndex g (contactSecondArcTriple g M a hn hc hu) i =
      secondHalfIndex M a
        (ZMod.ringEquivCongr (contactSecondArcTriple_contractedSize g M a hn hc hu) i +
          ((g - a).val : ZMod (secondHalfSize M a))) := by
  let t := contactSecondArcTriple g M a hn hc hu
  let e := ZMod.ringEquivCongr (contactSecondArcTriple_contractedSize g M a hn hc hu)
  have hd := contactDistance_bounds hn hc
  have huN : (g - M).val < n := ZMod.val_lt _
  have hvroot : (g - a).val = (g - M).val - contactDistance M a := by
    rw [contact_relative_offset_val M a g, if_neg (by omega)]
  have hv : (i - 1).val = (e i - 1).val := by
    have hh := ZMod.ringEquivCongr_val (contactSecondArcTriple_contractedSize g M a hn hc hu) (i - 1)
    simpa only [map_sub, map_one] using hh.symm
  have hrel : (((g - a).val : ZMod (secondHalfSize M a)) - 1) +
      ((n - (g - M).val + 1 : ℕ) : ZMod (secondHalfSize M a)) = 0 := by
    have he : (g - a).val + (n - (g - M).val) = secondHalfSize M a := by
      unfold secondHalfSize
      omega
    calc
      _ = (((g - a).val + (n - (g - M).val) : ℕ) : ZMod (secondHalfSize M a)) := by
        push_cast
        ring
      _ = 0 := by rw [he, ZMod.natCast_self]
  have hcut := zmod_cut_shift_val (n - (g - M).val)
    (by unfold secondHalfSize; omega : n - (g - M).val < secondHalfSize M a)
    (e i) (((g - a).val : ZMod (secondHalfSize M a)) - 1) hrel
  have hlower : t.lower.val = n - (g - M).val - 1 := rfl
  have herase : t.erasedInteriorCount = contactDistance M a := by
    dsimp [t, IncreasingBoundaryTriple.erasedInteriorCount, contactSecondArcTriple]
    omega
  have huZ : ((g - M).val : ZMod n) = g - M := ZMod.natCast_zmod_val _
  have hvZ : ((g - a).val : ZMod n) = g - a := ZMod.natCast_zmod_val _
  rw [secondHalfIndex_range]
  change g + ((t.expandPosition ⟨(i - 1).val, ZMod.val_lt _⟩).val : ZMod n) + 1 =
    a + 1 + ((e i + ((g - a).val : ZMod (secondHalfSize M a)) - 1).val : ZMod n)
  have hearg : e i + ((g - a).val : ZMod (secondHalfSize M a)) - 1 =
      e i + (((g - a).val : ZMod (secondHalfSize M a)) - 1) := by ring
  rw [IncreasingBoundaryTriple.expandPosition_val]
  change g + ((if (i - 1).val ≤ t.lower.val then (i - 1).val
      else (i - 1).val + t.erasedInteriorCount : ℕ) : ZMod n) + 1 =
    a + 1 + ((e i + ((g - a).val : ZMod (secondHalfSize M a)) - 1).val : ZMod n)
  rw [hlower, herase, hv, hearg, hcut]
  by_cases hk : (e i - 1).val < n - (g - M).val
  · rw [if_pos hk, if_pos (by omega : (e i - 1).val ≤ n - (g - M).val - 1)]
    have he : (e i - 1).val + secondHalfSize M a - (n - (g - M).val) =
        (e i - 1).val + (g - a).val := by
      unfold secondHalfSize
      omega
    rw [he, Nat.cast_add, hvZ]
    ring
  · rw [if_neg hk, if_neg (by omega : ¬ (e i - 1).val ≤ n - (g - M).val - 1)]
    rw [Nat.cast_add, Nat.cast_sub (by omega : n - (g - M).val ≤ (e i - 1).val),
      Nat.cast_sub (by omega : (g - M).val ≤ n), ZMod.natCast_self, huZ, contactDistance_cast]
    ring

/-- Full first-half tuple identity after the proved arity transport. -/
theorem contactFirstArc_contracted_tuple (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    (fun u : ZMod (firstHalfSize M a) => contractedWordTuple P g
      (contactFirstArcTriple g M a hn hc hu)
      ((ZMod.ringEquivCongr (contactFirstArcTriple_contractedSize g M a hn hc hu)).symm u)) =
      shift ((g - M).val : ZMod (firstHalfSize M a)) (firstHalf P M a) := by
  funext u
  unfold contractedWordTuple shift firstHalf
  rw [contactFirstArc_contracted_labels g M a hn hc hu]
  simp only [RingEquiv.apply_symm_apply]

/-- Full second-half tuple identity, at every label of the inherited root cut. -/
theorem contactSecondArc_contracted_tuple (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    (fun u : ZMod (secondHalfSize M a) => contractedWordTuple P g
      (contactSecondArcTriple g M a hn hc hu)
      ((ZMod.ringEquivCongr (contactSecondArcTriple_contractedSize g M a hn hc hu)).symm u)) =
      shift ((g - a).val : ZMod (secondHalfSize M a)) (secondHalf P M a) := by
  funext u
  unfold contractedWordTuple shift secondHalf
  rw [contactSecondArc_contracted_labels g M a hn hc hu]
  simp only [RingEquiv.apply_symm_apply]

end
end SM
