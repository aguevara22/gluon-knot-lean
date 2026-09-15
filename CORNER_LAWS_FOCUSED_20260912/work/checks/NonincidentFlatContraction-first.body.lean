namespace SM

noncomputable section
variable {q : ℕ} [NeZero q]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Every surviving physical vertex, including local label zero, agrees
with deletion followed by the proved physical-root cyclic shift. -/
theorem nonincident_flat_contracted_labels (g j : ZMod (q + 1)) (k : Fin (q + 1))
    (h0 : 0 < k.val) (hLast : k.val + 1 < q + 1)
    (hk : boundaryIndex g k = j) (hroot : ¬ incident j g)
    (i : ZMod (consecutiveBoundaryTriple k h0 hLast).contractedSize) :
    contractedVertexIndex g (consecutiveBoundaryTriple k h0 hLast) i =
      deletionIndex j (ZMod.ringEquivCongr (consecutive_contracted_size k h0 hLast) i +
        fusionIndex j g) := by
  let t := consecutiveBoundaryTriple k h0 hLast
  let e := ZMod.ringEquivCongr (consecutive_contracted_size k h0 hLast)
  have hv : (i - 1).val = (e i - 1).val := by
    have hh := ZMod.ringEquivCongr_val (consecutive_contracted_size k h0 hLast) (i - 1)
    simpa only [map_sub, map_one] using hh.symm
  have hcut := zmod_cut_shift_val k.val (by omega : k.val < q) (e i) (fusionIndex j g)
    (nonincident_fusionIndex_cut_relation g j k h0 hLast hk hroot)
  have he : g + (k.val : ZMod (q + 1)) + 1 = j := hk
  have hq : (q : ZMod (q + 1)) + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using ZMod.natCast_self (q + 1)
  change g + ((t.expandPosition ⟨(i - 1).val, ZMod.val_lt _⟩).val : ZMod (q + 1)) + 1 =
    ((e i + fusionIndex j g).val : ZMod (q + 1)) + (j + 1)
  rw [IncreasingBoundaryTriple.expandPosition_val]
  have hlower : t.lower.val = k.val - 1 := rfl
  have herase : t.erasedInteriorCount = 1 := consecutive_erased_one k h0 hLast
  rw [hlower, herase, hv, hcut]
  by_cases hc : (e i - 1).val < k.val
  · rw [if_pos hc, if_pos (by omega : (e i - 1).val ≤ k.val - 1)]
    rw [Nat.cast_sub (by omega : k.val ≤ (e i - 1).val + q), Nat.cast_add]
    linear_combination he - hq
  · rw [if_neg hc, if_neg (by omega : ¬ (e i - 1).val ≤ k.val - 1)]
    rw [Nat.cast_sub (by omega : k.val ≤ (e i - 1).val), Nat.cast_add, Nat.cast_one]
    linear_combination he

/-- Equality of whole tuples after the explicit arity transport; this is
stronger than merely identifying the root endpoints. -/
theorem nonincident_flat_contracted_tuple (P : LabelledTuple (q + 1))
    (g j : ZMod (q + 1)) (k : Fin (q + 1))
    (h0 : 0 < k.val) (hLast : k.val + 1 < q + 1)
    (hk : boundaryIndex g k = j) (hroot : ¬ incident j g) :
    (fun u : ZMod q => contractedWordTuple P g (consecutiveBoundaryTriple k h0 hLast)
      ((ZMod.ringEquivCongr (consecutive_contracted_size k h0 hLast)).symm u)) =
        shift (fusionIndex j g) (deleteVertex P j) := by
  funext u
  unfold contractedWordTuple shift deleteVertex
  rw [nonincident_flat_contracted_labels g j k h0 hLast hk hroot]
  simp only [RingEquiv.apply_symm_apply, add_comm]

/-- The same consecutive triple is exactly the source's critical turn support. -/
theorem nonincident_flat_contracted_support (g j : ZMod (q + 1)) (k : Fin (q + 1))
    (h0 : 0 < k.val) (hLast : k.val + 1 < q + 1) (hk : boundaryIndex g k = j) :
    (consecutiveBoundaryTriple k h0 hLast).vertexSet g = turnSupport j := by
  have hl := consecutiveBoundaryTriple_labels g j k h0 hLast hk
  simp only [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet,
    Finset.image_insert, Finset.image_singleton, hl.1, hl.2.1, hl.2.2, turnSupport]

/-- Size transport, the proved full tuple identity, and cyclic covariance
identify the actual contracted coefficient at the exact fused root. -/
theorem nonincident_flat_contracted_coefficient (P : LabelledTuple (q + 1))
    (g j : ZMod (q + 1)) (k : Fin (q + 1))
    (h0 : 0 < k.val) (hLast : k.val + 1 < q + 1)
    (hk : boundaryIndex g k = j) (hroot : ¬ incident j g)
    (hz : pointZeroTriples P = {turnSupport j}) (hq : 3 ≤ q) :
    treeCoefficient (contractedWordTuple P g (consecutiveBoundaryTriple k h0 hLast))
      (contractedWord_G1 P g (consecutiveBoundaryTriple k h0 hLast)
        (by rw [nonincident_flat_contracted_support g j k h0 hLast hk]; exact hz))
      0 (by rw [consecutive_contracted_size]; exact hq) =
      treeCoefficient (deleteVertex P j) (g1_deleteVertex hz) (fusionIndex j g) hq := by
  have he := treeCoefficient_of_reindexed_tuple_eq (consecutive_contracted_size k h0 hLast)
    (contractedWordTuple P g (consecutiveBoundaryTriple k h0 hLast))
    (shift (fusionIndex j g) (deleteVertex P j))
    (contractedWord_G1 P g (consecutiveBoundaryTriple k h0 hLast)
      (by rw [nonincident_flat_contracted_support g j k h0 hLast hk]; exact hz))
    (g1_shift_forward (fusionIndex j g) (g1_deleteVertex hz))
    (nonincident_flat_contracted_tuple P g j k h0 hLast hk hroot)
    (by rw [consecutive_contracted_size]; exact hq)
  have hs := treeCoefficient_shift (deleteVertex P j) (g1_deleteVertex hz)
    (fusionIndex j g) (fusionIndex j g) hq
  rw [sub_self] at hs
  exact he.trans hs

end
end SM
