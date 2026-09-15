namespace SM

noncomputable section
variable {m : ℕ}

/-- The incoming nonleaf gap samples every retained vertex in order,
including the wrap at child index zero. -/
theorem incoming_flat_gap_labels (j : ZMod (m + 4)) (i : ZMod (m + 3)) :
    restrictedVertexIndex (j - 1) (incomingFlatTriple (n := m + 4) (by omega)).rightInterval i =
      deletionIndex j (i - 1) := by
  change (j - 1) + ((1 + (i - 1).val : ℕ) : ZMod (m + 4)) + 1 =
    ((i - 1).val : ZMod (m + 4)) + (j + 1)
  rw [Nat.cast_add, Nat.cast_one]
  ring

/-- The outgoing nonleaf gap has the same complete retained label word. -/
theorem outgoing_flat_gap_labels (j : ZMod (m + 4)) (i : ZMod (m + 3)) :
    restrictedVertexIndex j (outgoingFlatTriple (n := m + 4) (by omega)).leftInterval i =
      deletionIndex j (i - 1) := by
  change j + ((0 + (i - 1).val : ℕ) : ZMod (m + 4)) + 1 =
    ((i - 1).val : ZMod (m + 4)) + (j + 1)
  rw [Nat.zero_add]
  ring

/-- Equality is pointwise on the entire closed tuple. The shift makes local
root zero the deleted polygon's closing root minus one. -/
theorem incoming_flat_gap_tuple (P : LabelledTuple (m + 4)) (j : ZMod (m + 4)) :
    restrictedWordTuple P (j - 1) (incomingFlatTriple (n := m + 4) (by omega)).rightInterval =
      shift (-1 : ZMod (m + 3)) (deleteVertex P j) := by
  funext i
  change P (restrictedVertexIndex (j - 1)
    (incomingFlatTriple (n := m + 4) (by omega)).rightInterval i) =
    P (deletionIndex j ((show ZMod (m + 3) from i) + (-1 : ZMod (m + 3))))
  erw [incoming_flat_gap_labels, sub_eq_add_neg]

theorem outgoing_flat_gap_tuple (P : LabelledTuple (m + 4)) (j : ZMod (m + 4)) :
    restrictedWordTuple P j (outgoingFlatTriple (n := m + 4) (by omega)).leftInterval =
      shift (-1 : ZMod (m + 3)) (deleteVertex P j) := by
  funext i
  change P (restrictedVertexIndex j
    (outgoingFlatTriple (n := m + 4) (by omega)).leftInterval i) =
    P (deletionIndex j ((show ZMod (m + 3) from i) + (-1 : ZMod (m + 3))))
  erw [outgoing_flat_gap_labels, sub_eq_add_neg]

/-- Transport an actual tree coefficient across tuple equality, including
its dependent G1 witness. Proof irrelevance identifies proofs after substitution. -/
theorem treeCoefficient_congr_tuple {k : ℕ} [NeZero k]
    (P Q : LabelledTuple k) (hP : G1 P) (hQ : G1 Q) (he : P = Q)
    (g : ZMod k) (hk : 3 ≤ k) : treeCoefficient P hP g hk = treeCoefficient Q hQ g hk := by
  subst Q
  rfl

/-- The incoming source B value is exactly the deletion coefficient at the
physical fused root. G1 follows from the sole turn support, not parent G1. -/
theorem incoming_flat_integer_gap (P : LabelledTuple (m + 4)) (j : ZMod (m + 4))
    (hz : pointZeroTriples P = {turnSupport j}) :
    criticalIntervalIntegerOutput P (j - 1) (incomingFlatTriple (n := m + 4) (by omega))
      (by simpa only [incomingFlatTriple_support] using hz)
      (incomingFlatTriple (n := m + 4) (by omega)).rightInterval
      (incomingFlatTriple (n := m + 4) (by omega)).rightInterval_excludes_span =
      treeCoefficient (deleteVertex P j) (g1_deleteVertex hz)
        (fusionIndex j (j - 1)) (by omega) := by
  have hleaf : (incomingFlatTriple (n := m + 4) (by omega)).rightInterval.leaves ≠ 1 := by
    change m + 2 ≠ 1
    omega
  rw [criticalIntervalIntegerOutput, dif_neg hleaf, fusionIndex_prev]
  change treeCoefficient (n := m + 3)
      (restrictedWordTuple P (j - 1) (incomingFlatTriple (n := m + 4) (by omega)).rightInterval) _ 0 _ =
    treeCoefficient (n := m + 3) (deleteVertex P j) (g1_deleteVertex hz) (-1) _
  calc
    _ = treeCoefficient (shift (-1) (deleteVertex P j))
        (g1_shift_forward (-1) (g1_deleteVertex hz)) 0 (by omega) :=
      treeCoefficient_congr_tuple (k := m + 3) _ _ _ _ (incoming_flat_gap_tuple P j) 0 (by omega)
    _ = _ := by
      simpa only [sub_self] using
        treeCoefficient_shift (deleteVertex P j) (g1_deleteVertex hz) (-1) (-1) (by omega)

/-- The outgoing source B value uses the same fused physical edge. -/
theorem outgoing_flat_integer_gap (P : LabelledTuple (m + 4)) (j : ZMod (m + 4))
    (hz : pointZeroTriples P = {turnSupport j}) :
    criticalIntervalIntegerOutput P j (outgoingFlatTriple (n := m + 4) (by omega))
      (by simpa only [outgoingFlatTriple_support] using hz)
      (outgoingFlatTriple (n := m + 4) (by omega)).leftInterval
      (outgoingFlatTriple (n := m + 4) (by omega)).leftInterval_excludes_span =
      treeCoefficient (deleteVertex P j) (g1_deleteVertex hz)
        (fusionIndex j j) (by omega) := by
  have hleaf : (outgoingFlatTriple (n := m + 4) (by omega)).leftInterval.leaves ≠ 1 := by
    change m + 2 ≠ 1
    omega
  rw [criticalIntervalIntegerOutput, dif_neg hleaf, fusionIndex_deleted]
  change treeCoefficient (n := m + 3)
      (restrictedWordTuple P j (outgoingFlatTriple (n := m + 4) (by omega)).leftInterval) _ 0 _ =
    treeCoefficient (n := m + 3) (deleteVertex P j) (g1_deleteVertex hz) (-1) _
  calc
    _ = treeCoefficient (shift (-1) (deleteVertex P j))
        (g1_shift_forward (-1) (g1_deleteVertex hz)) 0 (by omega) :=
      treeCoefficient_congr_tuple (k := m + 3) _ _ _ _ (outgoing_flat_gap_tuple P j) 0 (by omega)
    _ = _ := by
      simpa only [sub_self] using
        treeCoefficient_shift (deleteVertex P j) (g1_deleteVertex hz) (-1) (-1) (by omega)

end
end SM
