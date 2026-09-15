namespace SM

noncomputable section

theorem flat_epsilons_nonincident (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    wallLeftEpsilon 0 r 1 = 1 ∧ wallRightEpsilon 0 r 1 = 1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (r - 0) / (1 - 0)
    simpa using hr0
  · apply sign_eq_one_iff.mpr
    change 0 < (1 - r) / (1 - 0)
    simpa using sub_pos.mpr hr1

theorem flat_epsilons_incoming (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    wallLeftEpsilon r 1 0 = -1 ∧ wallRightEpsilon r 1 0 = 1 := by
  constructor
  · apply sign_eq_neg_one_iff.mpr
    change (1 - r) / (0 - r) < 0
    exact div_neg_of_pos_of_neg (by linarith) (by linarith)
  · apply sign_eq_one_iff.mpr
    change 0 < (0 - 1) / (0 - r)
    exact div_pos_of_neg_of_neg (by norm_num) (by linarith)

theorem flat_epsilons_outgoing (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    wallLeftEpsilon 1 0 r = 1 ∧ wallRightEpsilon 1 0 r = -1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (0 - 1) / (r - 1)
    exact div_pos_of_neg_of_neg (by norm_num) (by linarith)
  · apply sign_eq_neg_one_iff.mpr
    change (r - 0) / (r - 1) < 0
    exact div_neg_of_pos_of_neg (by linarith) (by linarith)

/-- The printed strict betweenness supplies concrete affine coordinates.
The two other root orders use the same three equations in cyclic order. -/
theorem strictBetween_flat_affine (a x b : Plane) (h : StrictBetween a x b) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ b - a ≠ 0 ∧
      a = a + (0 : ℝ) • (b - a) ∧ x = a + r • (b - a) ∧
      b = a + (1 : ℝ) • (b - a) := by
  obtain ⟨hab, r, hr0, hr1, hx⟩ := h
  refine ⟨r, hr0, hr1, sub_ne_zero.mpr hab.symm, ?_, hx, ?_⟩
  · simp
  · simp

variable {n : ℕ} [NeZero n]

/-- These are exactly the three cyclic orders of the critical labels in the
root word. This predicate introduces no geometric or wall assumption. -/
def CyclicTurnBoundaryOrder (g j : ZMod n) (t : IncreasingBoundaryTriple n) : Prop :=
    (boundaryIndex g t.lower = j - 1 ∧ boundaryIndex g t.middle = j ∧
      boundaryIndex g t.upper = j + 1) ∨
    (boundaryIndex g t.lower = j ∧ boundaryIndex g t.middle = j + 1 ∧
      boundaryIndex g t.upper = j - 1) ∨
    (boundaryIndex g t.lower = j + 1 ∧ boundaryIndex g t.middle = j - 1 ∧
      boundaryIndex g t.upper = j)

/-- Reversing each of the three even cyclic orders negates the same turn. -/
theorem turn_far_cyclic_signs (P : LabelledTuple n) (j : ZMod n) :
    chi P (j + 1) j (j - 1) = -turn P j ∧
      chi P (j - 1) (j + 1) j = -turn P j ∧
      chi P j (j - 1) (j + 1) = -turn P j := by
  exact ⟨chi_swap_outer P (j - 1) j (j + 1),
    chi_swap_last P (j - 1) j (j + 1), chi_swap_first P (j - 1) j (j + 1)⟩

theorem flat_boundary_chi_eq_neg_turn (P : LabelledTuple n) (g j : ZMod n)
    (t : IncreasingBoundaryTriple n) (h : CyclicTurnBoundaryOrder g j t) :
    chi P (boundaryIndex g t.upper) (boundaryIndex g t.middle) (boundaryIndex g t.lower) =
      -turn P j := by
  have hc := turn_far_cyclic_signs P j
  rcases h with h | h | h
  · simpa only [h.1, h.2.1, h.2.2] using hc.1
  · simpa only [h.1, h.2.1, h.2.2] using hc.2.1
  · simpa only [h.1, h.2.1, h.2.2] using hc.2.2

theorem flat_boundary_geometric_sign (P : LabelledTuple n) (g j : ZMod n)
    (t : IncreasingBoundaryTriple n) (h : CyclicTurnBoundaryOrder g j t) :
    geometricBoundaryArray (R := ℤ) P g t = -(turn P j : ℤ) := by
  simp only [geometricBoundaryArray, flat_boundary_chi_eq_neg_turn P g j t h,
    Int.cast_id, SignType.coe_neg]

/-- The existing turn sign-change hypothesis gives precisely the reverse
boundary chi premise required by the integer single-triple response. -/
theorem WallGerm.flat_boundary_chi_signChanges (w : WallGerm n) (g j : ZMod n)
    (t : IncreasingBoundaryTriple n) (h : CyclicTurnBoundaryOrder g j t)
    (hturn : w.SignChanges (fun P => (turn P j : ℝ))) :
    w.SignChanges (fun P => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ)) := by
  have he : (fun P : LabelledTuple n => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ)) =
      (fun P => -(turn P j : ℝ)) := by
    funext P
    rw [flat_boundary_chi_eq_neg_turn P g j t h, SignType.coe_neg]
  rw [he, w.signChanges_neg]
  exact hturn

end
end SM
