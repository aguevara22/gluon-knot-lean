namespace SM

noncomputable section

/-- At the contacted base edge the critical cut order is B,X,A. -/
theorem contact_epsilons_base (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    wallLeftEpsilon 1 r 0 = 1 ∧ wallRightEpsilon 1 r 0 = 1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (r - 1) / (0 - 1)
    exact div_pos_of_neg_of_neg (by linarith) (by norm_num)
  · apply sign_eq_one_iff.mpr
    change 0 < (0 - r) / (0 - 1)
    exact div_pos_of_neg_of_neg (by linarith) (by norm_num)

/-- On the original X-to-A arc the critical cut order is A,B,X. -/
theorem contact_epsilons_first_arc (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    wallLeftEpsilon 0 1 r = 1 ∧ wallRightEpsilon 0 1 r = -1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (1 - 0) / (r - 0)
    exact div_pos (by norm_num) (by linarith)
  · apply sign_eq_neg_one_iff.mpr
    change (r - 1) / (r - 0) < 0
    exact div_neg_of_neg_of_pos (by linarith) (by linarith)

/-- On the original B-to-X arc the critical cut order is X,A,B. -/
theorem contact_epsilons_second_arc (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    wallLeftEpsilon r 0 1 = -1 ∧ wallRightEpsilon r 0 1 = 1 := by
  constructor
  · apply sign_eq_neg_one_iff.mpr
    change (0 - r) / (1 - r) < 0
    exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  · apply sign_eq_one_iff.mpr
    change 0 < (1 - 0) / (1 - r)
    exact div_pos (by norm_num) (by linarith)

variable {n : ℕ} [NeZero n]

/-- The actual contact interior supplies the scalar. Central regularity,
proved from the named contact support, supplies the nonzero direction B-A.
No G1 or flat-wall premise on the center is assumed. -/
theorem WallGerm.contact_interior_affine (w : WallGerm n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.VertexEdgeAt M a) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      w.center (a + 1) - w.center a ≠ 0 ∧
      w.center a = w.center a + (0 : ℝ) • (w.center (a + 1) - w.center a) ∧
      w.center (a + 1) = w.center a + (1 : ℝ) • (w.center (a + 1) - w.center a) ∧
      w.center M = w.center a + r • (w.center (a + 1) - w.center a) := by
  have hreg := w.vertexEdge_regular hn hc
  have hω : edge w.center a ≠ 0 := (hreg a).2.1
  obtain ⟨r, hr0, hr1, hX⟩ := hc.2.2.2.1
  refine ⟨r, hr0, hr1, ?_, ?_, ?_, ?_⟩
  · simpa only [edge] using hω
  · simp
  · simp
  · simpa only [edgePoint, edge] using hX

/-- Exactly the three cyclic orders of A,B,X in an actual root word.
This predicate contains only label equalities, with no geometric premise. -/
def CyclicContactBoundaryOrder (g M a : ZMod n) (t : IncreasingBoundaryTriple n) : Prop :=
    (boundaryIndex g t.lower = a ∧ boundaryIndex g t.middle = a + 1 ∧
      boundaryIndex g t.upper = M) ∨
    (boundaryIndex g t.lower = a + 1 ∧ boundaryIndex g t.middle = M ∧
      boundaryIndex g t.upper = a) ∨
    (boundaryIndex g t.lower = M ∧ boundaryIndex g t.middle = a ∧
      boundaryIndex g t.upper = a + 1)

/-- Reversing any of the three even cyclic orders negates the same contact
chirotope. The equality holds for every tuple, including the wall center. -/
theorem contact_boundary_chi_eq_neg (P : LabelledTuple n) (g M a : ZMod n)
    (t : IncreasingBoundaryTriple n) (h : CyclicContactBoundaryOrder g M a t) :
    chi P (boundaryIndex g t.upper) (boundaryIndex g t.middle) (boundaryIndex g t.lower) =
      -chi P a (a + 1) M := by
  rcases h with h | h | h
  · simpa only [h.1, h.2.1, h.2.2] using chi_swap_outer P a (a + 1) M
  · simpa only [h.1, h.2.1, h.2.2] using chi_swap_last P a (a + 1) M
  · simpa only [h.1, h.2.1, h.2.2] using chi_swap_first P a (a + 1) M

theorem contact_boundary_geometric_sign (P : LabelledTuple n) (g M a : ZMod n)
    (t : IncreasingBoundaryTriple n) (h : CyclicContactBoundaryOrder g M a t) :
    geometricBoundaryArray (R := ℤ) P g t = -(chi P a (a + 1) M : ℤ) := by
  simp only [geometricBoundaryArray, contact_boundary_chi_eq_neg P g M a t h,
    Int.cast_id, SignType.coe_neg]

/-- The source contact observable's sign change gives exactly the reversed
boundary-chirotope premise of the single-triple response theorem. -/
theorem WallGerm.contact_boundary_chi_signChanges (w : WallGerm n) (g M a : ZMod n)
    (t : IncreasingBoundaryTriple n) (h : CyclicContactBoundaryOrder g M a t)
    (hcontact : w.SignChanges (fun P => (chi P a (a + 1) M : ℝ))) :
    w.SignChanges (fun P => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ)) := by
  have he : (fun P : LabelledTuple n => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ)) =
      (fun P => -(chi P a (a + 1) M : ℝ)) := by
    funext P
    rw [contact_boundary_chi_eq_neg P g M a t h, SignType.coe_neg]
  rw [he, w.signChanges_neg]
  exact hcontact

end
end SM
