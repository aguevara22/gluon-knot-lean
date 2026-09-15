import SM.NamedWallPredicates
import SM.UnorderedWallTriples
import SM.CriticalSourceResponse
import Mathlib.Data.Sign.Basic

namespace SM

noncomputable section

/-- The far sign on three actual points, in the source's reversed order. -/
def pointFarSign (a r c : Plane) : SignType :=
  SignType.sign (det (r - c) (a - c))

/-- A nonzero scalar has an involutive sign, so rescaling a determinant
can be inverted at the level of signs even when that determinant is0. -/
theorem sign_rescale_nonzero (s a : ℝ) (hs : s ≠ 0) :
    SignType.sign a = SignType.sign s * SignType.sign (s * a) := by
  have hh : SignType.sign s * SignType.sign s = 1 :=
    mul_inv_cancel₀ (sign_ne_zero.mpr hs)
  rw [sign_mul, ← mul_assoc, hh, one_mul]

def wallLeftEpsilon (x y z : ℝ) : SignType := SignType.sign ((y - x) / (z - x))

def wallRightEpsilon (x y z : ℝ) : SignType := SignType.sign ((z - y) / (z - x))

/-- The printed distinct scalar coordinates make both epsilon ratios nonzero. -/
theorem wall_epsilons_nonzero (x y z : ℝ) (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    wallLeftEpsilon x y z ≠ 0 ∧ wallRightEpsilon x y z ≠ 0 := by
  exact ⟨sign_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr hyx) (sub_ne_zero.mpr hzx)),
    sign_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr hzy) (sub_ne_zero.mpr hzx))⟩

theorem wall_epsilons_one_or_neg_one (x y z : ℝ)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    (wallLeftEpsilon x y z = 1 ∨ wallLeftEpsilon x y z = -1) ∧
      (wallRightEpsilon x y z = 1 ∨ wallRightEpsilon x y z = -1) := by
  have hn := wall_epsilons_nonzero x y z hyx hzy hzx
  constructor
  · rcases SignType.trichotomy (wallLeftEpsilon x y z) with h | h | h
    · exact Or.inr h
    · exact (hn.1 h).elim
    · exact Or.inl h
  · rcases SignType.trichotomy (wallRightEpsilon x y z) with h | h | h
    · exact Or.inr h
    · exact (hn.2 h).elim
    · exact Or.inl h

/-- The two actual ratios sum to1, so at least one epsilon is positive.
This does not assume where the middle labelled point lies on the line. -/
theorem wall_epsilon_positive (x y z : ℝ) (hzx : z ≠ x) :
    wallLeftEpsilon x y z = 1 ∨ wallRightEpsilon x y z = 1 := by
  have he : (y - x) / (z - x) + (z - y) / (z - x) = 1 := by
    rw [← add_div]
    have ha : y - x + (z - y) = z - x := by ring
    rw [ha, div_self (sub_ne_zero.mpr hzx)]
  by_cases hl : 0 < (y - x) / (z - x)
  · exact Or.inl (sign_eq_one_iff.mpr hl)
  · have hr : 0 < (z - y) / (z - x) := by linarith [le_of_not_gt hl]
    exact Or.inr (sign_eq_one_iff.mpr hr)

theorem affine_line_difference (p ω : Plane) (x y : ℝ) :
    (p + y • ω) - (p + x • ω) = (y - x) • ω := by
  ext <;> dsimp <;> ring

/-- The left-gap far-sign identity uses the actual common first endpoint. -/
theorem collinear_left_gate_sign (a b c r : Plane) (s : ℝ) (hs : s ≠ 0)
    (h : b - a = s • (c - a)) :
    pointFarSign a r c = SignType.sign s * pointFarSign a r b := by
  unfold pointFarSign
  rw [area_cyclic a c r, area_cyclic a b r, h]
  have hd : det (s • (c - a)) (r - a) = s * det (c - a) (r - a) := by
    dsimp [det]
    ring
  rw [hd]
  exact sign_rescale_nonzero s _ hs

/-- The right-gap far-sign identity uses the actual common last endpoint. -/
theorem collinear_right_gate_sign (a b c r : Plane) (s : ℝ) (hs : s ≠ 0)
    (h : b - c = s • (a - c)) :
    pointFarSign a r c = SignType.sign s * pointFarSign b r c := by
  unfold pointFarSign
  rw [h]
  have hd : det (r - c) (s • (a - c)) = s * det (r - c) (a - c) := by
    dsimp [det]
    ring
  rw [hd]
  exact sign_rescale_nonzero s _ hs

/-- Substitute the source's affine coordinates and its actual left ratio. -/
theorem affine_collinear_left_gate (p ω r : Plane) (x y z : ℝ)
    (hyx : y ≠ x) (hzx : z ≠ x) :
    pointFarSign (p + x • ω) r (p + z • ω) =
      wallLeftEpsilon x y z * pointFarSign (p + x • ω) r (p + y • ω) := by
  apply collinear_left_gate_sign _ _ _ _ ((y - x) / (z - x))
    (div_ne_zero (sub_ne_zero.mpr hyx) (sub_ne_zero.mpr hzx))
  rw [affine_line_difference, affine_line_difference, smul_smul,
    div_mul_cancel₀ _ (sub_ne_zero.mpr hzx)]

/-- The right ratio has the printed orientation; both differences reverse
together when expressed using vectors based at the last endpoint. -/
theorem affine_collinear_right_gate (p ω r : Plane) (x y z : ℝ)
    (hzy : z ≠ y) (hzx : z ≠ x) :
    pointFarSign (p + x • ω) r (p + z • ω) =
      wallRightEpsilon x y z * pointFarSign (p + y • ω) r (p + z • ω) := by
  apply collinear_right_gate_sign _ _ _ _ ((z - y) / (z - x))
    (div_ne_zero (sub_ne_zero.mpr hzy) (sub_ne_zero.mpr hzx))
  rw [affine_line_difference, affine_line_difference, smul_smul]
  have he : ((z - y) / (z - x)) * (x - z) = y - z := by
    field_simp [sub_ne_zero.mpr hzx]
    ring
  rw [he]

end
end SM

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


#check SM.contact_epsilons_base
#print axioms SM.contact_epsilons_base

#check SM.contact_epsilons_first_arc
#print axioms SM.contact_epsilons_first_arc

#check SM.contact_epsilons_second_arc
#print axioms SM.contact_epsilons_second_arc

#check SM.WallGerm.contact_interior_affine
#print axioms SM.WallGerm.contact_interior_affine

#check SM.CyclicContactBoundaryOrder
#print axioms SM.CyclicContactBoundaryOrder

#check SM.contact_boundary_chi_eq_neg
#print axioms SM.contact_boundary_chi_eq_neg

#check SM.contact_boundary_geometric_sign
#print axioms SM.contact_boundary_geometric_sign

#check SM.WallGerm.contact_boundary_chi_signChanges
#print axioms SM.WallGerm.contact_boundary_chi_signChanges
