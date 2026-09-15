import SM.CuspDefinition
import SM.Farout
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

/-- Incoming root, cut order M,B,A, with the cusp point beyond B. -/
theorem cusp_epsilons_incoming_gt_one (r : ℝ) (hr : 1 < r) :
    wallLeftEpsilon r 1 0 = 1 ∧ wallRightEpsilon r 1 0 = 1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (1 - r) / (0 - r)
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · apply sign_eq_one_iff.mpr
    change 0 < (0 - 1) / (0 - r)
    exact div_pos_of_neg_of_neg (by norm_num) (by linarith)

/-- Incoming root, cut order M,B,A, with the cusp point before A. -/
theorem cusp_epsilons_incoming_lt_zero (r : ℝ) (hr : r < 0) :
    wallLeftEpsilon r 1 0 = 1 ∧ wallRightEpsilon r 1 0 = -1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (1 - r) / (0 - r)
    exact div_pos (by linarith) (by linarith)
  · apply sign_eq_neg_one_iff.mpr
    change (0 - 1) / (0 - r) < 0
    exact div_neg_of_neg_of_pos (by norm_num) (by linarith)

/-- Outgoing root, cut order B,A,M, with the cusp point beyond B. -/
theorem cusp_epsilons_outgoing_gt_one (r : ℝ) (hr : 1 < r) :
    wallLeftEpsilon 1 0 r = -1 ∧ wallRightEpsilon 1 0 r = 1 := by
  constructor
  · apply sign_eq_neg_one_iff.mpr
    change (0 - 1) / (r - 1) < 0
    exact div_neg_of_neg_of_pos (by norm_num) (by linarith)
  · apply sign_eq_one_iff.mpr
    change 0 < (r - 0) / (r - 1)
    exact div_pos (by linarith) (by linarith)

/-- Outgoing root, cut order B,A,M, with the cusp point before A. -/
theorem cusp_epsilons_outgoing_lt_zero (r : ℝ) (hr : r < 0) :
    wallLeftEpsilon 1 0 r = 1 ∧ wallRightEpsilon 1 0 r = 1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (0 - 1) / (r - 1)
    exact div_pos_of_neg_of_neg (by norm_num) (by linarith)
  · apply sign_eq_one_iff.mpr
    change 0 < (r - 0) / (r - 1)
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)

variable {n : ℕ} [NeZero n]

/-- Construct the source line coordinates from the actual cusp predicate.
The direction is B-A and the scalar is obtained from the vanishing determinant.
The exterior clause excludes the entire closed parameter interval [0,1]. -/
theorem WallGerm.cusp_exterior_affine (w : WallGerm n) (j : ZMod n)
    (hc : w.CuspAt j) :
    ∃ r : ℝ, (r < 0 ∨ 1 < r) ∧
      w.center (j + 1) - w.center (j - 1) ≠ 0 ∧
      w.center (j - 1) = w.center (j - 1) +
        (0 : ℝ) • (w.center (j + 1) - w.center (j - 1)) ∧
      w.center j = w.center (j - 1) +
        r • (w.center (j + 1) - w.center (j - 1)) ∧
      w.center (j + 1) = w.center (j - 1) +
        (1 : ℝ) • (w.center (j + 1) - w.center (j - 1)) := by
  have hi := singlePointTriple_vertices_injective hc.1 hc.2.1
  have hAB : w.center (j - 1) ≠ w.center (j + 1) :=
    fun he => prev_ne_next (by have hn := hc.1; omega) j (hi he)
  have hω : w.center (j + 1) - w.center (j - 1) ≠ 0 :=
    sub_ne_zero.mpr hAB.symm
  have hz := singlePointTriple_turn_zero hc.2.1
  have hd : det (w.center j - w.center (j - 1))
      (w.center (j + 1) - w.center (j - 1)) = 0 := sign_eq_zero_iff.mp hz
  have hd' : det (w.center (j + 1) - w.center (j - 1))
      (w.center j - w.center (j - 1)) = 0 := by
    rw [det_swap, hd, neg_zero]
  let r := planeDot (w.center (j + 1) - w.center (j - 1))
      (w.center j - w.center (j - 1)) /
    planeDot (w.center (j + 1) - w.center (j - 1))
      (w.center (j + 1) - w.center (j - 1))
  have he : w.center j - w.center (j - 1) =
      r • (w.center (j + 1) - w.center (j - 1)) := scalar_of_det_zero hω hd'
  have hm : w.center j = w.center (j - 1) +
      r • (w.center (j + 1) - w.center (j - 1)) := by
    rw [← he]
    abel
  have hr : r < 0 ∨ 1 < r := by
    by_cases hr0 : r < 0
    · exact Or.inl hr0
    · right
      exact lt_of_not_ge (fun hr1 =>
        hc.2.2.2.1 ⟨r, le_of_not_gt hr0, hr1, hm⟩)
  refine ⟨r, hr, hω, ?_, hm, ?_⟩
  · simp
  · simp

end
end SM


#check SM.cusp_epsilons_incoming_gt_one
#print axioms SM.cusp_epsilons_incoming_gt_one

#check SM.cusp_epsilons_incoming_lt_zero
#print axioms SM.cusp_epsilons_incoming_lt_zero

#check SM.cusp_epsilons_outgoing_gt_one
#print axioms SM.cusp_epsilons_outgoing_gt_one

#check SM.cusp_epsilons_outgoing_lt_zero
#print axioms SM.cusp_epsilons_outgoing_lt_zero

#check SM.WallGerm.cusp_exterior_affine
#print axioms SM.WallGerm.cusp_exterior_affine
