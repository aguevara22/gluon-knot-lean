import SM.CriticalSourceResponse
import SM.UnorderedWallTriples
import SM.StrictBetween
import SM.EuclideanPlane
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

#check SM.flat_epsilons_nonincident
#print axioms SM.flat_epsilons_nonincident

#check SM.flat_epsilons_incoming
#print axioms SM.flat_epsilons_incoming

#check SM.flat_epsilons_outgoing
#print axioms SM.flat_epsilons_outgoing

#check SM.strictBetween_flat_affine
#print axioms SM.strictBetween_flat_affine

#check SM.CyclicTurnBoundaryOrder
#print axioms SM.CyclicTurnBoundaryOrder

#check SM.turn_far_cyclic_signs
#print axioms SM.turn_far_cyclic_signs

#check SM.flat_boundary_chi_eq_neg_turn
#print axioms SM.flat_boundary_chi_eq_neg_turn

#check SM.flat_boundary_geometric_sign
#print axioms SM.flat_boundary_geometric_sign

#check SM.WallGerm.flat_boundary_chi_signChanges
#print axioms SM.WallGerm.flat_boundary_chi_signChanges
