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

/-- Translating the point on the common line contributes a parallel vector,
whose determinant with the line direction is zero. -/
theorem det_line_base_translation (p ω r : Plane) (t : ℝ) :
    det ω (r - (p + t • ω)) = det ω (r - p) := by
  dsimp [det]
  ring

/-- The reversed far determinant is the endpoint difference times the
transverse determinant, with the source's exact orientation. -/
theorem affine_line_far_determinant (p ω r : Plane) (x z : ℝ) :
    det (r - (p + z • ω)) ((p + x • ω) - (p + z • ω)) =
      (z - x) * det ω (r - p) := by
  rw [area_cyclic (p + x • ω) (p + z • ω) r, affine_line_difference]
  calc
    det ((z - x) • ω) (r - (p + x • ω)) =
        (z - x) * det ω (r - (p + x • ω)) := by
      dsimp [det]
      ring
    _ = (z - x) * det ω (r - p) := by rw [det_line_base_translation]

/-- Both endpoints of an internal gap may differ from the outer endpoints.
No condition on the transverse point is imposed, so zero determinants remain. -/
theorem affine_internal_gap_determinant (p ω r : Plane) (x z a b : ℝ)
    (hzx : z ≠ x) :
    det (r - (p + b • ω)) ((p + a • ω) - (p + b • ω)) =
      ((b - a) / (z - x)) *
        det (r - (p + z • ω)) ((p + x • ω) - (p + z • ω)) := by
  rw [affine_line_far_determinant, affine_line_far_determinant]
  rw [← mul_assoc, div_mul_cancel₀ _ (sub_ne_zero.mpr hzx)]

/-- Source pf:gap-sign-identity for arbitrary internal-gap endpoints in
arbitrary affine coordinates, including a further silent cut. -/
theorem affine_internal_gap_sign (p ω r : Plane) (x z a b : ℝ)
    (hzx : z ≠ x) (hba : b ≠ a) :
    pointFarSign (p + x • ω) r (p + z • ω) =
      SignType.sign ((b - a) / (z - x)) *
        pointFarSign (p + a • ω) r (p + b • ω) := by
  unfold pointFarSign
  rw [affine_internal_gap_determinant p ω r x z a b hzx]
  exact sign_rescale_nonzero _ _
    (div_ne_zero (sub_ne_zero.mpr hba) (sub_ne_zero.mpr hzx))

/-- Silent further cuts are exactly the same for the outer and gap lines. -/
theorem affine_internal_gap_zero_iff (p ω r : Plane) (x z a b : ℝ)
    (hzx : z ≠ x) (hba : b ≠ a) :
    pointFarSign (p + x • ω) r (p + z • ω) = 0 ↔
      pointFarSign (p + a • ω) r (p + b • ω) = 0 := by
  rw [affine_internal_gap_sign p ω r x z a b hzx hba, mul_eq_zero]
  have hs : SignType.sign ((b - a) / (z - x)) ≠ 0 :=
    sign_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr hba) (sub_ne_zero.mpr hzx))
  simp only [hs, false_or]

/-- The same identity in any commutative coefficient ring, without
division by a geometric sign or a transverse determinant. -/
theorem affine_internal_gap_sign_cast {R : Type*} [CommRing R]
    (p ω r : Plane) (x z a b : ℝ) (hzx : z ≠ x) (hba : b ≠ a) :
    ((pointFarSign (p + x • ω) r (p + z • ω) : ℤ) : R) =
      ((SignType.sign ((b - a) / (z - x)) : ℤ) : R) *
        ((pointFarSign (p + a • ω) r (p + b • ω) : ℤ) : R) := by
  have h := congrArg (fun s : SignType => ((s : ℤ) : R))
    (affine_internal_gap_sign p ω r x z a b hzx hba)
  simpa only [SignType.coe_mul, Int.cast_mul] using h

end
end SM

#print axioms SM.det_line_base_translation
#print axioms SM.affine_line_far_determinant
#print axioms SM.affine_internal_gap_determinant
#print axioms SM.affine_internal_gap_sign
#print axioms SM.affine_internal_gap_zero_iff
#print axioms SM.affine_internal_gap_sign_cast
