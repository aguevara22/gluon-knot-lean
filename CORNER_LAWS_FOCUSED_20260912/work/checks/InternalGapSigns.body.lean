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
