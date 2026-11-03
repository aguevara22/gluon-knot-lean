import DirectGLSSW.GeometricGates

/-!
# Published spinor brackets and ratio gates

GLSSW, arXiv:2602.12176v1, equations (2)–(5), fixes the frame
`(ω, ω z)` and bracket `ωᵢ ωⱼ (zᵢ - zⱼ)`. In the component order
used for `PlanarPoint`, this is the negative Cartesian determinant.
The polynomial identities below prove its identification with the note's
`ep:H` convention, including sums of consecutive external momenta.

The ordinary and marked ratios of Section I.2 are identified with the
note's `ep:linear-gates` only on nonzero numerator and denominator inputs.
The total scalar sign and positive step are implementation extensions at
zero; they make no claim about degenerate physical vertex factors.
-/

namespace DirectGLSSW

variable {K : Type*}

section Brackets

variable [CommRing K]

/-- The alternating form in the published Cartesian component order. -/
def spinorBracket (u v : PlanarPoint K) : K := u.2 * v.1 - u.1 * v.2

/-- The component-order translation has exactly one orientation minus sign. -/
theorem spinorBracket_eq_neg_planarDet (u v : PlanarPoint K) :
    spinorBracket u v = -planarDet u v := by
  simp only [spinorBracket, planarDet]
  ring

/-- The displayed GLSSW frame reproduces its displayed bracket formula. -/
theorem spinorBracket_frame (ω₁ z₁ ω₂ z₂ : K) :
    spinorBracket (ω₁, ω₁ * z₁) (ω₂, ω₂ * z₂) =
      ω₁ * ω₂ * (z₁ - z₂) := by
  simp only [spinorBracket]
  ring

/-- The adjacent-block bracket is the scalar whose sign is the near H sign. -/
theorem spinorBracket_polygonChords (q : ℕ → PlanarPoint K) (a b c : ℕ) :
    spinorBracket (polygonChord q a b) (polygonChord q b c) =
      polygonHDet q a b c := by
  rw [spinorBracket_eq_neg_planarDet, polygonHDet_eq_neg_turn]

/-- The prefix/total bracket is the same far H determinant. -/
theorem spinorBracket_polygonPartialTotal (q : ℕ → PlanarPoint K) (i k j : ℕ) :
    spinorBracket (polygonChord q i k) (polygonChord q i j) =
      polygonHDet q i k j := by
  rw [spinorBracket_eq_neg_planarDet, polygonDet_partial_total,
    polygonHDet_eq_neg_turn]

/-- Two consecutive sums of external momenta give the bracket of their chords. -/
theorem spinorBracket_polygonMomentum_blocks (q : ℕ → PlanarPoint K)
    (a m n : ℕ) :
    spinorBracket (∑ r ∈ Finset.range m, polygonMomentum q (a + r))
        (∑ r ∈ Finset.range n, polygonMomentum q (a + m + r)) =
      polygonHDet q a (a + m) (a + m + n) := by
  rw [polygonMomentum_sum, polygonMomentum_sum, spinorBracket_polygonChords]

end Brackets

section Signs

variable [Field K] [LinearOrder K]

/-- The ordinary scalar sign, rational valued, with an explicit zero extension. -/
noncomputable def scalarSignValue (x : K) : ℚ :=
  if x = 0 then 0 else if x < 0 then -1 else 1

/-- On the nonzero domain the total scalar sign is the two-valued source sign. -/
theorem scalarSignValue_eq_nonzeroScalarSign (x : K) (hx : x ≠ 0) :
    scalarSignValue x = (nonzeroScalarSign x hx).value := by
  by_cases hn : x < 0 <;> simp [scalarSignValue, hx, nonzeroScalarSign, hn, Sign.value]

variable [IsStrictOrderedRing K]

/-- A ratio and the corresponding product have the same positive-step value.
The equality also holds for the total extensions at zero. -/
theorem scalarPositiveStep_div_mul (h d : K) :
    scalarPositiveStep (h / d) = scalarPositiveStep (h * d) := by
  simp only [scalarPositiveStep, div_eq_mul_inv, mul_pos_iff, inv_pos, inv_lt_zero]

/-- The negative ratio and negative product also have the same step. -/
theorem scalarPositiveStep_neg_div_mul (h d : K) :
    scalarPositiveStep (-(h / d)) = scalarPositiveStep (-(h * d)) := by
  simpa only [neg_div, neg_mul] using scalarPositiveStep_div_mul (-h) d

/-- The published ordinary ratio gate agrees with the note's ordinary gate. -/
theorem ordinaryGate_scalar_ratio (d h : K) (hd : d ≠ 0) (hh : h ≠ 0) :
    (nonzeroScalarSign d hd).value * scalarPositiveStep (-(h / d)) =
      ordinaryGate (nonzeroScalarSign d hd) (nonzeroScalarSign h hh) := by
  rw [scalarPositiveStep_neg_div_mul]
  exact ordinaryGate_scalar_heaviside d h hd hh

/-- The published marked ratio gate agrees with the note's marked gate. -/
theorem markedGate_scalar_ratio (d h : K) (hd : d ≠ 0) (hh : h ≠ 0) :
    (nonzeroScalarSign d hd).value * scalarPositiveStep (h / d) =
      markedGate (nonzeroScalarSign d hd) (nonzeroScalarSign h hh) := by
  rw [scalarPositiveStep_div_mul]
  exact markedGate_scalar_heaviside d h hd hh

/-- Scalar-sign presentation of the ordinary ratio gate, away from zero. -/
theorem scalarSignValue_ordinary_ratio (d h : K) (hd : d ≠ 0) (hh : h ≠ 0) :
    scalarSignValue d * scalarPositiveStep (-(h / d)) =
      (scalarSignValue d - scalarSignValue h) / 2 := by
  rw [scalarSignValue_eq_nonzeroScalarSign d hd,
    scalarSignValue_eq_nonzeroScalarSign h hh]
  exact ordinaryGate_scalar_ratio d h hd hh

/-- Scalar-sign presentation of the marked ratio gate, away from zero. -/
theorem scalarSignValue_marked_ratio (d h : K) (hd : d ≠ 0) (hh : h ≠ 0) :
    scalarSignValue d * scalarPositiveStep (h / d) =
      (scalarSignValue d + scalarSignValue h) / 2 := by
  rw [scalarSignValue_eq_nonzeroScalarSign d hd,
    scalarSignValue_eq_nonzeroScalarSign h hh]
  exact markedGate_scalar_ratio d h hd hh

end Signs

end DirectGLSSW
