import DirectGLSSW.GeometricGates
import Mathlib.Algebra.Module.Prod
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DirectGLSSW.EndpointCollinearity

open DirectGLSSW

variable {K : Type*}

theorem farDet_prefix_rescaling [CommRing K]
    (q : ℕ → PlanarPoint K) (p i k j : ℕ) (τ : K)
    (hk : q k = q p + τ • (q j - q p)) :
    polygonHDet q p i k = τ * polygonHDet q p i j := by
  simp only [polygonHDet, hk, planarDet, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem farDet_suffix_rescaling [CommRing K]
    (q : ℕ → PlanarPoint K) (p i k j : ℕ) (τ : K)
    (hk : q k = q p + τ • (q j - q p)) :
    polygonHDet q k i j = (1 - τ) * polygonHDet q p i j := by
  simp only [polygonHDet, hk, planarDet, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem nonzeroScalarSign_value_mul [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    (nonzeroScalarSign (x * y) (mul_ne_zero hx hy)).value =
      (nonzeroScalarSign x hx).value * (nonzeroScalarSign y hy).value := by
  by_cases hxn : x < 0
  · by_cases hyn : y < 0
    · have hxy : 0 < x * y := mul_pos_of_neg_of_neg hxn hyn
      simp [nonzeroScalarSign, hxn, hyn, not_lt_of_gt hxy, Sign.value]
    · have hyp : 0 < y := lt_of_le_of_ne (le_of_not_gt hyn) (Ne.symm hy)
      have hxy : x * y < 0 := mul_neg_of_neg_of_pos hxn hyp
      simp [nonzeroScalarSign, hxn, hyn, hxy, Sign.value]
  · have hxp : 0 < x := lt_of_le_of_ne (le_of_not_gt hxn) (Ne.symm hx)
    by_cases hyn : y < 0
    · have hxy : x * y < 0 := mul_neg_of_pos_of_neg hxp hyn
      simp [nonzeroScalarSign, hxn, hyn, hxy, Sign.value]
    · have hyp : 0 < y := lt_of_le_of_ne (le_of_not_gt hyn) (Ne.symm hy)
      have hxy : 0 < x * y := mul_pos hxp hyp
      simp [nonzeroScalarSign, hxn, hyn, not_lt_of_gt hxy, Sign.value]

theorem collinear_far_sign_identities [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (q : ℕ → PlanarPoint K) (p i k j : ℕ) (τ : K)
    (hk : q k = q p + τ • (q j - q p))
    (hτ : τ ≠ 0) (hτ1 : 1 - τ ≠ 0) (hH : polygonHDet q p i j ≠ 0) :
    ∃ hPrefix : polygonHDet q p i k ≠ 0,
      ∃ hSuffix : polygonHDet q k i j ≠ 0,
        (nonzeroScalarSign (polygonHDet q p i k) hPrefix).value =
          (nonzeroScalarSign τ hτ).value *
            (nonzeroScalarSign (polygonHDet q p i j) hH).value ∧
        (nonzeroScalarSign (polygonHDet q k i j) hSuffix).value =
          (nonzeroScalarSign (1 - τ) hτ1).value *
            (nonzeroScalarSign (polygonHDet q p i j) hH).value := by
  have hPrefix : polygonHDet q p i k ≠ 0 := by
    rw [farDet_prefix_rescaling q p i k j τ hk]
    exact mul_ne_zero hτ hH
  have hSuffix : polygonHDet q k i j ≠ 0 := by
    rw [farDet_suffix_rescaling q p i k j τ hk]
    exact mul_ne_zero hτ1 hH
  refine ⟨hPrefix, hSuffix, ?_, ?_⟩
  · simpa only [farDet_prefix_rescaling q p i k j τ hk] using
      nonzeroScalarSign_value_mul τ (polygonHDet q p i j) hτ hH
  · simpa only [farDet_suffix_rescaling q p i k j τ hk] using
      nonzeroScalarSign_value_mul (1 - τ) (polygonHDet q p i j) hτ1 hH






end DirectGLSSW.EndpointCollinearity
