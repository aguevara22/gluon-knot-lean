import SM.CoordinateAffinity

/-! Every monomial term of the actual three-line determinant uses one entry
from each row. Remote endpoints ensure a scalar coordinate affects at most one
row, so the actual determinant has degree at most one in that coordinate. -/

namespace SM

open MvPolynomial

variable {n : ℕ}

theorem remote_endpoints_exclude {k e f : ZMod n} (hr : remote e f)
    (hk : k = e ∨ k = e + 1) : k ≠ f ∧ k ≠ f + 1 := by
  obtain ⟨hfe, hfe1, hf1e, hf1e1⟩ := remote_endpoints e f hr
  rcases hk with rfl | rfl
  · exact ⟨hfe.symm, hf1e.symm⟩
  · exact ⟨hfe1.symm, hf1e1.symm⟩

theorem linePolynomial_triple_product_affine (z : ScalarCoordinate n)
    (e f g : ZMod n) (hef : remote e f) (heg : remote e g) (hfg : remote f g)
    (a b c : Fin 3) :
    (linePolynomialRow e a * linePolynomialRow f b * linePolynomialRow g c).degreeOf z ≤ 1 := by
  have hedeg := linePolynomialRow_affine z e a
  have hfdeg := linePolynomialRow_affine z f b
  have hgdeg := linePolynomialRow_affine z g c
  have hprod := degreeOf_mul_le z
    (linePolynomialRow e a * linePolynomialRow f b) (linePolynomialRow g c)
  have hpair := degreeOf_mul_le z (linePolynomialRow e a) (linePolynomialRow f b)
  by_cases he : z.1 = e ∨ z.1 = e + 1
  · obtain ⟨hzf, hzf1⟩ := remote_endpoints_exclude hef he
    obtain ⟨hzg, hzg1⟩ := remote_endpoints_exclude heg he
    have hf0 := linePolynomialRow_degree_zero z f hzf hzf1 b
    have hg0 := linePolynomialRow_degree_zero z g hzg hzg1 c
    omega
  · have he0 := linePolynomialRow_degree_zero z e (not_or.mp he).1 (not_or.mp he).2 a
    by_cases hf : z.1 = f ∨ z.1 = f + 1
    · obtain ⟨hzg, hzg1⟩ := remote_endpoints_exclude hfg hf
      have hg0 := linePolynomialRow_degree_zero z g hzg hzg1 c
      omega
    · have hf0 := linePolynomialRow_degree_zero z f (not_or.mp hf).1 (not_or.mp hf).2 b
      omega

theorem concurrencePolynomial_affine (z : ScalarCoordinate n)
    (e f g : ZMod n) (hef : remote e f) (heg : remote e g) (hfg : remote f g) :
    (concurrencePolynomial e f g).degreeOf z ≤ 1 := by
  have h := linePolynomial_triple_product_affine z e f g hef heg hfg
  rw [concurrencePolynomial_formula]
  exact polynomial_affine_sub z (polynomial_affine_add z
    (polynomial_affine_add z (polynomial_affine_sub z (polynomial_affine_sub z
      (h 0 1 2) (h 0 2 1)) (h 1 0 2)) (h 1 2 0)) (h 2 0 1)) (h 2 1 0)

end SM
