import SM.PolynomialLinearCore

/-! The coefficient argument for the three-line determinant, before substituting
the concrete first-two-line coefficients and discharging variable separation. -/

namespace SM

open MvPolynomial

theorem linearConcurrence_irreducible {σ : Type*} (A B C : MvPolynomial σ ℝ)
    (x y u v : σ) (hxy : x ≠ y) (hxu : x ≠ u) (hxv : x ≠ v)
    (hyv : y ≠ v) (huv : u ≠ v)
    (hA : ∀ i ∈ ({x, y, u, v} : Set σ), i ∉ A.vars)
    (hB : ∀ i ∈ ({x, y, u, v} : Set σ), i ∉ B.vars)
    (hC : ∀ i ∈ ({x, y, u, v} : Set σ), i ∉ C.vars)
    (hC0 : C ≠ 0) (hCA : IsRelPrime C A) :
    Irreducible ((C * X x - A) * X v + (B - C * X y) * X u) := by
  classical
  have hAx := hA x (by simp)
  have hAy := hA y (by simp)
  have hAv := hA v (by simp)
  have hBx := hB x (by simp)
  have hBy := hB y (by simp)
  have hBv := hB v (by simp)
  have hCx := hC x (by simp)
  have hCy := hC y (by simp)
  have hCv := hC v (by simp)
  let f := C * X x - A
  let g := (B - C * X y) * X u
  have hf : Irreducible f := polynomial_linear_sub_irreducible hC0 hCx hAx hCA
  have hfx : f.degreeOf x = 1 := polynomial_linear_sub_degree hC0 hCx hAx
  have hbdeg : (C * X y - B).degreeOf y = 1 := polynomial_linear_sub_degree hC0 hCy hBy
  have hb0 : C * X y - B ≠ 0 := ne_zero_of_degreeOf_ne_zero (i := y) (by rw [hbdeg]; omega)
  have hg0 : g ≠ 0 := by
    apply mul_ne_zero
    · rw [show B - C * X y = -(C * X y - B) by ring]
      exact neg_ne_zero.mpr hb0
    · exact X_ne_zero u
  have hgx : x ∉ g.vars :=
    polynomial_not_mem_mul
      (polynomial_not_mem_sub hBx (polynomial_not_mem_mul hCx (by simpa using hxy)))
      (by simpa using hxu)
  have hfv : v ∉ f.vars :=
    polynomial_not_mem_sub (polynomial_not_mem_mul hCv (by simpa using hxv.symm)) hAv
  have hgv : v ∉ g.vars :=
    polynomial_not_mem_mul
      (polynomial_not_mem_sub hBv (polynomial_not_mem_mul hCv (by simpa using hyv.symm)))
      (by simpa using huv.symm)
  have hfg : IsRelPrime f g := hf.isRelPrime_iff_not_dvd.mpr
    (polynomial_not_dvd_of_degree_lt hg0 (by rw [polynomial_degree_zero hgx, hfx]; omega))
  exact irreducible_mul_X_add f g v hf.ne_zero hfv hgv hfg

end SM
