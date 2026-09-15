import SM.FirstTwoLinePolynomials
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Degree at most one in each actual scalar coordinate for the area and line
row polynomials. These bounds concern the full polynomial ring, not evaluations. -/

namespace SM

open MvPolynomial

variable {n : ℕ}

theorem polynomial_affine_add {σ : Type*} (z : σ) {p q : MvPolynomial σ ℝ}
    (hp : p.degreeOf z ≤ 1) (hq : q.degreeOf z ≤ 1) : (p + q).degreeOf z ≤ 1 :=
  (degreeOf_add_le z p q).trans (max_le hp hq)

theorem polynomial_affine_sub {σ : Type*} (z : σ) {p q : MvPolynomial σ ℝ}
    (hp : p.degreeOf z ≤ 1) (hq : q.degreeOf z ≤ 1) : (p - q).degreeOf z ≤ 1 :=
  (degreeOf_sub_le z p q).trans (max_le hp hq)

theorem coordinateX_affine (z : ScalarCoordinate n) (i : ZMod n) :
    (coordinateX i).degreeOf z ≤ 1 := by
  classical
  simp only [coordinateX, degreeOf_X]
  split_ifs <;> omega

theorem coordinateY_affine (z : ScalarCoordinate n) (i : ZMod n) :
    (coordinateY i).degreeOf z ≤ 1 := by
  classical
  simp only [coordinateY, degreeOf_X]
  split_ifs <;> omega

theorem coordinateXY_affine (z : ScalarCoordinate n) (i j : ZMod n) :
    (coordinateX i * coordinateY j).degreeOf z ≤ 1 := by
  classical
  apply (degreeOf_mul_le z _ _).trans
  obtain ⟨v, s⟩ := z
  fin_cases s <;> simp only [coordinateX, coordinateY, degreeOf_X, Prod.mk.injEq]
  all_goals split_ifs <;> norm_num at *

theorem coordinateYX_affine (z : ScalarCoordinate n) (i j : ZMod n) :
    (coordinateY i * coordinateX j).degreeOf z ≤ 1 := by
  rw [mul_comm]
  exact coordinateXY_affine z j i

theorem linePolynomialC_eq_free (e : ZMod n) : linePolynomialC e = freeLineConstant e := by
  dsimp [linePolynomialC, freeLineConstant, directionPolynomialX, directionPolynomialY]
  ring

theorem freeLineConstant_affine (z : ScalarCoordinate n) (e : ZMod n) :
    (freeLineConstant e).degreeOf z ≤ 1 :=
  polynomial_affine_sub z (coordinateXY_affine z e (e + 1)) (coordinateYX_affine z e (e + 1))

theorem areaPolynomial_expanded (i j k : ZMod n) :
    areaPolynomial i j k =
      coordinateX j * coordinateY k - coordinateX j * coordinateY i -
      coordinateX i * coordinateY k - coordinateY j * coordinateX k +
      coordinateY j * coordinateX i + coordinateY i * coordinateX k := by
  dsimp [areaPolynomial]
  ring

theorem areaPolynomial_affine (z : ScalarCoordinate n) (i j k : ZMod n) :
    (areaPolynomial i j k).degreeOf z ≤ 1 := by
  rw [areaPolynomial_expanded]
  exact polynomial_affine_add z (polynomial_affine_add z
    (polynomial_affine_sub z (polynomial_affine_sub z
      (polynomial_affine_sub z (coordinateXY_affine z j k) (coordinateXY_affine z j i))
      (coordinateXY_affine z i k)) (coordinateYX_affine z j k))
    (coordinateYX_affine z j i)) (coordinateYX_affine z i k)

theorem linePolynomialRow_affine (z : ScalarCoordinate n) (e : ZMod n) (c : Fin 3) :
    (linePolynomialRow e c).degreeOf z ≤ 1 := by
  fin_cases c
  · change (-directionPolynomialY e).degreeOf z ≤ 1
    rw [degreeOf_neg]
    exact polynomial_affine_sub z (coordinateY_affine z (e + 1)) (coordinateY_affine z e)
  · change (directionPolynomialX e).degreeOf z ≤ 1
    exact polynomial_affine_sub z (coordinateX_affine z (e + 1)) (coordinateX_affine z e)
  · change (linePolynomialC e).degreeOf z ≤ 1
    rw [linePolynomialC_eq_free]
    exact freeLineConstant_affine z e

theorem linePolynomialRow_avoids (z : ScalarCoordinate n) (e : ZMod n)
    (he : z.1 ≠ e) (he1 : z.1 ≠ e + 1) (c : Fin 3) : z ∉ (linePolynomialRow e c).vars := by
  fin_cases c
  · change z ∉ (-directionPolynomialY e).vars
    exact polynomial_not_mem_neg (polynomial_not_mem_sub
      (coordinateY_avoids_vertex z (e + 1) he1) (coordinateY_avoids_vertex z e he))
  · change z ∉ (directionPolynomialX e).vars
    exact polynomial_not_mem_sub
      (coordinateX_avoids_vertex z (e + 1) he1) (coordinateX_avoids_vertex z e he)
  · change z ∉ (linePolynomialC e).vars
    rw [linePolynomialC_eq_free]
    exact freeLineConstant_avoids z e he he1

theorem linePolynomialRow_degree_zero (z : ScalarCoordinate n) (e : ZMod n)
    (he : z.1 ≠ e) (he1 : z.1 ≠ e + 1) (c : Fin 3) : (linePolynomialRow e c).degreeOf z = 0 :=
  polynomial_degree_zero (linePolynomialRow_avoids z e he he1 c)

end SM
