import SM.PolynomialLinearCore
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! Isolate one actual scalar indeterminate. Coefficients live in the polynomial
ring on precisely the other indeterminates, with proved embedding and evaluation
identities. The affine slope is nonzero whenever that coordinate occurs. -/

namespace SM

open MvPolynomial

noncomputable section

variable {σ : Type*}

abbrev RemainingPolynomial (i : σ) := MvPolynomial {j : σ // j ≠ i} ℝ

def isolateCoordinate (i : σ) : MvPolynomial σ ℝ ≃ₐ[ℝ] Polynomial (RemainingPolynomial i) := by
  classical
  exact (renameEquiv ℝ (Equiv.optionSubtypeNe i).symm).trans (optionEquivLeft ℝ _)

def embedRemaining (i : σ) : RemainingPolynomial i →ₐ[ℝ] MvPolynomial σ ℝ := rename Subtype.val

@[simp] theorem isolateCoordinate_X_self (i : σ) : isolateCoordinate i (X i) = Polynomial.X := by
  classical
  simp [isolateCoordinate]

@[simp] theorem isolateCoordinate_X_other (i j : σ) (h : j ≠ i) :
    isolateCoordinate i (X j) = Polynomial.C (X (⟨j, h⟩ : {j : σ // j ≠ i})) := by
  classical
  simp [isolateCoordinate, Equiv.optionSubtypeNe_symm_apply, h]

@[simp] theorem isolateCoordinate_embedRemaining (i : σ) (a : RemainingPolynomial i) :
    isolateCoordinate i (embedRemaining i a) = Polynomial.C a := by
  have hh : (isolateCoordinate i).toAlgHom.comp (embedRemaining i) = Polynomial.CAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [embedRemaining, j.property]
  exact DFunLike.congr_fun hh a

@[simp] theorem isolateCoordinate_symm_C (i : σ) (a : RemainingPolynomial i) :
    (isolateCoordinate i).symm (Polynomial.C a) = embedRemaining i a := by
  apply (isolateCoordinate i).injective
  simp

@[simp] theorem isolateCoordinate_symm_X (i : σ) :
    (isolateCoordinate i).symm Polynomial.X = X i := by
  apply (isolateCoordinate i).injective
  simp

theorem isolateCoordinate_natDegree (i : σ) (p : MvPolynomial σ ℝ) :
    (isolateCoordinate i p).natDegree = p.degreeOf i := by
  classical
  simpa [isolateCoordinate] using (degreeOf_eq_natDegree i p).symm

theorem embedRemaining_injective (i : σ) : Function.Injective (embedRemaining i) :=
  rename_injective Subtype.val Subtype.val_injective

theorem embedRemaining_avoids (i : σ) (a : RemainingPolynomial i) :
    i ∉ (embedRemaining i a).vars := by
  intro h
  obtain ⟨j, hj, he⟩ := mem_vars_rename Subtype.val a h
  exact j.property he

@[simp] theorem eval_embedRemaining (i : σ) (a : RemainingPolynomial i) (ρ : σ → ℝ) :
    eval ρ (embedRemaining i a) = eval (fun j : {j : σ // j ≠ i} => ρ j) a := by
  exact eval_rename (k := Subtype.val) ρ a

def coordinateSlope (i : σ) (p : MvPolynomial σ ℝ) : RemainingPolynomial i :=
  (isolateCoordinate i p).coeff 1

def coordinateIntercept (i : σ) (p : MvPolynomial σ ℝ) : RemainingPolynomial i :=
  (isolateCoordinate i p).coeff 0

theorem isolateCoordinate_affine (i : σ) (p : MvPolynomial σ ℝ) (h : p.degreeOf i ≤ 1) :
    isolateCoordinate i p = Polynomial.C (coordinateSlope i p) * Polynomial.X +
      Polynomial.C (coordinateIntercept i p) := by
  exact Polynomial.eq_X_add_C_of_natDegree_le_one ((isolateCoordinate_natDegree i p).trans_le h)

theorem coordinate_affine_decomposition (i : σ) (p : MvPolynomial σ ℝ) (h : p.degreeOf i ≤ 1) :
    p = embedRemaining i (coordinateSlope i p) * X i + embedRemaining i (coordinateIntercept i p) := by
  apply (isolateCoordinate i).injective
  simpa only [map_add, map_mul, isolateCoordinate_embedRemaining, isolateCoordinate_X_self] using
    isolateCoordinate_affine i p h

theorem coordinateSlope_ne_zero (i : σ) (p : MvPolynomial σ ℝ)
    (h : p.degreeOf i ≤ 1) (hdep : i ∈ p.vars) : coordinateSlope i p ≠ 0 := by
  intro hz
  have he := isolateCoordinate_affine i p h
  rw [hz, map_zero, zero_mul, zero_add] at he
  have hn := congrArg Polynomial.natDegree he
  rw [isolateCoordinate_natDegree, Polynomial.natDegree_C] at hn
  exact (mem_vars_iff_degreeOf_ne_zero.mp hdep) hn

theorem eval_coordinate_affine (i : σ) (p : MvPolynomial σ ℝ)
    (h : p.degreeOf i ≤ 1) (ρ : σ → ℝ) :
    eval ρ p = eval (fun j : {j : σ // j ≠ i} => ρ j) (coordinateSlope i p) * ρ i +
      eval (fun j : {j : σ // j ≠ i} => ρ j) (coordinateIntercept i p) := by
  have he := congrArg (eval ρ) (coordinate_affine_decomposition i p h)
  simpa only [map_add, map_mul, eval_embedRemaining, eval_X] using he

end

end SM
