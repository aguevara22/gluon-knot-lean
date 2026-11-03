import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Real.Basic

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceAuxiliaryProduct
open MvPolynomial

/-- Evaluation of the literal finite product is nonzero exactly when every
indexed factor evaluates nonzero. The empty family is included. -/
theorem eval_product_ne_zero_iff {ι σ : Type*}
    (s : Finset ι) (P : ι → MvPolynomial σ ℝ) (z : σ → ℝ) :
    MvPolynomial.eval z (∏ i ∈ s, P i) ≠ 0 ↔
      ∀ i ∈ s, MvPolynomial.eval z (P i) ≠ 0 := by
  simp only [map_prod, Finset.prod_ne_zero_iff]

/-- The product's nonzero locus has the exact conjunction of the original
per-factor conditions, with no genericity condition on the ambient point. -/
theorem eval_product_iff_conditions {ι σ : Type*}
    (s : Finset ι) (P : ι → MvPolynomial σ ℝ)
    (C : ι → (σ → ℝ) → Prop)
    (hC : ∀ i ∈ s, ∀ z, MvPolynomial.eval z (P i) ≠ 0 ↔ C i z)
    (z : σ → ℝ) :
    MvPolynomial.eval z (∏ i ∈ s, P i) ≠ 0 ↔
      ∀ i ∈ s, C i z := by
  rw [eval_product_ne_zero_iff]
  exact forall₂_congr fun i hi => hC i hi z

/-- Nonzero factors give a nonzero literal product. -/
theorem product_ne_zero_of_each {ι σ : Type*}
    (s : Finset ι) (P : ι → MvPolynomial σ ℝ)
    (hP : ∀ i ∈ s, P i ≠ 0) :
    (∏ i ∈ s, P i) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr hP

/-- A single actual simultaneous evaluation witness also certifies that
the product is not the zero polynomial. -/
theorem product_ne_zero_of_joint_witness {ι σ : Type*}
    (s : Finset ι) (P : ι → MvPolynomial σ ℝ)
    (z : σ → ℝ)
    (hz : ∀ i ∈ s, MvPolynomial.eval z (P i) ≠ 0) :
    (∏ i ∈ s, P i) ≠ 0 := by
  intro hzero
  have h : MvPolynomial.eval z (∏ i ∈ s, P i) ≠ 0 :=
    (eval_product_ne_zero_iff s P z).2 hz
  exact h (by simp [hzero])

/-- One point satisfying all geometrically characterized conditions is
enough to certify the product polynomial nonzero. -/
theorem product_ne_zero_of_condition_witness {ι σ : Type*}
    (s : Finset ι) (P : ι → MvPolynomial σ ℝ)
    (C : ι → (σ → ℝ) → Prop)
    (hC : ∀ i ∈ s, ∀ z, MvPolynomial.eval z (P i) ≠ 0 ↔ C i z)
    (z : σ → ℝ) (hz : ∀ i ∈ s, C i z) :
    (∏ i ∈ s, P i) ≠ 0 := by
  apply product_ne_zero_of_joint_witness s P z
  intro i hi
  exact (hC i hi z).2 (hz i hi)






end DirectGLSSW.SourceAuxiliaryProduct
