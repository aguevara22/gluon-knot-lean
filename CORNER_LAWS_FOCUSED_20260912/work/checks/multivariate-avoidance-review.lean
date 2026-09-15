import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Data.Real.Basic

/-! Prototype for the next thm:relgp work unit. Not part of the audited theorem
library; kernel compilation alone is not independent source acceptance. -/

namespace SM

open Set Topology MvPolynomial

noncomputable section

variable {σ : Type*}

def scalarAssignmentLine (x y : σ → ℝ) (t : ℝ) : σ → ℝ := fun i =>
  x i + t * (y i - x i)

@[simp] theorem scalarAssignmentLine_zero (x y : σ → ℝ) : scalarAssignmentLine x y 0 = x := by
  funext i
  simp [scalarAssignmentLine]

@[simp] theorem scalarAssignmentLine_one (x y : σ → ℝ) : scalarAssignmentLine x y 1 = y := by
  funext i
  simp [scalarAssignmentLine]

theorem continuous_scalarAssignmentLine (x y : σ → ℝ) : Continuous (scalarAssignmentLine x y) :=
  continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const)

def multivariateLineRestriction (p : MvPolynomial σ ℝ) (x y : σ → ℝ) : Polynomial ℝ :=
  eval₂Hom Polynomial.C (fun i => Polynomial.C (x i) +
    Polynomial.X * Polynomial.C (y i - x i)) p

theorem multivariateLineRestriction_eval (p : MvPolynomial σ ℝ) (x y : σ → ℝ) (t : ℝ) :
    (multivariateLineRestriction p x y).eval t = eval (scalarAssignmentLine x y t) p := by
  have hh : (Polynomial.evalRingHom t).comp
      (eval₂Hom Polynomial.C (fun i => Polynomial.C (x i) +
        Polynomial.X * Polynomial.C (y i - x i))) = eval (scalarAssignmentLine x y t) := by
    ext r <;> simp [scalarAssignmentLine]
  exact DFunLike.congr_fun hh p

theorem exists_nonzero_multivariate_eval (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
    ∃ x : σ → ℝ, eval x p ≠ 0 := by
  by_contra h
  push Not at h
  apply hp
  apply MvPolynomial.funext
  intro x
  simpa only [map_zero] using h x

theorem dense_nonzero_multivariate_eval (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
    Dense {x : σ → ℝ | eval x p ≠ 0} := by
  obtain ⟨y, hy⟩ := exists_nonzero_multivariate_eval p hp
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨x, hx⟩ := hne
  let q := multivariateLineRestriction p x y
  have hq1 : q.eval 1 = eval y p := by
    rw [multivariateLineRestriction_eval, scalarAssignmentLine_one]
  have hq : q ≠ 0 := by
    intro h
    rw [h, Polynomial.eval_zero] at hq1
    exact hy hq1.symm
  have hd : Dense {t : ℝ | q.eval t ≠ 0} := by
    have hr := (dense_univ : Dense (Set.univ : Set ℝ)).sdiff_finite
      (Polynomial.finite_setOfPred_isRoot hq)
    exact hr.mono (fun _ ht => ht.2)
  have ho : IsOpen ((scalarAssignmentLine x y) ⁻¹' U) :=
    hU.preimage (continuous_scalarAssignmentLine x y)
  have hn : ((scalarAssignmentLine x y) ⁻¹' U).Nonempty :=
    ⟨0, by simpa only [Set.mem_preimage, scalarAssignmentLine_zero] using hx⟩
  obtain ⟨t, ht, htU⟩ := hd.exists_mem_open ho hn
  refine ⟨scalarAssignmentLine x y t, htU, ?_⟩
  change eval (scalarAssignmentLine x y t) p ≠ 0
  rw [← multivariateLineRestriction_eval]
  exact ht

theorem dense_finite_nonzero_multivariate {ι : Type*} [Finite ι]
    (p : ι → MvPolynomial σ ℝ) (hp : ∀ i, p i ≠ 0) :
    Dense {x : σ → ℝ | ∀ i, eval x (p i) ≠ 0} := by
  let A : ι → Set (σ → ℝ) := fun i => {x | eval x (p i) ≠ 0}
  have ho : ∀ i, IsOpen (A i) := fun i =>
    isOpen_ne.preimage (MvPolynomial.continuous_eval (p i))
  have hd : ∀ i, Dense (A i) := fun i => dense_nonzero_multivariate_eval (p i) (hp i)
  have hs := (Set.finite_range A).dense_sInter
    (by rintro _ ⟨i, rfl⟩; exact ho i) (by rintro _ ⟨i, rfl⟩; exact hd i)
  apply hs.mono
  intro x hx i
  exact Set.mem_sInter.mp hx (A i) (Set.mem_range_self i)

theorem exists_simultaneous_nonzero_in_open {ι : Type*} [Finite ι]
    (p : ι → MvPolynomial σ ℝ) (hp : ∀ i, p i ≠ 0)
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ i, eval x (p i) ≠ 0 := by
  obtain ⟨x, hx, hxU⟩ := (dense_finite_nonzero_multivariate p hp).exists_mem_open hU hne
  exact ⟨x, hxU, hx⟩

end

end SM

#print axioms SM.multivariateLineRestriction_eval
#print axioms SM.exists_nonzero_multivariate_eval
#print axioms SM.dense_nonzero_multivariate_eval
#print axioms SM.dense_finite_nonzero_multivariate
#print axioms SM.exists_simultaneous_nonzero_in_open

-- Independent statement/definition inspection of the exact frozen prototype.
#print SM.scalarAssignmentLine
#print SM.multivariateLineRestriction
#check @SM.scalarAssignmentLine_zero
#check @SM.scalarAssignmentLine_one
#check @SM.continuous_scalarAssignmentLine
#check @SM.multivariateLineRestriction_eval
#check @SM.exists_nonzero_multivariate_eval
#check @SM.dense_nonzero_multivariate_eval
#check @SM.dense_finite_nonzero_multivariate
#check @SM.exists_simultaneous_nonzero_in_open

-- Empty finite condition families still have one common assignment in U.
example {σ : Type*} (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ i : Fin 0, MvPolynomial.eval x (0 : MvPolynomial σ ℝ) ≠ 0 := by
  exact SM.exists_simultaneous_nonzero_in_open (fun _ : Fin 0 => (0 : MvPolynomial σ ℝ))
    (fun i => Fin.elim0 i) U hU hne
