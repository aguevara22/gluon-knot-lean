import SM.AffineResultant
import SM.RealAffineRoots

/-! Real specialization of the remaining-variable coefficients. The variable
being isolated remains a genuine polynomial indeterminate until it is evaluated.
Simple-root and no-common-root assertions use exactly the source's nonzero tests. -/

namespace SM

open MvPolynomial
open scoped Polynomial

noncomputable section

variable {σ : Type*}

def extendCoordinateAssignment (i : σ) (η : {j : σ // j ≠ i} → ℝ) (t : ℝ) : σ → ℝ := by
  classical
  exact fun j => if h : j = i then t else η ⟨j, h⟩

@[simp] theorem extendCoordinateAssignment_self (i : σ) (η : {j : σ // j ≠ i} → ℝ) (t : ℝ) :
    extendCoordinateAssignment i η t i = t := by
  classical
  simp [extendCoordinateAssignment]

@[simp] theorem extendCoordinateAssignment_other (i : σ) (η : {j : σ // j ≠ i} → ℝ)
    (t : ℝ) (j : {j : σ // j ≠ i}) : extendCoordinateAssignment i η t j = η j := by
  classical
  simp [extendCoordinateAssignment, j.property]

theorem extendCoordinateAssignment_reconstruct (i : σ) (ρ : σ → ℝ) :
    extendCoordinateAssignment i (fun j : {j : σ // j ≠ i} => ρ j) (ρ i) = ρ := by
  classical
  funext j
  by_cases h : j = i <;> simp [extendCoordinateAssignment, h]

def specializeCoordinate (i : σ) (p : MvPolynomial σ ℝ) (η : {j : σ // j ≠ i} → ℝ) : ℝ[X] :=
  (isolateCoordinate i p).map (eval η)

theorem specializeCoordinate_affine (i : σ) (p : MvPolynomial σ ℝ) (h : p.degreeOf i ≤ 1)
    (η : {j : σ // j ≠ i} → ℝ) :
    specializeCoordinate i p η =
      realAffinePolynomial (eval η (coordinateSlope i p)) (eval η (coordinateIntercept i p)) := by
  unfold specializeCoordinate
  rw [isolateCoordinate_affine i p h]
  simp [realAffinePolynomial]

theorem specializeCoordinate_eval (i : σ) (p : MvPolynomial σ ℝ) (h : p.degreeOf i ≤ 1)
    (η : {j : σ // j ≠ i} → ℝ) (t : ℝ) :
    (specializeCoordinate i p η).eval t = eval (extendCoordinateAssignment i η t) p := by
  rw [specializeCoordinate_affine i p h η, realAffinePolynomial_eval]
  simpa only [extendCoordinateAssignment_self, extendCoordinateAssignment_other] using
    (eval_coordinate_affine i p h (extendCoordinateAssignment i η t)).symm

theorem specializeCoordinate_simple_root (i : σ) (p : MvPolynomial σ ℝ) (h : p.degreeOf i ≤ 1)
    (η : {j : σ // j ≠ i} → ℝ) (ha : eval η (coordinateSlope i p) ≠ 0) :
    let r := -eval η (coordinateIntercept i p) / eval η (coordinateSlope i p)
    (specializeCoordinate i p η).IsRoot r ∧
      (∀ t, (specializeCoordinate i p η).IsRoot t ↔ t = r) ∧
      (specializeCoordinate i p η).rootMultiplicity r = 1 := by
  dsimp only
  rw [specializeCoordinate_affine i p h η]
  exact ⟨(realAffinePolynomial_root_iff _ _ ha _).mpr rfl,
    realAffinePolynomial_root_iff _ _ ha, realAffinePolynomial_simple_root _ _ ha⟩

theorem specializeCoordinate_no_common_root (i : σ) (p q : MvPolynomial σ ℝ)
    (hp : p.degreeOf i ≤ 1) (hq : q.degreeOf i ≤ 1) (η : {j : σ // j ≠ i} → ℝ)
    (hr : eval η (coordinateResultant i p q) ≠ 0) (t : ℝ) :
    ¬ ((specializeCoordinate i p η).IsRoot t ∧ (specializeCoordinate i q η).IsRoot t) := by
  have hr' : eval η (coordinateSlope i p) * eval η (coordinateIntercept i q) -
      eval η (coordinateIntercept i p) * eval η (coordinateSlope i q) ≠ 0 := by
    simpa only [coordinateResultant, map_sub, map_mul] using hr
  rw [specializeCoordinate_affine i p hp η, specializeCoordinate_affine i q hq η]
  exact realAffinePolynomial_no_common_root _ _ _ _ hr' t

end

end SM
