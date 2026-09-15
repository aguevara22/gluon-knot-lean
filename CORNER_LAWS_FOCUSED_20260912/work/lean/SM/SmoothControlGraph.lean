import SM.CentralLegRootControls
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace SM

open Set MvPolynomial
open scoped ContDiff

noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem contDiff_polynomial_eval (p : MvPolynomial σ ℝ) :
    ContDiff ℝ ∞ (fun ρ : σ → ℝ => eval ρ p) :=
  (AnalyticOnNhd.eval_mvPolynomial p).contDiff

def coordinateSlopeDomain (i : σ) (p : MvPolynomial σ ℝ) :
    Set ({j : σ // j ≠ i} → ℝ) :=
  {η | eval η (coordinateSlope i p) ≠ 0}

def coordinateRootFunction (i : σ) (p : MvPolynomial σ ℝ)
    (η : {j : σ // j ≠ i} → ℝ) : ℝ :=
  -eval η (coordinateIntercept i p) / eval η (coordinateSlope i p)

theorem isOpen_coordinateSlopeDomain (i : σ) (p : MvPolynomial σ ℝ) :
    IsOpen (coordinateSlopeDomain i p) :=
  (isClosed_eq (contDiff_polynomial_eval (coordinateSlope i p)).continuous
    continuous_const).isOpen_compl

theorem contDiffOn_coordinateRootFunction (i : σ) (p : MvPolynomial σ ℝ) :
    ContDiffOn ℝ ∞ (coordinateRootFunction i p) (coordinateSlopeDomain i p) :=
  (contDiff_polynomial_eval (coordinateIntercept i p)).neg.contDiffOn.div
    (contDiff_polynomial_eval (coordinateSlope i p)).contDiffOn (fun _ h => h)

theorem coordinate_graph_zero_iff (i : σ) (p : MvPolynomial σ ℝ) (hp : p.degreeOf i ≤ 1)
    (η : {j : σ // j ≠ i} → ℝ) (hη : η ∈ coordinateSlopeDomain i p) (t : ℝ) :
    eval (extendCoordinateAssignment i η t) p = 0 ↔ t = coordinateRootFunction i p η := by
  rw [← specializeCoordinate_eval i p hp η t]
  exact (specializeCoordinate_simple_root i p hp η hη).2.1 t

theorem coordinate_graph_actual_assignment (i : σ) (p : MvPolynomial σ ℝ)
    (hp : p.degreeOf i ≤ 1) (ρ : σ → ℝ)
    (hρ : (fun j : {j : σ // j ≠ i} => ρ j) ∈ coordinateSlopeDomain i p) :
    eval ρ p = 0 ↔ ρ i = coordinateRootFunction i p (fun j => ρ j) := by
  have h := coordinate_graph_zero_iff i p hp _ hρ (ρ i)
  rwa [extendCoordinateAssignment_reconstruct] at h

theorem isOpen_coordinate_graph_ambient_domain (i : σ) (p : MvPolynomial σ ℝ) :
    IsOpen {ρ : σ → ℝ | (fun j : {j : σ // j ≠ i} => ρ j) ∈ coordinateSlopeDomain i p} :=
  (isOpen_coordinateSlopeDomain i p).preimage
    (continuous_pi fun j => continuous_apply j.val)

theorem coordinate_graph_injective (i : σ) (p : MvPolynomial σ ℝ) :
    Function.Injective (fun η : {j : σ // j ≠ i} → ℝ =>
      extendCoordinateAssignment i η (coordinateRootFunction i p η)) := by
  intro η ξ h
  funext j
  have he := congrFun h j.val
  simpa only [extendCoordinateAssignment_other] using he

theorem contDiffOn_coordinate_graph (i : σ) (p : MvPolynomial σ ℝ) :
    ContDiffOn ℝ ∞ (fun η : {j : σ // j ≠ i} → ℝ =>
      extendCoordinateAssignment i η (coordinateRootFunction i p η)) (coordinateSlopeDomain i p) := by
  apply contDiffOn_pi.mpr
  intro j
  by_cases hj : j = i
  · simpa only [extendCoordinateAssignment, hj, dite_true] using contDiffOn_coordinateRootFunction i p
  · simpa only [extendCoordinateAssignment, hj, dite_false] using
      (contDiff_apply ℝ ℝ (n := ∞) (⟨j, hj⟩ : {j : σ // j ≠ i})).contDiffOn

theorem coordinate_graph_projection (i : σ) (p : MvPolynomial σ ℝ)
    (η : {j : σ // j ≠ i} → ℝ) :
    (fun j : {j : σ // j ≠ i} =>
      extendCoordinateAssignment i η (coordinateRootFunction i p η) j) = η := by
  funext j
  exact extendCoordinateAssignment_other _ _ _ j

theorem contDiff_remaining_projection (i : σ) :
    ContDiff ℝ ∞ (fun ρ : σ → ℝ => fun j : {j : σ // j ≠ i} => ρ j) :=
  contDiff_pi.mpr (fun j => contDiff_apply ℝ ℝ j.val)

theorem coordinate_zero_set_eq_graph (i : σ) (p : MvPolynomial σ ℝ)
    (hp : p.degreeOf i ≤ 1) :
    {ρ : σ → ℝ | (fun j : {j : σ // j ≠ i} => ρ j) ∈ coordinateSlopeDomain i p ∧ eval ρ p = 0} =
      (fun η : {j : σ // j ≠ i} → ℝ =>
        extendCoordinateAssignment i η (coordinateRootFunction i p η)) '' coordinateSlopeDomain i p := by
  ext ρ
  constructor
  · rintro ⟨hρ, hz⟩
    refine ⟨(fun j => ρ j), hρ, ?_⟩
    have he := (coordinate_graph_actual_assignment i p hp ρ hρ).mp hz
    change extendCoordinateAssignment i (fun j => ρ j)
      (coordinateRootFunction i p (fun j => ρ j)) = ρ
    rw [← he, extendCoordinateAssignment_reconstruct]
  · rintro ⟨η, hη, rfl⟩
    refine ⟨?_, (coordinate_graph_zero_iff i p hp η hη _).mpr rfl⟩
    simpa only [coordinate_graph_projection] using hη

theorem central_root_smooth_graph {κ : Type*} {n : ℕ} [NeZero n]
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) (r : ℝ)
    (hr : eval (leg.assignment W r) (namedControlPolynomial name) = 0) :
    ∃ U : Set ({j : ScalarCoordinate n // j ≠ leg.moving} → ℝ),
      IsOpen U ∧ leg.fixedAssignment W ∈ U ∧
      ContDiffOn ℝ ∞ (coordinateRootFunction leg.moving (namedControlPolynomial name)) U ∧
      (∀ η ∈ U, ∀ t : ℝ,
        eval (extendCoordinateAssignment leg.moving η t) (namedControlPolynomial name) = 0 ↔
          t = coordinateRootFunction leg.moving (namedControlPolynomial name) η) ∧
      (leg.assignment W r) leg.moving =
        coordinateRootFunction leg.moving (namedControlPolynomial name) (leg.fixedAssignment W) := by
  have hroot : (leg.parameterPolynomial W (namedControlPolynomial name)).IsRoot r := by
    change (leg.parameterPolynomial W (namedControlPolynomial name)).eval r = 0
    rw [leg.parameterPolynomial_eval W _ (namedControlPolynomial_affine name _)]
    exact hr
  have hdep := central_root_forces_dependency leg W h name r hroot
  have hs := h.dependent_slopes name hdep
  refine ⟨coordinateSlopeDomain leg.moving (namedControlPolynomial name),
    isOpen_coordinateSlopeDomain _ _, hs, contDiffOn_coordinateRootFunction _ _, ?_, ?_⟩
  · intro η hη t
    exact coordinate_graph_zero_iff _ _ (namedControlPolynomial_affine name _) η hη t
  · have hfixed : (fun j : {j : ScalarCoordinate n // j ≠ leg.moving} =>
        leg.assignment W r j) = leg.fixedAssignment W := by
      funext j
      exact leg.assignment_other W r j
    have he := coordinate_graph_actual_assignment leg.moving (namedControlPolynomial name)
      (namedControlPolynomial_affine name _) (leg.assignment W r)
      (by simpa only [hfixed, coordinateSlopeDomain, Set.mem_setOf_eq] using hs)
    have hc := he.mp hr
    simpa only [hfixed] using hc

end

end SM
