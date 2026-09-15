import SM.CentralLegRootControls
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Development: the actual affine-in-one-coordinate control zero set is a
smooth graph wherever its fixed-coordinate slope is nonzero. No implicit
function theorem or extra regular-value assumption is admitted. -/

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


set_option pp.fullNames true
set_option pp.universes false

#check SM.contDiff_polynomial_eval
#print axioms SM.contDiff_polynomial_eval

#check SM.coordinateSlopeDomain
#print axioms SM.coordinateSlopeDomain

#check SM.coordinateRootFunction
#print axioms SM.coordinateRootFunction

#check SM.isOpen_coordinateSlopeDomain
#print axioms SM.isOpen_coordinateSlopeDomain

#check SM.contDiffOn_coordinateRootFunction
#print axioms SM.contDiffOn_coordinateRootFunction

#check SM.coordinate_graph_zero_iff
#print axioms SM.coordinate_graph_zero_iff

#check SM.coordinate_graph_actual_assignment
#print axioms SM.coordinate_graph_actual_assignment

#check SM.isOpen_coordinate_graph_ambient_domain
#print axioms SM.isOpen_coordinate_graph_ambient_domain

#check SM.coordinate_graph_injective
#print axioms SM.coordinate_graph_injective

#check SM.contDiffOn_coordinate_graph
#print axioms SM.contDiffOn_coordinate_graph

#check SM.coordinate_graph_projection
#print axioms SM.coordinate_graph_projection

#check SM.contDiff_remaining_projection
#print axioms SM.contDiff_remaining_projection

#check SM.coordinate_zero_set_eq_graph
#print axioms SM.coordinate_zero_set_eq_graph

#check SM.central_root_smooth_graph
#print axioms SM.central_root_smooth_graph

#print SM.coordinateSlopeDomain
#print SM.coordinateRootFunction

open Set MvPolynomial
open scoped ContDiff

-- A genuine control root with the actual joint conditions gives the full
-- concrete graph geometry at its actual scalar assignment. No slope or
-- smoothness premise is supplied, and n>=3 discharges NeZero locally.
example {kappa : Type*} {n : ℕ} (hn : 3 ≤ n)
    (leg : SM.CoordinateWaypointLeg kappa (SM.ScalarCoordinate n))
    (W : kappa × SM.ScalarCoordinate n → ℝ) (h : SM.JointLegConditions leg W)
    (name : SM.PolynomialControlName n) (r : ℝ)
    (hr : eval (leg.assignment W r) (SM.namedControlPolynomial name) = 0) :
    letI : NeZero n := ⟨by omega⟩
    let U := SM.coordinateSlopeDomain leg.moving (SM.namedControlPolynomial name)
    let G := fun eta : {j : SM.ScalarCoordinate n // j ≠ leg.moving} → ℝ =>
      SM.extendCoordinateAssignment leg.moving eta
        (SM.coordinateRootFunction leg.moving (SM.namedControlPolynomial name) eta)
    let R := fun rho : SM.ScalarCoordinate n → ℝ =>
      fun j : {j : SM.ScalarCoordinate n // j ≠ leg.moving} => rho j
    IsOpen U ∧ leg.fixedAssignment W ∈ U ∧ ContDiffOn ℝ ∞ G U ∧
      Function.Injective G ∧ ContDiff ℝ ∞ R ∧ (∀ eta, R (G eta) = eta) ∧
      IsOpen (R ⁻¹' U) ∧ leg.assignment W r ∈ R ⁻¹' U ∧
      {rho : SM.ScalarCoordinate n → ℝ | R rho ∈ U ∧
        eval rho (SM.namedControlPolynomial name) = 0} = G '' U ∧
      leg.assignment W r ∈ G '' U := by
  letI : NeZero n := ⟨by omega⟩
  dsimp only
  have hroot : (leg.parameterPolynomial W (SM.namedControlPolynomial name)).IsRoot r := by
    change (leg.parameterPolynomial W (SM.namedControlPolynomial name)).eval r = 0
    rw [leg.parameterPolynomial_eval W _ (SM.namedControlPolynomial_affine name _)]
    exact hr
  have hs := h.dependent_slopes name (SM.central_root_forces_dependency leg W h name r hroot)
  have hfixed : (fun j : {j : SM.ScalarCoordinate n // j ≠ leg.moving} =>
      leg.assignment W r j) = leg.fixedAssignment W := by
    funext j
    exact leg.assignment_other W r j
  have heta : (fun j : {j : SM.ScalarCoordinate n // j ≠ leg.moving} => leg.assignment W r j) ∈
      SM.coordinateSlopeDomain leg.moving (SM.namedControlPolynomial name) := by
    simpa only [hfixed, SM.coordinateSlopeDomain, Set.mem_setOf_eq] using hs
  have hz := SM.coordinate_zero_set_eq_graph leg.moving (SM.namedControlPolynomial name)
    (SM.namedControlPolynomial_affine name _)
  refine ⟨SM.isOpen_coordinateSlopeDomain _ _, hs,
    SM.contDiffOn_coordinate_graph _ _, SM.coordinate_graph_injective _ _,
    SM.contDiff_remaining_projection _, SM.coordinate_graph_projection _ _,
    SM.isOpen_coordinate_graph_ambient_domain _ _, heta, hz, ?_⟩
  rw [← hz]
  exact ⟨heta, hr⟩

-- The remaining-coordinate projection is also a right inverse on every
-- actual ambient zero in the slope neighborhood, not merely a left inverse.
example {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (i : sigma) (p : MvPolynomial sigma ℝ) (hp : p.degreeOf i ≤ 1)
    (rho : sigma → ℝ)
    (hdom : (fun j : {j : sigma // j ≠ i} => rho j) ∈ SM.coordinateSlopeDomain i p)
    (hz : eval rho p = 0) :
    SM.extendCoordinateAssignment i (fun j => rho j)
      (SM.coordinateRootFunction i p (fun j => rho j)) = rho := by
  have he := (SM.coordinate_graph_actual_assignment i p hp rho hdom).mp hz
  rw [← he, SM.extendCoordinateAssignment_reconstruct]
