import SM.CentralLegRootControls
import SM.NonzeroControlsGeneric

/-! Finite isolated root sets of actual central-leg controls, with the leg and
control labels retained. Nongeneric parameters are contained in these root sets;
the converse is not asserted because inactive concurrence roots may be generic. -/

namespace SM

open MvPolynomial Set

noncomputable section

variable {κ : Type*} {n : ℕ}

def centralControlRootSet (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) : Set ℝ :=
  {t | ∃ name : PolynomialControlName n, eval (leg.assignment W t) (namedControlPolynomial name) = 0}

theorem finite_centralControlRootSet [NeZero n]
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W) :
    (centralControlRootSet leg W).Finite := by
  have he : centralControlRootSet leg W = ⋃ name : PolynomialControlName n,
      {t : ℝ | (leg.parameterPolynomial W (namedControlPolynomial name)).IsRoot t} := by
    ext t
    simp only [centralControlRootSet, mem_setOf_eq, mem_iUnion]
    apply exists_congr
    intro name
    change eval (leg.assignment W t) (namedControlPolynomial name) = 0 ↔
      (leg.parameterPolynomial W (namedControlPolynomial name)).eval t = 0
    rw [leg.parameterPolynomial_eval W _ (namedControlPolynomial_affine name _)]
  rw [he]
  exact Set.finite_iUnion fun name => Polynomial.finite_setOfPred_isRoot
    (central_parameterPolynomial_ne_zero leg W h name)

def labelledCentralRootSet {ι : Type*}
    (legs : ι → CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) : Set (ι × ℝ) :=
  {it | it.2 ∈ centralControlRootSet (legs it.1) W}

theorem finite_labelledCentralRootSet [NeZero n] {ι : Type*} [Finite ι]
    (legs : ι → CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : ∀ i, JointLegConditions (legs i) W) :
    (labelledCentralRootSet legs W).Finite := by
  have hf : (⋃ i : ι, Prod.mk i '' centralControlRootSet (legs i) W).Finite :=
    Set.finite_iUnion fun i => (finite_centralControlRootSet (legs i) W (h i)).image (Prod.mk i)
  apply hf.subset
  rintro ⟨i, t⟩ ht
  exact mem_iUnion.mpr ⟨i, ⟨t, ht, rfl⟩⟩

theorem central_root_unique_name (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (r : ℝ) (hr : r ∈ centralControlRootSet leg W) :
    ∃! name : PolynomialControlName n, eval (leg.assignment W r) (namedControlPolynomial name) = 0 := by
  obtain ⟨name, hn⟩ := hr
  refine ⟨name, hn, ?_⟩
  intro other ho
  by_contra hne
  apply central_parameter_no_common_root leg W h other name hne r
  constructor
  · change (leg.parameterPolynomial W (namedControlPolynomial other)).eval r = 0
    rw [leg.parameterPolynomial_eval W _ (namedControlPolynomial_affine other _)]
    exact ho
  · change (leg.parameterPolynomial W (namedControlPolynomial name)).eval r = 0
    rw [leg.parameterPolynomial_eval W _ (namedControlPolynomial_affine name _)]
    exact hn

theorem finite_real_set_isolated (S : Set ℝ) (hS : S.Finite) (r : ℝ) :
    ∃ ε > 0, ∀ t ∈ S, |t - r| < ε → t = r := by
  have hc : IsClosed (S \ {r}) := (hS.subset (Set.diff_subset)).isClosed
  have hr : r ∈ (S \ {r})ᶜ := by simp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hc.isOpen_compl r hr
  refine ⟨ε, hε, ?_⟩
  intro t ht hd
  by_contra htr
  have hm : t ∈ Metric.ball r ε := by simpa only [Metric.mem_ball, Real.dist_eq] using hd
  exact hball hm ⟨ht, by simpa using htr⟩

theorem central_roots_isolated [NeZero n]
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W) (r : ℝ) :
    ∃ ε > 0, ∀ t ∈ centralControlRootSet leg W, |t - r| < ε → t = r :=
  finite_real_set_isolated _ (finite_centralControlRootSet leg W h) r

theorem central_root_zero_excluded (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W) :
    0 ∉ centralControlRootSet leg W := by
  rintro ⟨name, hz⟩
  rw [leg.assignment_zero] at hz
  exact h.endpoint_controls false name hz

theorem central_root_one_excluded (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W) :
    1 ∉ centralControlRootSet leg W := by
  rintro ⟨name, hz⟩
  rw [leg.assignment_one] at hz
  exact h.endpoint_controls true name hz

theorem central_generic_of_not_root (hn : 3 ≤ n)
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (t : ℝ) (ht : t ∉ centralControlRootSet leg W) :
    Generic (tupleOfScalarCoordinates (leg.assignment W t)) := by
  apply generic_of_named_controls_nonzero hn
  intro name hz
  apply ht
  refine ⟨name, ?_⟩
  simpa only [scalarCoordinates_tupleOf] using hz

theorem central_nongeneric_subset_roots (hn : 3 ≤ n)
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n)) (W : κ × ScalarCoordinate n → ℝ) :
    {t : ℝ | ¬ Generic (tupleOfScalarCoordinates (leg.assignment W t))} ⊆
      centralControlRootSet leg W := by
  intro t ht
  by_contra hr
  exact ht (central_generic_of_not_root hn leg W t hr)

theorem finite_central_nongeneric [NeZero n] (hn : 3 ≤ n)
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W) :
    {t : ℝ | ¬ Generic (tupleOfScalarCoordinates (leg.assignment W t))}.Finite :=
  (finite_centralControlRootSet leg W h).subset (central_nongeneric_subset_roots hn leg W)

end

end SM
