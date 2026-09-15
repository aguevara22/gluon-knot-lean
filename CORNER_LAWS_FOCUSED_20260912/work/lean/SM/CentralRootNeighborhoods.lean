import SM.CentralLegFiniteRoots

/-! Common neighbourhoods of actual central-leg roots. One positive radius keeps
all other control values on their original side of zero, excludes other roots,
and stays inside the original leg. Inactive generic roots remain allowed. -/

namespace SM

open MvPolynomial Set Filter Topology

noncomputable section

variable {κ : Type*} {n : ℕ}

theorem central_control_continuous
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (name : PolynomialControlName n) :
    Continuous (fun t => eval (leg.assignment W t) (namedControlPolynomial name)) :=
  continuous_iff_continuousAt.mpr fun t =>
    (central_control_hasDerivAt leg W name t).continuousAt

theorem central_root_other_control_ne_zero
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) (r : ℝ)
    (hr : eval (leg.assignment W r) (namedControlPolynomial name) = 0)
    (other : PolynomialControlName n) (hne : other ≠ name) :
    eval (leg.assignment W r) (namedControlPolynomial other) ≠ 0 := by
  intro ho
  apply central_parameter_no_common_root leg W h other name hne r
  constructor
  · change (leg.parameterPolynomial W (namedControlPolynomial other)).eval r = 0
    rw [leg.parameterPolynomial_eval W _ (namedControlPolynomial_affine other _)]
    exact ho
  · change (leg.parameterPolynomial W (namedControlPolynomial name)).eval r = 0
    rw [leg.parameterPolynomial_eval W _ (namedControlPolynomial_affine name _)]
    exact hr

theorem central_root_other_products_eventually [NeZero n]
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) (r : ℝ)
    (hr : eval (leg.assignment W r) (namedControlPolynomial name) = 0) :
    ∀ᶠ t in 𝓝 r, ∀ other : PolynomialControlName n, other ≠ name →
      0 < eval (leg.assignment W t) (namedControlPolynomial other) *
        eval (leg.assignment W r) (namedControlPolynomial other) := by
  apply eventually_all.mpr
  intro other
  by_cases hne : other ≠ name
  · have hnonzero := central_root_other_control_ne_zero leg W h name r hr other hne
    have hpos : 0 < eval (leg.assignment W r) (namedControlPolynomial other) *
        eval (leg.assignment W r) (namedControlPolynomial other) :=
      mul_self_pos.mpr hnonzero
    have he := ((central_control_continuous leg W other).continuousAt.mul
      continuousAt_const).eventually (isOpen_Ioi.mem_nhds hpos)
    exact he.mono fun _ ht _ => ht
  · exact Eventually.of_forall fun _ ho => (hne ho).elim

theorem central_root_neighborhood (hn : 3 ≤ n)
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) (r : ℝ) (hrange : r ∈ Ioo (0 : ℝ) 1)
    (hr : eval (leg.assignment W r) (namedControlPolynomial name) = 0) :
    ∃ ε > 0, ε ≤ r ∧ ε ≤ 1 - r ∧
      (∀ t : ℝ, |t - r| < ε → ∀ other : PolynomialControlName n, other ≠ name →
        0 < eval (leg.assignment W t) (namedControlPolynomial other) *
          eval (leg.assignment W r) (namedControlPolynomial other)) ∧
      (∀ t : ℝ, |t - r| < ε → t ≠ r →
        Generic (tupleOfScalarCoordinates (leg.assignment W t))) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (central_root_other_products_eventually leg W h name r hr)
  obtain ⟨η, hη, hisolate⟩ := central_roots_isolated leg W h r
  let ε := min δ (min η (min r (1 - r)))
  have hε : 0 < ε := lt_min hδ (lt_min hη (lt_min hrange.1 (sub_pos.mpr hrange.2)))
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεη : ε ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hεr : ε ≤ r :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεone : ε ≤ 1 - r :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, hε, hεr, hεone, ?_, ?_⟩
  · intro t ht
    apply hball
    change dist t r < δ
    rw [Real.dist_eq]
    exact lt_of_lt_of_le ht hεδ
  · intro t ht htr
    apply central_generic_of_not_root hn leg W t
    intro hroot
    exact htr (hisolate t hroot (lt_of_lt_of_le ht hεη))

end

end SM
