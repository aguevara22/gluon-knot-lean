open Set MvPolynomial
open scoped ContDiff
namespace RelgpIndependentReview

-- No NeZero hypothesis, no supplied approximation, root, slope or wall data.
theorem raw_source {n : ℕ} (hn : 3 ≤ n)
    (γ : unitInterval → SM.LabelledTuple n) (hγ : Continuous γ)
    (hreg : ∀ t, SM.Regular (γ t)) (h0 : SM.Generic (γ 0)) (h1 : SM.Generic (γ 1))
    (δ : ℝ) (hδ : 0 < δ) :
    letI : NeZero n := ⟨by omega⟩
    Nonempty (SM.RelativeGeneralPositionPath γ δ) := by
  letI : NeZero n := ⟨by omega⟩
  exact SM.relative_general_position hn γ hγ hreg h0 h1 δ hδ

-- Every actual physical labelled vertex has an affine plane formula on the
-- same genuine strict finite partition, with exact original labelled endpoints.
theorem actual_labelled_piecewise_affinity {n : ℕ} [NeZero n]
    {γ : unitInterval → SM.LabelledTuple n} {δ : ℝ}
    (P : SM.RelativeGeneralPositionPath γ δ) :
    (∀ i, P.path 0 i = γ 0 i ∧ P.path 1 i = γ 1 i) ∧
    StrictMono (SM.uniformMeshPoint P.cellCount P.cellCount_pos) ∧
    (⋃ k : Fin P.cellCount, SM.uniformMeshCell P.cellCount P.cellCount_pos k) = univ ∧
    ∀ k : Fin P.cellCount, ∃ a b : SM.LabelledTuple n,
      ∀ t ∈ SM.uniformMeshCell P.cellCount P.cellCount_pos k,
        ∀ i, P.path t i = a i + (t : ℝ) • b i := by
  refine ⟨fun i => ⟨congrFun P.first i, congrFun P.last i⟩,
    SM.uniformMeshPoint_strictMono _ _, SM.iUnion_uniformMeshCell _ _, ?_⟩
  intro k
  obtain ⟨a, b, hab⟩ := P.affine_on_cells k
  refine ⟨SM.tupleOfScalarCoordinates a, SM.tupleOfScalarCoordinates b, ?_⟩
  intro t ht i
  have h := congrArg SM.tupleOfScalarCoordinates (hab t ht)
  rw [SM.tupleOf_scalarCoordinates] at h
  have hi := congrFun h i
  exact hi

-- Pointwise strict closeness is genuinely uniform: compactness yields a
-- single upper bound smaller than delta, using the two actual continuous paths.
theorem uniform_margin {n : ℕ} [NeZero n]
    {γ : unitInterval → SM.LabelledTuple n} {δ : ℝ}
    (hγ : Continuous γ) (P : SM.RelativeGeneralPositionPath γ δ) :
    ∃ m : ℝ, m < δ ∧ ∀ t,
      dist (SM.tupleCoordinates (P.path t)) (SM.tupleCoordinates (γ t)) ≤ m := by
  let f := fun t => dist (SM.tupleCoordinates (P.path t)) (SM.tupleCoordinates (γ t))
  have hf : Continuous f := (SM.continuous_tupleCoordinates.comp P.continuous).dist
    (SM.continuous_tupleCoordinates.comp hγ)
  obtain ⟨t, _, ht⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set unitInterval).Nonempty) hf.continuousOn
  exact ⟨f t, P.close t, fun u => ht (Set.mem_univ u)⟩

-- The output record alone supplies finite actual events, exact shifted germs,
-- isolation, six-way uniqueness and absence of every possible centred cusp.
theorem actual_events {n : ℕ} [NeZero n]
    {γ : unitInterval → SM.LabelledTuple n} {δ : ℝ}
    (P : SM.RelativeGeneralPositionPath γ δ) :
    {t : unitInterval | ¬ SM.Generic (P.path t)}.Finite ∧
    ∀ t, ¬ SM.Generic (P.path t) → ∃ g : SM.WallGerm n,
      g.center = P.path t ∧
      (∀ s : g.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
        g.curve s = P.path ⟨(t : ℝ) + s.val, hs⟩) ∧
      (∃! k : SM.RegularWallKind, g.HasRegularWallKind k) ∧
      (∀ j, ¬ g.CuspAt j) ∧
      (∃ ε > 0, ∀ u : unitInterval, u ≠ t → |(u : ℝ) - (t : ℝ)| < ε →
        SM.Generic (P.path u)) := by
  refine ⟨P.finite_nongeneric, ?_⟩
  intro t hng
  obtain ⟨g, hc, he, _, hk⟩ := P.event t hng
  exact ⟨g, hc, he, hk, P.no_cusp t g hc, P.isolated t hng⟩

-- Vertex subtype exclusivity must handle distinct proposed occurrence marks.
theorem cross_mark_subtype_exclusion {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (g : SM.WallGerm n) (M a N b : ZMod n) (hb : g.BigonAt M a) :
    ¬ g.SlidingAt N b := by
  intro hs
  exact g.bigon_sliding_marks_incompatible hn ⟨M, a, hb⟩ ⟨N, b, hs⟩

-- ONE approximation and EVERY nongeneric event. The scalar function whose
-- nonzero derivative is proved agrees with the same shifted actual path on
-- the full returned germ; the same event is simultaneously classified.
theorem raw_source_transverse_events {n : ℕ} (hn : 3 ≤ n)
    (γ : unitInterval → SM.LabelledTuple n) (hγ : Continuous γ)
    (hreg : ∀ t, SM.Regular (γ t)) (h0 : SM.Generic (γ 0)) (h1 : SM.Generic (γ 1))
    (δ : ℝ) (hδ : 0 < δ) :
    letI : NeZero n := ⟨by omega⟩
    ∃ d : SM.CurveCubeSubdivision γ δ,
      ∃ W : d.InternalWaypoint × SM.ScalarCoordinate n → ℝ,
        ∃ A : d.CubeCoordinateApproximation W,
          ∀ t, ¬ SM.Generic (A.path t) →
            ∃ E : SM.CurveCubeSubdivision.TimedEventCertificate A hn t,
              (∃! k : SM.RegularWallKind, E.germ.HasRegularWallKind k) ∧
              ∃ F : ℝ → ℝ, ∃ v : ℝ, v ≠ 0 ∧ HasDerivAt F v 0 ∧
                ∀ s : E.germ.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
                  F s.val = eval (SM.scalarCoordinates (A.path ⟨(t : ℝ) + s.val, hs⟩))
                    (SM.namedControlPolynomial E.control) := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨d, W, A, _, _, hE⟩ :=
    SM.relative_general_position_with_certificates hn γ hγ hreg h0 h1 δ hδ
  refine ⟨d, W, A, ?_⟩
  intro t hng
  obtain ⟨E, hk, _⟩ := hE t hng
  let leg := SM.CurveCubeSubdivision.indexedCentralLeg hn E.index E.central
  refine ⟨E, hk,
    (fun s => eval (leg.assignment W (SM.uniformMeshLocalTime _ E.index t +
      (d.count * (2 * n) : ℕ) * s)) (SM.namedControlPolynomial E.control)),
    leg.parameterSlope W (SM.namedControlPolynomial E.control) * (d.count * (2 * n) : ℕ),
    E.derivative_ne_zero, E.derivative, ?_⟩
  intro s
  obtain ⟨hs, he⟩ := E.curve_on_path s
  refine ⟨hs, ?_⟩
  rw [← he, E.curve_on_leg, SM.scalarCoordinates_tupleOf]

-- Graph identity at the same classified root uses its actual polynomial;
-- the returned graph has the remaining-coordinate projection as inverse.
theorem event_on_actual_smooth_graph {n : ℕ} [NeZero n]
    {γ : unitInterval → SM.LabelledTuple n} {δ : ℝ}
    {d : SM.CurveCubeSubdivision γ δ}
    {W : d.InternalWaypoint × SM.ScalarCoordinate n → ℝ}
    {A : d.CubeCoordinateApproximation W} {hn : 3 ≤ n} {t : unitInterval}
    (E : SM.CurveCubeSubdivision.TimedEventCertificate A hn t) :
    let leg := SM.CurveCubeSubdivision.indexedCentralLeg hn E.index E.central
    let U := SM.coordinateSlopeDomain leg.moving (SM.namedControlPolynomial E.control)
    let G := fun eta : {j : SM.ScalarCoordinate n // j ≠ leg.moving} → ℝ =>
      SM.extendCoordinateAssignment leg.moving eta
        (SM.coordinateRootFunction leg.moving (SM.namedControlPolynomial E.control) eta)
    IsOpen U ∧ ContDiffOn ℝ ∞ G U ∧ Function.Injective G ∧
      (∀ eta, (fun j : {j : SM.ScalarCoordinate n // j ≠ leg.moving} => G eta j) = eta) ∧
      SM.scalarCoordinates E.germ.center ∈ G '' U := by
  dsimp only
  refine ⟨SM.isOpen_coordinateSlopeDomain _ _, SM.contDiffOn_coordinate_graph _ _,
    SM.coordinate_graph_injective _ _, SM.coordinate_graph_projection _ _, ?_⟩
  rw [← SM.coordinate_zero_set_eq_graph _ _ (SM.namedControlPolynomial_affine E.control _)]
  refine ⟨E.point_graph_domain, ?_⟩
  rw [E.germ_center]
  exact E.root

end RelgpIndependentReview
