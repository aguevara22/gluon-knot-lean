namespace SM

open Set

noncomputable section

variable {n : ℕ} [NeZero n]

theorem WallGerm.isolates_shifted_path (g : WallGerm n)
    (p : unitInterval → LabelledTuple n) (t : unitInterval)
    (hcurve : ∀ s : g.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
      g.curve s = p ⟨(t : ℝ) + s.val, hs⟩) :
    ∃ ε > 0, ∀ u : unitInterval, u ≠ t → |(u : ℝ) - (t : ℝ)| < ε → Generic (p u) := by
  refine ⟨g.radius, g.radius_pos, ?_⟩
  intro u hne hu
  let s : g.Parameter := ⟨(u : ℝ) - (t : ℝ), abs_lt.mp hu⟩
  have hsne : s.val ≠ 0 := sub_ne_zero.mpr (fun he => hne (Subtype.ext he))
  have hg := g.generic_punctured s hsne
  obtain ⟨hs, he⟩ := hcurve s
  have htu : (⟨(t : ℝ) + s.val, hs⟩ : unitInterval) = u := by
    apply Subtype.ext
    dsimp [s]
    ring
  rw [he, htu] at hg
  exact hg

/-- The source conclusion as explicit properties of one actual labelled path.
The uniform cells form a genuine finite partition; the affine formulas are in
the actual occurrence scalar coordinates. No cube, waypoint, control or wall
existence hypothesis is hidden in this structure. -/
structure RelativeGeneralPositionPath (γ : unitInterval → LabelledTuple n) (δ : ℝ) where
  path : unitInterval → LabelledTuple n
  continuous : Continuous path
  first : path 0 = γ 0
  last : path 1 = γ 1
  regular : ∀ t, Regular (path t)
  close : ∀ t, dist (tupleCoordinates (path t)) (tupleCoordinates (γ t)) < δ
  collision_free : ∀ t, Function.Injective (path t)
  edges_nonzero : ∀ t i, edge (path t) i ≠ 0
  cellCount : ℕ
  cellCount_pos : 0 < cellCount
  cell_cover : ∀ t, ∃ k : Fin cellCount, t ∈ uniformMeshCell cellCount cellCount_pos k
  affine_on_cells : ∀ k : Fin cellCount, ∃ a b : ScalarCoordinate n → ℝ,
    ∀ t ∈ uniformMeshCell cellCount cellCount_pos k,
      scalarCoordinates (path t) = fun z => a z + (t : ℝ) * b z
  generic_endpoint_collar : ∃ ε > 0, ∀ t : unitInterval,
    ((t : ℝ) < ε ∨ 1 - ε < (t : ℝ)) → Generic (path t)
  finite_nongeneric : {t : unitInterval | ¬ Generic (path t)}.Finite
  event : ∀ t, ¬ Generic (path t) → ∃ g : WallGerm n,
    g.center = path t ∧
    (∀ s : g.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
      g.curve s = path ⟨(t : ℝ) + s.val, hs⟩) ∧
    g.Simple ∧ ∃! kind : RegularWallKind, g.HasRegularWallKind kind
  isolated : ∀ t, ¬ Generic (path t) → ∃ ε > 0,
    ∀ u : unitInterval, u ≠ t → |(u : ℝ) - (t : ℝ)| < ε → Generic (path u)
  no_cusp : ∀ t (g : WallGerm n), g.center = path t → ∀ j, ¬ g.CuspAt j

/-- Strong construction retaining the same actual fine-cell/control/derivative/
smooth-graph certificate for every classified nongeneric event. -/
theorem relative_general_position_with_certificates (hn : 3 ≤ n)
    (γ : unitInterval → LabelledTuple n) (hγ : Continuous γ)
    (hregular : ∀ t, Regular (γ t)) (hfirst : Generic (γ 0)) (hlast : Generic (γ 1))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ d : CurveCubeSubdivision γ δ,
      ∃ W : d.InternalWaypoint × ScalarCoordinate n → ℝ,
        ∃ A : d.CubeCoordinateApproximation W,
          (∀ t, Function.Injective (A.path t)) ∧
          {t : unitInterval | ¬ Generic (A.path t)}.Finite ∧
          ∀ t, ¬ Generic (A.path t) →
            ∃ E : CurveCubeSubdivision.TimedEventCertificate A hn t,
              (∃! kind : RegularWallKind, E.germ.HasRegularWallKind kind) ∧
              ∀ j, ¬ E.germ.CuspAt j := by
  let d := chooseCurveCubeSubdivision hn γ hγ hregular hfirst hlast δ hδ
  obtain ⟨W, A, hJ, hcollision, hfinite⟩ := d.exists_joint_cubeCoordinateApproximation hn
  refine ⟨d, W, A, hcollision, hfinite, ?_⟩
  intro t hng
  obtain ⟨E⟩ := A.nonempty_timedEventCertificate hn hJ t hng
  exact ⟨E, E.regular_kind_unique⟩

/-- SM thm:relgp: relative general position, all six noncusp wall alternatives,
uniqueness of the kind, and retention of every labelled occurrence. -/
theorem relative_general_position (hn : 3 ≤ n)
    (γ : unitInterval → LabelledTuple n) (hγ : Continuous γ)
    (hregular : ∀ t, Regular (γ t)) (hfirst : Generic (γ 0)) (hlast : Generic (γ 1))
    (δ : ℝ) (hδ : 0 < δ) : Nonempty (RelativeGeneralPositionPath γ δ) := by
  obtain ⟨d, W, A, hcollision, hfinite, hE⟩ :=
    relative_general_position_with_certificates hn γ hγ hregular hfirst hlast δ hδ
  have hm : 0 < 2 * n := by omega
  have hN := Nat.mul_pos d.count_pos hm
  refine ⟨{
    path := A.path
    continuous := A.continuous
    first := A.first
    last := A.last
    regular := A.regular
    close := A.close
    collision_free := hcollision
    edges_nonzero := fun t i => (A.regular t i).2.1
    cellCount := d.count * (2 * n)
    cellCount_pos := hN
    cell_cover := fun t => exists_uniformMeshCell _ hN t
    affine_on_cells := A.affine_on_cells
    generic_endpoint_collar := A.generic_endpoint_collar
    finite_nongeneric := hfinite
    event := ?_
    isolated := ?_
    no_cusp := ?_ }⟩
  · intro t hng
    obtain ⟨E, hk, _⟩ := hE t hng
    exact ⟨E.germ, E.germ_center, E.curve_on_path, E.simple, hk⟩
  · intro t hng
    obtain ⟨E, _, _⟩ := hE t hng
    exact E.germ.isolates_shifted_path A.path t E.curve_on_path
  · intro t g he j
    apply g.not_cuspAt_of_regular
    rw [he]
    exact A.regular t

end

end SM
