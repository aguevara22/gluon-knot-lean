namespace SM.CurveCubeSubdivision

open Set MvPolynomial
open scoped ContDiff

noncomputable section

variable {n : ℕ} [NeZero n] {γ : unitInterval → LabelledTuple n} {δ : ℝ}
  {d : CurveCubeSubdivision γ δ} {W : d.InternalWaypoint × ScalarCoordinate n → ℝ}

abbrev indexedCentralLeg (hn : 3 ≤ n) (k : Fin (d.count * (2 * n)))
    (hc : 0 < k.divNat.val ∧ k.divNat.val + 1 < d.count) :=
  d.centralLeg hn (⟨k.divNat, hc⟩, k.modNat)

/- The incidence and leg equalities are explicit fields: later classification
must use the same occurrence, control and actual path as the graph and derivative. -/
structure TimedEventCertificate (A : d.CubeCoordinateApproximation W)
    (hn : 3 ≤ n) (t : unitInterval) where
  index : Fin (d.count * (2 * n))
  central : 0 < index.divNat.val ∧ index.divNat.val + 1 < d.count
  control : PolynomialControlName n
  germ : WallGerm n
  time_in_cell : t ∈ uniformMeshCell _ (Nat.mul_pos d.count_pos (by omega)) index
  localTime_interior : uniformMeshLocalTime _ index t ∈ Ioo (0 : ℝ) 1
  root : eval (scalarCoordinates (A.path t)) (namedControlPolynomial control) = 0
  germ_center : germ.center = A.path t
  central_center : scalarCoordinates germ.center =
    (indexedCentralLeg hn index central).assignment W (uniformMeshLocalTime _ index t)
  curve_on_leg : ∀ s : germ.Parameter, germ.curve s = tupleOfScalarCoordinates
    ((indexedCentralLeg hn index central).assignment W
      (uniformMeshLocalTime _ index t + (d.count * (2 * n) : ℕ) * s.val))
  curve_on_path : ∀ s : germ.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
    germ.curve s = A.path ⟨(t : ℝ) + s.val, hs⟩
  other_controls : ∀ other : PolynomialControlName n, other ≠ control →
    eval (scalarCoordinates germ.center) (namedControlPolynomial other) ≠ 0
  signChanges : germ.SignChanges (fun P => eval (scalarCoordinates P) (namedControlPolynomial control))
  nonzero_slope : eval ((indexedCentralLeg hn index central).fixedAssignment W)
    (coordinateSlope (indexedCentralLeg hn index central).moving (namedControlPolynomial control)) ≠ 0
  derivative : HasDerivAt (fun s : ℝ => eval
    ((indexedCentralLeg hn index central).assignment W
      (uniformMeshLocalTime _ index t + (d.count * (2 * n) : ℕ) * s))
    (namedControlPolynomial control))
    ((indexedCentralLeg hn index central).parameterSlope W (namedControlPolynomial control) *
      (d.count * (2 * n) : ℕ)) 0
  derivative_ne_zero :
    (indexedCentralLeg hn index central).parameterSlope W (namedControlPolynomial control) *
      (d.count * (2 * n) : ℕ) ≠ 0
  smooth_graph : ContDiffOn ℝ ∞
    (coordinateRootFunction (indexedCentralLeg hn index central).moving (namedControlPolynomial control))
    (coordinateSlopeDomain (indexedCentralLeg hn index central).moving (namedControlPolynomial control))
  graph_identity : ∀ ρ : ScalarCoordinate n → ℝ,
    (fun j : {j : ScalarCoordinate n // j ≠ (indexedCentralLeg hn index central).moving} => ρ j) ∈
      coordinateSlopeDomain (indexedCentralLeg hn index central).moving (namedControlPolynomial control) →
    (eval ρ (namedControlPolynomial control) = 0 ↔
      ρ (indexedCentralLeg hn index central).moving =
        coordinateRootFunction (indexedCentralLeg hn index central).moving
          (namedControlPolynomial control) (fun j => ρ j))
  point_graph_domain :
    (fun j : {j : ScalarCoordinate n // j ≠ (indexedCentralLeg hn index central).moving} =>
      scalarCoordinates germ.center j) ∈
        coordinateSlopeDomain (indexedCentralLeg hn index central).moving (namedControlPolynomial control)

namespace CubeCoordinateApproximation

variable (A : d.CubeCoordinateApproximation W)

theorem nonempty_timedEventCertificate (hn : 3 ≤ n)
    (hJ : ∀ j, JointLegConditions (d.centralLeg hn j) W)
    (t : unitInterval) (hng : ¬ Generic (A.path t)) :
    Nonempty (TimedEventCertificate A hn t) := by
  have hm : 0 < 2 * n := by omega
  let hNM := Nat.mul_pos d.count_pos hm
  let a : ℝ := (d.count * (2 * n) : ℕ)
  have ha : 0 < a := Nat.cast_pos.mpr hNM
  obtain ⟨k, ht⟩ := exists_uniformMeshCell _ hNM t
  obtain ⟨hc, hrange, hr⟩ := A.nongeneric_central_time hn hJ k t ht hng
  let leg := indexedCentralLeg hn k hc
  let r := uniformMeshLocalTime _ k t
  obtain ⟨name, hroot⟩ := hr
  have hleg : JointLegConditions leg W := hJ _
  let patch := chooseCentralRootPatch hn leg W hleg name r hrange hroot
  have hng' : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r)) := by
    rw [← A.central_branch hn k hc t ht]
    exact hng
  let g := patch.scaledToWallGerm a ha hng'
  have hcenter : g.center = tupleOfScalarCoordinates (leg.assignment W r) :=
    patch.scaledToWallGerm_center a ha hng'
  have hscalar : scalarCoordinates g.center = leg.assignment W r := by
    rw [hcenter, scalarCoordinates_tupleOf]
  have hcurve : ∀ s : g.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
      g.curve s = A.path ⟨(t : ℝ) + s.val, hs⟩ := by
    intro s
    have hloc := patch.scaled_time_mem_leg a ha hng' s
    have hs := uniformMesh_shift_mem_unit _ hNM k t s.val hloc
    let u : unitInterval := ⟨(t : ℝ) + s.val, hs⟩
    have he : uniformMeshLocalTime _ k u = r + a * s.val := by
      dsimp [uniformMeshLocalTime, u, r, a]
      ring
    have hu : u ∈ uniformMeshCell _ hNM k := by
      apply (uniformMeshLocalTime_mem_unit_iff _ hNM k u).mp
      rw [he]
      exact ⟨hloc.1.le, hloc.2.le⟩
    refine ⟨hs, ?_⟩
    change tupleOfScalarCoordinates (leg.assignment W (r + a * s.val)) = A.path u
    rw [A.central_branch hn k hc u hu, he]
  have hslope : eval (leg.fixedAssignment W) (coordinateSlope leg.moving (namedControlPolynomial name)) ≠ 0 :=
    hleg.dependent_slopes name (central_root_forces_dependency leg W hleg name r patch.parameter_isRoot)
  refine ⟨{
    index := k
    central := hc
    control := name
    germ := g
    time_in_cell := ht
    localTime_interior := hrange
    root := ?_
    germ_center := hcenter.trans (A.central_branch hn k hc t ht).symm
    central_center := hscalar
    curve_on_leg := fun _ => rfl
    curve_on_path := hcurve
    other_controls := ?_
    signChanges := patch.scaledToWallGerm_signChanges a ha hleg hng'
    nonzero_slope := hslope
    derivative := CentralRootPatch.scaled_control_hasDerivAt a
    derivative_ne_zero := mul_ne_zero (patch.parameterSlope_ne_zero hleg) (ne_of_gt ha)
    smooth_graph := contDiffOn_coordinateRootFunction _ _
    graph_identity := fun ρ hρ => coordinate_graph_actual_assignment _ _
      (namedControlPolynomial_affine name _) ρ hρ
    point_graph_domain := ?_ }⟩
  · rw [A.central_branch hn k hc t ht, scalarCoordinates_tupleOf]
    exact hroot
  · intro other hne hz
    have hp := patch.other_products r (by simpa only [sub_self, abs_zero] using patch.radius_pos) other hne
    rw [hscalar] at hz
    rw [hz, zero_mul] at hp
    exact (lt_irrefl 0) hp
  · change eval (fun j : {j : ScalarCoordinate n // j ≠ leg.moving} => scalarCoordinates g.center j)
      (coordinateSlope leg.moving (namedControlPolynomial name)) ≠ 0
    rw [hscalar]
    have he : (fun j : {j : ScalarCoordinate n // j ≠ leg.moving} => leg.assignment W r j) =
        leg.fixedAssignment W := by
      funext j
      exact leg.assignment_other W r j
    rwa [he]

end CubeCoordinateApproximation

end

end SM.CurveCubeSubdivision
