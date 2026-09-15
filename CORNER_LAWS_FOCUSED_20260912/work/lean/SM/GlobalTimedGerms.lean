import SM.GlobalTimedCollars
import SM.CentralRootGerms

namespace SM

open Set MvPolynomial

noncomputable section

namespace CentralRootPatch

variable {κ : Type*} {n : ℕ}
  {leg : CoordinateWaypointLeg κ (ScalarCoordinate n)}
  {W : κ × ScalarCoordinate n → ℝ} {name : PolynomialControlName n} {r : ℝ}
  (patch : CentralRootPatch leg W name r) (a : ℝ) (ha : 0 < a)

include ha in
theorem scaled_parameter_mem (s : Ioo (-(patch.radius / a)) (patch.radius / a)) :
    a * s.val ∈ Ioo (-patch.radius) patch.radius := by
  have hupper := (lt_div_iff₀ ha).mp s.property.2
  have hlower : -s.val < patch.radius / a := by linarith [s.property.1]
  have hneg := (lt_div_iff₀ ha).mp hlower
  constructor <;> nlinarith

def scaledToWallGerm
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r))) : WallGerm n where
  radius := patch.radius / a
  radius_pos := div_pos patch.radius_pos ha
  curve := fun s => tupleOfScalarCoordinates (leg.assignment W (r + a * s.val))
  continuous_curve := (continuous_central_tuple_leg leg W).comp
    (continuous_const.add (continuous_const.mul continuous_subtype_val))
  generic_punctured := by
    intro s hs
    apply patch.generic_punctured (r + a * s.val)
    · simpa only [add_sub_cancel_left] using abs_lt.mpr (patch.scaled_parameter_mem a ha s)
    · intro he
      apply mul_ne_zero (ne_of_gt ha) hs
      linarith
  nongeneric_center := by simpa only [mul_zero, add_zero] using hng

@[simp] theorem scaledToWallGerm_center
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r))) :
    (patch.scaledToWallGerm a ha hng).center = tupleOfScalarCoordinates (leg.assignment W r) := by
  simp only [WallGerm.center, WallGerm.zeroParameter, scaledToWallGerm, mul_zero, add_zero]

theorem scaled_time_mem_leg
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r)))
    (s : (patch.scaledToWallGerm a ha hng).Parameter) :
    r + a * s.val ∈ Ioo (0 : ℝ) 1 :=
  patch.time_mem_leg _ (patch.scaled_parameter_mem a ha s)

theorem scaledToWallGerm_signChanges (h : JointLegConditions leg W)
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r))) :
    (patch.scaledToWallGerm a ha hng).SignChanges
      (fun P => eval (scalarCoordinates P) (namedControlPolynomial name)) := by
  refine ⟨patch.radius / a, div_pos patch.radius_pos ha, le_rfl, ?_⟩
  intro s _
  have hs : 0 < a * s.val := mul_pos ha s.property.1
  have hp := central_control_crossing_product leg W h name r (r - a * s.val) (r + a * s.val)
    patch.parameter_isRoot (by linarith) (by linarith)
  change eval (scalarCoordinates (tupleOfScalarCoordinates (leg.assignment W (r + a * s.val))))
      (namedControlPolynomial name) *
    eval (scalarCoordinates (tupleOfScalarCoordinates (leg.assignment W (r + a * -s.val))))
      (namedControlPolynomial name) < 0
  simpa only [scalarCoordinates_tupleOf, mul_neg, sub_eq_add_neg, mul_comm] using hp

theorem scaledToWallGerm_other_products
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r)))
    (s : (patch.scaledToWallGerm a ha hng).Parameter)
    (other : PolynomialControlName n) (hne : other ≠ name) :
    0 < eval (scalarCoordinates ((patch.scaledToWallGerm a ha hng).curve s))
        (namedControlPolynomial other) *
      eval (scalarCoordinates (patch.scaledToWallGerm a ha hng).center)
        (namedControlPolynomial other) := by
  rw [patch.scaledToWallGerm_center a ha hng]
  change 0 < eval (scalarCoordinates (tupleOfScalarCoordinates (leg.assignment W (r + a * s.val))))
      (namedControlPolynomial other) *
    eval (scalarCoordinates (tupleOfScalarCoordinates (leg.assignment W r)))
      (namedControlPolynomial other)
  simp only [scalarCoordinates_tupleOf]
  apply patch.other_products _ _ other hne
  simpa only [add_sub_cancel_left] using abs_lt.mpr (patch.scaled_parameter_mem a ha s)

theorem scaled_control_hasDerivAt :
    HasDerivAt (fun s : ℝ => eval (leg.assignment W (r + a * s)) (namedControlPolynomial name))
      (leg.parameterSlope W (namedControlPolynomial name) * a) 0 := by
  have ht : HasDerivAt (fun s : ℝ => r + a * s) a 0 := by
    simpa only [mul_one] using ((hasDerivAt_id' (0 : ℝ)).const_mul a).const_add r
  have hc := (central_control_hasDerivAt leg W name (r + a * 0)).comp 0 ht
  simpa only [Function.comp_def] using hc

end CentralRootPatch

theorem uniformMesh_shift_mem_unit (N : ℕ) (hN : 0 < N) (k : Fin N)
    (t : unitInterval) (s : ℝ)
    (hloc : uniformMeshLocalTime N k t + (N : ℝ) * s ∈ Ioo (0 : ℝ) 1) :
    (t : ℝ) + s ∈ Icc (0 : ℝ) 1 := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hk0 : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
  have hk1 : (k.val : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast k.isLt
  dsimp [uniformMeshLocalTime] at hloc
  have hlo : (0 : ℝ) * (N : ℝ) < ((t : ℝ) + s) * (N : ℝ) := by nlinarith [hloc.1]
  have hhi : ((t : ℝ) + s) * (N : ℝ) < 1 * (N : ℝ) := by nlinarith [hloc.2]
  have hleft : (0 : ℝ) < (t : ℝ) + s :=
    (mul_lt_mul_iff_right₀ hNR).mp (by nlinarith [hlo])
  have hright : (t : ℝ) + s < 1 :=
    (mul_lt_mul_iff_right₀ hNR).mp (by nlinarith [hhi])
  exact ⟨hleft.le, hright.le⟩

namespace CurveCubeSubdivision.CubeCoordinateApproximation

variable {n : ℕ} [NeZero n] {γ : unitInterval → LabelledTuple n} {δ : ℝ}
  {d : CurveCubeSubdivision γ δ} {W : d.InternalWaypoint × ScalarCoordinate n → ℝ}
  (A : d.CubeCoordinateApproximation W)

theorem nongeneric_has_timed_wallGerm (hn : 3 ≤ n)
    (hJ : ∀ j, JointLegConditions (d.centralLeg hn j) W)
    (t : unitInterval) (hng : ¬ Generic (A.path t)) :
    ∃ k : Fin (d.count * (2 * n)),
      ∃ hc : 0 < k.divNat.val ∧ k.divNat.val + 1 < d.count,
        ∃ name : PolynomialControlName n, ∃ g : WallGerm n,
          g.center = A.path t ∧
          (∀ s : g.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
            g.curve s = A.path ⟨(t : ℝ) + s.val, hs⟩) ∧
          (∀ s : g.Parameter, Regular (g.curve s) ∧ Function.Injective (g.curve s)) ∧
          g.SignChanges (fun P => eval (scalarCoordinates P) (namedControlPolynomial name)) ∧
          (∀ s : g.Parameter, ∀ other : PolynomialControlName n, other ≠ name →
            0 < eval (scalarCoordinates (g.curve s)) (namedControlPolynomial other) *
              eval (scalarCoordinates g.center) (namedControlPolynomial other)) ∧
          (∃ slope : ℝ, slope ≠ 0 ∧ HasDerivAt
            (fun s : ℝ => eval
              ((d.centralLeg hn (⟨k.divNat, hc⟩, k.modNat)).assignment W
                (uniformMeshLocalTime _ k t + (d.count * (2 * n) : ℕ) * s))
              (namedControlPolynomial name)) slope 0) := by
  have hm : 0 < 2 * n := by omega
  let hNM := Nat.mul_pos d.count_pos hm
  let a : ℝ := (d.count * (2 * n) : ℕ)
  have ha : 0 < a := Nat.cast_pos.mpr hNM
  obtain ⟨k, ht⟩ := exists_uniformMeshCell _ hNM t
  obtain ⟨hc, hrange, hr⟩ := A.nongeneric_central_time hn hJ k t ht hng
  let leg := d.centralLeg hn (⟨k.divNat, hc⟩, k.modNat)
  let r := uniformMeshLocalTime _ k t
  obtain ⟨name, hroot⟩ := hr
  let patch := chooseCentralRootPatch hn leg W (hJ _) name r hrange hroot
  have hng' : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r)) := by
    rw [← A.central_branch hn k hc t ht]
    exact hng
  let g := patch.scaledToWallGerm a ha hng'
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
  refine ⟨k, hc, name, g, ?_, hcurve, ?_, patch.scaledToWallGerm_signChanges a ha (hJ _) hng',
    patch.scaledToWallGerm_other_products a ha hng', ?_⟩
  · rw [patch.scaledToWallGerm_center a ha hng']
    exact (A.central_branch hn k hc t ht).symm
  · intro s
    obtain ⟨hs, he⟩ := hcurve s
    rw [he]
    exact ⟨A.regular _, A.collision_free hn hJ _⟩
  · refine ⟨leg.parameterSlope W (namedControlPolynomial name) * a,
      mul_ne_zero (patch.parameterSlope_ne_zero (hJ _)) (ne_of_gt ha), ?_⟩
    exact CentralRootPatch.scaled_control_hasDerivAt a

end CurveCubeSubdivision.CubeCoordinateApproximation

end

end SM
