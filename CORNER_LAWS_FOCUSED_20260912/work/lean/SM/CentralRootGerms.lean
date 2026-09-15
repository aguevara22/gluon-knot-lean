import SM.CentralRootNeighborhoods
import SM.CentralLegCollision
import SM.GermSignChange
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Actual centred wall germs at nongeneric roots of central coordinate legs.
The radius and punctured Generic property are constructed from joint conditions;
the extra nongeneric-centre premise selects actual wall events among all roots.
No named wall classification or ambient hypersurface theorem is claimed here. -/

namespace SM

open MvPolynomial Set

noncomputable section

variable {κ : Type*} {n : ℕ}

structure CentralRootPatch (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (name : PolynomialControlName n) (r : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le_left : radius ≤ r
  radius_le_right : radius ≤ 1 - r
  root : eval (leg.assignment W r) (namedControlPolynomial name) = 0
  other_products : ∀ t : ℝ, |t - r| < radius → ∀ other : PolynomialControlName n,
    other ≠ name → 0 < eval (leg.assignment W t) (namedControlPolynomial other) *
      eval (leg.assignment W r) (namedControlPolynomial other)
  generic_punctured : ∀ t : ℝ, |t - r| < radius → t ≠ r →
    Generic (tupleOfScalarCoordinates (leg.assignment W t))

theorem nonempty_centralRootPatch (hn : 3 ≤ n)
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) (r : ℝ) (hrange : r ∈ Ioo (0 : ℝ) 1)
    (hr : eval (leg.assignment W r) (namedControlPolynomial name) = 0) :
    Nonempty (CentralRootPatch leg W name r) := by
  obtain ⟨ε, hε, hleft, hright, hother, hgeneric⟩ :=
    central_root_neighborhood hn leg W h name r hrange hr
  exact ⟨⟨ε, hε, hleft, hright, hr, hother, hgeneric⟩⟩

def chooseCentralRootPatch (hn : 3 ≤ n)
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (name : PolynomialControlName n) (r : ℝ) (hrange : r ∈ Ioo (0 : ℝ) 1)
    (hr : eval (leg.assignment W r) (namedControlPolynomial name) = 0) :
    CentralRootPatch leg W name r :=
  Classical.choice (nonempty_centralRootPatch hn leg W h name r hrange hr)

namespace CentralRootPatch

variable {leg : CoordinateWaypointLeg κ (ScalarCoordinate n)}
  {W : κ × ScalarCoordinate n → ℝ} {name : PolynomialControlName n} {r : ℝ}
  (patch : CentralRootPatch leg W name r)

theorem time_mem_leg (t : ℝ) (ht : t ∈ Ioo (-patch.radius) patch.radius) :
    r + t ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · linarith [patch.radius_le_left, ht.1]
  · linarith [patch.radius_le_right, ht.2]

def toWallGerm (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r))) :
    WallGerm n where
  radius := patch.radius
  radius_pos := patch.radius_pos
  curve := fun t => tupleOfScalarCoordinates (leg.assignment W (r + t.val))
  continuous_curve := (continuous_central_tuple_leg leg W).comp
    (continuous_const.add continuous_subtype_val)
  generic_punctured := by
    intro t ht
    apply patch.generic_punctured (r + t.val)
    · simpa only [add_sub_cancel_left] using abs_lt.mpr t.property
    · intro he
      apply ht
      linarith
  nongeneric_center := by simpa only [add_zero] using hng

@[simp] theorem toWallGerm_center
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r))) :
    (patch.toWallGerm hng).center = tupleOfScalarCoordinates (leg.assignment W r) := by
  simp only [WallGerm.center, WallGerm.zeroParameter, toWallGerm, add_zero]

theorem toWallGerm_curve_eq
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r)))
    (t : (patch.toWallGerm hng).Parameter) :
    (patch.toWallGerm hng).curve t =
      tupleOfScalarCoordinates (leg.assignment W (r + t.val)) := rfl

theorem toWallGerm_curve_collision_free
    (h : JointLegConditions leg W)
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r)))
    (t : (patch.toWallGerm hng).Parameter) :
    Function.Injective ((patch.toWallGerm hng).curve t) :=
  central_leg_collision_free leg W h (r + t.val)

theorem toWallGerm_other_products
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r)))
    (t : (patch.toWallGerm hng).Parameter)
    (other : PolynomialControlName n) (hne : other ≠ name) :
    0 < eval (scalarCoordinates ((patch.toWallGerm hng).curve t))
        (namedControlPolynomial other) *
      eval (scalarCoordinates (patch.toWallGerm hng).center)
        (namedControlPolynomial other) := by
  rw [patch.toWallGerm_curve_eq, patch.toWallGerm_center]
  simp only [scalarCoordinates_tupleOf]
  apply patch.other_products (r + t.val) _ other hne
  simpa only [add_sub_cancel_left, toWallGerm] using abs_lt.mpr t.property

include patch in

theorem parameter_isRoot :
    (leg.parameterPolynomial W (namedControlPolynomial name)).IsRoot r := by
  change (leg.parameterPolynomial W (namedControlPolynomial name)).eval r = 0
  rw [leg.parameterPolynomial_eval W _ (namedControlPolynomial_affine name _)]
  exact patch.root

theorem toWallGerm_control_signChanges (h : JointLegConditions leg W)
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r))) :
    (patch.toWallGerm hng).SignChanges
      (fun P => eval (scalarCoordinates P) (namedControlPolynomial name)) := by
  refine ⟨patch.radius, patch.radius_pos, le_rfl, ?_⟩
  intro t _
  have hp := central_control_crossing_product leg W h name r (r - t.val) (r + t.val)
    patch.parameter_isRoot (by linarith [t.property.1]) (by linarith [t.property.1])
  change eval (scalarCoordinates (tupleOfScalarCoordinates (leg.assignment W (r + t.val))))
      (namedControlPolynomial name) *
    eval (scalarCoordinates (tupleOfScalarCoordinates (leg.assignment W (r + -t.val))))
      (namedControlPolynomial name) < 0
  simpa only [scalarCoordinates_tupleOf, sub_eq_add_neg, mul_comm] using hp

include patch in
theorem parameterSlope_ne_zero (h : JointLegConditions leg W) :
    leg.parameterSlope W (namedControlPolynomial name) ≠ 0 :=
  central_parameterSlope_ne_zero leg W h name
    (central_root_forces_dependency leg W h name r patch.parameter_isRoot)

theorem centered_control_hasDerivAt :
    HasDerivAt (fun t : ℝ => eval (leg.assignment W (r + t)) (namedControlPolynomial name))
      (leg.parameterSlope W (namedControlPolynomial name)) 0 := by
  have ht : HasDerivAt (fun t : ℝ => r + t) 1 0 := by
    exact (hasDerivAt_id' (0 : ℝ)).const_add r
  have hc := (central_control_hasDerivAt leg W name (r + 0)).comp 0 ht
  simpa only [mul_one, Function.comp_def] using hc

end CentralRootPatch

/-- Every actual nongeneric interior parameter supplies a centred, collision-free
wall germ. Its unique vanishing name and nonzero derivative are obtained from the
actual joint conditions, not supplied as additional transversality premises. -/
theorem central_nongeneric_has_wallGerm (hn : 3 ≤ n)
    (leg : CoordinateWaypointLeg κ (ScalarCoordinate n))
    (W : κ × ScalarCoordinate n → ℝ) (h : JointLegConditions leg W)
    (r : ℝ) (hrange : r ∈ Ioo (0 : ℝ) 1)
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r))) :
    ∃ name : PolynomialControlName n, ∃ g : WallGerm n,
      g.center = tupleOfScalarCoordinates (leg.assignment W r) ∧
      (∀ t : g.Parameter, g.curve t = tupleOfScalarCoordinates (leg.assignment W (r + t.val))) ∧
      (∀ t : g.Parameter, r + t.val ∈ Ioo (0 : ℝ) 1) ∧
      (∀ t : g.Parameter, Function.Injective (g.curve t)) ∧
      g.SignChanges (fun P => eval (scalarCoordinates P) (namedControlPolynomial name)) ∧
      (∀ t : g.Parameter, ∀ other : PolynomialControlName n, other ≠ name →
        0 < eval (scalarCoordinates (g.curve t)) (namedControlPolynomial other) *
          eval (scalarCoordinates g.center) (namedControlPolynomial other)) ∧
      (∃ d : ℝ, d ≠ 0 ∧ HasDerivAt
        (fun s : ℝ => eval (leg.assignment W (r + s)) (namedControlPolynomial name)) d 0) := by
  obtain ⟨name, hr⟩ := central_nongeneric_subset_roots hn leg W hng
  let patch := chooseCentralRootPatch hn leg W h name r hrange hr
  refine ⟨name, patch.toWallGerm hng, patch.toWallGerm_center hng,
    patch.toWallGerm_curve_eq hng, ?_, patch.toWallGerm_curve_collision_free h hng,
    patch.toWallGerm_control_signChanges h hng, patch.toWallGerm_other_products hng,
    leg.parameterSlope W (namedControlPolynomial name), patch.parameterSlope_ne_zero h, ?_⟩
  · intro t
    exact patch.time_mem_leg t.val t.property
  · exact CentralRootPatch.centered_control_hasDerivAt

end

end SM
