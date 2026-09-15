import SM.FlatSpatial
import SM.GermChiStability
import SM.NamedWallPredicates

/-! The F geometric clause of named-wall sides, at every source size N>=4.
All central and nearby records come from the actual segment geometry. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

def FlatWallSidesData (g : WallGerm n) (j : ZMod n) (h : g.FlatAt j) : Prop :=
  Regular g.center ∧
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ →
    ChirotopesOutsideZerosAgree g.center (g.curve t) ∧
    CrossingParameterOrderAgrees g.center (g.curve t) ∧
    GeometricRecordsAgree (flat_crossingGeometry h.1 h.2.1 h.2.2.2.1 h.2.2.1)
      (flat_germ_crossingGeometry h.1 g h.2.1 h.2.2.2.1 h.2.2.1 t)

theorem flat_wall_sides (g : WallGerm n) {j : ZMod n} (h : g.FlatAt j) :
    FlatWallSidesData g j h := by
  have hg := flat_crossingGeometry h.1 h.2.1 h.2.2.2.1 h.2.2.1
  refine ⟨(flat_center_geometry h.1 h.2.1 h.2.2.2.1).2.2.1, ?_⟩
  apply (g.eventually_center_iff_radius _).mp
  have hchi := g.continuous_curve.continuousAt.eventually (outsideZeros_chi_persists g.center)
  have horder := g.continuous_curve.continuousAt.eventually (geometric_parameter_order_persists hg)
  have hrecords := g.continuous_curve.continuousAt.eventually (geometric_records_persist hg)
  filter_upwards [hchi, horder, hrecords] with t hct hot hrt
  exact ⟨hct, hot, hrt (flat_germ_crossingGeometry h.1 g h.2.1 h.2.2.2.1 h.2.2.1 t)⟩

end SM
