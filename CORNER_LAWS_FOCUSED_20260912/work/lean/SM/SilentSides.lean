import SM.SilentCenter
import SM.GermChiStability
import SM.GeometricRecords
import SM.CrossingVertexExclusion

/-! Complete E/C geometric record clauses of lem:wall-sides, including zero.
The full original lemma also requires F/V/T and is not accepted by this module. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

def SilentSidesData (hn : 3 ≤ n) (g : WallGerm n) (h : g.Silent) : Prop :=
  Regular g.center ∧
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ →
    ChirotopesOutsideZerosAgree g.center (g.curve t) ∧
    WeakGeneric (g.curve t) ∧ CrossingGeometry (g.curve t) ∧
    Function.Injective (@crossingPoint n (g.curve t)) ∧
    (∀ c : Crossing (g.curve t), ∀ k, crossingPoint c ≠ g.curve t k) ∧
    CrossingParameterOrderAgrees g.center (g.curve t) ∧
    GeometricRecordsAgree (weak_crossingGeometry (g.silent_center_weak hn h))
      (weak_crossingGeometry (g.silent_curve_weak hn h t))

theorem silent_sides (hn : 3 ≤ n) (g : WallGerm n) (h : g.Silent) :
    SilentSidesData hn g h := by
  have hw0 := g.silent_center_weak hn h
  have hg0 := weak_crossingGeometry hw0
  refine ⟨nonzero_turns_regular hw0.2.1, ?_⟩
  apply (g.eventually_center_iff_radius _).mp
  have hc := g.continuous_curve.continuousAt.eventually (outsideZeros_chi_persists g.center)
  have ho := g.continuous_curve.continuousAt.eventually (geometric_parameter_order_persists hg0)
  have hr := g.continuous_curve.continuousAt.eventually (geometric_records_persist hg0)
  filter_upwards [hc, ho, hr] with t hchi horder hrecords
  have hw := g.silent_curve_weak hn h t
  have hg := weak_crossingGeometry hw
  exact ⟨hchi, hw, hg, crossingPoint_injective_of_geometry hg,
    crossingPoint_ne_vertex_of_geometry hg hw.2.2.1, horder, hrecords hg⟩

end SM
