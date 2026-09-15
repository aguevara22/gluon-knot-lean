import SM.TripleVisitExchanges
import SM.GermChiStability

/-! Complete T geometry: all supports persist; exactly the selected actual
visit comparisons reverse; the selected visits are adjacent on one common
punctured interval. No central Generic word is asserted. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

def TripleWallSidesData (hn : 3 ≤ n) (g : WallGerm n) (e f k : ZMod n) : Prop :=
  Regular g.center ∧
  (∀ s t : g.SideParameter, ∃ hs : ∀ c,
    IsCrossing (g.sideTuple true s).val c ↔ IsCrossing (g.sideTuple false t).val c,
      ExactTriangleParameterOrders (g.sideTuple true s).val (g.sideTuple false t).val e f k ∧
      ExactTriangleVisitOrders (g.sideTuple true s).val (g.sideTuple false t).val e f k hs) ∧
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ →
    ChirotopesOutsideZerosAgree g.center (g.curve t) ∧ G1 (g.curve t) ∧
    (∀ c, IsCrossing (g.curve t) c ↔ IsCrossing g.center c) ∧
    TripleUnchangedOrders g.center (g.curve t) e f k ∧
    ∀ ht : t.val ≠ 0, TripleSides hn (g.generic_punctured t ht) e f k

theorem triple_wall_sides (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) : TripleWallSidesData hn g e f k := by
  have hG1 : G1 g.center := (g.pointZeros_empty_iff).mp h.1
  refine ⟨g.triple_regular hn h, ?_, ?_⟩
  · intro s t
    exact ⟨g.triple_sides_crossing_equiv hn h s t, g.triple_exact_parameter_orders hn h s t,
      g.triple_exact_visit_orders hn h s t⟩
  · apply (g.eventually_center_iff_radius _).mp
    have hchi := g.continuous_curve.continuousAt.eventually (outsideZeros_chi_persists g.center)
    have hcross := g.continuous_curve.continuousAt.eventually (g1_crossings_locally_constant hn hG1)
    have horder := g.continuous_curve.continuousAt.eventually (uniqueTriple_other_orders_persist hn hG1 h.2.1)
    have hadj := g.continuous_curve.continuousAt.eventually (uniqueTriple_sides_eventually hn hG1 h.2.1)
    filter_upwards [hchi, hcross, horder, hadj] with t hct hxt hot hat
    exact ⟨hct, hxt.1, hxt.2, hot, fun hne => hat (g.generic_punctured t hne)⟩

end SM
