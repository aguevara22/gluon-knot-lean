import SM.FlatAdjacent
import SM.SingleTripleTransverse
import SM.CrossingGeometry

/-! Actual flat-centre crossing geometry, derived from the source hypotheses.
The auxiliary record domain is proved here, never added as a wall hypothesis. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {j : ZMod n}

theorem flat_crossingGeometry (hn : 4 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) : CrossingGeometry P := by
  have hv := flat_nonincident_vertex_exclusion hn hz hb
  refine ⟨singlePointTriple_edge_ne_zero hn hz, ?_, flat_center_g2 hn hz hb hc⟩
  intro i k hr x hi hk
  exact ⟨remote_closed_point_interior hv hr hi hk,
    remote_closed_point_interior hv (remote_symm hr) hk hi,
    singlePointTriple_remote_transverse hn hz hr hi hk⟩

end SM
