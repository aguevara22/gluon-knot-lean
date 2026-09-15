import SM.CrossingVertexExclusion
import SM.FlatLocal

/-! The full spatial crossing clauses on a flat germ, at zero and at every
punctured Generic parameter: transverse interior meetings, distinct actual
crossing points, and no crossing point equal to any actual vertex. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem flat_germ_nonincident_vertex_exclusion (hn : 4 ≤ n) (g : WallGerm n) {j : ZMod n}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (t : g.Parameter) :
    ∀ k i, ¬ incident k i → g.curve t k ∉ edgeSegment (g.curve t) i := by
  by_cases ht : t.val = 0
  · have he : t = g.zeroParameter := Subtype.ext ht
    subst t
    exact flat_nonincident_vertex_exclusion hn hz hb
  · exact (generic_implies_weak (by omega) (g.generic_punctured t ht)).2.2.1

theorem flat_germ_spatial_data (hn : 4 ≤ n) (g : WallGerm n) {j : ZMod n}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.Parameter) :
    CrossingGeometry (g.curve t) ∧
    Function.Injective (@crossingPoint n (g.curve t)) ∧
    (∀ c : Crossing (g.curve t), ∀ k, crossingPoint c ≠ g.curve t k) := by
  have hgeo := flat_germ_crossingGeometry hn g hz hb hc t
  exact ⟨hgeo, crossingPoint_injective_of_geometry hgeo,
    crossingPoint_ne_vertex_of_geometry hgeo (flat_germ_nonincident_vertex_exclusion hn g hz hb t)⟩

end SM
