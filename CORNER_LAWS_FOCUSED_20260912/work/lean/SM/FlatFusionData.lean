import SM.FusionGaussWord
import SM.FusionInterlacement
import SM.FusionSigns

/-! Explicit actual deletion/fusion conclusions for flat-sides (iii). Every
map in this specification is the constructed geometric map, not supplied data. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}

def FlatFusionData (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) : Prop :=
  Generic (deleteVertex P j) ∧
  (∃ r : ℝ, 0 < r ∧ r < 1 ∧
    edge P (j - 1) = r • edge (deleteVertex P j) (-1) ∧
    edge P j = (1 - r) • edge (deleteVertex P j) (-1) ∧
    ∀ v : Visit P, visitParameter (fusionVisitEquiv hn hz hb hc v) =
      fusionParameter r j v.2.val (visitParameter v)) ∧
  (∀ c : Crossing P, (fusionCrossingEquiv hn hz hb hc c).val =
    c.val.image (fusionIndex j)) ∧
  (∀ c : Crossing P, crossingPoint (fusionCrossingEquiv hn hz hb hc c) = crossingPoint c) ∧
  (∀ v : Visit P, (fusionVisitEquiv hn hz hb hc v).2.val = fusionIndex j v.2.val) ∧
  (∀ v w : Visit P, (fusionVisitEquiv hn hz hb hc v).1 =
      (fusionVisitEquiv hn hz hb hc w).1 ↔ v.1 = w.1) ∧
  (∀ v w u : Visit P,
    traversalBetween
      (geometricVisitPosition (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc))
        (fusionVisitEquiv hn hz hb hc v))
      (geometricVisitPosition (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc))
        (fusionVisitEquiv hn hz hb hc w))
      (geometricVisitPosition (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc))
        (fusionVisitEquiv hn hz hb hc u)) ↔
    traversalBetween
      (geometricVisitPosition (flat_crossingGeometry (by omega) hz hb hc) v)
      (geometricVisitPosition (flat_crossingGeometry (by omega) hz hb hc) w)
      (geometricVisitPosition (flat_crossingGeometry (by omega) hz hb hc) u)) ∧
  ((geometricGaussWord (flat_crossingGeometry (by omega) hz hb hc)).map
    (fusionCrossingEquiv hn hz hb hc) =
    geometricGaussWord (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc))) ∧
  (∀ x y : Crossing P, GeometricInterlaces (flat_crossingGeometry (by omega) hz hb hc) x y ↔
    GeometricInterlaces (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc))
      (fusionCrossingEquiv hn hz hb hc x) (fusionCrossingEquiv hn hz hb hc y)) ∧
  (∀ a b, crossingSign (deleteVertex P j) (fusionIndex j a) (fusionIndex j b) =
    crossingSign P a b) ∧
  (∀ a b, 0 < det (edge P a) (edge P b) ↔
    0 < det (edge (deleteVertex P j) (fusionIndex j a))
      (edge (deleteVertex P j) (fusionIndex j b)))

theorem flat_fusion_data (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) : FlatFusionData hn hz hb hc := by
  letI : Fact (1 < n + 1) := ⟨by omega⟩
  refine ⟨generic_deleteVertex hn hz hb hc, ?_, fusionCrossing_support hn hz hb hc,
    crossingPoint_fusion hn hz hb hc, fusionVisit_edge hn hz hb hc,
    fusionVisit_pairing hn hz hb hc, fusionVisit_cyclic_order hn hz hb hc,
    geometricGaussWord_fusion hn hz hb hc, geometric_interlaces_fusion hn hz hb hc,
    crossingSign_fusion hb, positive_over_fusion hb⟩
  obtain ⟨r, hr0, hr1, hm⟩ := hb.2
  refine ⟨r, hr0, hr1, ?_, ?_, visitParameter_fusion hn hz hb hc hm⟩
  · simpa only [fusionScale, prev_ne_self j, ↓reduceIte, fusionIndex_prev] using
      edge_fusion P hm (j - 1)
  · simpa only [fusionScale, ↓reduceIte, fusionIndex_deleted] using edge_fusion P hm j

end SM
