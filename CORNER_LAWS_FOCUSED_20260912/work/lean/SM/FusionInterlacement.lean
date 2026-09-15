import SM.FusionKey
import SM.GeometricInterlacement

/-! The actual alternating-four-visit relation and graph transport through
fusion, using the independently proved crossing/fibre and cyclic-order maps. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}

theorem fusion_crossingVisitBetween (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) (x y : Crossing P)
    (x₀ x₁ : {i // i ∈ x.val}) (y₀ : {i // i ∈ y.val}) :
    geometricCrossingVisitBetween
      (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc))
      (fusionCrossingEquiv hn hz hb hc x)
      (fusionVisitEdgeEquiv hn hz hb hc x x₀) (fusionVisitEdgeEquiv hn hz hb hc x x₁)
      (fusionCrossingEquiv hn hz hb hc y) (fusionVisitEdgeEquiv hn hz hb hc y y₀) ↔
    geometricCrossingVisitBetween (flat_crossingGeometry (by omega) hz hb hc) x x₀ x₁ y y₀ :=
  fusionVisit_cyclic_order hn hz hb hc ⟨x, x₀⟩ ⟨y, y₀⟩ ⟨x, x₁⟩

theorem geometric_interlaces_fusion (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) (x y : Crossing P) :
    GeometricInterlaces (flat_crossingGeometry (by omega) hz hb hc) x y ↔
    GeometricInterlaces (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc))
      (fusionCrossingEquiv hn hz hb hc x) (fusionCrossingEquiv hn hz hb hc y) := by
  let e := fusionCrossingEquiv hn hz hb hc
  let ex := fusionVisitEdgeEquiv hn hz hb hc x
  let ey := fusionVisitEdgeEquiv hn hz hb hc y
  constructor
  · rintro ⟨hxy, x₀, x₁, y₀, y₁, hx, hy, h₀, h₁⟩
    refine ⟨fun he => hxy (e.injective he), ex x₀, ex x₁, ey y₀, ey y₁,
      fun he => hx (ex.injective he), fun he => hy (ey.injective he), ?_, ?_⟩
    · exact (fusion_crossingVisitBetween hn hz hb hc x y x₀ x₁ y₀).mpr h₀
    · exact (fusion_crossingVisitBetween hn hz hb hc x y x₁ x₀ y₁).mpr h₁
  · rintro ⟨hxy, x₀', x₁', y₀', y₁', hx, hy, h₀, h₁⟩
    obtain ⟨x₀, rfl⟩ := ex.surjective x₀'
    obtain ⟨x₁, rfl⟩ := ex.surjective x₁'
    obtain ⟨y₀, rfl⟩ := ey.surjective y₀'
    obtain ⟨y₁, rfl⟩ := ey.surjective y₁'
    refine ⟨fun he => hxy (congrArg e he), x₀, x₁, y₀, y₁,
      fun he => hx (congrArg ex he), fun he => hy (congrArg ey he), ?_, ?_⟩
    · exact (fusion_crossingVisitBetween hn hz hb hc x y x₀ x₁ y₀).mp h₀
    · exact (fusion_crossingVisitBetween hn hz hb hc x y x₁ x₀ y₁).mp h₁

noncomputable def fusionInterlacementGraphIso (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) :
    geometricInterlacementGraph (flat_crossingGeometry (by omega) hz hb hc) ≃g
      geometricInterlacementGraph (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc)) where
  toEquiv := fusionCrossingEquiv hn hz hb hc
  map_rel_iff' := (geometric_interlaces_fusion hn hz hb hc _ _).symm

end SM
