import SM.FusionGeometry
import SM.DeletionGeneric
import SM.FlatCrossingGeometry
import SM.TripleCenter

/-! The genuine crossing bijection under deletion: replace either incident
edge by the fused edge. Preservation and surjectivity use actual interior
points; injectivity uses their proved uniqueness and the full parent G2. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}

theorem isCrossing_fusion (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) {s : Finset (ZMod (n + 1))} (hs : IsCrossing P s) :
    IsCrossing (deleteVertex P j) (s.image (fusionIndex j)) := by
  letI : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨a, b, rfl, hr, x, hxa, hxb⟩ := hs
  have hgeo := flat_crossingGeometry (by omega) hz hb hc
  have hmeet := hgeo.2.1 a b hr x hxa hxb
  have ha := parent_interior_fusion hb hmeet.1
  have hb' := parent_interior_fusion hb hmeet.2.1
  have hr' := g1_common_interiors_remote hn (g1_deleteVertex hz)
    (fusionIndex_ne_of_remote (j := j) hr) ha hb'
  simpa only [Finset.image_insert, Finset.image_singleton] using
    isCrossing_of_common_interiors hr' ha hb'

def fusionCrossing (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) (c : Crossing P) : Crossing (deleteVertex P j) :=
  ⟨c.val.image (fusionIndex j), isCrossing_fusion hn hz hb hc c.property⟩

theorem fusionCrossing_support (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) (c : Crossing P) :
    (fusionCrossing hn hz hb hc c).val = c.val.image (fusionIndex j) := rfl

theorem crossingPoint_fusion (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) (c : Crossing P) :
    crossingPoint (fusionCrossing hn hz hb hc c) = crossingPoint c := by
  symm
  apply crossingPoint_unique_of_geometry
    (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc))
  intro i hi
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
  exact edgeInterior_subset_edgeSegment _ _
    (parent_interior_fusion hb
      (crossingPoint_interior_of_geometry (flat_crossingGeometry (by omega) hz hb hc) c k hk))

theorem fusionCrossing_injective (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) : Function.Injective (fusionCrossing hn hz hb hc) := by
  intro c d he
  apply crossingPoint_injective_of_geometry (flat_crossingGeometry (by omega) hz hb hc)
  rw [← crossingPoint_fusion hn hz hb hc c, ← crossingPoint_fusion hn hz hb hc d, he]

theorem fusionCrossing_surjective (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) : Function.Surjective (fusionCrossing hn hz hb hc) := by
  intro d
  obtain ⟨a, b, hd, hr, _⟩ := d.property
  have hgeom := generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc)
  have ha := crossingPoint_interior_of_geometry hgeom d a (by rw [hd]; simp)
  have hb' := crossingPoint_interior_of_geometry hgeom d b (by rw [hd]; simp)
  have hab : a ≠ b := (remote_endpoints a b hr).1.symm
  have hxm : crossingPoint d ≠ P j := by
    intro he
    by_cases hal : a = -1
    · have hbl : b ≠ -1 := fun hl => hab (hal.trans hl.symm)
      exact deleted_middle_not_on_unchanged hn hz hb hbl (he ▸ hb')
    · exact deleted_middle_not_on_unchanged hn hz hb hal (he ▸ ha)
  obtain ⟨ka, hka, hxa⟩ := deleted_interior_lift hb ha hxm
  obtain ⟨kb, hkb, hxb⟩ := deleted_interior_lift hb hb' hxm
  have hne : ka ≠ kb := fun he => hab (deletionEdgeLift_injective (he ▸ hka) hkb)
  have hr' := flat_common_interiors_remote (by omega) hz hb hne hxa hxb
  let c : Crossing P := ⟨{ka, kb}, isCrossing_of_common_interiors hr' hxa hxb⟩
  refine ⟨c, Subtype.ext ?_⟩
  rw [fusionCrossing_support, hd]
  change ({ka, kb} : Finset _).image (fusionIndex j) = {a, b}
  rw [Finset.image_insert, Finset.image_singleton,
    fusionIndex_of_lift hka, fusionIndex_of_lift hkb]

noncomputable def fusionCrossingEquiv (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) : Crossing P ≃ Crossing (deleteVertex P j) :=
  Equiv.ofBijective (fusionCrossing hn hz hb hc)
    ⟨fusionCrossing_injective hn hz hb hc, fusionCrossing_surjective hn hz hb hc⟩

end SM
