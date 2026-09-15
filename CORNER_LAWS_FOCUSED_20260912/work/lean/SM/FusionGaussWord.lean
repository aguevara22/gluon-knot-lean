import SM.FusionKey
import SM.SortedCompressedCut
import SM.GeometricRecords

/-! Transport of the independently constructed full Gauss lists and words under
actual deletion/fusion. The changed numerical cut is handled by rotation. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}

theorem geometricGaussList_fusion_perm (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) :
    ((geometricGaussList (flat_crossingGeometry (by omega) hz hb hc)).map
      (fusionVisitEquiv hn hz hb hc)).Perm
      (geometricGaussList (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc))) := by
  let hP := flat_crossingGeometry (by omega) hz hb hc
  let hQ := generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc)
  let e := fusionVisitEquiv hn hz hb hc
  apply (List.perm_ext_iff_of_nodup
    (List.Nodup.map e.injective (geometricGaussList_nodup hP))
    (geometricGaussList_nodup hQ)).mpr
  intro w
  constructor
  · intro _
    exact mem_geometricGaussList hQ w
  · intro _
    obtain ⟨v, rfl⟩ := e.surjective w
    exact List.mem_map.mpr ⟨v, mem_geometricGaussList hP v, rfl⟩

theorem geometricGaussList_fusion_rotation (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) :
    ((geometricGaussList (flat_crossingGeometry (by omega) hz hb hc)).map
      (fusionVisitEquiv hn hz hb hc)).IsRotated
      (geometricGaussList (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc))) := by
  let hP := flat_crossingGeometry (by omega) hz hb hc
  let hQ := generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc)
  obtain ⟨r, hr0, hr1, hm⟩ := hb.2
  apply sorted_map_monotone_cut_rotation _ _ (fusionVisitEquiv hn hz hb hc)
    (geometricVisitKey hP) (geometricVisitKey hQ) (n + 1) (j + 1).val
    (fusionKey ((n : ℝ) - 1) r) (fusionKey_strictMono _ hr0 hr1)
    (geometricVisitKey_injective hP) (geometricVisitKey_injective hQ)
    (geometricGaussList_sorted hP) (geometricGaussList_sorted hQ)
    (geometricGaussList_fusion_perm hn hz hb hc)
  · intro v _
    have hbound := traversalKey_lt_size (geometricVisitPosition hP v)
    exact ⟨traversalKey_nonneg _, by
      simpa only [geometricVisitKey, Nat.cast_add, Nat.cast_one] using hbound⟩
  · intro v _
    rw [fusionVisitKey_compression hn hz hb hc hm v, traversalKey_shift]
    simp only [Nat.cast_add, Nat.cast_one]
    rfl

theorem geometricGaussWord_fusion (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) :
    (geometricGaussWord (flat_crossingGeometry (by omega) hz hb hc)).map
      (fusionCrossingEquiv hn hz hb hc) =
      geometricGaussWord (generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc)) := by
  have hr := (geometricGaussList_fusion_rotation hn hz hb hc).map Sigma.fst
  apply Cycle.coe_eq_coe.mpr
  simpa only [List.map_map, Function.comp_def, fusionVisit_crossing] using hr

end SM
