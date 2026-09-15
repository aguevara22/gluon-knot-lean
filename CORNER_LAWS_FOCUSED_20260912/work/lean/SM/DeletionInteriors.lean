import SM.DeletionG1
import SM.AffineSubdivision
import SM.FlatAdjacent

/-! Lifting actual deleted-edge interiors to parent interiors, including the
fused edge. The middle vertex is explicitly excluded where required. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}

theorem deleted_middle_not_on_unchanged (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    {i : ZMod n} (hi : i ≠ -1) : P j ∉ edgeInterior (deleteVertex P j) i := by
  rw [edgeInterior_deleteVertex P j hi]
  intro hm
  exact flat_nonincident_vertex_exclusion (by omega) hz hb j (deletionIndex j i)
    (deletionIndex_not_incident j hi)
    (edgeInterior_subset_edgeSegment P (deletionIndex j i) hm)

theorem fused_interior_lift
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1))) {x : Plane}
    (hx : x ∈ edgeInterior (deleteVertex P j) (-1)) (hxm : x ≠ P j) :
    x ∈ edgeInterior P (j - 1) ∨ x ∈ edgeInterior P j := by
  obtain ⟨q, hq0, hq1, hq⟩ := hx
  simp only [edgePoint, deleteVertex_last, edge_deleteVertex_last] at hq
  obtain ⟨_, r, hr0, hr1, hr⟩ := hb
  rcases affine_interior_subdivision hr0 hr1 hr hq0 hq1 hq hxm with
    ⟨s, hs0, hs1, hs⟩ | ⟨s, hs0, hs1, hs⟩
  · left
    refine ⟨s, hs0, hs1, ?_⟩
    simpa only [edgePoint, edge, sub_add_cancel] using hs
  · right
    exact ⟨s, hs0, hs1, hs⟩

/-- A parent edge lifting one child edge: inherited edges have their unique
retained label; the fused edge has exactly the two incident labels as options. -/
def DeletionEdgeLift (j : ZMod (n + 1)) (i : ZMod n) (k : ZMod (n + 1)) : Prop :=
  if i = -1 then k = j - 1 ∨ k = j else k = deletionIndex j i

theorem deletionEdgeLift_injective {a b : ZMod n} {k : ZMod (n + 1)}
    (ha : DeletionEdgeLift j a k) (hb : DeletionEdgeLift j b k) : a = b := by
  by_cases hla : a = -1
  · by_cases hlb : b = -1
    · exact hla.trans hlb.symm
    · simp only [DeletionEdgeLift, hla, ↓reduceIte] at ha
      simp only [DeletionEdgeLift, hlb, ↓reduceIte] at hb
      rcases ha with ha | ha
      · exact (deletionIndex_ne_prev j hlb (hb.symm.trans ha)).elim
      · exact (deletionIndex_ne_deleted j b (hb.symm.trans ha)).elim
  · by_cases hlb : b = -1
    · simp only [DeletionEdgeLift, hla, ↓reduceIte] at ha
      simp only [DeletionEdgeLift, hlb, ↓reduceIte] at hb
      rcases hb with hb | hb
      · exact (deletionIndex_ne_prev j hla (ha.symm.trans hb)).elim
      · exact (deletionIndex_ne_deleted j a (ha.symm.trans hb)).elim
    · simp only [DeletionEdgeLift, hla, ↓reduceIte] at ha
      simp only [DeletionEdgeLift, hlb, ↓reduceIte] at hb
      exact deletionIndex_injective j (ha.symm.trans hb)

theorem deleted_interior_lift
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1))) {i : ZMod n} {x : Plane}
    (hx : x ∈ edgeInterior (deleteVertex P j) i) (hxm : x ≠ P j) :
    ∃ k : ZMod (n + 1), DeletionEdgeLift j i k ∧ x ∈ edgeInterior P k := by
  by_cases hi : i = -1
  · subst i
    rcases fused_interior_lift hb hx hxm with hl | hr
    · exact ⟨j - 1, by simp [DeletionEdgeLift], hl⟩
    · exact ⟨j, by simp [DeletionEdgeLift], hr⟩
  · exact ⟨deletionIndex j i, by simp [DeletionEdgeLift, hi],
      (edgeInterior_deleteVertex P j hi) ▸ hx⟩

end SM
