import SM.FusionIndices

/-! Exact edge and point formulas for actual fusion. The factors are positive,
and the affine parameter puts all first-piece visits before second-piece visits. -/

namespace SM

variable {n : ℕ} [NeZero n]

def fusionScale (r : ℝ) (j k : ZMod (n + 1)) : ℝ :=
  if k = j then 1 - r else if k = j - 1 then r else 1

def fusionParameter (r : ℝ) (j k : ZMod (n + 1)) (t : ℝ) : ℝ :=
  if k = j then r + (1 - r) * t else if k = j - 1 then r * t else t

theorem fusionScale_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (j k : ZMod (n + 1)) : 0 < fusionScale r j k := by
  unfold fusionScale
  split_ifs <;> first | exact hr0 | exact sub_pos.mpr hr1 | norm_num

theorem fusionParameter_interior {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (ht0 : 0 < t) (ht1 : t < 1) (j k : ZMod (n + 1)) :
    0 < fusionParameter r j k t ∧ fusionParameter r j k t < 1 := by
  unfold fusionParameter
  split_ifs
  · have hp := mul_pos (sub_pos.mpr hr1) ht0
    have hq := mul_pos (sub_pos.mpr hr1) (sub_pos.mpr ht1)
    constructor <;> nlinarith
  · have hp := mul_pos hr0 ht0
    have hq := mul_pos hr0 (sub_pos.mpr ht1)
    constructor <;> nlinarith
  · exact ⟨ht0, ht1⟩

theorem edge_fusion (P : LabelledTuple (n + 1)) {j : ZMod (n + 1)} {r : ℝ}
    (hm : P j = P (j - 1) + r • (P (j + 1) - P (j - 1))) (k : ZMod (n + 1)) :
    edge P k = fusionScale r j k • edge (deleteVertex P j) (fusionIndex j k) := by
  by_cases hk : k = j
  · subst k
    rw [fusionIndex_deleted, edge_deleteVertex_last]
    simp only [fusionScale, ↓reduceIte, edge]
    rw [hm]
    ext <;> dsimp <;> ring
  · by_cases hp : k = j - 1
    · subst k
      rw [fusionIndex_prev, edge_deleteVertex_last]
      simp only [fusionScale, hk, ↓reduceIte, edge, sub_add_cancel]
      rw [hm]
      ext <;> dsimp <;> ring
    · simp only [fusionScale, hk, hp, ↓reduceIte, one_smul]
      simpa only [deletionIndex_fusionIndex hk hp] using
        (edge_deleteVertex P j (fusionIndex_ne_last hk hp)).symm

theorem edgePoint_fusion (P : LabelledTuple (n + 1)) {j : ZMod (n + 1)} {r : ℝ}
    (hm : P j = P (j - 1) + r • (P (j + 1) - P (j - 1)))
    (k : ZMod (n + 1)) (t : ℝ) :
    edgePoint P k t = edgePoint (deleteVertex P j) (fusionIndex j k)
      (fusionParameter r j k t) := by
  by_cases hk : k = j
  · subst k
    rw [fusionIndex_deleted]
    simp only [fusionParameter, ↓reduceIte, edgePoint, deleteVertex_last,
      edge_deleteVertex_last, edge, neg_add_cancel, deleteVertex_zero]
    rw [hm]
    ext <;> dsimp <;> ring
  · by_cases hp : k = j - 1
    · subst k
      rw [fusionIndex_prev]
      simp only [fusionParameter, hk, ↓reduceIte, edgePoint, deleteVertex_last,
        edge_deleteVertex_last, edge, sub_add_cancel, neg_add_cancel, deleteVertex_zero]
      rw [hm]
      ext <;> dsimp <;> ring
    · simp only [fusionParameter, hk, hp, ↓reduceIte]
      simpa only [deletionIndex_fusionIndex hk hp] using
        (edgePoint_deleteVertex P j (fusionIndex_ne_last hk hp) t).symm

theorem parent_interior_fusion {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1))) {k : ZMod (n + 1)} {x : Plane}
    (hx : x ∈ edgeInterior P k) :
    x ∈ edgeInterior (deleteVertex P j) (fusionIndex j k) := by
  obtain ⟨_, r, hr0, hr1, hm⟩ := hb
  obtain ⟨t, ht0, ht1, ht⟩ := hx
  have hs := fusionParameter_interior hr0 hr1 ht0 ht1 j k
  exact ⟨fusionParameter r j k t, hs.1, hs.2, ht.trans (edgePoint_fusion P hm k t)⟩

end SM
