import SM.DeletionInteriors

/-! The actual edge-label fusion map. Both edges incident to the deleted
vertex map to the child's closing edge; every other edge has its retained label. -/

namespace SM

variable {n : ℕ} [NeZero n]

def fusionIndex (j k : ZMod (n + 1)) : ZMod n :=
  if k = j then -1 else ((k - (j + 1)).val : ZMod n)

theorem fusionIndex_deleted (j : ZMod (n + 1)) : fusionIndex j j = -1 := by
  simp [fusionIndex]

theorem fusionIndex_deletionIndex (j : ZMod (n + 1)) (i : ZMod n) :
    fusionIndex j (deletionIndex j i) = i := by
  rw [fusionIndex, if_neg (deletionIndex_ne_deleted j i)]
  simp only [deletionIndex, add_sub_cancel_right, insertIndex_val, ZMod.natCast_zmod_val]

theorem fusionIndex_prev (j : ZMod (n + 1)) : fusionIndex j (j - 1) = -1 := by
  rw [← deletionIndex_last (n := n) j, fusionIndex_deletionIndex]

theorem fusionIndex_of_lift {j k : ZMod (n + 1)} {i : ZMod n}
    (h : DeletionEdgeLift j i k) : fusionIndex j k = i := by
  by_cases hi : i = -1
  · subst i
    simp only [DeletionEdgeLift, ↓reduceIte] at h
    rcases h with rfl | rfl
    · exact fusionIndex_prev _
    · exact fusionIndex_deleted _
  · simp only [DeletionEdgeLift, hi, ↓reduceIte] at h
    rw [h, fusionIndex_deletionIndex]

theorem fusionIndex_lift (j k : ZMod (n + 1)) :
    DeletionEdgeLift j (fusionIndex j k) k := by
  by_cases hk : k = j
  · subst k
    simp [fusionIndex_deleted, DeletionEdgeLift]
  · obtain ⟨i, rfl⟩ := deletionIndex_exhaust j hk
    rw [fusionIndex_deletionIndex]
    by_cases hi : i = -1
    · simp [DeletionEdgeLift, hi, deletionIndex_last]
    · simp [DeletionEdgeLift, hi]

theorem fusionIndex_eq_iff_lift {j k : ZMod (n + 1)} {i : ZMod n} :
    fusionIndex j k = i ↔ DeletionEdgeLift j i k :=
  ⟨fun he => he ▸ fusionIndex_lift j k, fusionIndex_of_lift⟩

theorem fusionIndex_ne_of_remote {j a b : ZMod (n + 1)} (hr : remote a b) :
    fusionIndex j a ≠ fusionIndex j b := by
  intro he
  have ha := fusionIndex_lift j a
  have hb := fusionIndex_lift j b
  rw [← he] at hb
  by_cases hi : fusionIndex j a = -1
  · simp only [DeletionEdgeLift, hi, ↓reduceIte] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    all_goals apply hr; simp [adjacent]
  · simp only [DeletionEdgeLift, hi, ↓reduceIte] at ha hb
    have hab : a = b := ha.trans hb.symm
    exact (remote_endpoints a b hr).1 hab.symm

theorem fusionIndex_ne_last {j k : ZMod (n + 1)} (hj : k ≠ j) (hp : k ≠ j - 1) :
    fusionIndex j k ≠ -1 := by
  intro he
  have h := fusionIndex_lift j k
  simp only [DeletionEdgeLift, he, ↓reduceIte] at h
  exact h.elim hp hj

theorem deletionIndex_fusionIndex {j k : ZMod (n + 1)} (hj : k ≠ j) (hp : k ≠ j - 1) :
    deletionIndex j (fusionIndex j k) = k := by
  have h := fusionIndex_lift j k
  simp only [DeletionEdgeLift, fusionIndex_ne_last hj hp, ↓reduceIte] at h
  exact h.symm

end SM
