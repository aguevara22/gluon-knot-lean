namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The actual three nonempty presentations: A only, B only, then both. -/
def spanningCutSet (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (i : Fin 3) : BoundaryCutSet I :=
  expandCuts s I hI C (spanningRows s I hI C hL hR hs i)

/-- Every old-section cut lies in the actual strict parent interval. -/
theorem spanning_old_cut_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (k : Fin n) (hk : k ∈ C.cuts) :
    I.left ≤ old s k ∧ old s k ≤ I.right := by
  have hb := C.bounds k hk
  constructor
  · have hl := (old_strictMono s).monotone hb.1
    change old s (collapse s I.left) ≤ old s k at hl
    rwa [old_collapse_of_ne_B s I.left (ne_of_lt (lt_trans hL (A_lt_B s)))] at hl
  · have hr := (old_strictMono s).monotone hb.2
    change old s k ≤ old s (collapse s I.right) at hr
    rwa [old_collapse_of_ne_B s I.right (ne_of_gt hR)] at hr

/-- The tail section differs only at s, where B is strictly inside the parent. -/
theorem spanning_tail_cut_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (k : Fin n) (hk : k ∈ C.cuts) :
    I.left ≤ startingTailEmbedding s k ∧ startingTailEmbedding s k ≤ I.right := by
  by_cases he : k = s
  · subst k
    rw [startingTail_self]
    exact ⟨(lt_trans hL (A_lt_B s)).le, hR.le⟩
  · rw [startingTail_eq_old s k he]
    exact spanning_old_cut_bounds s I hI C hL hR k hk

theorem spanningCutSet_zero_cuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCutSet s I hI C hL hR hs 0).cuts = C.cuts.image (old s) := by
  ext p
  have hm := mem_expandCuts s I hI C (spanningRows s I hI C hL hR hs 0) p
  change p ∈ (spanningCutSet s I hI C hL hR hs 0).cuts ↔
    ((I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts ∧ collapse s p ≠ s) ∨
      p ∈ (spanningRows s I hI C hL hR hs 0).val at hm
  simp only [spanningRows, Matrix.cons_val_zero, Finset.mem_singleton] at hm
  rw [hm]
  constructor
  · rintro (h | rfl)
    · have he := (collapse_eq_iff_of_ne s (collapse s p) h.2.2 p).mp rfl
      exact Finset.mem_image.mpr ⟨collapse s p, h.2.1, he.symm⟩
    · exact Finset.mem_image.mpr ⟨s, hs, old_self s⟩
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    by_cases hks : k = s
    · exact Or.inr (by rw [hks, old_self])
    · left
      exact ⟨spanning_old_cut_bounds s I hI C hL hR k hk,
        by simpa only [collapse_old] using hk, by simpa only [collapse_old] using hks⟩

theorem spanningCutSet_one_cuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCutSet s I hI C hL hR hs 1).cuts = C.cuts.image (startingTailEmbedding s) := by
  ext p
  have hm := mem_expandCuts s I hI C (spanningRows s I hI C hL hR hs 1) p
  change p ∈ (spanningCutSet s I hI C hL hR hs 1).cuts ↔
    ((I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts ∧ collapse s p ≠ s) ∨
      p ∈ (spanningRows s I hI C hL hR hs 1).val at hm
  simp only [spanningRows, Matrix.cons_val_one, Finset.mem_singleton] at hm
  rw [hm]
  constructor
  · rintro (h | rfl)
    · have he := (collapse_eq_iff_of_ne s (collapse s p) h.2.2 p).mp rfl
      exact Finset.mem_image.mpr ⟨collapse s p, h.2.1,
        (startingTail_eq_old s _ h.2.2).trans he.symm⟩
    · exact Finset.mem_image.mpr ⟨s, hs, startingTail_self s⟩
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    by_cases hks : k = s
    · exact Or.inr (by rw [hks, startingTail_self])
    · left
      exact ⟨spanning_tail_cut_bounds s I hI C hL hR k hk,
        by simpa only [collapse_startingTail] using hk,
        by simpa only [collapse_startingTail] using hks⟩

/-- The both-cut row inserts exactly B into the A-only cut set. -/
theorem spanningCutSet_two_insert_B (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCutSet s I hI C hL hR hs 2).cuts =
      insert (B s) (spanningCutSet s I hI C hL hR hs 0).cuts := by
  ext p
  simp only [spanningCutSet, mem_expandCuts, spanningRows, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The same actual both-cut row inserts exactly A into the B-only cut set. -/
theorem spanningCutSet_two_insert_A (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCutSet s I hI C hL hR hs 2).cuts =
      insert (A s) (spanningCutSet s I hI C hL hR hs 1).cuts := by
  rw [spanningCutSet_two_insert_B, spanningCutSet_zero_cuts, spanningCutSet_one_cuts]
  exact starting_sections_cut_image s C.cuts hs

/-- Every actual A-only child is precisely one old-image core child. -/
def spanningChildrenZeroEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    {K : BoundaryInterval n // C.Consecutive K} ≃
      {K : BoundaryInterval (n + 1) // (spanningCutSet s I hI C hL hR hs 0).Consecutive K} :=
  consecutiveOrderedImageEquiv (startingOldEmbedding s) C _
    (spanningCutSet_zero_cuts s I hI C hL hR hs)

/-- Every actual B-only child is precisely one tail-image core child. -/
def spanningChildrenOneEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    {K : BoundaryInterval n // C.Consecutive K} ≃
      {K : BoundaryInterval (n + 1) // (spanningCutSet s I hI C hL hR hs 1).Consecutive K} :=
  consecutiveOrderedImageEquiv (startingTailEmbedding s) C _
    (spanningCutSet_one_cuts s I hI C hL hR hs)

end
end SM.SoftDuplication
