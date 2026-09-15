namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- A refined cut set contains all cuts of the chosen outer composition. -/
abbrev RefiningCutSet (π : IntervalComposition I) :=
  {S : BoundaryCutSet I // π.cutSet.cuts ⊆ S.cuts}

namespace IntervalComposition

/-- Half-open part membership is unique, including points at a shared cut. -/
theorem halfOpen_part_unique (π : IntervalComposition I) (x : Fin n)
    {k l : Fin π.parts} (hk : (π.part k).left ≤ x ∧ x < (π.part k).right)
    (hl : (π.part l).left ≤ x ∧ x < (π.part l).right) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · exact False.elim ((not_le_of_gt hk.2) (le_trans (π.part_order h) hl.1))
  · exact h
  · exact False.elim ((not_le_of_gt hl.2) (le_trans (π.part_order h) hk.1))

/-- The ordered union of every inner composition's cuts. Common endpoints
are identified as the same boundary position. -/
def flattenCutSets (π : IntervalComposition I)
    (S : ∀ k : Fin π.parts, BoundaryCutSet (π.part k)) : BoundaryCutSet I where
  cuts := Finset.univ.biUnion (fun k => (S k).cuts)
  left_mem := by
    let k : Fin π.parts := ⟨0, π.parts_pos⟩
    have hk : (π.part k).left = I.left := π.first
    apply Finset.mem_biUnion.mpr
    exact ⟨k, Finset.mem_univ _, hk ▸ (S k).left_mem⟩
  right_mem := by
    let k : Fin π.parts := ⟨π.parts - 1, by have := π.parts_pos; omega⟩
    have hs : k.succ = Fin.last π.parts := by
      apply Fin.ext
      change π.parts - 1 + 1 = π.parts
      have := π.parts_pos
      omega
    have hk : (π.part k).right = I.right := by change π.cut k.succ = I.right; rw [hs, π.last]
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hk ▸ (S k).right_mem⟩
  bounds := by
    intro x hx
    obtain ⟨k, _, hx⟩ := Finset.mem_biUnion.mp hx
    have hs := (S k).bounds x hx
    have hp := π.part_bounds k
    exact ⟨le_trans hp.1 hs.1, le_trans hs.2 hp.2⟩

theorem mem_flattenCutSets (π : IntervalComposition I)
    (S : ∀ k : Fin π.parts, BoundaryCutSet (π.part k)) (x : Fin n) :
    x ∈ (π.flattenCutSets S).cuts ↔ ∃ k, x ∈ (S k).cuts := by
  simp [flattenCutSets]

/-- Every outer cut remains in the union, including both global endpoints. -/
theorem outer_cuts_subset_flatten (π : IntervalComposition I)
    (S : ∀ k : Fin π.parts, BoundaryCutSet (π.part k)) :
    π.cutSet.cuts ⊆ (π.flattenCutSets S).cuts := by
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  rw [mem_flattenCutSets]
  by_cases hj : j.val < π.parts
  · let k : Fin π.parts := ⟨j.val, hj⟩
    have hk : k.castSucc = j := by apply Fin.ext; rfl
    refine ⟨k, ?_⟩
    have he : (π.part k).left = π.cut j := by change π.cut k.castSucc = π.cut j; rw [hk]
    exact he ▸ (S k).left_mem
  · have he : j = Fin.last π.parts := by
      apply Fin.ext
      have := j.isLt
      change j.val = π.parts
      omega
    rw [he, π.last]
    exact (mem_flattenCutSets π S I.right).mp (π.flattenCutSets S).right_mem

def flattenRefinement (π : IntervalComposition I)
    (S : ∀ k : Fin π.parts, BoundaryCutSet (π.part k)) : RefiningCutSet π :=
  ⟨π.flattenCutSets S, π.outer_cuts_subset_flatten S⟩

/-- Recover each inner composition's exact cut set by interval restriction. -/
def unflattenCutSets (π : IntervalComposition I) (T : RefiningCutSet π)
    (k : Fin π.parts) : BoundaryCutSet (π.part k) :=
  T.val.restrict (π.part k)
    (T.property (Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, rfl⟩))
    (T.property (Finset.mem_image.mpr ⟨k.succ, Finset.mem_univ _, rfl⟩))

/-- Restricting a union to an outer part recovers its inner cut set.
Cuts coming from different parts can enter only at a shared endpoint. -/
theorem unflatten_flatten (π : IntervalComposition I)
    (S : ∀ k : Fin π.parts, BoundaryCutSet (π.part k)) :
    π.unflattenCutSets (π.flattenRefinement S) = S := by
  funext k
  apply BoundaryCutSet.ext
  ext x
  simp only [unflattenCutSets, BoundaryCutSet.mem_restrict, flattenRefinement]
  constructor
  · rintro ⟨hx, hkl, hkr⟩
    obtain ⟨l, hl⟩ := (π.mem_flattenCutSets S x).mp hx
    rcases lt_trichotomy l k with h | h | h
    · have hb := (S l).bounds x hl
      have ho := π.part_order h
      have he : x = (π.part k).left := le_antisymm (le_trans hb.2 ho) hkl
      rw [he]
      exact (S k).left_mem
    · simpa [h] using hl
    · have hb := (S l).bounds x hl
      have ho := π.part_order h
      have he : x = (π.part k).right := le_antisymm hkr (le_trans ho hb.1)
      rw [he]
      exact (S k).right_mem
  · intro hx
    exact ⟨(π.mem_flattenCutSets S x).mpr ⟨k, hx⟩, (S k).bounds x hx⟩

/-- Every refined cut is covered by some outer part, so union after
restriction retains the entire refined cut set. -/
theorem flatten_unflatten (π : IntervalComposition I) (T : RefiningCutSet π) :
    π.flattenRefinement (π.unflattenCutSets T) = T := by
  apply Subtype.ext
  apply BoundaryCutSet.ext
  ext x
  change x ∈ (π.flattenCutSets (π.unflattenCutSets T)).cuts ↔ x ∈ T.val.cuts
  rw [mem_flattenCutSets]
  constructor
  · rintro ⟨k, hk⟩
    exact (Finset.mem_filter.mp hk).1
  · intro hx
    have hb := T.val.bounds x hx
    obtain ⟨k, hk⟩ := π.exists_closed_part x hb.1 hb.2
    exact ⟨k, Finset.mem_filter.mpr ⟨hx, hk⟩⟩

/-- The actual nested cut data and refined cut sets are inverse descriptions
for every outer composition, including the unary outer composition. -/
def nestedCutSetEquiv (π : IntervalComposition I) :
    (∀ k : Fin π.parts, BoundaryCutSet (π.part k)) ≃ RefiningCutSet π where
  toFun := π.flattenRefinement
  invFun := π.unflattenCutSets
  left_inv := π.unflatten_flatten
  right_inv := π.flatten_unflatten

/-- Every family of raw inner compositions corresponds bijectively to a
refining cut set. No inner arity or endpoint case has been excluded. -/
def nestedCompositionEquiv (π : IntervalComposition I) :
    (∀ k : Fin π.parts, IntervalComposition (π.part k)) ≃ RefiningCutSet π :=
  (Equiv.piCongrRight (fun k => cutSetEquiv (π.part k))).trans π.nestedCutSetEquiv

end IntervalComposition

end
end SM
