namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- The exact inner composition recovered from a refining cut set. -/
def refinementInner (π : IntervalComposition I) (T : RefiningCutSet π) (k : Fin π.parts) :
    IntervalComposition (π.part k) := (π.unflattenCutSets T k).toComposition

/-- A child of a recovered inner composition is globally consecutive in T:
restriction did not hide a cut between its endpoints. -/
theorem inner_child_consecutive (π : IntervalComposition I) (T : RefiningCutSet π)
    (k : Fin π.parts) (j : Fin (π.refinementInner T k).parts) :
    T.val.Consecutive ((π.refinementInner T k).part j) := by
  have hlocal := (π.refinementInner T k).part_consecutive j
  have he : (π.refinementInner T k).cutSet = π.unflattenCutSets T k :=
    BoundaryCutSet.toComposition_cutSet _
  rw [he] at hlocal
  have hb := (π.refinementInner T k).part_bounds j
  exact (T.val.consecutive_restrict_iff (π.part k)
    ((π.refinementInner T k).part j) _ _ hb.1 hb.2).mp hlocal

/-- The globally ordered fine composition has a part equal to each actual
inner child interval. -/
theorem exists_refined_child (π : IntervalComposition I) (T : RefiningCutSet π)
    (k : Fin π.parts) (j : Fin (π.refinementInner T k).parts) :
    ∃ r : Fin T.val.toComposition.parts,
      T.val.toComposition.part r = (π.refinementInner T k).part j := by
  apply T.val.toComposition.exists_part_of_consecutive
  rw [BoundaryCutSet.toComposition_cutSet]
  exact π.inner_child_consecutive T k j

def refinedChildIndex (π : IntervalComposition I) (T : RefiningCutSet π)
    (a : Σ k : Fin π.parts, Fin (π.refinementInner T k).parts) : Fin T.val.toComposition.parts :=
  Classical.choose (π.exists_refined_child T a.1 a.2)

theorem refinedChildIndex_part (π : IntervalComposition I) (T : RefiningCutSet π)
    (a : Σ k : Fin π.parts, Fin (π.refinementInner T k).parts) :
    T.val.toComposition.part (π.refinedChildIndex T a) = (π.refinementInner T a.1).part a.2 :=
  Classical.choose_spec (π.exists_refined_child T a.1 a.2)

/-- Equal fine parts imply equal outer parts, then equal inner indices. -/
theorem refinedChildIndex_injective (π : IntervalComposition I) (T : RefiningCutSet π) :
    Function.Injective (π.refinedChildIndex T) := by
  rintro ⟨k, j⟩ ⟨l, t⟩ h
  have hjt : (π.refinementInner T k).part j = (π.refinementInner T l).part t := by
    rw [← π.refinedChildIndex_part T ⟨k, j⟩, ← π.refinedChildIndex_part T ⟨l, t⟩, h]
  have hk := (π.refinementInner T k).part_bounds j
  have hl := (π.refinementInner T l).part_bounds t
  have hkl : k = l := by
    apply π.containing_part_unique ((π.refinementInner T k).part j) hk
    simpa only [hjt] using hl
  subst l
  have hidx : j = t := (π.refinementInner T k).part_injective hjt
  subst t
  rfl

/-- Every fine child lies inside a unique outer part and therefore occurs
in the complete inner family. -/
theorem refinedChildIndex_surjective (π : IntervalComposition I) (T : RefiningCutSet π) :
    Function.Surjective (π.refinedChildIndex T) := by
  intro r
  let J := T.val.toComposition.part r
  have hJ : T.val.Consecutive J := by
    have h := T.val.toComposition.part_consecutive r
    rw [BoundaryCutSet.toComposition_cutSet] at h
    exact h
  obtain ⟨k, hk⟩ := π.consecutive_contained_in_part T.val T.property J hJ
  have hlocal : (π.unflattenCutSets T k).Consecutive J :=
    (T.val.consecutive_restrict_iff (π.part k) J _ _ hk.1 hk.2).mpr hJ
  have hi : (π.refinementInner T k).cutSet.Consecutive J := by
    rw [show (π.refinementInner T k).cutSet = π.unflattenCutSets T k from
      BoundaryCutSet.toComposition_cutSet _]
    exact hlocal
  obtain ⟨j, hj⟩ := (π.refinementInner T k).exists_part_of_consecutive J hi
  refine ⟨⟨k, j⟩, ?_⟩
  apply T.val.toComposition.part_injective
  rw [π.refinedChildIndex_part T ⟨k, j⟩]
  exact hj

/-- The full family of all inner child indices is bijective with all fine
child indices; equality of the actual child intervals is retained. -/
def refinedChildrenEquiv (π : IntervalComposition I) (T : RefiningCutSet π) :
    (Σ k : Fin π.parts, Fin (π.refinementInner T k).parts) ≃ Fin T.val.toComposition.parts :=
  Equiv.ofBijective (π.refinedChildIndex T)
    ⟨π.refinedChildIndex_injective T, π.refinedChildIndex_surjective T⟩

/-- The child-coordinate product is exactly preserved under refinement,
for arbitrary values in any commutative monoid. -/
theorem prod_refined_children {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (T : RefiningCutSet π) (X : BoundaryInterval n → R) :
    (∏ k : Fin π.parts, ∏ j : Fin (π.refinementInner T k).parts,
      X ((π.refinementInner T k).part j)) =
      ∏ r : Fin T.val.toComposition.parts, X (T.val.toComposition.part r) := by
  rw [← Fintype.prod_sigma]
  exact Fintype.prod_equiv (π.refinedChildrenEquiv T) _ _
    (fun a => congrArg X (π.refinedChildIndex_part T a).symm)

/-- For a flattening of actual inner compositions, restriction recovers
them exactly, including each raw part count and ordered cut function. -/
theorem refinementInner_flatten (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) (k : Fin π.parts) :
    π.refinementInner (π.flattenRefinement (fun k => (σ k).cutSet)) k = σ k := by
  unfold refinementInner
  rw [congrFun (π.unflatten_flatten (fun k => (σ k).cutSet)) k]
  exact (σ k).cutSet_toComposition

/-- The expanded nested composition sum has exactly the refined product
of child coordinates; no edge is omitted or counted twice. -/
theorem prod_nested_children {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k))
    (X : BoundaryInterval n → R) :
    (∏ k : Fin π.parts, ∏ j : Fin (σ k).parts, X ((σ k).part j)) =
      ∏ r : Fin (π.flattenCutSets (fun k => (σ k).cutSet)).toComposition.parts,
        X ((π.flattenCutSets (fun k => (σ k).cutSet)).toComposition.part r) := by
  have h := π.prod_refined_children (π.flattenRefinement (fun k => (σ k).cutSet)) X
  simpa only [refinementInner_flatten, flattenRefinement] using h

end
end SM.IntervalComposition
