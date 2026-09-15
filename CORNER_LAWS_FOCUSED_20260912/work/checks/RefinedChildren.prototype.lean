import SM.NestedCutSets
import Mathlib.Tactic

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

namespace BoundaryInterval

/-- An interval is determined by its actual two endpoints. -/
theorem eq_of_endpoints {J K : BoundaryInterval n}
    (hl : J.left = K.left) (hr : J.right = K.right) : J = K := by
  cases J
  cases K
  cases hl
  cases hr
  rfl

end BoundaryInterval

namespace BoundaryCutSet

/-- Consecutive cut positions, with no chosen enumeration or omitted cut. -/
def Consecutive (S : BoundaryCutSet I) (J : BoundaryInterval n) : Prop :=
  J.left ∈ S.cuts ∧ J.right ∈ S.cuts ∧
    ∀ x ∈ S.cuts, ¬ (J.left < x ∧ x < J.right)

/-- Inside the restricting interval, consecutive cuts are exactly the same
before and after restriction. Every potential intervening cut remains inside. -/
theorem consecutive_restrict_iff (S : BoundaryCutSet I) (O J : BoundaryInterval n)
    (hol : O.left ∈ S.cuts) (hor : O.right ∈ S.cuts)
    (hl : O.left ≤ J.left) (hr : J.right ≤ O.right) :
    (S.restrict O hol hor).Consecutive J ↔ S.Consecutive J := by
  constructor
  · rintro ⟨hjl, hjr, hn⟩
    refine ⟨(Finset.mem_filter.mp hjl).1, (Finset.mem_filter.mp hjr).1, ?_⟩
    intro x hx hbetween
    have hox : O.left ≤ x ∧ x ≤ O.right :=
      ⟨le_trans hl (le_of_lt hbetween.1), le_trans (le_of_lt hbetween.2) hr⟩
    exact hn x (Finset.mem_filter.mpr ⟨hx, hox⟩) hbetween
  · rintro ⟨hjl, hjr, hn⟩
    refine ⟨Finset.mem_filter.mpr ⟨hjl, hl, le_trans (le_of_lt J.increasing) hr⟩,
      Finset.mem_filter.mpr ⟨hjr, le_trans hl (le_of_lt J.increasing), hr⟩, ?_⟩
    intro x hx
    exact hn x (Finset.mem_filter.mp hx).1

end BoundaryCutSet

namespace IntervalComposition

/-- No cut lies strictly between the endpoints of one actual part. -/
theorem part_consecutive (π : IntervalComposition I) (k : Fin π.parts) :
    π.cutSet.Consecutive (π.part k) := by
  refine ⟨Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, rfl⟩,
    Finset.mem_image.mpr ⟨k.succ, Finset.mem_univ _, rfl⟩, ?_⟩
  intro x hx hbetween
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  have hl := π.strict.lt_iff_lt.mp hbetween.1
  have hr := π.strict.lt_iff_lt.mp hbetween.2
  change k.val < j.val at hl
  change j.val < k.val + 1 at hr
  omega

theorem part_injective (π : IntervalComposition I) : Function.Injective π.part := by
  intro k l he
  have hl := congrArg BoundaryInterval.left he
  have hc := π.strict.injective hl
  apply Fin.ext
  exact congrArg (fun j : Fin (π.parts + 1) => j.val) hc

/-- Any consecutive pair in the full cut set is one of the actual parts. -/
theorem exists_part_of_consecutive (π : IntervalComposition I) (J : BoundaryInterval n)
    (hJ : π.cutSet.Consecutive J) : ∃ k : Fin π.parts, π.part k = J := by
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hJ.1
  obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hJ.2.1
  have hjl : j < l := π.strict.lt_iff_lt.mp (by rw [hj, hl]; exact J.increasing)
  have hjp : j.val < π.parts := by
    have hb := l.isLt
    change j.val < l.val at hjl
    omega
  let k : Fin π.parts := ⟨j.val, hjp⟩
  have hk : k.castSucc = j := by apply Fin.ext; rfl
  have hleft : (π.part k).left = J.left := by change π.cut k.castSucc = J.left; rw [hk, hj]
  have hle : (π.part k).right ≤ J.right := by
    rw [← hl]
    apply π.strict.monotone
    change j.val + 1 ≤ l.val
    exact hjl
  have hright : (π.part k).right = J.right := by
    by_contra he
    have hlt : (π.part k).right < J.right := lt_of_le_of_ne hle he
    have hmem : (π.part k).right ∈ π.cutSet.cuts :=
      Finset.mem_image.mpr ⟨k.succ, Finset.mem_univ _, rfl⟩
    have hb : J.left < (π.part k).right := by rw [← hleft]; exact (π.part k).increasing
    exact hJ.2.2 _ hmem ⟨hb, hlt⟩
  exact ⟨k, BoundaryInterval.eq_of_endpoints hleft hright⟩

/-- The original part index domain is exactly all consecutive pairs of
actual cuts. This equivalence preserves the complete child interval. -/
def partConsecutiveEquiv (π : IntervalComposition I) :
    Fin π.parts ≃ {J : BoundaryInterval n // π.cutSet.Consecutive J} :=
  Equiv.ofBijective (fun k => ⟨π.part k, π.part_consecutive k⟩) ⟨by
    intro k l he
    exact π.part_injective (congrArg Subtype.val he), by
    intro J
    obtain ⟨k, hk⟩ := π.exists_part_of_consecutive J.val J.property
    exact ⟨k, Subtype.ext hk⟩⟩

/-- Every globally consecutive fine interval is contained in an outer part,
provided every outer cut is retained. An outer boundary cannot split it. -/
theorem consecutive_contained_in_part (π : IntervalComposition I)
    (T : BoundaryCutSet I) (hπ : π.cutSet.cuts ⊆ T.cuts)
    (J : BoundaryInterval n) (hJ : T.Consecutive J) :
    ∃ k : Fin π.parts, (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right := by
  have hleft := (T.bounds J.left hJ.1).1
  have hright := (T.bounds J.right hJ.2.1).2
  obtain ⟨k, hk⟩ := π.exists_halfOpen_part J.left hleft (lt_of_lt_of_le J.increasing hright)
  refine ⟨k, hk.1, ?_⟩
  by_contra h
  have hlt : (π.part k).right < J.right := lt_of_not_ge h
  have hmem : (π.part k).right ∈ T.cuts :=
    hπ (Finset.mem_image.mpr ⟨k.succ, Finset.mem_univ _, rfl⟩)
  exact hJ.2.2 _ hmem ⟨hk.2, hlt⟩

/-- A positive-length child interval can belong to only one outer part;
the possible shared endpoints do not create duplicate children. -/
theorem containing_part_unique (π : IntervalComposition I) (J : BoundaryInterval n)
    {k l : Fin π.parts}
    (hk : (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right)
    (hl : (π.part l).left ≤ J.left ∧ J.right ≤ (π.part l).right) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · have ho := π.part_order h
    have he : J.right ≤ J.left := le_trans hk.2 (le_trans ho hl.1)
    exact False.elim ((not_le_of_gt J.increasing) he)
  · exact h
  · have ho := π.part_order h
    have he : J.right ≤ J.left := le_trans hl.2 (le_trans ho hk.1)
    exact False.elim ((not_le_of_gt J.increasing) he)

end IntervalComposition

end
end SM

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
  rw [← Fintype.prod_sigma' (fun (k : Fin π.parts) (j : Fin (π.refinementInner T k).parts) =>
    X ((π.refinementInner T k).part j))]
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
  let τ : ∀ k : Fin π.parts, IntervalComposition (π.part k) :=
    fun k => π.refinementInner (π.flattenRefinement (fun k => (σ k).cutSet)) k
  have ht : τ = σ := funext (π.refinementInner_flatten σ)
  have hp := congrArg (fun η : ∀ k : Fin π.parts, IntervalComposition (π.part k) =>
    ∏ k : Fin π.parts, ∏ j : Fin (η k).parts, X ((η k).part j)) ht
  have h := π.prod_refined_children (π.flattenRefinement (fun k => (σ k).cutSet)) X
  exact hp.symm.trans h

end
end SM.IntervalComposition

#print axioms SM.IntervalComposition.inner_child_consecutive
#print axioms SM.IntervalComposition.exists_refined_child
#print axioms SM.IntervalComposition.refinedChildIndex_part
#print axioms SM.IntervalComposition.refinedChildIndex_injective
#print axioms SM.IntervalComposition.refinedChildIndex_surjective
#print axioms SM.IntervalComposition.refinedChildrenEquiv
#print axioms SM.IntervalComposition.prod_refined_children
#print axioms SM.IntervalComposition.refinementInner_flatten
#print axioms SM.IntervalComposition.prod_nested_children
