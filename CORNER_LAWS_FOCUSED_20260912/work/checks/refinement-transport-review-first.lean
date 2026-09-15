import SM.MarkedRefinement
import SM.InteriorCutIndex
import SM.NearFar
import SM.UnaryComposition
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
set_option pp.universes false

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

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

namespace BoundaryCutSet

/-- Two consecutive intervals starting at the same cut have the same next
cut, since either smaller right endpoint would intervene in the other. -/
theorem consecutive_eq_of_left (S : BoundaryCutSet I) {J K : BoundaryInterval n}
    (hJ : S.Consecutive J) (hK : S.Consecutive K) (hl : J.left = K.left) : J = K := by
  apply BoundaryInterval.eq_of_endpoints hl
  rcases lt_trichotomy J.right K.right with h | h | h
  · have hb : K.left < J.right := by rw [← hl]; exact J.increasing
    exact False.elim (hK.2.2 J.right hJ.2.1 ⟨hb, h⟩)
  · exact h
  · have hb : J.left < K.right := by rw [hl]; exact K.increasing
    exact False.elim (hJ.2.2 K.right hK.2.1 ⟨hb, h⟩)

/-- Two consecutive intervals ending at the same cut have the same previous
cut, by the same no-intervening-cut condition. -/
theorem consecutive_eq_of_right (S : BoundaryCutSet I) {J K : BoundaryInterval n}
    (hJ : S.Consecutive J) (hK : S.Consecutive K) (hr : J.right = K.right) : J = K := by
  apply BoundaryInterval.eq_of_endpoints _ hr
  rcases lt_trichotomy J.left K.left with h | h | h
  · have hb : K.left < J.right := by rw [hr]; exact K.increasing
    exact False.elim (hJ.2.2 K.left hK.1 ⟨h, hb⟩)
  · exact h
  · have hb : J.left < K.right := by rw [← hr]; exact J.increasing
    exact False.elim (hK.2.2 J.left hJ.1 ⟨h, hb⟩)

end BoundaryCutSet

namespace IncreasingBoundaryTriple

def leftInterval (t : IncreasingBoundaryTriple n) : BoundaryInterval n :=
  ⟨t.lower, t.middle, t.lower_middle⟩

def rightInterval (t : IncreasingBoundaryTriple n) : BoundaryInterval n :=
  ⟨t.middle, t.upper, t.middle_upper⟩

theorem eq_of_entries {t u : IncreasingBoundaryTriple n}
    (hl : t.lower = u.lower) (hm : t.middle = u.middle) (hu : t.upper = u.upper) : t = u := by
  cases t
  cases u
  cases hl
  cases hm
  cases hu
  rfl

/-- A consecutive triple is determined by its middle cut in the full cut
set. Both neighboring positions are forced, with no geometric hypothesis. -/
theorem eq_of_consecutive_middle (S : BoundaryCutSet I) {t u : IncreasingBoundaryTriple n}
    (htl : S.Consecutive t.leftInterval) (htr : S.Consecutive t.rightInterval)
    (hul : S.Consecutive u.leftInterval) (hur : S.Consecutive u.rightInterval)
    (hm : t.middle = u.middle) : t = u := by
  have hl := S.consecutive_eq_of_right htl hul hm
  have hr := S.consecutive_eq_of_left htr hur hm
  exact eq_of_entries (congrArg BoundaryInterval.left hl) hm (congrArg BoundaryInterval.right hr)

end IncreasingBoundaryTriple

namespace IntervalComposition

/-- The near triple's left interval is the part just before its middle cut. -/
theorem nearTriple_leftInterval (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    (π.nearTriple k).leftInterval = π.part ⟨k.val, by have := k.isLt; omega⟩ := rfl

/-- The near triple's right interval is the part just after its middle cut. -/
theorem nearTriple_rightInterval (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    (π.nearTriple k).rightInterval = π.part ⟨k.val + 1, by have := k.isLt; omega⟩ := rfl

theorem nearTriple_consecutive (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    π.cutSet.Consecutive (π.nearTriple k).leftInterval ∧
      π.cutSet.Consecutive (π.nearTriple k).rightInterval := by
  rw [nearTriple_leftInterval, nearTriple_rightInterval]
  exact ⟨π.part_consecutive _, π.part_consecutive _⟩

theorem nearTriple_middle_position (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    (π.nearTriple k).middle = π.interiorPosition k := rfl

/-- At a specified physical middle cut the raw composition uses exactly the
unique consecutive triple, so neighboring near-array samples are fixed. -/
theorem nearTriple_eq_of_consecutive (π : IntervalComposition I) (k : Fin (π.parts - 1))
    (t : IncreasingBoundaryTriple n)
    (hl : π.cutSet.Consecutive t.leftInterval) (hr : π.cutSet.Consecutive t.rightInterval)
    (hm : π.interiorPosition k = t.middle) : π.nearTriple k = t :=
  IncreasingBoundaryTriple.eq_of_consecutive_middle π.cutSet
    (π.nearTriple_consecutive k).1 (π.nearTriple_consecutive k).2 hl hr hm

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

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- Send an arbitrary set of interior indices to its actual marked cut
positions. Injectivity of the position map prevents duplicate marks. -/
def indexMarks (π : IntervalComposition I) (s : Finset (Fin (π.parts - 1))) : MarkedCuts π.cutSet :=
  ⟨s.image π.interiorPosition, by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    exact π.interiorPosition_mem k⟩

/-- Recover exactly the marked indices from a set of physical marked cuts. -/
def markIndices (π : IntervalComposition I) (m : MarkedCuts π.cutSet) : Finset (Fin (π.parts - 1)) :=
  Finset.univ.filter (fun k => π.interiorPosition k ∈ m.val)

theorem markIndices_indexMarks (π : IntervalComposition I) (s : Finset (Fin (π.parts - 1))) :
    π.markIndices (π.indexMarks s) = s := by
  ext k
  simp only [markIndices, indexMarks, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨l, hl, he⟩
    have h : l = k := π.interiorPosition_injective he
    subst l
    exact hl
  · intro hk
    exact ⟨k, hk, rfl⟩

theorem indexMarks_markIndices (π : IntervalComposition I) (m : MarkedCuts π.cutSet) :
    π.indexMarks (π.markIndices m) = m := by
  apply Subtype.ext
  ext x
  change x ∈ (π.markIndices m).image π.interiorPosition ↔ x ∈ m.val
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hk).2
  · intro hx
    obtain ⟨k, hk⟩ := (π.mem_interior_iff_exists_index x).mp (m.property hx)
    exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.symm ▸ hx⟩, hk⟩

/-- All index subsets and all physical marked subsets correspond exactly,
including the unary empty universe. -/
def marksIndexEquiv (π : IntervalComposition I) :
    Finset (Fin (π.parts - 1)) ≃ MarkedCuts π.cutSet where
  toFun := π.indexMarks
  invFun := π.markIndices
  left_inv := π.markIndices_indexMarks
  right_inv := π.indexMarks_markIndices

theorem position_mem_indexMarks (π : IntervalComposition I)
    (s : Finset (Fin (π.parts - 1))) (k : Fin (π.parts - 1)) :
    π.interiorPosition k ∈ (π.indexMarks s).val ↔ k ∈ s := by
  change π.interiorPosition k ∈ s.image π.interiorPosition ↔ k ∈ s
  constructor
  · intro h
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp h
    have hkl : l = k := π.interiorPosition_injective he
    subst l
    exact hl
  · intro h
    exact Finset.mem_image.mpr ⟨k, h, rfl⟩

/-- Complementary index selections map to exactly the unmarked physical
interior cuts, rather than the complement in the whole boundary domain. -/
theorem indexMarks_compl (π : IntervalComposition I) (s : Finset (Fin (π.parts - 1))) :
    (π.indexMarks sᶜ).val = π.cutSet.interior.val \ (π.indexMarks s).val := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_sdiff.mpr
    refine ⟨π.interiorPosition_mem k, ?_⟩
    intro hm
    exact (Finset.mem_compl.mp hk) ((π.position_mem_indexMarks s k).mp hm)
  · intro hx
    have hb := Finset.mem_sdiff.mp hx
    obtain ⟨k, hk⟩ := (π.mem_interior_iff_exists_index x).mp hb.1
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_compl.mpr ?_, hk⟩
    intro hks
    apply hb.2
    rw [← hk]
    exact (π.position_mem_indexMarks s k).mpr hks

/-- Products over selected cut indices preserve their actual physical
arguments under the marked-set bijection. -/
theorem prod_indexMarks {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (s : Finset (Fin (π.parts - 1))) (f : Fin n → R) :
    (∏ k ∈ s, f (π.interiorPosition k)) = ∏ x ∈ (π.indexMarks s).val, f x := by
  change (∏ k ∈ s, f (π.interiorPosition k)) = ∏ x ∈ s.image π.interiorPosition, f x
  symm
  exact Finset.prod_image (fun _ _ _ _ h => π.interiorPosition_injective h)

theorem prod_markIndices {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (m : MarkedCuts π.cutSet) (f : Fin n → R) :
    (∏ k ∈ π.markIndices m, f (π.interiorPosition k)) = ∏ x ∈ m.val, f x := by
  have h := π.prod_indexMarks (π.markIndices m) f
  rw [π.indexMarks_markIndices m] at h
  exact h

/-- Reindex a sum over every physical marking by all subsets of the exact
interior index universe. No marking is excluded or given multiplicity. -/
theorem sum_all_indexMarks {R : Type*} [AddCommMonoid R]
    (π : IntervalComposition I) (f : MarkedCuts π.cutSet → R) :
    (∑ s : Finset (Fin (π.parts - 1)), f (π.indexMarks s)) = ∑ m : MarkedCuts π.cutSet, f m :=
  Fintype.sum_equiv π.marksIndexEquiv _ _ (fun _ => rfl)

end
end SM.IntervalComposition

namespace RefinementTransportIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

-- Characterize the actual raw child intervals, including unique indexing.
theorem actual_parts_are_exact_consecutive_pairs (π : IntervalComposition I)
    (J : BoundaryInterval n) :
    π.cutSet.Consecutive J ↔ ∃! k : Fin π.parts, π.part k = J := by
  constructor
  · intro hJ
    obtain ⟨k, hk⟩ := π.exists_part_of_consecutive J hJ
    exact ⟨k, hk, fun l hl => π.part_injective (hl.trans hk.symm)⟩
  · rintro ⟨k, rfl, _⟩
    exact π.part_consecutive k

-- Every globally fine child has exactly one containing outer part.
theorem actual_fine_child_has_unique_outer (π : IntervalComposition I)
    (T : RefiningCutSet π) (J : BoundaryInterval n) (hJ : T.val.Consecutive J) :
    ∃! k : Fin π.parts, (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right := by
  obtain ⟨k, hk⟩ := π.consecutive_contained_in_part T.val T.property J hJ
  exact ⟨k, hk, fun l hl => π.containing_part_unique J hl hk⟩

-- A physical interior position determines one actual neighboring triple.
theorem actual_near_sample_unique (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    ∃! t : IncreasingBoundaryTriple n,
      π.cutSet.Consecutive t.leftInterval ∧ π.cutSet.Consecutive t.rightInterval ∧
        t.middle = π.interiorPosition k := by
  refine ⟨π.nearTriple k, ⟨(π.nearTriple_consecutive k).1,
    (π.nearTriple_consecutive k).2, π.nearTriple_middle_position k⟩, ?_⟩
  intro t ht
  exact (π.nearTriple_eq_of_consecutive k t ht.1 ht.2.1 ht.2.2.symm).symm

-- Any coefficient array therefore samples the exact same three physical positions.
theorem arbitrary_array_samples_actual_neighbors {R : Type*}
    (π : IntervalComposition I) (k : Fin (π.parts - 1)) (D : TripleArray n R)
    (t : IncreasingBoundaryTriple n)
    (hl : π.cutSet.Consecutive t.leftInterval) (hr : π.cutSet.Consecutive t.rightInterval)
    (hm : π.interiorPosition k = t.middle) : D (π.nearTriple k) = D t := by
  rw [π.nearTriple_eq_of_consecutive k t hl hr hm]

-- The chosen index equivalence preserves the full child interval.
theorem refined_index_keeps_interval (π : IntervalComposition I) (T : RefiningCutSet π)
    (a : Σ k : Fin π.parts, Fin (π.refinementInner T k).parts) :
    T.val.toComposition.part (π.refinedChildrenEquiv T a) =
      (π.refinementInner T a.1).part a.2 :=
  π.refinedChildIndex_part T a

-- The bijection also fixes the total number of children, so none is lost or repeated.
theorem child_count_is_sum_of_inner_counts (π : IntervalComposition I) (T : RefiningCutSet π) :
    (∑ k : Fin π.parts, (π.refinementInner T k).parts) = T.val.toComposition.parts := by
  have h := Fintype.card_congr (π.refinedChildrenEquiv T)
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

-- Recover the original raw part count and cut map, not just an equal set of endpoints.
theorem recovered_inner_has_raw_data (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) (k : Fin π.parts) :
    (π.refinementInner (π.flattenRefinement (fun k => (σ k).cutSet)) k).parts = (σ k).parts ∧
      HEq (π.refinementInner (π.flattenRefinement (fun k => (σ k).cutSet)) k).cut (σ k).cut := by
  rw [π.refinementInner_flatten σ k]
  exact ⟨rfl, HEq.rfl⟩

-- The actual source marked-refinement map, not an unrelated enumeration, has the same product.
theorem actual_marked_refinement_child_product {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k))
    (X : BoundaryInterval n → R) :
    (∏ k : Fin π.parts, ∏ j : Fin (σ k).parts, X ((σ k).part j)) =
      ∏ r : Fin (IntervalComposition.nestedMarkedCutEquiv I ⟨π, σ⟩).1.parts,
        X ((IntervalComposition.nestedMarkedCutEquiv I ⟨π, σ⟩).1.part r) :=
  π.prod_nested_children σ X

-- Unary inner compositions keep exactly their outer child coordinate.
theorem all_inner_unary_product {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (X : BoundaryInterval n → R) :
    (∏ k : Fin π.parts, X (π.part k)) =
      ∏ r : Fin (π.flattenCutSets
        (fun k => (IntervalComposition.single (π.part k)).cutSet)).toComposition.parts,
        X ((π.flattenCutSets
          (fun k => (IntervalComposition.single (π.part k)).cutSet)).toComposition.part r) := by
  simpa only [IntervalComposition.single_product] using
    π.prod_nested_children (fun k => IntervalComposition.single (π.part k)) X

-- Full/empty markings are the exact interior universe and empty set.
theorem empty_and_full_index_marks (π : IntervalComposition I) :
    (π.indexMarks ∅).val = ∅ ∧
      (π.indexMarks Finset.univ).val = π.cutSet.interior.val := by
  constructor
  · simp [IntervalComposition.indexMarks]
  · simpa [IntervalComposition.indexMarks] using π.indexMarks_compl ∅

-- Complementary marks never include either endpoint or an unrelated boundary position.
theorem unmarked_positions_are_exactly_relative (π : IntervalComposition I)
    (s : Finset (Fin (π.parts - 1))) (x : Fin n) (hx : x ∈ (π.indexMarks sᶜ).val) :
    I.left < x ∧ x < I.right ∧ x ∉ (π.indexMarks s).val := by
  rw [π.indexMarks_compl] at hx
  have h := Finset.mem_sdiff.mp hx
  exact ⟨(π.cutSet.interior.property x h.1).1,
    (π.cutSet.interior.property x h.1).2, h.2⟩

-- Both chosen and complementary products transport their actual physical arguments.
theorem marked_and_unmarked_product_transport {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (m : MarkedCuts π.cutSet) (f g : Fin n → R) :
    (∏ k ∈ π.markIndices m, f (π.interiorPosition k)) *
      (∏ k ∈ (π.markIndices m)ᶜ, g (π.interiorPosition k)) =
    (∏ x ∈ m.val, f x) * (∏ x ∈ π.cutSet.interior.val \ m.val, g x) := by
  rw [π.prod_markIndices, π.prod_indexMarks, π.indexMarks_compl, π.indexMarks_markIndices]

-- Every one of the 2^(parts-1) possible source markings occurs exactly once.
theorem all_markings_have_full_cardinality (π : IntervalComposition I) :
    Fintype.card (MarkedCuts π.cutSet) = 2 ^ (π.parts - 1) := by
  have h := Fintype.card_congr π.marksIndexEquiv
  simpa only [Fintype.card_finset, Fintype.card_fin] using h.symm

-- In the unary case the complete sum contains precisely the empty marking.
theorem unary_marking_sum {R : Type*} [AddCommMonoid R]
    (I : BoundaryInterval n) (f : MarkedCuts (IntervalComposition.single I).cutSet → R) :
    (∑ m : MarkedCuts (IntervalComposition.single I).cutSet, f m) =
      f ((IntervalComposition.single I).indexMarks ∅) := by
  rw [← (IntervalComposition.single I).sum_all_indexMarks f]
  change (∑ s : Finset (Fin 0), f ((IntervalComposition.single I).indexMarks s)) = _
  simp

end
end RefinementTransportIndependentReview

#check SM.BoundaryCutSet.Consecutive
#print axioms SM.BoundaryCutSet.Consecutive
#check SM.BoundaryInterval.eq_of_endpoints
#print axioms SM.BoundaryInterval.eq_of_endpoints
#check SM.BoundaryCutSet.consecutive_restrict_iff
#print axioms SM.BoundaryCutSet.consecutive_restrict_iff
#check SM.IntervalComposition.part_consecutive
#print axioms SM.IntervalComposition.part_consecutive
#check SM.IntervalComposition.part_injective
#print axioms SM.IntervalComposition.part_injective
#check SM.IntervalComposition.exists_part_of_consecutive
#print axioms SM.IntervalComposition.exists_part_of_consecutive
#check SM.IntervalComposition.partConsecutiveEquiv
#print axioms SM.IntervalComposition.partConsecutiveEquiv
#check SM.IntervalComposition.consecutive_contained_in_part
#print axioms SM.IntervalComposition.consecutive_contained_in_part
#check SM.IntervalComposition.containing_part_unique
#print axioms SM.IntervalComposition.containing_part_unique
#check SM.IncreasingBoundaryTriple.leftInterval
#print axioms SM.IncreasingBoundaryTriple.leftInterval
#check SM.IncreasingBoundaryTriple.rightInterval
#print axioms SM.IncreasingBoundaryTriple.rightInterval
#check SM.BoundaryCutSet.consecutive_eq_of_left
#print axioms SM.BoundaryCutSet.consecutive_eq_of_left
#check SM.BoundaryCutSet.consecutive_eq_of_right
#print axioms SM.BoundaryCutSet.consecutive_eq_of_right
#check SM.IncreasingBoundaryTriple.eq_of_entries
#print axioms SM.IncreasingBoundaryTriple.eq_of_entries
#check SM.IncreasingBoundaryTriple.eq_of_consecutive_middle
#print axioms SM.IncreasingBoundaryTriple.eq_of_consecutive_middle
#check SM.IntervalComposition.nearTriple_leftInterval
#print axioms SM.IntervalComposition.nearTriple_leftInterval
#check SM.IntervalComposition.nearTriple_rightInterval
#print axioms SM.IntervalComposition.nearTriple_rightInterval
#check SM.IntervalComposition.nearTriple_consecutive
#print axioms SM.IntervalComposition.nearTriple_consecutive
#check SM.IntervalComposition.nearTriple_middle_position
#print axioms SM.IntervalComposition.nearTriple_middle_position
#check SM.IntervalComposition.nearTriple_eq_of_consecutive
#print axioms SM.IntervalComposition.nearTriple_eq_of_consecutive
#check SM.IntervalComposition.refinementInner
#print axioms SM.IntervalComposition.refinementInner
#check SM.IntervalComposition.refinedChildIndex
#print axioms SM.IntervalComposition.refinedChildIndex
#check SM.IntervalComposition.inner_child_consecutive
#print axioms SM.IntervalComposition.inner_child_consecutive
#check SM.IntervalComposition.exists_refined_child
#print axioms SM.IntervalComposition.exists_refined_child
#check SM.IntervalComposition.refinedChildIndex_part
#print axioms SM.IntervalComposition.refinedChildIndex_part
#check SM.IntervalComposition.refinedChildIndex_injective
#print axioms SM.IntervalComposition.refinedChildIndex_injective
#check SM.IntervalComposition.refinedChildIndex_surjective
#print axioms SM.IntervalComposition.refinedChildIndex_surjective
#check SM.IntervalComposition.refinedChildrenEquiv
#print axioms SM.IntervalComposition.refinedChildrenEquiv
#check SM.IntervalComposition.prod_refined_children
#print axioms SM.IntervalComposition.prod_refined_children
#check SM.IntervalComposition.refinementInner_flatten
#print axioms SM.IntervalComposition.refinementInner_flatten
#check SM.IntervalComposition.prod_nested_children
#print axioms SM.IntervalComposition.prod_nested_children
#check SM.IntervalComposition.indexMarks
#print axioms SM.IntervalComposition.indexMarks
#check SM.IntervalComposition.markIndices
#print axioms SM.IntervalComposition.markIndices
#check SM.IntervalComposition.markIndices_indexMarks
#print axioms SM.IntervalComposition.markIndices_indexMarks
#check SM.IntervalComposition.indexMarks_markIndices
#print axioms SM.IntervalComposition.indexMarks_markIndices
#check SM.IntervalComposition.marksIndexEquiv
#print axioms SM.IntervalComposition.marksIndexEquiv
#check SM.IntervalComposition.position_mem_indexMarks
#print axioms SM.IntervalComposition.position_mem_indexMarks
#check SM.IntervalComposition.indexMarks_compl
#print axioms SM.IntervalComposition.indexMarks_compl
#check SM.IntervalComposition.prod_indexMarks
#print axioms SM.IntervalComposition.prod_indexMarks
#check SM.IntervalComposition.prod_markIndices
#print axioms SM.IntervalComposition.prod_markIndices
#check SM.IntervalComposition.sum_all_indexMarks
#print axioms SM.IntervalComposition.sum_all_indexMarks
#print SM.BoundaryCutSet.Consecutive
#print SM.IncreasingBoundaryTriple.leftInterval
#print SM.IncreasingBoundaryTriple.rightInterval
#print SM.IntervalComposition.refinementInner
#print SM.IntervalComposition.refinedChildIndex
#print SM.IntervalComposition.indexMarks
#print SM.IntervalComposition.markIndices
#print SM.IntervalComposition.partConsecutiveEquiv
#print SM.IntervalComposition.refinedChildrenEquiv
#print SM.IntervalComposition.marksIndexEquiv
#print axioms RefinementTransportIndependentReview.actual_parts_are_exact_consecutive_pairs
#print axioms RefinementTransportIndependentReview.actual_fine_child_has_unique_outer
#print axioms RefinementTransportIndependentReview.actual_near_sample_unique
#print axioms RefinementTransportIndependentReview.arbitrary_array_samples_actual_neighbors
#print axioms RefinementTransportIndependentReview.refined_index_keeps_interval
#print axioms RefinementTransportIndependentReview.child_count_is_sum_of_inner_counts
#print axioms RefinementTransportIndependentReview.recovered_inner_has_raw_data
#print axioms RefinementTransportIndependentReview.actual_marked_refinement_child_product
#print axioms RefinementTransportIndependentReview.all_inner_unary_product
#print axioms RefinementTransportIndependentReview.empty_and_full_index_marks
#print axioms RefinementTransportIndependentReview.unmarked_positions_are_exactly_relative
#print axioms RefinementTransportIndependentReview.marked_and_unmarked_product_transport
#print axioms RefinementTransportIndependentReview.all_markings_have_full_cardinality
#print axioms RefinementTransportIndependentReview.unary_marking_sum
