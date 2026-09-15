import SM.MarkedRefinement
import SM.InteriorCutIndex
import SM.GeometricNearFar
import SM.NearFarCutExpansion
import SM.TriangularPolynomial
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

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

namespace BoundaryCutSet

theorem mem_interior_iff (S : BoundaryCutSet I) (x : Fin n) :
    x ∈ S.interior.val ↔ x ∈ S.cuts ∧ I.left < x ∧ x < I.right := by
  constructor
  · intro h
    have hb := S.interior.property x h
    simp only [interior, Finset.mem_erase] at h
    exact ⟨h.2.2, hb⟩
  · rintro ⟨hx, hl, hr⟩
    simp only [interior, Finset.mem_erase]
    exact ⟨ne_of_lt hr, ne_of_gt hl, hx⟩

end BoundaryCutSet

namespace IntervalComposition

/-- Fine interior indices that are not cuts of the outer composition. -/
abbrev RefinementUnmarked (π : IntervalComposition I) (T : RefiningCutSet π) :=
  {r : Fin (T.val.toComposition.parts - 1) //
    T.val.toComposition.interiorPosition r ∉ π.cutSet.cuts}

/-- An inner interior cut is a fine interior cut and cannot be an outer cut:
it lies strictly inside one outer part. -/
theorem innerPosition_in_refinement (π : IntervalComposition I) (T : RefiningCutSet π)
    (k : Fin π.parts) (j : Fin ((π.refinementInner T k).parts - 1)) :
    (π.refinementInner T k).interiorPosition j ∈ T.val.interior.val ∧
      (π.refinementInner T k).interiorPosition j ∉ π.cutSet.cuts := by
  let x := (π.refinementInner T k).interiorPosition j
  have hx := (π.refinementInner T k).interiorPosition_mem j
  have hb := (π.refinementInner T k).cutSet.interior.property x hx
  have hc := ((π.refinementInner T k).cutSet.mem_interior_iff x).mp hx
  have he : (π.refinementInner T k).cutSet = π.unflattenCutSets T k :=
    BoundaryCutSet.toComposition_cutSet _
  have hmem : x ∈ (π.unflattenCutSets T k).cuts := by rw [← he]; exact hc.1
  have ht : x ∈ T.val.cuts := (Finset.mem_filter.mp hmem).1
  have hp := π.part_bounds k
  refine ⟨(T.val.mem_interior_iff x).mpr ⟨ht, lt_of_le_of_lt hp.1 hb.1,
    lt_of_lt_of_le hb.2 hp.2⟩, ?_⟩
  intro ho
  exact (π.part_consecutive k).2.2 x ho hb

/-- The fine index of the same actual physical inner cut. -/
def refinedInteriorIndex (π : IntervalComposition I) (T : RefiningCutSet π)
    (a : Σ k : Fin π.parts, Fin ((π.refinementInner T k).parts - 1)) :
    Fin (T.val.toComposition.parts - 1) :=
  T.val.toComposition.interiorPositionEquiv.symm
    ⟨(π.refinementInner T a.1).interiorPosition a.2, by
      rw [BoundaryCutSet.toComposition_cutSet]
      exact (π.innerPosition_in_refinement T a.1 a.2).1⟩

theorem refinedInteriorIndex_position (π : IntervalComposition I) (T : RefiningCutSet π)
    (a : Σ k : Fin π.parts, Fin ((π.refinementInner T k).parts - 1)) :
    T.val.toComposition.interiorPosition (π.refinedInteriorIndex T a) =
      (π.refinementInner T a.1).interiorPosition a.2 := by
  exact congrArg
    (fun y : {x : Fin n // x ∈ T.val.toComposition.cutSet.interior.val} => y.val)
    (T.val.toComposition.interiorPositionEquiv.apply_symm_apply _)

def refinedUnmarkedIndex (π : IntervalComposition I) (T : RefiningCutSet π)
    (a : Σ k : Fin π.parts, Fin ((π.refinementInner T k).parts - 1)) : RefinementUnmarked π T :=
  ⟨π.refinedInteriorIndex T a, by
    rw [π.refinedInteriorIndex_position T a]
    exact (π.innerPosition_in_refinement T a.1 a.2).2⟩

/-- Distinct inner cuts remain distinct: equal physical cuts first force
the same strict outer-part interior, then the same inner cut index. -/
theorem refinedUnmarkedIndex_injective (π : IntervalComposition I) (T : RefiningCutSet π) :
    Function.Injective (π.refinedUnmarkedIndex T) := by
  rintro ⟨k, j⟩ ⟨l, t⟩ h
  have hi : π.refinedInteriorIndex T ⟨k, j⟩ = π.refinedInteriorIndex T ⟨l, t⟩ :=
    congrArg (fun r : RefinementUnmarked π T => r.val) h
  have hx : (π.refinementInner T k).interiorPosition j =
      (π.refinementInner T l).interiorPosition t := by
    rw [← π.refinedInteriorIndex_position T ⟨k, j⟩,
      ← π.refinedInteriorIndex_position T ⟨l, t⟩, hi]
  have hk := (π.refinementInner T k).cutSet.interior.property _
    ((π.refinementInner T k).interiorPosition_mem j)
  have hl := (π.refinementInner T l).cutSet.interior.property _
    ((π.refinementInner T l).interiorPosition_mem t)
  have hkl : k = l := by
    apply π.part_interior_unique ((π.refinementInner T k).interiorPosition j) hk
    rw [hx]
    exact hl
  subst l
  have hj : j = t := (π.refinementInner T k).interiorPosition_injective hx
  subst t
  rfl

/-- Every unmarked fine cut lies strictly inside an outer part and occurs
as an interior cut of that part's exact restricted composition. -/
theorem refinedUnmarkedIndex_surjective (π : IntervalComposition I) (T : RefiningCutSet π) :
    Function.Surjective (π.refinedUnmarkedIndex T) := by
  intro r
  let x := T.val.toComposition.interiorPosition r.val
  have hx : x ∈ T.val.interior.val := by
    have h := T.val.toComposition.interiorPosition_mem r.val
    rw [BoundaryCutSet.toComposition_cutSet] at h
    exact h
  have hb := T.val.interior.property x hx
  obtain ⟨k, hk⟩ := π.exists_halfOpen_part x (le_of_lt hb.1) hb.2
  have hleft : (π.part k).left < x := by
    apply lt_of_le_of_ne hk.1
    intro he
    apply r.property
    change x ∈ π.cutSet.cuts
    rw [← he]
    exact Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, rfl⟩
  have ht : x ∈ T.val.cuts := ((T.val.mem_interior_iff x).mp hx).1
  have hs : x ∈ (π.unflattenCutSets T k).cuts :=
    Finset.mem_filter.mpr ⟨ht, hk.1, le_of_lt hk.2⟩
  have hi : x ∈ (π.refinementInner T k).cutSet.interior.val := by
    apply ((π.refinementInner T k).cutSet.mem_interior_iff x).mpr
    refine ⟨?_, hleft, hk.2⟩
    rw [show (π.refinementInner T k).cutSet = π.unflattenCutSets T k from
      BoundaryCutSet.toComposition_cutSet _]
    exact hs
  obtain ⟨j, hj⟩ := ((π.refinementInner T k).mem_interior_iff_exists_index x).mp hi
  refine ⟨⟨k, j⟩, ?_⟩
  apply Subtype.ext
  apply T.val.toComposition.interiorPosition_injective
  rw [show (π.refinedUnmarkedIndex T ⟨k, j⟩).val = π.refinedInteriorIndex T ⟨k, j⟩ from rfl,
    π.refinedInteriorIndex_position T ⟨k, j⟩]
  exact hj

/-- All inner interior cuts are exactly the unmarked fine cuts. -/
def refinedUnmarkedEquiv (π : IntervalComposition I) (T : RefiningCutSet π) :
    (Σ k : Fin π.parts, Fin ((π.refinementInner T k).parts - 1)) ≃ RefinementUnmarked π T :=
  Equiv.ofBijective (π.refinedUnmarkedIndex T)
    ⟨π.refinedUnmarkedIndex_injective T, π.refinedUnmarkedIndex_surjective T⟩

/-- The near triple is preserved at an inner cut. Both of its neighboring
child intervals are globally consecutive, so the middle cut determines them. -/
theorem inner_nearTriple_transport (π : IntervalComposition I) (T : RefiningCutSet π)
    (k : Fin π.parts) (j : Fin ((π.refinementInner T k).parts - 1)) :
    T.val.toComposition.nearTriple (π.refinedInteriorIndex T ⟨k, j⟩) =
      (π.refinementInner T k).nearTriple j := by
  apply T.val.toComposition.nearTriple_eq_of_consecutive
  · rw [BoundaryCutSet.toComposition_cutSet, nearTriple_leftInterval]
    exact π.inner_child_consecutive T k _
  · rw [BoundaryCutSet.toComposition_cutSet, nearTriple_rightInterval]
    exact π.inner_child_consecutive T k _
  · exact π.refinedInteriorIndex_position T ⟨k, j⟩

/-- Products of arbitrary neighboring-triple factors are preserved exactly.
Taking f(t)=D(t)/2 supplies every inner near-only factor of the source sum. -/
theorem prod_inner_nearTriples {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (T : RefiningCutSet π) (f : IncreasingBoundaryTriple n → R) :
    (∏ k : Fin π.parts, ∏ j : Fin ((π.refinementInner T k).parts - 1),
      f ((π.refinementInner T k).nearTriple j)) =
      ∏ r : RefinementUnmarked π T, f (T.val.toComposition.nearTriple r.val) := by
  rw [← Fintype.prod_sigma' (fun (k : Fin π.parts)
    (j : Fin ((π.refinementInner T k).parts - 1)) => f ((π.refinementInner T k).nearTriple j))]
  exact Fintype.prod_equiv (π.refinedUnmarkedEquiv T) _ _
    (fun a => congrArg f (π.inner_nearTriple_transport T a.1 a.2).symm)

end IntervalComposition

end
end SM

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- Fine interior indices that are cuts of the outer composition. -/
abbrev RefinementMarked (π : IntervalComposition I) (T : RefiningCutSet π) :=
  {r : Fin (T.val.toComposition.parts - 1) //
    T.val.toComposition.interiorPosition r ∈ π.cutSet.cuts}

/-- Every outer interior cut remains a fine interior cut, with both global
endpoints fixed by the source interval. -/
theorem outerPosition_in_refinement (π : IntervalComposition I) (T : RefiningCutSet π)
    (j : Fin (π.parts - 1)) : π.interiorPosition j ∈ T.val.interior.val :=
  (BoundaryCutSet.cuts_subset_iff_interior_subset π.cutSet T.val).mp T.property
    (π.interiorPosition_mem j)

def refinedOuterIndex (π : IntervalComposition I) (T : RefiningCutSet π)
    (j : Fin (π.parts - 1)) : Fin (T.val.toComposition.parts - 1) :=
  T.val.toComposition.interiorPositionEquiv.symm ⟨π.interiorPosition j, by
    rw [BoundaryCutSet.toComposition_cutSet]
    exact π.outerPosition_in_refinement T j⟩

theorem refinedOuterIndex_position (π : IntervalComposition I) (T : RefiningCutSet π)
    (j : Fin (π.parts - 1)) :
    T.val.toComposition.interiorPosition (π.refinedOuterIndex T j) = π.interiorPosition j := by
  exact congrArg
    (fun y : {x : Fin n // x ∈ T.val.toComposition.cutSet.interior.val} => y.val)
    (T.val.toComposition.interiorPositionEquiv.apply_symm_apply _)

def refinedMarkedIndex (π : IntervalComposition I) (T : RefiningCutSet π)
    (j : Fin (π.parts - 1)) : RefinementMarked π T :=
  ⟨π.refinedOuterIndex T j, by
    rw [π.refinedOuterIndex_position T j]
    exact ((π.cutSet.mem_interior_iff _).mp (π.interiorPosition_mem j)).1⟩

theorem refinedMarkedIndex_injective (π : IntervalComposition I) (T : RefiningCutSet π) :
    Function.Injective (π.refinedMarkedIndex T) := by
  intro j l h
  have hi : π.refinedOuterIndex T j = π.refinedOuterIndex T l :=
    congrArg (fun r : RefinementMarked π T => r.val) h
  apply π.interiorPosition_injective
  rw [← π.refinedOuterIndex_position T j, ← π.refinedOuterIndex_position T l, hi]

/-- A marked fine cut is a genuine outer interior cut, not a global
endpoint; hence it occurs exactly once in the outer index domain. -/
theorem refinedMarkedIndex_surjective (π : IntervalComposition I) (T : RefiningCutSet π) :
    Function.Surjective (π.refinedMarkedIndex T) := by
  intro r
  let x := T.val.toComposition.interiorPosition r.val
  have hx := T.val.toComposition.interiorPosition_mem r.val
  have hb := T.val.toComposition.cutSet.interior.property x hx
  have ho : x ∈ π.cutSet.interior.val := (π.cutSet.mem_interior_iff x).mpr ⟨r.property, hb⟩
  obtain ⟨j, hj⟩ := (π.mem_interior_iff_exists_index x).mp ho
  refine ⟨j, ?_⟩
  apply Subtype.ext
  apply T.val.toComposition.interiorPosition_injective
  rw [show (π.refinedMarkedIndex T j).val = π.refinedOuterIndex T j from rfl,
    π.refinedOuterIndex_position T j]
  exact hj

/-- The outer interior indices are exactly all marked fine indices. -/
def refinedMarkedEquiv (π : IntervalComposition I) (T : RefiningCutSet π) :
    Fin (π.parts - 1) ≃ RefinementMarked π T :=
  Equiv.ofBijective (π.refinedMarkedIndex T)
    ⟨π.refinedMarkedIndex_injective T, π.refinedMarkedIndex_surjective T⟩

/-- Far samples retain the global interval endpoints and the same marked
middle cut. They do not use the endpoints of an inner part. -/
theorem outer_farTriple_transport (π : IntervalComposition I) (T : RefiningCutSet π)
    (j : Fin (π.parts - 1)) :
    T.val.toComposition.farTriple (π.refinedOuterIndex T j) = π.farTriple j := by
  apply IncreasingBoundaryTriple.eq_of_entries
  · rfl
  · exact π.refinedOuterIndex_position T j
  · rfl

/-- Arbitrary far-triple products are exactly the marked fine product.
Taking f(t)=-H(t)/2 supplies the source outer far-only factors. -/
theorem prod_outer_farTriples {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (T : RefiningCutSet π) (f : IncreasingBoundaryTriple n → R) :
    (∏ j : Fin (π.parts - 1), f (π.farTriple j)) =
      ∏ r : RefinementMarked π T, f (T.val.toComposition.farTriple r.val) :=
  Fintype.prod_equiv (π.refinedMarkedEquiv T) _ _
    (fun j => congrArg f (π.outer_farTriple_transport T j).symm)

end
end SM.IntervalComposition

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- The actual outer interior cuts, viewed as marks of the fine composition. -/
def refinementMarks (π : IntervalComposition I) (T : RefiningCutSet π) :
    MarkedCuts T.val.toComposition.cutSet :=
  ⟨π.cutSet.interior.val, by
    rw [BoundaryCutSet.toComposition_cutSet]
    exact (BoundaryCutSet.cuts_subset_iff_interior_subset _ _).mp T.property⟩

/-- Recover the marked fine indices from their physical outer cut positions. -/
def refinementMarkIndices (π : IntervalComposition I) (T : RefiningCutSet π) :
    Finset (Fin (T.val.toComposition.parts - 1)) :=
  T.val.toComposition.markIndices (π.refinementMarks T)

theorem mem_refinementMarkIndices (π : IntervalComposition I) (T : RefiningCutSet π)
    (r : Fin (T.val.toComposition.parts - 1)) :
    r ∈ π.refinementMarkIndices T ↔
      T.val.toComposition.interiorPosition r ∈ π.cutSet.cuts := by
  change (r ∈ Finset.univ.filter (fun r =>
    T.val.toComposition.interiorPosition r ∈ π.cutSet.interior.val)) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [π.cutSet.mem_interior_iff]
  have hb := T.val.toComposition.cutSet.interior.property _
    (T.val.toComposition.interiorPosition_mem r)
  exact ⟨And.left, fun h => ⟨h, hb⟩⟩

/-- Reindex the marked subtype product by its exact finite set of indices. -/
theorem prod_refinementMarked {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (T : RefiningCutSet π)
    (f : Fin (T.val.toComposition.parts - 1) → R) :
    (∏ r : RefinementMarked π T, f r.val) = ∏ r ∈ π.refinementMarkIndices T, f r :=
  (Finset.prod_subtype _ (π.mem_refinementMarkIndices T) f).symm

/-- The complementary index set is exactly all inner, unmarked cuts. -/
theorem prod_refinementUnmarked {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (T : RefiningCutSet π)
    (f : Fin (T.val.toComposition.parts - 1) → R) :
    (∏ r : RefinementUnmarked π T, f r.val) = ∏ r ∈ (π.refinementMarkIndices T)ᶜ, f r := by
  symm
  apply Finset.prod_subtype
  intro r
  rw [Finset.mem_compl, π.mem_refinementMarkIndices T]

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

theorem nearFarWeight_near_only (π : IntervalComposition I) (D : TripleArray n R) :
    π.nearFarWeight D 0 = ∏ r : Fin (π.parts - 1), D (π.nearTriple r) * ⅟ (2 : R) := by
  simp only [nearFarWeight, Pi.zero_apply, sub_zero]

theorem nearFarWeight_far_only (π : IntervalComposition I) (H : TripleArray n R) :
    π.nearFarWeight 0 H = ∏ r : Fin (π.parts - 1), -H (π.farTriple r) * ⅟ (2 : R) := by
  simp only [nearFarWeight, Pi.zero_apply, zero_sub]

/-- Every inner near-only coefficient supplies precisely an unmarked factor. -/
theorem prod_inner_near_weights (π : IntervalComposition I) (T : RefiningCutSet π)
    (D : TripleArray n R) :
    (∏ k : Fin π.parts, (π.refinementInner T k).nearFarWeight D 0) =
      ∏ r ∈ (π.refinementMarkIndices T)ᶜ,
        D (T.val.toComposition.nearTriple r) * ⅟ (2 : R) := by
  simp only [nearFarWeight_near_only]
  rw [π.prod_inner_nearTriples T (fun t => D t * ⅟ (2 : R))]
  exact π.prod_refinementUnmarked T (fun r => D (T.val.toComposition.nearTriple r) * ⅟ (2 : R))

/-- The outer far-only coefficient supplies precisely the marked factors,
each evaluated with the original global endpoints. -/
theorem outer_far_weight (π : IntervalComposition I) (T : RefiningCutSet π)
    (H : TripleArray n R) :
    π.nearFarWeight 0 H = ∏ r ∈ π.refinementMarkIndices T,
      -H (T.val.toComposition.farTriple r) * ⅟ (2 : R) := by
  rw [nearFarWeight_far_only, π.prod_outer_farTriples T (fun t => -H t * ⅟ (2 : R))]
  exact π.prod_refinementMarked T (fun r => -H (T.val.toComposition.farTriple r) * ⅟ (2 : R))

/-- Exact transport of one full nested summand, including every child
coordinate and every near or far factor. Unary cases use the same formula. -/
theorem nested_summand_transport (π : IntervalComposition I) (T : RefiningCutSet π)
    (D H : TripleArray n R) (X : IntervalArray n R) :
    π.nearFarWeight 0 H *
        (∏ k : Fin π.parts, (π.refinementInner T k).nearFarWeight D 0 *
          ∏ j : Fin ((π.refinementInner T k).parts), X ((π.refinementInner T k).part j)) =
      ((∏ r ∈ π.refinementMarkIndices T, -H (T.val.toComposition.farTriple r) * ⅟ (2 : R)) *
        (∏ r ∈ (π.refinementMarkIndices T)ᶜ, D (T.val.toComposition.nearTriple r) * ⅟ (2 : R))) *
          ∏ j : Fin T.val.toComposition.parts, X (T.val.toComposition.part j) := by
  rw [Finset.prod_mul_distrib]
  rw [π.prod_inner_near_weights T D, π.prod_refined_children T X, π.outer_far_weight T H]
  exact (mul_assoc _ _ _).symm

end
end SM.IntervalComposition

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- Transporting a marking between equal cut sets preserves its physical positions. -/
theorem BoundaryCutSet.marked_transport_val {S T : BoundaryCutSet I} (h : S = T)
    (m : MarkedCuts S) : (h ▸ m : MarkedCuts T).val = m.val := by
  subst T
  rfl

namespace IntervalComposition

/-- The full marked-refinement equivalence records exactly the outer interior
cuts as marks, including when the final dependent marking type is transported. -/
theorem nestedMarkedCutEquiv_marks (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) :
    (nestedMarkedCutEquiv I ⟨π, σ⟩).2.val = π.cutSet.interior.val := by
  let T := π.flattenCutSets (fun k => (σ k).cutSet)
  let m : MarkedCuts T := ⟨π.cutSet.interior.val,
    (BoundaryCutSet.cuts_subset_iff_interior_subset π.cutSet T).mp
      (π.outer_cuts_subset_flatten (fun k => (σ k).cutSet))⟩
  change (T.toComposition_cutSet.symm ▸ m : MarkedCuts T.toComposition.cutSet).val = _
  exact BoundaryCutSet.marked_transport_val T.toComposition_cutSet.symm m

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- One summand in the actual expanded composite F_H(G_D(X)). -/
def nestedSummand (D H : TripleArray n R) (X : IntervalArray n R)
    (π : IntervalComposition I) (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) : R :=
  π.nearFarWeight 0 H * ∏ k : Fin π.parts,
    (σ k).nearFarWeight D 0 * ∏ j : Fin (σ k).parts, X ((σ k).part j)

/-- One refined summand for an arbitrary set of physical marked cuts. -/
def markedSummand (D H : TripleArray n R) (X : IntervalArray n R)
    (ρ : IntervalComposition I) (m : MarkedCuts ρ.cutSet) : R :=
  ((∏ r ∈ ρ.markIndices m, -H (ρ.farTriple r) * ⅟ (2 : R)) *
    (∏ r ∈ (ρ.markIndices m)ᶜ, D (ρ.nearTriple r) * ⅟ (2 : R))) *
      ∏ j : Fin ρ.parts, X (ρ.part j)

/-- The actual source indexing equivalence preserves the complete summand
for any original family of raw inner compositions. -/
theorem nestedSummand_eq_markedSummand (D H : TripleArray n R) (X : IntervalArray n R)
    (π : IntervalComposition I) (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) :
    nestedSummand D H X π σ =
      markedSummand D H X (nestedMarkedCutEquiv I ⟨π, σ⟩).1
        (nestedMarkedCutEquiv I ⟨π, σ⟩).2 := by
  let T := π.flattenRefinement (fun k => (σ k).cutSet)
  have hm : (nestedMarkedCutEquiv I ⟨π, σ⟩).2 = π.refinementMarks T :=
    Subtype.ext (π.nestedMarkedCutEquiv_marks σ)
  rw [hm]
  have ht : (fun k => π.refinementInner T k) = σ :=
    funext (π.refinementInner_flatten σ)
  have hp := π.nested_summand_transport T D H X
  have hh := congrArg (fun η : ∀ k : Fin π.parts, IntervalComposition (π.part k) =>
    ∏ k : Fin π.parts, (η k).nearFarWeight D 0 *
      ∏ j : Fin (η k).parts, X ((η k).part j)) ht
  rw [hh] at hp
  exact hp

/-- Summing every possible marking produces the original near-far weight,
with the refined child-coordinate product held fixed. -/
theorem sum_markedSummand (D H : TripleArray n R) (X : IntervalArray n R)
    (ρ : IntervalComposition I) :
    (∑ m : MarkedCuts ρ.cutSet, markedSummand D H X ρ m) =
      ρ.nearFarWeight D H * ∏ j : Fin ρ.parts, X (ρ.part j) := by
  rw [← ρ.sum_all_indexMarks (markedSummand D H X ρ)]
  simp only [markedSummand, markIndices_indexMarks]
  rw [← Finset.sum_mul, ← nearFarWeight_marked_expansion]

end IntervalComposition

open IntervalComposition
variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Source factorization on every interval, over the full allowed coefficient
ring and all arrays. Distributivity expands the actual composite; the exact
source equivalence reindexes its full summands; all markings then recombine. -/
theorem nearFar_factorization_coordinate (D H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    farTransform H (nearTransform D X) I = nearFarTransform D H X I := by
  classical
  calc
    farTransform H (nearTransform D X) I =
        ∑ π : IntervalComposition I,
          ∑ σ : ∀ k : Fin π.parts, IntervalComposition (π.part k), nestedSummand D H X π σ := by
      simp only [farTransform, nearTransform, nearFarTransform, Fintype.prod_sum,
        Finset.mul_sum, nestedSummand]
    _ = ∑ a : (Σ π : IntervalComposition I,
        ∀ k : Fin π.parts, IntervalComposition (π.part k)), nestedSummand D H X a.1 a.2 :=
      (Fintype.sum_sigma' (nestedSummand D H X)).symm
    _ = ∑ b : (Σ ρ : IntervalComposition I, MarkedCuts ρ.cutSet),
        markedSummand D H X b.1 b.2 :=
      Fintype.sum_equiv (nestedMarkedCutEquiv I) _ _
        (fun a => nestedSummand_eq_markedSummand D H X a.1 a.2)
    _ = ∑ ρ : IntervalComposition I, ∑ m : MarkedCuts ρ.cutSet,
        markedSummand D H X ρ m := Fintype.sum_sigma' (markedSummand D H X)
    _ = ∑ ρ : IntervalComposition I,
        ρ.nearFarWeight D H * ∏ j : Fin ρ.parts, X (ρ.part j) := by
      apply Finset.sum_congr rfl
      intro ρ _
      exact sum_markedSummand D H X ρ
    _ = nearFarTransform D H X I := rfl

/-- The complete source transform is the far-only transform composed with
the near-only transform; this is an equality of the full polynomial maps. -/
theorem nearFar_factorization (D H : TripleArray n R) :
    nearFarTransform D H = farTransform H ∘ nearTransform D := by
  funext X I
  exact (nearFar_factorization_coordinate D H X I).symm

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Factorization and inverse uniqueness identify the entire near-only array
of any solution, for arbitrary right-hand side and independent arrays. -/
theorem nearTransform_of_nearFar_solution (D H : TripleArray n R)
    (X Y : IntervalArray n R) (h : nearFarTransform D H X = Y) :
    nearTransform D X = nearFarInverse 0 H Y := by
  apply nearFar_solution_unique 0 H
  calc
    nearFarTransform 0 H (nearTransform D X) = nearFarTransform D H X := by
      funext I
      exact nearFar_factorization_coordinate D H X I
    _ = Y := h

/-- The whole output with reversed far signs is determined by H and the
right-hand side. No claim of independence is made for individual tree terms. -/
theorem reversedFar_output_of_solution (D H : TripleArray n R)
    (X Y : IntervalArray n R) (h : nearFarTransform D H X = Y) :
    nearFarTransform D (-H) X = farTransform (-H) (nearFarInverse 0 H Y) := by
  have hc := nearTransform_of_nearFar_solution D H X Y h
  funext I
  rw [← nearFar_factorization_coordinate D (-H) X I, hc]

/-- Changing D while keeping H and the target fixed leaves the complete
reversed-far output unchanged, even though the two input arrays may differ. -/
theorem complete_output_near_independent (D₁ D₂ H : TripleArray n R)
    (X₁ X₂ Y : IntervalArray n R)
    (h₁ : nearFarTransform D₁ H X₁ = Y) (h₂ : nearFarTransform D₂ H X₂ = Y) :
    nearFarTransform D₁ (-H) X₁ = nearFarTransform D₂ (-H) X₂ := by
  rw [reversedFar_output_of_solution D₁ H X₁ Y h₁,
    reversedFar_output_of_solution D₂ H X₂ Y h₂]

def farOnlyCoordinates (H : TripleArray n R) : IntervalArray n R :=
  nearFarInverse 0 H boundaryUnitArray

def farOnlyOutput (H : TripleArray n R) : IntervalArray n R :=
  farTransform (-H) (farOnlyCoordinates H)

theorem farOnlyCoordinates_equation (H : TripleArray n R) :
    farTransform H (farOnlyCoordinates H) = boundaryUnitArray :=
  nearFarTransform_inverse 0 H boundaryUnitArray

/-- The source geometric open sums yield the same complete far-only output. -/
theorem geometric_farOnly_output (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    nearFarTransform (geometricBoundaryArray (R := R) P g) (-geometricBoundaryArray P g)
      (fun I => (openTreeSum P hP g I : R)) = farOnlyOutput (geometricBoundaryArray P g) :=
  reversedFar_output_of_solution _ _ _ _ (geometric_nearFar_open P hP g)

/-- The original rooted tree coefficient, at its specified root, is the
full-interval coordinate of the far-only output. -/
theorem treeCoefficient_farOnly (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) :
    (treeCoefficient P hP g hn : R) =
      farOnlyOutput (geometricBoundaryArray P g) (fullBoundaryInterval hn) := by
  rw [geometric_nearFar_root P hP g hn, geometric_farOnly_output P hP g]

/-- Every allowed transform is the identity on a one-leaf coordinate, since
there is no nonunary composition of that interval. -/
theorem nearFarTransform_leaf (D H : TripleArray n R) (X : IntervalArray n R)
    (I : BoundaryInterval n) (hI : I.leaves = 1) : nearFarTransform D H X I = X I := by
  letI : IsEmpty {π : IntervalComposition I // 2 ≤ π.parts} :=
    ⟨fun π => by have := π.val.parts_eq_one_of_leaves_eq_one hI; have := π.property; omega⟩
  rw [nearFarTransform_eq_triangular]
  simp [triangularTransform]

theorem boundaryUnitArray_leaf (I : BoundaryInterval n) (hI : I.leaves = 1) :
    boundaryUnitArray (R := R) I = 1 := by
  have hi := I.increasing
  have he : I.right.val = I.left.val + 1 := by
    unfold BoundaryInterval.leaves at hI
    change I.left.val < I.right.val at hi
    omega
  simp [boundaryUnitArray, he]

theorem farOnlyCoordinates_leaf (H : TripleArray n R) (I : BoundaryInterval n)
    (hI : I.leaves = 1) : farOnlyCoordinates H I = 1 := by
  have hc := congrFun (farOnlyCoordinates_equation H) I
  change nearFarTransform 0 H (farOnlyCoordinates H) I = boundaryUnitArray I at hc
  rw [nearFarTransform_leaf 0 H _ I hI, boundaryUnitArray_leaf I hI] at hc
  exact hc

/-- The two one-leaf values are both one. This is the source's open-word
convention; no two-vertex polygon amplitude is introduced. -/
theorem farOnly_leaf_values (H : TripleArray n R) (I : BoundaryInterval n)
    (hI : I.leaves = 1) :
    farTransform H (farOnlyCoordinates H) I = 1 ∧ farOnlyOutput H I = 1 := by
  constructor
  · rw [farOnlyCoordinates_equation, boundaryUnitArray_leaf I hI]
  · change nearFarTransform 0 (-H) (farOnlyCoordinates H) I = 1
    rw [nearFarTransform_leaf 0 (-H) _ I hI, farOnlyCoordinates_leaf H I hI]

/-- The ordinary far-transform coordinate vanishes on each nonleaf interval. -/
theorem farOnly_nonleaf_E (H : TripleArray n R) (I : BoundaryInterval n)
    (hI : 2 ≤ I.leaves) : farTransform H (farOnlyCoordinates H) I = 0 := by
  rw [farOnlyCoordinates_equation]
  have he : ¬ I.right.val = I.left.val + 1 := by
    unfold BoundaryInterval.leaves at hI
    omega
  simp [boundaryUnitArray, he]

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

namespace BoundaryInterval

/-- Translate a local position of the contiguous word J into its physical
position in the original boundary word. No intermediate position is omitted. -/
def globalPosition (J : BoundaryInterval n) (k : Fin (J.leaves + 1)) : Fin n :=
  ⟨J.left.val + k.val, by
    have hk := k.isLt
    have hr := J.right.isLt
    have hj := J.increasing
    unfold leaves at hk
    change J.left.val < J.right.val at hj
    omega⟩

theorem globalPosition_strict (J : BoundaryInterval n) : StrictMono J.globalPosition := by
  intro a b hab
  change J.left.val + a.val < J.left.val + b.val
  exact Nat.add_lt_add_left hab _

theorem globalPosition_bounds (J : BoundaryInterval n) (k : Fin (J.leaves + 1)) :
    J.left ≤ J.globalPosition k ∧ J.globalPosition k ≤ J.right := by
  have hk := k.isLt
  have hj := J.increasing
  unfold leaves at hk
  change J.left.val < J.right.val at hj
  change J.left.val ≤ J.left.val + k.val ∧ J.left.val + k.val ≤ J.right.val
  omega

/-- Subtract J's left position from a physical position known to lie in J. -/
def localPosition (J : BoundaryInterval n) (x : Fin n) (hl : J.left ≤ x) (hr : x ≤ J.right) :
    Fin (J.leaves + 1) :=
  ⟨x.val - J.left.val, by
    unfold leaves
    change J.left.val ≤ x.val at hl
    change x.val ≤ J.right.val at hr
    omega⟩

theorem global_localPosition (J : BoundaryInterval n) (x : Fin n)
    (hl : J.left ≤ x) (hr : x ≤ J.right) : J.globalPosition (J.localPosition x hl hr) = x := by
  apply Fin.ext
  change J.left.val + (x.val - J.left.val) = x.val
  change J.left.val ≤ x.val at hl
  omega

theorem local_globalPosition (J : BoundaryInterval n) (k : Fin (J.leaves + 1)) :
    J.localPosition (J.globalPosition k) (J.globalPosition_bounds k).1
      (J.globalPosition_bounds k).2 = k := by
  apply Fin.ext
  change J.left.val + k.val - J.left.val = k.val
  omega

/-- Translate an arbitrary subinterval of the local word to the same physical
subinterval in the original word. -/
def liftInterval (J : BoundaryInterval n) (K : BoundaryInterval (J.leaves + 1)) : BoundaryInterval n where
  left := J.globalPosition K.left
  right := J.globalPosition K.right
  increasing := J.globalPosition_strict K.increasing

def liftTriple (J : BoundaryInterval n) (t : IncreasingBoundaryTriple (J.leaves + 1)) :
    IncreasingBoundaryTriple n where
  lower := J.globalPosition t.lower
  middle := J.globalPosition t.middle
  upper := J.globalPosition t.upper
  lower_middle := J.globalPosition_strict t.lower_middle
  middle_upper := J.globalPosition_strict t.middle_upper

end BoundaryInterval

namespace IntervalComposition

theorem eq_of_parts_cut {I : BoundaryInterval n} {π ρ : IntervalComposition I}
    (hp : π.parts = ρ.parts) (hc : HEq π.cut ρ.cut) : π = ρ := by
  cases π
  cases ρ
  cases hp
  cases hc
  rfl

theorem cut_bounds {I : BoundaryInterval n} (π : IntervalComposition I) (k : Fin (π.parts + 1)) :
    I.left ≤ π.cut k ∧ π.cut k ≤ I.right := by
  constructor
  · rw [← π.first]
    exact π.strict.monotone (Fin.zero_le k)
  · rw [← π.last]
    exact π.strict.monotone (Fin.le_last k)

/-- Preserve every part and cut index while translating all physical positions. -/
def liftComposition (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) : IntervalComposition (J.liftInterval K) where
  parts := π.parts
  parts_pos := π.parts_pos
  cut := fun k => J.globalPosition (π.cut k)
  strict := J.globalPosition_strict.comp π.strict
  first := congrArg J.globalPosition π.first
  last := congrArg J.globalPosition π.last

/-- Every composition of a translated subinterval has all of its cuts in J,
so translation back is defined on the complete raw composition domain. -/
def lowerComposition (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition (J.liftInterval K)) : IntervalComposition K where
  parts := π.parts
  parts_pos := π.parts_pos
  cut := fun k => J.localPosition (π.cut k)
    (le_trans (J.globalPosition_bounds K.left).1 (π.cut_bounds k).1)
    (le_trans (π.cut_bounds k).2 (J.globalPosition_bounds K.right).2)
  strict := by
    intro a b hab
    have hs := π.strict hab
    have ha := (π.cut_bounds a).1
    have hb := (π.cut_bounds b).1
    change (π.cut a).val < (π.cut b).val at hs
    change J.left.val + K.left.val ≤ (π.cut a).val at ha
    change J.left.val + K.left.val ≤ (π.cut b).val at hb
    change (π.cut a).val - J.left.val < (π.cut b).val - J.left.val
    omega
  first := by
    apply Fin.ext
    have h := congrArg Fin.val π.first
    change (π.cut 0).val = J.left.val + K.left.val at h
    change (π.cut 0).val - J.left.val = K.left.val
    omega
  last := by
    apply Fin.ext
    have h := congrArg Fin.val π.last
    change (π.cut (Fin.last π.parts)).val = J.left.val + K.right.val at h
    change (π.cut (Fin.last π.parts)).val - J.left.val = K.right.val
    omega

theorem lower_liftComposition (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) : lowerComposition J (liftComposition J π) = π := by
  apply eq_of_parts_cut (π := lowerComposition J (liftComposition J π)) (ρ := π) rfl
  apply heq_of_eq
  funext k
  exact J.local_globalPosition (π.cut k)

theorem lift_lowerComposition (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition (J.liftInterval K)) : liftComposition J (lowerComposition J π) = π := by
  apply eq_of_parts_cut (π := liftComposition J (lowerComposition J π)) (ρ := π) rfl
  apply heq_of_eq
  funext k
  exact J.global_localPosition (π.cut k)
    (le_trans (J.globalPosition_bounds K.left).1 (π.cut_bounds k).1)
    (le_trans (π.cut_bounds k).2 (J.globalPosition_bounds K.right).2)

def restrictionEquiv (J : BoundaryInterval n) (K : BoundaryInterval (J.leaves + 1)) :
    IntervalComposition K ≃ IntervalComposition (J.liftInterval K) where
  toFun := liftComposition J
  invFun := lowerComposition J
  left_inv := lower_liftComposition J
  right_inv := lift_lowerComposition J

theorem liftComposition_part (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) (k : Fin π.parts) :
    (liftComposition J π).part k = J.liftInterval (π.part k) := rfl

theorem liftComposition_nearTriple (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) (k : Fin (π.parts - 1)) :
    (liftComposition J π).nearTriple k = J.liftTriple (π.nearTriple k) := rfl

theorem liftComposition_farTriple (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) (k : Fin (π.parts - 1)) :
    (liftComposition J π).farTriple k = J.liftTriple (π.farTriple k) := rfl

end IntervalComposition

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

def restrictTripleArray (J : BoundaryInterval n) (D : TripleArray n R) : TripleArray (J.leaves + 1) R :=
  fun t => D (J.liftTriple t)

def restrictIntervalArray (J : BoundaryInterval n) (X : IntervalArray n R) : IntervalArray (J.leaves + 1) R :=
  fun K => X (J.liftInterval K)

/-- Restriction commutes with every full coordinate equation because its
raw compositions, exact triples and child intervals correspond bijectively. -/
theorem nearFarTransform_restrict (J : BoundaryInterval n) (D H : TripleArray n R)
    (X : IntervalArray n R) :
    nearFarTransform (restrictTripleArray J D) (restrictTripleArray J H) (restrictIntervalArray J X) =
      restrictIntervalArray J (nearFarTransform D H X) := by
  funext K
  unfold nearFarTransform restrictIntervalArray
  exact Fintype.sum_equiv (IntervalComposition.restrictionEquiv J K) _ _ (fun _ => rfl)

/-- The unique triangular inverse therefore restricts to the unique inverse
constructed directly on the shorter word. -/
theorem nearFarInverse_restrict (J : BoundaryInterval n) (D H : TripleArray n R)
    (Y : IntervalArray n R) :
    restrictIntervalArray J (nearFarInverse D H Y) =
      nearFarInverse (restrictTripleArray J D) (restrictTripleArray J H) (restrictIntervalArray J Y) := by
  apply nearFar_solution_unique
  rw [nearFarTransform_restrict, nearFarTransform_inverse]

theorem boundaryUnitArray_restrict (J : BoundaryInterval n) :
    restrictIntervalArray J (boundaryUnitArray (R := R)) = boundaryUnitArray := by
  funext K
  have he : (J.liftInterval K).right.val = (J.liftInterval K).left.val + 1 ↔
      K.right.val = K.left.val + 1 := by
    change J.left.val + K.right.val = J.left.val + K.left.val + 1 ↔ _
    omega
  simp only [restrictIntervalArray, boundaryUnitArray, he]

theorem farOnlyCoordinates_restrict (J : BoundaryInterval n) (H : TripleArray n R) :
    restrictIntervalArray J (farOnlyCoordinates H) = farOnlyCoordinates (restrictTripleArray J H) := by
  unfold farOnlyCoordinates
  rw [nearFarInverse_restrict, boundaryUnitArray_restrict]
  rfl

theorem farOnlyOutput_restrict (J : BoundaryInterval n) (H : TripleArray n R) :
    restrictIntervalArray J (farOnlyOutput H) = farOnlyOutput (restrictTripleArray J H) := by
  change restrictIntervalArray J (nearFarTransform 0 (-H) (farOnlyCoordinates H)) =
    nearFarTransform 0 (-restrictTripleArray J H) (farOnlyCoordinates (restrictTripleArray J H))
  rw [← nearFarTransform_restrict, farOnlyCoordinates_restrict]
  rfl

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Close the actual contiguous boundary word on J. Residue zero labels its
last vertex, so the edge at root zero runs from the last vertex to the first. -/
def restrictedWordTuple (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n) :
    LabelledTuple (J.leaves + 1) :=
  fun j => boundaryWord P g (J.globalPosition ⟨(j - 1).val, ZMod.val_lt _⟩)

theorem restrictedWord_boundary (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n)
    (k : Fin (J.leaves + 1)) :
    boundaryWord (restrictedWordTuple P g J) 0 k = boundaryWord P g (J.globalPosition k) := by
  unfold boundaryWord restrictedWordTuple boundaryIndex
  have hz : (0 + (k.val : ZMod (J.leaves + 1)) + 1) - 1 = (k.val : ZMod (J.leaves + 1)) := by ring
  simp only [hz, ZMod.val_natCast_of_lt k.isLt]
  rfl

theorem restrictedWord_first_vertex (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n) :
    restrictedWordTuple P g J 1 = boundaryWord P g J.left := by
  unfold restrictedWordTuple
  apply congrArg (boundaryWord P g)
  apply Fin.ext
  simp [BoundaryInterval.globalPosition]

theorem restrictedWord_last_vertex (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n) :
    restrictedWordTuple P g J 0 = boundaryWord P g J.right := by
  unfold restrictedWordTuple
  apply congrArg (boundaryWord P g)
  apply Fin.ext
  have hj := J.increasing
  change J.left.val < J.right.val at hj
  change J.left.val + (0 - 1 : ZMod (J.leaves + 1)).val = J.right.val
  rw [zero_sub, ZMod.val_neg_one]
  unfold BoundaryInterval.leaves
  omega

/-- The chosen local root is exactly the physical closing edge required by
the source: from a_j to a_i, with that directed displacement. -/
theorem restrictedWord_closing_edge (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n) :
    edge (restrictedWordTuple P g J) 0 = boundaryWord P g J.left - boundaryWord P g J.right := by
  simp only [edge, zero_add, restrictedWord_first_vertex, restrictedWord_last_vertex]

theorem BoundaryInterval.lift_fullInterval (J : BoundaryInterval n) (hJ : 2 ≤ J.leaves) :
    J.liftInterval (fullBoundaryInterval (by omega : 3 ≤ J.leaves + 1)) = J := by
  apply BoundaryInterval.eq_of_endpoints
  · apply Fin.ext
    simp [BoundaryInterval.liftInterval, BoundaryInterval.globalPosition, fullBoundaryInterval]
  · apply Fin.ext
    have hj := J.increasing
    change J.left.val < J.right.val at hj
    simp only [BoundaryInterval.liftInterval, BoundaryInterval.globalPosition, fullBoundaryInterval]
    unfold BoundaryInterval.leaves
    omega

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Local geometric samples are exactly restrictions of the same physical
chirotope entries. No geometric genericity assumption is needed for this identity. -/
theorem geometricBoundaryArray_restrictedWord (P : LabelledTuple n) (g : ZMod n)
    (J : BoundaryInterval n) :
    geometricBoundaryArray (R := R) (restrictedWordTuple P g J) 0 =
      restrictTripleArray J (geometricBoundaryArray P g) := by
  funext t
  simp only [restrictTripleArray, geometricBoundaryArray, chi]
  change ((SignType.sign (det
    (boundaryWord (restrictedWordTuple P g J) 0 t.middle - boundaryWord (restrictedWordTuple P g J) 0 t.upper)
    (boundaryWord (restrictedWordTuple P g J) 0 t.lower - boundaryWord (restrictedWordTuple P g J) 0 t.upper)) : ℤ) : R) = _
  rw [restrictedWord_boundary, restrictedWord_boundary, restrictedWord_boundary]
  rfl

/-- Full source nonleaf restriction clause: whenever the closed endpoint word
satisfies G1, its tree coefficient at the physical closing root is exactly the
J coordinate of the original far-only output. No global G1 is added as a premise. -/
theorem farOnlyOutput_restricted_tree (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n)
    (hJ : 2 ≤ J.leaves) (hP : G1 (restrictedWordTuple P g J)) :
    farOnlyOutput (geometricBoundaryArray (R := R) P g) J =
      (treeCoefficient (restrictedWordTuple P g J) hP 0 (by omega : 3 ≤ J.leaves + 1) : R) := by
  let K := fullBoundaryInterval (by omega : 3 ≤ J.leaves + 1)
  have hr := congrFun (farOnlyOutput_restrict J (geometricBoundaryArray (R := R) P g)) K
  change farOnlyOutput (geometricBoundaryArray P g) (J.liftInterval K) =
    farOnlyOutput (restrictTripleArray J (geometricBoundaryArray P g)) K at hr
  rw [J.lift_fullInterval hJ, ← geometricBoundaryArray_restrictedWord P g J] at hr
  exact hr.trans (treeCoefficient_farOnly (restrictedWordTuple P g J) hP 0 (by omega)).symm

end
end SM

namespace SM

noncomputable section

/-- All clauses of source lem:farout. The inverse is given by actual coordinate
polynomials; factorization and near-array freedom concern full arrays; the
nonleaf restriction uses the original physical closing edge and only local G1.
The final two conjuncts separately retain the open one-leaf convention and the
closed polygon coefficient, so no two-gon amplitude is introduced. -/
theorem farout (n : ℕ) [NeZero n] (R : Type*) [CommRing R] [Invertible (2 : R)] (hn : 3 ≤ n) :
    (∀ D H : TripleArray n R,
      (∃ Ψ : BoundaryInterval n → MvPolynomial (BoundaryInterval n) R,
        (∀ Y : IntervalArray n R,
          nearFarTransform D H (fun I => MvPolynomial.eval₂Hom (RingHom.id R) Y (Ψ I)) = Y) ∧
        (∀ X : IntervalArray n R,
          (fun I => MvPolynomial.eval₂Hom (RingHom.id R) (nearFarTransform D H X) (Ψ I)) = X)) ∧
      nearFarTransform D H = farTransform H ∘ nearTransform D) ∧
    (∀ (P : LabelledTuple n) (hP : G1 P) (g : ZMod n),
      nearFarTransform (geometricBoundaryArray (R := R) P g) (geometricBoundaryArray P g)
          (fun I => (openTreeSum P hP g I : R)) = boundaryUnitArray ∧
      (treeCoefficient P hP g hn : R) =
        nearFarTransform (geometricBoundaryArray P g) (-geometricBoundaryArray P g)
          (fun I => (openTreeSum P hP g I : R)) (fullBoundaryInterval hn) ∧
      (treeCoefficient P hP g hn : R) =
        farOnlyOutput (geometricBoundaryArray P g) (fullBoundaryInterval hn)) ∧
    (∀ (D₁ D₂ H : TripleArray n R) (X₁ X₂ : IntervalArray n R),
      nearFarTransform D₁ H X₁ = boundaryUnitArray →
      nearFarTransform D₂ H X₂ = boundaryUnitArray →
      nearFarTransform D₁ (-H) X₁ = nearFarTransform D₂ (-H) X₂) ∧
    (∀ (H : TripleArray n R) (J : BoundaryInterval n),
      (2 ≤ J.leaves → farTransform H (farOnlyCoordinates H) J = 0) ∧
      (J.leaves = 1 → farTransform H (farOnlyCoordinates H) J = 1 ∧ farOnlyOutput H J = 1)) ∧
    (∀ (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n)
        (hJ : 2 ≤ J.leaves) (hP : G1 (restrictedWordTuple P g J)),
      edge (restrictedWordTuple P g J) 0 = boundaryWord P g J.left - boundaryWord P g J.right ∧
      farOnlyOutput (geometricBoundaryArray (R := R) P g) J =
        (treeCoefficient (restrictedWordTuple P g J) hP 0 (by omega : 3 ≤ J.leaves + 1) : R)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro D H
    exact ⟨nearFar_has_polynomial_inverse D H, nearFar_factorization D H⟩
  · intro P hP g
    exact ⟨geometric_nearFar_open P hP g, geometric_nearFar_root P hP g hn,
      treeCoefficient_farOnly P hP g hn⟩
  · intro D₁ D₂ H X₁ X₂ h₁ h₂
    exact complete_output_near_independent D₁ D₂ H X₁ X₂ boundaryUnitArray h₁ h₂
  · intro H J
    exact ⟨farOnly_nonleaf_E H J, farOnly_leaf_values H J⟩
  · intro P g J hJ hP
    exact ⟨restrictedWord_closing_edge P g J, farOnlyOutput_restricted_tree P g J hJ hP⟩

end
end SM

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
  simp only [Fintype.sum_unique]
  exact congrArg (fun s : Finset (Fin 0) => f ((IntervalComposition.single I).indexMarks s))
    (Subsingleton.elim _ _)

end
end RefinementTransportIndependentReview

namespace RefinedWeightsIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

-- Every fine interior factor occurs once, either at an outer cut or inside one inner part.
theorem complete_factor_count (π : IntervalComposition I) (T : RefiningCutSet π) :
    (π.parts - 1) + (∑ k : Fin π.parts, ((π.refinementInner T k).parts - 1)) =
      T.val.toComposition.parts - 1 := by
  have hm : Fintype.card (IntervalComposition.RefinementMarked π T) = π.parts - 1 := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (π.refinedMarkedEquiv T)).symm
  have hu : Fintype.card (IntervalComposition.RefinementUnmarked π T) =
      ∑ k : Fin π.parts, ((π.refinementInner T k).parts - 1) := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using
      (Fintype.card_congr (π.refinedUnmarkedEquiv T)).symm
  have hc := Fintype.card_subtype_compl
    (fun r : Fin (T.val.toComposition.parts - 1) =>
      T.val.toComposition.interiorPosition r ∈ π.cutSet.cuts)
  have hle := Fintype.card_le_of_injective
    (fun r : IntervalComposition.RefinementMarked π T => r.val) Subtype.val_injective
  simp only [Fintype.card_fin] at hc hle
  change Fintype.card (IntervalComposition.RefinementUnmarked π T) =
    T.val.toComposition.parts - 1 - Fintype.card (IntervalComposition.RefinementMarked π T) at hc
  omega

-- The transported inner near sample retains all three actual entries.
theorem inner_near_entries_are_exact (π : IntervalComposition I) (T : RefiningCutSet π)
    (k : Fin π.parts) (j : Fin ((π.refinementInner T k).parts - 1)) :
    let u := T.val.toComposition.nearTriple (π.refinedInteriorIndex T ⟨k,j⟩)
    let v := (π.refinementInner T k).nearTriple j
    u.lower = v.lower ∧ u.middle = v.middle ∧ u.upper = v.upper := by
  dsimp only
  rw [π.inner_nearTriple_transport T k j]
  exact ⟨rfl,rfl,rfl⟩

-- The far sample uses the original global endpoints, not those of an inner part.
theorem outer_far_entries_are_global (π : IntervalComposition I) (T : RefiningCutSet π)
    (j : Fin (π.parts - 1)) :
    let t := T.val.toComposition.farTriple (π.refinedOuterIndex T j)
    t.lower = I.left ∧ t.middle = π.interiorPosition j ∧ t.upper = I.right := by
  dsimp only
  rw [π.outer_farTriple_transport T j]
  exact ⟨rfl,rfl,rfl⟩

-- Unary outer data produces the empty marked subset for any refinement.
theorem unary_outer_has_empty_marks (I : BoundaryInterval n)
    (T : RefiningCutSet (IntervalComposition.single I)) :
    (IntervalComposition.single I).refinementMarkIndices T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hm := ((IntervalComposition.single I).mem_refinementMarkIndices T r).mp hr
  have j := ((IntervalComposition.single I).refinedMarkedEquiv T).symm ⟨r,hm⟩
  exact Fin.elim0 j

-- Retaining exactly the outer cut set marks every fine interior position.
theorem identical_outer_and_fine_marks_all (π : IntervalComposition I) :
    π.refinementMarkIndices ⟨π.cutSet, Finset.Subset.refl _⟩ = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro r
  rw [π.mem_refinementMarkIndices]
  have h := π.cutSet.toComposition.interiorPosition_mem r
  rw [BoundaryCutSet.toComposition_cutSet] at h
  exact ((π.cutSet.mem_interior_iff _).mp h).1

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

-- The reconstructed-family formula applies to every original raw inner family.
theorem raw_family_near_weight_transport (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) (D : TripleArray n R) :
    let T := π.flattenRefinement (fun k => (σ k).cutSet)
    (∏ k : Fin π.parts, (σ k).nearFarWeight D 0) =
      ∏ r ∈ (π.refinementMarkIndices T)ᶜ,
        D (T.val.toComposition.nearTriple r) * ⅟ (2 : R) := by
  let T := π.flattenRefinement (fun k => (σ k).cutSet)
  let τ : ∀ k : Fin π.parts, IntervalComposition (π.part k) := fun k => π.refinementInner T k
  have ht : τ = σ := funext (π.refinementInner_flatten σ)
  have hp := congrArg (fun η : ∀ k : Fin π.parts, IntervalComposition (π.part k) =>
    ∏ k : Fin π.parts, (η k).nearFarWeight D 0) ht
  exact hp.symm.trans (π.prod_inner_near_weights T D)

-- Both coefficient families and every child factor are transported for the raw source summand.
theorem raw_full_nested_summand (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k))
    (D H : TripleArray n R) (X : IntervalArray n R) :
    let T := π.flattenRefinement (fun k => (σ k).cutSet)
    π.nearFarWeight 0 H *
      (∏ k : Fin π.parts, (σ k).nearFarWeight D 0 * ∏ j : Fin (σ k).parts, X ((σ k).part j)) =
    ((∏ r ∈ π.refinementMarkIndices T, -H (T.val.toComposition.farTriple r) * ⅟ (2 : R)) *
      (∏ r ∈ (π.refinementMarkIndices T)ᶜ, D (T.val.toComposition.nearTriple r) * ⅟ (2 : R))) *
        ∏ j : Fin T.val.toComposition.parts, X (T.val.toComposition.part j) := by
  let T := π.flattenRefinement (fun k => (σ k).cutSet)
  let τ : ∀ k : Fin π.parts, IntervalComposition (π.part k) := fun k => π.refinementInner T k
  have ht : τ = σ := funext (π.refinementInner_flatten σ)
  have hp := congrArg (fun η : ∀ k : Fin π.parts, IntervalComposition (π.part k) =>
    π.nearFarWeight 0 H * (∏ k : Fin π.parts, (η k).nearFarWeight D 0 *
      ∏ j : Fin (η k).parts, X ((η k).part j))) ht
  exact hp.symm.trans (π.nested_summand_transport T D H X)

-- All unary inner coefficients contribute one, without a nontrivial-ring premise.
theorem all_unary_inner_coefficients_one (π : IntervalComposition I) (D : TripleArray n R) :
    (∏ k : Fin π.parts, (IntervalComposition.single (π.part k)).nearFarWeight D 0) = 1 := by
  apply Finset.prod_eq_one
  intro k _
  exact (IntervalComposition.single (π.part k)).nearFarWeight_one D 0 rfl

-- The actual marked-refinement output uses the same underlying physical marks.
theorem raw_marks_match_actual_bijection (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) :
    (π.refinementMarks (π.flattenRefinement (fun k => (σ k).cutSet))).val =
      (IntervalComposition.nestedMarkedCutEquiv I ⟨π,σ⟩).2.val := by
  have transport_val {S U : BoundaryCutSet I} (e : S = U) (m : MarkedCuts S) :
      (e ▸ m : MarkedCuts U).val = m.val := by
    cases e
    rfl
  let S := π.flattenCutSets (fun k => (σ k).cutSet)
  let m : MarkedCuts S := ⟨π.cutSet.interior.val,
    (BoundaryCutSet.cuts_subset_iff_interior_subset π.cutSet S).mp
      (π.outer_cuts_subset_flatten (fun k => (σ k).cutSet))⟩
  change m.val = (S.toComposition_cutSet.symm ▸ m : MarkedCuts S.toComposition.cutSet).val
  exact (transport_val S.toComposition_cutSet.symm m).symm

end
end RefinedWeightsIndependentReview

namespace NearFarFactorizationIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

-- The inverse order is near-inverse after far-inverse, matching F after G.
theorem inverse_factorization_order (D H : TripleArray n R) (Y : IntervalArray n R) :
    nearFarInverse D H Y = nearFarInverse D 0 (nearFarInverse 0 H Y) := by
  symm
  apply nearFar_solution_unique D H
  rw [nearFar_factorization D H]
  change farTransform H (nearTransform D (nearFarInverse D 0 (nearFarInverse 0 H Y))) = Y
  simp only [nearTransform, farTransform, nearFarTransform_inverse]

-- No assumed solutions are needed: the canonical inverse supplies every target.
theorem output_independent_with_actual_inverse (D₁ D₂ H : TripleArray n R)
    (Y : IntervalArray n R) :
    nearFarTransform D₁ (-H) (nearFarInverse D₁ H Y) =
      nearFarTransform D₂ (-H) (nearFarInverse D₂ H Y) :=
  complete_output_near_independent D₁ D₂ H _ _ Y
    (nearFarTransform_inverse D₁ H Y) (nearFarTransform_inverse D₂ H Y)

theorem inverse_target_E_has_far_only_output (D H : TripleArray n R) :
    nearFarTransform D (-H) (nearFarInverse D H boundaryUnitArray) = farOnlyOutput H :=
  reversedFar_output_of_solution D H _ _ (nearFarTransform_inverse D H boundaryUnitArray)

-- The actual geometric root coefficient remains the same with arbitrary near-array D.
theorem actual_root_all_near_arrays (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) (D : TripleArray n R) :
    (treeCoefficient P hP g hn : R) =
      nearFarTransform D (-geometricBoundaryArray P g)
        (nearFarInverse D (geometricBoundaryArray P g) boundaryUnitArray)
        (fullBoundaryInterval hn) := by
  rw [inverse_target_E_has_far_only_output]
  exact treeCoefficient_farOnly P hP g hn

-- The output is tied to the same physical root when the representative is shifted.
theorem far_only_output_physical_root_shift (P : LabelledTuple n) (g a : ZMod n) :
    farOnlyOutput (geometricBoundaryArray (R := R) (shift a P) (g-a)) =
      farOnlyOutput (geometricBoundaryArray P g) := by
  rw [geometricBoundaryArray_shift]

-- Open-word leaf and nonleaf conventions use every original interval coordinate.
theorem all_interval_E_and_leaf_B_values (H : TripleArray n R) (I : BoundaryInterval n) :
    (I.leaves = 1 → farTransform H (farOnlyCoordinates H) I = 1 ∧ farOnlyOutput H I = 1) ∧
    (2 ≤ I.leaves → farTransform H (farOnlyCoordinates H) I = 0) :=
  ⟨farOnly_leaf_values H I, farOnly_nonleaf_E H I⟩

-- The whole marked sum keeps the source unary composition's exact X_I term.
theorem unary_marked_sum_retains_coordinate (D H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    (∑ m : MarkedCuts (IntervalComposition.single I).cutSet,
      IntervalComposition.markedSummand D H X (IntervalComposition.single I) m) = X I := by
  rw [IntervalComposition.sum_markedSummand]
  rw [(IntervalComposition.single I).nearFarWeight_one D H rfl,
    one_mul, IntervalComposition.single_product]

end
end NearFarFactorizationIndependentReview

namespace FaroutIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n]

theorem all_physical_positions_once (J : BoundaryInterval n) (x : Fin n)
    (hl : J.left ≤ x) (hr : x ≤ J.right) :
    ∃! k : Fin (J.leaves + 1), J.globalPosition k = x := by
  refine ⟨J.localPosition x hl hr, J.global_localPosition x hl hr, ?_⟩
  intro k hk
  exact J.globalPosition_strict.injective (hk.trans (J.global_localPosition x hl hr).symm)

theorem translated_leaf_count (J : BoundaryInterval n) (K : BoundaryInterval (J.leaves + 1)) :
    (J.liftInterval K).leaves = K.leaves := by
  unfold BoundaryInterval.leaves BoundaryInterval.liftInterval BoundaryInterval.globalPosition
  simp only
  omega

theorem all_physical_subintervals (J I : BoundaryInterval n)
    (hl : J.left ≤ I.left) (hr : I.right ≤ J.right) :
    ∃ K : BoundaryInterval (J.leaves + 1), J.liftInterval K = I := by
  have hli : J.left ≤ I.right := le_trans hl (le_of_lt I.increasing)
  have hri : I.left ≤ J.right := le_trans (le_of_lt I.increasing) hr
  let K : BoundaryInterval (J.leaves + 1) :=
    ⟨J.localPosition I.left hl hri, J.localPosition I.right hli hr, by
      have hi := I.increasing
      change I.left.val < I.right.val at hi
      change J.left.val ≤ I.left.val at hl
      change I.left.val - J.left.val < I.right.val - J.left.val
      omega⟩
  refine ⟨K, ?_⟩
  apply BoundaryInterval.eq_of_endpoints
  · exact J.global_localPosition I.left hl hri
  · exact J.global_localPosition I.right hli hr

theorem all_raw_parts_and_cuts (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) :
    (IntervalComposition.liftComposition J π).parts = π.parts ∧
    (∀ k : Fin (π.parts + 1),
      ((IntervalComposition.liftComposition J π).cut k).val = J.left.val + (π.cut k).val) ∧
    IntervalComposition.lowerComposition J (IntervalComposition.liftComposition J π) = π :=
  ⟨rfl, fun _ => rfl, IntervalComposition.lower_liftComposition J π⟩

theorem unary_is_preserved (J : BoundaryInterval n) (K : BoundaryInterval (J.leaves + 1)) :
    IntervalComposition.liftComposition J (IntervalComposition.single K) =
      IntervalComposition.single (J.liftInterval K) :=
  IntervalComposition.eq_single_of_parts_eq_one _ rfl

theorem complete_composition_cardinality (J : BoundaryInterval n)
    (K : BoundaryInterval (J.leaves + 1)) :
    Fintype.card (IntervalComposition K) = Fintype.card (IntervalComposition (J.liftInterval K)) :=
  Fintype.card_congr (IntervalComposition.restrictionEquiv J K)

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

theorem actual_child_product (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) (X : IntervalArray n R) :
    (∏ k : Fin π.parts, restrictIntervalArray J X (π.part k)) =
      ∏ k : Fin (IntervalComposition.liftComposition J π).parts,
        X ((IntervalComposition.liftComposition J π).part k) := rfl

theorem all_actual_samples (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) (D H : TripleArray n R) (k : Fin (π.parts - 1)) :
    restrictTripleArray J D (π.nearTriple k) =
      D ((IntervalComposition.liftComposition J π).nearTriple k) ∧
    restrictTripleArray J H (π.farTriple k) =
      H ((IntervalComposition.liftComposition J π).farTriple k) := ⟨rfl, rfl⟩

theorem local_inverse_solves_actual_restriction (J : BoundaryInterval n) (D H : TripleArray n R)
    (Y : IntervalArray n R) :
    nearFarTransform (restrictTripleArray J D) (restrictTripleArray J H)
      (restrictIntervalArray J (nearFarInverse D H Y)) = restrictIntervalArray J Y := by
  rw [nearFarTransform_restrict, nearFarTransform_inverse]

theorem restricted_c_is_actual_local_inverse (P : LabelledTuple n) (g : ZMod n)
    (J : BoundaryInterval n) :
    restrictIntervalArray J (farOnlyCoordinates (geometricBoundaryArray (R := R) P g)) =
      nearFarInverse 0 (geometricBoundaryArray (restrictedWordTuple P g J) 0) boundaryUnitArray := by
  rw [farOnlyCoordinates_restrict, ← geometricBoundaryArray_restrictedWord]
  rfl

theorem full_contiguous_word_and_directed_root (P : LabelledTuple n) (g : ZMod n)
    (J : BoundaryInterval n) :
    (∀ k : Fin (J.leaves + 1), boundaryWord (restrictedWordTuple P g J) 0 k =
      boundaryWord P g (J.globalPosition k)) ∧
    restrictedWordTuple P g J 0 = boundaryWord P g J.right ∧
    restrictedWordTuple P g J 1 = boundaryWord P g J.left ∧
    edge (restrictedWordTuple P g J) 0 = boundaryWord P g J.left - boundaryWord P g J.right :=
  ⟨restrictedWord_boundary P g J, restrictedWord_last_vertex P g J,
    restrictedWord_first_vertex P g J, restrictedWord_closing_edge P g J⟩

theorem nonleaf_has_three_vertices (J : BoundaryInterval n) (hJ : 2 ≤ J.leaves) :
    3 ≤ J.leaves + 1 := by omega

theorem local_root_without_global_G1 (hn : 3 ≤ n) (P : LabelledTuple n) (g : ZMod n)
    (J : BoundaryInterval n) (hJ : 2 ≤ J.leaves) (hlocal : G1 (restrictedWordTuple P g J)) :
    farOnlyOutput (geometricBoundaryArray (R := R) P g) J =
      (treeCoefficient (restrictedWordTuple P g J) hlocal 0 (by omega) : R) :=
  ((farout n R hn).2.2.2.2 P g J hJ hlocal).2

theorem aggregate_polynomials_both_directions (hn : 3 ≤ n) (D H : TripleArray n R) :
    ∃ Ψ : BoundaryInterval n → MvPolynomial (BoundaryInterval n) R,
      (∀ Y : IntervalArray n R, nearFarTransform D H
        (fun I => MvPolynomial.eval₂Hom (RingHom.id R) Y (Ψ I)) = Y) ∧
      (∀ X : IntervalArray n R,
        (fun I => MvPolynomial.eval₂Hom (RingHom.id R) (nearFarTransform D H X) (Ψ I)) = X) :=
  ((farout n R hn).1 D H).1

theorem aggregate_factorization_on_every_array (hn : 3 ≤ n)
    (D H : TripleArray n R) (X : IntervalArray n R) :
    nearFarTransform D H X = farTransform H (nearTransform D X) :=
  congrFun ((farout n R hn).1 D H).2 X

theorem aggregate_geometry_and_actual_full_root (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : G1 P) (g : ZMod n) :
    nearFarTransform (geometricBoundaryArray (R := R) P g) (geometricBoundaryArray P g)
      (fun I => (openTreeSum P hP g I : R)) = boundaryUnitArray ∧
    (treeCoefficient P hP g hn : R) =
      farOnlyOutput (geometricBoundaryArray P g) (fullBoundaryInterval hn) :=
  ⟨((farout n R hn).2.1 P hP g).1, ((farout n R hn).2.1 P hP g).2.2⟩

theorem aggregate_near_freedom_has_real_solutions (hn : 3 ≤ n) (D₁ D₂ H : TripleArray n R) :
    nearFarTransform D₁ (-H) (nearFarInverse D₁ H boundaryUnitArray) =
      nearFarTransform D₂ (-H) (nearFarInverse D₂ H boundaryUnitArray) :=
  (farout n R hn).2.2.1 D₁ D₂ H _ _ (nearFarTransform_inverse _ _ _) (nearFarTransform_inverse _ _ _)

theorem aggregate_open_leaf_and_nonleaf (hn : 3 ≤ n) (H : TripleArray n R)
    (J : BoundaryInterval n) :
    (2 ≤ J.leaves → farTransform H (farOnlyCoordinates H) J = 0) ∧
    (J.leaves = 1 → farTransform H (farOnlyCoordinates H) J = 1 ∧ farOnlyOutput H J = 1) :=
  (farout n R hn).2.2.2.1 H J

end
end FaroutIndependentReview

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
#check SM.IntervalComposition.RefinementUnmarked
#print axioms SM.IntervalComposition.RefinementUnmarked
#check SM.IntervalComposition.refinedInteriorIndex
#print axioms SM.IntervalComposition.refinedInteriorIndex
#check SM.IntervalComposition.refinedUnmarkedIndex
#print axioms SM.IntervalComposition.refinedUnmarkedIndex
#check SM.BoundaryCutSet.mem_interior_iff
#print axioms SM.BoundaryCutSet.mem_interior_iff
#check SM.IntervalComposition.innerPosition_in_refinement
#print axioms SM.IntervalComposition.innerPosition_in_refinement
#check SM.IntervalComposition.refinedInteriorIndex_position
#print axioms SM.IntervalComposition.refinedInteriorIndex_position
#check SM.IntervalComposition.refinedUnmarkedIndex_injective
#print axioms SM.IntervalComposition.refinedUnmarkedIndex_injective
#check SM.IntervalComposition.refinedUnmarkedIndex_surjective
#print axioms SM.IntervalComposition.refinedUnmarkedIndex_surjective
#check SM.IntervalComposition.refinedUnmarkedEquiv
#print axioms SM.IntervalComposition.refinedUnmarkedEquiv
#check SM.IntervalComposition.inner_nearTriple_transport
#print axioms SM.IntervalComposition.inner_nearTriple_transport
#check SM.IntervalComposition.prod_inner_nearTriples
#print axioms SM.IntervalComposition.prod_inner_nearTriples
#check SM.IntervalComposition.RefinementMarked
#print axioms SM.IntervalComposition.RefinementMarked
#check SM.IntervalComposition.refinedOuterIndex
#print axioms SM.IntervalComposition.refinedOuterIndex
#check SM.IntervalComposition.refinedMarkedIndex
#print axioms SM.IntervalComposition.refinedMarkedIndex
#check SM.IntervalComposition.outerPosition_in_refinement
#print axioms SM.IntervalComposition.outerPosition_in_refinement
#check SM.IntervalComposition.refinedOuterIndex_position
#print axioms SM.IntervalComposition.refinedOuterIndex_position
#check SM.IntervalComposition.refinedMarkedIndex_injective
#print axioms SM.IntervalComposition.refinedMarkedIndex_injective
#check SM.IntervalComposition.refinedMarkedIndex_surjective
#print axioms SM.IntervalComposition.refinedMarkedIndex_surjective
#check SM.IntervalComposition.refinedMarkedEquiv
#print axioms SM.IntervalComposition.refinedMarkedEquiv
#check SM.IntervalComposition.outer_farTriple_transport
#print axioms SM.IntervalComposition.outer_farTriple_transport
#check SM.IntervalComposition.prod_outer_farTriples
#print axioms SM.IntervalComposition.prod_outer_farTriples
#check SM.IntervalComposition.refinementMarks
#print axioms SM.IntervalComposition.refinementMarks
#check SM.IntervalComposition.refinementMarkIndices
#print axioms SM.IntervalComposition.refinementMarkIndices
#check SM.IntervalComposition.mem_refinementMarkIndices
#print axioms SM.IntervalComposition.mem_refinementMarkIndices
#check SM.IntervalComposition.prod_refinementMarked
#print axioms SM.IntervalComposition.prod_refinementMarked
#check SM.IntervalComposition.prod_refinementUnmarked
#print axioms SM.IntervalComposition.prod_refinementUnmarked
#check SM.IntervalComposition.nearFarWeight_near_only
#print axioms SM.IntervalComposition.nearFarWeight_near_only
#check SM.IntervalComposition.nearFarWeight_far_only
#print axioms SM.IntervalComposition.nearFarWeight_far_only
#check SM.IntervalComposition.prod_inner_near_weights
#print axioms SM.IntervalComposition.prod_inner_near_weights
#check SM.IntervalComposition.outer_far_weight
#print axioms SM.IntervalComposition.outer_far_weight
#check SM.IntervalComposition.nested_summand_transport
#print axioms SM.IntervalComposition.nested_summand_transport
#check SM.IntervalComposition.nestedSummand
#print axioms SM.IntervalComposition.nestedSummand
#check SM.IntervalComposition.markedSummand
#print axioms SM.IntervalComposition.markedSummand
#check SM.BoundaryCutSet.marked_transport_val
#print axioms SM.BoundaryCutSet.marked_transport_val
#check SM.IntervalComposition.nestedMarkedCutEquiv_marks
#print axioms SM.IntervalComposition.nestedMarkedCutEquiv_marks
#check SM.IntervalComposition.nestedSummand_eq_markedSummand
#print axioms SM.IntervalComposition.nestedSummand_eq_markedSummand
#check SM.IntervalComposition.sum_markedSummand
#print axioms SM.IntervalComposition.sum_markedSummand
#check SM.nearFar_factorization_coordinate
#print axioms SM.nearFar_factorization_coordinate
#check SM.nearFar_factorization
#print axioms SM.nearFar_factorization
#check SM.farOnlyCoordinates
#print axioms SM.farOnlyCoordinates
#check SM.farOnlyOutput
#print axioms SM.farOnlyOutput
#check SM.nearTransform_of_nearFar_solution
#print axioms SM.nearTransform_of_nearFar_solution
#check SM.reversedFar_output_of_solution
#print axioms SM.reversedFar_output_of_solution
#check SM.complete_output_near_independent
#print axioms SM.complete_output_near_independent
#check SM.farOnlyCoordinates_equation
#print axioms SM.farOnlyCoordinates_equation
#check SM.geometric_farOnly_output
#print axioms SM.geometric_farOnly_output
#check SM.treeCoefficient_farOnly
#print axioms SM.treeCoefficient_farOnly
#check SM.nearFarTransform_leaf
#print axioms SM.nearFarTransform_leaf
#check SM.boundaryUnitArray_leaf
#print axioms SM.boundaryUnitArray_leaf
#check SM.farOnlyCoordinates_leaf
#print axioms SM.farOnlyCoordinates_leaf
#check SM.farOnly_leaf_values
#print axioms SM.farOnly_leaf_values
#check SM.farOnly_nonleaf_E
#print axioms SM.farOnly_nonleaf_E
#check SM.BoundaryInterval.globalPosition
#print axioms SM.BoundaryInterval.globalPosition
#check SM.BoundaryInterval.localPosition
#print axioms SM.BoundaryInterval.localPosition
#check SM.BoundaryInterval.liftInterval
#print axioms SM.BoundaryInterval.liftInterval
#check SM.BoundaryInterval.liftTriple
#print axioms SM.BoundaryInterval.liftTriple
#check SM.IntervalComposition.liftComposition
#print axioms SM.IntervalComposition.liftComposition
#check SM.IntervalComposition.lowerComposition
#print axioms SM.IntervalComposition.lowerComposition
#check SM.restrictTripleArray
#print axioms SM.restrictTripleArray
#check SM.restrictIntervalArray
#print axioms SM.restrictIntervalArray
#check SM.BoundaryInterval.globalPosition_strict
#print axioms SM.BoundaryInterval.globalPosition_strict
#check SM.BoundaryInterval.globalPosition_bounds
#print axioms SM.BoundaryInterval.globalPosition_bounds
#check SM.BoundaryInterval.global_localPosition
#print axioms SM.BoundaryInterval.global_localPosition
#check SM.BoundaryInterval.local_globalPosition
#print axioms SM.BoundaryInterval.local_globalPosition
#check SM.IntervalComposition.eq_of_parts_cut
#print axioms SM.IntervalComposition.eq_of_parts_cut
#check SM.IntervalComposition.cut_bounds
#print axioms SM.IntervalComposition.cut_bounds
#check SM.IntervalComposition.lower_liftComposition
#print axioms SM.IntervalComposition.lower_liftComposition
#check SM.IntervalComposition.lift_lowerComposition
#print axioms SM.IntervalComposition.lift_lowerComposition
#check SM.IntervalComposition.restrictionEquiv
#print axioms SM.IntervalComposition.restrictionEquiv
#check SM.IntervalComposition.liftComposition_part
#print axioms SM.IntervalComposition.liftComposition_part
#check SM.IntervalComposition.liftComposition_nearTriple
#print axioms SM.IntervalComposition.liftComposition_nearTriple
#check SM.IntervalComposition.liftComposition_farTriple
#print axioms SM.IntervalComposition.liftComposition_farTriple
#check SM.nearFarTransform_restrict
#print axioms SM.nearFarTransform_restrict
#check SM.nearFarInverse_restrict
#print axioms SM.nearFarInverse_restrict
#check SM.boundaryUnitArray_restrict
#print axioms SM.boundaryUnitArray_restrict
#check SM.farOnlyCoordinates_restrict
#print axioms SM.farOnlyCoordinates_restrict
#check SM.farOnlyOutput_restrict
#print axioms SM.farOnlyOutput_restrict
#check SM.restrictedWordTuple
#print axioms SM.restrictedWordTuple
#check SM.restrictedWord_boundary
#print axioms SM.restrictedWord_boundary
#check SM.restrictedWord_first_vertex
#print axioms SM.restrictedWord_first_vertex
#check SM.restrictedWord_last_vertex
#print axioms SM.restrictedWord_last_vertex
#check SM.restrictedWord_closing_edge
#print axioms SM.restrictedWord_closing_edge
#check SM.BoundaryInterval.lift_fullInterval
#print axioms SM.BoundaryInterval.lift_fullInterval
#check SM.geometricBoundaryArray_restrictedWord
#print axioms SM.geometricBoundaryArray_restrictedWord
#check SM.farOnlyOutput_restricted_tree
#print axioms SM.farOnlyOutput_restricted_tree
#check SM.farout
#print axioms SM.farout
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
#print SM.IntervalComposition.RefinementUnmarked
#print SM.IntervalComposition.refinedInteriorIndex
#print SM.IntervalComposition.refinedUnmarkedIndex
#print SM.IntervalComposition.RefinementMarked
#print SM.IntervalComposition.refinedOuterIndex
#print SM.IntervalComposition.refinedMarkedIndex
#print SM.IntervalComposition.refinementMarks
#print SM.IntervalComposition.refinementMarkIndices
#print SM.IntervalComposition.nestedSummand
#print SM.IntervalComposition.markedSummand
#print SM.farOnlyCoordinates
#print SM.farOnlyOutput
#print SM.IntervalComposition.refinedUnmarkedEquiv
#print SM.IntervalComposition.refinedMarkedEquiv
#print SM.BoundaryInterval.globalPosition
#print SM.BoundaryInterval.localPosition
#print SM.BoundaryInterval.liftInterval
#print SM.BoundaryInterval.liftTriple
#print SM.IntervalComposition.liftComposition
#print SM.IntervalComposition.lowerComposition
#print SM.restrictTripleArray
#print SM.restrictIntervalArray
#print SM.restrictedWordTuple
#print SM.IntervalComposition.restrictionEquiv
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
#print axioms RefinedWeightsIndependentReview.complete_factor_count
#print axioms RefinedWeightsIndependentReview.inner_near_entries_are_exact
#print axioms RefinedWeightsIndependentReview.outer_far_entries_are_global
#print axioms RefinedWeightsIndependentReview.unary_outer_has_empty_marks
#print axioms RefinedWeightsIndependentReview.identical_outer_and_fine_marks_all
#print axioms RefinedWeightsIndependentReview.raw_family_near_weight_transport
#print axioms RefinedWeightsIndependentReview.raw_full_nested_summand
#print axioms RefinedWeightsIndependentReview.all_unary_inner_coefficients_one
#print axioms RefinedWeightsIndependentReview.raw_marks_match_actual_bijection
#print axioms NearFarFactorizationIndependentReview.inverse_factorization_order
#print axioms NearFarFactorizationIndependentReview.output_independent_with_actual_inverse
#print axioms NearFarFactorizationIndependentReview.inverse_target_E_has_far_only_output
#print axioms NearFarFactorizationIndependentReview.actual_root_all_near_arrays
#print axioms NearFarFactorizationIndependentReview.far_only_output_physical_root_shift
#print axioms NearFarFactorizationIndependentReview.all_interval_E_and_leaf_B_values
#print axioms NearFarFactorizationIndependentReview.unary_marked_sum_retains_coordinate
#print axioms FaroutIndependentReview.all_physical_positions_once
#print axioms FaroutIndependentReview.translated_leaf_count
#print axioms FaroutIndependentReview.all_physical_subintervals
#print axioms FaroutIndependentReview.all_raw_parts_and_cuts
#print axioms FaroutIndependentReview.unary_is_preserved
#print axioms FaroutIndependentReview.complete_composition_cardinality
#print axioms FaroutIndependentReview.actual_child_product
#print axioms FaroutIndependentReview.all_actual_samples
#print axioms FaroutIndependentReview.local_inverse_solves_actual_restriction
#print axioms FaroutIndependentReview.restricted_c_is_actual_local_inverse
#print axioms FaroutIndependentReview.full_contiguous_word_and_directed_root
#print axioms FaroutIndependentReview.nonleaf_has_three_vertices
#print axioms FaroutIndependentReview.local_root_without_global_G1
#print axioms FaroutIndependentReview.aggregate_polynomials_both_directions
#print axioms FaroutIndependentReview.aggregate_factorization_on_every_array
#print axioms FaroutIndependentReview.aggregate_geometry_and_actual_full_root
#print axioms FaroutIndependentReview.aggregate_near_freedom_has_real_solutions
#print axioms FaroutIndependentReview.aggregate_open_leaf_and_nonleaf
