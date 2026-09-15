import SM.NearFar
import SM.MarkedRefinement
import SM.InteriorCutIndex
import SM.NearFarCutExpansion
import SM.GeometricNearFar
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

#print axioms SM.nearTransform_of_nearFar_solution
#print axioms SM.reversedFar_output_of_solution
#print axioms SM.complete_output_near_independent
#print axioms SM.farOnlyCoordinates_equation
#print axioms SM.geometric_farOnly_output
#print axioms SM.treeCoefficient_farOnly
#print axioms SM.nearFarTransform_leaf
#print axioms SM.boundaryUnitArray_leaf
#print axioms SM.farOnlyCoordinates_leaf
#print axioms SM.farOnly_leaf_values
#print axioms SM.farOnly_nonleaf_E
