import SM.NearFar
import SM.InteriorCutIndex
import SM.CompositionSegments
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

#print axioms SM.BoundaryCutSet.consecutive_eq_of_left
#print axioms SM.BoundaryCutSet.consecutive_eq_of_right
#print axioms SM.IncreasingBoundaryTriple.eq_of_entries
#print axioms SM.IncreasingBoundaryTriple.eq_of_consecutive_middle
#print axioms SM.IntervalComposition.nearTriple_leftInterval
#print axioms SM.IntervalComposition.nearTriple_rightInterval
#print axioms SM.IntervalComposition.nearTriple_consecutive
#print axioms SM.IntervalComposition.nearTriple_middle_position
#print axioms SM.IntervalComposition.nearTriple_eq_of_consecutive
