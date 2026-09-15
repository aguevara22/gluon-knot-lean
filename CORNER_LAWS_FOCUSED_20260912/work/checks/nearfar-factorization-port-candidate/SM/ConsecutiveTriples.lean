import SM.ConsecutiveCuts
import SM.InteriorCutIndex
import SM.NearFar

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
