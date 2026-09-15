import SM.PureCutIndices
import SM.ConsecutiveTriples
import SM.TreeCoefficient
import SM.CriticalCutSplit
import Mathlib.Tactic

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

namespace IncreasingBoundaryTriple

def positionSet (t : IncreasingBoundaryTriple n) : Finset (Fin n) :=
  {t.lower, t.middle, t.upper}

theorem positionSet_bounds (t : IncreasingBoundaryTriple n) (x : Fin n)
    (hx : x ∈ t.positionSet) : t.lower ≤ x ∧ x ≤ t.upper := by
  simp only [positionSet, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨le_rfl, le_of_lt (lt_trans t.lower_middle t.middle_upper)⟩
  · exact ⟨le_of_lt t.lower_middle, le_of_lt t.middle_upper⟩
  · exact ⟨le_of_lt (lt_trans t.lower_middle t.middle_upper), le_rfl⟩

/-- The unordered position set determines the increasing triple. Min/max
fix both endpoints, and the distinct remaining position fixes the middle. -/
theorem positionSet_injective : Function.Injective (positionSet (n := n)) := by
  intro t u he
  have hl : t.lower = u.lower := by
    apply le_antisymm
    · exact (t.positionSet_bounds u.lower (by rw [he]; simp [positionSet])).1
    · exact (u.positionSet_bounds t.lower (by rw [← he]; simp [positionSet])).1
  have hr : t.upper = u.upper := by
    apply le_antisymm
    · exact (u.positionSet_bounds t.upper (by rw [← he]; simp [positionSet])).2
    · exact (t.positionSet_bounds u.upper (by rw [he]; simp [positionSet])).2
  have hm : t.middle = u.middle := by
    have hx : t.middle ∈ u.positionSet := by rw [← he]; simp [positionSet]
    simp only [positionSet, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · exact ((ne_of_gt t.lower_middle) (h.trans hl.symm)).elim
    · exact h
    · exact ((ne_of_lt t.middle_upper) (h.trans hr.symm)).elim
  exact eq_of_entries hl hm hr

/-- The actual unordered source vertex support in the chosen root reading. -/
def vertexSet (g : ZMod n) (t : IncreasingBoundaryTriple n) : Finset (ZMod n) :=
  t.positionSet.image (boundaryIndex g)

theorem vertexSet_injective (g : ZMod n) : Function.Injective (vertexSet g) := by
  intro t u he
  apply positionSet_injective
  exact Finset.image_injective (boundaryIndex_injective g) he

theorem vertexSet_reversed (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    t.vertexSet g = {boundaryIndex g t.upper, boundaryIndex g t.middle, boundaryIndex g t.lower} := by
  ext x
  simp [vertexSet, positionSet, or_comm, or_left_comm, or_assoc]

end IncreasingBoundaryTriple

/-- Unique zero support implies every other increasing boundary triple has
a nonzero determinant sign. This uses label injectivity of the root reading,
without inferring geometric vertex distinctness from singleton Zpt at n=3. -/
theorem boundary_chi_nonzero_off_critical (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hP : pointZeroTriples P = {t.vertexSet g})
    (u : IncreasingBoundaryTriple n) (hu : u ≠ t) :
    chi P (boundaryIndex g u.upper) (boundaryIndex g u.middle) (boundaryIndex g u.lower) ≠ 0 := by
  apply chi_nonzero_outside_singleton hP
  · exact fun h => (ne_of_gt u.middle_upper) (boundaryIndex_injective g h)
  · exact fun h => (ne_of_gt u.lower_middle) (boundaryIndex_injective g h)
  · exact fun h => (ne_of_gt (lt_trans u.lower_middle u.middle_upper)) (boundaryIndex_injective g h)
  · intro he
    have hs : u.vertexSet g = t.vertexSet g := (u.vertexSet_reversed g).trans he
    exact hu (IncreasingBoundaryTriple.vertexSet_injective g hs)

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- A singleton left gap would put two consecutive physical labels in the
critical support. No exclusion of the first boundary position is assumed. -/
theorem pureCut_left_gap_nonleaf (g : ZMod n) (t : IncreasingBoundaryTriple n)
    (h : NoConsecutive (t.vertexSet g)) : 2 ≤ t.leftInterval.leaves := by
  have hlt : t.lower.val < t.middle.val := t.lower_middle
  by_contra hsmall
  have hnext : t.middle.val = t.lower.val + 1 := by
    change ¬ 2 ≤ t.middle.val - t.lower.val at hsmall
    omega
  have hadj : boundaryIndex g t.middle = boundaryIndex g t.lower + 1 := by
    change g + (t.middle.val : ZMod n) + 1 =
      (g + (t.lower.val : ZMod n) + 1) + 1
    rw [hnext, Nat.cast_add, Nat.cast_one]
    ring
  apply h (boundaryIndex g t.lower)
  · rw [t.vertexSet_reversed g]
    simp
  · rw [← hadj, t.vertexSet_reversed g]
    simp

/-- A singleton right gap also forces consecutive physical critical labels.
The last boundary position remains available as an individual endpoint. -/
theorem pureCut_right_gap_nonleaf (g : ZMod n) (t : IncreasingBoundaryTriple n)
    (h : NoConsecutive (t.vertexSet g)) : 2 ≤ t.rightInterval.leaves := by
  have hlt : t.middle.val < t.upper.val := t.middle_upper
  by_contra hsmall
  have hnext : t.upper.val = t.middle.val + 1 := by
    change ¬ 2 ≤ t.upper.val - t.middle.val at hsmall
    omega
  have hadj : boundaryIndex g t.upper = boundaryIndex g t.middle + 1 := by
    change g + (t.upper.val : ZMod n) + 1 =
      (g + (t.middle.val : ZMod n) + 1) + 1
    rw [hnext, Nat.cast_add, Nat.cast_one]
    ring
  apply h (boundaryIndex g t.middle)
  · rw [t.vertexSet_reversed g]
    simp
  · rw [← hadj, t.vertexSet_reversed g]
    simp

/-- The source's third cyclic gap bound. Only the simultaneous extreme
positions would give a singleton wrap gap, namely the actual root g to g+1. -/
theorem pureCut_wrap_gap_nonleaf (g : ZMod n) (t : IncreasingBoundaryTriple n)
    (h : NoConsecutive (t.vertexSet g)) : 2 ≤ n + t.lower.val - t.upper.val := by
  have hu : t.upper.val < n := t.upper.isLt
  have hn : 0 < n := NeZero.pos n
  by_contra hsmall
  have hlower : t.lower.val = 0 := by omega
  have hupper : t.upper.val = n - 1 := by omega
  have hsum : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
    calc
      ((n - 1 : ℕ) : ZMod n) + 1 = (((n - 1) + 1 : ℕ) : ZMod n) := by simp
      _ = (n : ZMod n) := congrArg (fun k : ℕ => (k : ZMod n)) (Nat.sub_add_cancel hn)
      _ = 0 := ZMod.natCast_self n
  have hlast : boundaryIndex g t.upper = g := by
    change g + (t.upper.val : ZMod n) + 1 = g
    rw [hupper, add_assoc, hsum, add_zero]
  have hfirst : boundaryIndex g t.lower = g + 1 := by
    simp only [boundaryIndex, hlower, Nat.cast_zero, add_zero]
  have hadj : boundaryIndex g t.upper + 1 = boundaryIndex g t.lower := by
    rw [hlast, hfirst]
  apply h (boundaryIndex g t.upper)
  · rw [t.vertexSet_reversed g]
    simp
  · rw [hadj, t.vertexSet_reversed g]
    simp

/-- A pure-cut critical span is proper in every root reading, including
readings with lower=0 or upper=n-1 separately. Only their conjunction is ruled out. -/
theorem pureCut_span_proper (g : ZMod n) (hn : 3 ≤ n) (t : IncreasingBoundaryTriple n)
    (h : NoConsecutive (t.vertexSet g)) : t.spanInterval ≠ fullBoundaryInterval hn := by
  intro he
  have hl := congrArg (fun J : BoundaryInterval n => J.left.val) he
  have hu := congrArg (fun J : BoundaryInterval n => J.right.val) he
  dsimp [IncreasingBoundaryTriple.spanInterval, fullBoundaryInterval] at hl hu
  have hwrap := pureCut_wrap_gap_nonleaf g t h
  rw [hl, hu] at hwrap
  omega

end
end SM

#check SM.pureCut_left_gap_nonleaf
#print axioms SM.pureCut_left_gap_nonleaf

#check SM.pureCut_right_gap_nonleaf
#print axioms SM.pureCut_right_gap_nonleaf

#check SM.pureCut_wrap_gap_nonleaf
#print axioms SM.pureCut_wrap_gap_nonleaf

#check SM.pureCut_span_proper
#print axioms SM.pureCut_span_proper
