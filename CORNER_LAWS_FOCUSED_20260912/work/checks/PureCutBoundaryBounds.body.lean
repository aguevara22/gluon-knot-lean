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
