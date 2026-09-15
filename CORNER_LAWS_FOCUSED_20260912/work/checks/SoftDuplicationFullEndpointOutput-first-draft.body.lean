namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ} [NeZero n]

/-- At the first position the actual full parent interval is a starting interval. -/
theorem full_start_bounds (hn : 3 ≤ n) (s : Fin n) (hs : s.val = 0) :
    (fullBoundaryInterval (by omega : 3 ≤ n + 1)).left = A s ∧
      B s < (fullBoundaryInterval (by omega : 3 ≤ n + 1)).right := by
  constructor
  · apply Fin.ext
    exact hs.symm
  · change s.val + 1 < n + 1 - 1
    omega

/-- At the last position the actual full parent interval is an ending interval. -/
theorem full_end_bounds (hn : 3 ≤ n) (s : Fin n) (hs : s.val = n - 1) :
    (fullBoundaryInterval (by omega : 3 ≤ n + 1)).left < A s ∧
      (fullBoundaryInterval (by omega : 3 ≤ n + 1)).right = B s := by
  constructor
  · change 0 < s.val
    omega
  · apply Fin.ext
    change n + 1 - 1 = s.val + 1
    omega

/-- The last endpoint of the core full word is the first vertex's cyclic predecessor. -/
theorem full_right_is_pred (hn : 3 ≤ n) (s : Fin n) (hs : s.val = 0) :
    (fullBoundaryInterval hn).right = cyclicPred s := by
  apply Fin.ext
  exact (cyclicPred_val_zero s hs).symm

/-- The first endpoint of the core full word is the last vertex's cyclic successor. -/
theorem full_left_is_succ (hn : 3 ≤ n) (s : Fin n) (hs : s.val = n - 1) :
    (fullBoundaryInterval hn).left = cyclicSucc s := by
  apply Fin.ext
  exact (cyclicSucc_val_last s hs).symm

/-- The complete auxiliary root transform has multiplier k at the first position.
This keeps arbitrary core arrays and b0; geometric identification remains separate. -/
theorem rootTransform_full_start (hn : 3 ≤ n) (s : Fin n) (hs : s.val = 0)
    (D0 H0 : TripleArray n ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    nearFarTransform (tripleLift s D0 t) (-tripleLift s H0 t)
      (ordinaryLift s (t (cyclicPred s)) (t (cyclicSucc s)) t b0)
      (fullBoundaryInterval (by omega : 3 ≤ n + 1)) =
      ((t (cyclicPred s) + t (cyclicSucc s)) / 2) *
        nearFarTransform D0 (-H0) b0 (fullBoundaryInterval hn) := by
  have hb := full_start_bounds hn s hs
  calc
    _ = ((t (cyclicSucc s) + t (fullBoundaryInterval hn).right) / 2) *
        nearFarTransform D0 (-H0) b0 (fullBoundaryInterval hn) := by
      simpa only [collapse_fullInterval hn s] using
        (rootTransform_starting s (fullBoundaryInterval (by omega : 3 ≤ n + 1))
          (fullInterval_not_duplicate hn s) hb.1 hb.2 D0 H0
          (t (cyclicPred s)) (t (cyclicSucc s)) t b0)
    _ = _ := by
      rw [full_right_is_pred hn s hs]
      ring

/-- The complete auxiliary root transform has the same multiplier k at the last position. -/
theorem rootTransform_full_end (hn : 3 ≤ n) (s : Fin n) (hs : s.val = n - 1)
    (D0 H0 : TripleArray n ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    nearFarTransform (tripleLift s D0 t) (-tripleLift s H0 t)
      (ordinaryLift s (t (cyclicPred s)) (t (cyclicSucc s)) t b0)
      (fullBoundaryInterval (by omega : 3 ≤ n + 1)) =
      ((t (cyclicPred s) + t (cyclicSucc s)) / 2) *
        nearFarTransform D0 (-H0) b0 (fullBoundaryInterval hn) := by
  have hb := full_end_bounds hn s hs
  calc
    _ = ((t (cyclicPred s) + t (fullBoundaryInterval hn).left) / 2) *
        nearFarTransform D0 (-H0) b0 (fullBoundaryInterval hn) := by
      simpa only [collapse_fullInterval hn s] using
        (rootTransform_ending s (fullBoundaryInterval (by omega : 3 ≤ n + 1))
          (fullInterval_not_duplicate hn s) hb.1 hb.2 D0 H0
          (t (cyclicPred s)) (t (cyclicSucc s)) t b0)
    _ = _ := by rw [full_left_is_succ hn s hs]

end
end SM.SoftDuplication
