namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Every coordinate of the actual proposed ordinary array satisfies the full
near/far equation. The five exhaustive interval cases include the duplicate
singleton and unary compositions; no recurrence is assumed of the proposed array. -/
theorem ordinaryLift_equation (s : Fin n) (H0 : TripleArray n ℚ) (t : Fin n → ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    nearFarTransform (parentNear s t) (tripleLift s H0 t)
      (ordinaryLift s (t (cyclicPred s)) (t (cyclicSucc s)) t
        (nearFarInverse (coreNear s t) H0 boundaryUnitArray)) = boundaryUnitArray := by
  funext I
  rcases interval_five_cases s I with ha | hd | ⟨hl, hr⟩ | ⟨hl, hr⟩ | ⟨hl, hr⟩
  · exact ordinaryLift_equation_avoiding s I (not_duplicate_of_not_contains s I ha)
      ha H0 (t (cyclicPred s)) (t (cyclicSucc s)) t
  · subst I
    exact ordinaryLift_equation_duplicate s (t (cyclicPred s)) (t (cyclicSucc s)) t
      (nearFarInverse (coreNear s t) H0 boundaryUnitArray) (parentNear s t) (tripleLift s H0 t)
  · exact ordinaryLift_equation_starting s I (not_duplicate_of_right_gt s I hr) hl hr H0 t
  · exact ordinaryLift_equation_ending s I (not_duplicate_of_left_lt s I hl) hl hr H0 t
  · exact ordinaryLift_equation_spanning s I (not_duplicate_of_left_lt s I hl) hl hr H0 t hH ht

/-- Finite triangular uniqueness identifies the five-row formula with the
actual parent ordinary inverse. This concludes the ordinary-array verification
before any substitution into a root transform or geometric specialization. -/
theorem ordinaryLift_eq_parent_inverse (s : Fin n) (H0 : TripleArray n ℚ) (t : Fin n → ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    ordinaryLift s (t (cyclicPred s)) (t (cyclicSucc s)) t
      (nearFarInverse (coreNear s t) H0 boundaryUnitArray) =
      nearFarInverse (parentNear s t) (tripleLift s H0 t) boundaryUnitArray := by
  exact nearFar_solution_unique (parentNear s t) (tripleLift s H0 t) _ boundaryUnitArray
    (ordinaryLift_equation s H0 t hH ht)

/-- Every interior duplicate position strictly spans the actual full interval. -/
theorem full_spanning_bounds (hn : 3 ≤ n) (s : Fin n)
    (hfirst : s.val ≠ 0) (hlast : s.val ≠ n - 1) :
    (fullBoundaryInterval (by omega : 3 ≤ n + 1)).left < A s ∧
      B s < (fullBoundaryInterval (by omega : 3 ≤ n + 1)).right := by
  have hs := s.isLt
  constructor
  · change 0 < s.val
    omega
  · change s.val + 1 < n + 1 - 1
    omega

/-- At every duplicate position, the complete auxiliary root transform of the
proposed lift has the source multiplier. Endpoint cases use their actual cyclic
neighbors; the strict case includes every cut fiber and zero exterior factors. -/
theorem rootTransform_full_ordinaryLift (hn : 3 ≤ n) (s : Fin n)
    (H0 : TripleArray n ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    nearFarTransform (parentNear s t) (-tripleLift s H0 t)
      (ordinaryLift s (t (cyclicPred s)) (t (cyclicSucc s)) t b0)
      (fullBoundaryInterval (by omega : 3 ≤ n + 1)) =
      ((t (cyclicPred s) + t (cyclicSucc s)) / 2) *
        nearFarTransform (coreNear s t) (-H0) b0 (fullBoundaryInterval hn) := by
  change nearFarTransform (tripleLift s (coreNear s t) t) (-tripleLift s H0 t) _ _ = _
  by_cases hfirst : s.val = 0
  · exact rootTransform_full_start hn s hfirst (coreNear s t) H0 t b0
  · by_cases hlast : s.val = n - 1
    · exact rootTransform_full_end hn s hlast (coreNear s t) H0 t b0
    · have hb := full_spanning_bounds hn s hfirst hlast
      simpa only [collapse_fullInterval hn s] using
        (rootTransform_spanning s (fullBoundaryInterval (by omega : 3 ≤ n + 1))
          (fullInterval_not_duplicate hn s) hb.1 hb.2 H0
          (t (cyclicPred s)) (t (cyclicSucc s)) t t b0 hH ht)

/-- The full auxiliary root duplication identity now uses the actual ordinary
inverse on both sides. Near-array independence and geometric specialization
remain separate obligations; they are not premises hidden in this identity. -/
theorem auxiliary_root_duplication (hn : 3 ≤ n) (s : Fin n)
    (H0 : TripleArray n ℚ) (t : Fin n → ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    nearFarTransform (parentNear s t) (-tripleLift s H0 t)
      (nearFarInverse (parentNear s t) (tripleLift s H0 t) boundaryUnitArray)
      (fullBoundaryInterval (by omega : 3 ≤ n + 1)) =
      ((t (cyclicPred s) + t (cyclicSucc s)) / 2) *
        nearFarTransform (coreNear s t) (-H0)
          (nearFarInverse (coreNear s t) H0 boundaryUnitArray) (fullBoundaryInterval hn) := by
  rw [← ordinaryLift_eq_parent_inverse s H0 t hH ht]
  exact rootTransform_full_ordinaryLift hn s H0 t
    (nearFarInverse (coreNear s t) H0 boundaryUnitArray) hH ht

/-- The formal duplication identity for the complete far-only output. The
existing complete-output factorization removes the auxiliary near arrays on
both sides; no independence of individual open sums is asserted. -/
theorem farOnlyOutput_duplication (hn : 3 ≤ n) (s : Fin n)
    (H0 : TripleArray n ℚ) (t : Fin n → ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    farOnlyOutput (tripleLift s H0 t) (fullBoundaryInterval (by omega : 3 ≤ n + 1)) =
      ((t (cyclicPred s) + t (cyclicSucc s)) / 2) *
        farOnlyOutput H0 (fullBoundaryInterval hn) := by
  have hp := reversedFar_output_of_solution (parentNear s t) (tripleLift s H0 t)
    (nearFarInverse (parentNear s t) (tripleLift s H0 t) boundaryUnitArray) boundaryUnitArray
    (nearFarTransform_inverse (parentNear s t) (tripleLift s H0 t) boundaryUnitArray)
  have hc := reversedFar_output_of_solution (coreNear s t) H0
    (nearFarInverse (coreNear s t) H0 boundaryUnitArray) boundaryUnitArray
    (nearFarTransform_inverse (coreNear s t) H0 boundaryUnitArray)
  have hd := auxiliary_root_duplication hn s H0 t hH ht
  rw [hp, hc] at hd
  exact hd

end
end SM.SoftDuplication
