namespace CriticalContractionIndependentReview
open SM

noncomputable section
variable {n : ℕ} [NeZero n]

-- The range is exactly the physical survivors, not merely an injection of that size.
theorem surviving_range_iff (t : IncreasingBoundaryTriple n) (x : Fin n) :
    (∃ k : Fin t.contractedSize, t.expandPosition k = x) ↔
      x ≤ t.lower ∨ t.upper ≤ x := by
  constructor
  · rintro ⟨k, hk⟩
    simpa only [hk] using t.expandPosition_survives k
  · intro hx
    exact ⟨t.contractPosition x hx, t.expand_contractPosition x hx⟩

-- Every survivor occurs once; the witness is the actual inverse position map.
theorem every_survivor_has_unique_preimage (t : IncreasingBoundaryTriple n) (x : Fin n)
    (hx : x ≤ t.lower ∨ t.upper ≤ x) :
    ∃! k : Fin t.contractedSize, t.expandPosition k = x := by
  refine ⟨t.contractPosition x hx, t.expand_contractPosition x hx, ?_⟩
  intro k hk
  apply t.expandPosition_strict.injective
  exact hk.trans (t.expand_contractPosition x hx).symm

-- Exactly the strict interior is deleted: neither endpoint disappears.
theorem deleted_range_iff (t : IncreasingBoundaryTriple n) (x : Fin n) :
    (¬ ∃ k : Fin t.contractedSize, t.expandPosition k = x) ↔
      t.lower < x ∧ x < t.upper := by
  constructor
  · intro hx
    constructor
    · by_contra hl
      exact hx ((surviving_range_iff t x).mpr (Or.inl (le_of_not_gt hl)))
    · by_contra hr
      exact hx ((surviving_range_iff t x).mpr (Or.inr (le_of_not_gt hr)))
  · rintro ⟨hl, hr⟩ hx
    rcases (surviving_range_iff t x).mp hx with hx | hx
    · exact (not_le_of_gt hl) hx
    · exact (not_le_of_gt hr) hx

-- The forbidden geometric triple loses its middle occurrence under contraction.
theorem critical_middle_is_deleted (t : IncreasingBoundaryTriple n) :
    ¬ ∃ k : Fin t.contractedSize, t.expandPosition k = t.middle :=
  (deleted_range_iff t t.middle).mpr ⟨t.lower_middle, t.middle_upper⟩

-- The concrete domain size agrees with the complete physical survivor subtype.
theorem surviving_card (t : IncreasingBoundaryTriple n) :
    Fintype.card {x : Fin n // x ≤ t.lower ∨ t.upper ≤ x} = t.contractedSize := by
  classical
  simpa only [Fintype.card_fin] using (Fintype.card_congr t.survivingPositionEquiv).symm

-- A genuine critical triple removes at least one position, without an extra n bound.
theorem contraction_strictly_reduces_positions (t : IncreasingBoundaryTriple n) :
    t.contractedSize < n := by
  have hp := t.erasedInteriorCount_pos
  have hn := t.lower.isLt
  unfold IncreasingBoundaryTriple.contractedSize
  omega

-- The inverse respects the original order on every pair of surviving positions.
theorem contraction_preserves_survivor_order (t : IncreasingBoundaryTriple n)
    (x y : Fin n) (hx : x ≤ t.lower ∨ t.upper ≤ x)
    (hy : y ≤ t.lower ∨ t.upper ≤ y) (hxy : x < y) :
    t.contractPosition x hx < t.contractPosition y hy := by
  apply t.expandPosition_strict.lt_iff_lt.mp
  simpa only [IncreasingBoundaryTriple.expand_contractPosition] using hxy

-- The distinguished contracted interval is a formal one-leaf interval with exact old endpoints.
theorem distinguished_leaf_has_actual_endpoints (t : IncreasingBoundaryTriple n) :
    ∃ J : BoundaryInterval t.contractedSize,
      J.leaves = 1 ∧ t.expandPosition J.left = t.lower ∧ t.expandPosition J.right = t.upper := by
  let J : BoundaryInterval t.contractedSize :=
    ⟨⟨t.lower.val, by have := t.contractedSize_bounds; omega⟩,
     ⟨t.lower.val + 1, by have := t.contractedSize_bounds; omega⟩,
     by change t.lower.val < t.lower.val + 1; omega⟩
  refine ⟨J, ?_, ?_, ?_⟩
  · change t.lower.val + 1 - t.lower.val = 1
    omega
  · exact t.expandPosition_lower
  · exact t.expandPosition_upper

-- The complete contracted word has one leaf exactly for the full critical span.
theorem complete_word_one_leaf_iff (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n) :
    t.contractedSize - 1 = 1 ↔ t.spanInterval = fullBoundaryInterval hn := by
  have hb := t.contractedSize_bounds
  have he : t.contractedSize - 1 = 1 ↔ t.contractedSize = 2 := by omega
  exact he.trans (t.contractedSize_eq_two_iff hn)

-- A proper critical span retains at least two leaves in the complete contracted word.
theorem proper_word_has_at_least_two_leaves (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n)
    (hp : t.spanInterval ≠ fullBoundaryInterval hn) : 2 ≤ t.contractedSize - 1 := by
  have hs := t.contractedSize_of_proper hn hp
  omega

end
end CriticalContractionIndependentReview
