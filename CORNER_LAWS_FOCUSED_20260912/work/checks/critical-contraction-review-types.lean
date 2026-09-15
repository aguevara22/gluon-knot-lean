import SM.CriticalSourceResponse

namespace SM.IncreasingBoundaryTriple

noncomputable section
variable {n : ℕ}

/-- Contract the entire positive-length critical arc to one leaf by deleting
exactly its strictly interior positions, retaining both endpoints. -/
def erasedInteriorCount (t : IncreasingBoundaryTriple n) : ℕ :=
  t.upper.val - t.lower.val - 1

def contractedSize (t : IncreasingBoundaryTriple n) : ℕ :=
  n - t.erasedInteriorCount

theorem erasedInteriorCount_pos (t : IncreasingBoundaryTriple n) :
    0 < t.erasedInteriorCount := by
  have hl := t.lower_middle
  have hr := t.middle_upper
  change t.lower.val < t.middle.val at hl
  change t.middle.val < t.upper.val at hr
  unfold erasedInteriorCount
  omega

/-- Both endpoints survive, even when the contracted word is one formal
leaf. No arity-three polygon amplitude is inferred from this bound. -/
theorem contractedSize_bounds (t : IncreasingBoundaryTriple n) :
    t.lower.val + 2 ≤ t.contractedSize ∧ t.contractedSize ≤ n := by
  have hu := t.upper.isLt
  have hl := lt_trans t.lower_middle t.middle_upper
  change t.lower.val < t.upper.val at hl
  unfold contractedSize erasedInteriorCount
  omega

def expandPosition (t : IncreasingBoundaryTriple n) (k : Fin t.contractedSize) : Fin n :=
  if hk : k.val ≤ t.lower.val then
    ⟨k.val, lt_of_le_of_lt hk t.lower.isLt⟩
  else
    ⟨k.val + t.erasedInteriorCount, by
      have hb := k.isLt
      unfold contractedSize at hb
      omega⟩

theorem expandPosition_val (t : IncreasingBoundaryTriple n) (k : Fin t.contractedSize) :
    (t.expandPosition k).val =
      if k.val ≤ t.lower.val then k.val else k.val + t.erasedInteriorCount := by
  unfold expandPosition
  split_ifs <;> rfl

theorem expandPosition_strict (t : IncreasingBoundaryTriple n) : StrictMono t.expandPosition := by
  intro a b hab
  change a.val < b.val at hab
  change (t.expandPosition a).val < (t.expandPosition b).val
  rw [expandPosition_val, expandPosition_val]
  split_ifs <;> omega

theorem expandPosition_lower (t : IncreasingBoundaryTriple n) :
    t.expandPosition ⟨t.lower.val, by have := t.contractedSize_bounds; omega⟩ = t.lower := by
  apply Fin.ext
  rw [expandPosition_val]
  simp

/-- The distinguished surviving edge expands from the old first endpoint
directly to the old last endpoint, not to the old critical middle vertex. -/
theorem expandPosition_upper (t : IncreasingBoundaryTriple n) :
    t.expandPosition ⟨t.lower.val + 1, by have := t.contractedSize_bounds; omega⟩ = t.upper := by
  apply Fin.ext
  rw [expandPosition_val]
  have hl := lt_trans t.lower_middle t.middle_upper
  change t.lower.val < t.upper.val at hl
  simp only [show ¬ t.lower.val + 1 ≤ t.lower.val by omega, ite_false]
  unfold erasedInteriorCount
  omega

theorem expandPosition_survives (t : IncreasingBoundaryTriple n) (k : Fin t.contractedSize) :
    t.expandPosition k ≤ t.lower ∨ t.upper ≤ t.expandPosition k := by
  change (t.expandPosition k).val ≤ t.lower.val ∨ t.upper.val ≤ (t.expandPosition k).val
  rw [expandPosition_val]
  have hl := lt_trans t.lower_middle t.middle_upper
  change t.lower.val < t.upper.val at hl
  unfold erasedInteriorCount
  split_ifs <;> omega

/-- Translate back only surviving positions. The range condition excludes
every deleted interior position explicitly. -/
def contractPosition (t : IncreasingBoundaryTriple n) (x : Fin n)
    (hx : x ≤ t.lower ∨ t.upper ≤ x) : Fin t.contractedSize :=
  ⟨if x.val ≤ t.lower.val then x.val else x.val - t.erasedInteriorCount, by
    have hb := t.contractedSize_bounds
    have hxn := x.isLt
    change x.val ≤ t.lower.val ∨ t.upper.val ≤ x.val at hx
    have hl := lt_trans t.lower_middle t.middle_upper
    change t.lower.val < t.upper.val at hl
    unfold contractedSize erasedInteriorCount at *
    split_ifs <;> omega⟩

theorem expand_contractPosition (t : IncreasingBoundaryTriple n) (x : Fin n)
    (hx : x ≤ t.lower ∨ t.upper ≤ x) : t.expandPosition (t.contractPosition x hx) = x := by
  apply Fin.ext
  rw [expandPosition_val]
  simp only [contractPosition]
  change x.val ≤ t.lower.val ∨ t.upper.val ≤ x.val at hx
  have hl := lt_trans t.lower_middle t.middle_upper
  change t.lower.val < t.upper.val at hl
  unfold erasedInteriorCount
  split_ifs <;> omega

theorem contract_expandPosition (t : IncreasingBoundaryTriple n) (k : Fin t.contractedSize) :
    t.contractPosition (t.expandPosition k) (t.expandPosition_survives k) = k := by
  apply Fin.ext
  change (if (t.expandPosition k).val ≤ t.lower.val then (t.expandPosition k).val
    else (t.expandPosition k).val - t.erasedInteriorCount) = k.val
  rw [expandPosition_val]
  split_ifs <;> omega

/-- A bijection onto every surviving boundary position, in the original
linear reading. It deletes exactly the open critical arc. -/
def survivingPositionEquiv (t : IncreasingBoundaryTriple n) :
    Fin t.contractedSize ≃ {x : Fin n // x ≤ t.lower ∨ t.upper ≤ x} where
  toFun k := ⟨t.expandPosition k, t.expandPosition_survives k⟩
  invFun x := t.contractPosition x.val x.property
  left_inv := t.contract_expandPosition
  right_inv x := Subtype.ext (t.expand_contractPosition x.val x.property)

end
end SM.IncreasingBoundaryTriple

namespace SM.IncreasingBoundaryTriple

noncomputable section
variable {n : ℕ} [NeZero n]

theorem expandPosition_initial (t : IncreasingBoundaryTriple n) :
    (t.expandPosition ⟨0, by have := t.contractedSize_bounds; omega⟩).val = 0 := by
  rw [expandPosition_val]
  simp

/-- Both ends of the complete linear word survive contraction. Together
with the first-position identity this preserves the physical closing edge. -/
theorem expandPosition_final (t : IncreasingBoundaryTriple n) :
    (t.expandPosition ⟨t.contractedSize - 1, by have := t.contractedSize_bounds; omega⟩).val = n - 1 := by
  rw [expandPosition_val]
  have hb := t.contractedSize_bounds
  have he : ¬ t.contractedSize - 1 ≤ t.lower.val := by omega
  rw [if_neg he]
  change t.contractedSize - 1 + t.erasedInteriorCount = n - 1
  unfold contractedSize at *
  omega

/-- Exactly the full-span case contracts the complete word to one formal
leaf. This characterizes, rather than suppresses, the two-position case. -/
theorem contractedSize_eq_two_iff (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n) :
    t.contractedSize = 2 ↔ t.spanInterval = fullBoundaryInterval hn := by
  constructor
  · intro hs
    have hb := t.contractedSize_bounds
    have hl : t.lower.val = 0 := by omega
    have hu : t.upper.val = n - 1 := by
      have hu := t.upper.isLt
      have hlt := lt_trans t.lower_middle t.middle_upper
      change t.lower.val < t.upper.val at hlt
      unfold contractedSize erasedInteriorCount at hs
      omega
    apply BoundaryInterval.eq_of_endpoints
    · apply Fin.ext
      exact hl
    · apply Fin.ext
      exact hu
  · intro he
    have hl := congrArg (fun I : BoundaryInterval n => I.left.val) he
    have hu := congrArg (fun I : BoundaryInterval n => I.right.val) he
    change t.lower.val = 0 at hl
    change t.upper.val = n - 1 at hu
    unfold contractedSize erasedInteriorCount
    rw [hl, hu]
    omega

/-- Every proper critical span leaves at least three actual positions, so
the final contracted polygon may use the source's arity-three amplitude. -/
theorem contractedSize_of_proper (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n)
    (hproper : t.spanInterval ≠ fullBoundaryInterval hn) : 3 ≤ t.contractedSize := by
  have hb := t.contractedSize_bounds
  have he : t.contractedSize ≠ 2 := fun h => hproper ((t.contractedSize_eq_two_iff hn).mp h)
  omega

end
end SM.IncreasingBoundaryTriple

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

#check SM.IncreasingBoundaryTriple.erasedInteriorCount
#print axioms SM.IncreasingBoundaryTriple.erasedInteriorCount
#check SM.IncreasingBoundaryTriple.contractedSize
#print axioms SM.IncreasingBoundaryTriple.contractedSize
#check SM.IncreasingBoundaryTriple.erasedInteriorCount_pos
#print axioms SM.IncreasingBoundaryTriple.erasedInteriorCount_pos
#check SM.IncreasingBoundaryTriple.contractedSize_bounds
#print axioms SM.IncreasingBoundaryTriple.contractedSize_bounds
#check SM.IncreasingBoundaryTriple.expandPosition
#print axioms SM.IncreasingBoundaryTriple.expandPosition
#check SM.IncreasingBoundaryTriple.expandPosition_val
#print axioms SM.IncreasingBoundaryTriple.expandPosition_val
#check SM.IncreasingBoundaryTriple.expandPosition_strict
#print axioms SM.IncreasingBoundaryTriple.expandPosition_strict
#check SM.IncreasingBoundaryTriple.expandPosition_lower
#print axioms SM.IncreasingBoundaryTriple.expandPosition_lower
#check SM.IncreasingBoundaryTriple.expandPosition_upper
#print axioms SM.IncreasingBoundaryTriple.expandPosition_upper
#check SM.IncreasingBoundaryTriple.expandPosition_survives
#print axioms SM.IncreasingBoundaryTriple.expandPosition_survives
#check SM.IncreasingBoundaryTriple.contractPosition
#print axioms SM.IncreasingBoundaryTriple.contractPosition
#check SM.IncreasingBoundaryTriple.expand_contractPosition
#print axioms SM.IncreasingBoundaryTriple.expand_contractPosition
#check SM.IncreasingBoundaryTriple.contract_expandPosition
#print axioms SM.IncreasingBoundaryTriple.contract_expandPosition
#check SM.IncreasingBoundaryTriple.survivingPositionEquiv
#print axioms SM.IncreasingBoundaryTriple.survivingPositionEquiv
#check SM.IncreasingBoundaryTriple.expandPosition_initial
#print axioms SM.IncreasingBoundaryTriple.expandPosition_initial
#check SM.IncreasingBoundaryTriple.expandPosition_final
#print axioms SM.IncreasingBoundaryTriple.expandPosition_final
#check SM.IncreasingBoundaryTriple.contractedSize_eq_two_iff
#print axioms SM.IncreasingBoundaryTriple.contractedSize_eq_two_iff
#check SM.IncreasingBoundaryTriple.contractedSize_of_proper
#print axioms SM.IncreasingBoundaryTriple.contractedSize_of_proper
#check CriticalContractionIndependentReview.surviving_range_iff
#print axioms CriticalContractionIndependentReview.surviving_range_iff
#check CriticalContractionIndependentReview.every_survivor_has_unique_preimage
#print axioms CriticalContractionIndependentReview.every_survivor_has_unique_preimage
#check CriticalContractionIndependentReview.deleted_range_iff
#print axioms CriticalContractionIndependentReview.deleted_range_iff
#check CriticalContractionIndependentReview.critical_middle_is_deleted
#print axioms CriticalContractionIndependentReview.critical_middle_is_deleted
#check CriticalContractionIndependentReview.surviving_card
#print axioms CriticalContractionIndependentReview.surviving_card
#check CriticalContractionIndependentReview.contraction_strictly_reduces_positions
#print axioms CriticalContractionIndependentReview.contraction_strictly_reduces_positions
#check CriticalContractionIndependentReview.contraction_preserves_survivor_order
#print axioms CriticalContractionIndependentReview.contraction_preserves_survivor_order
#check CriticalContractionIndependentReview.distinguished_leaf_has_actual_endpoints
#print axioms CriticalContractionIndependentReview.distinguished_leaf_has_actual_endpoints
#check CriticalContractionIndependentReview.complete_word_one_leaf_iff
#print axioms CriticalContractionIndependentReview.complete_word_one_leaf_iff
#check CriticalContractionIndependentReview.proper_word_has_at_least_two_leaves
#print axioms CriticalContractionIndependentReview.proper_word_has_at_least_two_leaves
