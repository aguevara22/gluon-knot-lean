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

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- A positive-length interval belongs to at most one full child. This
also covers a contracted formal leaf without an interior vertex label. -/
theorem part_contains_unique (π : IntervalComposition I) (J : BoundaryInterval n)
    {k l : Fin π.parts}
    (hk : (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right)
    (hl : (π.part l).left ≤ J.left ∧ J.right ≤ (π.part l).right) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · exact ((not_le_of_gt J.increasing) (hk.2.trans ((π.part_order h).trans hl.1))).elim
  · exact h
  · exact ((not_le_of_gt J.increasing) (hl.2.trans ((π.part_order h).trans hk.1))).elim

theorem other_part_excludes (π : IntervalComposition I) (J : BoundaryInterval n)
    (k : Fin π.parts) (hk : (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right)
    (l : Fin π.parts) (hl : l ≠ k) :
    ¬ ((π.part l).left ≤ J.left ∧ J.right ≤ (π.part l).right) := by
  intro hc
  exact hl (π.part_contains_unique J hc hk)

variable {R : Type*} [CommRing R]

/-- If no child contains the critical span, every child inverse coordinate
is unchanged, hence so is the complete child product. -/
theorem child_product_unchanged (π : IntervalComposition I) (J : BoundaryInterval n)
    (X₁ X₂ : IntervalArray n R)
    (h : ∀ K, ¬ (K.left ≤ J.left ∧ J.right ≤ K.right) → X₁ K = X₂ K)
    (hπ : ∀ k : Fin π.parts, ¬ ((π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right)) :
    (∏ k : Fin π.parts, X₁ (π.part k)) = ∏ k : Fin π.parts, X₂ (π.part k) := by
  apply Finset.prod_congr rfl
  intro k _
  exact h _ (hπ k)

/-- Remove the unique potentially changing child from each full product.
Every remaining factor agrees; subtraction gives exactly one changed factor,
with no division and no product of two changes, including zero coordinates. -/
theorem child_product_difference (π : IntervalComposition I) (J : BoundaryInterval n)
    (X₁ X₂ : IntervalArray n R)
    (h : ∀ K, ¬ (K.left ≤ J.left ∧ J.right ≤ K.right) → X₁ K = X₂ K)
    (k : Fin π.parts) (hk : (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right) :
    (∏ l : Fin π.parts, X₂ (π.part l)) - (∏ l : Fin π.parts, X₁ (π.part l)) =
      (X₂ (π.part k) - X₁ (π.part k)) *
        ∏ l ∈ Finset.univ.erase k, X₁ (π.part l) := by
  classical
  have hp : (∏ l ∈ Finset.univ.erase k, X₂ (π.part l)) =
      ∏ l ∈ Finset.univ.erase k, X₁ (π.part l) := by
    apply Finset.prod_congr rfl
    intro l hl
    exact (h _ (π.other_part_excludes J k hk l (Finset.mem_erase.mp hl).1)).symm
  rw [← Finset.mul_prod_erase Finset.univ (fun l => X₂ (π.part l)) (Finset.mem_univ k)]
  rw [← Finset.mul_prod_erase Finset.univ (fun l => X₁ (π.part l)) (Finset.mem_univ k)]
  rw [hp]
  ring

end
end SM.IntervalComposition

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

namespace CriticalContractionChildIndependentReview
open SM

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

-- At most one index is in the entire set of children containing a positive interval.
theorem containing_child_card_le_one (π : IntervalComposition I) (J : BoundaryInterval n) :
    (Finset.univ.filter (fun k : Fin π.parts =>
      (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro k hk l hl
  exact π.part_contains_unique J (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2

-- Every formal leaf in I belongs to one complete child, including at a shared cut.
theorem formal_leaf_has_unique_child (π : IntervalComposition I) (J : BoundaryInterval n)
    (hj : J.leaves = 1) (hl : I.left ≤ J.left) (hr : J.right ≤ I.right) :
    ∃! k : Fin π.parts, (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right := by
  obtain ⟨k, hk⟩ := π.exists_halfOpen_part J.left hl (lt_of_lt_of_le J.increasing hr)
  have hkright : J.right ≤ (π.part k).right := by
    have hi := J.increasing
    change J.left.val < J.right.val at hi
    change J.right.val - J.left.val = 1 at hj
    have hp := hk.2
    change J.left.val < (π.part k).right.val at hp
    change J.right.val ≤ (π.part k).right.val
    omega
  refine ⟨k, ⟨hk.1, hkright⟩, ?_⟩
  intro l hl
  exact π.part_contains_unique J hl ⟨hk.1, hkright⟩

variable {R : Type*} [CommRing R]

-- The unaffected factor product is identical on both sides: the response has no side ambiguity.
theorem difference_uses_either_side_for_other_children (π : IntervalComposition I)
    (J : BoundaryInterval n) (X₁ X₂ : IntervalArray n R)
    (h : ∀ K, ¬ (K.left ≤ J.left ∧ J.right ≤ K.right) → X₁ K = X₂ K)
    (k : Fin π.parts) (hk : (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right) :
    (∏ l : Fin π.parts, X₂ (π.part l)) - (∏ l : Fin π.parts, X₁ (π.part l)) =
      (X₂ (π.part k) - X₁ (π.part k)) * ∏ l ∈ Finset.univ.erase k, X₂ (π.part l) := by
  classical
  rw [π.child_product_difference J X₁ X₂ h k hk]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  exact h _ (π.other_part_excludes J k hk l (Finset.mem_erase.mp hl).1)

-- Zero unaffected factors force a zero response, with no division or nonzero premise.
theorem zero_unchanged_child_annihilates_difference (π : IntervalComposition I)
    (J : BoundaryInterval n) (X₁ X₂ : IntervalArray n R)
    (h : ∀ K, ¬ (K.left ≤ J.left ∧ J.right ≤ K.right) → X₁ K = X₂ K)
    (k : Fin π.parts) (hk : (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right)
    (l : Fin π.parts) (hl : l ≠ k) (hz : X₁ (π.part l) = 0) :
    (∏ j : Fin π.parts, X₂ (π.part j)) - (∏ j : Fin π.parts, X₁ (π.part j)) = 0 := by
  classical
  rw [π.child_product_difference J X₁ X₂ h k hk]
  have hp : (∏ j ∈ Finset.univ.erase k, X₁ (π.part j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩) hz
  rw [hp, mul_zero]

-- The product response applies to actual canonical inverse coordinates on any containing parent.
theorem actual_inverse_child_response [Invertible (2 : R)]
    (H₁ H₂ : TripleArray n R) (t : IncreasingBoundaryTriple n)
    (h : ∀ u, u ≠ t → H₁ u = H₂ u) (π : IntervalComposition I)
    (k : Fin π.parts) (hk : (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right) :
    (∏ l : Fin π.parts, farOnlyCoordinates H₂ (π.part l)) -
      (∏ l : Fin π.parts, farOnlyCoordinates H₁ (π.part l)) =
        (farOnlyCoordinates H₂ (π.part k) - farOnlyCoordinates H₁ (π.part k)) *
          ∏ l ∈ Finset.univ.erase k, farOnlyCoordinates H₁ (π.part l) := by
  apply π.child_product_difference t.spanInterval (farOnlyCoordinates H₁) (farOnlyCoordinates H₂)
    (fun K hK => farOnlyCoordinates_unchanged_off_critical H₁ H₂ t h K hK) k hk

end
end CriticalContractionChildIndependentReview

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
#check SM.IntervalComposition.part_contains_unique
#print axioms SM.IntervalComposition.part_contains_unique
#check SM.IntervalComposition.other_part_excludes
#print axioms SM.IntervalComposition.other_part_excludes
#check SM.IntervalComposition.child_product_unchanged
#print axioms SM.IntervalComposition.child_product_unchanged
#check SM.IntervalComposition.child_product_difference
#print axioms SM.IntervalComposition.child_product_difference
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
#check CriticalContractionChildIndependentReview.containing_child_card_le_one
#print axioms CriticalContractionChildIndependentReview.containing_child_card_le_one
#check CriticalContractionChildIndependentReview.formal_leaf_has_unique_child
#print axioms CriticalContractionChildIndependentReview.formal_leaf_has_unique_child
#check CriticalContractionChildIndependentReview.difference_uses_either_side_for_other_children
#print axioms CriticalContractionChildIndependentReview.difference_uses_either_side_for_other_children
#check CriticalContractionChildIndependentReview.zero_unchanged_child_annihilates_difference
#print axioms CriticalContractionChildIndependentReview.zero_unchanged_child_annihilates_difference
#check CriticalContractionChildIndependentReview.actual_inverse_child_response
#print axioms CriticalContractionChildIndependentReview.actual_inverse_child_response
