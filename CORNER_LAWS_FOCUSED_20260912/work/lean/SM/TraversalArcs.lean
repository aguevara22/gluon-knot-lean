import SM.TraversalRelabel

/-! Open complementary arcs and rotation of four alternating traversal points.
These are statements about the actual traversal order, including its cut. -/

namespace SM

variable {n : ℕ}

theorem traversalBetween_complement [NeZero n] {p q r : TraversalPoint n}
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p) :
    traversalBetween p q r ↔ ¬ traversalBetween r q p := by
  letI := traversalCircularOrder (n := n)
  change sbtw p q r ↔ ¬ sbtw r q p
  constructor
  · exact sbtw_asymm
  · intro h
    have hb : btw p q r := btw_iff_not_sbtw.mpr h
    apply hb.sbtw_of_not_btw
    intro hr
    rcases hb.antisymm hr with he | he | he
    · exact hpq he
    · exact hqr he
    · exact hrp he

theorem traversalAlternating_rotate {p q r s : TraversalPoint n}
    (hpqr : traversalBetween p q r) (hrsp : traversalBetween r s p) :
    traversalBetween q r s ∧ traversalBetween s p q := by
  unfold traversalBetween at *
  rcases hpqr with h | h | h <;> rcases hrsp with k | k | k <;>
    rcases h with ⟨h₁, h₂⟩ <;> rcases k with ⟨k₁, k₂⟩ <;>
    constructor <;>
    first | exact Or.inl ⟨by linarith, by linarith⟩
          | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
          | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

end SM
