import SM.Traversal

/-! Relabelling of the whole traversal circle, including all half-open edge
points, not just crossing visits. The numerical coordinate wraps exactly once. -/

namespace SM

variable {n : ℕ}

def traversalShiftEquiv (a : ZMod n) : TraversalPoint n ≃ TraversalPoint n where
  toFun := traversalShift a
  invFun := traversalShift (-a)
  left_inv p := by simp [traversalShift]
  right_inv p := by simp [traversalShift]

theorem traversalKey_nonneg (p : TraversalPoint n) : 0 ≤ traversalKey p := by
  exact add_nonneg (Nat.cast_nonneg _) p.2.property.1

theorem traversalKey_lt_size [NeZero n] (p : TraversalPoint n) : traversalKey p < n := by
  have hi : (p.1.val : ℝ) + 1 ≤ n := by exact_mod_cast p.1.val_lt
  have hp := p.2.property.2
  dsimp [traversalKey]
  linarith

theorem traversalKey_before_label [NeZero n] (a : ZMod n) (p : TraversalPoint n) :
    traversalKey p < (a.val : ℝ) ↔ p.1.val < a.val := by
  constructor
  · intro h
    by_contra hi
    have hi' : (a.val : ℝ) ≤ p.1.val := by exact_mod_cast Nat.le_of_not_gt hi
    have hp := p.2.property.1
    dsimp [traversalKey] at h
    linarith
  · intro hi
    have hi' : (p.1.val : ℝ) + 1 ≤ a.val := by exact_mod_cast hi
    have hp := p.2.property.2
    dsimp [traversalKey]
    linarith

theorem traversalKey_shift_high [NeZero n] (a : ZMod n) (p : TraversalPoint n)
    (h : a.val ≤ p.1.val) :
    traversalKey (traversalShift a p) = traversalKey p - (a.val : ℝ) := by
  dsimp [traversalKey, traversalShift]
  rw [ZMod.val_sub h, Nat.cast_sub h]
  ring

theorem traversalKey_shift_low [NeZero n] (a : ZMod n) (p : TraversalPoint n)
    (h : p.1.val < a.val) :
    traversalKey (traversalShift a p) = traversalKey p - (a.val : ℝ) + n := by
  have hne : a - p.1 ≠ 0 := by
    intro hz
    have ha : a = p.1 := sub_eq_zero.mp hz
    exact (ne_of_lt h) (congrArg ZMod.val ha).symm
  have he : p.1 - a = -(a - p.1) := by ring
  have hbound : a.val - p.1.val ≤ n := by have := a.val_lt; omega
  dsimp [traversalKey, traversalShift]
  rw [he, ZMod.neg_val, if_neg hne, ZMod.val_sub h.le,
    Nat.cast_sub hbound, Nat.cast_sub h.le]
  ring

theorem traversalKey_shift [NeZero n] (a : ZMod n) (p : TraversalPoint n) :
    traversalKey (traversalShift a p) =
      if traversalKey p < (a.val : ℝ) then traversalKey p - (a.val : ℝ) + n
      else traversalKey p - (a.val : ℝ) := by
  by_cases h : p.1.val < a.val
  · rw [if_pos ((traversalKey_before_label a p).mpr h)]
    exact traversalKey_shift_low a p h
  · rw [if_neg (fun ht => h ((traversalKey_before_label a p).mp ht))]
    exact traversalKey_shift_high a p (Nat.le_of_not_gt h)

/-- The key lies in [0,n); adding n to points before the new cut and subtracting
the cut from all keys cyclically permutes their order. Each branch below uses
these bounds, so it does not silently assume an unbounded linear translation. -/
theorem traversalBetween_shift [NeZero n] (a : ZMod n) (p q r : TraversalPoint n) :
    traversalBetween (traversalShift a p) (traversalShift a q) (traversalShift a r) ↔
      traversalBetween p q r := by
  have hp0 := traversalKey_nonneg p
  have hq0 := traversalKey_nonneg q
  have hr0 := traversalKey_nonneg r
  have hpn := traversalKey_lt_size p
  have hqn := traversalKey_lt_size q
  have hrn := traversalKey_lt_size r
  unfold traversalBetween
  rw [traversalKey_shift, traversalKey_shift, traversalKey_shift]
  split_ifs <;>
    constructor <;>
    rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

end SM
