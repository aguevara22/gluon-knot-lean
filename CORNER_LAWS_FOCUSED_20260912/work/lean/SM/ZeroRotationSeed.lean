import SM.FibreReduction
import SM.RotationReversal
import SM.CumulativeTurns
import Mathlib.Tactic.FinCases

/-! The actual four-vertex bowtie is regular and has zero total turn.
Angle cancellation avoids needing explicit arctangent values. Subdivision
and the proved full generic density give every larger zero-rotation fibre. -/

namespace SM

theorem principalAngle_neg_neg (u v : Plane) :
    principalAngle (-u) (-v) = principalAngle u v := by
  simp only [principalAngle, cornerRotor, planeComplex_neg, star_neg, neg_mul_neg]

theorem principalAngle_swap {u v : Plane} (h : RegularPair u v) :
    principalAngle v u = -principalAngle u v := by
  simpa only [principalAngle_neg_neg] using principalAngle_reverse h

def bowtieSeed : LabelledTuple 4 := fun i =>
  if i = 0 then (0, 0) else if i = 1 then (2, 2) else if i = 2 then (0, 2) else (2, 0)

theorem bowtieSeed_regular : Regular bowtieSeed := by
  apply (regular_iff_edges _).mpr
  intro i
  have hedge : edge bowtieSeed i ≠ 0 := by
    fin_cases i <;> simp +decide [edge, bowtieSeed, ZMod, Prod.ext_iff] <;> norm_num
  refine ⟨hedge, ?_⟩
  rintro ⟨r, hr, he⟩
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  fin_cases i
  all_goals simp +decide [edge, bowtieSeed, ZMod] at hx hy
  all_goals linarith

theorem bowtieSeed_turn_cancel_left :
    principalTurn bowtieSeed 0 = -principalTurn bowtieSeed 1 := by
  have h := principalAngle_swap (bowtieSeed_regular 1)
  simpa +decide [principalTurn, edge, bowtieSeed, ZMod] using h

theorem bowtieSeed_turn_cancel_right :
    principalTurn bowtieSeed 2 = -principalTurn bowtieSeed 3 := by
  have h := principalAngle_swap (bowtieSeed_regular 3)
  simpa +decide [principalTurn, edge, bowtieSeed, ZMod] using h

theorem bowtieSeed_rotation : rotationNumber bowtieSeed = 0 := by
  have hs : (∑ i : ZMod 4, principalTurn bowtieSeed i) = 0 := by
    rw [sum_zmod_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
      Nat.cast_one, zero_add]
    norm_num only
    rw [bowtieSeed_turn_cancel_left, bowtieSeed_turn_cancel_right]
    ring
  unfold rotationNumber
  rw [hs, zero_div]

theorem exists_generic_rotation_zero {n : ℕ} [NeZero n] (hn : 4 ≤ n) :
    ∃ P : LabelledTuple n, Generic P ∧ rotationNumber P = 0 := by
  obtain ⟨P, hP, hr⟩ := exists_generic_at_larger_size (by omega) bowtieSeed_regular hn
  exact ⟨P, hP, hr.trans bowtieSeed_rotation⟩

end SM
