import SM.RotationReversal
import Mathlib.Tactic.FinCases

/-! Exact scope test for source lem:shift(iii). This file is a separate
counterexample/repair investigation and does not replace the source claim. -/

namespace SM.ScopeInvestigation

def zeroTurnFour : LabelledTuple 4 := fun i =>
  if i = 0 then (0, 0) else if i = 1 then (1, 0) else if i = 2 then (2, 0) else (0, 1)

theorem zeroTurnFour_turns (i : ZMod 4) :
    turn zeroTurnFour i = if i = 1 then 0 else 1 := by
  fin_cases i <;> simp +decide [turn, chi, det, zeroTurnFour, ZMod]

theorem zeroTurnFour_regular : Regular zeroTurnFour := by
  apply (regular_iff_edges _).mpr
  intro i
  have hedge : edge zeroTurnFour i ≠ 0 := by
    fin_cases i <;> simp +decide [edge, zeroTurnFour, ZMod, Prod.ext_iff] <;> norm_num
  refine ⟨hedge, ?_⟩
  rintro ⟨r, hr, he⟩
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  fin_cases i
  all_goals simp +decide [edge, zeroTurnFour, ZMod] at hx hy
  all_goals linarith

theorem zeroTurnFour_left : leftTurns zeroTurnFour = 3 := by
  classical
  unfold leftTurns
  simp_rw [zeroTurnFour_turns]
  decide

theorem zeroTurnFour_reversed_left : leftTurns (reversal zeroTurnFour) = 0 := by
  classical
  unfold leftTurns
  simp_rw [turn_reversal, zeroTurnFour_turns]
  decide

theorem shift_left_count_fails_on_regular :
    ∃ P : LabelledTuple 4, Regular P ∧ leftTurns (reversal P) ≠ 4 - leftTurns P := by
  refine ⟨zeroTurnFour, zeroTurnFour_regular, ?_⟩
  rw [zeroTurnFour_reversed_left, zeroTurnFour_left]
  norm_num

#print axioms shift_left_count_fails_on_regular

end SM.ScopeInvestigation
