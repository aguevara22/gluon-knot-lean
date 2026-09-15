import SM.CumulativeTurns
import SM.DirectionProjection

/-! If all turns away from a chosen cut are positive, nonpositive rotation
would put all actual edges in a narrow sector. Its explicit middle direction
has positive dot product with every edge, contradicting the actual edge sum. -/

namespace SM

theorem cos_sub_of_angle_eq {a b : ℝ} (h : (a : Real.Angle) = (b : Real.Angle)) (c : ℝ) :
    Real.cos (a - c) = Real.cos (b - c) := by
  have hc := congrArg (fun q : Real.Angle => (q - (c : Real.Angle)).cos) h
  simpa only [← Real.Angle.coe_sub, Real.Angle.cos_coe] using hc

variable {n : ℕ} [NeZero n]

theorem edge_projection_from_prefix {P : LabelledTuple n} (h : Regular P) (k : ℕ) :
    planeDot (unitDirection ((planeComplex (edge P 0)).arg + turnPrefix P (n - 1) / 2))
      (edge P (k : ZMod n)) =
    euclideanLength (edge P (k : ZMod n)) * Real.cos (turnPrefix P k - turnPrefix P (n - 1) / 2) := by
  have ha : (turnPrefix P k : Real.Angle) =
      (((planeComplex (edge P (k : ZMod n))).arg - (planeComplex (edge P 0)).arg : ℝ) : Real.Angle) := by
    simpa only [edgeDirectionAngle, Real.Angle.coe_sub] using turnPrefix_coe_angle h k
  rw [unitDirection_projection]
  apply congrArg (fun x : ℝ => euclideanLength (edge P (k : ZMod n)) * x)
  calc
    Real.cos ((planeComplex (edge P (k : ZMod n))).arg -
        ((planeComplex (edge P 0)).arg + turnPrefix P (n - 1) / 2)) =
      Real.cos (((planeComplex (edge P (k : ZMod n))).arg -
        (planeComplex (edge P 0)).arg) - turnPrefix P (n - 1) / 2) := by congr 1; ring
    _ = Real.cos (turnPrefix P k - turnPrefix P (n - 1) / 2) :=
      (cos_sub_of_angle_eq ha _).symm

theorem edge_projection_from_prefix_index {P : LabelledTuple n} (h : Regular P) (i : ZMod n) :
    planeDot (unitDirection ((planeComplex (edge P 0)).arg + turnPrefix P (n - 1) / 2)) (edge P i) =
      euclideanLength (edge P i) * Real.cos (turnPrefix P i.val - turnPrefix P (n - 1) / 2) := by
  simpa only [ZMod.natCast_zmod_val] using edge_projection_from_prefix h i.val

theorem turnPrefix_lt_pi_of_rotation_nonpos {P : LabelledTuple n} (h : Regular P)
    (hr : rotationNumber P ≤ 0) : turnPrefix P (n - 1) < Real.pi := by
  have hs : (∑ i : ZMod n, principalTurn P i) ≤ 0 * (2 * Real.pi) :=
    (div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mp hr
  have hs' : turnPrefix P (n - 1) + principalTurn P 0 ≤ 0 := by
    simpa only [zero_mul, sum_principalTurn_eq_prefix] using hs
  have hb : -Real.pi < principalTurn P 0 := (principalAngle_bounds (h 0)).1
  linarith

theorem positive_edge_projection_of_short_prefix {P : LabelledTuple n} (h : Regular P)
    (hp : ∀ i : ZMod n, i ≠ 0 → 0 < principalTurn P i)
    (hL : turnPrefix P (n - 1) < Real.pi) :
    ∀ i : ZMod n, 0 < planeDot
      (unitDirection ((planeComplex (edge P 0)).arg + turnPrefix P (n - 1) / 2)) (edge P i) := by
  intro i
  rw [edge_projection_from_prefix_index h i]
  have hb := turnPrefix_bounds hp i.val_lt
  have hc : 0 < Real.cos (turnPrefix P i.val - turnPrefix P (n - 1) / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [hb.1, hb.2]
  exact mul_pos (euclideanLength_pos (h i).2.1) hc

theorem rotationNumber_pos_of_other_principalTurns_pos {P : LabelledTuple n} (h : Regular P)
    (hp : ∀ i : ZMod n, i ≠ 0 → 0 < principalTurn P i) : 0 < rotationNumber P := by
  by_contra hr
  have hL := turnPrefix_lt_pi_of_rotation_nonpos h (le_of_not_gt hr)
  exact no_positive_edge_projection P _ (positive_edge_projection_of_short_prefix h hp hL)

end SM
