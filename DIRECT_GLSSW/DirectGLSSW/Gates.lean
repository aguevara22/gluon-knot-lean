import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact GLSSW gate algebra

Source labels: `ep:linear-gates`, `ep:endpoint-two-lifts`, `ep:three-lifts`.
No determinant is evaluated at zero. Geometric realization is a later layer.
-/

namespace DirectGLSSW

inductive Sign where
  | neg
  | pos
  deriving DecidableEq, Repr

@[simp] theorem Sign.neg_ne_pos : Sign.neg ≠ Sign.pos := by
  intro h
  cases h

@[simp] theorem Sign.pos_ne_neg : Sign.pos ≠ Sign.neg := by
  intro h
  cases h

def Sign.value : Sign → ℚ
  | .neg => -1
  | .pos => 1

def Sign.reverse : Sign → Sign
  | .neg => .pos
  | .pos => .neg

@[simp] theorem Sign.value_sq (s : Sign) : s.value ^ 2 = 1 := by
  cases s <;> norm_num [Sign.value]

@[simp] theorem Sign.value_reverse (s : Sign) : s.reverse.value = -s.value := by
  cases s <;> norm_num [Sign.reverse, Sign.value]

def ordinaryGate (d h : Sign) : ℚ := (d.value - h.value) / 2

def markedGate (d h : Sign) : ℚ := (d.value + h.value) / 2

theorem ordinaryGate_eq (d h : Sign) :
    ordinaryGate d h = if d = h then 0 else d.value := by
  cases d <;> cases h <;> norm_num [ordinaryGate, Sign.value]

theorem markedGate_eq (d h : Sign) :
    markedGate d h = if d = h then d.value else 0 := by
  cases d <;> cases h <;> norm_num [markedGate, Sign.value]

theorem markedGate_sub_ordinaryGate (d h : Sign) :
    markedGate d h - ordinaryGate d h = h.value := by
  unfold markedGate ordinaryGate
  ring

theorem markedGate_add_ordinaryGate (d h : Sign) :
    markedGate d h + ordinaryGate d h = d.value := by
  unfold markedGate ordinaryGate
  ring

theorem ordinaryGate_reverse (d h : Sign) :
    ordinaryGate d.reverse h.reverse = -ordinaryGate d h := by
  simp only [ordinaryGate, Sign.value_reverse]
  ring

theorem markedGate_reverse (d h : Sign) :
    markedGate d.reverse h.reverse = -markedGate d h := by
  simp only [markedGate, Sign.value_reverse]
  ring

/-- The two lifts of a collapsed endpoint cut list have this total weight.
The identity is algebraic and does not require the inputs to be signs. -/
theorem endpoint_two_lifts (β x y η : ℚ) :
    (β - x) / 2 + (x + η * y) / 2 = (β + η * y) / 2 := by
  ring

/-- Exactly the three-lift cancellation used in short-edge insertion.
This proves its scalar identity, not the geometric enumeration of lifts. -/
theorem spanning_three_lifts (a b h η : Sign) :
    -(a.value + b.value) * (a.value + η.value * h.value) / 4
      + (a.value + η.value * h.value) * (b.value + η.value * h.value) / 4 = 0 := by
  cases a <;> cases b <;> cases h <;> cases η <;> norm_num [Sign.value]

/-- The smoothing-containing and smoothing-free contributions combine
to a first-under projector. Source: `un:primitive-jump`. -/
theorem primitive_jump_coefficient (δ : ℚ) :
    δ - (1 + δ) / 2 = (δ - 1) / 2 := by
  ring

theorem primitive_jump_projector (δ : Sign) :
    (δ.value - 1) / 2 = if δ = .neg then -1 else 0 := by
  cases δ <;> norm_num [Sign.value]

end DirectGLSSW
