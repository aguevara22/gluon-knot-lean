import Mathlib.Data.Sign.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-! Finite sign algebra for the actual V-wall bigon/sliding alternatives.
The opposite-side condition is exactly the source real product inequality. -/

namespace SM

theorem sign_contact_complement (p q u : SignType)
    (h : (p : ℝ) * (q : ℝ) < 0) (hu : u ≠ 0) :
    p * u = -1 ↔ q * u ≠ -1 := by
  cases p <;> cases q <;> cases u <;> norm_num at *

theorem sign_contact_bigon (p q u v : SignType)
    (h : (p : ℝ) * (q : ℝ) < 0) (hu : u ≠ 0) (he : u = v) :
    (p * u = -1 ∧ p * v = -1 ∧ q * u ≠ -1 ∧ q * v ≠ -1) ∨
    (p * u ≠ -1 ∧ p * v ≠ -1 ∧ q * u = -1 ∧ q * v = -1) := by
  subst v
  have hc := sign_contact_complement p q u h hu
  by_cases hp : p * u = -1
  · exact Or.inl ⟨hp, hp, hc.mp hp, hc.mp hp⟩
  · have hq : q * u = -1 := by
      by_contra hn
      exact hp (hc.mpr hn)
    exact Or.inr ⟨hp, hp, hq, hq⟩

theorem sign_contact_sliding (p q u v : SignType)
    (h : (p : ℝ) * (q : ℝ) < 0) (hu : u ≠ 0) (hv : v ≠ 0) (hne : u ≠ v) :
    (p * u = -1 ∧ p * v ≠ -1 ∧ q * u ≠ -1 ∧ q * v = -1) ∨
    (p * u ≠ -1 ∧ p * v = -1 ∧ q * u = -1 ∧ q * v ≠ -1) := by
  cases p <;> cases q <;> cases u <;> cases v <;> norm_num at *

end SM
