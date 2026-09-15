import SM.AngleScaling
import Mathlib.Algebra.Module.Torsion.Free

/-! Strict affine betweenness in the actual plane and the resulting exact
positive decomposition of the two consecutive edge vectors. -/

namespace SM

def StrictBetween (a x b : Plane) : Prop :=
  a ≠ b ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = a + t • (b - a)

theorem strictBetween_parameter_unique {a x b : Plane} (h : StrictBetween a x b) :
    ∃! t : ℝ, 0 < t ∧ t < 1 ∧ x = a + t • (b - a) := by
  obtain ⟨hab, t, ht0, ht1, ht⟩ := h
  refine ⟨t, ⟨ht0, ht1, ht⟩, ?_⟩
  intro s hs
  exact smul_left_injective ℝ (sub_ne_zero.mpr hab.symm)
    (add_left_cancel (hs.2.2.symm.trans ht))

theorem strictBetween_fusion {a x b : Plane} (h : StrictBetween a x b) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x - a = t • (b - a) ∧
      b - x = (1 - t) • (b - a) := by
  obtain ⟨_, t, ht0, ht1, ht⟩ := h
  refine ⟨t, ht0, ht1, ?_, ?_⟩
  · rw [ht]
    abel
  · rw [ht]
    ext <;> dsimp <;> ring

theorem strictBetween_regularPair {a x b : Plane} (h : StrictBetween a x b) :
    RegularPair (x - a) (b - x) := by
  have hw : b - a ≠ 0 := sub_ne_zero.mpr h.1.symm
  obtain ⟨t, ht0, ht1, hu, hv⟩ := strictBetween_fusion h
  rw [hu, hv]
  exact regularPair_smul ht0 (sub_pos.mpr ht1) (regularPair_self hw)

theorem strictBetween_positive_multiple {a x b : Plane} (h : StrictBetween a x b) :
    ∃ r : ℝ, 0 < r ∧ b - x = r • (x - a) := by
  obtain ⟨t, ht0, ht1, hu, hv⟩ := strictBetween_fusion h
  refine ⟨(1 - t) / t, div_pos (sub_pos.mpr ht1) ht0, ?_⟩
  rw [hu, hv, smul_smul, div_mul_cancel₀ _ ht0.ne']

theorem strictBetween_reverse {a x b : Plane} (h : StrictBetween a x b) :
    StrictBetween b x a := by
  obtain ⟨hab, t, ht0, ht1, ht⟩ := h
  refine ⟨hab.symm, 1 - t, sub_pos.mpr ht1, by linarith, ?_⟩
  rw [ht]
  ext <;> dsimp <;> ring

end SM
