import SM.G1Consequences
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.FieldSimp

/-! The analytic core of SM lem:crossing-test: two strict side tests are
equivalent to a transverse intersection in the interiors of both segments. -/

namespace SM

theorem ratio_between_iff {x d : ℝ} (hd : d ≠ 0) :
    0 < x / d ∧ x / d < 1 ↔ x * (x - d) < 0 := by
  constructor
  · rintro ⟨hx, hu⟩
    rcases lt_or_gt_of_ne hd with hn | hp
    · have hx' : x < 0 := by simpa using (lt_div_iff_of_neg hn).mp hx
      have hu' : d < x := (div_lt_one_of_neg hn).mp hu
      exact mul_neg_of_neg_of_pos hx' (sub_pos.mpr hu')
    · have hx' : 0 < x := by simpa using (lt_div_iff₀ hp).mp hx
      have hu' : x < d := (div_lt_one₀ hp).mp hu
      exact mul_neg_of_pos_of_neg hx' (sub_neg.mpr hu')
  · intro h
    rcases mul_neg_iff.mp h with ⟨hx, hu⟩ | ⟨hx, hu⟩
    · have hp : 0 < d := by linarith
      exact ⟨div_pos hx hp, (div_lt_one₀ hp).mpr (by linarith)⟩
    · have hn : d < 0 := by linarith
      exact ⟨div_pos_of_neg_of_neg hx hn, (div_lt_one_of_neg hn).mpr (by linarith)⟩

theorem cramer_intersection (a b u v : Plane) (hd : det u v ≠ 0) :
    a + (det (b - a) v / det u v) • u =
    b + (det (b - a) u / det u v) • v := by
  apply Prod.ext
  · change a.1 + (det (b - a) v / det u v) * u.1 =
      b.1 + (det (b - a) u / det u v) * v.1
    apply mul_left_cancel₀ hd
    simp only [mul_add, ← mul_assoc, mul_div_cancel₀ _ hd]
    dsimp [det]
    ring
  · change a.2 + (det (b - a) v / det u v) * u.2 =
      b.2 + (det (b - a) u / det u v) * v.2
    apply mul_left_cancel₀ hd
    simp only [mul_add, ← mul_assoc, mul_div_cancel₀ _ hd]
    dsimp [det]
    ring

theorem intersection_second_parameter_identity {a b u v : Plane} {s t : ℝ}
    (h : a + s • u = b + t • v) : det (b - a) u = t * det u v := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp at hx hy
  dsimp [det]
  linear_combination -u.2 * hx + u.1 * hy

theorem side_product_first (a b u v : Plane) :
    det u (b - a) * det u (b + v - a) =
    det (b - a) u * (det (b - a) u - det u v) := by
  dsimp [det]
  ring

theorem side_product_second (a b u v : Plane) :
    det v (a - b) * det v (a + u - b) =
    det (b - a) v * (det (b - a) v - det u v) := by
  dsimp [det]
  ring

theorem segment_crossing_criterion (a b u v : Plane) :
    (∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      a + s • u = b + t • v ∧ det u v ≠ 0) ↔
    det u (b - a) * det u (b + v - a) < 0 ∧
    det v (a - b) * det v (a + u - b) < 0 := by
  rw [side_product_first, side_product_second]
  constructor
  · rintro ⟨s, t, hs0, hs1, ht0, ht1, heq, hd⟩
    have hsi : det (b - a) v / det u v = s :=
      (div_eq_iff hd).mpr (intersection_parameter_identity heq)
    have hti : det (b - a) u / det u v = t :=
      (div_eq_iff hd).mpr (intersection_second_parameter_identity heq)
    constructor
    · apply (ratio_between_iff hd).mp
      rw [hti]
      exact ⟨ht0, ht1⟩
    · apply (ratio_between_iff hd).mp
      rw [hsi]
      exact ⟨hs0, hs1⟩
  · rintro ⟨ht, hs⟩
    have hd : det u v ≠ 0 := by
      intro hz
      rw [hz, sub_zero] at ht
      exact (not_lt_of_ge (mul_self_nonneg _)) ht
    obtain ⟨hs0, hs1⟩ := (ratio_between_iff hd).mpr hs
    obtain ⟨ht0, ht1⟩ := (ratio_between_iff hd).mpr ht
    exact ⟨_, _, hs0, hs1, ht0, ht1, cramer_intersection a b u v hd, hd⟩

theorem sign_product_neg_iff (x y : ℝ) :
    SignType.sign x * SignType.sign y = -1 ↔ x * y < 0 := by
  rw [← sign_mul]
  exact sign_eq_neg_one_iff

variable {n : ℕ}

/-- The iff portion of source lem:crossing-test; the distinct-crossing and
finiteness clauses will be assembled with the actual unordered crossing set. -/
theorem crossing_test_iff (hn : 3 ≤ n) (P : LabelledTuple n) (h : G1 P)
    (i j : ZMod n) (hr : remote i j) :
    (edgeSegment P i ∩ edgeSegment P j).Nonempty ↔
    chi P i (i + 1) j * chi P i (i + 1) (j + 1) = -1 ∧
    chi P j (j + 1) i * chi P j (j + 1) (i + 1) = -1 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  simp only [chi_edge, sign_product_neg_iff]
  have hend : ∀ k : ZMod n, P k + edge P k = P (k + 1) := by
    intro k
    simp [edge]
  have crit := segment_crossing_criterion (P i) (P j) (edge P i) (edge P j)
  rw [hend i, hend j] at crit
  rw [← crit]
  constructor
  · rintro ⟨x, hxi, hxj⟩
    obtain ⟨s, hs0, hs1, hs⟩ := hxi
    obtain ⟨t, ht0, ht1, ht⟩ := hxj
    have heq := hs.symm.trans ht
    obtain ⟨hs0', hs1', ht0', ht1'⟩ :=
      g1_remote_parameters_interior h hr hs0 hs1 ht0 ht1 heq
    exact ⟨s, t, hs0', hs1', ht0', ht1', heq, g1_remote_intersection_det h hr heq⟩
  · rintro ⟨s, t, hs0, hs1, ht0, ht1, heq, _⟩
    exact ⟨edgePoint P i s, ⟨s, hs0.le, hs1.le, rfl⟩,
      ⟨t, ht0.le, ht1.le, heq⟩⟩

end SM
