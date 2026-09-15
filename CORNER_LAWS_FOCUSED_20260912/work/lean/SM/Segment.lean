import SM.Generic
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Module.Prod

/-! Coordinate lemmas needed to prove SM lem:g1 and lem:crossing-test.
Every intersection statement uses actual points of R², not an abstract relation. -/

namespace SM

def IndependentPair (u v : Plane) : Prop :=
  ∀ a b : ℝ, a • u + b • v = 0 → a = 0 ∧ b = 0

theorem independent_of_det_ne_zero {u v : Plane} (hd : det u v ≠ 0) :
    IndependentPair u v := by
  intro a b heq
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  dsimp at hx hy
  have ha : a * det u v = 0 := by
    dsimp [det]
    linear_combination v.2 * hx - v.1 * hy
  have hb : b * det u v = 0 := by
    dsimp [det]
    linear_combination u.1 * hy - u.2 * hx
  exact ⟨(mul_eq_zero.mp ha).resolve_right hd, (mul_eq_zero.mp hb).resolve_right hd⟩

theorem det_smul_right (u v : Plane) (t : ℝ) :
    det u (t • v) = t * det u v := by
  dsimp [det]
  ring

theorem det_smul_self (u : Plane) (t : ℝ) : det u (t • u) = 0 := by
  dsimp [det]
  ring

theorem det_add_right (u v w : Plane) : det u (v + w) = det u v + det u w := by
  dsimp [det]
  ring

theorem no_multiple_of_det_ne_zero {u v : Plane} (hd : det u v ≠ 0) (t : ℝ) :
    v ≠ t • u := by
  intro heq
  apply hd
  rw [heq, det_smul_self]

/-- Cramer's-rule identity before division; valid even with zero determinant. -/
theorem intersection_parameter_identity {a b u v : Plane} {s t : ℝ}
    (h : a + s • u = b + t • v) : det (b - a) v = s * det u v := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp at hx hy
  dsimp [det]
  linear_combination -v.2 * hx + v.1 * hy

theorem intersection_parameters_unique {a b u v : Plane} (hd : det u v ≠ 0)
    {s t s' t' : ℝ} (h : a + s • u = b + t • v)
    (h' : a + s' • u = b + t' • v) : s = s' ∧ t = t' := by
  have hs := intersection_parameter_identity h
  have hs' := intersection_parameter_identity h'
  have ht := intersection_parameter_identity h.symm
  have ht' := intersection_parameter_identity h'.symm
  have hd' : det v u ≠ 0 := by
    rw [det_swap]
    exact neg_ne_zero.mpr hd
  exact ⟨mul_right_cancel₀ hd (hs.symm.trans hs'),
    mul_right_cancel₀ hd' (ht.symm.trans ht')⟩

variable {n : ℕ}

theorem next_ne_self [Nontrivial (ZMod n)] (i : ZMod n) : i + 1 ≠ i := by
  intro hi
  exact one_ne_zero (add_left_cancel (hi.trans (add_zero i).symm))

theorem prev_ne_self [Nontrivial (ZMod n)] (i : ZMod n) : i - 1 ≠ i := by
  intro hi
  exact next_ne_self i (sub_eq_iff_eq_add.mp hi).symm

theorem prev_ne_next (hn : 3 ≤ n) (i : ZMod n) : i - 1 ≠ i + 1 := by
  intro h
  have htwo : (2 : ZMod n) = 0 := by linear_combination -h
  have hd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by simpa using htwo)
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

theorem g1_turn_nonzero [NeZero n] [Nontrivial (ZMod n)] (hn : 3 ≤ n)
    {P : LabelledTuple n} (h : G1 P) (i : ZMod n) :
    det (edge P (i - 1)) (edge P i) ≠ 0 :=
  g1_turn_area hn h i (prev_ne_self i) (next_ne_self i).symm (prev_ne_next hn i)

theorem remote_endpoints (i j : ZMod n) (h : remote i j) :
    j ≠ i ∧ j ≠ i + 1 ∧ j + 1 ≠ i ∧ j + 1 ≠ i + 1 := by
  have hneg : j - i ≠ -1 := fun he => h (Or.inl he)
  have hzero : j - i ≠ 0 := fun he => h (Or.inr (Or.inl he))
  have hpos : j - i ≠ 1 := fun he => h (Or.inr (Or.inr he))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun he => hzero (sub_eq_zero.mpr he)
  · intro he
    apply hpos
    rw [he, add_sub_cancel_left]
  · intro he
    apply hneg
    linear_combination he
  · intro he
    exact hzero (sub_eq_zero.mpr (add_right_cancel he))

theorem remote_symm {i j : ZMod n} (h : remote i j) : remote j i := by
  rintro (hneg | hzero | hpos)
  · apply h
    right; right
    linear_combination -hneg
  · apply h
    right; left
    linear_combination -hzero
  · apply h
    left
    linear_combination -hpos

theorem g1_remote_intersection_det [Nontrivial (ZMod n)]
    {P : LabelledTuple n} (h : G1 P) {i j : ZMod n} (hr : remote i j)
    {s t : ℝ} (heq : edgePoint P i s = edgePoint P j t) :
    det (edge P i) (edge P j) ≠ 0 := by
  intro hd
  obtain ⟨hj0, hj1, _, _⟩ := remote_endpoints i j hr
  have harea := g1_area_ne_zero h (next_ne_self i).symm hj1.symm hj0.symm
  change det (edge P i) (P j - P i) ≠ 0 at harea
  have hid := intersection_parameter_identity heq.symm
  have hswap : det (edge P j) (edge P i) = 0 := by rw [det_swap, hd, neg_zero]
  rw [hswap, mul_zero] at hid
  apply harea
  have hcoords : det (edge P i) (P j - P i) = det (P i - P j) (edge P i) := by
    dsimp [det]
    ring
  rw [hcoords, hid]

theorem g1_remote_parameters_interior [Nontrivial (ZMod n)]
    {P : LabelledTuple n} (h : G1 P) {i j : ZMod n} (hr : remote i j)
    {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (heq : edgePoint P i s = edgePoint P j t) :
    0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 := by
  obtain ⟨hj0, hj1, hjp0, hjp1⟩ := remote_endpoints i j hr
  have hs_ne0 : s ≠ 0 := by
    intro hz
    have he : P i = edgePoint P j t := by simpa [hz, edgePoint] using heq
    exact g1_vertex_off_edge_line h j i (next_ne_self j).symm hj0.symm hjp0.symm t he
  have hs_ne1 : s ≠ 1 := by
    intro hz
    have he : P (i + 1) = edgePoint P j t := by simpa [hz, edgePoint, edge] using heq
    exact g1_vertex_off_edge_line h j (i + 1) (next_ne_self j).symm hj1.symm hjp1.symm t he
  have ht_ne0 : t ≠ 0 := by
    intro hz
    have he : P j = edgePoint P i s := by simpa [hz, edgePoint] using heq.symm
    exact g1_vertex_off_edge_line h i j (next_ne_self i).symm hj0 hj1 s he
  have ht_ne1 : t ≠ 1 := by
    intro hz
    have he : P (j + 1) = edgePoint P i s := by simpa [hz, edgePoint, edge] using heq.symm
    exact g1_vertex_off_edge_line h i (j + 1) (next_ne_self i).symm hjp0 hjp1 s he
  exact ⟨lt_of_le_of_ne hs0 hs_ne0.symm, lt_of_le_of_ne hs1 hs_ne1,
    lt_of_le_of_ne ht0 ht_ne0.symm, lt_of_le_of_ne ht1 ht_ne1⟩

end SM
