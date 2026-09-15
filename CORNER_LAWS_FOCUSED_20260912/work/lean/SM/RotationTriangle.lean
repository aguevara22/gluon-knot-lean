import SM.RegularTriangle

/-! Complete triangle clause of lem:rot, derived from actual regular geometry,
the common determinant sign, integrality and the strict rotation bound. -/

namespace SM

theorem integer_eq_one_of_small_positive {x : ℝ} (hx : 0 < x)
    (hb : 2 * |x| < 3) (hk : ∃ k : ℤ, x = (k : ℝ)) : x = 1 := by
  obtain ⟨k, rfl⟩ := hk
  have hp : (0 : ℤ) < k := by exact_mod_cast hx
  have hl : (k : ℝ) < 2 := by nlinarith [le_abs_self (k : ℝ)]
  have hl' : k < (2 : ℤ) := by exact_mod_cast hl
  have he : k = 1 := by omega
  simp [he]

theorem integer_eq_neg_one_of_small_negative {x : ℝ} (hx : x < 0)
    (hb : 2 * |x| < 3) (hk : ∃ k : ℤ, x = (k : ℝ)) : x = -1 := by
  have hi : ∃ k : ℤ, -x = (k : ℝ) := by
    obtain ⟨k, hk⟩ := hk
    exact ⟨-k, by simp [hk]⟩
  have he := integer_eq_one_of_small_positive (neg_pos.mpr hx) (by simpa using hb) hi
  linarith

theorem rotationNumber_triangle {P : LabelledTuple 3} (h : Regular P) :
    (∀ i : ZMod 3, rotationNumber P = (turn P i : ℝ)) ∧
    (rotationNumber P = 1 ∨ rotationNumber P = -1) ∧ rotationNumber P ≠ 0 := by
  have hb : 2 * |rotationNumber P| < 3 := by simpa using rotationNumber_strict_bound h
  have hk := rotationNumber_integer h
  have hd := regular_triangle_det_ne_zero h
  rcases lt_or_gt_of_ne hd with hdneg | hdpos
  · have ht (i : ZMod 3) : principalTurn P i < 0 :=
      sign_eq_neg_one_iff.mp ((regular_triangle_principalTurn_sign h i).trans
        (sign_eq_neg_one_iff.mpr hdneg))
    have hs : (∑ i : ZMod 3, principalTurn P i) < 0 :=
      Finset.sum_neg (fun i _ => ht i) Finset.univ_nonempty
    have hr : rotationNumber P < 0 :=
      div_neg_of_neg_of_pos hs (mul_pos (by norm_num) Real.pi_pos)
    have he := integer_eq_neg_one_of_small_negative hr hb hk
    refine ⟨?_, Or.inr he, ne_of_lt hr⟩
    intro i
    have htau : turn P i = -1 := by
      rw [turn_det, triangle_turn_det, sign_eq_neg_one_iff.mpr hdneg]
    simp [he, htau]
  · have ht (i : ZMod 3) : 0 < principalTurn P i :=
      sign_eq_one_iff.mp ((regular_triangle_principalTurn_sign h i).trans
        (sign_eq_one_iff.mpr hdpos))
    have hs : 0 < ∑ i : ZMod 3, principalTurn P i :=
      Finset.sum_pos (fun i _ => ht i) Finset.univ_nonempty
    have hr : 0 < rotationNumber P := div_pos hs (mul_pos (by norm_num) Real.pi_pos)
    have he := integer_eq_one_of_small_positive hr hb hk
    refine ⟨?_, Or.inl he, ne_of_gt hr⟩
    intro i
    have htau : turn P i = 1 := by
      rw [turn_det, triangle_turn_det, sign_eq_one_iff.mpr hdpos]
    simp [he, htau]

end SM
