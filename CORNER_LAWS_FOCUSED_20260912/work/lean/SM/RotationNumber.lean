import SM.RegularDefinition

/-! Actual rotation number and the telescoping angle identity. These are
partial clauses of lem:rot; no full source proof is claimed by this module. -/

namespace SM

variable {n : ℕ}

noncomputable def rotationNumber [NeZero n] (P : LabelledTuple n) : ℝ :=
  (∑ i : ZMod n, principalTurn P i) / (2 * Real.pi)

theorem principalAngle_coe_angle {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) :
    (principalAngle u v : Real.Angle) =
      ((planeComplex v).arg : Real.Angle) - ((planeComplex u).arg : Real.Angle) := by
  change ((star (planeComplex u) * planeComplex v).arg : Real.Angle) = _
  rw [Complex.arg_mul_coe_angle (star_ne_zero.mpr (planeComplex_ne_zero hu))
    (planeComplex_ne_zero hv)]
  have hc : ((star (planeComplex u)).arg : Real.Angle) =
      -((planeComplex u).arg : Real.Angle) := Complex.arg_conj_coe_angle _
  rw [hc]
  abel

theorem principalTurn_coe_angle {P : LabelledTuple n} (h : Regular P) (i : ZMod n) :
    (principalTurn P i : Real.Angle) =
      ((planeComplex (edge P i)).arg : Real.Angle) -
        ((planeComplex (edge P (i - 1))).arg : Real.Angle) :=
  principalAngle_coe_angle (h i).1 (h i).2.1

theorem sum_principalTurn_coe_angle [NeZero n] {P : LabelledTuple n} (h : Regular P) :
    ((∑ i : ZMod n, principalTurn P i : ℝ) : Real.Angle) = 0 := by
  have hsum : ((∑ i : ZMod n, principalTurn P i : ℝ) : Real.Angle) =
      ∑ i : ZMod n, (principalTurn P i : Real.Angle) :=
    map_sum Real.Angle.coeHom _ _
  rw [hsum]
  simp_rw [principalTurn_coe_angle h]
  rw [Finset.sum_sub_distrib]
  have he : (∑ i : ZMod n, ((planeComplex (edge P (i - 1))).arg : Real.Angle)) =
      ∑ i : ZMod n, ((planeComplex (edge P i)).arg : Real.Angle) := by
    simpa [sub_eq_add_neg] using
      Equiv.sum_comp (Equiv.addRight (-1 : ZMod n))
        (fun i => ((planeComplex (edge P i)).arg : Real.Angle))
  rw [he, sub_self]

theorem rotationNumber_integer [NeZero n] {P : LabelledTuple n} (h : Regular P) :
    ∃ k : ℤ, rotationNumber P = (k : ℝ) := by
  obtain ⟨k, hk⟩ := Real.Angle.coe_eq_zero_iff.mp (sum_principalTurn_coe_angle h)
  refine ⟨k, ?_⟩
  change (∑ i : ZMod n, principalTurn P i) / (2 * Real.pi) = (k : ℝ)
  rw [← hk, zsmul_eq_mul]
  exact mul_div_cancel_right₀ _ (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))

theorem rotationNumber_shift [NeZero n] (a : ZMod n) (P : LabelledTuple n) :
    rotationNumber (shift a P) = rotationNumber P := by
  unfold rotationNumber
  simp_rw [principalTurn_shift]
  have hs : (∑ i : ZMod n, principalTurn P (i + a)) = ∑ i : ZMod n, principalTurn P i := by
    simpa using Equiv.sum_comp (Equiv.addRight a) (principalTurn P)
  rw [hs]

end SM
