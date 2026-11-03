import Mathlib.Algebra.MonoidAlgebra.Defs




namespace DirectGLSSW.HOMFLY.Coefficients

abbrev HOMFLYCoeff := AddMonoidAlgebra ℤ (ℤ × ℤ)

noncomputable def coeff (P : HOMFLYCoeff) (i j : ℤ) : ℤ := P (i, j)

noncomputable def aMonomial : HOMFLYCoeff := Finsupp.single (1, 0) 1

noncomputable def aInvMonomial : HOMFLYCoeff := Finsupp.single (-1, 0) 1

noncomputable def zMonomial : HOMFLYCoeff := Finsupp.single (0, 1) 1

noncomputable def zInvMonomial : HOMFLYCoeff := Finsupp.single (0, -1) 1

noncomputable def unlinkFactor : HOMFLYCoeff :=
  (aMonomial - aInvMonomial) * zInvMonomial

noncomputable def zFloor (P : HOMFLYCoeff) (n : ℤ) : Prop :=
  ∀ i j : ℤ, j < n → coeff P i j = 0

theorem coeff_aMonomial_mul (P : HOMFLYCoeff) (i j : ℤ) :
    coeff (aMonomial * P) i j = coeff P (i - 1) j := by
  simp [coeff, aMonomial, AddMonoidAlgebra.single_mul_apply]
  all_goals rw [show (-1 : ℤ) + i = i - 1 by omega]

theorem coeff_aInvMonomial_mul (P : HOMFLYCoeff) (i j : ℤ) :
    coeff (aInvMonomial * P) i j = coeff P (i + 1) j := by
  simp [coeff, aInvMonomial, AddMonoidAlgebra.single_mul_apply]
  all_goals rw [add_comm (1 : ℤ) i]

theorem coeff_zMonomial_mul (P : HOMFLYCoeff) (i j : ℤ) :
    coeff (zMonomial * P) i j = coeff P i (j - 1) := by
  simp [coeff, zMonomial, AddMonoidAlgebra.single_mul_apply]
  all_goals rw [show (-1 : ℤ) + j = j - 1 by omega]

theorem coeff_zInvMonomial_mul (P : HOMFLYCoeff) (i j : ℤ) :
    coeff (zInvMonomial * P) i j = coeff P i (j + 1) := by
  simp [coeff, zInvMonomial, AddMonoidAlgebra.single_mul_apply]
  all_goals rw [add_comm (1 : ℤ) j]

theorem zFloor_add (P Q : HOMFLYCoeff) (n : ℤ)
    (hP : zFloor P n) (hQ : zFloor Q n) :
    zFloor (P + Q) n := by
  intro i j hj
  simp only [zFloor, coeff] at hP hQ ⊢
  rw [Finsupp.add_apply]
  rw [hP i j hj, hQ i j hj, add_zero]

theorem zFloor_mul (P Q : HOMFLYCoeff) (p q : ℤ)
    (hP : zFloor P p) (hQ : zFloor Q q) :
    zFloor (P * Q) (p + q) := by
  intro i j hj
  rw [coeff]
  rw [AddMonoidAlgebra.mul_apply]
  simp only [Finsupp.sum] 
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hxy : x + y = (i, j)
  · simp only [hxy, if_pos, mul_eq_zero]
    apply Or.inr
    have hjx : p ≤ x.2 := by
      by_contra hn
      have : x.2 < p := by omega
      have hxmem : P x ≠ 0 := Finsupp.mem_support_iff.mp hx
      have hPzero : P x = 0 := by
        simpa [coeff] using hP x.1 x.2 this
      exact hxmem hPzero
    have hjy : q ≤ y.2 := by
      by_contra hn
      have : y.2 < q := by omega
      have hymem : Q y ≠ 0 := Finsupp.mem_support_iff.mp hy
      have hQzero : Q y = 0 := by
        simpa [coeff] using hQ y.1 y.2 this
      exact hymem hQzero
    have hdegree : j = x.2 + y.2 := by
      have hz := congrArg Prod.snd hxy
      simpa using hz.symm
    omega
  · simp [hxy]

theorem zFloor_zmul (P : HOMFLYCoeff) (p : ℤ)
    (hP : zFloor P p) :
    zFloor (zMonomial * P) (p + 1) := by
  intro i j hj
  rw [coeff_zMonomial_mul]
  apply hP
  omega

theorem aMonomial_mul_aInvMonomial :
    aMonomial * aInvMonomial = 1 := by
  rw [aMonomial, aInvMonomial, AddMonoidAlgebra.single_mul_single]
  change AddMonoidAlgebra.single (0, 0) (1 * 1) = 1
  rw [one_mul]
  exact AddMonoidAlgebra.one_def.symm

theorem zMonomial_mul_zInvMonomial :
    zMonomial * zInvMonomial = 1 := by
  rw [zMonomial, zInvMonomial, AddMonoidAlgebra.single_mul_single]
  change AddMonoidAlgebra.single (0, 0) (1 * 1) = 1
  rw [one_mul]
  exact AddMonoidAlgebra.one_def.symm

theorem unlinkFactor_coeff (i j : ℤ) :
    coeff unlinkFactor i j =
      (if (i, j) = (1, -1) then 1 else 0) -
      (if (i, j) = (-1, -1) then 1 else 0) := by
  simp only [coeff, unlinkFactor, aMonomial, aInvMonomial, zInvMonomial]
  rw [sub_mul, Finsupp.sub_apply]
  simp only [AddMonoidAlgebra.single_mul_single, one_mul]
  simp [Finsupp.sub_apply, AddMonoidAlgebra.single_apply,
    Prod.mk.injEq, eq_comm]

theorem unlinkFactor_support :
    unlinkFactor.support = {(1, -1), (-1, -1)} := by
  ext x
  rcases x with ⟨i, j⟩
  rw [Finset.mem_insert, Finset.mem_singleton]
  rw [Finsupp.mem_support_iff]
  change coeff unlinkFactor i j ≠ 0 ↔ _
  rw [unlinkFactor_coeff]
  simp only [Prod.mk.injEq]
  by_cases h1 : i = 1 ∧ j = -1 <;> by_cases h2 : i = -1 ∧ j = -1
  · exact False.elim (by omega)
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

end DirectGLSSW.HOMFLY.Coefficients
