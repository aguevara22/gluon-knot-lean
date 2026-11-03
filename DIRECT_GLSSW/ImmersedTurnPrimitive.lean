import ImmersedCyclicCurve
set_option autoImplicit false
open scoped BigOperators
namespace DirectGLSSW.ImmersedGlobalRounding
open DirectGLSSW.HOMFLY.PolygonDrawingBridge
noncomputable def turnPrimitive {n : ℕ} (q : Fin n → PlanarPoint ℝ) (base : Fin n) (k : ℤ) : ℝ :=
  Int.inductionOn' (C := fun _ => ℝ) k 0 0
    (fun j _ a => a + originalCornerTurn q (phase base j))
    (fun j _ a => a - originalCornerTurn q (phase base (j-1)))

theorem turnPrimitive_zero {n : ℕ} (q : Fin n → PlanarPoint ℝ) (base : Fin n) :
    turnPrimitive q base 0 = 0 := by
  unfold turnPrimitive
  rw [Int.inductionOn'_self]

theorem turnPrimitive_pred {n : ℕ} (q : Fin n → PlanarPoint ℝ) (base : Fin n)
    (k : ℤ) (hk : k ≤ 0) :
    turnPrimitive q base (k - 1) =
      turnPrimitive q base k - originalCornerTurn q (phase base (k-1)) := by
  unfold turnPrimitive
  rw [Int.inductionOn'_sub_one hk]

theorem turnPrimitive_succ {n : ℕ} (q : Fin n → PlanarPoint ℝ) (base : Fin n) (k : ℤ) :
    turnPrimitive q base (k + 1) =
      turnPrimitive q base k + originalCornerTurn q (phase base k) := by
  by_cases hk : 0 ≤ k
  · unfold turnPrimitive
    rw [Int.inductionOn'_add_one hk]
  · have h := turnPrimitive_pred q base (k + 1) (by omega)
    simp only [add_sub_cancel_right] at h
    linarith

theorem turnPrimitive_nat {n : ℕ} (q : Fin n → PlanarPoint ℝ) (base : Fin n) (m : ℕ) :
    turnPrimitive q base m = ∑ j ∈ Finset.range m, originalCornerTurn q (phase base j) := by
  induction m with
  | zero => simp [turnPrimitive_zero]
  | succ m ih =>
    rw [Nat.cast_succ,turnPrimitive_succ,ih,Finset.sum_range_succ]

theorem phase_nat_traversal {n : ℕ} (base : Fin n) (j : ℕ) :
    phase base (j:ℤ) = (cyclicSuccessorPerm n ^ (j+1)) ((cyclicSuccessorPerm n).symm base) := by
  simp only [phase,zpow_natCast,pow_succ,Equiv.Perm.mul_apply,Equiv.apply_symm_apply]

theorem turnPrimitive_period {n : ℕ} (q : Fin n → PlanarPoint ℝ) (base : Fin n) :
    turnPrimitive q base n = originalCornerTotalTurn q := by
  rw [turnPrimitive_nat,← Fin.sum_univ_eq_sum_range]
  let E : Fin n ≃ Fin n := Equiv.ofBijective
    (fun i : Fin n => (cyclicSuccessorPerm n ^ (i.val+1)) ((cyclicSuccessorPerm n).symm base))
    (cyclicSuccessorPerm_oneTraversal ((cyclicSuccessorPerm n).symm base))
  exact Fintype.sum_equiv E _ _ (fun i => by rw [phase_nat_traversal]; rfl)
end DirectGLSSW.ImmersedGlobalRounding


