import SM.RotationNumber

/-! Actual real prefix sums of principal turns and the telescoping identity
for the actual edge direction classes. No unwrapped edge argument is assumed. -/

namespace SM

variable {n : ℕ} [NeZero n]

noncomputable def turnPrefix (P : LabelledTuple n) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, principalTurn P ((j + 1 : ℕ) : ZMod n)

noncomputable def edgeDirectionAngle (P : LabelledTuple n) (i : ZMod n) : Real.Angle :=
  ((planeComplex (edge P i)).arg : Real.Angle)

theorem principalTurn_nat_succ_angle {P : LabelledTuple n} (h : Regular P) (j : ℕ) :
    (principalTurn P ((j + 1 : ℕ) : ZMod n) : Real.Angle) =
      edgeDirectionAngle P ((j + 1 : ℕ) : ZMod n) - edgeDirectionAngle P (j : ZMod n) := by
  simpa only [edgeDirectionAngle, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
    principalTurn_coe_angle h ((j + 1 : ℕ) : ZMod n)

theorem turnPrefix_coe_angle {P : LabelledTuple n} (h : Regular P) (k : ℕ) :
    (turnPrefix P k : Real.Angle) = edgeDirectionAngle P (k : ZMod n) - edgeDirectionAngle P 0 := by
  calc
    (turnPrefix P k : Real.Angle) =
        ∑ j ∈ Finset.range k, (principalTurn P ((j + 1 : ℕ) : ZMod n) : Real.Angle) :=
      map_sum Real.Angle.coeHom _ _
    _ = ∑ j ∈ Finset.range k,
        (edgeDirectionAngle P ((j + 1 : ℕ) : ZMod n) - edgeDirectionAngle P (j : ZMod n)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact principalTurn_nat_succ_angle h j
    _ = edgeDirectionAngle P (k : ZMod n) - edgeDirectionAngle P 0 := by
      simpa only [Nat.cast_zero] using
        Finset.sum_range_sub (fun j : ℕ => edgeDirectionAngle P (j : ZMod n)) k

theorem finEquiv_apply_natCast (j : Fin n) : ZMod.finEquiv n j = (j.val : ZMod n) := by
  cases n with
  | zero => exact j.elim0
  | succ m => exact (ZMod.natCast_zmod_val (n := m + 1) j).symm

theorem sum_zmod_eq_sum_range {A : Type*} [AddCommMonoid A] (f : ZMod n → A) :
    (∑ i : ZMod n, f i) = ∑ j ∈ Finset.range n, f (j : ZMod n) := by
  calc
    (∑ i : ZMod n, f i) = ∑ j : Fin n, f (ZMod.finEquiv n j) :=
      (Equiv.sum_comp (ZMod.finEquiv n).toEquiv f).symm
    _ = ∑ j : Fin n, f (j.val : ZMod n) := by simp_rw [finEquiv_apply_natCast]
    _ = ∑ j ∈ Finset.range n, f (j : ZMod n) :=
      Fin.sum_univ_eq_sum_range (fun j : ℕ => f (j : ZMod n)) n

theorem sum_principalTurn_eq_prefix (P : LabelledTuple n) :
    (∑ i : ZMod n, principalTurn P i) = turnPrefix P (n - 1) + principalTurn P 0 := by
  have hn : n - 1 + 1 = n := by have hz := NeZero.ne n; omega
  rw [sum_zmod_eq_sum_range]
  simpa only [hn, turnPrefix, Nat.cast_zero] using
    Finset.sum_range_succ' (fun j : ℕ => principalTurn P (j : ZMod n)) (n - 1)

theorem natIndex_ne_zero {j : ℕ} (hj0 : 0 < j) (hjn : j < n) : (j : ZMod n) ≠ 0 := by
  intro he
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt hjn, ZMod.val_zero] at hv
  omega

theorem turnPrefix_nonneg {P : LabelledTuple n}
    (hp : ∀ i : ZMod n, i ≠ 0 → 0 < principalTurn P i) {k : ℕ} (hk : k < n) :
    0 ≤ turnPrefix P k := by
  apply Finset.sum_nonneg
  intro j hj
  have hjk := Finset.mem_range.mp hj
  exact (hp _ (natIndex_ne_zero (by omega) (by omega))).le

theorem turnPrefix_mono {P : LabelledTuple n}
    (hp : ∀ i : ZMod n, i ≠ 0 → 0 < principalTurn P i) {k l : ℕ}
    (hkl : k ≤ l) (hl : l < n) : turnPrefix P k ≤ turnPrefix P l := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkl)
  intro j hj _
  have hjl := Finset.mem_range.mp hj
  exact (hp _ (natIndex_ne_zero (by omega) (by omega))).le

theorem turnPrefix_bounds {P : LabelledTuple n}
    (hp : ∀ i : ZMod n, i ≠ 0 → 0 < principalTurn P i) {k : ℕ} (hk : k < n) :
    0 ≤ turnPrefix P k ∧ turnPrefix P k ≤ turnPrefix P (n - 1) := by
  have hn : n - 1 < n := by have hz := NeZero.ne n; omega
  exact ⟨turnPrefix_nonneg hp hk, turnPrefix_mono hp (by omega) hn⟩

end SM
