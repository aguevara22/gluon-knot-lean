import DirectGLSSW.GlobalCapCut
import DirectGLSSW.TriangularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace DirectGLSSW.CapMatrixRestriction
open scoped BigOperators
open DirectGLSSW

/-- The consecutive principal-block embedding `i ↦ offset+i`. -/
def consecutiveBlockEmbedding {n m : ℕ} (offset : ℕ)
    (hbound : offset + m ≤ n) : Fin m → Fin n :=
  fun i => ⟨offset + i.val, by omega⟩

/-- Matrices with zero entries strictly below the diagonal. -/
def UpperTriangularBlock {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∀ i j, i.val > j.val → A i j = 0

private theorem consecutiveBlockEmbedding_val {n m offset : ℕ}
    (hbound : offset + m ≤ n) (i : Fin m) :
    (consecutiveBlockEmbedding offset hbound i).val = offset + i.val := rfl

private theorem consecutiveBlockEmbedding_lt_iff {n m offset : ℕ}
    (hbound : offset + m ≤ n) (i j : Fin m) :
    (consecutiveBlockEmbedding offset hbound i).val <
      (consecutiveBlockEmbedding offset hbound j).val ↔ i.val < j.val := by
  simp [consecutiveBlockEmbedding]

private theorem strictUpperBlock_upper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : StrictUpper A) : UpperTriangularBlock A := by
  intro i j hij
  exact hA i j (by omega)

private theorem upperTriangularBlock_mul {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℚ)
    (hA : UpperTriangularBlock A) (hC : UpperTriangularBlock C) :
    UpperTriangularBlock (A * C) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : k.val < i.val
  · rw [hA i k (by omega), zero_mul]
  · have hik : i.val ≤ k.val := by omega
    have hkj : j.val < k.val := by omega
    rw [hC k j (by omega), mul_zero]

private theorem consecutiveBlockEmbedding_injective {n m offset : ℕ}
    (hbound : offset + m ≤ n) :
    Function.Injective (consecutiveBlockEmbedding offset hbound) := by
  intro i j hij
  apply Fin.ext
  have heq := congrArg Fin.val hij
  simpa [consecutiveBlockEmbedding] using heq

private theorem consecutiveBlock_sum_reindex
    {n m offset : ℕ} (hbound : offset + m ≤ n)
    (f : Fin n → ℚ)
    (hleft : ∀ k, k.val < offset → f k = 0)
    (hright : ∀ k, offset + m ≤ k.val → f k = 0) :
    (∑ k : Fin n, f k) =
      ∑ i : Fin m, f (consecutiveBlockEmbedding offset hbound i) := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter
    (fun k => offset ≤ k.val ∧ k.val < offset + m)
  have hsum : (∑ k : Fin n, f k) = ∑ k ∈ s, f k := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro k _ hnot
    by_cases hlt : k.val < offset
    · exact hleft k hlt
    · have hge : offset ≤ k.val := by omega
      have hupper : offset + m ≤ k.val := by
        by_contra h
        have hsmall : k.val < offset + m := by omega
        have : k ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hge, hsmall⟩⟩
        exact hnot this
      exact hright k hupper
  let hequiv : Fin m ≃ ↥s := {
    toFun := fun i => ⟨consecutiveBlockEmbedding offset hbound i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        constructor
        · simp [consecutiveBlockEmbedding]
        · have hi := i.isLt
          simp [consecutiveBlockEmbedding]⟩⟩
    invFun := fun k => ⟨k.1.val - offset, by
      have hk := Finset.mem_filter.mp k.2
      have hlt : k.1.val < offset + m := hk.2.2
      have hge : offset ≤ k.1.val := hk.2.1
      simp
      omega⟩
    left_inv := by
      intro i
      apply Fin.ext
      simp [consecutiveBlockEmbedding]
    right_inv := by
      intro k
      apply Subtype.ext
      apply Fin.ext
      have hk := Finset.mem_filter.mp k.2
      simp [consecutiveBlockEmbedding]
      omega }
  have hcoe : (∑ k ∈ s, f k) = ∑ k : ↥s, f k.1 :=
    (Finset.sum_coe_sort s f).symm
  calc
    _ = ∑ k : ↥s, f k.1 := hsum.trans hcoe
    _ = ∑ i : Fin m, f (consecutiveBlockEmbedding offset hbound i) := by
      have hcomp : (∑ k : ↥s, f k.1) =
          ∑ i : Fin m, f (hequiv i).1 :=
        (hequiv.sum_comp (fun k : ↥s => f k.1)).symm
      calc
        _ = ∑ i : Fin m, f (hequiv i).1 := hcomp
        _ = ∑ i : Fin m, f (consecutiveBlockEmbedding offset hbound i) := by
          apply Finset.sum_congr rfl
          intro i _
          change f (↑(hequiv i)) = f (consecutiveBlockEmbedding offset hbound i)
          congr 1

theorem submatrix_mul_consecutive_upper
    {n m offset : ℕ} (hbound : offset + m ≤ n)
    (A C : Matrix (Fin n) (Fin n) ℚ)
    (hA : UpperTriangularBlock A) (hC : UpperTriangularBlock C) :
    (A * C).submatrix (consecutiveBlockEmbedding offset hbound)
      (consecutiveBlockEmbedding offset hbound) =
      A.submatrix (consecutiveBlockEmbedding offset hbound)
        (consecutiveBlockEmbedding offset hbound) *
      C.submatrix (consecutiveBlockEmbedding offset hbound)
        (consecutiveBlockEmbedding offset hbound) := by
  ext i j
  change (∑ k : Fin n,
      A (consecutiveBlockEmbedding offset hbound i) k *
        C k (consecutiveBlockEmbedding offset hbound j)) =
    (A.submatrix (consecutiveBlockEmbedding offset hbound)
      (consecutiveBlockEmbedding offset hbound) *
      C.submatrix (consecutiveBlockEmbedding offset hbound)
        (consecutiveBlockEmbedding offset hbound)) i j
  rw [Matrix.mul_apply]
  apply consecutiveBlock_sum_reindex hbound
  · intro k hlt
    have hrow : (consecutiveBlockEmbedding offset hbound i).val > k.val := by
      simp [consecutiveBlockEmbedding]
      omega
    rw [hA _ _ hrow, zero_mul]
  · intro k hge
    have hcol : k.val > (consecutiveBlockEmbedding offset hbound j).val := by
      simp [consecutiveBlockEmbedding]
      omega
    rw [hC _ _ hcol, mul_zero]

private theorem upperTriangularBlock_submatrix
    {n m offset : ℕ} (hbound : offset + m ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : UpperTriangularBlock A) :
    UpperTriangularBlock (A.submatrix (consecutiveBlockEmbedding offset hbound)
      (consecutiveBlockEmbedding offset hbound)) := by
  intro i j hij
  change A (consecutiveBlockEmbedding offset hbound i)
    (consecutiveBlockEmbedding offset hbound j) = 0
  apply hA
  simp [consecutiveBlockEmbedding]
  omega

private theorem upperTriangularBlock_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : UpperTriangularBlock A) : ∀ k, UpperTriangularBlock (A ^ k) := by
  intro k
  induction k with
  | zero =>
      intro i j hij
      have hne : i ≠ j := by
        intro heq
        subst j
        omega
      simp [Matrix.one_apply, hne]
  | succ k ih =>
      rw [pow_succ]
      exact upperTriangularBlock_mul _ _ ih hA

private theorem submatrix_pow_consecutive_upper
    {n m offset : ℕ} (hbound : offset + m ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : UpperTriangularBlock A) :
    ∀ k, (A ^ k).submatrix (consecutiveBlockEmbedding offset hbound)
      (consecutiveBlockEmbedding offset hbound) =
      (A.submatrix (consecutiveBlockEmbedding offset hbound)
        (consecutiveBlockEmbedding offset hbound)) ^ k := by
  intro k
  induction k with
  | zero =>
      ext i j
      have hinj := consecutiveBlockEmbedding_injective hbound
      have heq : consecutiveBlockEmbedding offset hbound i =
          consecutiveBlockEmbedding offset hbound j ↔ i = j := by
        constructor
        · intro h
          exact hinj h
        · intro h; cases h; rfl
      simp [Matrix.one_apply, heq]
  | succ k ih =>
      rw [pow_succ, submatrix_mul_consecutive_upper hbound (A ^ k) A
        (upperTriangularBlock_pow A hA k) hA, ih, pow_succ]

private theorem strictUpperBlock_submatrix
    {n m offset : ℕ} (hbound : offset + m ≤ n)
    (X : Matrix (Fin n) (Fin n) ℚ) (hX : StrictUpper X) :
    StrictUpper (X.submatrix (consecutiveBlockEmbedding offset hbound)
      (consecutiveBlockEmbedding offset hbound)) := by
  intro i j hji
  change X (consecutiveBlockEmbedding offset hbound i)
    (consecutiveBlockEmbedding offset hbound j) = 0
  apply hX
  simp [consecutiveBlockEmbedding]
  omega

theorem finiteInverse_submatrix_consecutive_strictUpper
    {n m offset : ℕ} (hbound : offset + m ≤ n)
    (X : Matrix (Fin n) (Fin n) ℚ) (hX : StrictUpper X) :
    (finiteInverse X n).submatrix (consecutiveBlockEmbedding offset hbound)
      (consecutiveBlockEmbedding offset hbound) =
      finiteInverse
        (X.submatrix (consecutiveBlockEmbedding offset hbound)
          (consecutiveBlockEmbedding offset hbound)) m := by
  classical
  let e := consecutiveBlockEmbedding offset hbound
  let Y := X.submatrix e e
  let hY : StrictUpper Y := strictUpperBlock_submatrix hbound X hX
  let A := -X
  let AY := -Y
  have hA : UpperTriangularBlock A := by
    intro i j hij
    change -X i j = 0
    rw [hX i j (by omega)]
    simp
  have hAY : StrictUpper AY := by
    intro i j hji
    change -(Y i j) = 0
    rw [hY i j hji]
    simp
  have hAYupper : UpperTriangularBlock AY := strictUpperBlock_upper AY hAY
  have hpow (k : ℕ) : (A ^ k).submatrix e e = (AY ^ k) :=
    submatrix_pow_consecutive_upper hbound A hA k
  have hpowtail (k : ℕ) (hkm : m ≤ k) (i j : Fin m) : (AY ^ k) i j = 0 := by
    apply strictUpper_pow_entry_zero AY hAY k i j
    have hj := j.isLt
    omega
  have hmn : m ≤ n := by omega
  have hsplit : n = m + (n-m) := by omega
  unfold finiteInverse
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.sum_apply]
  change (∑ k ∈ Finset.range n, (A ^ k) (e i) (e j)) =
    ∑ k ∈ Finset.range m, (AY ^ k) i j
  have hrange : Finset.range n = Finset.range (m + (n-m)) :=
    congrArg Finset.range hsplit
  rw [hrange, Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range m, (A ^ k) (e i) (e j)) =
      ∑ k ∈ Finset.range m, (AY ^ k) i j := by
    apply Finset.sum_congr rfl
    intro k hk
    have he := congrArg (fun M : Matrix (Fin m) (Fin m) ℚ => M i j) (hpow k)
    simpa using he
  have htail : (∑ k ∈ Finset.range (n-m), (A ^ (m+k)) (e i) (e j)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have he : (A ^ (m+k)) (e i) (e j) = (AY ^ (m+k)) i j := by
      simpa [Matrix.submatrix_apply] using
        congrArg (fun M : Matrix (Fin m) (Fin m) ℚ => M i j) (hpow (m+k))
    rw [hpowtail (m+k) (by omega) i j] at he
    exact he
  rw [hfirst, htail, add_zero]

private theorem strictUpper_mul_diagonal
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (hB : StrictUpper B)
    (h : Fin n → ℚ) : StrictUpper (B * Matrix.diagonal h) := by
  intro i j hji
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hkj : k = j
  · subst k
    rw [hB i j hji, zero_mul]
  · simp [Matrix.diagonal, hkj]

private theorem diagonal_submatrix_consecutive
    {n m offset : ℕ} (hbound : offset + m ≤ n) (h : Fin n → ℚ) :
    (Matrix.diagonal h).submatrix (consecutiveBlockEmbedding offset hbound)
      (consecutiveBlockEmbedding offset hbound) =
      Matrix.diagonal (fun i => h (consecutiveBlockEmbedding offset hbound i)) := by
  ext i j
  have heq : consecutiveBlockEmbedding offset hbound i =
      consecutiveBlockEmbedding offset hbound j ↔ i = j := by
    constructor
    · intro h
      exact consecutiveBlockEmbedding_injective hbound h
    · intro h; cases h; rfl
  simp [Matrix.diagonal, heq]

private theorem upperTriangularBlock_finiteInverse
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (hX : StrictUpper X) :
    UpperTriangularBlock (finiteInverse X n) := by
  classical
  intro i j hij
  unfold finiteInverse
  rw [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro k _
  exact strictUpper_pow_entry_zero (-X) (by
    intro r s hrs
    change -X r s = 0
    rw [hX r s (by omega)]
    simp) k i j (by omega)

private theorem globalCapResolvent_submatrix_consecutive
    {n m offset : ℕ} (hbound : offset + m ≤ n)
    (B : Matrix (Fin n) (Fin n) ℚ) (h : Fin n → ℚ) (hB : StrictUpper B) :
    (globalCapResolvent B h).submatrix (consecutiveBlockEmbedding offset hbound)
      (consecutiveBlockEmbedding offset hbound) =
      globalCapResolvent
        (B.submatrix (consecutiveBlockEmbedding offset hbound)
          (consecutiveBlockEmbedding offset hbound))
        (fun i => h (consecutiveBlockEmbedding offset hbound i)) := by
  let e := consecutiveBlockEmbedding offset hbound
  have hD : UpperTriangularBlock (Matrix.diagonal h) := by
    intro i j hij
    have hne : i ≠ j := by
      intro heq
      subst j
      omega
    simp [Matrix.diagonal, hne]
  have hBup : UpperTriangularBlock B := strictUpperBlock_upper B hB
  have hmul := submatrix_mul_consecutive_upper hbound B (Matrix.diagonal h) hBup hD
  have hmulStrict : StrictUpper (B * Matrix.diagonal h) := strictUpper_mul_diagonal B hB h
  have hneg : StrictUpper (-(B * Matrix.diagonal h)) := by
    intro i j hji
    change -((B * Matrix.diagonal h) i j) = 0
    rw [hmulStrict i j hji]
    simp
  change (finiteInverse (-(B * Matrix.diagonal h)) n).submatrix e e =
      finiteInverse (-(B.submatrix e e * Matrix.diagonal (fun i => h (e i)))) m
  rw [finiteInverse_submatrix_consecutive_strictUpper hbound _ hneg]
  have hdiag := diagonal_submatrix_consecutive hbound h
  have hprod : (B * Matrix.diagonal h).submatrix e e =
      B.submatrix e e * Matrix.diagonal (fun i => h (e i)) := by
    simpa [e] using hmul.trans (congrArg (fun M => B.submatrix e e * M) hdiag)
  have harg : (-(B * Matrix.diagonal h)).submatrix e e =
      -(B.submatrix e e * Matrix.diagonal (fun i => h (e i))) := by
    ext i j
    change -((B * Matrix.diagonal h) (e i) (e j)) =
      -((B.submatrix e e * Matrix.diagonal (fun i => h (e i))) i j)
    have heq : (B * Matrix.diagonal h) (e i) (e j) =
        (B.submatrix e e * Matrix.diagonal (fun i => h (e i))) i j := by
      simpa [Matrix.submatrix_apply] using
        congrArg (fun M : Matrix (Fin m) (Fin m) ℚ => M i j) hprod
    exact congrArg Neg.neg heq
  rw [harg]

/-- The global cap pairing restricts to its consecutive principal block. -/
theorem globalCapPairing_submatrix_consecutive
    {n m offset : ℕ} (hbound : offset + m ≤ n)
    (F B G : Matrix (Fin n) (Fin n) ℚ) (h : Fin n → ℚ)
    (hF : UpperTriangularBlock F) (hB : StrictUpper B)
    (hG : UpperTriangularBlock G) :
    (globalCapPairing F B G h).submatrix
      (consecutiveBlockEmbedding offset hbound)
      (consecutiveBlockEmbedding offset hbound) =
      globalCapPairing
        (F.submatrix (consecutiveBlockEmbedding offset hbound)
          (consecutiveBlockEmbedding offset hbound))
        (B.submatrix (consecutiveBlockEmbedding offset hbound)
          (consecutiveBlockEmbedding offset hbound))
        (G.submatrix (consecutiveBlockEmbedding offset hbound)
          (consecutiveBlockEmbedding offset hbound))
        (fun i => h (consecutiveBlockEmbedding offset hbound i)) := by
  let e := consecutiveBlockEmbedding offset hbound
  let D := Matrix.diagonal h
  let Dm := Matrix.diagonal (fun i => h (e i))
  let R := globalCapResolvent B h
  let Rm := globalCapResolvent (B.submatrix e e) (fun i => h (e i))
  have hD : UpperTriangularBlock D := by
    intro i j hij
    have hne : i ≠ j := by
      intro heq
      subst j
      omega
    simp [D, Matrix.diagonal, hne]
  have hBup : UpperTriangularBlock B := strictUpperBlock_upper B hB
  have hK : StrictUpper (B * D) := by
    simpa [D] using strictUpper_mul_diagonal B hB h
  have hR : UpperTriangularBlock R := upperTriangularBlock_finiteInverse
    (-(B * D)) (by
      intro i j hji
      change -((B * D) i j) = 0
      rw [hK i j hji]
      simp)
  have hFD : UpperTriangularBlock (F * D) := upperTriangularBlock_mul F D hF hD
  have hFDR : UpperTriangularBlock ((F * D) * R) := upperTriangularBlock_mul (F * D) R hFD hR
  have hFR : (R.submatrix e e) = Rm := globalCapResolvent_submatrix_consecutive hbound B h hB
  have hDsub : D.submatrix e e = Dm := by
    simpa [e, Dm, D] using diagonal_submatrix_consecutive hbound h
  have hFDsub : (F * D).submatrix e e = F.submatrix e e * Dm := by
    rw [submatrix_mul_consecutive_upper hbound F D hF hD, hDsub]
  have hFDRsub : ((F * D) * R).submatrix e e = (F.submatrix e e * Dm) * Rm := by
    rw [submatrix_mul_consecutive_upper hbound (F * D) R hFD hR, hFDsub, hFR]
  have hfinal : (((F * D) * R) * G).submatrix e e =
      ((F.submatrix e e * Dm) * Rm) * G.submatrix e e := by
    rw [submatrix_mul_consecutive_upper hbound ((F * D) * R) G hFDR hG, hFDRsub]
  change ((((F * D) * R) * G).submatrix e e) =
    (((F.submatrix e e * Matrix.diagonal (fun i => h (e i))) *
      globalCapResolvent (B.submatrix e e) (fun i => h (e i))) * G.submatrix e e)
  rw [hfinal]





















end DirectGLSSW.CapMatrixRestriction
