import DirectGLSSW.FirstCut
import DirectGLSSW.TriangularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW
open scoped BigOperators

def globalCapNear {n : ℕ} (h : Fin n → ℚ) : ℕ → ℚ :=
  fun r => if hr : 0 < r ∧ r ≤ n then h ⟨r - 1, by omega⟩ else 0

def globalCapBranch {n : ℕ}
    (F B G : Matrix (Fin n) (Fin n) ℚ) (a b : Fin n) : IntervalArray :=
  fun r s =>
    if hr0 : r = 0 then
      if hs : 0 < s ∧ s ≤ n then F a ⟨s - 1, by omega⟩ else 0
    else if hsN : s = n + 1 then
      if hr : 0 < r ∧ r ≤ n then G ⟨r - 1, by omega⟩ b else 0
    else if hr : 0 < r ∧ r ≤ n then
      if hs : 0 < s ∧ s ≤ n then
        B ⟨r - 1, by omega⟩ ⟨s - 1, by omega⟩
      else 0
    else 0

def globalCapResolvent {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ)
    (h : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  finiteInverse (-(B * Matrix.diagonal h)) n

def globalCapPairing {n : ℕ} (F B G : Matrix (Fin n) (Fin n) ℚ)
    (h : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  F * Matrix.diagonal h * globalCapResolvent B h * G

theorem globalCapNear_at_internal {n : ℕ} (h : Fin n → ℚ) (r : Fin n) :
    globalCapNear h (r.val + 1) = h r := by
  simp [globalCapNear]
  omega

theorem globalCapBranch_first {n : ℕ} (F B G : Matrix (Fin n) (Fin n) ℚ)
    (a b r : Fin n) :
    globalCapBranch F B G a b 0 (r.val + 1) = F a r := by
  unfold globalCapBranch
  rw [dif_pos rfl]
  have hs : 0 < r.val + 1 ∧ r.val + 1 ≤ n := by omega
  rw [dif_pos hs]
  rfl

theorem globalCapBranch_middle {n : ℕ} (F B G : Matrix (Fin n) (Fin n) ℚ)
    (a b r s : Fin n) :
    globalCapBranch F B G a b (r.val + 1) (s.val + 1) = B r s := by
  unfold globalCapBranch
  have hr0 : r.val + 1 ≠ 0 := by omega
  have hsN : s.val + 1 ≠ n + 1 := by omega
  have hr : 0 < r.val + 1 ∧ r.val + 1 ≤ n := by omega
  have hs : 0 < s.val + 1 ∧ s.val + 1 ≤ n := by omega
  rw [dif_neg hr0, dif_neg hsN, dif_pos hr, dif_pos hs]
  rfl

private theorem globalCap_sum_fin_eq_Ioo {n : ℕ} (p : Fin n) (f : Fin n → ℚ) :
    (∑ q : Fin n, if p.val < q.val then f q else 0) =
      ∑ k : ↥(Finset.Ioo (p.val + 1) (n + 1)),
        f ⟨k.1 - 1, by have hk := Finset.mem_Ioo.mp k.2; omega⟩ := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun q => p.val < q.val)
  have hfilter : (∑ q : Fin n, if p.val < q.val then f q else 0) =
      ∑ q ∈ s, f q := by
    change (∑ q ∈ Finset.univ, if p.val < q.val then f q else 0) = _
    simp [s, Finset.sum_filter]
  rw [hfilter]
  have hcoe : (∑ q ∈ s, f q) = ∑ q : ↥s, f q.1 :=
    (Finset.sum_coe_sort s f).symm
  rw [hcoe]
  let e : ↥s ≃ ↥(Finset.Ioo (p.val + 1) (n + 1)) := {
    toFun := fun q => ⟨q.1.val + 1,
      Finset.mem_Ioo.mpr (by have hq := Finset.mem_filter.mp q.2; have hp := p.isLt; omega)⟩
    invFun := fun k => by
      have hk := Finset.mem_Ioo.mp k.2
      have hkn : k.1 ≤ n := by omega
      have hpq : p.val < k.1 - 1 := by omega
      refine ⟨⟨k.1 - 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpq⟩⟩
    left_inv := by
      intro q
      apply Subtype.ext
      apply Fin.ext
      have hq := Finset.mem_filter.mp q.2
      simp only [Fin.val_mk]
      omega
    right_inv := by
      intro k
      apply Subtype.ext
      have hk := Finset.mem_Ioo.mp k.2
      simp only [Fin.val_mk]
      omega }
  simpa [e] using e.sum_comp (fun k => f ⟨k.1 - 1,
    by have hk := Finset.mem_Ioo.mp k.2; omega⟩)

private theorem globalCap_sum_fin_eq_Ioo_all {n : ℕ} (f : Fin n → ℚ) :
    (∑ q : Fin n, f q) =
      ∑ k : ↥(Finset.Ioo 0 (n + 1)),
        f ⟨k.1 - 1, by have hk := Finset.mem_Ioo.mp k.2; omega⟩ := by
  classical
  let e : (Fin n) ≃ ↥(Finset.Ioo 0 (n + 1)) := {
    toFun := fun q => ⟨q.val + 1, Finset.mem_Ioo.mpr (by omega)⟩
    invFun := fun k => ⟨k.1 - 1, by have hk := Finset.mem_Ioo.mp k.2; omega⟩
    left_inv := by intro q; apply Fin.ext; simp only [Fin.val_mk]; omega
    right_inv := by intro k; apply Subtype.ext; have hk := Finset.mem_Ioo.mp k.2; simp only [Fin.val_mk]; omega }
  simpa [e] using e.sum_comp (fun k => f ⟨k.1 - 1,
    by have hk := Finset.mem_Ioo.mp k.2; omega⟩)

private def globalCapInternalWeight {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℚ) (h : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  B * Matrix.diagonal h

private theorem globalCapInternalWeight_apply {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℚ) (h : Fin n → ℚ) (r s : Fin n) :
    globalCapInternalWeight B h r s = B r s * h s := by
  classical
  simp [globalCapInternalWeight, Matrix.mul_apply, Matrix.diagonal,
    Finset.sum_eq_single s]

theorem globalCapBranch_last {n : ℕ} (F B G : Matrix (Fin n) (Fin n) ℚ)
    (a b r : Fin n) :
    globalCapBranch F B G a b (r.val + 1) (n + 1) = G r b := by
  unfold globalCapBranch
  have hr0 : r.val + 1 ≠ 0 := by omega
  have hsN : n + 1 = n + 1 := rfl
  have hr : 0 < r.val + 1 ∧ r.val + 1 ≤ n := by omega
  rw [dif_neg hr0, dif_pos hsN, dif_pos hr]
  rfl

private theorem globalCapResolvent_recurrence {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℚ) (h : Fin n → ℚ)
    (hB : StrictUpper B) :
    globalCapResolvent B h =
      1 + globalCapInternalWeight B h * globalCapResolvent B h := by
  let X := globalCapInternalWeight B h
  have hX : StrictUpper (-X) := by
    intro r s hrs
    change -(globalCapInternalWeight B h r s) = 0
    rw [globalCapInternalWeight_apply, hB r s hrs]
    ring
  have hInv := (strictUpper_finiteInverse (-X) hX).2
  change (1 + -X) * globalCapResolvent B h = 1 at hInv
  have hmul : globalCapResolvent B h + (-X) * globalCapResolvent B h = 1 := by
    simpa [Matrix.add_mul] using hInv
  have hneg : (-X) * globalCapResolvent B h =
      -(X * globalCapResolvent B h) := by
    ext r s
    simp [Matrix.mul_apply]
  rw [hneg] at hmul
  have hrec : globalCapResolvent B h =
      1 + X * globalCapResolvent B h := by
    ext r s
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M r s) hmul
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.neg_apply] at he
    simp only [Matrix.add_apply, Matrix.one_apply]
    rw [← he]
    ring
  dsimp [X] at hrec ⊢
  exact hrec

private theorem globalCapResolvent_mul_G_recurrence {n : ℕ}
    (B G : Matrix (Fin n) (Fin n) ℚ) (h : Fin n → ℚ)
    (hB : StrictUpper B) :
    globalCapResolvent B h * G = G +
      globalCapInternalWeight B h * (globalCapResolvent B h * G) := by
  have hr := globalCapResolvent_recurrence B h hB
  have hm := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M * G) hr
  simpa [Matrix.add_mul, Matrix.mul_assoc] using hm

private theorem globalCapResolvent_column_eq_weightedCutSum {n : ℕ}
    (F B G : Matrix (Fin n) (Fin n) ℚ) (h : Fin n → ℚ) (a b : Fin n)
    (hB : StrictUpper B) (p : Fin n) :
    (globalCapResolvent B h * G) p b =
      weightedCutSum (globalCapNear h) (globalCapBranch F B G a b)
        (p.val + 1) (n + 1) := by
  let Q := globalCapResolvent B h * G
  let P : ℕ → Prop := fun m => ∀ p : Fin n, n - p.val = m →
    Q p b = weightedCutSum (globalCapNear h) (globalCapBranch F B G a b)
      (p.val + 1) (n + 1)
  have hall : ∀ m, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro p hlen
      have hp : p.val + 1 < n + 1 := by omega
      have hrow := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M p b)
        (globalCapResolvent_mul_G_recurrence B G h hB)
      have hmatprod : (globalCapInternalWeight B h * Q) p b =
          ∑ q : Fin n, (if p.val < q.val then B p q * h q else 0) * Q q b := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro q _
        rw [globalCapInternalWeight_apply]
        by_cases hpq : p.val < q.val
        · simp [hpq]
        · have hz : B p q = 0 := hB p q (by omega)
          simp [hpq, hz]
      have hrow' : Q p b = G p b +
          ∑ q : Fin n, (if p.val < q.val then B p q * h q else 0) * Q q b := by
        simpa [Q, Matrix.add_apply, hmatprod] using hrow
      have hrow'' : Q p b = G p b +
          ∑ q : Fin n, if p.val < q.val then B p q * h q * Q q b else 0 := by
        simpa only [ite_mul, zero_mul, mul_assoc] using hrow'
      have hsum := globalCap_sum_fin_eq_Ioo p (fun q => B p q * h q * Q q b)
      rw [hsum] at hrow''
      rw [weightedCutSum_eq_firstCut (globalCapNear h)
        (globalCapBranch F B G a b) hp]
      rw [globalCapBranch_last]
      rw [hrow'']
      congr 1
      rw [← Finset.sum_coe_sort (Finset.Ioo (p.val + 1) (n + 1))
        (fun k => globalCapBranch F B G a b (p.val + 1) k * globalCapNear h k *
          weightedCutSum (globalCapNear h) (globalCapBranch F B G a b) k (n + 1))]
      apply Fintype.sum_congr
      intro k
      have hk := Finset.mem_Ioo.mp k.2
      let q : Fin n := ⟨k.1 - 1, by omega⟩
      have hlt : n - q.val < m := by rw [← hlen]; dsimp [q]; omega
      have hq := ih (n - q.val) hlt q rfl
      have hqval : q.val + 1 = k.1 := by dsimp [q]; omega
      calc
        B p q * h q * Q q b =
            globalCapBranch F B G a b (p.val + 1) (q.val + 1) *
              globalCapNear h (q.val + 1) *
              weightedCutSum (globalCapNear h) (globalCapBranch F B G a b)
                (q.val + 1) (n + 1) := by
                  rw [globalCapBranch_middle, globalCapNear_at_internal, hq]
        _ = globalCapBranch F B G a b (p.val + 1) k.1 *
              globalCapNear h k.1 *
              weightedCutSum (globalCapNear h) (globalCapBranch F B G a b)
                k.1 (n + 1) := by rw [hqval]
  exact hall (n - p.val) p rfl

theorem weightedCutSumNonempty_globalCapPairing {n : ℕ}
    (F B G : Matrix (Fin n) (Fin n) ℚ) (h : Fin n → ℚ)
    (hB : StrictUpper B) (a b : Fin n) :
    weightedCutSumNonempty (globalCapNear h)
      (globalCapBranch F B G a b) 0 (n + 1) =
        globalCapPairing F B G h a b := by
  classical
  let Q : Matrix (Fin n) (Fin n) ℚ := globalCapResolvent B h * G
  have hsumQ :
      (∑ k ∈ Finset.Ioo 0 (n + 1),
        globalCapBranch F B G a b 0 k * globalCapNear h k *
          weightedCutSum (globalCapNear h) (globalCapBranch F B G a b) k (n + 1)) =
        ∑ q : Fin n, F a q * h q * Q q b := by
    rw [← Finset.sum_coe_sort (Finset.Ioo 0 (n + 1))
      (fun k => globalCapBranch F B G a b 0 k * globalCapNear h k *
        weightedCutSum (globalCapNear h) (globalCapBranch F B G a b) k (n + 1))]
    rw [globalCap_sum_fin_eq_Ioo_all (fun q => F a q * h q * Q q b)]
    apply Fintype.sum_congr
    intro q
    have hqmem := Finset.mem_Ioo.mp q.2
    let r : Fin n := ⟨q.1 - 1, by omega⟩
    have hqval : r.val + 1 = q.1 := by dsimp [r]; omega
    have hqtail := globalCapResolvent_column_eq_weightedCutSum F B G h a b hB r
    calc
      globalCapBranch F B G a b 0 q.1 * globalCapNear h q.1 *
          weightedCutSum (globalCapNear h) (globalCapBranch F B G a b) q.1 (n + 1) =
        globalCapBranch F B G a b 0 (r.val + 1) * globalCapNear h (r.val + 1) *
          weightedCutSum (globalCapNear h) (globalCapBranch F B G a b) (r.val + 1) (n + 1) := by
            rw [hqval]
      _ = F a r * h r * Q r b := by
            rw [globalCapBranch_first, globalCapNear_at_internal, hqtail.symm]
  have hmat : globalCapPairing F B G h a b = ∑ q : Fin n, F a q * h q * Q q b := by
    change (((F * Matrix.diagonal h) * globalCapResolvent B h) * G) a b = _
    simp only [Matrix.mul_assoc]
    change (F * (Matrix.diagonal h * Q)) a b = _
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro q _
    have hdiag : (Matrix.diagonal h * Q) q b = h q * Q q b := by
      simp [Matrix.mul_apply, Matrix.diagonal, Finset.sum_eq_single q]
    rw [hdiag]
    ring
  calc
    weightedCutSumNonempty (globalCapNear h) (globalCapBranch F B G a b) 0 (n + 1) =
        ∑ k ∈ Finset.Ioo 0 (n + 1),
          globalCapBranch F B G a b 0 k * globalCapNear h k *
            weightedCutSum (globalCapNear h) (globalCapBranch F B G a b) k (n + 1) :=
      weightedCutSumNonempty_eq_firstCut _ _ (by omega)
    _ = ∑ q : Fin n, F a q * h q * Q q b := hsumQ
    _ = globalCapPairing F B G h a b := hmat.symm


















end DirectGLSSW
