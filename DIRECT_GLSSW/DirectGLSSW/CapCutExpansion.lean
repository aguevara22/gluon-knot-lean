import DirectGLSSW.FirstCut
import DirectGLSSW.TriangularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW
open scoped BigOperators

/-- Strictly upper branch matrix on all positions before the terminal vertex. -/
def capBranchMatrix {j : ℕ} (b : IntervalArray) : Matrix (Fin j) (Fin j) ℚ :=
  fun p q => if p.val < q.val then b p.val q.val else 0

/-- Diagonal matrix of vertex weights. -/
def capWeightMatrix {j : ℕ} (w : ℕ → ℚ) : Matrix (Fin j) (Fin j) ℚ :=
  Matrix.diagonal (fun p => w p.val)

/-- First branch row, supported strictly after the initial vertex. -/
def capFirstRow {j : ℕ} (b : IntervalArray) (i : ℕ) : Matrix (Fin 1) (Fin j) ℚ :=
  fun _ p => if i < p.val then b i p.val else 0

/-- Last branch column into the terminal vertex. -/
def capLastColumn {j : ℕ} (b : IntervalArray) : Matrix (Fin j) (Fin 1) ℚ :=
  fun p _ => b p.val j

/-- Finite resolvent for the strictly upper branch-weight matrix. -/
def capCutResolvent {j : ℕ} (w : ℕ → ℚ) (b : IntervalArray) : Matrix (Fin j) (Fin j) ℚ :=
  finiteInverse (-(capBranchMatrix b * capWeightMatrix w)) j

/-- Matrix expression for the nonempty weighted cut expansion. -/
def capCutExpansion {j : ℕ} (w : ℕ → ℚ) (b : IntervalArray) (i : ℕ) : ℚ :=
  (capFirstRow (j := j) b i * capWeightMatrix (j := j) w *
    capCutResolvent (j := j) w b * capLastColumn (j := j) b) (0 : Fin 1) (0 : Fin 1)

private theorem capBranchWeight_apply {j : ℕ} (w : ℕ → ℚ) (b : IntervalArray)
    (p q : Fin j) :
    (capBranchMatrix (j := j) b * capWeightMatrix (j := j) w) p q =
      if p.val < q.val then b p.val q.val * w q.val else 0 := by
  classical
  simp [capBranchMatrix, capWeightMatrix, Matrix.mul_apply, Matrix.diagonal,
    Finset.sum_eq_single q]

private theorem capBranchWeight_strictUpper {j : ℕ} (w : ℕ → ℚ) (b : IntervalArray) :
    StrictUpper (n := j) (capBranchMatrix (j := j) b * capWeightMatrix (j := j) w) := by
  intro p q hqp
  rw [capBranchWeight_apply (j := j)]
  simp [Nat.not_lt.mpr hqp]

private theorem capResolvent_recurrence {j : ℕ} (w : ℕ → ℚ) (b : IntervalArray) :
    capCutResolvent (j := j) w b * capLastColumn (j := j) b =
      capLastColumn (j := j) b + (capBranchMatrix (j := j) b * capWeightMatrix (j := j) w) *
        (capCutResolvent (j := j) w b * capLastColumn (j := j) b) := by
  let X : Matrix (Fin j) (Fin j) ℚ := capBranchMatrix (j := j) b * capWeightMatrix (j := j) w
  have hX : StrictUpper (n := j) (-X) := by
    intro p q hqp
    dsimp [X]
    change -((capBranchMatrix (j := j) b * capWeightMatrix (j := j) w) p q) = 0
    rw [capBranchWeight_apply (j := j)]
    simp [Nat.not_lt.mpr hqp]
  have hInv := (strictUpper_finiteInverse (-X) hX).2
  change (1 + -X) * capCutResolvent (j := j) w b = 1 at hInv
  have hmul := congrArg (fun M : Matrix (Fin j) (Fin j) ℚ =>
      M * capLastColumn (j := j) b) hInv
  have hmul' : capCutResolvent (j := j) w b * capLastColumn (j := j) b +
      (-X) * (capCutResolvent (j := j) w b * capLastColumn (j := j) b) =
      capLastColumn (j := j) b := by
    simpa [Matrix.mul_assoc, Matrix.add_mul] using hmul
  have hnegMul : (-X) * (capCutResolvent (j := j) w b * capLastColumn (j := j) b) =
      -(X * (capCutResolvent (j := j) w b * capLastColumn (j := j) b)) := by
    ext p q
    simp [Matrix.mul_apply]
  have hmul2 := hmul'
  rw [hnegMul] at hmul2
  have hrec : capCutResolvent (j := j) w b * capLastColumn (j := j) b =
      capLastColumn (j := j) b + X * (capCutResolvent (j := j) w b * capLastColumn (j := j) b) := by
    ext p q
    have he := congrArg (fun M : Matrix (Fin j) (Fin 1) ℚ => M p q) hmul2
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply] at he
    simp only [Matrix.add_apply, Matrix.neg_apply]
    rw [← he]
    ring
  dsimp [X] at hrec ⊢
  exact hrec

private theorem cap_sum_fin_eq_Ioo {j : ℕ} (p : Fin j) (f : Fin j → ℚ) :
    (∑ q : Fin j, if p.val < q.val then f q else 0) =
      ∑ k : ↥(Finset.Ioo p.val j), f ⟨k.1, (Finset.mem_Ioo.mp k.2).2⟩ := by
  classical
  let s : Finset (Fin j) := Finset.univ.filter (fun q => p.val < q.val)
  have hfilter : (∑ q : Fin j, if p.val < q.val then f q else 0) =
      ∑ q ∈ s, f q := by
    change (∑ q ∈ Finset.univ, if p.val < q.val then f q else 0) = _
    simp [s, Finset.sum_filter]
  rw [hfilter]
  have hcoe : (∑ q ∈ s, f q) = ∑ q : ↥s, f q.1 := (Finset.sum_coe_sort s f).symm
  rw [hcoe]
  let e : ↥s ≃ ↥(Finset.Ioo p.val j) := {
    toFun := fun q => ⟨q.1.val, Finset.mem_Ioo.mpr ⟨(Finset.mem_filter.mp q.2).2, q.1.isLt⟩⟩
    invFun := fun k => ⟨⟨k.1, (Finset.mem_Ioo.mp k.2).2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_Ioo.mp k.2).1⟩⟩
    left_inv := by intro q; apply Subtype.ext; apply Fin.ext; rfl
    right_inv := by intro k; apply Subtype.ext; rfl }
  simpa [e] using e.sum_comp (fun k => f ⟨k.1, (Finset.mem_Ioo.mp k.2).2⟩)

private theorem capFirstRowWeight_apply {j : ℕ} (w : ℕ → ℚ) (b : IntervalArray)
    (i : ℕ) (p : Fin j) :
    (capFirstRow (j := j) b i * capWeightMatrix (j := j) w) (0 : Fin 1) p =
      if i < p.val then b i p.val * w p.val else 0 := by
  classical
  simp [capFirstRow, capWeightMatrix, Matrix.mul_apply, Matrix.diagonal,
    Finset.sum_eq_single p]

private theorem capResolvent_column_eq_weightedCutSum {j : ℕ}
    (w : ℕ → ℚ) (b : IntervalArray) (p : Fin j) :
    (capCutResolvent (j := j) w b * capLastColumn (j := j) b) p (0 : Fin 1) =
      weightedCutSum w b p.val j := by
  let P : ℕ → Prop := fun n => ∀ p : Fin j, j - p.val = n →
    (capCutResolvent (j := j) w b * capLastColumn (j := j) b) p (0 : Fin 1) =
      weightedCutSum w b p.val j
  have hall : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hlen
      have hp : p.val < j := p.isLt
      have hrow := congrArg (fun M : Matrix (Fin j) (Fin 1) ℚ => M p (0 : Fin 1))
        (capResolvent_recurrence (j := j) w b)
      have hprod :
          ((capBranchMatrix (j := j) b * capWeightMatrix (j := j) w) *
            (capCutResolvent (j := j) w b * capLastColumn (j := j) b)) p (0 : Fin 1) =
            ∑ q : Fin j,
              (if p.val < q.val then b p.val q.val * w q.val else 0) *
                (capCutResolvent (j := j) w b * capLastColumn (j := j) b) q (0 : Fin 1) := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro q hq
        rw [capBranchWeight_apply]
      have hrow' :
          (capCutResolvent (j := j) w b * capLastColumn (j := j) b) p (0 : Fin 1) =
            b p.val j + ∑ q : Fin j,
              (if p.val < q.val then b p.val q.val * w q.val else 0) *
                (capCutResolvent (j := j) w b * capLastColumn (j := j) b) q (0 : Fin 1) := by
        change (capCutResolvent (j := j) w b * capLastColumn (j := j) b) p (0 : Fin 1) =
          (capLastColumn (j := j) b +
            (capBranchMatrix (j := j) b * capWeightMatrix (j := j) w) *
              (capCutResolvent (j := j) w b * capLastColumn (j := j) b)) p (0 : Fin 1) at hrow
        rw [Matrix.add_apply] at hrow
        simpa [capLastColumn, hprod] using hrow
      have hmatrix :
          (capCutResolvent (j := j) w b * capLastColumn (j := j) b) p (0 : Fin 1) =
            b p.val j + ∑ q : Fin j,
              (if p.val < q.val then b p.val q.val * w q.val *
                (capCutResolvent (j := j) w b * capLastColumn (j := j) b) q (0 : Fin 1) else 0) := by
        simpa only [ite_mul, zero_mul] using hrow'
      have hsum := cap_sum_fin_eq_Ioo p (fun q =>
        b p.val q.val * w q.val *
          (capCutResolvent (j := j) w b * capLastColumn (j := j) b) q (0 : Fin 1))
      rw [hsum] at hmatrix
      rw [weightedCutSum_eq_firstCut w b hp]
      rw [hmatrix]
      congr 1
      rw [← Finset.sum_coe_sort (Finset.Ioo p.val j)
        (fun k => b p.val k * w k * weightedCutSum w b k j)]
      apply Fintype.sum_congr
      intro k
      have hk' := Finset.mem_Ioo.mp k.2
      have hlt : j - k.1 < n := by rw [← hlen]; omega
      have hq := ih (j - k.1) hlt (⟨k.1, hk'.2⟩ : Fin j) rfl
      change b p.val k.1 * w k.1 *
          (capCutResolvent (j := j) w b * capLastColumn (j := j) b)
            ⟨k.1, hk'.2⟩ (0 : Fin 1) =
        b p.val k.1 * w k.1 * weightedCutSum w b k.1 j
      rw [hq]
  exact hall (j - p.val) p rfl

/--
This is an algebraic finite expansion only. It allows arbitrary rational weights,
including zero weights, arbitrary branch entries, and the length-one case. It
establishes no geometric sign evaluation or root-independence statement.
-/
theorem weightedCutSumNonempty_eq_capCutExpansion
    (w : ℕ → ℚ) (b : IntervalArray) {i j : ℕ} (hij : i < j) :
    weightedCutSumNonempty w b i j = capCutExpansion (j := j) w b i := by
  classical
  let Q : Matrix (Fin j) (Fin 1) ℚ :=
    capCutResolvent (j := j) w b * capLastColumn (j := j) b
  have hmatrix : capCutExpansion (j := j) w b i =
      ∑ p : Fin j, if i < p.val then b i p.val * w p.val * Q p (0 : Fin 1) else 0 := by
    change (((capFirstRow (j := j) b i * capWeightMatrix (j := j) w) *
      capCutResolvent (j := j) w b) * capLastColumn (j := j) b)
        (0 : Fin 1) (0 : Fin 1) = _
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp_rw [capFirstRowWeight_apply]
    simp only [ite_mul, zero_mul]
    rfl
  have hsumQ :
      (∑ p : Fin j, if i < p.val then b i p.val * w p.val * Q p (0 : Fin 1) else 0) =
        ∑ k ∈ Finset.Ioo i j, b i k * w k * weightedCutSum w b k j := by
    let pi : Fin j := ⟨i, hij⟩
    have hrange := cap_sum_fin_eq_Ioo pi (fun p =>
      b i p.val * w p.val * Q p (0 : Fin 1))
    rw [hrange]
    calc
      (∑ k : ↥(Finset.Ioo i j),
          b i k.1 * w k.1 * Q ⟨k.1, (Finset.mem_Ioo.mp k.2).2⟩ (0 : Fin 1))
          = ∑ k : ↥(Finset.Ioo i j),
            b i k.1 * w k.1 * weightedCutSum w b k.1 j := by
              apply Fintype.sum_congr
              intro k
              have hq := capResolvent_column_eq_weightedCutSum w b
                (⟨k.1, (Finset.mem_Ioo.mp k.2).2⟩ : Fin j)
              change b i k.1 * w k.1 *
                  (capCutResolvent (j := j) w b * capLastColumn (j := j) b)
                    ⟨k.1, (Finset.mem_Ioo.mp k.2).2⟩ (0 : Fin 1) =
                b i k.1 * w k.1 * weightedCutSum w b k.1 j
              rw [hq]
      _ = ∑ k ∈ Finset.Ioo i j, b i k * w k * weightedCutSum w b k j :=
        Finset.sum_coe_sort (Finset.Ioo i j)
          (fun k => b i k * w k * weightedCutSum w b k j)
  calc
    weightedCutSumNonempty w b i j =
        ∑ k ∈ Finset.Ioo i j, b i k * w k * weightedCutSum w b k j :=
      weightedCutSumNonempty_eq_firstCut w b hij
    _ = capCutExpansion (j := j) w b i := by rw [← hsumQ, ← hmatrix]















end DirectGLSSW
