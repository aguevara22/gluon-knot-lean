import DirectGLSSW.Gates
import DirectGLSSW.TriangularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

/-!
# Algebraic cap cancellation

Source: `ep:cap-matrix` to `ep:K`. The cap relation and inverse identities
are explicit hypotheses. Their realization by polygon currents is M3.
-/

namespace DirectGLSSW

/-- The finite-current cap equation forces this identity for a two-sided
inverse of `1 + X`. The ambient ring need not be commutative. -/
theorem cap_inverse_identity {R : Type*} [Ring R] (X S K : R)
    (hcap : S * X + X * S + (X * S * X + X * S * X) = 0)
    (hleft : K * (1 + X) = 1) (hright : (1 + X) * K = 1) :
    K * S + S * K = S + S := by
  have hexpand :
      (1 + X) * S + S * (1 + X) -
        ((1 + X) * S * (1 + X) + (1 + X) * S * (1 + X)) =
      -(S * X + X * S + (X * S * X + X * S * X)) := by
    noncomm_ring
  rw [hcap, neg_zero, sub_eq_zero] at hexpand
  have h := congrArg (fun T : R => K * T * K) hexpand
  dsimp only at h
  have hKS : K * ((1 + X) * S) * K = S * K := by
    rw [← mul_assoc K (1 + X), hleft, one_mul]
  have hSK : K * (S * (1 + X)) * K = K * S := by
    rw [mul_assoc, mul_assoc S, hright, mul_one]
  have hKSK : K * ((1 + X) * S * (1 + X)) * K = S := by
    calc
      K * ((1 + X) * S * (1 + X)) * K =
          (K * (1 + X)) * S * ((1 + X) * K) := by noncomm_ring
      _ = S := by rw [hleft, hright, one_mul, mul_one]
  have hL : K * ((1 + X) * S + S * (1 + X)) * K = S * K + K * S := by
    rw [mul_add, add_mul, hKS, hSK]
  have hR : K * ((1 + X) * S * (1 + X) + (1 + X) * S * (1 + X)) * K =
      S + S := by
    rw [mul_add, add_mul, hKSK]
  rw [hL, hR] at h
  simpa only [add_comm (S * K) (K * S)] using h

/-- Equal diagonal signs force an off-diagonal entry of K to vanish.
This is the algebraic source of the mixed-edge cancellation. -/
theorem equal_sign_offDiagonal_zero {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℚ) (s : n → Sign)
    (h : K * Matrix.diagonal (fun i => (s i).value) +
        Matrix.diagonal (fun i => (s i).value) * K =
        Matrix.diagonal (fun i => (s i).value) +
        Matrix.diagonal (fun i => (s i).value))
    (c d : n) (hne : c ≠ d) (hs : s c = s d) : K c d = 0 := by
  have he := congrFun (congrFun h c) d
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.diagonal_apply_ne _ hne, add_zero] at he
  rw [hs] at he
  cases hd : s d <;> simp only [hd, Sign.value] at he <;> linarith

/-- The concrete finite inverse of a strict upper triangular cap matrix
vanishes between distinct positions of the same sign. Only the cap
relation remains a hypothesis; inverse existence has been proved. -/
theorem cap_finiteInverse_entry_zero {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (s : Fin n → Sign)
    (hX : StrictUpper X)
    (hcap : Matrix.diagonal (fun i => (s i).value) * X +
        X * Matrix.diagonal (fun i => (s i).value) +
        (X * Matrix.diagonal (fun i => (s i).value) * X +
         X * Matrix.diagonal (fun i => (s i).value) * X) = 0)
    (c d : Fin n) (hne : c ≠ d) (hs : s c = s d) :
    finiteInverse X n c d = 0 := by
  obtain ⟨hl, hr⟩ := strictUpper_finiteInverse X hX
  exact equal_sign_offDiagonal_zero (finiteInverse X n) s
    (cap_inverse_identity X _ _ hcap hl hr) c d hne hs

end DirectGLSSW
