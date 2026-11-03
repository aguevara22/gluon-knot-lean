import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DirectGLSSW

open scoped BigOperators


theorem finiteRankOneSandwich {n : ℕ} (a b c d : Fin n → ℚ) (κ : ℚ) :
    (∑ i, ∑ j, (a i * (κ * c i * b j)) * d j) =
      κ * (∑ i, a i * c i) * (∑ j, b j * d j) := by
  calc
    (∑ i, ∑ j, (a i * (κ * c i * b j)) * d j) =
        ∑ i, (κ * a i * c i) * (∑ j, b j * d j) := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            (∑ j, (a i * (κ * c i * b j)) * d j) =
                ∑ j, (κ * a i * c i) * (b j * d j) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = (κ * a i * c i) * (∑ j, b j * d j) := by rw [Finset.mul_sum]
    _ = (κ * (∑ i, a i * c i)) * (∑ j, b j * d j) := by
          calc
            (∑ i, (κ * a i * c i) * (∑ j, b j * d j)) =
                (∑ i, κ * a i * c i) * (∑ j, b j * d j) :=
                  (Finset.sum_mul Finset.univ (fun i => κ * a i * c i) (∑ j, b j * d j)).symm
            _ = (κ * (∑ i, a i * c i)) * (∑ j, b j * d j) := by
                  congr 1
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
    _ = κ * (∑ i, a i * c i) * (∑ j, b j * d j) := by ring

/-- Entrywise rank-one jumps and the endpoint left/right eigenvector laws
force the finite pairwise sandwich identity. The geometry that supplies
these premises is intentionally outside this algebraic lemma. -/
theorem finiteCapSandwichIdentity
    {α : Type} [DecidableEq α] (E : Finset α) (n : ℕ)
    (s : α → ℚ) (u v : α → Fin n → ℚ)
    (JL JR : Matrix (Fin n) (Fin n) ℚ)
    (vc ud : Fin n → ℚ) (sc sd : ℚ)
    (hjump : ∀ i j, JR i j - JL i j =
      ∑ e ∈ E, 2 * s e * u e i * v e j)
    (hleft : ∀ j, (∑ i, vc i * JL i j) = sc * vc j)
    (hright : ∀ i, (∑ j, JR i j * ud j) = -sd * ud i) :
    (sc + sd) * (∑ i, vc i * ud i) +
      2 * ∑ e ∈ E, s e * (∑ i, vc i * u e i) * (∑ j, v e j * ud j) = 0 := by
  classical
  let dot : ℚ := ∑ i, vc i * ud i
  let sandwich (M : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
    ∑ i, vc i * (∑ j, M i j * ud j)
  have hRightSandwich : sandwich JR = -sd * dot := by
    dsimp [sandwich, dot]
    calc
      (∑ i, vc i * ∑ j, JR i j * ud j) =
          ∑ i, vc i * (-sd * ud i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hright i]
      _ = -sd * ∑ i, vc i * ud i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
  have hLeftSandwich : sandwich JL = sc * dot := by
    dsimp [sandwich, dot]
    calc
      (∑ i, vc i * ∑ j, JL i j * ud j) =
          ∑ i, ∑ j, (vc i * JL i j) * ud j := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = ∑ j, ∑ i, (vc i * JL i j) * ud j := Finset.sum_comm
      _ = ∑ j, (∑ i, vc i * JL i j) * ud j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.sum_mul]
      _ = ∑ j, (sc * vc j) * ud j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hleft j]
      _ = sc * ∑ j, vc j * ud j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
  have hSubSandwich : sandwich (JR - JL) = sandwich JR - sandwich JL := by
    dsimp [sandwich]
    calc
      (∑ i, vc i * ∑ j, (JR - JL) i j * ud j) =
          ∑ i, vc i * ((∑ j, JR i j * ud j) - ∑ j, JL i j * ud j) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply congrArg (fun z : ℚ => vc i * z)
            calc
              (∑ j, (JR - JL) i j * ud j) =
                  ∑ j, (JR i j - JL i j) * ud j := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [Matrix.sub_apply]
              _ = (∑ j, JR i j * ud j) - ∑ j, JL i j * ud j := by
                    calc
                      (∑ j, (JR i j - JL i j) * ud j) =
                          ∑ j, (JR i j * ud j - JL i j * ud j) := by
                            apply Finset.sum_congr rfl
                            intro j hj
                            ring
                      _ = (∑ j, JR i j * ud j) - ∑ j, JL i j * ud j :=
                            Finset.sum_sub_distrib
      _ = ∑ i, (vc i * (∑ j, JR i j * ud j) - vc i * ∑ j, JL i j * ud j) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i, vc i * ∑ j, JR i j * ud j) -
          ∑ i, vc i * ∑ j, JL i j * ud j := Finset.sum_sub_distrib
  have hentry (i j : Fin n) : (JR - JL) i j =
      ∑ e ∈ E, 2 * s e * u e i * v e j := by
    rw [Matrix.sub_apply, hjump i j]
  have hRowJump (i : Fin n) :
      (∑ j, (∑ e ∈ E, 2 * s e * u e i * v e j) * ud j) =
        ∑ e ∈ E, (2 * s e * u e i) * (∑ j, v e j * ud j) := by
    calc
      (∑ j, (∑ e ∈ E, 2 * s e * u e i * v e j) * ud j) =
          ∑ j, ∑ e ∈ E, (2 * s e * u e i * v e j) * ud j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.sum_mul]
      _ = ∑ e ∈ E, ∑ j, (2 * s e * u e i * v e j) * ud j := Finset.sum_comm
      _ = ∑ e ∈ E, (2 * s e * u e i) * (∑ j, v e j * ud j) := by
            apply Finset.sum_congr rfl
            intro e he
            calc
              (∑ j, (2 * s e * u e i * v e j) * ud j) =
                  ∑ j, (2 * s e * u e i) * (v e j * ud j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
              _ = (2 * s e * u e i) * (∑ j, v e j * ud j) := by rw [Finset.mul_sum]
  have hJumpSandwich : sandwich (JR - JL) =
      2 * ∑ e ∈ E, s e * (∑ i, vc i * u e i) * (∑ j, v e j * ud j) := by
    dsimp [sandwich]
    calc
      (∑ i, vc i * ∑ j, (JR - JL) i j * ud j) =
          ∑ i, vc i * ∑ e ∈ E, (2 * s e * u e i) * (∑ j, v e j * ud j) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply congrArg (fun z : ℚ => vc i * z)
            calc
              (∑ j, (JR - JL) i j * ud j) =
                  ∑ j, (∑ e ∈ E, 2 * s e * u e i * v e j) * ud j := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [hentry i j]
              _ = ∑ e ∈ E, (2 * s e * u e i) * (∑ j, v e j * ud j) := hRowJump i
      _ = ∑ i, ∑ e ∈ E, (2 * s e * vc i * u e i) * (∑ j, v e j * ud j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e he
            ring
      _ = ∑ e ∈ E, ∑ i, (2 * s e * vc i * u e i) * (∑ j, v e j * ud j) := Finset.sum_comm
      _ = ∑ e ∈ E, (2 * s e) * (∑ i, vc i * u e i) * (∑ j, v e j * ud j) := by
            apply Finset.sum_congr rfl
            intro e he
            calc
              (∑ i, (2 * s e * vc i * u e i) * (∑ j, v e j * ud j)) =
                  (∑ i, 2 * s e * vc i * u e i) * (∑ j, v e j * ud j) :=
                    (Finset.sum_mul Finset.univ (fun i => 2 * s e * vc i * u e i)
                      (∑ j, v e j * ud j)).symm
              _ = (2 * s e * (∑ i, vc i * u e i)) * (∑ j, v e j * ud j) := by
                    congr 1
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
      _ = 2 * ∑ e ∈ E, s e * (∑ i, vc i * u e i) * (∑ j, v e j * ud j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e he
            ring
  have hvalue : sandwich (JR - JL) = -(sc + sd) * dot := by
    calc
      sandwich (JR - JL) = sandwich JR - sandwich JL := hSubSandwich
      _ = (-sd * dot) - (sc * dot) := by rw [hRightSandwich, hLeftSandwich]
      _ = -(sc + sd) * dot := by ring
  have hscalar : -(sc + sd) * dot =
      2 * ∑ e ∈ E, s e * (∑ i, vc i * u e i) * (∑ j, v e j * ud j) :=
    hvalue.symm.trans hJumpSandwich
  dsimp [dot] at hscalar ⊢
  linarith



end DirectGLSSW

