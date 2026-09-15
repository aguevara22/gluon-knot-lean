import SM.RotationContinuity
import SM.RotationReversal
import SM.RotationTriangle
import SM.VertexInsertion

/-! Every clause of source lem:rot, including actual strict edge-interior
vertex insertion on every edge. All constructions use the source's expressly
permitted labelled/equivariant formalization, with actual cyclic invariance. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem rotation_number (hn : 3 ≤ n) (P : LabelledTuple n) (h : Regular P) :
    rotationNumber P = (1 / (2 * Real.pi)) * (∑ i : ZMod n, principalTurn P i) ∧
    (∃ k : ℤ, rotationNumber P = (k : ℝ)) ∧
    (∀ Q : LabelledTuple n, ∀ γ : Path P Q, (∀ u, Regular (γ u)) →
      ∀ s t : unitInterval, rotationNumber (γ s) = rotationNumber (γ t)) ∧
    (∀ i : ZMod n, ∀ t : ℝ, 0 < t → t < 1 →
      (∀ j : ZMod n, insertVertex P i t (insertIndex j) = P (j + (i + 1))) ∧
      insertVertex P i t (insertedIndex n) = edgePoint P i t ∧
      insertVertex P i t (insertedIndex n) ∈ edgeInterior P i ∧
      Regular (insertVertex P i t) ∧ rotationNumber (insertVertex P i t) = rotationNumber P) ∧
    Regular (reversal P) ∧ rotationNumber (reversal P) = -rotationNumber P ∧
    (n = 3 → (∀ i : ZMod n, rotationNumber P = (turn P i : ℝ)) ∧
      (rotationNumber P = 1 ∨ rotationNumber P = -1) ∧ rotationNumber P ≠ 0) ∧
    2 * |rotationNumber P| < (n : ℝ) ∧
    (∀ a : ZMod n, rotationNumber (shift a P) = rotationNumber P) := by
  refine ⟨?_, rotationNumber_integer h, ?_, ?_, regular_reversal_forward h,
    rotationNumber_reversal h, ?_, rotationNumber_strict_bound h,
    fun a => rotationNumber_shift a P⟩
  · unfold rotationNumber
    ring
  · intro Q γ hr s t
    exact rotationNumber_family_constant γ.continuous hr s t
  · intro i t ht0 ht1
    exact ⟨fun j => insertVertex_old P i j t, insertVertex_new P i t,
      insertVertex_new_mem_edgeInterior P i ht0 ht1, regular_insertVertex h i ht0 ht1,
      rotationNumber_insertVertex h i ht0 ht1⟩
  · intro hthree
    subst n
    exact rotationNumber_triangle h

end SM
