import SM.RegularPerturbation
import SM.VertexInsertion
import SM.RotationTriangle
import SM.Admissible

/-! Actual subdivision and generic perturbation reduce fibre existence to
regular seed polygons. Necessary admissibility follows from geometric bounds.
The seed-existence part of the full source lemma is not assumed or asserted. -/

namespace SM

variable {m n : ℕ} [NeZero m] [NeZero n]

theorem exists_regular_subdivision {P : LabelledTuple m} (hP : Regular P) (k : ℕ) :
    ∃ Q : LabelledTuple (m + k), Regular Q ∧ rotationNumber Q = rotationNumber P := by
  induction k with
  | zero => exact ⟨P, hP, rfl⟩
  | succ k ih =>
    obtain ⟨Q, hQ, hrot⟩ := ih
    refine ⟨insertVertex Q 0 (1 / 2), regular_insertVertex hQ 0 (by norm_num) (by norm_num), ?_⟩
    exact (rotationNumber_insertVertex hQ 0 (by norm_num) (by norm_num)).trans hrot

theorem exists_regular_at_larger_size {P : LabelledTuple m} (hP : Regular P) (hmn : m ≤ n) :
    ∃ Q : LabelledTuple n, Regular Q ∧ rotationNumber Q = rotationNumber P := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact exists_regular_subdivision hP k

theorem exists_generic_at_larger_size (hn : 3 ≤ n) {P : LabelledTuple m}
    (hP : Regular P) (hmn : m ≤ n) :
    ∃ Q : LabelledTuple n, Generic Q ∧ rotationNumber Q = rotationNumber P := by
  obtain ⟨Q, hQ, hrot⟩ := exists_regular_at_larger_size hP hmn
  obtain ⟨T, hT, hTrot⟩ := exists_generic_same_rotation hn hQ
  exact ⟨T, hT, hTrot.trans hrot⟩

theorem generic_rotation_admissible (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (r : ℤ) (hr : rotationNumber P = (r : ℝ)) : Admissible (n : ℤ) r := by
  have hreg := generic_regular hn hP
  have hb := rotationNumber_strict_bound hreg
  rw [hr] at hb
  refine ⟨by exact_mod_cast hn, by exact_mod_cast hb, ?_⟩
  intro hbad
  have hn3z : (n : ℤ) = 3 := congrArg Prod.fst hbad
  have hn3 : n = 3 := by exact_mod_cast hn3z
  have hr0 : r = 0 := congrArg Prod.snd hbad
  subst n
  have hz : rotationNumber P = 0 := by simpa only [hr0, Int.cast_zero] using hr
  exact (rotationNumber_triangle hreg).2.2 hz

end SM
