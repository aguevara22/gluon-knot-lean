import DirectGLSSW.CurrentFidelity

/-!
# Universal finite inverse for the concrete Phi map

This candidate proves the inverse for every rational interval array, on all
natural-number index pairs. On nonpositive intervals both Phi and its inverse
are the identity; on positive intervals recursion uses only strictly shorter
entries.
-/

namespace DirectGLSSW
open scoped BigOperators

/-- The triangular inverse of `phi D H` applied to arbitrary target data. -/
def inverseCurrent (D H : TripleArray) (Y : IntervalArray) (i j : ℕ) : ℚ :=
  Y i j - nonUnary D H
    (fun a b => if _h : b - a < j - i then inverseCurrent D H Y a b else 0) i j
termination_by j - i

private theorem nonUnary_eq_zero_of_not_lt (D H : TripleArray) (X : IntervalArray)
    {i j : ℕ} (hij : ¬ i < j) : nonUnary D H X i j = 0 := by
  have hIoo : Finset.Ioo i j = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro a ha
    simp only [Finset.mem_Ioo] at ha
    omega
  simp [nonUnary, hIoo]

private theorem phi_eq_input_of_not_lt (D H : TripleArray) (X : IntervalArray)
    {i j : ℕ} (hij : ¬ i < j) : phi D H X i j = X i j := by
  have hIoo : Finset.Ioo i j = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro a ha
    simp only [Finset.mem_Ioo] at ha
    omega
  rw [phi, hIoo]
  simp [cutContribution_empty]

private theorem inverseCurrent_eq_input_of_not_lt (D H : TripleArray) (Y : IntervalArray)
    {i j : ℕ} (hij : ¬ i < j) : inverseCurrent D H Y i j = Y i j := by
  rw [inverseCurrent]
  rw [nonUnary_eq_zero_of_not_lt D H _ hij]
  simp

/-- On positive intervals, the generalized inverse satisfies its triangular recurrence. -/
theorem inverseCurrent_recurrence (D H : TripleArray) (Y : IntervalArray)
    {i j : ℕ} (hij : i < j) :
    inverseCurrent D H Y i j = Y i j - nonUnary D H (inverseCurrent D H Y) i j := by
  rw [inverseCurrent]
  congr 1
  apply nonUnary_congr_lt D H hij
  intro a b _ hlt
  simp only [dif_pos hlt]

/-- The finite triangular inverse solves Phi against every target array entry. -/
theorem inverseCurrent_phi (D H : TripleArray) (Y : IntervalArray) :
    ∀ i j, phi D H (inverseCurrent D H Y) i j = Y i j := by
  intro i j
  by_cases hij : i < j
  · calc
      phi D H (inverseCurrent D H Y) i j =
          inverseCurrent D H Y i j + nonUnary D H (inverseCurrent D H Y) i j :=
        phi_eq_unary_add D H (inverseCurrent D H Y) i j
      _ = Y i j := by
        rw [inverseCurrent_recurrence D H Y hij]
        exact sub_add_cancel _ _
  · calc
      phi D H (inverseCurrent D H Y) i j = inverseCurrent D H Y i j :=
        phi_eq_input_of_not_lt D H _ hij
      _ = Y i j := inverseCurrent_eq_input_of_not_lt D H Y hij

private theorem inverseCurrent_unique_upper (D H : TripleArray) (Y X : IntervalArray)
    (hX : ∀ i j, phi D H X i j = Y i j) {i j : ℕ} (hij : i < j) :
    X i j = inverseCurrent D H Y i j := by
  generalize hn : j - i = n
  induction n using Nat.strong_induction_on generalizing i j with
  | h n ih =>
      have hshort : nonUnary D H X i j =
          nonUnary D H (inverseCurrent D H Y) i j := by
        apply nonUnary_congr_lt D H hij
        intro a b hab hlt
        exact ih (b - a) (by omega) hab rfl
      have hsource : X i j + nonUnary D H X i j = Y i j := by
        rw [← phi_eq_unary_add]
        exact hX i j
      have hvalue : X i j = Y i j - nonUnary D H (inverseCurrent D H Y) i j := by
        rw [← hshort]
        exact (eq_sub_iff_add_eq).mpr hsource
      rw [hvalue, inverseCurrent_recurrence D H Y hij]

/-- Any array solving the Phi equation is the generalized triangular inverse. -/
theorem inverseCurrent_unique (D H : TripleArray) (Y X : IntervalArray)
    (hX : ∀ i j, phi D H X i j = Y i j) :
    ∀ i j, X i j = inverseCurrent D H Y i j := by
  intro i j
  by_cases hij : i < j
  · exact inverseCurrent_unique_upper D H Y X hX hij
  · calc
      X i j = phi D H X i j := (phi_eq_input_of_not_lt D H X hij).symm
      _ = Y i j := hX i j
      _ = inverseCurrent D H Y i j :=
        (inverseCurrent_eq_input_of_not_lt D H Y hij).symm

/-- For arbitrary rational near data, the concrete finite Phi map is bijective. -/
theorem phi_bijective (D H : TripleArray) :
    Function.Bijective (fun X : IntervalArray => phi D H X) := by
  constructor
  · intro X Z hXZ
    have hX : ∀ i j, phi D H X i j = phi D H X i j := by intro _ _; rfl
    have hZ : ∀ i j, phi D H Z i j = phi D H X i j := by
      intro i j
      exact (congrFun (congrFun hXZ i) j).symm
    funext i
    funext j
    calc
      X i j = inverseCurrent D H (phi D H X) i j :=
        inverseCurrent_unique D H (phi D H X) X hX i j
      _ = Z i j :=
        (inverseCurrent_unique D H (phi D H X) Z hZ i j).symm
  · intro Y
    refine ⟨inverseCurrent D H Y, ?_⟩
    funext i
    funext j
    exact inverseCurrent_phi D H Y i j


end DirectGLSSW
