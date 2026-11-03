import DirectGLSSW.CutFactorization

/-!
# Near-data independence of the concrete finite current

Source: `ep:gauge`, `ep:factorization`, `ep:near-free`.
The entrywise congruence below concerns exactly the strict upper domain.
-/

namespace DirectGLSSW
open scoped BigOperators

/-- Phi on a positive interval reads only strictly upper entries. -/
theorem phi_congr_upper (D H : TripleArray) {X Y : IntervalArray}
    (hXY : ∀ a b, a < b → X a b = Y a b) {i j : ℕ} (hij : i < j) :
    phi D H X i j = phi D H Y i j := by
  rw [phi_eq_unary_add, phi_eq_unary_add, hXY i j hij]
  congr 1
  apply nonUnary_congr_lt D H hij
  intro a b hab _
  exact hXY a b hab

/-- Changing near data first maps the ordinary current to the zero-near
ordinary solution, by factorization and the already proved uniqueness. -/
theorem ordinaryCurrent_after_near (D H : TripleArray) {i j : ℕ} (hij : i < j) :
    phi D (fun _ _ _ => 0) (ordinaryCurrent D H) i j =
      ordinaryCurrent (fun _ _ _ => 0) H i j := by
  apply ordinaryCurrent_unique (fun _ _ _ => 0) H
    (fun a b => phi D (fun _ _ _ => 0) (ordinaryCurrent D H) a b) _ hij
  intro a b hab
  rw [← phi_factorization D H (ordinaryCurrent D H) hab]
  exact ordinaryCurrent_phi D H hab

/-- Source near-free form of the marked output on every positive interval. -/
theorem markedAmplitude_zero_near (D H : TripleArray) {i j : ℕ} (hij : i < j) :
    markedAmplitude D H i j = markedAmplitude (fun _ _ _ => 0) H i j := by
  unfold markedAmplitude
  rw [phi_factorization D (fun a b c => -H a b c) (ordinaryCurrent D H) hij]
  apply phi_congr_upper _ _ _ hij
  intro a b hab
  exact ordinaryCurrent_after_near D H hab

/-- Near-data independence for the actual finite-cut marked expression.
No root-independence or geometry premise enters this rational-array theorem. -/
theorem markedAmplitude_near_independent (D₁ D₂ H : TripleArray)
    {i j : ℕ} (hij : i < j) :
    markedAmplitude D₁ H i j = markedAmplitude D₂ H i j := by
  exact (markedAmplitude_zero_near D₁ H hij).trans
    (markedAmplitude_zero_near D₂ H hij).symm

end DirectGLSSW
