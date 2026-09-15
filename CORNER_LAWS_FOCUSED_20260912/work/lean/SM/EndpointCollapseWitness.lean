import SM.SixEndpointTuples

/-! Explicit diagonal-collapse witnesses for distinct edge pairings. Finite
slot calculations are linked to unrestricted actual labelled tuples. -/

namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ}

def endpointCollapseWitness (i j : Fin 6) : Fin 6 → Plane := fun k =>
  if k.val = i.val ∨ k.val = j.val then (0, 0)
  else if k.val / 2 = i.val / 2 then (1, 0)
  else if k.val / 2 = j.val / 2 then (0, 1)
  else if k.val % 2 = 0 then (1, 0) else (0, 1)

theorem endpointCollapseWitness_equal (i j : Fin 6) :
    endpointCollapseWitness i j i = endpointCollapseWitness i j j := by
  simp [endpointCollapseWitness]

theorem endpointCollapseWitness_ne_zero (i j : Fin 6) (h : i.val / 2 ≠ j.val / 2) :
    sixPointConcurrence (endpointCollapseWitness i j) ≠ 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [endpointCollapseWitness, sixPointConcurrence_formula] at *

theorem concurrenceDet_zero_of_collapsed_first (P : LabelledTuple n) (e f g : ZMod n)
    (h : P e = P (e + 1)) : concurrenceDet P e f g = 0 := by
  rw [concurrenceDet_formula]
  simp [edgeLineA, edgeLineB, edgeLineC, h]

theorem polynomial_not_dvd_of_evaluation {σ : Type*} (p q : MvPolynomial σ ℝ)
    (ρ : σ → ℝ) (hp : eval ρ p = 0) (hq : eval ρ q ≠ 0) : ¬ p ∣ q := by
  rintro ⟨r, hr⟩
  apply hq
  rw [hr, map_mul, hp, zero_mul]

theorem concurrence_not_associated_of_crossed_slots [Nontrivial (ZMod n)]
    (e f g a b c : ZMod n) (hab : remote a b) (hac : remote a c) (hbc : remote b c)
    (i j : Fin 6) (he : e = sixEndpointMap a b c i)
    (he1 : e + 1 = sixEndpointMap a b c j) (hij : i.val / 2 ≠ j.val / 2) :
    ¬ Associated (concurrencePolynomial e f g) (concurrencePolynomial a b c) := by
  let U := endpointCollapseWitness i j
  let P := extendSixEndpointTuple a b c U
  have hP : P e = P (e + 1) := by
    change extendSixEndpointTuple a b c U e = extendSixEndpointTuple a b c U (e + 1)
    rw [he1, he, extendSixEndpointTuple_apply a b c hab hac hbc,
      extendSixEndpointTuple_apply a b c hab hac hbc]
    exact endpointCollapseWitness_equal i j
  have hp : eval (scalarCoordinates P) (concurrencePolynomial e f g) = 0 := by
    rw [eval_concurrencePolynomial]
    exact concurrenceDet_zero_of_collapsed_first P e f g hP
  have hq : eval (scalarCoordinates P) (concurrencePolynomial a b c) ≠ 0 := by
    rw [eval_concurrencePolynomial]
    change concurrenceDet (extendSixEndpointTuple a b c U) a b c ≠ 0
    rw [concurrenceDet_extendSixEndpointTuple a b c hab hac hbc]
    exact endpointCollapseWitness_ne_zero i j hij
  intro h
  exact polynomial_not_dvd_of_evaluation _ _ (scalarCoordinates P) hp hq h.dvd

end

end SM
