import SM.PolynomialVertexSupport
import SM.SixEndpointTuples

/-! Exact six-endpoint support of the actual concurrence polynomial. Explicit
finite tuples show that every endpoint's x coordinate genuinely occurs. -/

namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ}

theorem scalarCoordinates_agree_off_X (P Q : LabelledTuple n) (i : ZMod n)
    (hother : ∀ v, v ≠ i → P v = Q v) (hy : (P i).2 = (Q i).2)
    (z : ScalarCoordinate n) (hz : z ≠ (i, 0)) :
    scalarCoordinates P z = scalarCoordinates Q z := by
  obtain ⟨v, c⟩ := z
  by_cases hv : v = i
  · subst v
    fin_cases c
    · exact (hz rfl).elim
    · simpa [scalarCoordinates] using hy
  · simp [scalarCoordinates, hother v hv]

def endpointCoordinateWitness (j : Fin 6) (t : ℝ) (k : Fin 6) : Plane :=
  match j.val, k.val with
  | 0, 0 => (t, 0)
  | 0, 1 => (0, 1)
  | 0, 2 => (1, 0)
  | 0, 3 => (1, 1)
  | 0, 4 => (0, 0)
  | 0, 5 => (1, 0)
  | 1, 0 => (0, 1)
  | 1, 1 => (t, 0)
  | 1, 2 => (1, 0)
  | 1, 3 => (1, 1)
  | 1, 4 => (0, 0)
  | 1, 5 => (1, 0)
  | 2, 0 => (1, 0)
  | 2, 1 => (1, 1)
  | 2, 2 => (t, 0)
  | 2, 3 => (0, 1)
  | 2, 4 => (0, 0)
  | 2, 5 => (1, 0)
  | 3, 0 => (1, 0)
  | 3, 1 => (1, 1)
  | 3, 2 => (0, 1)
  | 3, 3 => (t, 0)
  | 3, 4 => (0, 0)
  | 3, 5 => (1, 0)
  | 4, 0 => (1, 0)
  | 4, 1 => (1, 1)
  | 4, 2 => (0, 0)
  | 4, 3 => (1, 0)
  | 4, 4 => (t, 0)
  | 4, 5 => (0, 1)
  | 5, 0 => (1, 0)
  | 5, 1 => (1, 1)
  | 5, 2 => (0, 0)
  | 5, 3 => (1, 0)
  | 5, 4 => (0, 1)
  | 5, 5 => (t, 0)
  | _, _ => (0, 0)

theorem endpointCoordinateWitness_agree (j k : Fin 6) (h : k ≠ j) (s t : ℝ) :
    endpointCoordinateWitness j s k = endpointCoordinateWitness j t k := by
  fin_cases j <;> fin_cases k <;> simp_all [endpointCoordinateWitness]

theorem endpointCoordinateWitness_y (j : Fin 6) (s t : ℝ) :
    (endpointCoordinateWitness j s j).2 = (endpointCoordinateWitness j t j).2 := by
  fin_cases j <;> simp [endpointCoordinateWitness]

theorem endpointCoordinateWitness_values (j : Fin 6) :
    sixPointConcurrence (endpointCoordinateWitness j 0) ≠
      sixPointConcurrence (endpointCoordinateWitness j 1) := by
  fin_cases j <;>
    norm_num [sixPointConcurrence_formula, endpointCoordinateWitness]

theorem concurrencePolynomial_X_endpoint [Nontrivial (ZMod n)] (e f g : ZMod n)
    (hef : remote e f) (heg : remote e g) (hfg : remote f g) (j : Fin 6) :
    (sixEndpointMap e f g j, 0) ∈ (concurrencePolynomial e f g).vars := by
  let U := endpointCoordinateWitness j 0
  let V := endpointCoordinateWitness j 1
  let P := extendSixEndpointTuple e f g U
  let Q := extendSixEndpointTuple e f g V
  have hagree : ∀ z, z ≠ (sixEndpointMap e f g j, 0) →
      scalarCoordinates P z = scalarCoordinates Q z := by
    apply scalarCoordinates_agree_off_X P Q (sixEndpointMap e f g j)
    · intro v hv
      exact extendSixEndpointTuple_agree e f g hef heg hfg U V j
        (fun k hk => endpointCoordinateWitness_agree j k hk 0 1) v hv
    · change (extendSixEndpointTuple e f g U (sixEndpointMap e f g j)).2 =
        (extendSixEndpointTuple e f g V (sixEndpointMap e f g j)).2
      rw [extendSixEndpointTuple_apply e f g hef heg hfg,
        extendSixEndpointTuple_apply e f g hef heg hfg]
      exact endpointCoordinateWitness_y j 0 1
  apply polynomial_variable_of_eval_ne (concurrencePolynomial e f g)
    (sixEndpointMap e f g j, 0) (scalarCoordinates P) (scalarCoordinates Q) hagree
  rw [eval_concurrencePolynomial, eval_concurrencePolynomial]
  change concurrenceDet (extendSixEndpointTuple e f g U) e f g ≠
    concurrenceDet (extendSixEndpointTuple e f g V) e f g
  rw [concurrenceDet_extendSixEndpointTuple e f g hef heg hfg,
    concurrenceDet_extendSixEndpointTuple e f g hef heg hfg]
  exact endpointCoordinateWitness_values j

theorem concurrencePolynomial_avoids (z : ScalarCoordinate n) (e f g : ZMod n)
    (he : z.1 ≠ e) (he1 : z.1 ≠ e + 1) (hf : z.1 ≠ f)
    (hf1 : z.1 ≠ f + 1) (hg : z.1 ≠ g) (hg1 : z.1 ≠ g + 1) :
    z ∉ (concurrencePolynomial e f g).vars := by
  have ht (a b c : Fin 3) :
      z ∉ (linePolynomialRow e a * linePolynomialRow f b * linePolynomialRow g c).vars :=
    polynomial_not_mem_mul
      (polynomial_not_mem_mul (linePolynomialRow_avoids z e he he1 a)
        (linePolynomialRow_avoids z f hf hf1 b))
      (linePolynomialRow_avoids z g hg hg1 c)
  rw [concurrencePolynomial_formula]
  exact polynomial_not_mem_sub
    (polynomial_not_mem_add
      (polynomial_not_mem_add
        (polynomial_not_mem_sub (polynomial_not_mem_sub (ht 0 1 2) (ht 0 2 1)) (ht 1 0 2))
        (ht 1 2 0))
      (ht 2 0 1))
    (ht 2 1 0)

theorem concurrencePolynomial_vertexSupport [Nontrivial (ZMod n)] (e f g : ZMod n)
    (hef : remote e f) (heg : remote e g) (hfg : remote f g) :
    polynomialVertexSupport (concurrencePolynomial e f g) =
      {e, e + 1, f, f + 1, g, g + 1} := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨c, hc⟩ := (mem_polynomialVertexSupport_iff _ v).mp hv
    by_contra h
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact concurrencePolynomial_avoids (v, c) e f g h.1 h.2.1 h.2.2.1 h.2.2.2.1
      h.2.2.2.2.1 h.2.2.2.2.2 hc
  · intro v hv
    obtain ⟨j, rfl⟩ := (mem_sixEndpointMap_range e f g v).mpr hv
    exact (mem_polynomialVertexSupport_iff _ _).mpr
      ⟨0, concurrencePolynomial_X_endpoint e f g hef heg hfg j⟩

end

end SM
