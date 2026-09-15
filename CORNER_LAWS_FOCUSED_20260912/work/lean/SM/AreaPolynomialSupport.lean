import SM.PolynomialVertexSupport

/-! Exact three-vertex support of the area polynomial. Dependence is established
by actual unrestricted tuples, varying a single scalar coordinate. -/

namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ}

theorem areaPolynomial_cyclic (i j k : ZMod n) :
    areaPolynomial i j k = areaPolynomial j k i := by
  dsimp [areaPolynomial]
  ring

theorem areaPolynomial_avoids (z : ScalarCoordinate n) (i j k : ZMod n)
    (hi : z.1 ≠ i) (hj : z.1 ≠ j) (hk : z.1 ≠ k) :
    z ∉ (areaPolynomial i j k).vars := by
  have hXi := coordinateX_avoids_vertex z i hi
  have hYi := coordinateY_avoids_vertex z i hi
  have hXj := coordinateX_avoids_vertex z j hj
  have hYj := coordinateY_avoids_vertex z j hj
  have hXk := coordinateX_avoids_vertex z k hk
  have hYk := coordinateY_avoids_vertex z k hk
  exact polynomial_not_mem_sub
    (polynomial_not_mem_mul (polynomial_not_mem_sub hXj hXi)
      (polynomial_not_mem_sub hYk hYi))
    (polynomial_not_mem_mul (polynomial_not_mem_sub hYj hYi)
      (polynomial_not_mem_sub hXk hXi))

def areaVertexWitness (j k : ZMod n) (t : ℝ) : LabelledTuple n := fun v =>
  if v = k then (0, 1) else if v = j then (t, 0) else (0, 0)

theorem areaVertexWitness_value (i j k : ZMod n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (t : ℝ) :
    eval (scalarCoordinates (areaVertexWitness j k t)) (areaPolynomial i j k) = t := by
  rw [eval_areaPolynomial]
  simp [areaVertexWitness, det, hij, hik, hjk]

theorem areaVertexWitness_agree (j k : ZMod n) (s t : ℝ)
    (z : ScalarCoordinate n) (hz : z ≠ (j, 0)) :
    scalarCoordinates (areaVertexWitness j k s) z =
      scalarCoordinates (areaVertexWitness j k t) z := by
  obtain ⟨v, c⟩ := z
  fin_cases c
  · have hv : v ≠ j := by
      intro h
      subst v
      exact hz rfl
    simp [scalarCoordinates, areaVertexWitness, hv]
  · simp [scalarCoordinates, areaVertexWitness]
    split_ifs <;> rfl

theorem areaPolynomial_X_middle (i j k : ZMod n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (j, 0) ∈ (areaPolynomial i j k).vars := by
  apply polynomial_variable_of_eval_ne (areaPolynomial i j k) (j, 0)
    (scalarCoordinates (areaVertexWitness j k 0))
    (scalarCoordinates (areaVertexWitness j k 1))
    (areaVertexWitness_agree j k 0 1)
  rw [areaVertexWitness_value i j k hij hik hjk,
    areaVertexWitness_value i j k hij hik hjk]
  norm_num

theorem areaPolynomial_X_first (i j k : ZMod n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (i, 0) ∈ (areaPolynomial i j k).vars := by
  have h := areaPolynomial_X_middle k i j hik.symm hjk.symm hij
  rwa [areaPolynomial_cyclic k i j] at h

theorem areaPolynomial_X_last (i j k : ZMod n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (k, 0) ∈ (areaPolynomial i j k).vars := by
  have h := areaPolynomial_X_middle j k i hjk hij.symm hik.symm
  rwa [← areaPolynomial_cyclic i j k] at h

theorem areaPolynomial_vertexSupport (i j k : ZMod n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    polynomialVertexSupport (areaPolynomial i j k) = {i, j, k} := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨c, hc⟩ := (mem_polynomialVertexSupport_iff _ v).mp hv
    by_contra h
    have hi : v ≠ i := by intro hvi; exact h (by simp [hvi])
    have hj : v ≠ j := by intro hvj; exact h (by simp [hvj])
    have hk : v ≠ k := by intro hvk; exact h (by simp [hvk])
    exact areaPolynomial_avoids (v, c) i j k hi hj hk hc
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    apply (mem_polynomialVertexSupport_iff _ v).mpr
    rcases hv with hv | hv | hv <;> subst v
    · exact ⟨0, areaPolynomial_X_first i j k hij hik hjk⟩
    · exact ⟨0, areaPolynomial_X_middle i j k hij hik hjk⟩
    · exact ⟨0, areaPolynomial_X_last i j k hij hik hjk⟩

theorem areaPolynomial_not_associated_of_support_ne (i j k a b c : ZMod n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : ({i, j, k} : Finset (ZMod n)) ≠ {a, b, c}) :
    ¬ Associated (areaPolynomial i j k) (areaPolynomial a b c) := by
  intro h
  apply hs
  have he := polynomialVertexSupport_eq_of_associated
    (areaPolynomial_ne_zero i j k hij hik hjk)
    (areaPolynomial_ne_zero a b c hab hac hbc) h
  simpa only [areaPolynomial_vertexSupport i j k hij hik hjk,
    areaPolynomial_vertexSupport a b c hab hac hbc] using he

end

end SM
