import SM.PolynomialAvoidance

/-! Density of the full all-triple G1 locus. Every determinant has its own
explicit coordinate witness and an actual polynomial on each affine family. -/

namespace SM

open Set Polynomial

variable {n : ℕ}

noncomputable def areaLinePolynomial (P Q : LabelledTuple n) (i j k : ZMod n) : ℝ[X] :=
  (lineXPolynomial P Q j - lineXPolynomial P Q i) *
      (lineYPolynomial P Q k - lineYPolynomial P Q i) -
    (lineYPolynomial P Q j - lineYPolynomial P Q i) *
      (lineXPolynomial P Q k - lineXPolynomial P Q i)

theorem area_polynomial_on_lines (i j k : ZMod n) :
    PolynomialOnTupleLines (fun P => det (P j - P i) (P k - P i)) := by
  intro P Q
  refine ⟨areaLinePolynomial P Q i j k, ?_⟩
  intro t
  simp [areaLinePolynomial, det]

def areaWitness (j k : ZMod n) : LabelledTuple n := fun i =>
  if i = j then (1, 0) else if i = k then (0, 1) else (0, 0)

theorem areaWitness_value (i j k : ZMod n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    det (areaWitness j k j - areaWitness j k i)
      (areaWitness j k k - areaWitness j k i) = 1 := by
  norm_num [areaWitness, det, hij, hik, hjk.symm]

theorem area_nonzero_witness (i j k : ZMod n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ P : LabelledTuple n, det (P j - P i) (P k - P i) ≠ 0 := by
  refine ⟨areaWitness j k, ?_⟩
  rw [areaWitness_value i j k hij hjk hik]
  norm_num

abbrev DistinctVertexTriple (n : ℕ) :=
  {v : ZMod n × ZMod n × ZMod n // v.1 ≠ v.2.1 ∧ v.2.1 ≠ v.2.2 ∧ v.1 ≠ v.2.2}

theorem dense_G1 [NeZero n] : Dense {P : LabelledTuple n | G1 P} := by
  let f : DistinctVertexTriple n → LabelledTuple n → ℝ := fun v P =>
    det (P v.val.2.1 - P v.val.1) (P v.val.2.2 - P v.val.1)
  have hd : Dense {P | ∀ v, f v P ≠ 0} := dense_finite_nonzero_family f
    (fun v => continuous_area v.val.1 v.val.2.1 v.val.2.2)
    (fun v => area_polynomial_on_lines v.val.1 v.val.2.1 v.val.2.2)
    (fun v => area_nonzero_witness v.val.1 v.val.2.1 v.val.2.2
      v.property.1 v.property.2.1 v.property.2.2)
  apply hd.mono
  intro P hP i j k hij hjk hik
  exact sign_ne_zero.mpr (hP ⟨(i, j, k), hij, hjk, hik⟩)

end SM
