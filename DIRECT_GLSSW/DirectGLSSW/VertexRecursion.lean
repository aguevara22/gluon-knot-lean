import DirectGLSSW.CurrentFidelity

/-!
# Array specialization of the ordinary-vertex and marked-root conventions

Source: `ep:linear-gates`, `ep:Phi`, `ep:tree-recursion`; the GLSSW paper's
version 1, Section I.2, equations (18)--(22), as recorded in
`docs/MARKED_TREE_PROOF_DESIGN.md`.

At D = H the binary ordinary gate vanishes, so the ordinary recurrence
can retain only vertices with at least three branches. The difference of
the marked and ordinary vertex-product sums equals the marked output
after subtracting the exact source term. This is a rational-array result;
no identification with a spinor convention or physical amplitude is made.

These declarations are provisional pending independent fidelity review.
-/

namespace DirectGLSSW
open scoped BigOperators

/-- A single cut makes a binary ordinary vertex; its sole gate is zero
when the near and far arrays agree. -/
theorem gateProduct_self_singleton (H : TripleArray) (i k j : ℕ) :
    gateProduct H H i j (cutVertices i j {k}) = 0 := by
  simp [gateProduct, cutVertices]

/-- Binary ordinary contributions vanish independently of their children. -/
theorem cutContribution_self_singleton (H : TripleArray) (X : IntervalArray)
    (i k j : ℕ) : cutContribution H H X i j {k} = 0 := by
  unfold cutContribution
  rw [gateProduct_self_singleton, zero_mul]

/-- At equal near and far arrays, removing all binary vertices leaves the
ordinary nonunary sum unchanged. Two or more cuts mean three or more branches. -/
theorem nonUnary_self_eq_sum_card_ge_two (H : TripleArray) (X : IntervalArray)
    (i j : ℕ) :
    nonUnary H H X i j =
      ∑ S ∈ (Finset.Ioo i j).powerset.filter (fun S => 2 ≤ S.card),
        cutContribution H H X i j S := by
  unfold nonUnary
  symm
  apply Finset.sum_subset
  · intro S hS
    obtain ⟨hsub, hcard⟩ := Finset.mem_filter.mp hS
    apply Finset.mem_erase.mpr
    refine ⟨?_, hsub⟩
    intro hzero
    simp only [hzero, Finset.card_empty] at hcard
    omega
  · intro S hS hnot
    obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hS
    have hcard : ¬2 ≤ S.card := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨hsub, h⟩)
    have hpos : 0 < S.card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    obtain ⟨k, rfl⟩ := Finset.card_eq_one.mp (show S.card = 1 by omega)
    exact cutContribution_self_singleton H X i k j

/-- The concrete ordinary current at D = H satisfies the recurrence with
at least three branches at every contributing ordinary vertex. -/
theorem ordinaryCurrent_self_recurrence (H : TripleArray) {i j : ℕ}
    (hij : i < j) :
    ordinaryCurrent H H i j = source i j -
      ∑ S ∈ (Finset.Ioo i j).powerset.filter (fun S => 2 ≤ S.card),
        cutContribution H H (ordinaryCurrent H H) i j S := by
  rw [ordinaryCurrent_recurrence H H hij, nonUnary_self_eq_sum_card_ge_two]

/-- The two-edge ordinary base vanishes at equal near and far arrays. -/
theorem ordinaryCurrent_self_two (H : TripleArray) (i : ℕ) :
    ordinaryCurrent H H i (i + 2) = 0 := by
  rw [ordinaryCurrent_two]
  simp

/-- The two vertex-product sums, evaluated on the actual ordinary current
at equal near and far arrays. The marked root uses D + H and the ordinary
root uses D - H through the existing Phi definition. -/
def vertexDifferenceAmplitude (H : TripleArray) (i j : ℕ) : ℚ :=
  phi H (fun a b c => -H a b c) (ordinaryCurrent H H) i j -
    phi H H (ordinaryCurrent H H) i j

/-- The exact comparison retains the elementary-interval source correction. -/
theorem vertexDifferenceAmplitude_eq_marked_sub_source (H : TripleArray)
    {i j : ℕ} (hij : i < j) :
    vertexDifferenceAmplitude H i j = markedAmplitude H H i j - source i j := by
  unfold vertexDifferenceAmplitude markedAmplitude
  rw [ordinaryCurrent_phi H H hij]

/-- On intervals with at least two elementary edges the source vanishes, and the two
vertex-product expression equals the marked array output. -/
theorem vertexDifferenceAmplitude_eq_marked (H : TripleArray) {i j : ℕ}
    (hij : i + 1 < j) :
    vertexDifferenceAmplitude H i j = markedAmplitude H H i j := by
  rw [vertexDifferenceAmplitude_eq_marked_sub_source H (by omega)]
  have hne : j ≠ i + 1 := by omega
  simp only [source, if_neg hne, sub_zero]

/-- The same replacement on an elementary interval has a unit correction. -/
theorem vertexDifferenceAmplitude_adjacent_correction (H : TripleArray) (i : ℕ) :
    vertexDifferenceAmplitude H i (i + 1) = markedAmplitude H H i (i + 1) - 1 := by
  rw [vertexDifferenceAmplitude_eq_marked_sub_source H (by omega)]
  simp [source]

end DirectGLSSW
