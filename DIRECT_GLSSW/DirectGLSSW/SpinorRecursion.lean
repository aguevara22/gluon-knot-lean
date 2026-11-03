import DirectGLSSW.SpinorVertices

/-!
# Independent published preamplitude and amplitude recursion

The preamplitude is defined from the spinor ratio vertices with at least
three branches at each ordinary node. Its recursive calls use an explicit
interval-length guard, which the recurrence theorem removes on every valid
cut. It is not defined through the rational-array ordinary current.

The amplitude is the negative finite sum of ordinary-minus-marked vertex
products, including the unary partition. Its equality with the note's
marked current is proved under interval noncollinearity, with the exact
one-edge source correction retained. Cyclic root independence is not proved
or assumed in this representation bridge.
-/

namespace DirectGLSSW
open scoped BigOperators

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Interval noncollinearity is inherited by every contained subinterval. -/
theorem intervalNoncollinear_subinterval (q : ℕ → PlanarPoint K)
    {i j a b : ℕ} (hq : IntervalNoncollinear q i j)
    (hia : i ≤ a) (hbj : b ≤ j) : IntervalNoncollinear q a b := by
  intro u v w hau huv hvw hwb
  exact hq u v w (le_trans hia hau) huv hvw (le_trans hwb hbj)

/-- The published ordinary recursion: singleton source one, and a negative
sum over vertices with at least three branches. The guard is solely for
well-founded implementation; it is always true on contributing branches. -/
noncomputable def spinorPreAmplitude (q : ℕ → PlanarPoint K) (i j : ℕ) : ℚ :=
  source i j -
    ∑ S ∈ (Finset.Ioo i j).powerset.filter (fun S => 2 ≤ S.card),
      spinorOrdinaryVertex q i j S *
        branchProduct
          (fun a b => if _h : b - a < j - i then spinorPreAmplitude q a b else 0)
          (cutVertices i j S)
termination_by j - i

omit [IsStrictOrderedRing K] in
/-- The implemented preamplitude obeys the unguarded published recurrence
on every positive interval, without a noncollinearity assumption. -/
theorem spinorPreAmplitude_recurrence (q : ℕ → PlanarPoint K)
    {i j : ℕ} (hij : i < j) :
    spinorPreAmplitude q i j = source i j -
      ∑ S ∈ (Finset.Ioo i j).powerset.filter (fun S => 2 ≤ S.card),
        spinorOrdinaryVertex q i j S *
          branchProduct (spinorPreAmplitude q) (cutVertices i j S) := by
  rw [spinorPreAmplitude]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  obtain ⟨hsub, hcard⟩ := Finset.mem_filter.mp hS
  have hsne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hs : S ⊆ Finset.Ioo i j := Finset.mem_powerset.mp hsub
  congr 1
  unfold branchProduct
  apply congrArg List.prod
  apply List.map_congr_left
  rintro ⟨a, b⟩ hab
  have hb := cutVertices_branch_bounds hij hs hsne hab
  simp only [dif_pos hb.2.2.2]

/-- The independently recursive preamplitude agrees with the source's
unique ordinary current. Noncollinearity is inherited by each child. -/
theorem spinorPreAmplitude_eq_ordinaryCurrent (q : ℕ → PlanarPoint K)
    {i j : ℕ} (hij : i < j) (hq : IntervalNoncollinear q i j) :
    spinorPreAmplitude q i j =
      ordinaryCurrent (polygonSignArray q) (polygonSignArray q) i j := by
  generalize hn : j - i = n
  induction n using Nat.strong_induction_on generalizing i j with
  | h n ih =>
      rw [spinorPreAmplitude_recurrence q hij,
        ordinaryCurrent_spinor_recurrence q hij hq]
      congr 1
      apply Finset.sum_congr rfl
      intro S hS
      obtain ⟨hsub, hcard⟩ := Finset.mem_filter.mp hS
      have hsne : S.Nonempty := Finset.card_pos.mp (by omega)
      have hs : S ⊆ Finset.Ioo i j := Finset.mem_powerset.mp hsub
      congr 1
      unfold branchProduct
      apply congrArg List.prod
      apply List.map_congr_left
      rintro ⟨a, b⟩ hab
      obtain ⟨hia, hablt, hbj, hlt⟩ := cutVertices_branch_bounds hij hs hsne hab
      exact ih (b - a) (by omega) hablt
        (intervalNoncollinear_subinterval q hq hia hbj) rfl

/-- A singleton boundary word has the published preamplitude one. -/
theorem spinorPreAmplitude_adjacent (q : ℕ → PlanarPoint K) (i : ℕ) :
    spinorPreAmplitude q i (i + 1) = 1 := by
  have hq : IntervalNoncollinear q i (i + 1) := by
    intro a b c hia hab hbc hci
    omega
  rw [spinorPreAmplitude_eq_ordinaryCurrent q (by omega) hq,
    ordinaryCurrent_adjacent]

omit [IsStrictOrderedRing K] in
/-- A two-letter boundary word has the published preamplitude zero.
No geometric assumption is needed because no three-branch partition exists. -/
theorem spinorPreAmplitude_two (q : ℕ → PlanarPoint K) (i : ℕ) :
    spinorPreAmplitude q i (i + 2) = 0 := by
  have he : Finset.Ioo i (i + 2) = {i + 1} := by
    ext k
    simp only [Finset.mem_Ioo, Finset.mem_singleton]
    omega
  have hf : (({i + 1} : Finset ℕ).powerset.filter (fun S => 2 ≤ S.card)) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro S hS
    obtain ⟨hsub, hcard⟩ := Finset.mem_filter.mp hS
    have hle := Finset.card_le_card (Finset.mem_powerset.mp hsub)
    simp only [Finset.card_singleton] at hle
    omega
  rw [spinorPreAmplitude_recurrence q (by omega), he, hf]
  simp [source]

/-- The original amplitude formula: the negative sum of ordinary-minus-
marked vertices, evaluated on the independently defined preamplitudes.
All partitions, including the one-branch partition, are retained. -/
noncomputable def spinorAmplitude (q : ℕ → PlanarPoint K) (i j : ℕ) : ℚ :=
  -(∑ S ∈ (Finset.Ioo i j).powerset,
    (spinorOrdinaryVertex q i j S - spinorMarkedVertex q i j S) *
      branchProduct (spinorPreAmplitude q) (cutVertices i j S))

omit [IsStrictOrderedRing K] in
/-- The negative vertex difference is exactly marked minus ordinary. -/
theorem spinorAmplitude_eq_vertexDifference (q : ℕ → PlanarPoint K) (i j : ℕ) :
    spinorAmplitude q i j =
      spinorVertexDifference q (spinorPreAmplitude q) i j := by
  unfold spinorAmplitude spinorVertexDifference spinorMarkedPhi spinorOrdinaryPhi
  simp only [sub_mul, Finset.sum_sub_distrib, neg_sub]

/-- Every child of a valid cut uses the same preamplitude and current,
including the full parent interval at a unary root. -/
theorem branchProduct_spinorPreAmplitude_eq (q : ℕ → PlanarPoint K)
    {i j : ℕ} {S : Finset ℕ} (hij : i < j)
    (hq : IntervalNoncollinear q i j) (hS : S ⊆ Finset.Ioo i j) :
    branchProduct (spinorPreAmplitude q) (cutVertices i j S) =
      branchProduct (ordinaryCurrent (polygonSignArray q) (polygonSignArray q))
        (cutVertices i j S) := by
  by_cases hsne : S.Nonempty
  · unfold branchProduct
    apply congrArg List.prod
    apply List.map_congr_left
    rintro ⟨a, b⟩ hab
    obtain ⟨hia, hablt, hbj, _⟩ := cutVertices_branch_bounds hij hS hsne hab
    exact spinorPreAmplitude_eq_ordinaryCurrent q hablt
      (intervalNoncollinear_subinterval q hq hia hbj)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsne
    simpa [he, cutVertices, branchProduct] using
      spinorPreAmplitude_eq_ordinaryCurrent q hij hq

/-- The fully independent published recursion equals the marked current
with its exact elementary-interval source correction. -/
theorem spinorAmplitude_eq_marked_sub_source (q : ℕ → PlanarPoint K)
    {i j : ℕ} (hij : i < j) (hq : IntervalNoncollinear q i j) :
    spinorAmplitude q i j =
      markedAmplitude (polygonSignArray q) (polygonSignArray q) i j - source i j := by
  rw [spinorAmplitude_eq_vertexDifference]
  have hm : spinorVertexDifference q (spinorPreAmplitude q) i j =
      spinorVertexDifference q
        (ordinaryCurrent (polygonSignArray q) (polygonSignArray q)) i j := by
    unfold spinorVertexDifference spinorMarkedPhi spinorOrdinaryPhi
    congr 1 <;> apply Finset.sum_congr rfl <;> intro S hS <;>
      rw [branchProduct_spinorPreAmplitude_eq q hij hq (Finset.mem_powerset.mp hS)]
  rw [hm, spinorVertexDifference_eq_marked_sub_source q hij hq]

/-- On a word with at least two elementary edges, the independent GLSSW
amplitude equals the note's marked current without a source correction. -/
theorem spinorAmplitude_eq_marked (q : ℕ → PlanarPoint K)
    {i j : ℕ} (hij : i + 1 < j) (hq : IntervalNoncollinear q i j) :
    spinorAmplitude q i j =
      markedAmplitude (polygonSignArray q) (polygonSignArray q) i j := by
  rw [spinorAmplitude_eq_marked_sub_source q (by omega) hq]
  have hne : j ≠ i + 1 := by omega
  simp only [source, if_neg hne, sub_zero]

end DirectGLSSW
