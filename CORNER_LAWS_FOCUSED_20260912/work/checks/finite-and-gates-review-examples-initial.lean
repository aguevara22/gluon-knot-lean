namespace FiniteAndGatesIndependentReview
open SM

-- The canonical typeclass domain is the unchanged source composition type.
theorem every_composition_enumerated {n : ℕ} [NeZero n] (I : BoundaryInterval n) :
    (∀ π : IntervalComposition I, π ∈ (Finset.univ : Finset (IntervalComposition I))) ∧
      0 < Fintype.card (IntervalComposition I) := by
  exact ⟨fun _ => Finset.mem_univ _, Fintype.card_pos_iff.mpr ⟨IntervalComposition.single I⟩⟩

-- Actual child intervals have positive and strictly smaller leaf counts.
theorem all_source_children_decrease {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (hp : 2 ≤ π.parts) :
    ∀ k : Fin π.parts, 0 < (π.part k).leaves ∧ (π.part k).leaves < I.leaves :=
  fun k => ⟨(π.part k).leaves_pos, π.part_leaves_lt hp k⟩

-- The exact source recursive-child relation is well founded under that measure.
theorem source_child_relation_wellFounded {n : ℕ} [NeZero n] :
    WellFounded (fun J I : BoundaryInterval n =>
      ∃ π : IntervalComposition I, 2 ≤ π.parts ∧ ∃ k : Fin π.parts, J = π.part k) := by
  apply (measure BoundaryInterval.leaves).wf.mono
  intro J I h
  obtain ⟨π, hp, k, rfl⟩ := h
  exact π.part_leaves_lt hp k

-- The excluded one-part case has equal measure, not a false strict decrease.
theorem singleton_measure_equal {n : ℕ} [NeZero n] (I : BoundaryInterval n) :
    ((IntervalComposition.single I).part ⟨0, by decide⟩).leaves = I.leaves := by
  cases I
  rfl

-- Every source interior cut1<=k<=s-1 has exactly an indexing position k-1.
theorem interior_cut_exhaustion {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (k : ℕ) (hk : 0 < k) (hks : k < π.parts) :
    ∃ j : Fin (π.parts - 1), j.val + 1 = k := by
  exact ⟨⟨k - 1, by omega⟩, by simp; omega⟩

-- The nonzero SignType step is the source Real step on every actual gate argument.
theorem real_step_interpretation (s : SignType) (hs : s ≠ 0) :
    (signTheta s hs : ℝ) = (if 0 < (s : ℝ) then 1 else 0) := by
  cases s <;> first | exact (hs rfl).elim | norm_num [signTheta]

-- Both half-formulas are exact rational/real identities, not rounded integer division.
theorem real_gate_identities (d h : SignType) (hd : d ≠ 0) (hh : h ≠ 0) :
    (ordinaryGate d h hd hh : ℝ) = ((d : ℝ) - (h : ℝ)) / 2 ∧
    (rootGate d h hd hh : ℝ) = ((d : ℝ) + (h : ℝ)) / 2 := by
  cases d <;> cases h <;>
    first | exact (hd rfl).elim | exact (hh rfl).elim |
      norm_num [ordinaryGate, rootGate, signTheta]

-- Embedding the actual complete weights gives the product of the source halves.
theorem real_weight_identities {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    (π.ordinaryWeight P hP g : ℝ) = ∏ k : Fin (π.parts - 1),
      ((π.nearSign P g k : ℝ) - (π.farSign P g k : ℝ)) / 2 ∧
    (π.rootWeight P hP g : ℝ) = ∏ k : Fin (π.parts - 1),
      ((π.nearSign P g k : ℝ) + (π.farSign P g k : ℝ)) / 2 := by
  constructor
  · rw [IntervalComposition.ordinaryWeight, Int.cast_prod]
    apply Finset.prod_congr rfl
    intro k _
    exact (real_gate_identities _ _ (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)).1
  · rw [IntervalComposition.rootWeight, Int.cast_prod]
    apply Finset.prod_congr rfl
    intro k _
    exact (real_gate_identities _ _ (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)).2

-- Empty products and the arbitrary two-part source composition need only G1.
theorem source_small_part_cases {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    (π.parts = 1 → π.ordinaryWeight P hP g = 1 ∧ π.rootWeight P hP g = 1) ∧
    (π.parts = 2 → π.ordinaryWeight P hP g = 0) :=
  ⟨π.one_part_weights P hP g, π.binary_ordinaryWeight_zero P hP g⟩

-- Independent check of the representative-equivalence obligation.
theorem gate_signs_shift {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (P : LabelledTuple n) (g a : ZMod n)
    (k : Fin (π.parts - 1)) :
    π.nearSign (shift a P) (g - a) k = π.nearSign P g k ∧
      π.farSign (shift a P) (g - a) k = π.farSign P g k := by
  have hb : ∀ j : Fin n, boundaryIndex (g - a) j + a = boundaryIndex g j := by
    intro j
    unfold boundaryIndex
    ring
  constructor
  · simp only [IntervalComposition.nearSign, chi_shift, hb]
  · simp only [IntervalComposition.farSign, chi_shift, hb]

-- All factors and weights preserve the pair(polygon,root), including G1 transport.
theorem gate_weights_shift {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) :
    π.ordinaryWeight (shift a P) (g1_shift_forward a hP) (g - a) = π.ordinaryWeight P hP g ∧
    π.rootWeight (shift a P) (g1_shift_forward a hP) (g - a) = π.rootWeight P hP g := by
  constructor
  · unfold IntervalComposition.ordinaryWeight
    apply Finset.prod_congr rfl
    intro k _
    rcases gate_signs_shift I π P g a k with ⟨hd, hh⟩
    simp only [hd, hh]
  · unfold IntervalComposition.rootWeight
    apply Finset.prod_congr rfl
    intro k _
    rcases gate_signs_shift I π P g a k with ⟨hd, hh⟩
    simp only [hd, hh]

end FiniteAndGatesIndependentReview
