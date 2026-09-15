namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Exact top cancellation with fixed geometric inverse coordinates.
The explicit gap hypothesis will be discharged by the positive/full-root
negative source gap lemmas in the following two theorems. -/
theorem silent_scaled_top_eq {P : LabelledTuple n} (hP : WeakGeneric P) (g : ZMod n)
    (I : BoundaryInterval n) (U : TripleArray n R)
    (hU : ∀ t, geometricBoundaryArray (R := ℚ) P g t ≠ 0 → U t = 0) (η : R)
    (hgap : ∀ π : IntervalComposition I, 2 ≤ π.parts →
      (∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) →
      ∃ k : Fin π.parts,
        η * ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) = 1 ∧
          2 ≤ (π.part k).leaves) :
    farTransform (fun t => η * (geometricBoundaryArray P g t + U t))
      (farOnlyCoordinates (geometricBoundaryArray P g)) I =
    farTransform (fun t => η * geometricBoundaryArray P g t)
      (farOnlyCoordinates (geometricBoundaryArray P g)) I := by
  classical
  have hs : (fun t => η * (geometricBoundaryArray P g t + U t)) =
      (fun t => η * geometricBoundaryArray P g t) + (fun t => η * U t) := by
    funext t
    exact mul_add _ _ _
  rw [hs]
  apply farTransform_add_eq_of_nonunary_zero
  intro π hparts
  by_cases hz : ∀ j : Fin (π.parts - 1),
      geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0
  · obtain ⟨k, hε, hlength⟩ := hgap π hparts hz
    have hf : (∑ σ : IntervalComposition (π.part k),
        IntervalComposition.positionCutSummand
          (intervalFarCutWeight (fun t => η * geometricBoundaryArray P g t) I)
          (farOnlyCoordinates (geometricBoundaryArray P g)) σ) = 0 := by
      rw [silent_gap_positionCutSum hP g π hz k η]
      have he : (fun t => η *
          ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) *
            geometricBoundaryArray P g t) = geometricBoundaryArray P g := by
        funext t
        rw [hε, one_mul]
      rw [he]
      exact farOnly_nonleaf_E (geometricBoundaryArray P g) (π.part k) hlength
    have hp : (∏ k : Fin π.parts, ∑ σ : IntervalComposition (π.part k),
        IntervalComposition.positionCutSummand
          (intervalFarCutWeight (fun t => η * geometricBoundaryArray P g t) I)
          (farOnlyCoordinates (geometricBoundaryArray P g)) σ) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) hf
    rw [hp, mul_zero]
  · push_neg at hz
    obtain ⟨j, hj⟩ := hz
    have hu := hU (π.farTriple j) hj
    have hw : intervalFarCutWeight (fun t => η * U t) I (π.interiorPosition j) = 0 := by
      unfold intervalFarCutWeight
      rw [intervalFarValue_interior, hu, mul_zero, neg_zero, zero_mul]
    have hp : (∏ x ∈ π.cutSet.interior.val,
        intervalFarCutWeight (fun t => η * U t) I x) = 0 :=
      Finset.prod_eq_zero (π.interiorPosition_mem j) hw
    rw [hp, zero_mul]

/-- All forward top coordinates are unchanged by any simultaneous
perturbation supported on the rational geometric zero entries. -/
theorem silent_supported_forward_top (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (U : TripleArray n R)
    (hU : ∀ t, geometricBoundaryArray (R := ℚ) P g t ≠ 0 → U t = 0)
    (I : BoundaryInterval n) :
    farTransform (geometricBoundaryArray P g + U)
      (farOnlyCoordinates (geometricBoundaryArray P g)) I =
      farTransform (geometricBoundaryArray P g) (farOnlyCoordinates (geometricBoundaryArray P g)) I := by
  have hg : ∀ π : IntervalComposition I, 2 ≤ π.parts →
      (∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) →
      ∃ k : Fin π.parts,
        (1 : R) * ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) = 1 ∧
          2 ≤ (π.part k).leaves := by
    intro π hp hz
    obtain ⟨k, he, hl⟩ := silent_composition_positive_gap hn hP g π hp hz
    exact ⟨k, by simp [he], hl⟩
  have h := silent_scaled_top_eq hP g I U hU 1 hg
  have ha : (fun t => (1 : R) * (geometricBoundaryArray P g t + U t)) =
      geometricBoundaryArray P g + U := by funext t; exact one_mul _
  have hb : (fun t => (1 : R) * geometricBoundaryArray P g t) =
      geometricBoundaryArray P g := by funext t; exact one_mul _
  rw [ha, hb] at h
  exact h

/-- Reversed-far top cancellation uses the physical root interval and
the negative gap supplied there. No arbitrary-open-interval claim is made. -/
theorem silent_supported_reversed_full_top (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (U : TripleArray n R)
    (hU : ∀ t, geometricBoundaryArray (R := ℚ) P g t ≠ 0 → U t = 0) :
    farTransform (-(geometricBoundaryArray P g + U))
      (farOnlyCoordinates (geometricBoundaryArray P g)) (fullBoundaryInterval hn) =
      farTransform (-geometricBoundaryArray P g)
        (farOnlyCoordinates (geometricBoundaryArray P g)) (fullBoundaryInterval hn) := by
  have hg : ∀ π : IntervalComposition (fullBoundaryInterval hn), 2 ≤ π.parts →
      (∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) →
      ∃ k : Fin π.parts,
        (-1 : R) * ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) = 1 ∧
          2 ≤ (π.part k).leaves := by
    intro π hp hz
    obtain ⟨k, he, hl⟩ := silent_composition_full_negative_gap hn hP g π hp hz
    exact ⟨k, by simp [he], hl⟩
  have h := silent_scaled_top_eq hP g (fullBoundaryInterval hn) U hU (-1) hg
  have ha : (fun t => (-1 : R) * (geometricBoundaryArray P g t + U t)) =
      -(geometricBoundaryArray P g + U) := by funext t; exact neg_one_mul _
  have hb : (fun t => (-1 : R) * geometricBoundaryArray P g t) =
      -geometricBoundaryArray P g := by funext t; exact neg_one_mul _
  rw [ha, hb] at h
  exact h

/-- Uniqueness of the actual triangular inverse converts the fixed-child
top equations into equality of the complete inverse arrays. -/
theorem silent_supported_coordinates (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (U : TripleArray n R)
    (hU : ∀ t, geometricBoundaryArray (R := ℚ) P g t ≠ 0 → U t = 0) :
    farOnlyCoordinates (geometricBoundaryArray P g + U) =
      farOnlyCoordinates (geometricBoundaryArray P g) := by
  symm
  apply nearFar_solution_unique 0 (geometricBoundaryArray P g + U)
  funext I
  change farTransform (geometricBoundaryArray P g + U)
    (farOnlyCoordinates (geometricBoundaryArray P g)) I = boundaryUnitArray I
  rw [silent_supported_forward_top hn hP g U hU I, farOnlyCoordinates_equation]

/-- The complete reversed-far root output is unchanged as well, after
the full inverse array has been shown equal. -/
theorem silent_supported_output (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (U : TripleArray n R)
    (hU : ∀ t, geometricBoundaryArray (R := ℚ) P g t ≠ 0 → U t = 0) :
    farOnlyOutput (geometricBoundaryArray P g + U) (fullBoundaryInterval hn) =
      farOnlyOutput (geometricBoundaryArray P g) (fullBoundaryInterval hn) := by
  unfold farOnlyOutput
  rw [silent_supported_coordinates hn hP g U hU]
  exact silent_supported_reversed_full_top hn hP g U hU

end
end SM
