namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R]

/-- Scaling a far array scales its fixed-endpoint positional value, also
outside the interval where both values are defined to be zero. -/
theorem intervalFarValue_left_mul (η : R) (H : TripleArray n R)
    (I : BoundaryInterval n) (u : Fin n) :
    intervalFarValue (fun t => η * H t) I u = η * intervalFarValue H I u := by
  by_cases h : I.left < u ∧ u < I.right <;> simp [intervalFarValue, h]

/-- Every actual interior cut of every actual selected gap has the source
outer-to-gap far-array identity. All line coordinates and nonzero endpoint
differences are derived from the actual rational silent top cuts and WeakGeneric. -/
theorem silent_gap_intervalFarValue {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {I : BoundaryInterval n} (π : IntervalComposition I)
    (hzero : ∀ j : Fin (π.parts - 1),
      geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0)
    (k : Fin π.parts) (σ : IntervalComposition (π.part k)) (j : Fin (σ.parts - 1)) :
    intervalFarValue (geometricBoundaryArray (R := R) P g) I (σ.interiorPosition j) =
      ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) *
        geometricBoundaryArray P g (σ.farTriple j) := by
  have hl : π.cut k.castSucc < σ.interiorPosition j := (σ.farTriple j).lower_middle
  have hr : σ.interiorPosition j < π.cut k.succ := (σ.farTriple j).middle_upper
  have hp := π.part_bounds k
  have hb : I.left < σ.interiorPosition j ∧ σ.interiorPosition j < I.right :=
    ⟨lt_of_le_of_lt hp.1 hl, lt_of_lt_of_le hr hp.2⟩
  have h := weak_selected_gap_far_array_of_collinear (R := R) hP g π.parts_pos
    π.cut π.strict (silent_composition_cuts_collinear P g π hzero)
    k (σ.interiorPosition j) hl hr
  have hout : selectedOuterCutTriple π.cut π.strict k (σ.interiorPosition j) hl hr =
      (⟨I.left, σ.interiorPosition j, I.right, hb.1, hb.2⟩ : IncreasingBoundaryTriple n) := by
    apply IncreasingBoundaryTriple.eq_of_entries
    · exact π.first
    · rfl
    · exact π.last
  have hgap : selectedGapCutTriple π.cut k (σ.interiorPosition j) hl hr = σ.farTriple j := by
    apply IncreasingBoundaryTriple.eq_of_entries <;> rfl
  rw [hout, hgap] at h
  unfold intervalFarValue
  rw [dif_pos hb]
  exact h

variable [Invertible (2 : R)]

/-- The complete scalar cut weight, including its negative sign and half,
uses the same source epsilon and the actual inner far triple. Zero far
entries are allowed and are never divided out. -/
theorem silent_gap_intervalFarCutWeight {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {I : BoundaryInterval n} (π : IntervalComposition I)
    (hzero : ∀ j : Fin (π.parts - 1),
      geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0)
    (k : Fin π.parts) (σ : IntervalComposition (π.part k)) (j : Fin (σ.parts - 1)) (η : R) :
    intervalFarCutWeight (fun t => η * geometricBoundaryArray P g t) I (σ.interiorPosition j) =
      -(η * ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) *
        geometricBoundaryArray P g (σ.farTriple j)) * ⅟ (2 : R) := by
  unfold intervalFarCutWeight
  rw [intervalFarValue_left_mul, silent_gap_intervalFarValue hP g π hzero k σ j]
  ring

/-- All inner cut factors and all actual child coordinates agree termwise.
Unary inner compositions retain both their empty cut product and sole child. -/
theorem silent_gap_positionCutSummand {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {I : BoundaryInterval n} (π : IntervalComposition I)
    (hzero : ∀ j : Fin (π.parts - 1),
      geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0)
    (k : Fin π.parts) (σ : IntervalComposition (π.part k))
    (η : R) (X : IntervalArray n R) :
    IntervalComposition.positionCutSummand
        (intervalFarCutWeight (fun t => η * geometricBoundaryArray P g t) I) X σ =
      σ.nearFarWeight 0
        (fun t => η * ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) *
          geometricBoundaryArray P g t) * ∏ j : Fin σ.parts, X (σ.part j) := by
  unfold IntervalComposition.positionCutSummand IntervalComposition.nearFarWeight
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [Pi.zero_apply, zero_sub]
  exact silent_gap_intervalFarCutWeight hP g π hzero k σ j η

/-- Every gap sum in the positional top decomposition is exactly the
geometric far transform with the source's eta-times-epsilon multiplier.
Every raw inner composition is retained, including a one-leaf gap and
compositions containing further silent cuts with zero factors. -/
theorem silent_gap_positionCutSum {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {I : BoundaryInterval n} (π : IntervalComposition I)
    (hzero : ∀ j : Fin (π.parts - 1),
      geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0)
    (k : Fin π.parts) (η : R) (X : IntervalArray n R) :
    (∑ σ : IntervalComposition (π.part k),
      IntervalComposition.positionCutSummand
        (intervalFarCutWeight (fun t => η * geometricBoundaryArray P g t) I) X σ) =
      farTransform
        (fun t => η * ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) *
          geometricBoundaryArray P g t) X (π.part k) := by
  unfold farTransform nearFarTransform
  apply Finset.sum_congr rfl
  intro σ _
  exact silent_gap_positionCutSummand hP g π hzero k σ η X

end
end SM
