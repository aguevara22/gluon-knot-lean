namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R]

/-- Read the far entry with fixed outer endpoints at a physical position.
The value outside that open interval is irrelevant to its compositions. -/
def intervalFarValue (H : TripleArray n R) (I : BoundaryInterval n) (u : Fin n) : R := by
  classical
  exact if h : I.left < u ∧ u < I.right then H ⟨I.left, u, I.right, h.1, h.2⟩ else 0

theorem intervalFarValue_interior (H : TripleArray n R) {I : BoundaryInterval n}
    (π : IntervalComposition I) (j : Fin (π.parts - 1)) :
    intervalFarValue H I (π.interiorPosition j) = H (π.farTriple j) := by
  have hb : I.left < π.interiorPosition j ∧ π.interiorPosition j < I.right :=
    ⟨(π.farTriple j).lower_middle, (π.farTriple j).middle_upper⟩
  unfold intervalFarValue
  rw [dif_pos hb]
  rfl

theorem intervalFarValue_map {S : Type*} [CommRing S] (f : R →+* S)
    (H : TripleArray n R) (I : BoundaryInterval n) (u : Fin n) :
    f (intervalFarValue H I u) = intervalFarValue (fun t => f (H t)) I u := by
  by_cases h : I.left < u ∧ u < I.right <;> simp [intervalFarValue, h]

variable [Invertible (2 : R)]

def intervalFarCutWeight (H : TripleArray n R) (I : BoundaryInterval n) (u : Fin n) : R :=
  -intervalFarValue H I u * ⅟ (2 : R)

theorem intervalFarCutWeight_add (H U : TripleArray n R) (I : BoundaryInterval n) :
    intervalFarCutWeight (H + U) I = intervalFarCutWeight U I + intervalFarCutWeight H I := by
  funext u
  by_cases h : I.left < u ∧ u < I.right
  · simp only [intervalFarCutWeight, intervalFarValue, dif_pos h, Pi.add_apply]
    ring
  · simp [intervalFarCutWeight, intervalFarValue, h]

/-- Fixed-endpoint positional weights reproduce each complete actual
far-transform summand and its unchanged actual child-coordinate product. -/
theorem positionCutSummand_intervalFar (H : TripleArray n R) (X : IntervalArray n R)
    {I : BoundaryInterval n} (π : IntervalComposition I) :
    IntervalComposition.positionCutSummand (intervalFarCutWeight H I) X π =
      π.nearFarWeight 0 H * ∏ j : Fin π.parts, X (π.part j) := by
  unfold IntervalComposition.positionCutSummand IntervalComposition.nearFarWeight
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [intervalFarCutWeight, intervalFarValue_interior, Pi.zero_apply, zero_sub]

theorem farTransform_positionCutSum (H : TripleArray n R) (X : IntervalArray n R)
    (I : BoundaryInterval n) :
    farTransform H X I = ∑ π : IntervalComposition I,
      IntervalComposition.positionCutSummand (intervalFarCutWeight H I) X π := by
  unfold farTransform nearFarTransform
  apply Finset.sum_congr rfl
  intro π _
  exact (positionCutSummand_intervalFar H X π).symm

/-- Exact polynomial expansion of the top coordinate around H, with all
child coordinates fixed to X. The outer cuts carry U and independent gap
compositions carry H read using the original outer endpoints. This holds
for arbitrary arrays in the full ring, with no realizability restriction. -/
theorem farTransform_add_decomposition (H U : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    farTransform (H + U) X I =
      ∑ π : IntervalComposition I,
        (∏ x ∈ π.cutSet.interior.val, intervalFarCutWeight U I x) *
          ∏ k : Fin π.parts, ∑ σ : IntervalComposition (π.part k),
            IntervalComposition.positionCutSummand (intervalFarCutWeight H I) X σ := by
  rw [farTransform_positionCutSum, intervalFarCutWeight_add]
  exact positionCutSum_add_decomposition (intervalFarCutWeight U I)
    (intervalFarCutWeight H I) X I

end
end SM
