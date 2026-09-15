namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Complete composition sum with scalar weights at actual interior cut
positions and coordinates at actual child intervals, including the unary term. -/
def cutWeightedSum (f : Fin n → R) (X : IntervalArray n R) (I : BoundaryInterval n) : R :=
  ∑ π : IntervalComposition I,
    (∏ k : Fin (π.parts - 1), f (π.interiorPosition k)) *
      ∏ k : Fin π.parts, X (π.part k)

/-- If each cut scalar is the actual far gate, the weighted sum is the
entire source transform on that interval. -/
theorem cutWeightedSum_eq_farTransform (f : Fin n → R) (H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n)
    (h : ∀ π : IntervalComposition I, ∀ k : Fin (π.parts - 1),
      f (π.interiorPosition k) = -H (π.farTriple k) * ⅟ (2 : R)) :
    cutWeightedSum f X I = farTransform H X I := by
  unfold cutWeightedSum farTransform nearFarTransform
  apply Finset.sum_congr rfl
  intro π _
  rw [π.nearFarWeight_far_only]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  exact h π k

namespace IncreasingBoundaryTriple

/-- Evaluate a far gate at fixed critical endpoints and a varying physical
middle position. The value outside the open span is0; all sampled positions
are proved strictly inside before the evaluation rule is used. -/
def fixedFarGate (t : IncreasingBoundaryTriple n) (H : TripleArray n R) (x : Fin n) : R :=
  if hx : t.lower < x ∧ x < t.upper then
    -H ⟨t.lower, x, t.upper, hx.1, hx.2⟩ * ⅟ (2 : R)
  else 0

theorem fixedFarGate_at_interior (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (π : IntervalComposition t.spanInterval) (k : Fin (π.parts - 1)) :
    t.fixedFarGate H (π.interiorPosition k) = -H (π.farTriple k) * ⅟ (2 : R) := by
  have h : t.lower < π.interiorPosition k ∧ π.interiorPosition k < t.upper :=
    ⟨(π.farTriple k).lower_middle, (π.farTriple k).middle_upper⟩
  rw [fixedFarGate, dif_pos h]
  rfl

theorem fixedFarGate_neg (t : IncreasingBoundaryTriple n) (H : TripleArray n R) (x : Fin n) :
    t.fixedFarGate (-H) x = -t.fixedFarGate H x := by
  by_cases hx : t.lower < x ∧ x < t.upper
  · simp only [fixedFarGate, dif_pos hx, Pi.neg_apply, neg_neg, neg_mul]
  · simp only [fixedFarGate, dif_neg hx, neg_zero]

theorem fixedFarGate_weight (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (π : IntervalComposition t.spanInterval) :
    π.nearFarWeight 0 H =
      ∏ k : Fin (π.parts - 1), t.fixedFarGate H (π.interiorPosition k) := by
  rw [π.nearFarWeight_far_only]
  apply Finset.prod_congr rfl
  intro k _
  exact (t.fixedFarGate_at_interior H π k).symm

/-- Express the one-gate response by erasing exactly the physical middle
cut. This is the form needed by the full erased-gap sum bijection. -/
theorem farWeight_difference_physical (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (π : t.MiddleComposition) :
    π.val.nearFarWeight 0 H₂ - π.val.nearFarWeight 0 H₁ =
      (-(H₂ t - H₁ t) * ⅟ (2 : R)) *
        ∏ x ∈ π.val.cutSet.interior.val.erase t.middle, t.fixedFarGate H₁ x := by
  obtain ⟨k, hk, _⟩ := (π.val.existsUnique_farTriple_iff t).mpr ⟨rfl, π.property⟩
  have hm := ((π.val.farTriple_eq_iff k t).mp hk).2
  rw [π.val.farWeight_difference_at_critical t H₁ H₂ h k hk]
  congr 1
  have hp : (∏ j ∈ Finset.univ.erase k, -H₁ (π.val.farTriple j) * ⅟ (2 : R)) =
      ∏ j ∈ Finset.univ.erase k, t.fixedFarGate H₁ (π.val.interiorPosition j) := by
    apply Finset.prod_congr rfl
    intro j _
    exact (t.fixedFarGate_at_interior H₁ π.val j).symm
  rw [hp, π.val.prod_interiorPositions_erase, hm]

end IncreasingBoundaryTriple

end
end SM
