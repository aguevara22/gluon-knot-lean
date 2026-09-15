namespace SM.IntervalComposition

noncomputable section
universe u
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

/-- At each interior cut choose independently the negative far factor or
the neighboring near factor. The sum includes empty and full marked subsets. -/
theorem nearFarWeight_marked_expansion (π : IntervalComposition I) (D H : TripleArray n R) :
    π.nearFarWeight D H =
      ∑ marked : Finset (Fin (π.parts - 1)),
        (∏ k ∈ marked, (-H (π.farTriple k)) * ⅟ (2 : R)) *
        ∏ k ∈ markedᶜ, D (π.nearTriple k) * ⅟ (2 : R) := by
  classical
  unfold nearFarWeight
  calc
    (∏ k : Fin (π.parts - 1), (D (π.nearTriple k) - H (π.farTriple k)) * ⅟ (2 : R)) =
        ∏ k : Fin (π.parts - 1),
          ((-H (π.farTriple k)) * ⅟ (2 : R) + D (π.nearTriple k) * ⅟ (2 : R)) := by
      apply Finset.prod_congr rfl
      intro k _
      ring
    _ = _ := Fintype.prod_add _ _

end
end SM.IntervalComposition
