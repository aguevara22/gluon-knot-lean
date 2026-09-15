namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- The raw expansion preserves the exact nonunary part-count condition. -/
def expandNonunaryComposition (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize}
    (π : {π : IntervalComposition J // 2 ≤ π.parts}) :
    {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts} :=
  ⟨expandComposition t π.val, π.property⟩

theorem expandNonunaryComposition_injective (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) :
    Function.Injective (expandNonunaryComposition t (J := J)) := by
  intro π ρ he
  have hc : expandComposition t π.val = expandComposition t ρ.val :=
    congrArg (fun q : {q : IntervalComposition (t.expandInterval J) // 2 ≤ q.parts} => q.val) he
  apply Subtype.ext
  exact (survivingCompositionEquiv t J).injective (Subtype.ext hc)

/-- Its range is all surviving original nonunary compositions, with no
extra geometric, root, or weight condition. -/
theorem mem_range_expandNonunary (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts}) :
    π ∈ Set.range (expandNonunaryComposition t (J := J)) ↔ SurvivingCuts t π.val := by
  constructor
  · rintro ⟨ρ, rfl⟩
    exact expandComposition_survives t ρ.val
  · intro hπ
    refine ⟨⟨contractComposition t π.val hπ, π.property⟩, ?_⟩
    exact Subtype.ext (expand_contractComposition t π.val hπ)

variable {R : Type*} [AddCommMonoid R]

/-- Reindex the entire nonunary response sum when nonsurviving terms have
zero response. The premise concerns the summand's difference, not the value
of either side's original composition term. -/
theorem sum_nonunary_expansion (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (f : IntervalComposition (t.expandInterval J) → R)
    (hzero : ∀ π : IntervalComposition (t.expandInterval J),
      2 ≤ π.parts → ¬ SurvivingCuts t π → f π = 0) :
    (∑ π : {π : IntervalComposition J // 2 ≤ π.parts}, f (expandComposition t π.val)) =
      ∑ π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts}, f π.val := by
  apply Fintype.sum_of_injective (expandNonunaryComposition t)
    (expandNonunaryComposition_injective t J)
  · intro π hπ
    exact hzero π.val π.property (fun h => hπ ((mem_range_expandNonunary t J π).mpr h))
  · intro π
    rfl

end
end SM.IntervalComposition
