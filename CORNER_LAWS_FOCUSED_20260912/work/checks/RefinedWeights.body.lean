namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- The actual outer interior cuts, viewed as marks of the fine composition. -/
def refinementMarks (π : IntervalComposition I) (T : RefiningCutSet π) :
    MarkedCuts T.val.toComposition.cutSet :=
  ⟨π.cutSet.interior.val, by
    rw [BoundaryCutSet.toComposition_cutSet]
    exact (BoundaryCutSet.cuts_subset_iff_interior_subset _ _).mp T.property⟩

/-- Recover the marked fine indices from their physical outer cut positions. -/
def refinementMarkIndices (π : IntervalComposition I) (T : RefiningCutSet π) :
    Finset (Fin (T.val.toComposition.parts - 1)) :=
  T.val.toComposition.markIndices (π.refinementMarks T)

theorem mem_refinementMarkIndices (π : IntervalComposition I) (T : RefiningCutSet π)
    (r : Fin (T.val.toComposition.parts - 1)) :
    r ∈ π.refinementMarkIndices T ↔
      T.val.toComposition.interiorPosition r ∈ π.cutSet.cuts := by
  change (r ∈ Finset.univ.filter (fun r =>
    T.val.toComposition.interiorPosition r ∈ π.cutSet.interior.val)) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [π.cutSet.mem_interior_iff]
  have hb := T.val.toComposition.cutSet.interior.property _
    (T.val.toComposition.interiorPosition_mem r)
  exact ⟨And.left, fun h => ⟨h, hb⟩⟩

/-- Reindex the marked subtype product by its exact finite set of indices. -/
theorem prod_refinementMarked {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (T : RefiningCutSet π)
    (f : Fin (T.val.toComposition.parts - 1) → R) :
    (∏ r : RefinementMarked π T, f r.val) = ∏ r ∈ π.refinementMarkIndices T, f r :=
  (Finset.prod_subtype _ (π.mem_refinementMarkIndices T) f).symm

/-- The complementary index set is exactly all inner, unmarked cuts. -/
theorem prod_refinementUnmarked {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (T : RefiningCutSet π)
    (f : Fin (T.val.toComposition.parts - 1) → R) :
    (∏ r : RefinementUnmarked π T, f r.val) = ∏ r ∈ (π.refinementMarkIndices T)ᶜ, f r := by
  symm
  apply Finset.prod_subtype
  intro r
  rw [Finset.mem_compl, π.mem_refinementMarkIndices T]

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

theorem nearFarWeight_near_only (π : IntervalComposition I) (D : TripleArray n R) :
    π.nearFarWeight D 0 = ∏ r : Fin (π.parts - 1), D (π.nearTriple r) * ⅟ (2 : R) := by
  simp only [nearFarWeight, Pi.zero_apply, sub_zero]

theorem nearFarWeight_far_only (π : IntervalComposition I) (H : TripleArray n R) :
    π.nearFarWeight 0 H = ∏ r : Fin (π.parts - 1), -H (π.farTriple r) * ⅟ (2 : R) := by
  simp only [nearFarWeight, Pi.zero_apply, zero_sub]

/-- Every inner near-only coefficient supplies precisely an unmarked factor. -/
theorem prod_inner_near_weights (π : IntervalComposition I) (T : RefiningCutSet π)
    (D : TripleArray n R) :
    (∏ k : Fin π.parts, (π.refinementInner T k).nearFarWeight D 0) =
      ∏ r ∈ (π.refinementMarkIndices T)ᶜ,
        D (T.val.toComposition.nearTriple r) * ⅟ (2 : R) := by
  simp only [nearFarWeight_near_only]
  rw [π.prod_inner_nearTriples T (fun t => D t * ⅟ (2 : R))]
  exact π.prod_refinementUnmarked T (fun r => D (T.val.toComposition.nearTriple r) * ⅟ (2 : R))

/-- The outer far-only coefficient supplies precisely the marked factors,
each evaluated with the original global endpoints. -/
theorem outer_far_weight (π : IntervalComposition I) (T : RefiningCutSet π)
    (H : TripleArray n R) :
    π.nearFarWeight 0 H = ∏ r ∈ π.refinementMarkIndices T,
      -H (T.val.toComposition.farTriple r) * ⅟ (2 : R) := by
  rw [nearFarWeight_far_only, π.prod_outer_farTriples T (fun t => -H t * ⅟ (2 : R))]
  exact π.prod_refinementMarked T (fun r => -H (T.val.toComposition.farTriple r) * ⅟ (2 : R))

/-- Exact transport of one full nested summand, including every child
coordinate and every near or far factor. Unary cases use the same formula. -/
theorem nested_summand_transport (π : IntervalComposition I) (T : RefiningCutSet π)
    (D H : TripleArray n R) (X : IntervalArray n R) :
    π.nearFarWeight 0 H *
        (∏ k : Fin π.parts, (π.refinementInner T k).nearFarWeight D 0 *
          ∏ j : Fin ((π.refinementInner T k).parts), X ((π.refinementInner T k).part j)) =
      ((∏ r ∈ π.refinementMarkIndices T, -H (T.val.toComposition.farTriple r) * ⅟ (2 : R)) *
        (∏ r ∈ (π.refinementMarkIndices T)ᶜ, D (T.val.toComposition.nearTriple r) * ⅟ (2 : R))) *
          ∏ j : Fin T.val.toComposition.parts, X (T.val.toComposition.part j) := by
  rw [Finset.prod_mul_distrib]
  rw [π.prod_inner_near_weights T D, π.prod_refined_children T X, π.outer_far_weight T H]
  exact (mul_assoc _ _ _).symm

end
end SM.IntervalComposition
