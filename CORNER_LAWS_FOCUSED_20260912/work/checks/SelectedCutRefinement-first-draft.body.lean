namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- Fine raw compositions containing every selected outer cut correspond
exactly to the existing refining cut sets. -/
def refiningCompositionEquiv (π : IntervalComposition I) :
    {ρ : IntervalComposition I // π.cutSet.cuts ⊆ ρ.cutSet.cuts} ≃ RefiningCutSet π :=
  Equiv.subtypeEquiv (cutSetEquiv I) (fun _ => Iff.rfl)

/-- Fixing the selected outer cuts leaves one independent raw composition
in each actual gap. Unary inner compositions and one-leaf gaps are retained. -/
def nestedRefiningCompositionEquiv (π : IntervalComposition I) :
    (∀ k : Fin π.parts, IntervalComposition (π.part k)) ≃
      {ρ : IntervalComposition I // π.cutSet.cuts ⊆ ρ.cutSet.cuts} :=
  π.nestedCompositionEquiv.trans π.refiningCompositionEquiv.symm

theorem nestedRefiningCompositionEquiv_val (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) :
    (π.nestedRefiningCompositionEquiv σ).val =
      (π.flattenCutSets (fun k => (σ k).cutSet)).toComposition := rfl

/-- Arbitrary selected interior positions produce the exact outer cuts,
including the empty selection. -/
theorem selectedComposition_interior (S : InteriorCutSet I) :
    (BoundaryCutSet.ofInterior S).toComposition.cutSet.interior = S := by
  rw [BoundaryCutSet.toComposition_cutSet, BoundaryCutSet.interior_ofInterior]

/-- Containment of all outer cuts is precisely containment of the selected
interior positions; the two global endpoints contribute no extra condition. -/
theorem selectedComposition_refines_iff (S : InteriorCutSet I)
    (ρ : IntervalComposition I) :
    (BoundaryCutSet.ofInterior S).toComposition.cutSet.cuts ⊆ ρ.cutSet.cuts ↔
      S.val ⊆ ρ.cutSet.interior.val := by
  rw [BoundaryCutSet.cuts_subset_iff_interior_subset, selectedComposition_interior]

/-- Every physical interior position occurs once, also for a unary
composition whose interior index type and cut set are both empty. -/
theorem prod_interior_positions {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (b : Fin n → R) :
    (∏ j : Fin (π.parts - 1), b (π.interiorPosition j)) =
      ∏ x ∈ π.cutSet.interior.val, b x := by
  calc
    _ = ∏ x : {x : Fin n // x ∈ π.cutSet.interior.val}, b x.val :=
      Fintype.prod_equiv π.interiorPositionEquiv _ _ (fun _ => rfl)
    _ = _ := (Finset.prod_subtype _ (fun _ => Iff.rfl) b).symm

/-- All inner cuts are exactly the unselected fine physical cuts. In
particular a selected mark cannot reappear inside a gap. -/
theorem prod_inner_positions {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (T : RefiningCutSet π) (b : Fin n → R) :
    (∏ k : Fin π.parts, ∏ j : Fin ((π.refinementInner T k).parts - 1),
      b ((π.refinementInner T k).interiorPosition j)) =
      ∏ x ∈ T.val.interior.val \ π.cutSet.interior.val, b x := by
  calc
    _ = ∏ r : RefinementUnmarked π T,
        b (T.val.toComposition.interiorPosition r.val) :=
      π.prod_inner_nearTriples T (fun t => b t.middle)
    _ = ∏ r ∈ (π.refinementMarkIndices T)ᶜ,
        b (T.val.toComposition.interiorPosition r) :=
      π.prod_refinementUnmarked T (fun r => b (T.val.toComposition.interiorPosition r))
    _ = ∏ x ∈ (T.val.toComposition.indexMarks (π.refinementMarkIndices T)ᶜ).val,
        b x := T.val.toComposition.prod_indexMarks (π.refinementMarkIndices T)ᶜ b
    _ = _ := by
      rw [indexMarks_compl]
      unfold refinementMarkIndices
      rw [indexMarks_markIndices]
      simp only [refinementMarks, BoundaryCutSet.toComposition_cutSet]

/-- A gap summand with arbitrary weights at its actual interior positions,
and the original coordinates at every actual child interval. -/
def positionCutSummand {R : Type*} [CommMonoid R]
    (b : Fin n → R) (X : BoundaryInterval n → R) (π : IntervalComposition I) : R :=
  (∏ j : Fin (π.parts - 1), b (π.interiorPosition j)) *
    ∏ j : Fin π.parts, X (π.part j)

/-- Splitting a fixed refining cut set preserves every unselected cut
factor and every actual fine child coordinate, without arity restrictions. -/
theorem prod_refinement_gap_summands {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (T : RefiningCutSet π)
    (b : Fin n → R) (X : BoundaryInterval n → R) :
    (∏ k : Fin π.parts, positionCutSummand b X (π.refinementInner T k)) =
      (∏ x ∈ T.val.interior.val \ π.cutSet.interior.val, b x) *
        ∏ j : Fin T.val.toComposition.parts, X (T.val.toComposition.part j) := by
  simp only [positionCutSummand, Finset.prod_mul_distrib]
  rw [π.prod_inner_positions T b, π.prod_refined_children T X]

/-- The complete termwise identity for an arbitrary independent family
of actual gap compositions, using the genuine ordered flattening. -/
theorem prod_nested_gap_summands {R : Type*} [CommMonoid R]
    (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k))
    (b : Fin n → R) (X : BoundaryInterval n → R) :
    (∏ k : Fin π.parts, positionCutSummand b X (σ k)) =
      (∏ x ∈ (π.flattenCutSets (fun k => (σ k).cutSet)).interior.val \
        π.cutSet.interior.val, b x) *
        ∏ j : Fin (π.flattenCutSets (fun k => (σ k).cutSet)).toComposition.parts,
          X ((π.flattenCutSets (fun k => (σ k).cutSet)).toComposition.part j) := by
  let T := π.flattenRefinement (fun k => (σ k).cutSet)
  have ht : (fun k => π.refinementInner T k) = σ :=
    funext (π.refinementInner_flatten σ)
  have hp := congrArg
    (fun η : ∀ k : Fin π.parts, IntervalComposition (π.part k) =>
      ∏ k : Fin π.parts, positionCutSummand b X (η k)) ht
  exact hp.symm.trans (π.prod_refinement_gap_summands T b X)

/-- The exact fixed-selected-cut sum factors into independent gap sums.
No coefficient identity is assumed: this follows from the actual refining
composition equivalence, the full termwise identity, and finite distributivity. -/
theorem sum_refining_cut_products {R : Type*} [CommSemiring R]
    (π : IntervalComposition I) (b : Fin n → R) (X : BoundaryInterval n → R) :
    (∑ ρ : {ρ : IntervalComposition I // π.cutSet.cuts ⊆ ρ.cutSet.cuts},
      (∏ x ∈ ρ.val.cutSet.interior.val \ π.cutSet.interior.val, b x) *
        ∏ j : Fin ρ.val.parts, X (ρ.val.part j)) =
      ∏ k : Fin π.parts, ∑ σ : IntervalComposition (π.part k), positionCutSummand b X σ := by
  classical
  symm
  calc
    _ = ∑ σ : ∀ k : Fin π.parts, IntervalComposition (π.part k),
        ∏ k : Fin π.parts, positionCutSummand b X (σ k) := Fintype.prod_sum _
    _ = _ := Fintype.sum_equiv π.nestedRefiningCompositionEquiv _ _ (by
      intro σ
      rw [π.nestedRefiningCompositionEquiv_val σ, BoundaryCutSet.toComposition_cutSet]
      exact π.prod_nested_gap_summands σ b X)

/-- Restoring the selected factors gives the product decomposition used
by the source top-coefficient calculation. Zero unselected weights are
allowed, so other silent cuts can be killed without changing the indexing. -/
theorem sum_refining_selected_cut_products {R : Type*} [CommSemiring R]
    (π : IntervalComposition I) (a b : Fin n → R) (X : BoundaryInterval n → R) :
    (∑ ρ : {ρ : IntervalComposition I // π.cutSet.cuts ⊆ ρ.cutSet.cuts},
      (∏ x ∈ π.cutSet.interior.val, a x) *
        ((∏ x ∈ ρ.val.cutSet.interior.val \ π.cutSet.interior.val, b x) *
          ∏ j : Fin ρ.val.parts, X (ρ.val.part j))) =
      (∏ x ∈ π.cutSet.interior.val, a x) *
        ∏ k : Fin π.parts, ∑ σ : IntervalComposition (π.part k), positionCutSummand b X σ := by
  rw [← Finset.mul_sum, π.sum_refining_cut_products b X]

/-- A constant selected weight contributes its power with exponent equal
to the number of actual selected interior positions. -/
theorem sum_refining_constant_selected_factor {R : Type*} [CommSemiring R]
    (π : IntervalComposition I) (q : R) (b : Fin n → R) (X : BoundaryInterval n → R) :
    (∑ ρ : {ρ : IntervalComposition I // π.cutSet.cuts ⊆ ρ.cutSet.cuts},
      q ^ π.cutSet.interior.val.card *
        ((∏ x ∈ ρ.val.cutSet.interior.val \ π.cutSet.interior.val, b x) *
          ∏ j : Fin ρ.val.parts, X (ρ.val.part j))) =
      q ^ π.cutSet.interior.val.card *
        ∏ k : Fin π.parts, ∑ σ : IntervalComposition (π.part k), positionCutSummand b X σ := by
  simpa only [Finset.prod_const] using π.sum_refining_selected_cut_products (fun _ => q) b X

end
end SM.IntervalComposition
