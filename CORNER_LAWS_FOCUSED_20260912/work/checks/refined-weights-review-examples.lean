namespace RefinedWeightsIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

-- Every fine interior factor occurs once, either at an outer cut or inside one inner part.
theorem complete_factor_count (π : IntervalComposition I) (T : RefiningCutSet π) :
    (π.parts - 1) + (∑ k : Fin π.parts, ((π.refinementInner T k).parts - 1)) =
      T.val.toComposition.parts - 1 := by
  have hm : Fintype.card (IntervalComposition.RefinementMarked π T) = π.parts - 1 := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (π.refinedMarkedEquiv T)).symm
  have hu : Fintype.card (IntervalComposition.RefinementUnmarked π T) =
      ∑ k : Fin π.parts, ((π.refinementInner T k).parts - 1) := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using
      (Fintype.card_congr (π.refinedUnmarkedEquiv T)).symm
  have hc := Fintype.card_subtype_compl
    (fun r : Fin (T.val.toComposition.parts - 1) =>
      T.val.toComposition.interiorPosition r ∈ π.cutSet.cuts)
  have hle := Fintype.card_le_of_injective
    (fun r : IntervalComposition.RefinementMarked π T => r.val) Subtype.val_injective
  simp only [Fintype.card_fin] at hc hle
  change Fintype.card (IntervalComposition.RefinementUnmarked π T) =
    T.val.toComposition.parts - 1 - Fintype.card (IntervalComposition.RefinementMarked π T) at hc
  omega

-- The transported inner near sample retains all three actual entries.
theorem inner_near_entries_are_exact (π : IntervalComposition I) (T : RefiningCutSet π)
    (k : Fin π.parts) (j : Fin ((π.refinementInner T k).parts - 1)) :
    let u := T.val.toComposition.nearTriple (π.refinedInteriorIndex T ⟨k,j⟩)
    let v := (π.refinementInner T k).nearTriple j
    u.lower = v.lower ∧ u.middle = v.middle ∧ u.upper = v.upper := by
  dsimp only
  rw [π.inner_nearTriple_transport T k j]
  exact ⟨rfl,rfl,rfl⟩

-- The far sample uses the original global endpoints, not those of an inner part.
theorem outer_far_entries_are_global (π : IntervalComposition I) (T : RefiningCutSet π)
    (j : Fin (π.parts - 1)) :
    let t := T.val.toComposition.farTriple (π.refinedOuterIndex T j)
    t.lower = I.left ∧ t.middle = π.interiorPosition j ∧ t.upper = I.right := by
  dsimp only
  rw [π.outer_farTriple_transport T j]
  exact ⟨rfl,rfl,rfl⟩

-- Unary outer data produces the empty marked subset for any refinement.
theorem unary_outer_has_empty_marks (I : BoundaryInterval n)
    (T : RefiningCutSet (IntervalComposition.single I)) :
    (IntervalComposition.single I).refinementMarkIndices T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hm := ((IntervalComposition.single I).mem_refinementMarkIndices T r).mp hr
  have j := ((IntervalComposition.single I).refinedMarkedEquiv T).symm ⟨r,hm⟩
  exact Fin.elim0 j

-- Retaining exactly the outer cut set marks every fine interior position.
theorem identical_outer_and_fine_marks_all (π : IntervalComposition I) :
    π.refinementMarkIndices ⟨π.cutSet, Finset.Subset.refl _⟩ = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro r
  rw [π.mem_refinementMarkIndices]
  have h := π.cutSet.toComposition.interiorPosition_mem r
  rw [BoundaryCutSet.toComposition_cutSet] at h
  exact ((π.cutSet.mem_interior_iff _).mp h).1

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

-- The reconstructed-family formula applies to every original raw inner family.
theorem raw_family_near_weight_transport (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) (D : TripleArray n R) :
    let T := π.flattenRefinement (fun k => (σ k).cutSet)
    (∏ k : Fin π.parts, (σ k).nearFarWeight D 0) =
      ∏ r ∈ (π.refinementMarkIndices T)ᶜ,
        D (T.val.toComposition.nearTriple r) * ⅟ (2 : R) := by
  let T := π.flattenRefinement (fun k => (σ k).cutSet)
  let τ : ∀ k : Fin π.parts, IntervalComposition (π.part k) := fun k => π.refinementInner T k
  have ht : τ = σ := funext (π.refinementInner_flatten σ)
  have hp := congrArg (fun η : ∀ k : Fin π.parts, IntervalComposition (π.part k) =>
    ∏ k : Fin π.parts, (η k).nearFarWeight D 0) ht
  exact hp.symm.trans (π.prod_inner_near_weights T D)

-- Both coefficient families and every child factor are transported for the raw source summand.
theorem raw_full_nested_summand (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k))
    (D H : TripleArray n R) (X : IntervalArray n R) :
    let T := π.flattenRefinement (fun k => (σ k).cutSet)
    π.nearFarWeight 0 H *
      (∏ k : Fin π.parts, (σ k).nearFarWeight D 0 * ∏ j : Fin (σ k).parts, X ((σ k).part j)) =
    ((∏ r ∈ π.refinementMarkIndices T, -H (T.val.toComposition.farTriple r) * ⅟ (2 : R)) *
      (∏ r ∈ (π.refinementMarkIndices T)ᶜ, D (T.val.toComposition.nearTriple r) * ⅟ (2 : R))) *
        ∏ j : Fin T.val.toComposition.parts, X (T.val.toComposition.part j) := by
  let T := π.flattenRefinement (fun k => (σ k).cutSet)
  let τ : ∀ k : Fin π.parts, IntervalComposition (π.part k) := fun k => π.refinementInner T k
  have ht : τ = σ := funext (π.refinementInner_flatten σ)
  have hp := congrArg (fun η : ∀ k : Fin π.parts, IntervalComposition (π.part k) =>
    π.nearFarWeight 0 H * (∏ k : Fin π.parts, (η k).nearFarWeight D 0 *
      ∏ j : Fin (η k).parts, X ((η k).part j))) ht
  exact hp.symm.trans (π.nested_summand_transport T D H X)

-- All unary inner coefficients contribute one, without a nontrivial-ring premise.
theorem all_unary_inner_coefficients_one (π : IntervalComposition I) (D : TripleArray n R) :
    (∏ k : Fin π.parts, (IntervalComposition.single (π.part k)).nearFarWeight D 0) = 1 := by
  apply Finset.prod_eq_one
  intro k _
  exact (IntervalComposition.single (π.part k)).nearFarWeight_one D 0 rfl

-- The actual marked-refinement output uses the same underlying physical marks.
theorem raw_marks_match_actual_bijection (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) :
    (π.refinementMarks (π.flattenRefinement (fun k => (σ k).cutSet))).val =
      (IntervalComposition.nestedMarkedCutEquiv I ⟨π,σ⟩).2.val := by
  have transport_val {S U : BoundaryCutSet I} (e : S = U) (m : MarkedCuts S) :
      (e ▸ m : MarkedCuts U).val = m.val := by
    cases e
    rfl
  let S := π.flattenCutSets (fun k => (σ k).cutSet)
  let m : MarkedCuts S := ⟨π.cutSet.interior.val,
    (BoundaryCutSet.cuts_subset_iff_interior_subset π.cutSet S).mp
      (π.outer_cuts_subset_flatten (fun k => (σ k).cutSet))⟩
  change m.val = (S.toComposition_cutSet.symm ▸ m : MarkedCuts S.toComposition.cutSet).val
  exact (transport_val S.toComposition_cutSet.symm m).symm

end
end RefinedWeightsIndependentReview
