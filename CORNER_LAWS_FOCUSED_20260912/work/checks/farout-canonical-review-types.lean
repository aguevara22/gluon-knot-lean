import SM.Farout
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
set_option pp.universes false

namespace RefinementTransportIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

-- Characterize the actual raw child intervals, including unique indexing.
theorem actual_parts_are_exact_consecutive_pairs (π : IntervalComposition I)
    (J : BoundaryInterval n) :
    π.cutSet.Consecutive J ↔ ∃! k : Fin π.parts, π.part k = J := by
  constructor
  · intro hJ
    obtain ⟨k, hk⟩ := π.exists_part_of_consecutive J hJ
    exact ⟨k, hk, fun l hl => π.part_injective (hl.trans hk.symm)⟩
  · rintro ⟨k, rfl, _⟩
    exact π.part_consecutive k

-- Every globally fine child has exactly one containing outer part.
theorem actual_fine_child_has_unique_outer (π : IntervalComposition I)
    (T : RefiningCutSet π) (J : BoundaryInterval n) (hJ : T.val.Consecutive J) :
    ∃! k : Fin π.parts, (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right := by
  obtain ⟨k, hk⟩ := π.consecutive_contained_in_part T.val T.property J hJ
  exact ⟨k, hk, fun l hl => π.containing_part_unique J hl hk⟩

-- A physical interior position determines one actual neighboring triple.
theorem actual_near_sample_unique (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    ∃! t : IncreasingBoundaryTriple n,
      π.cutSet.Consecutive t.leftInterval ∧ π.cutSet.Consecutive t.rightInterval ∧
        t.middle = π.interiorPosition k := by
  refine ⟨π.nearTriple k, ⟨(π.nearTriple_consecutive k).1,
    (π.nearTriple_consecutive k).2, π.nearTriple_middle_position k⟩, ?_⟩
  intro t ht
  exact (π.nearTriple_eq_of_consecutive k t ht.1 ht.2.1 ht.2.2.symm).symm

-- Any coefficient array therefore samples the exact same three physical positions.
theorem arbitrary_array_samples_actual_neighbors {R : Type*}
    (π : IntervalComposition I) (k : Fin (π.parts - 1)) (D : TripleArray n R)
    (t : IncreasingBoundaryTriple n)
    (hl : π.cutSet.Consecutive t.leftInterval) (hr : π.cutSet.Consecutive t.rightInterval)
    (hm : π.interiorPosition k = t.middle) : D (π.nearTriple k) = D t := by
  rw [π.nearTriple_eq_of_consecutive k t hl hr hm]

-- The chosen index equivalence preserves the full child interval.
theorem refined_index_keeps_interval (π : IntervalComposition I) (T : RefiningCutSet π)
    (a : Σ k : Fin π.parts, Fin (π.refinementInner T k).parts) :
    T.val.toComposition.part (π.refinedChildrenEquiv T a) =
      (π.refinementInner T a.1).part a.2 :=
  π.refinedChildIndex_part T a

-- The bijection also fixes the total number of children, so none is lost or repeated.
theorem child_count_is_sum_of_inner_counts (π : IntervalComposition I) (T : RefiningCutSet π) :
    (∑ k : Fin π.parts, (π.refinementInner T k).parts) = T.val.toComposition.parts := by
  have h := Fintype.card_congr (π.refinedChildrenEquiv T)
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

-- Recover the original raw part count and cut map, not just an equal set of endpoints.
theorem recovered_inner_has_raw_data (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) (k : Fin π.parts) :
    (π.refinementInner (π.flattenRefinement (fun k => (σ k).cutSet)) k).parts = (σ k).parts ∧
      HEq (π.refinementInner (π.flattenRefinement (fun k => (σ k).cutSet)) k).cut (σ k).cut := by
  rw [π.refinementInner_flatten σ k]
  exact ⟨rfl, HEq.rfl⟩

-- The actual source marked-refinement map, not an unrelated enumeration, has the same product.
theorem actual_marked_refinement_child_product {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k))
    (X : BoundaryInterval n → R) :
    (∏ k : Fin π.parts, ∏ j : Fin (σ k).parts, X ((σ k).part j)) =
      ∏ r : Fin (IntervalComposition.nestedMarkedCutEquiv I ⟨π, σ⟩).1.parts,
        X ((IntervalComposition.nestedMarkedCutEquiv I ⟨π, σ⟩).1.part r) :=
  π.prod_nested_children σ X

-- Unary inner compositions keep exactly their outer child coordinate.
theorem all_inner_unary_product {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (X : BoundaryInterval n → R) :
    (∏ k : Fin π.parts, X (π.part k)) =
      ∏ r : Fin (π.flattenCutSets
        (fun k => (IntervalComposition.single (π.part k)).cutSet)).toComposition.parts,
        X ((π.flattenCutSets
          (fun k => (IntervalComposition.single (π.part k)).cutSet)).toComposition.part r) := by
  simpa only [IntervalComposition.single_product] using
    π.prod_nested_children (fun k => IntervalComposition.single (π.part k)) X

-- Full/empty markings are the exact interior universe and empty set.
theorem empty_and_full_index_marks (π : IntervalComposition I) :
    (π.indexMarks ∅).val = ∅ ∧
      (π.indexMarks Finset.univ).val = π.cutSet.interior.val := by
  constructor
  · simp [IntervalComposition.indexMarks]
  · simpa [IntervalComposition.indexMarks] using π.indexMarks_compl ∅

-- Complementary marks never include either endpoint or an unrelated boundary position.
theorem unmarked_positions_are_exactly_relative (π : IntervalComposition I)
    (s : Finset (Fin (π.parts - 1))) (x : Fin n) (hx : x ∈ (π.indexMarks sᶜ).val) :
    I.left < x ∧ x < I.right ∧ x ∉ (π.indexMarks s).val := by
  rw [π.indexMarks_compl] at hx
  have h := Finset.mem_sdiff.mp hx
  exact ⟨(π.cutSet.interior.property x h.1).1,
    (π.cutSet.interior.property x h.1).2, h.2⟩

-- Both chosen and complementary products transport their actual physical arguments.
theorem marked_and_unmarked_product_transport {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (m : MarkedCuts π.cutSet) (f g : Fin n → R) :
    (∏ k ∈ π.markIndices m, f (π.interiorPosition k)) *
      (∏ k ∈ (π.markIndices m)ᶜ, g (π.interiorPosition k)) =
    (∏ x ∈ m.val, f x) * (∏ x ∈ π.cutSet.interior.val \ m.val, g x) := by
  rw [π.prod_markIndices, π.prod_indexMarks, π.indexMarks_compl, π.indexMarks_markIndices]

-- Every one of the 2^(parts-1) possible source markings occurs exactly once.
theorem all_markings_have_full_cardinality (π : IntervalComposition I) :
    Fintype.card (MarkedCuts π.cutSet) = 2 ^ (π.parts - 1) := by
  have h := Fintype.card_congr π.marksIndexEquiv
  simpa only [Fintype.card_finset, Fintype.card_fin] using h.symm

-- In the unary case the complete sum contains precisely the empty marking.
theorem unary_marking_sum {R : Type*} [AddCommMonoid R]
    (I : BoundaryInterval n) (f : MarkedCuts (IntervalComposition.single I).cutSet → R) :
    (∑ m : MarkedCuts (IntervalComposition.single I).cutSet, f m) =
      f ((IntervalComposition.single I).indexMarks ∅) := by
  rw [← (IntervalComposition.single I).sum_all_indexMarks f]
  change (∑ s : Finset (Fin 0), f ((IntervalComposition.single I).indexMarks s)) = _
  simp only [Fintype.sum_unique]
  exact congrArg (fun s : Finset (Fin 0) => f ((IntervalComposition.single I).indexMarks s))
    (Subsingleton.elim _ _)

end
end RefinementTransportIndependentReview

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

namespace NearFarFactorizationIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

-- The inverse order is near-inverse after far-inverse, matching F after G.
theorem inverse_factorization_order (D H : TripleArray n R) (Y : IntervalArray n R) :
    nearFarInverse D H Y = nearFarInverse D 0 (nearFarInverse 0 H Y) := by
  symm
  apply nearFar_solution_unique D H
  rw [nearFar_factorization D H]
  change farTransform H (nearTransform D (nearFarInverse D 0 (nearFarInverse 0 H Y))) = Y
  simp only [nearTransform, farTransform, nearFarTransform_inverse]

-- No assumed solutions are needed: the canonical inverse supplies every target.
theorem output_independent_with_actual_inverse (D₁ D₂ H : TripleArray n R)
    (Y : IntervalArray n R) :
    nearFarTransform D₁ (-H) (nearFarInverse D₁ H Y) =
      nearFarTransform D₂ (-H) (nearFarInverse D₂ H Y) :=
  complete_output_near_independent D₁ D₂ H _ _ Y
    (nearFarTransform_inverse D₁ H Y) (nearFarTransform_inverse D₂ H Y)

theorem inverse_target_E_has_far_only_output (D H : TripleArray n R) :
    nearFarTransform D (-H) (nearFarInverse D H boundaryUnitArray) = farOnlyOutput H :=
  reversedFar_output_of_solution D H _ _ (nearFarTransform_inverse D H boundaryUnitArray)

-- The actual geometric root coefficient remains the same with arbitrary near-array D.
theorem actual_root_all_near_arrays (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) (D : TripleArray n R) :
    (treeCoefficient P hP g hn : R) =
      nearFarTransform D (-geometricBoundaryArray P g)
        (nearFarInverse D (geometricBoundaryArray P g) boundaryUnitArray)
        (fullBoundaryInterval hn) := by
  rw [inverse_target_E_has_far_only_output]
  exact treeCoefficient_farOnly P hP g hn

-- The output is tied to the same physical root when the representative is shifted.
theorem far_only_output_physical_root_shift (P : LabelledTuple n) (g a : ZMod n) :
    farOnlyOutput (geometricBoundaryArray (R := R) (shift a P) (g-a)) =
      farOnlyOutput (geometricBoundaryArray P g) := by
  rw [geometricBoundaryArray_shift]

-- Open-word leaf and nonleaf conventions use every original interval coordinate.
theorem all_interval_E_and_leaf_B_values (H : TripleArray n R) (I : BoundaryInterval n) :
    (I.leaves = 1 → farTransform H (farOnlyCoordinates H) I = 1 ∧ farOnlyOutput H I = 1) ∧
    (2 ≤ I.leaves → farTransform H (farOnlyCoordinates H) I = 0) :=
  ⟨farOnly_leaf_values H I, farOnly_nonleaf_E H I⟩

-- The whole marked sum keeps the source unary composition's exact X_I term.
theorem unary_marked_sum_retains_coordinate (D H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    (∑ m : MarkedCuts (IntervalComposition.single I).cutSet,
      IntervalComposition.markedSummand D H X (IntervalComposition.single I) m) = X I := by
  rw [IntervalComposition.sum_markedSummand]
  rw [(IntervalComposition.single I).nearFarWeight_one D H rfl,
    one_mul, IntervalComposition.single_product]

end
end NearFarFactorizationIndependentReview

namespace FaroutIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n]

theorem all_physical_positions_once (J : BoundaryInterval n) (x : Fin n)
    (hl : J.left ≤ x) (hr : x ≤ J.right) :
    ∃! k : Fin (J.leaves + 1), J.globalPosition k = x := by
  refine ⟨J.localPosition x hl hr, J.global_localPosition x hl hr, ?_⟩
  intro k hk
  exact J.globalPosition_strict.injective (hk.trans (J.global_localPosition x hl hr).symm)

theorem translated_leaf_count (J : BoundaryInterval n) (K : BoundaryInterval (J.leaves + 1)) :
    (J.liftInterval K).leaves = K.leaves := by
  unfold BoundaryInterval.leaves BoundaryInterval.liftInterval BoundaryInterval.globalPosition
  simp only
  omega

theorem all_physical_subintervals (J I : BoundaryInterval n)
    (hl : J.left ≤ I.left) (hr : I.right ≤ J.right) :
    ∃ K : BoundaryInterval (J.leaves + 1), J.liftInterval K = I := by
  have hli : J.left ≤ I.right := le_trans hl (le_of_lt I.increasing)
  have hri : I.left ≤ J.right := le_trans (le_of_lt I.increasing) hr
  let K : BoundaryInterval (J.leaves + 1) :=
    ⟨J.localPosition I.left hl hri, J.localPosition I.right hli hr, by
      have hi := I.increasing
      change I.left.val < I.right.val at hi
      change J.left.val ≤ I.left.val at hl
      change I.left.val - J.left.val < I.right.val - J.left.val
      omega⟩
  refine ⟨K, ?_⟩
  apply BoundaryInterval.eq_of_endpoints
  · exact J.global_localPosition I.left hl hri
  · exact J.global_localPosition I.right hli hr

theorem all_raw_parts_and_cuts (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) :
    (IntervalComposition.liftComposition J π).parts = π.parts ∧
    (∀ k : Fin (π.parts + 1),
      ((IntervalComposition.liftComposition J π).cut k).val = J.left.val + (π.cut k).val) ∧
    IntervalComposition.lowerComposition J (IntervalComposition.liftComposition J π) = π :=
  ⟨rfl, fun _ => rfl, IntervalComposition.lower_liftComposition J π⟩

theorem unary_is_preserved (J : BoundaryInterval n) (K : BoundaryInterval (J.leaves + 1)) :
    IntervalComposition.liftComposition J (IntervalComposition.single K) =
      IntervalComposition.single (J.liftInterval K) :=
  IntervalComposition.eq_single_of_parts_eq_one _ rfl

theorem complete_composition_cardinality (J : BoundaryInterval n)
    (K : BoundaryInterval (J.leaves + 1)) :
    Fintype.card (IntervalComposition K) = Fintype.card (IntervalComposition (J.liftInterval K)) :=
  Fintype.card_congr (IntervalComposition.restrictionEquiv J K)

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

theorem actual_child_product (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) (X : IntervalArray n R) :
    (∏ k : Fin π.parts, restrictIntervalArray J X (π.part k)) =
      ∏ k : Fin (IntervalComposition.liftComposition J π).parts,
        X ((IntervalComposition.liftComposition J π).part k) := rfl

theorem all_actual_samples (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) (D H : TripleArray n R) (k : Fin (π.parts - 1)) :
    restrictTripleArray J D (π.nearTriple k) =
      D ((IntervalComposition.liftComposition J π).nearTriple k) ∧
    restrictTripleArray J H (π.farTriple k) =
      H ((IntervalComposition.liftComposition J π).farTriple k) := ⟨rfl, rfl⟩

theorem local_inverse_solves_actual_restriction (J : BoundaryInterval n) (D H : TripleArray n R)
    (Y : IntervalArray n R) :
    nearFarTransform (restrictTripleArray J D) (restrictTripleArray J H)
      (restrictIntervalArray J (nearFarInverse D H Y)) = restrictIntervalArray J Y := by
  rw [nearFarTransform_restrict, nearFarTransform_inverse]

theorem restricted_c_is_actual_local_inverse (P : LabelledTuple n) (g : ZMod n)
    (J : BoundaryInterval n) :
    restrictIntervalArray J (farOnlyCoordinates (geometricBoundaryArray (R := R) P g)) =
      nearFarInverse 0 (geometricBoundaryArray (restrictedWordTuple P g J) 0) boundaryUnitArray := by
  rw [farOnlyCoordinates_restrict, ← geometricBoundaryArray_restrictedWord]
  rfl

theorem full_contiguous_word_and_directed_root (P : LabelledTuple n) (g : ZMod n)
    (J : BoundaryInterval n) :
    (∀ k : Fin (J.leaves + 1), boundaryWord (restrictedWordTuple P g J) 0 k =
      boundaryWord P g (J.globalPosition k)) ∧
    restrictedWordTuple P g J 0 = boundaryWord P g J.right ∧
    restrictedWordTuple P g J 1 = boundaryWord P g J.left ∧
    edge (restrictedWordTuple P g J) 0 = boundaryWord P g J.left - boundaryWord P g J.right :=
  ⟨restrictedWord_boundary P g J, restrictedWord_last_vertex P g J,
    restrictedWord_first_vertex P g J, restrictedWord_closing_edge P g J⟩

theorem nonleaf_has_three_vertices (J : BoundaryInterval n) (hJ : 2 ≤ J.leaves) :
    3 ≤ J.leaves + 1 := by omega

theorem local_root_without_global_G1 (hn : 3 ≤ n) (P : LabelledTuple n) (g : ZMod n)
    (J : BoundaryInterval n) (hJ : 2 ≤ J.leaves) (hlocal : G1 (restrictedWordTuple P g J)) :
    farOnlyOutput (geometricBoundaryArray (R := R) P g) J =
      (treeCoefficient (restrictedWordTuple P g J) hlocal 0 (by omega) : R) :=
  ((farout n R hn).2.2.2.2 P g J hJ hlocal).2

theorem aggregate_polynomials_both_directions (hn : 3 ≤ n) (D H : TripleArray n R) :
    ∃ Ψ : BoundaryInterval n → MvPolynomial (BoundaryInterval n) R,
      (∀ Y : IntervalArray n R, nearFarTransform D H
        (fun I => MvPolynomial.eval₂Hom (RingHom.id R) Y (Ψ I)) = Y) ∧
      (∀ X : IntervalArray n R,
        (fun I => MvPolynomial.eval₂Hom (RingHom.id R) (nearFarTransform D H X) (Ψ I)) = X) :=
  ((farout n R hn).1 D H).1

theorem aggregate_factorization_on_every_array (hn : 3 ≤ n)
    (D H : TripleArray n R) (X : IntervalArray n R) :
    nearFarTransform D H X = farTransform H (nearTransform D X) :=
  congrFun ((farout n R hn).1 D H).2 X

theorem aggregate_geometry_and_actual_full_root (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : G1 P) (g : ZMod n) :
    nearFarTransform (geometricBoundaryArray (R := R) P g) (geometricBoundaryArray P g)
      (fun I => (openTreeSum P hP g I : R)) = boundaryUnitArray ∧
    (treeCoefficient P hP g hn : R) =
      farOnlyOutput (geometricBoundaryArray P g) (fullBoundaryInterval hn) :=
  ⟨((farout n R hn).2.1 P hP g).1, ((farout n R hn).2.1 P hP g).2.2⟩

theorem aggregate_near_freedom_has_real_solutions (hn : 3 ≤ n) (D₁ D₂ H : TripleArray n R) :
    nearFarTransform D₁ (-H) (nearFarInverse D₁ H boundaryUnitArray) =
      nearFarTransform D₂ (-H) (nearFarInverse D₂ H boundaryUnitArray) :=
  (farout n R hn).2.2.1 D₁ D₂ H _ _ (nearFarTransform_inverse _ _ _) (nearFarTransform_inverse _ _ _)

theorem aggregate_open_leaf_and_nonleaf (hn : 3 ≤ n) (H : TripleArray n R)
    (J : BoundaryInterval n) :
    (2 ≤ J.leaves → farTransform H (farOnlyCoordinates H) J = 0) ∧
    (J.leaves = 1 → farTransform H (farOnlyCoordinates H) J = 1 ∧ farOnlyOutput H J = 1) :=
  (farout n R hn).2.2.2.1 H J

end
end FaroutIndependentReview

#check SM.BoundaryCutSet.Consecutive
#print axioms SM.BoundaryCutSet.Consecutive
#check SM.BoundaryInterval.eq_of_endpoints
#print axioms SM.BoundaryInterval.eq_of_endpoints
#check SM.BoundaryCutSet.consecutive_restrict_iff
#print axioms SM.BoundaryCutSet.consecutive_restrict_iff
#check SM.IntervalComposition.part_consecutive
#print axioms SM.IntervalComposition.part_consecutive
#check SM.IntervalComposition.part_injective
#print axioms SM.IntervalComposition.part_injective
#check SM.IntervalComposition.exists_part_of_consecutive
#print axioms SM.IntervalComposition.exists_part_of_consecutive
#check SM.IntervalComposition.partConsecutiveEquiv
#print axioms SM.IntervalComposition.partConsecutiveEquiv
#check SM.IntervalComposition.consecutive_contained_in_part
#print axioms SM.IntervalComposition.consecutive_contained_in_part
#check SM.IntervalComposition.containing_part_unique
#print axioms SM.IntervalComposition.containing_part_unique
#check SM.IncreasingBoundaryTriple.leftInterval
#print axioms SM.IncreasingBoundaryTriple.leftInterval
#check SM.IncreasingBoundaryTriple.rightInterval
#print axioms SM.IncreasingBoundaryTriple.rightInterval
#check SM.BoundaryCutSet.consecutive_eq_of_left
#print axioms SM.BoundaryCutSet.consecutive_eq_of_left
#check SM.BoundaryCutSet.consecutive_eq_of_right
#print axioms SM.BoundaryCutSet.consecutive_eq_of_right
#check SM.IncreasingBoundaryTriple.eq_of_entries
#print axioms SM.IncreasingBoundaryTriple.eq_of_entries
#check SM.IncreasingBoundaryTriple.eq_of_consecutive_middle
#print axioms SM.IncreasingBoundaryTriple.eq_of_consecutive_middle
#check SM.IntervalComposition.nearTriple_leftInterval
#print axioms SM.IntervalComposition.nearTriple_leftInterval
#check SM.IntervalComposition.nearTriple_rightInterval
#print axioms SM.IntervalComposition.nearTriple_rightInterval
#check SM.IntervalComposition.nearTriple_consecutive
#print axioms SM.IntervalComposition.nearTriple_consecutive
#check SM.IntervalComposition.nearTriple_middle_position
#print axioms SM.IntervalComposition.nearTriple_middle_position
#check SM.IntervalComposition.nearTriple_eq_of_consecutive
#print axioms SM.IntervalComposition.nearTriple_eq_of_consecutive
#check SM.IntervalComposition.refinementInner
#print axioms SM.IntervalComposition.refinementInner
#check SM.IntervalComposition.refinedChildIndex
#print axioms SM.IntervalComposition.refinedChildIndex
#check SM.IntervalComposition.inner_child_consecutive
#print axioms SM.IntervalComposition.inner_child_consecutive
#check SM.IntervalComposition.exists_refined_child
#print axioms SM.IntervalComposition.exists_refined_child
#check SM.IntervalComposition.refinedChildIndex_part
#print axioms SM.IntervalComposition.refinedChildIndex_part
#check SM.IntervalComposition.refinedChildIndex_injective
#print axioms SM.IntervalComposition.refinedChildIndex_injective
#check SM.IntervalComposition.refinedChildIndex_surjective
#print axioms SM.IntervalComposition.refinedChildIndex_surjective
#check SM.IntervalComposition.refinedChildrenEquiv
#print axioms SM.IntervalComposition.refinedChildrenEquiv
#check SM.IntervalComposition.prod_refined_children
#print axioms SM.IntervalComposition.prod_refined_children
#check SM.IntervalComposition.refinementInner_flatten
#print axioms SM.IntervalComposition.refinementInner_flatten
#check SM.IntervalComposition.prod_nested_children
#print axioms SM.IntervalComposition.prod_nested_children
#check SM.IntervalComposition.indexMarks
#print axioms SM.IntervalComposition.indexMarks
#check SM.IntervalComposition.markIndices
#print axioms SM.IntervalComposition.markIndices
#check SM.IntervalComposition.markIndices_indexMarks
#print axioms SM.IntervalComposition.markIndices_indexMarks
#check SM.IntervalComposition.indexMarks_markIndices
#print axioms SM.IntervalComposition.indexMarks_markIndices
#check SM.IntervalComposition.marksIndexEquiv
#print axioms SM.IntervalComposition.marksIndexEquiv
#check SM.IntervalComposition.position_mem_indexMarks
#print axioms SM.IntervalComposition.position_mem_indexMarks
#check SM.IntervalComposition.indexMarks_compl
#print axioms SM.IntervalComposition.indexMarks_compl
#check SM.IntervalComposition.prod_indexMarks
#print axioms SM.IntervalComposition.prod_indexMarks
#check SM.IntervalComposition.prod_markIndices
#print axioms SM.IntervalComposition.prod_markIndices
#check SM.IntervalComposition.sum_all_indexMarks
#print axioms SM.IntervalComposition.sum_all_indexMarks
#check SM.IntervalComposition.RefinementUnmarked
#print axioms SM.IntervalComposition.RefinementUnmarked
#check SM.IntervalComposition.refinedInteriorIndex
#print axioms SM.IntervalComposition.refinedInteriorIndex
#check SM.IntervalComposition.refinedUnmarkedIndex
#print axioms SM.IntervalComposition.refinedUnmarkedIndex
#check SM.BoundaryCutSet.mem_interior_iff
#print axioms SM.BoundaryCutSet.mem_interior_iff
#check SM.IntervalComposition.innerPosition_in_refinement
#print axioms SM.IntervalComposition.innerPosition_in_refinement
#check SM.IntervalComposition.refinedInteriorIndex_position
#print axioms SM.IntervalComposition.refinedInteriorIndex_position
#check SM.IntervalComposition.refinedUnmarkedIndex_injective
#print axioms SM.IntervalComposition.refinedUnmarkedIndex_injective
#check SM.IntervalComposition.refinedUnmarkedIndex_surjective
#print axioms SM.IntervalComposition.refinedUnmarkedIndex_surjective
#check SM.IntervalComposition.refinedUnmarkedEquiv
#print axioms SM.IntervalComposition.refinedUnmarkedEquiv
#check SM.IntervalComposition.inner_nearTriple_transport
#print axioms SM.IntervalComposition.inner_nearTriple_transport
#check SM.IntervalComposition.prod_inner_nearTriples
#print axioms SM.IntervalComposition.prod_inner_nearTriples
#check SM.IntervalComposition.RefinementMarked
#print axioms SM.IntervalComposition.RefinementMarked
#check SM.IntervalComposition.refinedOuterIndex
#print axioms SM.IntervalComposition.refinedOuterIndex
#check SM.IntervalComposition.refinedMarkedIndex
#print axioms SM.IntervalComposition.refinedMarkedIndex
#check SM.IntervalComposition.outerPosition_in_refinement
#print axioms SM.IntervalComposition.outerPosition_in_refinement
#check SM.IntervalComposition.refinedOuterIndex_position
#print axioms SM.IntervalComposition.refinedOuterIndex_position
#check SM.IntervalComposition.refinedMarkedIndex_injective
#print axioms SM.IntervalComposition.refinedMarkedIndex_injective
#check SM.IntervalComposition.refinedMarkedIndex_surjective
#print axioms SM.IntervalComposition.refinedMarkedIndex_surjective
#check SM.IntervalComposition.refinedMarkedEquiv
#print axioms SM.IntervalComposition.refinedMarkedEquiv
#check SM.IntervalComposition.outer_farTriple_transport
#print axioms SM.IntervalComposition.outer_farTriple_transport
#check SM.IntervalComposition.prod_outer_farTriples
#print axioms SM.IntervalComposition.prod_outer_farTriples
#check SM.IntervalComposition.refinementMarks
#print axioms SM.IntervalComposition.refinementMarks
#check SM.IntervalComposition.refinementMarkIndices
#print axioms SM.IntervalComposition.refinementMarkIndices
#check SM.IntervalComposition.mem_refinementMarkIndices
#print axioms SM.IntervalComposition.mem_refinementMarkIndices
#check SM.IntervalComposition.prod_refinementMarked
#print axioms SM.IntervalComposition.prod_refinementMarked
#check SM.IntervalComposition.prod_refinementUnmarked
#print axioms SM.IntervalComposition.prod_refinementUnmarked
#check SM.IntervalComposition.nearFarWeight_near_only
#print axioms SM.IntervalComposition.nearFarWeight_near_only
#check SM.IntervalComposition.nearFarWeight_far_only
#print axioms SM.IntervalComposition.nearFarWeight_far_only
#check SM.IntervalComposition.prod_inner_near_weights
#print axioms SM.IntervalComposition.prod_inner_near_weights
#check SM.IntervalComposition.outer_far_weight
#print axioms SM.IntervalComposition.outer_far_weight
#check SM.IntervalComposition.nested_summand_transport
#print axioms SM.IntervalComposition.nested_summand_transport
#check SM.IntervalComposition.nestedSummand
#print axioms SM.IntervalComposition.nestedSummand
#check SM.IntervalComposition.markedSummand
#print axioms SM.IntervalComposition.markedSummand
#check SM.BoundaryCutSet.marked_transport_val
#print axioms SM.BoundaryCutSet.marked_transport_val
#check SM.IntervalComposition.nestedMarkedCutEquiv_marks
#print axioms SM.IntervalComposition.nestedMarkedCutEquiv_marks
#check SM.IntervalComposition.nestedSummand_eq_markedSummand
#print axioms SM.IntervalComposition.nestedSummand_eq_markedSummand
#check SM.IntervalComposition.sum_markedSummand
#print axioms SM.IntervalComposition.sum_markedSummand
#check SM.nearFar_factorization_coordinate
#print axioms SM.nearFar_factorization_coordinate
#check SM.nearFar_factorization
#print axioms SM.nearFar_factorization
#check SM.farOnlyCoordinates
#print axioms SM.farOnlyCoordinates
#check SM.farOnlyOutput
#print axioms SM.farOnlyOutput
#check SM.nearTransform_of_nearFar_solution
#print axioms SM.nearTransform_of_nearFar_solution
#check SM.reversedFar_output_of_solution
#print axioms SM.reversedFar_output_of_solution
#check SM.complete_output_near_independent
#print axioms SM.complete_output_near_independent
#check SM.farOnlyCoordinates_equation
#print axioms SM.farOnlyCoordinates_equation
#check SM.geometric_farOnly_output
#print axioms SM.geometric_farOnly_output
#check SM.treeCoefficient_farOnly
#print axioms SM.treeCoefficient_farOnly
#check SM.nearFarTransform_leaf
#print axioms SM.nearFarTransform_leaf
#check SM.boundaryUnitArray_leaf
#print axioms SM.boundaryUnitArray_leaf
#check SM.farOnlyCoordinates_leaf
#print axioms SM.farOnlyCoordinates_leaf
#check SM.farOnly_leaf_values
#print axioms SM.farOnly_leaf_values
#check SM.farOnly_nonleaf_E
#print axioms SM.farOnly_nonleaf_E
#check SM.BoundaryInterval.globalPosition
#print axioms SM.BoundaryInterval.globalPosition
#check SM.BoundaryInterval.localPosition
#print axioms SM.BoundaryInterval.localPosition
#check SM.BoundaryInterval.liftInterval
#print axioms SM.BoundaryInterval.liftInterval
#check SM.BoundaryInterval.liftTriple
#print axioms SM.BoundaryInterval.liftTriple
#check SM.IntervalComposition.liftComposition
#print axioms SM.IntervalComposition.liftComposition
#check SM.IntervalComposition.lowerComposition
#print axioms SM.IntervalComposition.lowerComposition
#check SM.restrictTripleArray
#print axioms SM.restrictTripleArray
#check SM.restrictIntervalArray
#print axioms SM.restrictIntervalArray
#check SM.BoundaryInterval.globalPosition_strict
#print axioms SM.BoundaryInterval.globalPosition_strict
#check SM.BoundaryInterval.globalPosition_bounds
#print axioms SM.BoundaryInterval.globalPosition_bounds
#check SM.BoundaryInterval.global_localPosition
#print axioms SM.BoundaryInterval.global_localPosition
#check SM.BoundaryInterval.local_globalPosition
#print axioms SM.BoundaryInterval.local_globalPosition
#check SM.IntervalComposition.eq_of_parts_cut
#print axioms SM.IntervalComposition.eq_of_parts_cut
#check SM.IntervalComposition.cut_bounds
#print axioms SM.IntervalComposition.cut_bounds
#check SM.IntervalComposition.lower_liftComposition
#print axioms SM.IntervalComposition.lower_liftComposition
#check SM.IntervalComposition.lift_lowerComposition
#print axioms SM.IntervalComposition.lift_lowerComposition
#check SM.IntervalComposition.restrictionEquiv
#print axioms SM.IntervalComposition.restrictionEquiv
#check SM.IntervalComposition.liftComposition_part
#print axioms SM.IntervalComposition.liftComposition_part
#check SM.IntervalComposition.liftComposition_nearTriple
#print axioms SM.IntervalComposition.liftComposition_nearTriple
#check SM.IntervalComposition.liftComposition_farTriple
#print axioms SM.IntervalComposition.liftComposition_farTriple
#check SM.nearFarTransform_restrict
#print axioms SM.nearFarTransform_restrict
#check SM.nearFarInverse_restrict
#print axioms SM.nearFarInverse_restrict
#check SM.boundaryUnitArray_restrict
#print axioms SM.boundaryUnitArray_restrict
#check SM.farOnlyCoordinates_restrict
#print axioms SM.farOnlyCoordinates_restrict
#check SM.farOnlyOutput_restrict
#print axioms SM.farOnlyOutput_restrict
#check SM.restrictedWordTuple
#print axioms SM.restrictedWordTuple
#check SM.restrictedWord_boundary
#print axioms SM.restrictedWord_boundary
#check SM.restrictedWord_first_vertex
#print axioms SM.restrictedWord_first_vertex
#check SM.restrictedWord_last_vertex
#print axioms SM.restrictedWord_last_vertex
#check SM.restrictedWord_closing_edge
#print axioms SM.restrictedWord_closing_edge
#check SM.BoundaryInterval.lift_fullInterval
#print axioms SM.BoundaryInterval.lift_fullInterval
#check SM.geometricBoundaryArray_restrictedWord
#print axioms SM.geometricBoundaryArray_restrictedWord
#check SM.farOnlyOutput_restricted_tree
#print axioms SM.farOnlyOutput_restricted_tree
#check SM.farout
#print axioms SM.farout
#print SM.BoundaryCutSet.Consecutive
#print SM.IncreasingBoundaryTriple.leftInterval
#print SM.IncreasingBoundaryTriple.rightInterval
#print SM.IntervalComposition.refinementInner
#print SM.IntervalComposition.refinedChildIndex
#print SM.IntervalComposition.indexMarks
#print SM.IntervalComposition.markIndices
#print SM.IntervalComposition.partConsecutiveEquiv
#print SM.IntervalComposition.refinedChildrenEquiv
#print SM.IntervalComposition.marksIndexEquiv
#print SM.IntervalComposition.RefinementUnmarked
#print SM.IntervalComposition.refinedInteriorIndex
#print SM.IntervalComposition.refinedUnmarkedIndex
#print SM.IntervalComposition.RefinementMarked
#print SM.IntervalComposition.refinedOuterIndex
#print SM.IntervalComposition.refinedMarkedIndex
#print SM.IntervalComposition.refinementMarks
#print SM.IntervalComposition.refinementMarkIndices
#print SM.IntervalComposition.nestedSummand
#print SM.IntervalComposition.markedSummand
#print SM.farOnlyCoordinates
#print SM.farOnlyOutput
#print SM.IntervalComposition.refinedUnmarkedEquiv
#print SM.IntervalComposition.refinedMarkedEquiv
#print SM.BoundaryInterval.globalPosition
#print SM.BoundaryInterval.localPosition
#print SM.BoundaryInterval.liftInterval
#print SM.BoundaryInterval.liftTriple
#print SM.IntervalComposition.liftComposition
#print SM.IntervalComposition.lowerComposition
#print SM.restrictTripleArray
#print SM.restrictIntervalArray
#print SM.restrictedWordTuple
#print SM.IntervalComposition.restrictionEquiv
#print axioms RefinementTransportIndependentReview.actual_parts_are_exact_consecutive_pairs
#print axioms RefinementTransportIndependentReview.actual_fine_child_has_unique_outer
#print axioms RefinementTransportIndependentReview.actual_near_sample_unique
#print axioms RefinementTransportIndependentReview.arbitrary_array_samples_actual_neighbors
#print axioms RefinementTransportIndependentReview.refined_index_keeps_interval
#print axioms RefinementTransportIndependentReview.child_count_is_sum_of_inner_counts
#print axioms RefinementTransportIndependentReview.recovered_inner_has_raw_data
#print axioms RefinementTransportIndependentReview.actual_marked_refinement_child_product
#print axioms RefinementTransportIndependentReview.all_inner_unary_product
#print axioms RefinementTransportIndependentReview.empty_and_full_index_marks
#print axioms RefinementTransportIndependentReview.unmarked_positions_are_exactly_relative
#print axioms RefinementTransportIndependentReview.marked_and_unmarked_product_transport
#print axioms RefinementTransportIndependentReview.all_markings_have_full_cardinality
#print axioms RefinementTransportIndependentReview.unary_marking_sum
#print axioms RefinedWeightsIndependentReview.complete_factor_count
#print axioms RefinedWeightsIndependentReview.inner_near_entries_are_exact
#print axioms RefinedWeightsIndependentReview.outer_far_entries_are_global
#print axioms RefinedWeightsIndependentReview.unary_outer_has_empty_marks
#print axioms RefinedWeightsIndependentReview.identical_outer_and_fine_marks_all
#print axioms RefinedWeightsIndependentReview.raw_family_near_weight_transport
#print axioms RefinedWeightsIndependentReview.raw_full_nested_summand
#print axioms RefinedWeightsIndependentReview.all_unary_inner_coefficients_one
#print axioms RefinedWeightsIndependentReview.raw_marks_match_actual_bijection
#print axioms NearFarFactorizationIndependentReview.inverse_factorization_order
#print axioms NearFarFactorizationIndependentReview.output_independent_with_actual_inverse
#print axioms NearFarFactorizationIndependentReview.inverse_target_E_has_far_only_output
#print axioms NearFarFactorizationIndependentReview.actual_root_all_near_arrays
#print axioms NearFarFactorizationIndependentReview.far_only_output_physical_root_shift
#print axioms NearFarFactorizationIndependentReview.all_interval_E_and_leaf_B_values
#print axioms NearFarFactorizationIndependentReview.unary_marked_sum_retains_coordinate
#print axioms FaroutIndependentReview.all_physical_positions_once
#print axioms FaroutIndependentReview.translated_leaf_count
#print axioms FaroutIndependentReview.all_physical_subintervals
#print axioms FaroutIndependentReview.all_raw_parts_and_cuts
#print axioms FaroutIndependentReview.unary_is_preserved
#print axioms FaroutIndependentReview.complete_composition_cardinality
#print axioms FaroutIndependentReview.actual_child_product
#print axioms FaroutIndependentReview.all_actual_samples
#print axioms FaroutIndependentReview.local_inverse_solves_actual_restriction
#print axioms FaroutIndependentReview.restricted_c_is_actual_local_inverse
#print axioms FaroutIndependentReview.full_contiguous_word_and_directed_root
#print axioms FaroutIndependentReview.nonleaf_has_three_vertices
#print axioms FaroutIndependentReview.local_root_without_global_G1
#print axioms FaroutIndependentReview.aggregate_polynomials_both_directions
#print axioms FaroutIndependentReview.aggregate_factorization_on_every_array
#print axioms FaroutIndependentReview.aggregate_geometry_and_actual_full_root
#print axioms FaroutIndependentReview.aggregate_near_freedom_has_real_solutions
#print axioms FaroutIndependentReview.aggregate_open_leaf_and_nonleaf
