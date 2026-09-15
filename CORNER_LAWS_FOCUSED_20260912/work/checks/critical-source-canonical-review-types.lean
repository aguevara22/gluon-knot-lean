import SM.CriticalSourceResponse
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
set_option pp.universes false

namespace FarOnlyLocalityIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
local instance : DecidableEq (IncreasingBoundaryTriple n) := Classical.decEq _

theorem entire_restricted_c_equal (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t) :
    restrictIntervalArray J (farOnlyCoordinates H₁) = restrictIntervalArray J (farOnlyCoordinates H₂) := by
  rw [farOnlyCoordinates_restrict, farOnlyCoordinates_restrict, restrictTripleArray_eq_of_local J H₁ H₂ h]

theorem every_actual_local_subinterval (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t)
    (K : BoundaryInterval (J.leaves + 1)) :
    farOnlyCoordinates H₁ (J.liftInterval K) = farOnlyCoordinates H₂ (J.liftInterval K) :=
  congrFun (entire_restricted_c_equal J H₁ H₂ h) K

theorem left_gap_unchanged (H₁ H₂ : TripleArray n R) (critical : IncreasingBoundaryTriple n)
    (h : ∀ t : IncreasingBoundaryTriple n, t ≠ critical → H₁ t = H₂ t) :
    farOnlyCoordinates H₁ critical.leftInterval = farOnlyCoordinates H₂ critical.leftInterval := by
  apply farOnlyCoordinates_unchanged_off_critical H₁ H₂ critical h
  intro hc
  have hb := hc.2
  change critical.upper ≤ critical.middle at hb
  exact (not_le_of_gt critical.middle_upper) hb

theorem right_gap_unchanged (H₁ H₂ : TripleArray n R) (critical : IncreasingBoundaryTriple n)
    (h : ∀ t : IncreasingBoundaryTriple n, t ≠ critical → H₁ t = H₂ t) :
    farOnlyCoordinates H₁ critical.rightInterval = farOnlyCoordinates H₂ critical.rightInterval := by
  apply farOnlyCoordinates_unchanged_off_critical H₁ H₂ critical h
  intro hc
  have hb := hc.1
  change critical.middle ≤ critical.lower at hb
  exact (not_le_of_gt critical.lower_middle) hb

theorem every_proper_critical_child (H₁ H₂ : TripleArray n R) (critical : IncreasingBoundaryTriple n)
    (h : ∀ t : IncreasingBoundaryTriple n, t ≠ critical → H₁ t = H₂ t)
    (π : IntervalComposition (⟨critical.lower, critical.upper,
      lt_trans critical.lower_middle critical.middle_upper⟩ : BoundaryInterval n))
    (hp : 2 ≤ π.parts) (k : Fin π.parts) :
    farOnlyCoordinates H₁ (π.part k) = farOnlyCoordinates H₂ (π.part k) := by
  apply farOnlyCoordinates_unchanged_off_critical H₁ H₂ critical h
  intro hc
  have hs := π.part_leaves_lt hp k
  have hl := hc.1
  have hr := hc.2
  change (π.part k).left.val ≤ critical.lower.val at hl
  change critical.upper.val ≤ (π.part k).right.val at hr
  change (π.part k).right.val - (π.part k).left.val < critical.upper.val - critical.lower.val at hs
  omega

theorem leaf_needs_no_array_agreement (J : BoundaryInterval n) (hj : J.leaves = 1)
    (H₁ H₂ : TripleArray n R) : farOnlyCoordinates H₁ J = farOnlyCoordinates H₂ J := by
  rw [farOnlyCoordinates_leaf H₁ J hj, farOnlyCoordinates_leaf H₂ J hj]

theorem arbitrary_critical_update_off_span (H : TripleArray n R) (critical : IncreasingBoundaryTriple n)
    (value : R) (J : BoundaryInterval n)
    (hj : ¬ (J.left ≤ critical.lower ∧ critical.upper ≤ J.right)) :
    farOnlyCoordinates H J = farOnlyCoordinates (Function.update H critical value) J := by
  classical
  apply farOnlyCoordinates_unchanged_off_critical H (Function.update H critical value) critical _ J hj
  intro t ht
  simp [Function.update_of_ne ht]

theorem entire_restricted_output_equal (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t) :
    restrictIntervalArray J (farOnlyOutput H₁) = restrictIntervalArray J (farOnlyOutput H₂) := by
  rw [farOnlyOutput_restrict, farOnlyOutput_restrict, restrictTripleArray_eq_of_local J H₁ H₂ h]

end
end FarOnlyLocalityIndependentReview

namespace CriticalCutIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n]

theorem shared_endpoint_is_exact_intersection (t : IncreasingBoundaryTriple n)
    (L : IntervalComposition t.leftInterval) (R : IntervalComposition t.rightInterval) :
    L.cutSet.cuts ∩ R.cutSet.cuts = {t.middle} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hr⟩
    exact le_antisymm (L.cutSet.bounds x hl).2 (R.cutSet.bounds x hr).1
  · intro hx
    subst x
    exact ⟨L.cutSet.right_mem, R.cutSet.left_mem⟩

theorem left_unary_roundtrip (t : IncreasingBoundaryTriple n)
    (R : IntervalComposition t.rightInterval) :
    t.gapCompositionEquiv (t.gapCompositionEquiv.symm (IntervalComposition.single t.leftInterval, R)) =
      (IntervalComposition.single t.leftInterval, R) := t.gapCompositionEquiv.apply_symm_apply _

theorem right_unary_roundtrip (t : IncreasingBoundaryTriple n)
    (L : IntervalComposition t.leftInterval) :
    t.gapCompositionEquiv (t.gapCompositionEquiv.symm (L, IntervalComposition.single t.rightInterval)) =
      (L, IntervalComposition.single t.rightInterval) := t.gapCompositionEquiv.apply_symm_apply _

theorem all_pairs_are_counted (t : IncreasingBoundaryTriple n) :
    Fintype.card t.MiddleComposition =
      Fintype.card (IntervalComposition t.leftInterval) * Fintype.card (IntervalComposition t.rightInterval) := by
  rw [Fintype.card_congr t.gapCompositionEquiv, Fintype.card_prod]

theorem all_joined_positions_are_exact (t : IncreasingBoundaryTriple n)
    (L : IntervalComposition t.leftInterval) (R : IntervalComposition t.rightInterval) (x : Fin n) :
    x ∈ (t.gapCompositionEquiv.symm (L, R)).val.cutSet.cuts ↔ x ∈ L.cutSet.cuts ∨ x ∈ R.cutSet.cuts := by
  rw [t.gapCompositionEquiv_symm_cuts]
  exact Finset.mem_union

theorem arbitrary_left_right_summands {A : Type*} [AddCommMonoid A]
    (t : IncreasingBoundaryTriple n)
    (f : IntervalComposition t.leftInterval → IntervalComposition t.rightInterval → A) :
    (∑ π : t.MiddleComposition, f (t.gapCompositionEquiv π).1 (t.gapCompositionEquiv π).2) =
      ∑ L : IntervalComposition t.leftInterval, ∑ R : IntervalComposition t.rightInterval, f L R := by
  rw [t.sum_middle_compositions]
  simp only [Equiv.apply_symm_apply]

theorem middle_composition_has_exactly_one_gate (t : IncreasingBoundaryTriple n)
    (π : t.MiddleComposition) :
    2 ≤ π.val.parts ∧ ∃! k : Fin (π.val.parts - 1), π.val.farTriple k = t := by
  have he := (π.val.existsUnique_farTriple_iff t).mpr ⟨rfl, π.property⟩
  refine ⟨?_, he⟩
  obtain ⟨k, _, _⟩ := he
  have hk := k.isLt
  omega

theorem no_critical_far_gate_on_any_other_coordinate {I : BoundaryInterval n}
    (π : IntervalComposition I) (t : IncreasingBoundaryTriple n) (hI : I ≠ t.spanInterval)
    (k : Fin (π.parts - 1)) : π.farTriple k ≠ t := by
  intro he
  exact hI ((π.farTriple_eq_iff k t).mp he).1

theorem no_middle_means_no_critical_gate {I : BoundaryInterval n}
    (π : IntervalComposition I) (t : IncreasingBoundaryTriple n) (hm : t.middle ∉ π.cutSet.cuts)
    (k : Fin (π.parts - 1)) : π.farTriple k ≠ t := by
  intro he
  have hu : ∃! j : Fin (π.parts - 1), π.farTriple j = t :=
    ⟨k, he, fun j hj => π.farTriple_injective (hj.trans he.symm)⟩
  exact hm ((π.existsUnique_farTriple_iff t).mp hu).2

variable {A : Type*} [CommRing A] [Invertible (2 : A)]

theorem unary_far_coefficients_are_one (I : BoundaryInterval n) (H : TripleArray n A) :
    (IntervalComposition.single I).nearFarWeight 0 H = 1 ∧
    (IntervalComposition.single I).nearFarWeight 0 (-H) = 1 :=
  ⟨IntervalComposition.nearFarWeight_one _ _ _ rfl, IntervalComposition.nearFarWeight_one _ _ _ rfl⟩

theorem no_middle_keeps_both_coefficients {I : BoundaryInterval n}
    (π : IntervalComposition I) (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n A)
    (h : ∀ u, u ≠ t → H₁ u = H₂ u) (hm : t.middle ∉ π.cutSet.cuts) :
    π.nearFarWeight 0 H₁ = π.nearFarWeight 0 H₂ ∧
    π.nearFarWeight 0 (-H₁) = π.nearFarWeight 0 (-H₂) :=
  ⟨π.farWeight_unchanged_without_middle t H₁ H₂ h hm,
    π.farWeight_unchanged_without_middle t (-H₁) (-H₂) (fun u hu => congrArg Neg.neg (h u hu)) hm⟩

theorem binary_gate_has_both_delta_signs {I : BoundaryInterval n}
    (π : IntervalComposition I) (hp : π.parts = 2) (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n A) (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (k : Fin (π.parts - 1)) (hk : π.farTriple k = t) :
    π.nearFarWeight 0 H₂ - π.nearFarWeight 0 H₁ = -((H₂ t - H₁ t) * ⅟ (2 : A)) ∧
    π.nearFarWeight 0 (-H₂) - π.nearFarWeight 0 (-H₁) = (H₂ t - H₁ t) * ⅟ (2 : A) := by
  classical
  have he : (Finset.univ : Finset (Fin (π.parts - 1))).erase k = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    apply (Finset.mem_erase.mp hj).1
    apply Fin.ext
    have hjb := j.isLt
    have hkb := k.isLt
    omega
  constructor
  · rw [π.farWeight_difference_at_critical t H₁ H₂ h k hk, he]
    simp only [Finset.prod_empty, mul_one, neg_mul]
  · rw [π.reversedFarWeight_difference_at_critical t H₁ H₂ h k hk, he]
    simp

theorem general_scalar_delta_preserves_all_other_factors {I : BoundaryInterval n}
    (π : IntervalComposition I) (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n A)
    (h : ∀ u, u ≠ t → H₁ u = H₂ u) (k : Fin (π.parts - 1)) (hk : π.farTriple k = t)
    (δ : A) (hd : δ = (H₂ t - H₁ t) * ⅟ (2 : A)) :
    π.nearFarWeight 0 H₂ - π.nearFarWeight 0 H₁ =
      -δ * ∏ j ∈ Finset.univ.erase k, -H₁ (π.farTriple j) * ⅟ (2 : A) ∧
    π.nearFarWeight 0 (-H₂) - π.nearFarWeight 0 (-H₁) =
      δ * ∏ j ∈ Finset.univ.erase k, H₁ (π.farTriple j) * ⅟ (2 : A) := by
  subst δ
  constructor
  · simpa only [neg_mul] using π.farWeight_difference_at_critical t H₁ H₂ h k hk
  · exact π.reversedFarWeight_difference_at_critical t H₁ H₂ h k hk

end
end CriticalCutIndependentReview

namespace GapSplitProductsIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n]

theorem every_raw_left_child_preserved (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition)
    (j : Fin (t.gapCompositionEquiv π).1.parts) :
    ∃ r : Fin π.val.parts, π.val.part r = (t.gapCompositionEquiv π).1.part j := by
  have h := t.gapBaseComposition.exists_refined_child (t.gapRefinement π) (0 : Fin 2) j
  change ∃ r : Fin π.val.cutSet.toComposition.parts,
    π.val.cutSet.toComposition.part r = (t.gapCompositionEquiv π).1.part j at h
  rw [π.val.cutSet_toComposition] at h
  exact h

theorem every_raw_right_child_preserved (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition)
    (j : Fin (t.gapCompositionEquiv π).2.parts) :
    ∃ r : Fin π.val.parts, π.val.part r = (t.gapCompositionEquiv π).2.part j := by
  have h := t.gapBaseComposition.exists_refined_child (t.gapRefinement π) (1 : Fin 2) j
  change ∃ r : Fin π.val.cutSet.toComposition.parts,
    π.val.cutSet.toComposition.part r = (t.gapCompositionEquiv π).2.part j at h
  rw [π.val.cutSet_toComposition] at h
  exact h

variable {R : Type*} [CommMonoid R]

theorem arbitrary_raw_pair_child_product (t : IncreasingBoundaryTriple n)
    (L : IntervalComposition t.leftInterval) (Q : IntervalComposition t.rightInterval)
    (X : BoundaryInterval n → R) :
    (∏ k : Fin (t.gapCompositionEquiv.symm (L,Q)).val.parts,
      X ((t.gapCompositionEquiv.symm (L,Q)).val.part k)) =
      (∏ k : Fin L.parts, X (L.part k)) * ∏ k : Fin Q.parts, X (Q.part k) := by
  have h := t.gapComposition_child_product (t.gapCompositionEquiv.symm (L,Q)) X
  rw [t.gapCompositionEquiv.apply_symm_apply] at h
  exact h

theorem unary_left_keeps_actual_gap_coordinate (t : IncreasingBoundaryTriple n)
    (Q : IntervalComposition t.rightInterval) (X : BoundaryInterval n → R) :
    (∏ k : Fin (t.gapCompositionEquiv.symm (IntervalComposition.single t.leftInterval,Q)).val.parts,
      X ((t.gapCompositionEquiv.symm (IntervalComposition.single t.leftInterval,Q)).val.part k)) =
      X t.leftInterval * ∏ k : Fin Q.parts, X (Q.part k) := by
  rw [arbitrary_raw_pair_child_product, IntervalComposition.single_product]

theorem unary_right_keeps_actual_gap_coordinate (t : IncreasingBoundaryTriple n)
    (L : IntervalComposition t.leftInterval) (X : BoundaryInterval n → R) :
    (∏ k : Fin (t.gapCompositionEquiv.symm (L,IntervalComposition.single t.rightInterval)).val.parts,
      X ((t.gapCompositionEquiv.symm (L,IntervalComposition.single t.rightInterval)).val.part k)) =
      (∏ k : Fin L.parts, X (L.part k)) * X t.rightInterval := by
  rw [arbitrary_raw_pair_child_product, IntervalComposition.single_product]

theorem erased_product_ignores_omitted_value (t : IncreasingBoundaryTriple n) (π : t.MiddleComposition)
    (f g : Fin n → R) (h : ∀ x, x ≠ t.middle → f x = g x) :
    (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, f x) =
      ∏ x ∈ π.val.cutSet.interior.val.erase t.middle, g x := by
  classical
  apply Finset.prod_congr rfl
  intro x hx
  exact h x (Finset.mem_erase.mp hx).1

theorem two_unary_gaps_leave_empty_gate_product (t : IncreasingBoundaryTriple n)
    (π : t.MiddleComposition) (hL : (t.gapCompositionEquiv π).1.parts = 1)
    (hR : (t.gapCompositionEquiv π).2.parts = 1)
    (k : Fin (π.val.parts - 1)) (hk : π.val.interiorPosition k = t.middle) (f : Fin n → R) :
    (∏ j ∈ Finset.univ.erase k, f (π.val.interiorPosition j)) = 1 := by
  letI : IsEmpty (Fin ((t.gapCompositionEquiv π).1.parts - 1)) :=
    ⟨fun j => by have := j.isLt; omega⟩
  letI : IsEmpty (Fin ((t.gapCompositionEquiv π).2.parts - 1)) :=
    ⟨fun j => by have := j.isLt; omega⟩
  rw [t.gapComposition_cut_product_without_middle π k hk]
  simp

end
end GapSplitProductsIndependentReview

namespace GapSplitProductsIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommSemiring R]

theorem zero_middle_annuls_full_sum (t : IncreasingBoundaryTriple n) (f : Fin n → R)
    (X : BoundaryInterval n → R) (hzero : f t.middle = 0) :
    (∑ π : t.MiddleComposition,
      (∏ k : Fin (π.val.parts - 1), f (π.val.interiorPosition k)) *
        ∏ k : Fin π.val.parts, X (π.val.part k)) = 0 := by
  rw [t.middle_weighted_composition_sum, hzero, zero_mul]

theorem erased_sum_keeps_gap_products_when_middle_zero (t : IncreasingBoundaryTriple n)
    (f : Fin n → R) (X : BoundaryInterval n → R) (_hzero : f t.middle = 0) :
    (∑ π : t.MiddleComposition,
      (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, f x) *
        ∏ k : Fin π.val.parts, X (π.val.part k)) =
      (∑ L : IntervalComposition t.leftInterval,
        (∏ k : Fin (L.parts - 1), f (L.interiorPosition k)) * ∏ k : Fin L.parts, X (L.part k)) *
      (∑ Q : IntervalComposition t.rightInterval,
        (∏ k : Fin (Q.parts - 1), f (Q.interiorPosition k)) * ∏ k : Fin Q.parts, X (Q.part k)) :=
  t.middle_erased_weighted_composition_sum f X

theorem erased_sum_ignores_any_middle_change (t : IncreasingBoundaryTriple n)
    (f g : Fin n → R) (h : ∀ x, x ≠ t.middle → f x = g x) (X : BoundaryInterval n → R) :
    (∑ π : t.MiddleComposition,
      (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, f x) * ∏ k : Fin π.val.parts, X (π.val.part k)) =
    (∑ π : t.MiddleComposition,
      (∏ x ∈ π.val.cutSet.interior.val.erase t.middle, g x) * ∏ k : Fin π.val.parts, X (π.val.part k)) := by
  classical
  apply Finset.sum_congr rfl
  intro π _
  rw [erased_product_ignores_omitted_value t π f g h]

end
end GapSplitProductsIndependentReview

namespace CriticalSourceIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
local instance : DecidableEq (IncreasingBoundaryTriple n) := Classical.decEq _

theorem fixed_coefficients_retain_unary_change (H : TripleArray n R) (X₁ X₂ : IntervalArray n R)
    (I : BoundaryInterval n)
    (hX : ∀ π : IntervalComposition I, 2 ≤ π.parts → ∀ k : Fin π.parts, X₁ (π.part k) = X₂ (π.part k)) :
    farTransform H X₂ I - farTransform H X₁ I = X₂ I - X₁ I := by
  rw [farTransform_difference_of_proper_children H H X₁ X₂ I hX]
  simp

theorem coefficient_sum_is_actual_fixed_input_difference (H₁ H₂ : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    coefficientDifferenceSum H₁ H₂ X I = farTransform H₂ X I - farTransform H₁ X I := by
  simp only [coefficientDifferenceSum, farTransform, nearFarTransform, sub_mul, Finset.sum_sub_distrib]

theorem actual_critical_middle_gate (t : IncreasingBoundaryTriple n) (H : TripleArray n R) :
    t.fixedFarGate H t.middle = -H t * ⅟ (2 : R) := by
  rw [IncreasingBoundaryTriple.fixedFarGate, dif_pos ⟨t.lower_middle,t.middle_upper⟩]

theorem unused_fixed_gate_positions_are_zero (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (x : Fin n) (h : ¬ (t.lower < x ∧ x < t.upper)) : t.fixedFarGate H x = 0 := by
  rw [IncreasingBoundaryTriple.fixedFarGate, dif_neg h]

theorem actual_full_span_gate_sum (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (X : IntervalArray n R) : cutWeightedSum (t.fixedFarGate H) X t.spanInterval = farTransform H X t.spanInterval :=
  cutWeightedSum_eq_farTransform _ _ _ _ (t.fixedFarGate_at_interior H)

theorem both_responses_vanish_when_critical_value_unchanged (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) (ht : H₂ t = H₁ t) :
    farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval = 0 ∧
    farOnlyOutput H₂ t.spanInterval - farOnlyOutput H₁ t.spanInterval = 0 := by
  constructor
  · rw [critical_inverse_source_jump H₁ H₂ t h, ht]
    simp
  · rw [critical_output_source_jump H₁ H₂ t h, ht]
    simp

theorem reversed_orientation_uses_new_baseline (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    farOnlyCoordinates H₁ t.spanInterval - farOnlyCoordinates H₂ t.spanInterval =
      -((H₂ t - H₁ t) * ⅟ (2 : R)) *
        (cutWeightedSum (t.fixedFarGate H₂) (farOnlyCoordinates H₂) t.leftInterval *
         cutWeightedSum (t.fixedFarGate H₂) (farOnlyCoordinates H₂) t.rightInterval) := by
  rw [critical_inverse_source_jump H₂ H₁ t (fun u hu => (h u hu).symm)]
  ring

theorem arbitrary_single_entry_update_has_actual_inverse_response (H : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (v : R) :
    farOnlyCoordinates (Function.update H t v) t.spanInterval - farOnlyCoordinates H t.spanInterval =
      ((v - H t) * ⅟ (2 : R)) *
        (cutWeightedSum (t.fixedFarGate H) (farOnlyCoordinates H) t.leftInterval *
         cutWeightedSum (t.fixedFarGate H) (farOnlyCoordinates H) t.rightInterval) := by
  have h : ∀ u, u ≠ t → H u = Function.update H t v u := by
    intro u hu
    simp [Function.update_of_ne hu]
  simpa only [Function.update_self] using critical_inverse_source_jump H (Function.update H t v) t h

theorem output_is_reversed_minus_ordinary_coefficient_response (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    farOnlyOutput H₂ t.spanInterval - farOnlyOutput H₁ t.spanInterval =
      coefficientDifferenceSum (-H₁) (-H₂) (farOnlyCoordinates H₁) t.spanInterval -
        coefficientDifferenceSum H₁ H₂ (farOnlyCoordinates H₁) t.spanInterval := by
  rw [critical_output_difference H₁ H₂ t h, critical_inverse_difference H₁ H₂ t h,
    ← coefficientDifferenceSum_eq_nonunary H₁ H₂ (farOnlyCoordinates H₁) t.spanInterval,
    ← coefficientDifferenceSum_eq_nonunary (-H₁) (-H₂) (farOnlyCoordinates H₁) t.spanInterval]
  ring

theorem arbitrary_delta_has_positive_inverse_and_both_output_terms (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (δ : R) (hd : δ = (H₂ t - H₁ t) * ⅟ (2 : R)) :
    farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval =
      δ * (cutWeightedSum (t.fixedFarGate H₁) (farOnlyCoordinates H₁) t.leftInterval *
        cutWeightedSum (t.fixedFarGate H₁) (farOnlyCoordinates H₁) t.rightInterval) ∧
    farOnlyOutput H₂ t.spanInterval - farOnlyOutput H₁ t.spanInterval =
      δ * ((cutWeightedSum (t.fixedFarGate H₁) (farOnlyCoordinates H₁) t.leftInterval *
          cutWeightedSum (t.fixedFarGate H₁) (farOnlyCoordinates H₁) t.rightInterval) +
        (cutWeightedSum (t.fixedFarGate (-H₁)) (farOnlyCoordinates H₁) t.leftInterval *
          cutWeightedSum (t.fixedFarGate (-H₁)) (farOnlyCoordinates H₁) t.rightInterval)) := by
  subst δ
  exact ⟨critical_inverse_source_jump H₁ H₂ t h, critical_output_source_jump H₁ H₂ t h⟩

end
end CriticalSourceIndependentReview

#check SM.IncreasingBoundaryTriple.MiddleCutSet
#print axioms SM.IncreasingBoundaryTriple.MiddleCutSet
#check SM.IncreasingBoundaryTriple.MiddleComposition
#print axioms SM.IncreasingBoundaryTriple.MiddleComposition
#check SM.IncreasingBoundaryTriple.spanInterval
#print axioms SM.IncreasingBoundaryTriple.spanInterval
#check SM.IncreasingBoundaryTriple.joinGapCuts
#print axioms SM.IncreasingBoundaryTriple.joinGapCuts
#check SM.IncreasingBoundaryTriple.splitGapCuts
#print axioms SM.IncreasingBoundaryTriple.splitGapCuts
#check SM.IncreasingBoundaryTriple.split_joinGapCuts
#print axioms SM.IncreasingBoundaryTriple.split_joinGapCuts
#check SM.IncreasingBoundaryTriple.join_splitGapCuts
#print axioms SM.IncreasingBoundaryTriple.join_splitGapCuts
#check SM.IncreasingBoundaryTriple.gapCutEquiv
#print axioms SM.IncreasingBoundaryTriple.gapCutEquiv
#check SM.IncreasingBoundaryTriple.middleCompositionCutEquiv
#print axioms SM.IncreasingBoundaryTriple.middleCompositionCutEquiv
#check SM.IncreasingBoundaryTriple.gapCompositionEquiv
#print axioms SM.IncreasingBoundaryTriple.gapCompositionEquiv
#check SM.IncreasingBoundaryTriple.gapCompositionEquiv_left_cuts
#print axioms SM.IncreasingBoundaryTriple.gapCompositionEquiv_left_cuts
#check SM.IncreasingBoundaryTriple.gapCompositionEquiv_right_cuts
#print axioms SM.IncreasingBoundaryTriple.gapCompositionEquiv_right_cuts
#check SM.IncreasingBoundaryTriple.gapCompositionEquiv_symm_cuts
#print axioms SM.IncreasingBoundaryTriple.gapCompositionEquiv_symm_cuts
#check SM.IncreasingBoundaryTriple.sum_middle_compositions
#print axioms SM.IncreasingBoundaryTriple.sum_middle_compositions
#check SM.restrictTripleArray_eq_of_local
#print axioms SM.restrictTripleArray_eq_of_local
#check SM.farOnlyCoordinates_local
#print axioms SM.farOnlyCoordinates_local
#check SM.farOnlyCoordinates_unchanged_off_critical
#print axioms SM.farOnlyCoordinates_unchanged_off_critical
#check SM.IntervalComposition.farTriple_eq_iff
#print axioms SM.IntervalComposition.farTriple_eq_iff
#check SM.IntervalComposition.farTriple_injective
#print axioms SM.IntervalComposition.farTriple_injective
#check SM.IntervalComposition.existsUnique_farTriple_iff
#print axioms SM.IntervalComposition.existsUnique_farTriple_iff
#check SM.IntervalComposition.farWeight_unchanged_off_span
#print axioms SM.IntervalComposition.farWeight_unchanged_off_span
#check SM.IntervalComposition.farWeight_unchanged_without_middle
#print axioms SM.IntervalComposition.farWeight_unchanged_without_middle
#check SM.IntervalComposition.farWeight_difference_at_critical
#print axioms SM.IntervalComposition.farWeight_difference_at_critical
#check SM.IntervalComposition.reversedFarWeight_difference_at_critical
#print axioms SM.IntervalComposition.reversedFarWeight_difference_at_critical
#check SM.IntervalComposition.prod_interiorPositions
#print axioms SM.IntervalComposition.prod_interiorPositions
#check SM.IntervalComposition.prod_interiorPositions_erase
#print axioms SM.IntervalComposition.prod_interiorPositions_erase
#check SM.IncreasingBoundaryTriple.gapBaseComposition
#print axioms SM.IncreasingBoundaryTriple.gapBaseComposition
#check SM.IncreasingBoundaryTriple.gapRefinement
#print axioms SM.IncreasingBoundaryTriple.gapRefinement
#check SM.IncreasingBoundaryTriple.gapComposition_child_product
#print axioms SM.IncreasingBoundaryTriple.gapComposition_child_product
#check SM.IncreasingBoundaryTriple.gapComposition_interior_union
#print axioms SM.IncreasingBoundaryTriple.gapComposition_interior_union
#check SM.IncreasingBoundaryTriple.gapComposition_interiors_disjoint
#print axioms SM.IncreasingBoundaryTriple.gapComposition_interiors_disjoint
#check SM.IncreasingBoundaryTriple.middle_not_gap_interiors
#print axioms SM.IncreasingBoundaryTriple.middle_not_gap_interiors
#check SM.IncreasingBoundaryTriple.gapComposition_cut_product
#print axioms SM.IncreasingBoundaryTriple.gapComposition_cut_product
#check SM.IncreasingBoundaryTriple.gapComposition_cut_product_without_middle
#print axioms SM.IncreasingBoundaryTriple.gapComposition_cut_product_without_middle
#check SM.IncreasingBoundaryTriple.middle_weighted_composition_sum
#print axioms SM.IncreasingBoundaryTriple.middle_weighted_composition_sum
#check SM.IncreasingBoundaryTriple.middle_erased_weighted_composition_sum
#print axioms SM.IncreasingBoundaryTriple.middle_erased_weighted_composition_sum
#check SM.farTransform_difference_of_proper_children
#print axioms SM.farTransform_difference_of_proper_children
#check SM.critical_proper_child_coordinates
#print axioms SM.critical_proper_child_coordinates
#check SM.critical_inverse_difference
#print axioms SM.critical_inverse_difference
#check SM.critical_output_difference
#print axioms SM.critical_output_difference
#check SM.cutWeightedSum
#print axioms SM.cutWeightedSum
#check SM.cutWeightedSum_eq_farTransform
#print axioms SM.cutWeightedSum_eq_farTransform
#check SM.IncreasingBoundaryTriple.fixedFarGate
#print axioms SM.IncreasingBoundaryTriple.fixedFarGate
#check SM.IncreasingBoundaryTriple.fixedFarGate_at_interior
#print axioms SM.IncreasingBoundaryTriple.fixedFarGate_at_interior
#check SM.IncreasingBoundaryTriple.fixedFarGate_neg
#print axioms SM.IncreasingBoundaryTriple.fixedFarGate_neg
#check SM.IncreasingBoundaryTriple.fixedFarGate_weight
#print axioms SM.IncreasingBoundaryTriple.fixedFarGate_weight
#check SM.IncreasingBoundaryTriple.farWeight_difference_physical
#print axioms SM.IncreasingBoundaryTriple.farWeight_difference_physical
#check SM.coefficientDifferenceSum
#print axioms SM.coefficientDifferenceSum
#check SM.coefficientDifferenceSum_eq_nonunary
#print axioms SM.coefficientDifferenceSum_eq_nonunary
#check SM.coefficientDifferenceSum_span
#print axioms SM.coefficientDifferenceSum_span
#check SM.coefficientDifferenceSum_span_reversed
#print axioms SM.coefficientDifferenceSum_span_reversed
#check SM.critical_inverse_source_jump
#print axioms SM.critical_inverse_source_jump
#check SM.critical_output_source_jump
#print axioms SM.critical_output_source_jump
#print SM.IncreasingBoundaryTriple.spanInterval
#print SM.IncreasingBoundaryTriple.MiddleCutSet
#print SM.IncreasingBoundaryTriple.MiddleComposition
#print SM.IncreasingBoundaryTriple.joinGapCuts
#print SM.IncreasingBoundaryTriple.splitGapCuts
#print SM.IncreasingBoundaryTriple.gapCutEquiv
#print SM.IncreasingBoundaryTriple.middleCompositionCutEquiv
#print SM.IncreasingBoundaryTriple.gapCompositionEquiv
#print SM.IntervalComposition.farTriple
#print SM.IntervalComposition.interiorPosition
#print SM.IntervalComposition.nearFarWeight
#print SM.IncreasingBoundaryTriple.gapBaseComposition
#print SM.IncreasingBoundaryTriple.gapRefinement
#print SM.farOnlyCoordinates
#print SM.farOnlyOutput
#print SM.cutWeightedSum
#print SM.IncreasingBoundaryTriple.fixedFarGate
#print SM.coefficientDifferenceSum
#print axioms FarOnlyLocalityIndependentReview.entire_restricted_c_equal
#print axioms FarOnlyLocalityIndependentReview.every_actual_local_subinterval
#print axioms FarOnlyLocalityIndependentReview.left_gap_unchanged
#print axioms FarOnlyLocalityIndependentReview.right_gap_unchanged
#print axioms FarOnlyLocalityIndependentReview.every_proper_critical_child
#print axioms FarOnlyLocalityIndependentReview.leaf_needs_no_array_agreement
#print axioms FarOnlyLocalityIndependentReview.arbitrary_critical_update_off_span
#print axioms FarOnlyLocalityIndependentReview.entire_restricted_output_equal
#print axioms CriticalCutIndependentReview.shared_endpoint_is_exact_intersection
#print axioms CriticalCutIndependentReview.left_unary_roundtrip
#print axioms CriticalCutIndependentReview.right_unary_roundtrip
#print axioms CriticalCutIndependentReview.all_pairs_are_counted
#print axioms CriticalCutIndependentReview.all_joined_positions_are_exact
#print axioms CriticalCutIndependentReview.arbitrary_left_right_summands
#print axioms CriticalCutIndependentReview.middle_composition_has_exactly_one_gate
#print axioms CriticalCutIndependentReview.no_critical_far_gate_on_any_other_coordinate
#print axioms CriticalCutIndependentReview.no_middle_means_no_critical_gate
#print axioms CriticalCutIndependentReview.unary_far_coefficients_are_one
#print axioms CriticalCutIndependentReview.no_middle_keeps_both_coefficients
#print axioms CriticalCutIndependentReview.binary_gate_has_both_delta_signs
#print axioms CriticalCutIndependentReview.general_scalar_delta_preserves_all_other_factors
#print axioms GapSplitProductsIndependentReview.every_raw_left_child_preserved
#print axioms GapSplitProductsIndependentReview.every_raw_right_child_preserved
#print axioms GapSplitProductsIndependentReview.arbitrary_raw_pair_child_product
#print axioms GapSplitProductsIndependentReview.unary_left_keeps_actual_gap_coordinate
#print axioms GapSplitProductsIndependentReview.unary_right_keeps_actual_gap_coordinate
#print axioms GapSplitProductsIndependentReview.erased_product_ignores_omitted_value
#print axioms GapSplitProductsIndependentReview.two_unary_gaps_leave_empty_gate_product
#print axioms GapSplitProductsIndependentReview.zero_middle_annuls_full_sum
#print axioms GapSplitProductsIndependentReview.erased_sum_keeps_gap_products_when_middle_zero
#print axioms GapSplitProductsIndependentReview.erased_sum_ignores_any_middle_change
#print axioms CriticalSourceIndependentReview.fixed_coefficients_retain_unary_change
#print axioms CriticalSourceIndependentReview.coefficient_sum_is_actual_fixed_input_difference
#print axioms CriticalSourceIndependentReview.actual_critical_middle_gate
#print axioms CriticalSourceIndependentReview.unused_fixed_gate_positions_are_zero
#print axioms CriticalSourceIndependentReview.actual_full_span_gate_sum
#print axioms CriticalSourceIndependentReview.both_responses_vanish_when_critical_value_unchanged
#print axioms CriticalSourceIndependentReview.reversed_orientation_uses_new_baseline
#print axioms CriticalSourceIndependentReview.arbitrary_single_entry_update_has_actual_inverse_response
#print axioms CriticalSourceIndependentReview.output_is_reversed_minus_ordinary_coefficient_response
#print axioms CriticalSourceIndependentReview.arbitrary_delta_has_positive_inverse_and_both_output_terms
