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
