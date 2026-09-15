namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- A far sample has the actual coordinate endpoints and its actual interior
cut. These three positions completely determine whether it is critical. -/
theorem farTriple_eq_iff (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) (t : IncreasingBoundaryTriple n) :
    π.farTriple k = t ↔ I = t.spanInterval ∧ π.interiorPosition k = t.middle := by
  constructor
  · intro h
    exact ⟨BoundaryInterval.eq_of_endpoints
      (congrArg IncreasingBoundaryTriple.lower h)
      (congrArg IncreasingBoundaryTriple.upper h),
      congrArg IncreasingBoundaryTriple.middle h⟩
  · rintro ⟨hI, hm⟩
    exact IncreasingBoundaryTriple.eq_of_entries
      (congrArg BoundaryInterval.left hI) hm (congrArg BoundaryInterval.right hI)

/-- Distinct interior cuts cannot give the same far triple. -/
theorem farTriple_injective (π : IntervalComposition I) : Function.Injective π.farTriple := by
  intro k l h
  exact π.interiorPosition_injective (congrArg IncreasingBoundaryTriple.middle h)

/-- A critical triple occurs exactly once precisely when the coordinate is
its full span and the raw composition actually cuts at its middle position. -/
theorem existsUnique_farTriple_iff (π : IntervalComposition I) (t : IncreasingBoundaryTriple n) :
    (∃! k : Fin (π.parts - 1), π.farTriple k = t) ↔
      I = t.spanInterval ∧ t.middle ∈ π.cutSet.cuts := by
  constructor
  · rintro ⟨k, hk, _⟩
    have he := (π.farTriple_eq_iff k t).mp hk
    refine ⟨he.1, ?_⟩
    have hm := π.interiorPosition_mem k
    rw [he.2] at hm
    exact (BoundaryCutSet.mem_interior_iff π.cutSet t.middle).mp hm |>.1
  · rintro ⟨hI, hm⟩
    have hbounds : I.left < t.middle ∧ t.middle < I.right := by
      rw [hI]
      exact ⟨t.lower_middle, t.middle_upper⟩
    have hi : t.middle ∈ π.cutSet.interior.val :=
      (BoundaryCutSet.mem_interior_iff π.cutSet t.middle).mpr ⟨hm, hbounds⟩
    obtain ⟨k, hk⟩ := (π.mem_interior_iff_exists_index t.middle).mp hi
    have ht : π.farTriple k = t := (π.farTriple_eq_iff k t).mpr ⟨hI, hk⟩
    exact ⟨k, ht, fun l hl => π.farTriple_injective (hl.trans ht.symm)⟩

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- On every other coordinate the entire far coefficient is unchanged,
even when the interval contains the critical span as a proper subinterval. -/
theorem farWeight_unchanged_off_span (π : IntervalComposition I)
    (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n R)
    (h : ∀ u, u ≠ t → H₁ u = H₂ u) (hI : I ≠ t.spanInterval) :
    π.nearFarWeight 0 H₁ = π.nearFarWeight 0 H₂ := by
  rw [nearFarWeight_far_only, nearFarWeight_far_only]
  apply Finset.prod_congr rfl
  intro k _
  rw [h (π.farTriple k) (fun hk => hI ((π.farTriple_eq_iff k t).mp hk).1)]

/-- In the critical coordinate, a composition with no middle cut also has
unchanged coefficient. Unary compositions are included by this statement. -/
theorem farWeight_unchanged_without_middle (π : IntervalComposition I)
    (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n R)
    (h : ∀ u, u ≠ t → H₁ u = H₂ u) (hm : t.middle ∉ π.cutSet.cuts) :
    π.nearFarWeight 0 H₁ = π.nearFarWeight 0 H₂ := by
  rw [nearFarWeight_far_only, nearFarWeight_far_only]
  apply Finset.prod_congr rfl
  intro k _
  have ht : π.farTriple k ≠ t := by
    intro hk
    have hi := π.interiorPosition_mem k
    rw [((π.farTriple_eq_iff k t).mp hk).2] at hi
    exact hm ((BoundaryCutSet.mem_interior_iff π.cutSet t.middle).mp hi).1
  rw [h (π.farTriple k) ht]

/-- Compute the ordinary coefficient change by removing exactly its one
changing gate. Every remaining factor is proved equal across the two arrays. -/
theorem farWeight_difference_at_critical (π : IntervalComposition I)
    (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n R)
    (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (k : Fin (π.parts - 1)) (hk : π.farTriple k = t) :
    π.nearFarWeight 0 H₂ - π.nearFarWeight 0 H₁ =
      (-(H₂ t - H₁ t) * ⅟ (2 : R)) *
        ∏ j ∈ (Finset.univ.erase k), -H₁ (π.farTriple j) * ⅟ (2 : R) := by
  classical
  have hp : (∏ j ∈ Finset.univ.erase k, -H₂ (π.farTriple j) * ⅟ (2 : R)) =
      ∏ j ∈ Finset.univ.erase k, -H₁ (π.farTriple j) * ⅟ (2 : R) := by
    apply Finset.prod_congr rfl
    intro j hj
    have ht : π.farTriple j ≠ t := by
      intro he
      exact (Finset.mem_erase.mp hj).1 (π.farTriple_injective (he.trans hk.symm))
    rw [h (π.farTriple j) ht]
  rw [nearFarWeight_far_only, nearFarWeight_far_only]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => -H₂ (π.farTriple j) * ⅟ (2 : R))
    (Finset.mem_univ k)]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => -H₁ (π.farTriple j) * ⅟ (2 : R))
    (Finset.mem_univ k)]
  rw [hk, hp]
  ring

/-- The reversed-far coefficient change is calculated separately. Its
changing gate has the opposite sign, and every retained factor is reversed. -/
theorem reversedFarWeight_difference_at_critical (π : IntervalComposition I)
    (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n R)
    (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (k : Fin (π.parts - 1)) (hk : π.farTriple k = t) :
    π.nearFarWeight 0 (-H₂) - π.nearFarWeight 0 (-H₁) =
      ((H₂ t - H₁ t) * ⅟ (2 : R)) *
        ∏ j ∈ (Finset.univ.erase k), H₁ (π.farTriple j) * ⅟ (2 : R) := by
  have he := π.farWeight_difference_at_critical t (-H₁) (-H₂)
    (fun u hu => congrArg Neg.neg (h u hu)) k hk
  simpa only [Pi.neg_apply, neg_neg, neg_sub_neg, neg_sub] using he

end
end SM.IntervalComposition
