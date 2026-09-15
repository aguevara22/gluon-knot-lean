namespace NearFarRefinementIndependentReview
open SM
noncomputable section
universe u
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

-- The proved geometric b really is the inverse solution of E for every ring.
theorem geometric_open_is_actual_inverse (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    (fun I => (openTreeSum P hP g I : R)) =
      nearFarInverse (geometricBoundaryArray P g) (geometricBoundaryArray P g) boundaryUnitArray := by
  have h := congrArg
    (nearFarInverse (geometricBoundaryArray (R := R) P g) (geometricBoundaryArray P g))
    (geometric_nearFar_open (R := R) P hP g)
  rw [nearFarInverse_transform] at h
  exact h

-- Check the source amplitude with its physical root and actual 0..N interval.
theorem geometric_root_retains_full_transform (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) :
    (treeCoefficient P hP g hn : R) =
      nearFarTransform (geometricBoundaryArray P g) (-geometricBoundaryArray P g)
        (nearFarInverse (geometricBoundaryArray P g) (geometricBoundaryArray P g)
          boundaryUnitArray) (fullBoundaryInterval hn) := by
  rw [geometric_nearFar_root]
  rw [geometric_open_is_actual_inverse]

-- Every subset of interior physical positions corresponds to an actual raw composition.
theorem arbitrary_interior_subset_realized (C : Finset (Fin n))
    (hc : ∀ x ∈ C, I.left < x ∧ x < I.right) :
    ∃ π : IntervalComposition I, π.cutSet.interior.val = C := by
  let s : InteriorCutSet I := ⟨C, hc⟩
  refine ⟨(IntervalComposition.interiorCutSetEquiv I).symm s, ?_⟩
  exact congrArg Subtype.val ((IntervalComposition.interiorCutSetEquiv I).apply_symm_apply s)

-- Existence together with the added uniqueness includes every shared cut.
theorem actual_half_open_partition (π : IntervalComposition I) (x : Fin n)
    (hl : I.left ≤ x) (hr : x < I.right) :
    ∃! k : Fin π.parts, (π.part k).left ≤ x ∧ x < (π.part k).right := by
  obtain ⟨k, hk⟩ := π.exists_halfOpen_part x hl hr
  exact ⟨k, hk, fun l h => π.halfOpen_part_unique x h hk⟩

-- Forward flattening contains exactly the union of the actual raw inner cut maps.
theorem nested_forward_cut_union (π : IntervalComposition I)
    (inner : ∀ k : Fin π.parts, IntervalComposition (π.part k)) (x : Fin n) :
    x ∈ (π.nestedCompositionEquiv inner).val.cuts ↔
      ∃ k, x ∈ (inner k).cutSet.cuts := by
  exact π.mem_flattenCutSets (fun k => (inner k).cutSet) x

-- Reverse restriction recovers each exact raw inner composition, not only cardinalities.
theorem nested_inner_raw_roundtrip (π : IntervalComposition I)
    (inner : ∀ k : Fin π.parts, IntervalComposition (π.part k)) :
    π.nestedCompositionEquiv.symm (π.nestedCompositionEquiv inner) = inner :=
  π.nestedCompositionEquiv.symm_apply_apply inner

-- The final marked bijection returns the actual union and the outer interior cuts.
theorem marked_forward_has_actual_cuts (π : IntervalComposition I)
    (inner : ∀ k : Fin π.parts, IntervalComposition (π.part k)) :
    let output := IntervalComposition.nestedMarkedCutEquiv I ⟨π, inner⟩
    output.1.cutSet = π.flattenCutSets (fun k => (inner k).cutSet) ∧
      output.2.val = π.cutSet.interior.val := by
  constructor
  · exact (π.flattenCutSets (fun k => (inner k).cutSet)).toComposition_cutSet
  · have transport_val {S T : BoundaryCutSet I} (e : S = T) (m : MarkedCuts S) :
        (e ▸ m : MarkedCuts T).val = m.val := by
      cases e
      rfl
    let T := π.flattenCutSets (fun k => (inner k).cutSet)
    let m : MarkedCuts T := ⟨π.cutSet.interior.val,
      (BoundaryCutSet.cuts_subset_iff_interior_subset π.cutSet T).mp
        (π.outer_cuts_subset_flatten (fun k => (inner k).cutSet))⟩
    change (T.toComposition_cutSet.symm ▸ m : MarkedCuts T.toComposition.cutSet).val = _
    exact transport_val T.toComposition_cutSet.symm m

-- Surjectivity retains every selected subset, and its reverse reconstructs raw nested data.
theorem every_marked_refinement_recovered (ρ : IntervalComposition I)
    (m : Finset (Fin n)) (hm : m ⊆ ρ.cutSet.interior.val) :
    IntervalComposition.nestedMarkedCutEquiv I
      ((IntervalComposition.nestedMarkedCutEquiv I).symm ⟨ρ, ⟨m, hm⟩⟩) = ⟨ρ, ⟨m, hm⟩⟩ :=
  (IntervalComposition.nestedMarkedCutEquiv I).apply_symm_apply _

theorem empty_and_full_markings_allowed (ρ : IntervalComposition I) :
    (∃ m : MarkedCuts ρ.cutSet, m.val = ∅) ∧
      ∃ m : MarkedCuts ρ.cutSet, m.val = ρ.cutSet.interior.val := by
  exact ⟨⟨⟨∅, Finset.empty_subset _⟩, rfl⟩, ⟨⟨_, Finset.Subset.refl _⟩, rfl⟩⟩

-- No marks gives the endpoint-only outer composition, with one actual part.
theorem empty_marks_give_unary_outer (T : BoundaryCutSet I) :
    (T.outerFromMarks ⟨∅, Finset.empty_subset _⟩).toComposition.parts = 1 := by
  simp [BoundaryCutSet.outerFromMarks, BoundaryCutSet.ofInterior,
    BoundaryCutSet.toComposition, ne_of_lt I.increasing]

-- Marking every refined interior cut leaves exactly the refined outer composition.
theorem full_marks_recover_refined_outer (ρ : IntervalComposition I) :
    (ρ.cutSet.outerFromMarks ⟨ρ.cutSet.interior.val, Finset.Subset.refl _⟩).toComposition = ρ := by
  have he : ρ.cutSet.outerFromMarks ⟨ρ.cutSet.interior.val, Finset.Subset.refl _⟩ = ρ.cutSet :=
    BoundaryCutSet.ofInterior_interior ρ.cutSet
  rw [he, ρ.cutSet_toComposition]

-- Both sides are the actual complete finite indexing domains of the source sum.
theorem full_nested_and_marked_domains_finite (I : BoundaryInterval n) :
    Finite (Σ π : IntervalComposition I, ∀ k : Fin π.parts, IntervalComposition (π.part k)) ∧
      Finite (Σ ρ : IntervalComposition I, MarkedCuts ρ.cutSet) := by
  exact ⟨inferInstance, inferInstance⟩

-- Every source interior cut position is represented once, with its exact position.
theorem interior_indices_have_exact_coverage (π : IntervalComposition I) (x : Fin n) :
    x ∈ π.cutSet.interior.val ↔ ∃! k : Fin (π.parts - 1), π.interiorPosition k = x := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := (π.mem_interior_iff_exists_index x).mp hx
    exact ⟨k, hk, fun l hl => π.interiorPosition_injective (hl.trans hk.symm)⟩
  · rintro ⟨k, hk, _⟩
    exact (π.mem_interior_iff_exists_index x).mpr ⟨k, hk⟩

-- The unary case has no interior positions, so its marked expansion is one.
theorem unary_has_no_interior_positions (π : IntervalComposition I) (hπ : π.parts = 1) :
    π.cutSet.interior.val = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨k, _⟩ := (π.mem_interior_iff_exists_index x).mp hx
  have := k.isLt
  omega

theorem unary_marked_expansion_equals_one (I : BoundaryInterval n) (D H : TripleArray n R) :
    (∑ marked : Finset (Fin ((IntervalComposition.single I).parts - 1)),
      (∏ k ∈ marked, (-H ((IntervalComposition.single I).farTriple k)) * ⅟ (2 : R)) *
        ∏ k ∈ markedᶜ, D ((IntervalComposition.single I).nearTriple k) * ⅟ (2 : R)) = 1 := by
  rw [← IntervalComposition.nearFarWeight_marked_expansion]
  exact (IntervalComposition.single I).nearFarWeight_one D H rfl

-- Zero near entries select the full marked term; zero far entries select none.
theorem extreme_array_weights (π : IntervalComposition I) (D H : TripleArray n R) :
    π.nearFarWeight 0 H = ∏ k, (-H (π.farTriple k)) * ⅟ (2 : R) ∧
    π.nearFarWeight D 0 = ∏ k, D (π.nearTriple k) * ⅟ (2 : R) := by
  simp [IntervalComposition.nearFarWeight]

end
end NearFarRefinementIndependentReview
