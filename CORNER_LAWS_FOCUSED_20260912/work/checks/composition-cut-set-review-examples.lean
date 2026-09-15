namespace CompositionCutSetIndependentReview
open SM
variable {n : ℕ} [NeZero n]

def endpointSet (I : BoundaryInterval n) : BoundaryCutSet I where
  cuts := {I.left, I.right}
  left_mem := by simp
  right_mem := by simp
  bounds := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact ⟨by simp [I.increasing.le], by simp [I.increasing.le]⟩

def fullCutSet (I : BoundaryInterval n) : BoundaryCutSet I where
  cuts := Finset.Icc I.left I.right
  left_mem := Finset.mem_Icc.mpr ⟨le_rfl, I.increasing.le⟩
  right_mem := Finset.mem_Icc.mpr ⟨I.increasing.le, le_rfl⟩
  bounds := fun _ hx => Finset.mem_Icc.mp hx

-- No bounded endpoint-containing finite cut set is omitted.
theorem every_raw_cut_set_admitted (I : BoundaryInterval n) (C : Finset (Fin n))
    (hl : I.left ∈ C) (hr : I.right ∈ C)
    (hb : ∀ x ∈ C, I.left ≤ x ∧ x ≤ I.right) :
    ∃ π : IntervalComposition I, π.cutSet.cuts = C ∧ π.parts + 1 = C.card := by
  let S : BoundaryCutSet I := ⟨C, hl, hr, hb⟩
  refine ⟨S.toComposition, ?_, ?_⟩
  · exact congrArg BoundaryCutSet.cuts S.toComposition_cutSet
  · have hs := congrArg (fun T : BoundaryCutSet I => T.cuts.card) S.toComposition_cutSet
    rw [IntervalComposition.cutSet_card] at hs
    exact hs

theorem unary_cut_set_is_exactly_endpoints (I : BoundaryInterval n) :
    (IntervalComposition.single I).cutSet = endpointSet I ∧
      (endpointSet I).toComposition = IntervalComposition.single I := by
  have hp : (endpointSet I).toComposition.parts = 1 := by
    simp [BoundaryCutSet.toComposition, endpointSet, ne_of_lt I.increasing]
  have he := (endpointSet I).toComposition.eq_single_of_parts_eq_one hp
  refine ⟨?_, he⟩
  rw [← he]
  exact (endpointSet I).toComposition_cutSet

-- Full cuts are allowed, have maximal source arity, and retain every position.
theorem full_cut_coverage (I : BoundaryInterval n) :
    (fullCutSet I).toComposition.cutSet.cuts = Finset.Icc I.left I.right ∧
      (fullCutSet I).toComposition.parts = I.leaves := by
  constructor
  · exact congrArg BoundaryCutSet.cuts (fullCutSet I).toComposition_cutSet
  · simp only [BoundaryCutSet.toComposition, fullCutSet, Fin.card_Icc, BoundaryInterval.leaves]
    have := I.increasing
    change I.right.val + 1 - I.left.val - 1 = I.right.val - I.left.val
    omega

-- Sorted reconstruction has all and only the original cuts.
theorem exact_cut_membership (I : BoundaryInterval n) (S : BoundaryCutSet I) (x : Fin n) :
    (∃ k, S.toComposition.cut k = x) ↔ x ∈ S.cuts := by
  have hs := congrArg BoundaryCutSet.cuts S.toComposition_cutSet
  change Finset.univ.image S.toComposition.cut = S.cuts at hs
  rw [← hs]
  simp

-- Full raw composition data, including its natural part count and dependent
-- cut function, are recovered rather than only an equal cardinality.
theorem complete_raw_roundtrip (I : BoundaryInterval n) (π : IntervalComposition I) :
    π.cutSet.toComposition.parts = π.parts ∧ HEq π.cutSet.toComposition.cut π.cut := by
  rw [π.cutSet_toComposition]
  exact ⟨rfl, HEq.rfl⟩

theorem same_cut_set_iff_same_composition (I : BoundaryInterval n)
    (π ρ : IntervalComposition I) : π.cutSet.cuts = ρ.cutSet.cuts ↔ π = ρ := by
  constructor
  · intro h
    exact IntervalComposition.cutSet_injective (BoundaryCutSet.ext _ _ h)
  · rintro rfl
    rfl

end CompositionCutSetIndependentReview
