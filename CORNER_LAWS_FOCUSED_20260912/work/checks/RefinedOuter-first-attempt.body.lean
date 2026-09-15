namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- Fine interior indices that are cuts of the outer composition. -/
abbrev RefinementMarked (π : IntervalComposition I) (T : RefiningCutSet π) :=
  {r : Fin (T.val.toComposition.parts - 1) //
    T.val.toComposition.interiorPosition r ∈ π.cutSet.cuts}

/-- Every outer interior cut remains a fine interior cut, with both global
endpoints fixed by the source interval. -/
theorem outerPosition_in_refinement (π : IntervalComposition I) (T : RefiningCutSet π)
    (j : Fin (π.parts - 1)) : π.interiorPosition j ∈ T.val.interior.val :=
  (BoundaryCutSet.cuts_subset_iff_interior_subset π.cutSet T.val).mp T.property
    (π.interiorPosition_mem j)

def refinedOuterIndex (π : IntervalComposition I) (T : RefiningCutSet π)
    (j : Fin (π.parts - 1)) : Fin (T.val.toComposition.parts - 1) :=
  T.val.toComposition.interiorPositionEquiv.symm ⟨π.interiorPosition j, by
    rw [BoundaryCutSet.toComposition_cutSet]
    exact π.outerPosition_in_refinement T j⟩

theorem refinedOuterIndex_position (π : IntervalComposition I) (T : RefiningCutSet π)
    (j : Fin (π.parts - 1)) :
    T.val.toComposition.interiorPosition (π.refinedOuterIndex T j) = π.interiorPosition j := by
  exact congrArg
    (fun y : {x : Fin n // x ∈ T.val.toComposition.cutSet.interior.val} => y.val)
    (T.val.toComposition.interiorPositionEquiv.apply_symm_apply _)

def refinedMarkedIndex (π : IntervalComposition I) (T : RefiningCutSet π)
    (j : Fin (π.parts - 1)) : RefinementMarked π T :=
  ⟨π.refinedOuterIndex T j, by
    rw [π.refinedOuterIndex_position T j]
    exact ((π.cutSet.mem_interior_iff _).mp (π.interiorPosition_mem j)).1⟩

theorem refinedMarkedIndex_injective (π : IntervalComposition I) (T : RefiningCutSet π) :
    Function.Injective (π.refinedMarkedIndex T) := by
  intro j l h
  have hi : π.refinedOuterIndex T j = π.refinedOuterIndex T l :=
    congrArg (fun r : RefinementMarked π T => r.val) h
  apply π.interiorPosition_injective
  rw [← π.refinedOuterIndex_position T j, ← π.refinedOuterIndex_position T l, hi]

/-- A marked fine cut is a genuine outer interior cut, not a global
endpoint; hence it occurs exactly once in the outer index domain. -/
theorem refinedMarkedIndex_surjective (π : IntervalComposition I) (T : RefiningCutSet π) :
    Function.Surjective (π.refinedMarkedIndex T) := by
  intro r
  let x := T.val.toComposition.interiorPosition r.val
  have hx := T.val.toComposition.interiorPosition_mem r.val
  have hb := T.val.toComposition.cutSet.interior.property x hx
  have ho : x ∈ π.cutSet.interior.val := (π.cutSet.mem_interior_iff x).mpr ⟨r.property, hb⟩
  obtain ⟨j, hj⟩ := (π.mem_interior_iff_exists_index x).mp ho
  refine ⟨j, ?_⟩
  apply Subtype.ext
  apply T.val.toComposition.interiorPosition_injective
  rw [show (π.refinedMarkedIndex T j).val = π.refinedOuterIndex T j from rfl,
    π.refinedOuterIndex_position T j]
  exact hj

/-- The outer interior indices are exactly all marked fine indices. -/
def refinedMarkedEquiv (π : IntervalComposition I) (T : RefiningCutSet π) :
    Fin (π.parts - 1) ≃ RefinementMarked π T :=
  Equiv.ofBijective (π.refinedMarkedIndex T)
    ⟨π.refinedMarkedIndex_injective T, π.refinedMarkedIndex_surjective T⟩

/-- Far samples retain the global interval endpoints and the same marked
middle cut. They do not use the endpoints of an inner part. -/
theorem outer_farTriple_transport (π : IntervalComposition I) (T : RefiningCutSet π)
    (j : Fin (π.parts - 1)) :
    T.val.toComposition.farTriple (π.refinedOuterIndex T j) = π.farTriple j := by
  apply IncreasingBoundaryTriple.eq_of_entries rfl _ rfl
  exact π.refinedOuterIndex_position T j

/-- Arbitrary far-triple products are exactly the marked fine product.
Taking f(t)=-H(t)/2 supplies the source outer far-only factors. -/
theorem prod_outer_farTriples {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (T : RefiningCutSet π) (f : IncreasingBoundaryTriple n → R) :
    (∏ j : Fin (π.parts - 1), f (π.farTriple j)) =
      ∏ r : RefinementMarked π T, f (T.val.toComposition.farTriple r.val) :=
  Fintype.prod_equiv (π.refinedMarkedEquiv T) _ _
    (fun j => congrArg f (π.outer_farTriple_transport T j).symm)

end
end SM.IntervalComposition
