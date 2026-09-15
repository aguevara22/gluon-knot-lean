namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

namespace BoundaryCutSet

theorem mem_interior_iff (S : BoundaryCutSet I) (x : Fin n) :
    x ∈ S.interior.val ↔ x ∈ S.cuts ∧ I.left < x ∧ x < I.right := by
  constructor
  · intro h
    have hb := S.interior.property x h
    simp only [interior, Finset.mem_erase] at h
    exact ⟨h.2.2, hb⟩
  · rintro ⟨hx, hl, hr⟩
    simp only [interior, Finset.mem_erase]
    exact ⟨ne_of_lt hr, ne_of_gt hl, hx⟩

end BoundaryCutSet

namespace IntervalComposition

/-- Fine interior indices that are not cuts of the outer composition. -/
abbrev RefinementUnmarked (π : IntervalComposition I) (T : RefiningCutSet π) :=
  {r : Fin (T.val.toComposition.parts - 1) //
    T.val.toComposition.interiorPosition r ∉ π.cutSet.cuts}

/-- An inner interior cut is a fine interior cut and cannot be an outer cut:
it lies strictly inside one outer part. -/
theorem innerPosition_in_refinement (π : IntervalComposition I) (T : RefiningCutSet π)
    (k : Fin π.parts) (j : Fin ((π.refinementInner T k).parts - 1)) :
    (π.refinementInner T k).interiorPosition j ∈ T.val.interior.val ∧
      (π.refinementInner T k).interiorPosition j ∉ π.cutSet.cuts := by
  let x := (π.refinementInner T k).interiorPosition j
  have hx := (π.refinementInner T k).interiorPosition_mem j
  have hb := (π.refinementInner T k).cutSet.interior.property x hx
  have hc := ((π.refinementInner T k).cutSet.mem_interior_iff x).mp hx
  have he : (π.refinementInner T k).cutSet = π.unflattenCutSets T k :=
    BoundaryCutSet.toComposition_cutSet _
  have hmem : x ∈ (π.unflattenCutSets T k).cuts := by rw [← he]; exact hc.1
  have ht : x ∈ T.val.cuts := (Finset.mem_filter.mp hmem).1
  have hp := π.part_bounds k
  refine ⟨(T.val.mem_interior_iff x).mpr ⟨ht, lt_of_le_of_lt hp.1 hb.1,
    lt_of_lt_of_le hb.2 hp.2⟩, ?_⟩
  intro ho
  exact (π.part_consecutive k).2.2 x ho hb

/-- The fine index of the same actual physical inner cut. -/
def refinedInteriorIndex (π : IntervalComposition I) (T : RefiningCutSet π)
    (a : Σ k : Fin π.parts, Fin ((π.refinementInner T k).parts - 1)) :
    Fin (T.val.toComposition.parts - 1) :=
  T.val.toComposition.interiorPositionEquiv.symm
    ⟨(π.refinementInner T a.1).interiorPosition a.2, by
      rw [BoundaryCutSet.toComposition_cutSet]
      exact (π.innerPosition_in_refinement T a.1 a.2).1⟩

theorem refinedInteriorIndex_position (π : IntervalComposition I) (T : RefiningCutSet π)
    (a : Σ k : Fin π.parts, Fin ((π.refinementInner T k).parts - 1)) :
    T.val.toComposition.interiorPosition (π.refinedInteriorIndex T a) =
      (π.refinementInner T a.1).interiorPosition a.2 := by
  exact congrArg
    (fun y : {x : Fin n // x ∈ T.val.toComposition.cutSet.interior.val} => y.val)
    (T.val.toComposition.interiorPositionEquiv.apply_symm_apply _)

def refinedUnmarkedIndex (π : IntervalComposition I) (T : RefiningCutSet π)
    (a : Σ k : Fin π.parts, Fin ((π.refinementInner T k).parts - 1)) : RefinementUnmarked π T :=
  ⟨π.refinedInteriorIndex T a, by
    rw [π.refinedInteriorIndex_position T a]
    exact (π.innerPosition_in_refinement T a.1 a.2).2⟩

/-- Distinct inner cuts remain distinct: equal physical cuts first force
the same strict outer-part interior, then the same inner cut index. -/
theorem refinedUnmarkedIndex_injective (π : IntervalComposition I) (T : RefiningCutSet π) :
    Function.Injective (π.refinedUnmarkedIndex T) := by
  rintro ⟨k, j⟩ ⟨l, t⟩ h
  have hi : π.refinedInteriorIndex T ⟨k, j⟩ = π.refinedInteriorIndex T ⟨l, t⟩ :=
    congrArg (fun r : RefinementUnmarked π T => r.val) h
  have hx : (π.refinementInner T k).interiorPosition j =
      (π.refinementInner T l).interiorPosition t := by
    rw [← π.refinedInteriorIndex_position T ⟨k, j⟩,
      ← π.refinedInteriorIndex_position T ⟨l, t⟩, hi]
  have hk := (π.refinementInner T k).cutSet.interior.property _
    ((π.refinementInner T k).interiorPosition_mem j)
  have hl := (π.refinementInner T l).cutSet.interior.property _
    ((π.refinementInner T l).interiorPosition_mem t)
  have hkl : k = l := by
    apply π.part_interior_unique ((π.refinementInner T k).interiorPosition j) hk
    rw [hx]
    exact hl
  subst l
  have hj : j = t := (π.refinementInner T k).interiorPosition_injective hx
  subst t
  rfl

/-- Every unmarked fine cut lies strictly inside an outer part and occurs
as an interior cut of that part's exact restricted composition. -/
theorem refinedUnmarkedIndex_surjective (π : IntervalComposition I) (T : RefiningCutSet π) :
    Function.Surjective (π.refinedUnmarkedIndex T) := by
  intro r
  let x := T.val.toComposition.interiorPosition r.val
  have hx : x ∈ T.val.interior.val := by
    have h := T.val.toComposition.interiorPosition_mem r.val
    rw [BoundaryCutSet.toComposition_cutSet] at h
    exact h
  have hb := T.val.interior.property x hx
  obtain ⟨k, hk⟩ := π.exists_halfOpen_part x (le_of_lt hb.1) hb.2
  have hleft : (π.part k).left < x := by
    apply lt_of_le_of_ne hk.1
    intro he
    apply r.property
    change x ∈ π.cutSet.cuts
    rw [← he]
    exact Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, rfl⟩
  have ht : x ∈ T.val.cuts := ((T.val.mem_interior_iff x).mp hx).1
  have hs : x ∈ (π.unflattenCutSets T k).cuts :=
    Finset.mem_filter.mpr ⟨ht, hk.1, le_of_lt hk.2⟩
  have hi : x ∈ (π.refinementInner T k).cutSet.interior.val := by
    apply ((π.refinementInner T k).cutSet.mem_interior_iff x).mpr
    refine ⟨?_, hleft, hk.2⟩
    rw [show (π.refinementInner T k).cutSet = π.unflattenCutSets T k from
      BoundaryCutSet.toComposition_cutSet _]
    exact hs
  obtain ⟨j, hj⟩ := ((π.refinementInner T k).mem_interior_iff_exists_index x).mp hi
  refine ⟨⟨k, j⟩, ?_⟩
  apply Subtype.ext
  apply T.val.toComposition.interiorPosition_injective
  rw [show (π.refinedUnmarkedIndex T ⟨k, j⟩).val = π.refinedInteriorIndex T ⟨k, j⟩ from rfl,
    π.refinedInteriorIndex_position T ⟨k, j⟩]
  exact hj

/-- All inner interior cuts are exactly the unmarked fine cuts. -/
def refinedUnmarkedEquiv (π : IntervalComposition I) (T : RefiningCutSet π) :
    (Σ k : Fin π.parts, Fin ((π.refinementInner T k).parts - 1)) ≃ RefinementUnmarked π T :=
  Equiv.ofBijective (π.refinedUnmarkedIndex T)
    ⟨π.refinedUnmarkedIndex_injective T, π.refinedUnmarkedIndex_surjective T⟩

/-- The near triple is preserved at an inner cut. Both of its neighboring
child intervals are globally consecutive, so the middle cut determines them. -/
theorem inner_nearTriple_transport (π : IntervalComposition I) (T : RefiningCutSet π)
    (k : Fin π.parts) (j : Fin ((π.refinementInner T k).parts - 1)) :
    T.val.toComposition.nearTriple (π.refinedInteriorIndex T ⟨k, j⟩) =
      (π.refinementInner T k).nearTriple j := by
  apply T.val.toComposition.nearTriple_eq_of_consecutive
  · rw [BoundaryCutSet.toComposition_cutSet, nearTriple_leftInterval]
    exact π.inner_child_consecutive T k _
  · rw [BoundaryCutSet.toComposition_cutSet, nearTriple_rightInterval]
    exact π.inner_child_consecutive T k _
  · exact π.refinedInteriorIndex_position T ⟨k, j⟩

/-- Products of arbitrary neighboring-triple factors are preserved exactly.
Taking f(t)=D(t)/2 supplies every inner near-only factor of the source sum. -/
theorem prod_inner_nearTriples {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (T : RefiningCutSet π) (f : IncreasingBoundaryTriple n → R) :
    (∏ k : Fin π.parts, ∏ j : Fin ((π.refinementInner T k).parts - 1),
      f ((π.refinementInner T k).nearTriple j)) =
      ∏ r : RefinementUnmarked π T, f (T.val.toComposition.nearTriple r.val) := by
  rw [← Fintype.prod_sigma' (fun (k : Fin π.parts)
    (j : Fin ((π.refinementInner T k).parts - 1)) => f ((π.refinementInner T k).nearTriple j))]
  exact Fintype.prod_equiv (π.refinedUnmarkedEquiv T) _ _
    (fun a => congrArg f (π.inner_nearTriple_transport T a.1 a.2).symm)

end IntervalComposition

end
end SM
