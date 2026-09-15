import SM.GeometricNearFar
import SM.MarkedRefinement
import SM.InteriorCutIndex
import SM.NearFarCutExpansion
import SM.TriangularPolynomial
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
set_option pp.universes false

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

#check SM.IntervalComposition.eq_single_of_parts_eq_one
#print axioms SM.IntervalComposition.eq_single_of_parts_eq_one
#check SM.IntervalComposition.parts_eq_one_iff_eq_single
#print axioms SM.IntervalComposition.parts_eq_one_iff_eq_single
#check SM.IntervalComposition.single_part
#print axioms SM.IntervalComposition.single_part
#check SM.IntervalComposition.single_product
#print axioms SM.IntervalComposition.single_product
#check SM.IntervalComposition.nonSingleEquiv
#print axioms SM.IntervalComposition.nonSingleEquiv
#check SM.BoundaryCutSet
#print axioms SM.BoundaryCutSet
#check SM.BoundaryCutSet.ext
#print axioms SM.BoundaryCutSet.ext
#check SM.BoundaryCutSet.card_ge_two
#print axioms SM.BoundaryCutSet.card_ge_two
#check SM.BoundaryCutSet.toComposition
#print axioms SM.BoundaryCutSet.toComposition
#check SM.IntervalComposition.cutSet
#print axioms SM.IntervalComposition.cutSet
#check SM.IntervalComposition.cutSet_card
#print axioms SM.IntervalComposition.cutSet_card
#check SM.IntervalComposition.cutSet_injective
#print axioms SM.IntervalComposition.cutSet_injective
#check SM.BoundaryCutSet.toComposition_cutSet
#print axioms SM.BoundaryCutSet.toComposition_cutSet
#check SM.IntervalComposition.cutSet_toComposition
#print axioms SM.IntervalComposition.cutSet_toComposition
#check SM.IntervalComposition.cutSetEquiv
#print axioms SM.IntervalComposition.cutSetEquiv
#check SM.InteriorCutSet
#print axioms SM.InteriorCutSet
#check SM.BoundaryCutSet.interior
#print axioms SM.BoundaryCutSet.interior
#check SM.BoundaryCutSet.ofInterior
#print axioms SM.BoundaryCutSet.ofInterior
#check SM.BoundaryCutSet.interior_ofInterior
#print axioms SM.BoundaryCutSet.interior_ofInterior
#check SM.BoundaryCutSet.ofInterior_interior
#print axioms SM.BoundaryCutSet.ofInterior_interior
#check SM.BoundaryCutSet.interiorEquiv
#print axioms SM.BoundaryCutSet.interiorEquiv
#check SM.BoundaryCutSet.restrict
#print axioms SM.BoundaryCutSet.restrict
#check SM.BoundaryCutSet.mem_restrict
#print axioms SM.BoundaryCutSet.mem_restrict
#check SM.BoundaryCutSet.restrict_self
#print axioms SM.BoundaryCutSet.restrict_self
#check SM.BoundaryCutSet.restrict_restrict
#print axioms SM.BoundaryCutSet.restrict_restrict
#check SM.IntervalComposition.interiorCutSetEquiv
#print axioms SM.IntervalComposition.interiorCutSetEquiv
#check SM.IntervalComposition.part_bounds
#print axioms SM.IntervalComposition.part_bounds
#check SM.IntervalComposition.part_order
#print axioms SM.IntervalComposition.part_order
#check SM.IntervalComposition.exists_halfOpen_part
#print axioms SM.IntervalComposition.exists_halfOpen_part
#check SM.IntervalComposition.exists_closed_part
#print axioms SM.IntervalComposition.exists_closed_part
#check SM.IntervalComposition.part_interior_unique
#print axioms SM.IntervalComposition.part_interior_unique
#check SM.RefiningCutSet
#print axioms SM.RefiningCutSet
#check SM.IntervalComposition.halfOpen_part_unique
#print axioms SM.IntervalComposition.halfOpen_part_unique
#check SM.IntervalComposition.flattenCutSets
#print axioms SM.IntervalComposition.flattenCutSets
#check SM.IntervalComposition.mem_flattenCutSets
#print axioms SM.IntervalComposition.mem_flattenCutSets
#check SM.IntervalComposition.outer_cuts_subset_flatten
#print axioms SM.IntervalComposition.outer_cuts_subset_flatten
#check SM.IntervalComposition.flattenRefinement
#print axioms SM.IntervalComposition.flattenRefinement
#check SM.IntervalComposition.unflattenCutSets
#print axioms SM.IntervalComposition.unflattenCutSets
#check SM.IntervalComposition.unflatten_flatten
#print axioms SM.IntervalComposition.unflatten_flatten
#check SM.IntervalComposition.flatten_unflatten
#print axioms SM.IntervalComposition.flatten_unflatten
#check SM.IntervalComposition.nestedCutSetEquiv
#print axioms SM.IntervalComposition.nestedCutSetEquiv
#check SM.IntervalComposition.nestedCompositionEquiv
#print axioms SM.IntervalComposition.nestedCompositionEquiv
#check SM.MarkedCuts
#print axioms SM.MarkedCuts
#check SM.BoundaryCutSet.cuts_subset_iff_interior_subset
#print axioms SM.BoundaryCutSet.cuts_subset_iff_interior_subset
#check SM.BoundaryCutSet.outerFromMarks
#print axioms SM.BoundaryCutSet.outerFromMarks
#check SM.BoundaryCutSet.outerFromMarks_subset
#print axioms SM.BoundaryCutSet.outerFromMarks_subset
#check SM.BoundaryCutSet.outerMarkedEquiv
#print axioms SM.BoundaryCutSet.outerMarkedEquiv
#check SM.swapSigmaSubtype
#print axioms SM.swapSigmaSubtype
#check SM.IntervalComposition.outerCompositionMarkedEquiv
#print axioms SM.IntervalComposition.outerCompositionMarkedEquiv
#check SM.IntervalComposition.nestedMarkedCutEquiv
#print axioms SM.IntervalComposition.nestedMarkedCutEquiv
#check SM.IntervalComposition.interiorPosition
#print axioms SM.IntervalComposition.interiorPosition
#check SM.IntervalComposition.interiorPosition_injective
#print axioms SM.IntervalComposition.interiorPosition_injective
#check SM.IntervalComposition.interiorPosition_mem
#print axioms SM.IntervalComposition.interiorPosition_mem
#check SM.IntervalComposition.mem_interior_iff_exists_index
#print axioms SM.IntervalComposition.mem_interior_iff_exists_index
#check SM.IntervalComposition.interiorPositionEquiv
#print axioms SM.IntervalComposition.interiorPositionEquiv
#check SM.IntervalComposition.nearFarWeight_marked_expansion
#print axioms SM.IntervalComposition.nearFarWeight_marked_expansion
#check SM.gate_pair_cast
#print axioms SM.gate_pair_cast
#check SM.IntervalComposition.ordinaryWeight_cast
#print axioms SM.IntervalComposition.ordinaryWeight_cast
#check SM.IntervalComposition.rootWeight_cast
#print axioms SM.IntervalComposition.rootWeight_cast
#check SM.IntervalComposition.parts_eq_one_of_leaves_eq_one
#print axioms SM.IntervalComposition.parts_eq_one_of_leaves_eq_one
#check SM.geometric_nearFar_open
#print axioms SM.geometric_nearFar_open
#check SM.geometric_nearFar_root
#print axioms SM.geometric_nearFar_root
#print SM.BoundaryCutSet
#print SM.BoundaryCutSet.toComposition
#print SM.IntervalComposition.cutSet
#print SM.IntervalComposition.cutSetEquiv
#print SM.InteriorCutSet
#print SM.BoundaryCutSet.interior
#print SM.BoundaryCutSet.ofInterior
#print SM.BoundaryCutSet.restrict
#print SM.RefiningCutSet
#print SM.IntervalComposition.flattenCutSets
#print SM.IntervalComposition.flattenRefinement
#print SM.IntervalComposition.unflattenCutSets
#print SM.IntervalComposition.nestedCompositionEquiv
#print SM.MarkedCuts
#print SM.BoundaryCutSet.outerFromMarks
#print SM.BoundaryCutSet.outerMarkedEquiv
#print SM.IntervalComposition.nestedMarkedCutEquiv
#print SM.IntervalComposition.interiorPosition
#print SM.IntervalComposition.interiorPositionEquiv
#print axioms CompositionCutSetIndependentReview.every_raw_cut_set_admitted
#print axioms CompositionCutSetIndependentReview.unary_cut_set_is_exactly_endpoints
#print axioms CompositionCutSetIndependentReview.full_cut_coverage
#print axioms CompositionCutSetIndependentReview.exact_cut_membership
#print axioms CompositionCutSetIndependentReview.complete_raw_roundtrip
#print axioms CompositionCutSetIndependentReview.same_cut_set_iff_same_composition
#print axioms NearFarRefinementIndependentReview.geometric_open_is_actual_inverse
#print axioms NearFarRefinementIndependentReview.geometric_root_retains_full_transform
#print axioms NearFarRefinementIndependentReview.arbitrary_interior_subset_realized
#print axioms NearFarRefinementIndependentReview.actual_half_open_partition
#print axioms NearFarRefinementIndependentReview.nested_forward_cut_union
#print axioms NearFarRefinementIndependentReview.nested_inner_raw_roundtrip
#print axioms NearFarRefinementIndependentReview.marked_forward_has_actual_cuts
#print axioms NearFarRefinementIndependentReview.every_marked_refinement_recovered
#print axioms NearFarRefinementIndependentReview.empty_and_full_markings_allowed
#print axioms NearFarRefinementIndependentReview.empty_marks_give_unary_outer
#print axioms NearFarRefinementIndependentReview.full_marks_recover_refined_outer
#print axioms NearFarRefinementIndependentReview.full_nested_and_marked_domains_finite
#print axioms NearFarRefinementIndependentReview.interior_indices_have_exact_coverage
#print axioms NearFarRefinementIndependentReview.unary_has_no_interior_positions
#print axioms NearFarRefinementIndependentReview.unary_marked_expansion_equals_one
#print axioms NearFarRefinementIndependentReview.extreme_array_weights
