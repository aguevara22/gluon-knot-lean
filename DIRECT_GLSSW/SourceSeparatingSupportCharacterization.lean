import DirectGLSSW.GeometricSmoothingWeights
import DaughterLocalCrossingEquiv
import DaughterG2Inheritance
import SourceNonalternatingSeparation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceSeparatingSupportCharacterization
open GeometricSmoothingWeights PermutationOrbits PolygonNonalternation
open DaughterFirstReturn DaughterParentCrossing DaughterLocalCrossingEquiv
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

theorem separating_support_iff (S : Finset (PolygonCrossing q)) :
    (∃ s : SeparatingSupport q hq, s.val = S) ↔ polygonNonalternating q hq.g2 S := by
  constructor
  · rintro ⟨s,rfl⟩
    exact s.property
  · intro h
    exact ⟨⟨S,h⟩,rfl⟩

variable (S : SeparatingSupport q hq)
variable (A : Component (smoothingDartPermutation q hq.g2 S.val))

/-- Complete literal vertex equation of the existing daughter carrier. -/
theorem component_vertex_literal
    (i : Fin (Fintype.card (CornerCoord q hq.g2 S.val (componentRoot q hq S.val A)))) :
    componentPolygon q hq S.val A i =
      polygonEventPoint q (orbitEventAt q hq.g2 S.val (componentRoot q hq S.val A)
        (cornerEnumeration q hq.g2 S.val (componentRoot q hq S.val A) i).val) := rfl

theorem component_count :
    componentCount (smoothingDartPermutation q hq.g2 S.val) = S.val.card + 1 :=
  (polygonNonalternating_iff_dart_count q hq.g2 hq.size_ge_three S.val).mp S.property

theorem component_g2 : cyclicNoTripleIntersections (componentPolygon q hq S.val A) :=
  DaughterG2Inheritance.daughter_g2_of_cyclicGeneric q hq S.val S.property
    (componentRoot q hq S.val A)

/-- Every actual daughter edge is nonzero. -/
theorem component_edge_nonzero
    (i : Fin (Fintype.card (CornerCoord q hq.g2 S.val (componentRoot q hq S.val A)))) :
    componentPolygon q hq S.val A (cyclicSuccessor i) - componentPolygon q hq S.val A i ≠ 0 :=
  daughterSide_ne_zero q hq.g2 S.val hq.size_ge_three hq.g1
    (componentRoot q hq S.val A) (componentRoot_retainedCorner q hq S.val A) i

/-- Self-crossings are exactly unselected original crossings with both actual
visits in this component. The map is the proved geometric parent-crossing map. -/
theorem self_crossing_iff (c : PolygonCrossing q) :
    (∃ d : PolygonCrossing (componentPolygon q hq S.val A),
      parentCrossing q hq S.val S.property (componentRoot q hq S.val A)
        (componentRoot_retainedCorner q hq S.val A) d = c) ↔
      c ∉ S.val ∧
      componentOf (smoothingDartPermutation q hq.g2 S.val) (Sum.inr (c,false)) = A ∧
      componentOf (smoothingDartPermutation q hq.g2 S.val) (Sum.inr (c,true)) = A := by
  let E := localCrossingEquiv q hq S.val S.property (componentRoot q hq S.val A)
    (componentRoot_retainedCorner q hq S.val A)
  have hr := componentRoot_sameComponent q hq S.val A
  constructor
  · rintro ⟨d,rfl⟩
    have h := (E d).property
    change _ ∉ S.val ∧ _ = _ ∧ _ = _ at h
    simpa only [hr] using h
  · intro h
    have hc : c ∉ S.val ∧
        componentOf (smoothingDartPermutation q hq.g2 S.val) (Sum.inr (c,false)) =
          componentOf (smoothingDartPermutation q hq.g2 S.val) (componentRoot q hq S.val A) ∧
        componentOf (smoothingDartPermutation q hq.g2 S.val) (Sum.inr (c,true)) =
          componentOf (smoothingDartPermutation q hq.g2 S.val) (componentRoot q hq S.val A) := by
      simpa only [hr] using h
    refine ⟨E.symm ⟨c,hc⟩, ?_⟩
    exact congrArg Subtype.val (E.apply_symm_apply ⟨c,hc⟩)

/-- Together with the iff, this gives a bijective crossing correspondence. -/
theorem self_crossing_map_injective :
    Function.Injective (parentCrossing q hq S.val S.property (componentRoot q hq S.val A)
      (componentRoot_retainedCorner q hq S.val A)) :=
  parentCrossing_injective q hq S.val S.property (componentRoot q hq S.val A)
    (componentRoot_retainedCorner q hq S.val A)

/-- An intersection between different gluing components is not a self-crossing
of any daughter. Its parent point is not erased from the geometry. -/
theorem intercomponent_not_self_crossing (c : PolygonCrossing q)
    (hc : componentOf (smoothingDartPermutation q hq.g2 S.val) (Sum.inr (c,false)) ≠
      componentOf (smoothingDartPermutation q hq.g2 S.val) (Sum.inr (c,true))) :
    ¬ ∃ d : PolygonCrossing (componentPolygon q hq S.val A),
      parentCrossing q hq S.val S.property (componentRoot q hq S.val A)
        (componentRoot_retainedCorner q hq S.val A) d = c := by
  intro h
  have hh := (self_crossing_iff q hq S A c).mp h
  exact hc (hh.2.1.trans hh.2.2.symm)

/-- Literal daughter sides preserve the orientation of their original edge. -/
theorem component_edge_positive_multiple
    (i : Fin (Fintype.card (CornerCoord q hq.g2 S.val (componentRoot q hq S.val A)))) :
    0 < daughterSideScale q hq.g2 S.val (componentRoot q hq S.val A)
      (cornerEnumeration q hq.g2 S.val (componentRoot q hq S.val A) i) ∧
    componentPolygon q hq S.val A (cyclicSuccessor i) - componentPolygon q hq S.val A i =
      daughterSideScale q hq.g2 S.val (componentRoot q hq S.val A)
        (cornerEnumeration q hq.g2 S.val (componentRoot q hq S.val A) i) •
      cyclicTangent q (polygonEventEdge q (orbitEventAt q hq.g2 S.val (componentRoot q hq S.val A)
        (cornerEnumeration q hq.g2 S.val (componentRoot q hq S.val A) i).val)) :=
  daughterSide_positive_multiple q hq.g2 S.val hq.size_ge_three
    (componentRoot q hq S.val A) (componentRoot_retainedCorner q hq S.val A) i

theorem self_crossing_point
    (d : PolygonCrossing (componentPolygon q hq S.val A)) :
    crossingPoint q (parentCrossing q hq S.val S.property (componentRoot q hq S.val A)
      (componentRoot_retainedCorner q hq S.val A) d) =
      crossingPoint (componentPolygon q hq S.val A) d :=
  parentCrossing_point q hq S.val S.property (componentRoot q hq S.val A)
    (componentRoot_retainedCorner q hq S.val A) d

end DirectGLSSW.SourceSeparatingSupportCharacterization











