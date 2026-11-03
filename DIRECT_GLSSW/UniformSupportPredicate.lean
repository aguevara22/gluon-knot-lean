import PolygonUniformity
import UniformDaughterSupportCharacterization
import DirectGLSSW.GeometricSmoothingWeights

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.UniformSupportReconstruction
open DaughterFirstReturn GeometricSmoothingWeights PermutationOrbits
  PolygonUniformity UniformDaughterSupportLocality
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Polygon uniformity is the literal disjunction of daughter-side signs. -/
theorem daughterPolygon_uniform_iff {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q) :
    PolygonUniform (daughterVertex q hq.g2 S root) ↔ daughterUniform q hq S root := by
  rfl

/-- Uniformity depends on the retained component, not its selected root. -/
theorem daughterUniform_iff_of_same_component {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (root root' : PolygonEvent q)
    (hr : retainedCorner q S root) (hr' : retainedCorner q S root')
    (hc : componentOf (smoothingDartPermutation q hq.g2 S) root =
      componentOf (smoothingDartPermutation q hq.g2 S) root') :
    daughterUniform q hq S root ↔ daughterUniform q hq S root' := by
  rw [daughterUniform_iff_carrier q hq S root hr,
    daughterUniform_iff_carrier q hq S root' hr', hc]

/-- The chosen component polygons characterize the literal all-root support filter. -/
theorem uniformDaughterSupport_iff_componentPolygon {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) :
    uniformDaughterSupport q hq S ↔
      PolygonNonalternation.polygonNonalternating q hq.g2 S ∧
      ∀ C : Component (smoothingDartPermutation q hq.g2 S),
        PolygonUniform (componentPolygon q hq S C) := by
  constructor
  · rintro ⟨hNA, hs⟩
    refine ⟨hNA, ?_⟩
    intro C
    obtain ⟨r, hr, hc, hu⟩ := hs C
    apply (daughterPolygon_uniform_iff q hq S (componentRoot q hq S C)).mpr
    exact (daughterUniform_iff_of_same_component q hq S r (componentRoot q hq S C)
      hr (componentRoot_retainedCorner q hq S C)
      (hc.trans (componentRoot_sameComponent q hq S C).symm)).mp hu
  · rintro ⟨hNA, hs⟩
    refine ⟨hNA, ?_⟩
    intro C
    exact ⟨componentRoot q hq S C, componentRoot_retainedCorner q hq S C,
      componentRoot_sameComponent q hq S C,
      (daughterPolygon_uniform_iff q hq S (componentRoot q hq S C)).mp (hs C)⟩

/-- Exact equivalence between the chosen-component and literal support subtypes. -/
def uniformSupportEquiv {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    {S : SeparatingSupport q hq //
      ∀ C : Component (smoothingDartPermutation q hq.g2 S.val),
        PolygonUniform (componentPolygon q hq S.val C)} ≃
    {S : Finset (PolygonCrossing q) // uniformDaughterSupport q hq S} where
  toFun S := ⟨S.val.val,
    (uniformDaughterSupport_iff_componentPolygon q hq S.val.val).mpr
      ⟨S.val.property, S.property⟩⟩
  invFun S := ⟨⟨S.val, S.property.1⟩,
    ((uniformDaughterSupport_iff_componentPolygon q hq S.val).mp S.property).2⟩
  left_inv S := by cases S; rfl
  right_inv S := by cases S; rfl





end DirectGLSSW.UniformSupportReconstruction
