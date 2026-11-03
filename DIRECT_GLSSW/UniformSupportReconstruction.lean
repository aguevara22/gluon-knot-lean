import UniformSupportPredicate
import LiteralInversionComponents
import NonuniformPrimitive

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.UniformSupportReconstruction
open DaughterFirstReturn GeometricSmoothingWeights PermutationOrbits
  PolygonUniformity UniformDaughterSupportLocality
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The unchanged outgoing-component primitive product in actual scalar inversion. -/
def componentPrimitiveProduct {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hAux : auxiliaryGenericity q hq)
    (S : SeparatingSupport q hq) : ℚ :=
  ∏ C : Component (smoothingDartPermutation q hq.g2 S.val),
    separatingSmoothingSum (componentPolygon q hq S.val C)
      (hAux S.val S.property (componentRoot q hq S.val C))
      (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.val S.property
        (componentRoot q hq S.val C) (componentRoot_retainedCorner q hq S.val C) hAux)

/-- One nonuniform daughter kills the whole actual inversion term. -/
theorem componentPrimitiveProduct_eq_zero_of_not_uniform {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq) (hRI : GLSSWRootIndependence)
    (S : SeparatingSupport q hq)
    (hnu : ¬ ∀ C : Component (smoothingDartPermutation q hq.g2 S.val),
      PolygonUniform (componentPolygon q hq S.val C)) :
    componentPrimitiveProduct q hq hAux S = 0 := by
  push_neg at hnu
  obtain ⟨C, hC⟩ := hnu
  unfold componentPrimitiveProduct
  apply Finset.prod_eq_zero (Finset.mem_univ C)
  exact NonuniformPrimitive.separatingSmoothingSum_eq_zero_of_not_uniform
    (componentPolygon q hq S.val C)
    (hAux S.val S.property (componentRoot q hq S.val C))
    (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.val S.property
      (componentRoot q hq S.val C) (componentRoot_retainedCorner q hq S.val C) hAux)
    hRI hC

/-- Actual inversion restricted to uniform component polygons, with no replacement weights. -/
theorem polygonAmplitude_eq_sum_uniformComponentPrimitives {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq) (hRI : GLSSWRootIndependence) :
    polygonAmplitude q hq =
      ∑ S : {S : SeparatingSupport q hq //
        ∀ C : Component (smoothingDartPermutation q hq.g2 S.val),
          PolygonUniform (componentPolygon q hq S.val C)},
        componentPrimitiveProduct q hq hAux S.val := by
  rw [ScalarInversionFinal.polygonAmplitude_eq_sum_componentPrimitives q hq hRI hAux]
  change (∑ S : SeparatingSupport q hq, componentPrimitiveProduct q hq hAux S) = _
  let p : SeparatingSupport q hq → Prop := fun S =>
    ∀ C : Component (smoothingDartPermutation q hq.g2 S.val),
      PolygonUniform (componentPolygon q hq S.val C)
  have hz : (∑ S : {S : SeparatingSupport q hq // ¬ p S},
      componentPrimitiveProduct q hq hAux S.val) = 0 := by
    apply Finset.sum_eq_zero
    intro S _
    exact componentPrimitiveProduct_eq_zero_of_not_uniform q hq hAux hRI S.val S.property
  have hs := Fintype.sum_subtype_add_sum_subtype p (componentPrimitiveProduct q hq hAux)
  rw [hz, add_zero] at hs
  exact hs.symm

/-- Literal uniform-support reconstruction, retaining the actual primitive factors.
Only the original polygon, its daughter auxiliary predicate and RI are supplied. -/
theorem polygonAmplitude_eq_sum_uniformDaughterPrimitives {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq) (hRI : GLSSWRootIndependence) :
    polygonAmplitude q hq =
      ∑ S : {S : Finset (PolygonCrossing q) // uniformDaughterSupport q hq S},
        componentPrimitiveProduct q hq hAux ⟨S.val, S.property.1⟩ := by
  rw [polygonAmplitude_eq_sum_uniformComponentPrimitives q hq hAux hRI]
  apply Fintype.sum_equiv (uniformSupportEquiv q hq)
  intro S
  rfl





end DirectGLSSW.UniformSupportReconstruction
