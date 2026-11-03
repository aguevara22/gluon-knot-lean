import LiteralInversionFinal

set_option autoImplicit false

namespace DirectGLSSW.ScalarInversionFinal

open scoped BigOperators
open GeometricSmoothingWeights DaughterFirstReturn PermutationOrbits

/-- Literal inversion expressed in the actual outgoing smoothing components
used by `componentPolygon` and the separating primitive. Auxiliary daughter
genericity and GLSSW root independence remain explicit. -/
theorem polygonAmplitude_eq_sum_componentPrimitives
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq) :
    polygonAmplitude q hq =
      ∑ S : SeparatingSupport q hq,
        ∏ C : Component (smoothingDartPermutation q hq.g2 S.val),
          separatingSmoothingSum (componentPolygon q hq S.val C)
            (hAux S.val S.property (componentRoot q hq S.val C))
            (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.val
              S.property (componentRoot q hq S.val C)
              (componentRoot_retainedCorner q hq S.val C) hAux) := by
  classical
  rw [literal_scalar_inversion q hq hRI hAux]
  apply Fintype.sum_congr
  intro S
  apply Fintype.prod_equiv
    (productOrderEquiv (polygonEventSuccessor q hq.g2) (smoothingPairing q S.val))
  intro A
  rfl



end DirectGLSSW.ScalarInversionFinal
