import DirectGLSSW.MixedEdgeComponentRoots
import DirectGLSSW.GeometricSmoothingWeights
import DirectGLSSW.DaughterRootAmplitude

set_option autoImplicit false

namespace DirectGLSSW.MixedEdgeRootWeights

open PermutationOrbits PolygonNonalternation DaughterFirstReturn
open GeometricSmoothingWeights MixedEdgeComponentRoots DaughterRootAmplitude
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

theorem componentAmplitude_at_edgeRoot
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (T : Finset (EdgeChord q e)) (hAux : auxiliaryGenericity q hq)
    (hNA : polygonNonalternating q hq.g2 (T.image Subtype.val))
    (r : EdgeRoot q e T) :
    componentAmplitude q hq (T.image Subtype.val) hAux hNA
        (rootComponent q hq.g2 e T r) =
      polygonAmplitude
        (daughterVertex q hq.g2 (T.image Subtype.val) (rootEvent q e T r))
        (hAux (T.image Subtype.val) hNA (rootEvent q e T r)) := by
  have hcycle : (smoothingDartPermutation q hq.g2 (T.image Subtype.val)).SameCycle
      (componentRoot q hq (T.image Subtype.val) (rootComponent q hq.g2 e T r))
      (rootEvent q e T r) := by
    apply (componentOf_eq_iff _ _ _).mp
    exact componentRoot_sameComponent q hq (T.image Subtype.val)
      (rootComponent q hq.g2 e T r)
  simpa only [componentAmplitude, componentPolygon] using
    daughterPolygonAmplitude_eq_of_sameCycle hRI q hq.g2 (T.image Subtype.val)
      (componentRoot q hq (T.image Subtype.val) (rootComponent q hq.g2 e T r))
      (rootEvent q e T r) hcycle
      (hAux (T.image Subtype.val) hNA
        (componentRoot q hq (T.image Subtype.val) (rootComponent q hq.g2 e T r)))


theorem componentAmplitudeProduct_eq_edgeRootProduct
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (T : Finset (EdgeChord q e)) (hAux : auxiliaryGenericity q hq)
    (hNA : polygonNonalternating q hq.g2 (T.image Subtype.val)) :
    componentAmplitudeProduct q hq (T.image Subtype.val) hAux hNA =
      ∏ r : EdgeRoot q e T,
        polygonAmplitude
          (daughterVertex q hq.g2 (T.image Subtype.val) (rootEvent q e T r))
          (hAux (T.image Subtype.val) hNA (rootEvent q e T r)) := by
  classical
  unfold componentAmplitudeProduct
  rw [← (rootComponent_bijective q hq.g2 hq.size_ge_three e T hNA).prod_comp
    (componentAmplitude q hq (T.image Subtype.val) hAux hNA)]
  apply Finset.prod_congr rfl
  intro r _
  exact componentAmplitude_at_edgeRoot hRI q hq e T hAux hNA r





end
end DirectGLSSW.MixedEdgeRootWeights
