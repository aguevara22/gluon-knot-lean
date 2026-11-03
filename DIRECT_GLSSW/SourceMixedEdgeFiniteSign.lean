import SourceMixedEdgeContinuation
import DirectGLSSW.PolygonSignExtensionality

set_option autoImplicit false

open DirectGLSSW GeometricSmoothingWeights ChosenEdgeNormalization PermutationOrbits
open DirectGLSSW.SourceMixedEdgeFormula DirectGLSSW.MixedEdgeDensityRecursion
open DirectGLSSW.CrossingIncidenceNeighborhood DirectGLSSW.ActualAuxiliaryDensity
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open DirectGLSSW.SourceMixedEdgeContinuation

namespace DirectGLSSW.SourceMixedEdgeFiniteSign

/-- The unique locally constant continuation of the literal auxiliary
chosen-edge sum is invariant under equality of all oriented-triple signs of
the full endpoint cap. -/
theorem existsUnique_mixed_edge_rhs_continuation_finite_signs
    (hRI : GLSSWRootIndependence) (n : ℕ) (e : Fin n) :
    ∃! Φ : (q : Fin n → PlanarPoint ℝ) → CyclicGeneric q →
        (planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
          planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0) → ℚ,
      (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
        (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
          planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0),
        ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r)
          (htr : planarDet (cyclicTangent r e) (cyclicTangent r (cyclicSuccessor e)) *
            planarDet (cyclicTangent r (cyclicVertexIndex e (n-2))) (cyclicTangent r e) < 0),
          Φ r hr htr = Φ q hq ht) ∧
      (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
        (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
          planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0)
        (hAux : auxiliaryGenericity q hq),
        Φ q hq ht = ∑ T : ChosenEdgeSeparatingSupport q hq e,
          (-1 : ℚ)^((T.val.image Subtype.val).card+1) *
            ∏ c : Component (smoothingDartPermutation q hq.g2 (T.val.image Subtype.val)),
              polygonAmplitude (componentPolygon q hq (T.val.image Subtype.val) c)
                (hAux _ T.property.2 (componentRoot q hq _ c))) ∧
      (∀ (q q' : Fin n → PlanarPoint ℝ)
        (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
        (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
          planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0)
        (ht' : planarDet (cyclicTangent q' e) (cyclicTangent q' (cyclicSuccessor e)) *
          planarDet (cyclicTangent q' (cyclicVertexIndex e (n-2))) (cyclicTangent q' e) < 0)
        (hsign : ∀ a b c : Fin n, a ≠ b → b ≠ c → a ≠ c →
          scalarSignValue (planarDet (q b - q c) (q a - q c)) =
          scalarSignValue (planarDet (q' b - q' c) (q' a - q' c))),
        Φ q hq ht = Φ q' hq' ht') := by
  obtain ⟨Φ, hΦ, huniq⟩ :=
    DirectGLSSW.SourceMixedEdgeContinuation.existsUnique_mixed_edge_rhs_continuation hRI n e
  have hfinite :
      ∀ (q q' : Fin n → PlanarPoint ℝ)
        (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
        (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
          planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0)
        (ht' : planarDet (cyclicTangent q' e) (cyclicTangent q' (cyclicSuccessor e)) *
          planarDet (cyclicTangent q' (cyclicVertexIndex e (n-2))) (cyclicTangent q' e) < 0)
        (hsign : ∀ a b c : Fin n, a ≠ b → b ≠ c → a ≠ c →
          scalarSignValue (planarDet (q b - q c) (q a - q c)) =
          scalarSignValue (planarDet (q' b - q' c) (q' a - q' c))),
        Φ q hq ht = Φ q' hq' ht' := by
    intro q q' hq hq' ht ht' hsign
    have hqAmp :=
      DirectGLSSW.SourceMixedEdgeContinuation.mixed_edge_rhs_continuation_eq_amplitude
        hRI n e Φ hΦ.1 hΦ.2 q hq ht
    have hq'Amp :=
      DirectGLSSW.SourceMixedEdgeContinuation.mixed_edge_rhs_continuation_eq_amplitude
        hRI n e Φ hΦ.1 hΦ.2 q' hq' ht'
    have hAmp := polygonAmplitude_eq_of_oriented_triple_signs q q' hq hq' hsign
    calc
      Φ q hq ht = polygonAmplitude q hq := hqAmp
      _ = polygonAmplitude q' hq' := hAmp
      _ = Φ q' hq' ht' := hq'Amp.symm
  refine ⟨Φ, ⟨hΦ.1, hΦ.2, hfinite⟩, ?_⟩
  intro F hF
  exact huniq F ⟨hF.1, hF.2.1⟩



end DirectGLSSW.SourceMixedEdgeFiniteSign
