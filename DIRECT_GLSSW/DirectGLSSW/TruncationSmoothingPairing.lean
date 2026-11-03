import DirectGLSSW.TruncationEventOrder
import DirectGLSSW.SmoothingPermutations

set_option autoImplicit false

namespace DirectGLSSW.TruncationSmoothingPairing

open TruncationDirection TruncationEventOrder

theorem truncationPolygonEventMap_pairing {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n) (scale ε : ℝ)
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    smoothingPairing (truncateCyclicCorner q a p scale ε) (S.map E.toEmbedding)
        (truncationPolygonEventMap q a p scale ε E x) =
      truncationPolygonEventMap q a p scale ε E (smoothingPairing q S x) := by
  classical
  cases x with
  | inl e => rfl
  | inr v =>
      rcases v with ⟨c, b⟩
      by_cases hc : c ∈ S <;> cases b <;>
        simp [smoothingPairing, smoothingPairingMap, truncationPolygonEventMap,
          crossingVisit_mapEquiv, crossingVisitFlip, hc]

end DirectGLSSW.TruncationSmoothingPairing
