import AllCellCapMatrix
set_option autoImplicit false
open scoped BigOperators
namespace DirectGLSSW.SourceMixedEdgeCapFactors
open MixedConsecutiveCapWord SelectedCellClippedWord ExtendedReturnArcGeometry
open OrderedCapEvents CrossingCapPairing DaughterFirstReturn DaughterRootAmplitude
open GeometricSmoothingWeights MixedCellWeights MixedCellOrbitWord CellEventOrders

variable {n : ℕ}
theorem exists_actual_cell_weights (hRI : GLSSWRootIndependence)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ) (hε : 0 < ε)
    (hAux : auxiliaryGenericity q hq) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    let ℓ := (q e).1-(q (cyclicSuccessor e)).1
    ∃ (cU cV : EventIndex Q n)
      (E : DirectGLSSW.EdgeChord q e ≃
        {c : EventIndex Q n // 0 < eventTime Q n c ∧ eventTime Q n c < ℓ}),
      eventTime Q n cU = 0 ∧ eventTime Q n cV = ℓ ∧
      eventPair Q n cU = (1,2) ∧ eventPair Q n cV = (n-1,n) ∧ cU < cV ∧
      (∀ z, eventTime Q n (E z).val = (crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
        eventPair Q n (E z).val = (returnRank q e z+1,returnRank q e z+2)) ∧
      (∀ (L : List (DirectGLSSW.EdgeChord q e)) (hL : OrderedEdgeSupport q hq e L),
        (∀ i : Fin (L.length+1),
          eventMatrix Q n (leftBoundary cU (fun z => (E z).val) L i)
            (rightBoundary cV (fun z => (E z).val) L i) =
          polygonAmplitude (daughterVertex q hq.g2 (supportOfList q e L) (cellRootEvent q e L i))
            (hAux (supportOfList q e L)
              (ordered_support_nonalternating q hq e (hV.trans hU.symm) hleft L hL)
              (cellRootEvent q e L i))) ∧
        (∏ i : Fin (L.length+1),
          eventMatrix Q n (leftBoundary cU (fun z => (E z).val) L i)
            (rightBoundary cV (fun z => (E z).val) L i)) =
        componentAmplitudeProduct q hq (supportOfList q e L) hAux
          (ordered_support_nonalternating q hq e (hV.trans hU.symm) hleft L hL)) := by
  exact AllCellCapMatrix.exists_actual_cell_weights hRI q hq e hU hV hleft ε hε hAux


end DirectGLSSW.SourceMixedEdgeCapFactors
