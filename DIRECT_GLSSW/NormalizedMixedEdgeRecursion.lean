import NormalizedEdgeTurns
import AllCellCapMatrix

set_option autoImplicit false

namespace DirectGLSSW.NormalizedMixedEdgeRecursion
open OrderedCapEvents MixedEdgeSupportOrder MixedConsecutiveCapWord
open SelectedCellClippedWord SupportCellSums NormalizedMixedEdgeMatrixSum NormalizedEdgeTurns
open ExtendedReturnArcGeometry CapCriticalTimes CapCriticalEventGeometry
open GeometricSmoothingWeights
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (hturn : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
      planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0)
    (ε : ℝ) (hε : 0 < ε)
    (hbound : ε < geometricRadius hq.size_ge_three (q ∘ cyclicVertexEquiv e))
    (hroots : Set.InjOn
      (criticalRoot (extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε))
      ↑(criticalPairs (extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε) n))

include hRI hU hV hleft hturn ε hε hbound hroots in
/-- Source mixed-edge recursion on the normalized auxiliary domain. Every
summand uses the actual oriented smoothing-component amplitude product.
Auxiliary daughter genericity and global critical-root injectivity remain explicit. -/
theorem normalized_mixed_edge_recursion (hAux : auxiliaryGenericity q hq) :
    polygonAmplitude q hq =
      ∑ T : EdgeSeparatingSupport q hq.g2 e (hV.trans hU.symm) hleft,
        (-1 : ℚ)^(T.val.card+1) *
          componentAmplitudeProduct q hq (T.val.image Subtype.val) hAux T.property.2 := by
  have htopen :
      planarDet (cyclicTangent (q ∘ cyclicVertexEquiv e) (lastIndex hq.size_ge_three))
        (cyclicTangent (q ∘ cyclicVertexEquiv e) (zeroIndex hq.size_ge_three)) *
      planarDet (cyclicTangent (q ∘ cyclicVertexEquiv e) (penultimateIndex hq.size_ge_three))
        (cyclicTangent (q ∘ cyclicVertexEquiv e) (lastIndex hq.size_ge_three)) < 0 := by
    rwa [opened_endpoint_turn_product]
  obtain ⟨u,v,F,hu,hv,hpu,hpv,hF,hamp⟩ := exists_amplitude_eq_support_cell_sum
    hRI q hq e hU hV hleft htopen ε hε hbound hroots
  rw [hamp]
  apply Finset.sum_congr rfl
  intro T _
  let L := (edgeSupportOrderEquiv q hq.g2 hq.size_ge_three e (hV.trans hU.symm) hleft T).val
  have hL : OrderedEdgeSupport q hq e L :=
    (edgeSupportOrderEquiv q hq.g2 hq.size_ge_three e (hV.trans hU.symm) hleft T).property.2
  have hT : L.toFinset = T.val := ordered_support_toFinset q hq e (hV.trans hU.symm) hleft T
  have hprod := AllCellCapMatrix.actual_cell_eventMatrix_product_eq_componentProduct
    hRI q hq e hU hV hleft ε hAux u v F hu hv hpu hpv hF L hL
  apply congrArg (fun x : ℚ => (-1 : ℚ)^(T.val.card+1)*x)
  simpa only [supportOfList,hT] using hprod

include hRI hU hV hleft hturn ε hε hbound hroots in
/-- An uncrossed mixed edge makes the nonempty support sum empty. This corollary
uses no daughter-genericity assumption, because it uses the matrix sum directly. -/
theorem normalized_uncrossed_edge_amplitude_zero
    (hno : ∀ c : DirectGLSSW.EdgeChord q e, False) : polygonAmplitude q hq = 0 := by
  have htopen :
      planarDet (cyclicTangent (q ∘ cyclicVertexEquiv e) (lastIndex hq.size_ge_three))
        (cyclicTangent (q ∘ cyclicVertexEquiv e) (zeroIndex hq.size_ge_three)) *
      planarDet (cyclicTangent (q ∘ cyclicVertexEquiv e) (penultimateIndex hq.size_ge_three))
        (cyclicTangent (q ∘ cyclicVertexEquiv e) (lastIndex hq.size_ge_three)) < 0 := by
    rwa [opened_endpoint_turn_product]
  obtain ⟨u,v,F,hu,hv,hpu,hpv,hF,hamp⟩ := exists_amplitude_eq_support_cell_sum
    hRI q hq e hU hV hleft htopen ε hε hbound hroots
  rw [hamp]
  apply Finset.sum_eq_zero
  intro T _
  obtain ⟨c,_⟩ := T.property.1
  exact (hno c).elim



end DirectGLSSW.NormalizedMixedEdgeRecursion
