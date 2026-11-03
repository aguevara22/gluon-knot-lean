import PolygonSourceNeighborhood
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PhysicalSourceInitialization
open Filter Topology GeometricSmoothingWeights ExposedOpenPrimitive ActiveArc.ExposedChart
  UniversalCarrierDomain AuxiliaryCarrierChart

/-- Actual polygon locality, pulled back by the exact exposed-cut inverse,
produces supplied universal lines without changing the primitive. -/
theorem exists_nearby_source_supplied (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q 0) (hAux : auxiliaryGenericity q hq)
    (hl : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (V : Set (Fin (n+2) → PlanarPoint ℝ)) (hV : V∈𝓝 q) :
    ∃ p∈V, ∃ hp : CyclicGeneric p, ∃ hAp : auxiliaryGenericity p hp,
      LeftExposed p 0 ∧
      (∀ i, 0 < planarDet (cyclicTangent p i) (cyclicTangent p (cyclicSuccessor i))) ∧
      separatingSmoothingSum p hp hAp=separatingSmoothingSum q hq hAux ∧
      ∃ L : Fin (n+1) ⊕ Unit → CarrierLine, UniversalLocus L ∧ PairTransverse L ∧
        (∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (cutArc p 0 e.castSucc)=0 ∧
          lineValue (L (Sum.inl e)) (cutArc p 0 e.succ)=0) ∧
        lineValue (L (Sum.inr ())) (cutArc p 0 ⟨n+1,by omega⟩)=0 := by
  let W := V ∩ {p | ∃ hp : CyclicGeneric p, ∃ hAp : auxiliaryGenericity p hp,
      LeftExposed p 0 ∧
      (∀ i, 0 < planarDet (cyclicTangent p i) (cyclicTangent p (cyclicSuccessor i))) ∧
      separatingSmoothingSum p hp hAp=separatingSmoothingSum q hq hAux}
  have hW : W∈𝓝 q := by
    apply inter_mem hV
    filter_upwards [eventually_auxiliary_primitive hRI q hq hAux,
      eventually_uniform_left q hl,eventually_leftExposed q 0 he] with p hA hleft hE
    obtain ⟨hp,hAp,hν⟩ := hA
    exact ⟨hp,hAp,hE,hleft,hν⟩
  have hG : cyclicNoncollinear (cutArc q 0) := by
    intro i j k hij hjk hik
    exact hq.g1 (cyclicVertexEquiv (0 : Fin (n+2)) i) (cyclicVertexEquiv 0 j) (cyclicVertexEquiv 0 k)
      (fun hh => hij ((cyclicVertexEquiv 0).injective hh))
      (fun hh => hjk ((cyclicVertexEquiv 0).injective hh))
      (fun hh => hik ((cyclicVertexEquiv 0).injective hh))
  obtain ⟨r,hrW,hR,hAR,hGR,L,hL,hT,hinc,hterm⟩ :=
    exists_nearby_universal_supplied (cutArc q 0) (cutArc_regular q 0 hq) hG
      (closedAuxiliary_of_parent q 0 hq he hAux) _
      (uncutArc_preimage_mem_nhds q 0 W hW)
  obtain ⟨hp,hAp,hEp,hleftp,hν⟩ := hrW.2
  refine ⟨uncutArc r 0,hrW.1,hp,hAp,hEp,hleftp,hν,L,hL,hT,?_,?_⟩
  · simpa only [cutArc_uncutArc] using hinc
  · simpa only [cutArc_uncutArc] using hterm
end DirectGLSSW.PhysicalSourceInitialization
