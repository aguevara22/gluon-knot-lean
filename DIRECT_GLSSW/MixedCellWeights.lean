import DirectGLSSW.MixedConsecutiveCapWord
import DirectGLSSW.MixedEdgeRootWeights

set_option autoImplicit false

namespace DirectGLSSW.MixedCellWeights
open scoped BigOperators
open MixedConsecutiveCapWord MixedEdgeSupportOrder MixedEdgeComponentRoots
open GeometricSmoothingWeights DaughterFirstReturn

theorem ordered_support_nonalternating
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}
    (q : Fin n → PlanarPoint K) (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (L : List (DirectGLSSW.EdgeChord q e)) (hL : OrderedEdgeSupport q hq e L) :
    PolygonNonalternation.polygonNonalternating q hq.g2 (supportOfList q e L) := by
  classical
  apply (polygonNonalternating_iff_returnVisitOrder q hq.g2 hq.size_ge_three
    e hflat hleft L.toFinset).mpr
  intro c hc d hd hne hcd
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hc)
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hd)
  rcases lt_trichotomy i j with hij | hij | hji
  · have hab := (List.pairwise_iff_get.mp hL.2) i j hij
    simpa only [hi,hj] using hab.2
  · have heq : c = d := by rw [← hi,← hj,hij]
    exact (hne heq).elim
  · have hab := (List.pairwise_iff_get.mp hL.2) j i hji
    rw [hi,hj] at hab
    exact (lt_asymm hcd hab.1).elim

/-- Reindex the actual component product by cells; root independence is explicit.
The factors here remain actual daughter amplitudes, before the cap-word theorem. -/
theorem componentAmplitudeProduct_eq_cellProduct (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (L : List (DirectGLSSW.EdgeChord q e)) (hL : OrderedEdgeSupport q hq e L)
    (hAux : auxiliaryGenericity q hq) :
    componentAmplitudeProduct q hq (supportOfList q e L) hAux
      (ordered_support_nonalternating q hq e hflat hleft L hL) =
    ∏ i : Fin (L.length+1),
      polygonAmplitude (daughterVertex q hq.g2 (supportOfList q e L) (cellRootEvent q e L i))
        (hAux (supportOfList q e L)
          (ordered_support_nonalternating q hq e hflat hleft L hL) (cellRootEvent q e L i)) := by
  classical
  let hNA := ordered_support_nonalternating q hq e hflat hleft L hL
  let f : EdgeRoot q e L.toFinset → ℚ := fun r =>
    polygonAmplitude (daughterVertex q hq.g2 (supportOfList q e L)
      (rootEvent q e L.toFinset r))
      (hAux (supportOfList q e L) hNA (rootEvent q e L.toFinset r))
  have hprod := MixedEdgeRootWeights.componentAmplitudeProduct_eq_edgeRootProduct
    hRI q hq e L.toFinset hAux hNA
  change componentAmplitudeProduct q hq (supportOfList q e L) hAux hNA = _
  calc
    _ = ∏ r : EdgeRoot q e L.toFinset, f r := hprod
    _ = ∏ i : Fin (L.length+1), f (cellRootEquiv q e L hL.1 i) :=
      ((cellRootEquiv q e L hL.1).prod_comp f).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      let amp : PolygonEvent q → ℚ := fun x =>
        polygonAmplitude (daughterVertex q hq.g2 (supportOfList q e L) x)
          (hAux (supportOfList q e L) hNA x)
      change amp (rootEvent q e L.toFinset (cellRootEquiv q e L hL.1 i)) =
        amp (cellRootEvent q e L i)
      exact congrArg amp (cellRootEvent_eq_rootEvent q e L hL.1 i).symm



end DirectGLSSW.MixedCellWeights
