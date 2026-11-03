import SupportCellSums

set_option autoImplicit false

namespace DirectGLSSW.NormalizedMixedEdgeMatrixSum
open OrderedCapEvents MixedEdgeSupportOrder MixedEventOrder MixedCapChainRestriction
open SelectedCellClippedWord SupportCellSums FiniteSupportCuts
open ExtendedReturnArcGeometry InteriorEdgeEvents CapCriticalTimes CapCriticalEventGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The inverse-zero expansion, at the actual endpoint events of the extended
return arc, is exactly the signed sum over separating supports of the original
polygon. The factors are actual event-matrix entries, before daughter identification. -/
theorem exists_amplitude_eq_support_cell_sum (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (hturn :
      planarDet (cyclicTangent (q ∘ cyclicVertexEquiv e) (lastIndex hq.size_ge_three))
        (cyclicTangent (q ∘ cyclicVertexEquiv e) (zeroIndex hq.size_ge_three)) *
      planarDet (cyclicTangent (q ∘ cyclicVertexEquiv e) (penultimateIndex hq.size_ge_three))
        (cyclicTangent (q ∘ cyclicVertexEquiv e) (lastIndex hq.size_ge_three)) < 0)
    (ε : ℝ) (hε : 0 < ε)
    (hbound : ε < geometricRadius hq.size_ge_three (q ∘ cyclicVertexEquiv e))
    (hroots : Set.InjOn
      (criticalRoot (extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε))
      ↑(criticalPairs (extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε) n)) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    ∃ (u v : EventIndex Q n) (F : DirectGLSSW.EdgeChord q e → EventIndex Q n),
      eventTime Q n u = 0 ∧
      eventTime Q n v = (q e).1-(q (cyclicSuccessor e)).1 ∧
      eventPair Q n u = (1,2) ∧ eventPair Q n v = (n-1,n) ∧
      (∀ z, eventTime Q n (F z) = (crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
        eventPair Q n (F z) = (returnRank q e z+1,returnRank q e z+2)) ∧
      polygonAmplitude q hq =
        ∑ T : EdgeSeparatingSupport q hq.g2 e (hV.trans hU.symm) hleft,
          let L := (edgeSupportOrderEquiv q hq.g2 hq.size_ge_three e
            (hV.trans hU.symm) hleft T).val
          (-1 : ℚ)^(T.val.card+1) * ∏ i : Fin (L.length+1),
            eventMatrix Q n (leftBoundary u F L i) (rightBoundary v F L i) := by
  dsimp only
  let P := q ∘ cyclicVertexEquiv e
  let Q := extendedArc hq.size_ge_three P ε
  have hP := InteriorEdgeEvents.opened_generic q hq e
  have hPu : (P (zeroIndex hq.size_ge_three)).2 = 0 := by
    simpa only [P,InteriorEdgeEvents.opened_zero] using hU
  have hPv : (P (lastIndex hq.size_ge_three)).2 = 0 := by
    simpa only [P,InteriorEdgeEvents.opened_last] using hV
  have hPl : (P (zeroIndex hq.size_ge_three)).1 < (P (lastIndex hq.size_ge_three)).1 := by
    simpa only [P,InteriorEdgeEvents.opened_zero,InteriorEdgeEvents.opened_last] using hleft
  obtain ⟨u,v,E,hu,hv,hpu,hpv,huv,hE,_⟩ :=
    SelectedCellClippedWord.exists_actual_selected_cell_words q hq e hU hV hleft ε hε
  obtain ⟨u',v',hu',hv',huv',hamp⟩ :=
    MixedCapChainRestriction.exists_amplitude_eq_arcIncreasingCutSum hRI
      hq.size_ge_three P hP hPu hPv hPl hturn ε hε hbound hroots
  have huu : u'=u := (eventTime_strictMono Q n).injective (hu'.trans hu.symm)
  have hvv : v'=v := by
    apply (eventTime_strictMono Q n).injective
    change eventTime Q n v' = eventTime Q n v
    rw [hv',hv]
    simp only [P,InteriorEdgeEvents.opened_zero,InteriorEdgeEvents.opened_last]
  subst u'
  subst v'
  let Er := E.trans (interiorEventRanksEquiv Q n u v 0
    ((q e).1-(q (cyclicSuccessor e)).1) hu hv)
  let F := fun z => (E z).val
  have hF : ∀ z, (Er z).val = (F z).val := fun _ => rfl
  refine ⟨u,v,F,hu,hv,hpu,hpv,hE,?_⟩
  calc
    polygonAmplitude q hq = polygonAmplitude P hP :=
      (polygonAmplitude_relabel hRI hq (cyclicVertexEquiv e)
        (cyclicVertexEquiv_commutes_successor e)).symm
    _ = ∑ S : ArcIncreasingEventCuts Q n u v huv,
        (-1 : ℚ)^(S.val.val.card+1) * branchProduct (eventIntervalArray Q n)
          (cutVertices u.val v.val S.val.val) := hamp
    _ = _ := event_cut_sum_eq_support_cell_sum q hq e (hV.trans hU.symm) hleft
      Q u v huv Er F hF (q (cyclicSuccessor e)).1 (fun z => (hE z).1)
      hpu hpv (fun z => (hE z).2)


end DirectGLSSW.NormalizedMixedEdgeMatrixSum
