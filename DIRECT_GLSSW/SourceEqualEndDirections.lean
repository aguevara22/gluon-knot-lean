import ChosenEdgeNormalization
import NormalizedEdgeTurns
import ExtendedReturnCapInverse

set_option autoImplicit false

namespace DirectGLSSW.SourceEqualEndDirections
open DirectGLSSW EdgeAffineNormalization ChosenEdgeNormalization
open ExtendedReturnArcGeometry InteriorEdgeEvents NormalizedEdgeTurns
open OrderedCapEvents CapCriticalTimes CapCriticalEventGeometry

/-- The source's chosen-edge coordinate change and cyclic opening feed the
actual endpoint-event cap inverse. The events are on the normalized opened
polygon, exactly as in the proof's chosen coordinates. -/
theorem chosen_edge_equal_end_directions (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hturn : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
      planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0)
    (ε : ℝ) (hε : 0 < ε)
    (hbound : ε < geometricRadius hq.size_ge_three
      ((normalizedPolygon q e) ∘ cyclicVertexEquiv e))
    (hroots : Set.InjOn
      (criticalRoot (extendedArc hq.size_ge_three
        ((normalizedPolygon q e) ∘ cyclicVertexEquiv e) ε))
      ↑(criticalPairs (extendedArc hq.size_ge_three
        ((normalizedPolygon q e) ∘ cyclicVertexEquiv e) ε) n)) :
    let P := (normalizedPolygon q e) ∘ cyclicVertexEquiv e
    ∃ cU cV : EventIndex (extendedArc hq.size_ge_three P ε) n,
      eventTime (extendedArc hq.size_ge_three P ε) n cU = 0 ∧
      eventTime (extendedArc hq.size_ge_three P ε) n cV =
        ((normalizedPolygon q e) e).1-
          ((normalizedPolygon q e) (cyclicSuccessor e)).1 ∧
      cU < cV ∧
      eventMatrix (extendedArc hq.size_ge_three P ε) n cU cV = polygonAmplitude q hq ∧
      finiteInverse (eventMatrix (extendedArc hq.size_ge_three P ε) n)
        (actualTimes (extendedArc hq.size_ge_three P ε) n).card cU cV = 0 := by
  let R := normalizedPolygon q e
  let P := R ∘ cyclicVertexEquiv e
  have hR : CyclicGeneric R := normalizedPolygon_generic q hq e
  have hP : CyclicGeneric P := opened_generic R hR e
  obtain ⟨hV,hU,hleft⟩ := normalizedPolygon_leftward q hq e
  have hU' : (P (zeroIndex hq.size_ge_three)).2 = 0 := by
    simpa only [P,opened_zero] using hU
  have hV' : (P (lastIndex hq.size_ge_three)).2 = 0 := by
    simpa only [P,opened_last] using hV
  have hleft' : (P (zeroIndex hq.size_ge_three)).1 <
      (P (lastIndex hq.size_ge_three)).1 := by
    simpa only [P,opened_zero,opened_last] using hleft
  have hturn' :
      planarDet (cyclicTangent P (lastIndex hq.size_ge_three))
        (cyclicTangent P (zeroIndex hq.size_ge_three)) *
      planarDet (cyclicTangent P (penultimateIndex hq.size_ge_three))
        (cyclicTangent P (lastIndex hq.size_ge_three)) < 0 := by
    rw [opened_endpoint_turn_product]
    exact (normalizedPolygon_endpoint_turn_product_neg_iff q hq e).mpr hturn
  obtain ⟨cU,cV,htU,htV,hord,hX,hK⟩ :=
    ExtendedReturnCapInverse.exists_endpoint_matrix_and_inverse hRI
      hq.size_ge_three P hP hU' hV' hleft' hturn' ε hε hbound hroots
  have hAmp : polygonAmplitude P hP = polygonAmplitude q hq := by
    calc
      polygonAmplitude P hP = polygonAmplitude R hR := by
        simpa only [P] using
          (polygonAmplitude_relabel hRI hR (cyclicVertexEquiv e)
            (cyclicVertexEquiv_commutes_successor e))
      _ = polygonAmplitude q hq := (normalizedPolygon_amplitude q hq e).symm
  exact ⟨cU,cV,htU,by simpa only [P,opened_zero,opened_last] using htV,
    hord,hX.trans hAmp,hK⟩


end DirectGLSSW.SourceEqualEndDirections
