import PolygonSuppliedInitialization
import PositivePolygonEvaluatorLocality
import PolygonTurnLocality
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PhysicalSourceInitialization
open Filter Topology GeometricSmoothingWeights ExposedOpenPrimitive ActiveArc.ExposedChart
  UniversalCarrierDomain AuxiliaryCarrierChart HOMFLY HOMFLY.PolygonDrawingBridge
  HOMFLY.PrincipalTurning HOMFLY.Coefficients

theorem exists_nearby_source_full_preservation (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q 0) (hAux : auxiliaryGenericity q hq)
    (hl : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (V : Set (Fin (n+2) → PlanarPoint ℝ)) (hV : V∈𝓝 q) :
    ∃ p∈V, ∃ hp : CyclicGeneric p, ∃ hAp : auxiliaryGenericity p hp,
      LeftExposed p 0 ∧
      (∀ i, 0 < planarDet (cyclicTangent p i) (cyclicTangent p (cyclicSuccessor i))) ∧
      separatingSmoothingSum p hp hAp=separatingSmoothingSum q hq hAux ∧
      (positivePolygonEventDiagram p hp).nCrossing=(positivePolygonEventDiagram q hq).nCrossing ∧
      Gemini.candidateEvaluator (positivePolygonEventDiagram p hp) (positivePolygonEventDiagram_nArc_pos p hp)=
        Gemini.candidateEvaluator (positivePolygonEventDiagram q hq) (positivePolygonEventDiagram_nArc_pos q hq) ∧
      turnInteger (positivePolygonEventDiagram p hp)=turnInteger (positivePolygonEventDiagram q hq) ∧
      coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram p hp) (positivePolygonEventDiagram_nArc_pos p hp))
          (1-((positivePolygonEventDiagram p hp).nCrossing:ℤ)-|turnInteger (positivePolygonEventDiagram p hp)|) 0 =
        coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq) (positivePolygonEventDiagram_nArc_pos q hq))
          (1-((positivePolygonEventDiagram q hq).nCrossing:ℤ)-|turnInteger (positivePolygonEventDiagram q hq)|) 0 ∧
      ∃ L : Fin (n+1) ⊕ Unit → CarrierLine, UniversalLocus L ∧ PairTransverse L ∧
        (∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (cutArc p 0 e.castSucc)=0 ∧
          lineValue (L (Sum.inl e)) (cutArc p 0 e.succ)=0) ∧
        lineValue (L (Sum.inr ())) (cutArc p 0 ⟨n+1,by omega⟩)=0 := by
  let W := V ∩ {p | ∃ hp : CyclicGeneric p,
      (positivePolygonEventDiagram p hp).nCrossing=(positivePolygonEventDiagram q hq).nCrossing ∧
      Gemini.candidateEvaluator (positivePolygonEventDiagram p hp) (positivePolygonEventDiagram_nArc_pos p hp)=
        Gemini.candidateEvaluator (positivePolygonEventDiagram q hq) (positivePolygonEventDiagram_nArc_pos q hq) ∧
      turnInteger (positivePolygonEventDiagram p hp)=turnInteger (positivePolygonEventDiagram q hq)}
  have hW : W∈𝓝 q := by
    apply inter_mem hV
    filter_upwards [PositivePolygonLocality.eventually_positivePolygon_evaluator_count q hq,
      PolygonTurnLocality.eventually_positivePolygon_turnInteger q hq] with p hE hT
    obtain ⟨hp,hcount,hEval⟩ := hE
    exact ⟨hp,hcount,hEval,hT hp⟩
  obtain ⟨p,hpW,hp,hAp,hEp,hleft,hν,L,hL,hT,hinc,hterm⟩ :=
    exists_nearby_source_supplied hRI q hq he hAux hl W hW
  obtain ⟨hp',hcount,hEval,hTurn⟩ := hpW.2
  refine ⟨p,hpW.1,hp,hAp,hEp,hleft,hν,hcount,hEval,hTurn,?_,L,hL,hT,hinc,hterm⟩
  rw [hcount,hEval,hTurn]
end DirectGLSSW.PhysicalSourceInitialization
