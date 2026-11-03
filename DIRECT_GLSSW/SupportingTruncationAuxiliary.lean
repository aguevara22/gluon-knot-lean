import SupportingEventAvoidance
import SupportingDaughterFamily
import SupportingTruncationFamily
import TruncationCornerUniformLeft
import DirectGLSSW.TruncationSeparatingSum
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open TruncationDirection TruncationEdgeLift ExposedOpenPrimitive Coefficients
open GeometricSmoothingWeights DaughterFirstReturn
attribute [local instance] Classical.propDecidable

/-- The same actual supporting truncation preserves the source's normalized
separating smoothing sum and prescribed HOMFLY coefficient. All auxiliary
components of the truncated polygon are produced from the original domain. -/
theorem exists_supporting_truncation_preserves_nu_and_corner
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq) :
    ∃ a p : Fin n, cyclicSuccessor p = a ∧ ∃ scale : ℝ, 0 < scale ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        ε < 1 ∧ ε * scale < 1 ∧
        ∃ hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε),
        ∃ hAuxQ : auxiliaryGenericity (truncateCyclicCorner q a p scale ε) hQ,
          (∀ i, 0 < planarDet (cyclicTangent (truncateCyclicCorner q a p scale ε) i)
            (cyclicTangent (truncateCyclicCorner q a p scale ε) (cyclicSuccessor i))) ∧
          LeftExposed (truncateCyclicCorner q a p scale ε) a.castSucc ∧
          polygonAmplitude (truncateCyclicCorner q a p scale ε) hQ = -polygonAmplitude q hq ∧
          separatingSmoothingSum (truncateCyclicCorner q a p scale ε) hQ hAuxQ =
            -separatingSmoothingSum q hq hAux ∧
          (-1 : ℚ)^(n+1) * separatingSmoothingSum (truncateCyclicCorner q a p scale ε) hQ hAuxQ =
            (-1 : ℚ)^n * separatingSmoothingSum q hq hAux ∧
          (positivePolygonEventDiagram q hq).nCrossing =
            (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ).nCrossing ∧
          PrincipalTurning.totalTurn
            (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ) =
            PrincipalTurning.totalTurn (positivePolygonEventDiagram q hq) ∧
          PrincipalTurning.turnInteger
            (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ) =
            PrincipalTurning.turnInteger (positivePolygonEventDiagram q hq) ∧
          Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
              (positivePolygonEventDiagram_nArc_pos q hq) =
            Gemini.candidateEvaluator (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ)
              (positivePolygonEventDiagram_nArc_pos _ hQ) ∧
          coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
              (positivePolygonEventDiagram_nArc_pos q hq))
              (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
                |PrincipalTurning.turnInteger (positivePolygonEventDiagram q hq)|) 0 =
            coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ)
              (positivePolygonEventDiagram_nArc_pos _ hQ))
              (1-((positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ).nCrossing : ℤ)-
                |PrincipalTurning.turnInteger (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ)|) 0 := by
  obtain ⟨a,p,hp,scale,hs,hsupport⟩ := exists_supporting_left_corner_scale q hq hleft
  have ht : 0 < planarDet (q a-q p) (q (cyclicSuccessor a)-q a) := by
    simpa only [cyclicTangent,hp] using hleft p
  have ha := strict_support_event_avoidance q hq a
    (scale • (q (cyclicSuccessor a)-q a)-(q p-q a)) hsupport
  obtain ⟨δK,hδK,hK⟩ := TruncationDaughterUniform.exists_fixedScale_truncation_all_affected_amplitudes
    hRI q hq a p hp ht scale hs ha (fun S hS => hAux S hS (Sum.inl a))
  obtain ⟨δE,hδE,hE⟩ := exists_small_truncation_leftExposed q a p scale hsupport
  refine ⟨a,p,hp,scale,hs,min δK δE,lt_min hδK hδE,?_⟩
  intro ε hε hεδ
  obtain ⟨hε1,hs1,hQ,hamp,E,hlabels,hpoint,hsep,hAffected⟩ :=
    hK ε hε (lt_of_lt_of_le hεδ (min_le_left _ _))
  have hl (c : PolygonCrossing q) := congrArg Prod.fst (hlabels c)
  have hr (c : PolygonCrossing q) := congrArg Prod.snd (hlabels c)
  have hAuxQ : auxiliaryGenericity (truncateCyclicCorner q a p scale ε) hQ :=
    TruncationDaughterGenericity.auxiliaryGenericity_transport q hq a p hp scale ε
      hε hε1 (mul_pos hε hs) hs1 hQ E hl hr hpoint hAux
      (fun S hS => (hAffected S hS).choose)
  have hsum : separatingSmoothingSum (truncateCyclicCorner q a p scale ε) hQ hAuxQ =
      -separatingSmoothingSum q hq hAux := by
    apply GeometricSmoothingSumTransport.separatingSmoothingSum_transport_neg
      q hq (truncateCyclicCorner q a p scale ε) hQ E hsep hAux hAuxQ
    intro S hS
    exact TruncationComponentWeights.componentAmplitudeProduct_truncation
      hRI q hq a p hp scale ε hε hε1 (mul_pos hε hs) hs1 hQ E hl hr hpoint
      hAux hAuxQ S hS ((hsep S).mp hS) (hAffected S hS)
  have hcount := truncation_positive_crossing_count q hq a p scale ε hQ E
  have hturn := truncate_positive_totalTurn_eq q hq a p hp scale ε hε hε1 (mul_pos hε hs) hs1 hQ ht
  have hdegree := truncate_positive_turnInteger_eq q hq a p hp scale ε hε hε1 (mul_pos hε hs) hs1 hQ ht
  have heval := truncation_positive_normalizedEvaluator q hq a p hp scale ε hε hε1
    (mul_pos hε hs) hs1 hQ E hl hr hpoint Gemini.candidateEvaluator
    (Gemini.candidateEvaluator_isNormalized Gemini.all_lowerCrossingEvaluatorSkeinIH)
  refine ⟨hε1,hs1,hQ,hAuxQ,
    truncate_uniform_left q hq hleft a p hp scale ε hε hε1 (mul_pos hε hs) hs1,
    hE ε hε (lt_of_lt_of_le hεδ (min_le_right _ _)),hamp,hsum,?_,hcount,hturn,hdegree,heval,?_⟩
  · rw [hsum,pow_succ];ring
  · rw [←heval,hcount,hdegree]
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
