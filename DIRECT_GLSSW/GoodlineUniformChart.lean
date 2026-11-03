import LiteralHistorySupportedTruncation
import SupportingTruncationAuxiliary
import PolygonRebaseTurning
import PolygonRebaseGeometry

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.SourceTruncationScaleStability

open DirectGLSSW DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.HOMFLY
open DirectGLSSW.PolygonRebase DirectGLSSW.ExposedOpenPrimitive
open DirectGLSSW.HOMFLY.Gemini DirectGLSSW.HOMFLY.PrincipalTurning
open DirectGLSSW.HOMFLY.Coefficients
open DirectGLSSW.GeometricSmoothingWeights DirectGLSSW.TruncationDirection
open DirectGLSSW.SourceTruncationSupport
  DirectGLSSW.SourceTruncationLineWindow
  DirectGLSSW.CyclicCarrierClearing DirectGLSSW.AuxiliaryCarrierChart
  DirectGLSSW.UniversalCarrierDomain
open TruncationEdgeLift PolygonNonalternation TruncationDaughterEvents
open DaughterFirstReturn GeometricSmoothingWeights PermutationOrbits
open ExposedOpenPrimitive MvPolynomial Set

attribute [local instance] Classical.propDecidable

/-- The selected good-line scale retains the actual all-left source condition,
and its literal rebased truncation carries the old source evaluator data.  The
canonical carrier inventory remains attached to the unre-based truncation at
the very same scale. -/
theorem exists_literal_history_goodline_uniform_exposed_chart
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∃ c : MvPolynomial (Fin n × Fin 2) ℝ, c ≠ 0 ∧
      Dense {r : Fin n → PlanarPoint ℝ |
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0} ∧
      IsOpen {r : Fin n → PlanarPoint ℝ |
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0} ∧
      ∀ (r : Fin n → PlanarPoint ℝ) (hr : CyclicGeneric r),
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0 →
        ∀ (m : ℕ) (d : Fin m → PlanarPoint ℝ) (hd : CyclicGeneric d),
          LiteralCarrierPath (.inl ⟨n,r⟩) (.inl ⟨m,d⟩) →
          (∀ i : Fin m, 0 < planarDet (cyclicTangent d i)
            (cyclicTangent d (cyclicSuccessor i))) →
          ∃ hAuxD : auxiliaryGenericity d hd,
          ∃ hWindows : (∀ V : Set CarrierLine, IsOpen V → V.Nonempty →
            ∃ K ∈ V, UniversalLocus (canonicalAugmentedCarrier d K) ∧
              PairTransverse (canonicalAugmentedCarrier d K) ∧
              allCycleSecantExclusions (canonicalAugmentedCarrier d K)),
          ∃ a p : Fin m, cyclicSuccessor p = a ∧
          ∃ scale : ℝ, 0 < scale ∧ ∃ δ : ℝ, 0 < δ ∧
            ∀ ε : ℝ, 0 < ε → ε < δ →
              ε < 1 ∧ ε * scale < 1 ∧
              ∃ hT : CyclicGeneric (truncateCyclicCorner d a p scale ε),
              ∃ hAuxT : auxiliaryGenericity
                (truncateCyclicCorner d a p scale ε) hT,
                (∀ i : Fin (m+1), 0 < planarDet
                  (cyclicTangent (truncateCyclicCorner d a p scale ε) i)
                  (cyclicTangent (truncateCyclicCorner d a p scale ε)
                    (cyclicSuccessor i))) ∧
                LeftExposed (truncateCyclicCorner d a p scale ε) a.castSucc ∧
                polygonAmplitude (truncateCyclicCorner d a p scale ε) hT =
                  -polygonAmplitude d hd ∧
                separatingSmoothingSum (truncateCyclicCorner d a p scale ε) hT hAuxT =
                  -separatingSmoothingSum d hd hAuxD ∧
                (-1 : ℚ)^(m+1) * polygonAmplitude
                    (truncateCyclicCorner d a p scale ε) hT =
                  (-1 : ℚ)^m * polygonAmplitude d hd ∧
                (-1 : ℚ)^(m+1) * separatingSmoothingSum
                    (truncateCyclicCorner d a p scale ε) hT hAuxT =
                  (-1 : ℚ)^m * separatingSmoothingSum d hd hAuxD ∧
                ∃ E : PolygonCrossing d ≃ PolygonCrossing
                    (truncateCyclicCorner d a p scale ε),
                  (∀ c : PolygonCrossing d,
                    (E c).val = (edgeLift a c.val.1, edgeLift a c.val.2)) ∧
                  (∀ c : PolygonCrossing d,
                    crossingPoint (truncateCyclicCorner d a p scale ε) (E c) =
                      crossingPoint d c) ∧
                  (∀ S : Finset (PolygonCrossing d),
                    polygonNonalternating d hd.g2 S ↔
                      polygonNonalternating (truncateCyclicCorner d a p scale ε) hT.g2
                        (S.map E.toEmbedding)) ∧
                  (∀ (S : Finset (PolygonCrossing d))
                      (hS : polygonNonalternating d hd.g2 S),
                    ∃ hNew : CyclicGeneric (daughterVertex
                        (truncateCyclicCorner d a p scale ε) hT.g2
                        (S.map E.toEmbedding) (Sum.inl a.castSucc)),
                      polygonAmplitude (daughterVertex
                        (truncateCyclicCorner d a p scale ε) hT.g2
                        (S.map E.toEmbedding) (Sum.inl a.castSucc)) hNew =
                        -polygonAmplitude (daughterVertex d hd.g2 S (Sum.inl a))
                          (hAuxD S hS (Sum.inl a))) ∧
                actualDaughterSecants (truncateCyclicCorner d a p scale ε) hT ∧
                UniversalLocus (polygonCarrierCoordinates
                  (truncateCyclicCorner d a p scale ε)) ∧
                PairTransverse (polygonCarrierCoordinates
                  (truncateCyclicCorner d a p scale ε)) ∧
                allCycleSecantExclusions (polygonCarrierCoordinates
                  (truncateCyclicCorner d a p scale ε)) ∧
                ∃ Q : Fin (m+1) → PlanarPoint ℝ,
                Q = truncateCyclicCorner d a p scale ε ∘ atEdge a.castSucc ∧
                ∃ hQ : CyclicGeneric Q,
                ∃ hAuxQ : auxiliaryGenericity Q hQ,
                  (∀ i, 0 < planarDet (cyclicTangent Q i)
                    (cyclicTangent Q (cyclicSuccessor i))) ∧
                  LeftExposed Q 0 ∧
                  (positivePolygonEventDiagram Q hQ).nCrossing =
                    (positivePolygonEventDiagram d hd).nCrossing ∧
                  PrincipalTurning.totalTurn
                    (positivePolygonEventDiagram Q hQ) =
                    PrincipalTurning.totalTurn
                      (positivePolygonEventDiagram d hd) ∧
                  PrincipalTurning.turnInteger
                    (positivePolygonEventDiagram Q hQ) =
                    PrincipalTurning.turnInteger
                      (positivePolygonEventDiagram d hd) ∧
                  Gemini.candidateEvaluator
                    (positivePolygonEventDiagram Q hQ)
                    (positivePolygonEventDiagram_nArc_pos Q hQ) =
                    Gemini.candidateEvaluator
                      (positivePolygonEventDiagram d hd)
                      (positivePolygonEventDiagram_nArc_pos d hd) ∧
                  coeff (Gemini.candidateEvaluator
                      (positivePolygonEventDiagram Q hQ)
                      (positivePolygonEventDiagram_nArc_pos Q hQ))
                    (1 - ((positivePolygonEventDiagram Q hQ).nCrossing : ℤ) -
                      |PrincipalTurning.turnInteger
                        (positivePolygonEventDiagram Q hQ)|) 0 =
                  coeff (Gemini.candidateEvaluator
                      (positivePolygonEventDiagram d hd)
                      (positivePolygonEventDiagram_nArc_pos d hd))
                    (1 - ((positivePolygonEventDiagram d hd).nCrossing : ℤ) -
                      |PrincipalTurning.turnInteger
                        (positivePolygonEventDiagram d hd)|) 0 := by
  obtain ⟨c,hc,hDense,hOpen,hHistory⟩ :=
    exists_original_coefficient_with_supported_truncations_for_all_literal_histories
      hRI q hq
  refine ⟨c,hc,hDense,hOpen,?_⟩
  intro r hr hrc m d hd hpath hleftD
  obtain ⟨hAuxD,hWindows,hcorner⟩ := hHistory r hr hrc m d hd hpath
  have hn : 3 ≤ m := by exact hd.size_ge_three
  obtain ⟨a,v,hv⟩ := exists_strict_support_vertex (by omega) d
    (cyclicNoncollinear_injective hd.size_ge_three d hd.g1)
  let p := (cyclicSuccessorPerm m).symm a
  have hp : cyclicSuccessor p = a :=
    (cyclicSuccessorPerm m).apply_symm_apply a
  have hturn : 0 < planarDet (d a-d p) (d (cyclicSuccessor a)-d a) := by
    simpa only [cyclicTangent,hp] using hleftD p
  have hexposed : ∀ i : Fin m, i ≠ a → 0 < planarDet v (d i-d a) := hv
  obtain ⟨scale,hscale,δ,hδ,hFamily⟩ := hcorner a p hp hturn v hexposed
  refine ⟨hAuxD,hWindows,a,p,hp,scale,hscale,δ,hδ,?_⟩
  intro ε hε hεδ
  obtain ⟨hε1,hεs1,hT,hAuxT,hExposeT,hamp,hsum,hAmpParity,hSumParity,E,
      hlabels,hpoints,hsep,hAffected,hDaughterSecants,hU,hTrans,hC⟩ :=
    hFamily ε hε hεδ
  have hleftT := truncate_uniform_left d hd hleftD a p hp scale ε hε hε1
    (mul_pos hε hscale) hεs1
  let ρ := atEdge a.castSucc
  let Q := (truncateCyclicCorner d a p scale ε) ∘ ρ
  let hQ : CyclicGeneric Q := cyclicGeneric_relabel
    (truncateCyclicCorner d a p scale ε) ρ (atEdge_commutes_successor _) hT
  let hAuxQ : auxiliaryGenericity Q hQ := auxiliaryGenericity_relabel
    (truncateCyclicCorner d a p scale ε) hT ρ (atEdge_commutes_successor _) hAuxT
  have hleftQ := strictLeft_relabel (truncateCyclicCorner d a p scale ε)
    ρ (atEdge_commutes_successor _) hleftT
  have hExposeQ : LeftExposed Q 0 := by
    apply leftExposed_relabel (truncateCyclicCorner d a p scale ε)
      ρ (atEdge_commutes_successor _)
    have hz : ρ (0 : Fin (m+1)) = a.castSucc :=
      atEdge_zero a.castSucc (by omega)
    rw [hz]
    exact hExposeT
  have hcountT := truncation_positive_crossing_count d hd a p scale ε hT E
  have htotalT := truncate_positive_totalTurn_eq d hd a p hp scale ε hε hε1
    (mul_pos hε hscale) hεs1 hT hturn
  have hdegreeT := truncate_positive_turnInteger_eq d hd a p hp scale ε hε hε1
    (mul_pos hε hscale) hεs1 hT hturn
  have hEvalT := truncation_positive_normalizedEvaluator d hd a p hp scale ε
    hε hε1 (mul_pos hε hscale) hεs1 hT E
    (fun c => congrArg Prod.fst (hlabels c))
    (fun c => congrArg Prod.snd (hlabels c)) hpoints Gemini.candidateEvaluator
    (Gemini.candidateEvaluator_isNormalized Gemini.all_lowerCrossingEvaluatorSkeinIH)
  have hcountQ : (positivePolygonEventDiagram Q hQ).nCrossing =
      (positivePolygonEventDiagram d hd).nCrossing := by
    calc
      (positivePolygonEventDiagram Q hQ).nCrossing =
          (positivePolygonEventDiagram (truncateCyclicCorner d a p scale ε) hT).nCrossing := by
        simpa [Q] using (positiveDiagram_crossingCount
          (truncateCyclicCorner d a p scale ε) ρ (atEdge_commutes_successor _) hT)
      _ = (positivePolygonEventDiagram d hd).nCrossing := hcountT.symm
  have htotalQ : PrincipalTurning.totalTurn (positivePolygonEventDiagram Q hQ) =
      PrincipalTurning.totalTurn (positivePolygonEventDiagram d hd) := by
    calc
      PrincipalTurning.totalTurn (positivePolygonEventDiagram Q hQ) =
          PrincipalTurning.totalTurn
            (positivePolygonEventDiagram (truncateCyclicCorner d a p scale ε) hT) := by
        simpa [Q] using totalTurn_relabel
          (truncateCyclicCorner d a p scale ε) hT ρ (atEdge_commutes_successor _)
      _ = PrincipalTurning.totalTurn (positivePolygonEventDiagram d hd) := htotalT
  have hdegreeQ : PrincipalTurning.turnInteger (positivePolygonEventDiagram Q hQ) =
      PrincipalTurning.turnInteger (positivePolygonEventDiagram d hd) := by
    calc
      PrincipalTurning.turnInteger (positivePolygonEventDiagram Q hQ) =
          PrincipalTurning.turnInteger
            (positivePolygonEventDiagram (truncateCyclicCorner d a p scale ε) hT) := by
        simpa [Q] using turnInteger_relabel
          (truncateCyclicCorner d a p scale ε) hT ρ (atEdge_commutes_successor _)
      _ = PrincipalTurning.turnInteger (positivePolygonEventDiagram d hd) := hdegreeT
  have hEvalQ : Gemini.candidateEvaluator (positivePolygonEventDiagram Q hQ)
      (positivePolygonEventDiagram_nArc_pos Q hQ) =
      Gemini.candidateEvaluator (positivePolygonEventDiagram d hd)
        (positivePolygonEventDiagram_nArc_pos d hd) := by
    calc
      Gemini.candidateEvaluator (positivePolygonEventDiagram Q hQ)
          (positivePolygonEventDiagram_nArc_pos Q hQ) =
        Gemini.candidateEvaluator
          (positivePolygonEventDiagram (truncateCyclicCorner d a p scale ε) hT)
          (positivePolygonEventDiagram_nArc_pos _ hT) := by
            simpa [Q] using candidateEvaluator_relabel
              (truncateCyclicCorner d a p scale ε) hT ρ (atEdge_commutes_successor _)
      _ = Gemini.candidateEvaluator (positivePolygonEventDiagram d hd)
          (positivePolygonEventDiagram_nArc_pos d hd) := hEvalT.symm
  have hcoeff : coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram Q hQ)
        (positivePolygonEventDiagram_nArc_pos Q hQ))
      (1 - ((positivePolygonEventDiagram Q hQ).nCrossing : ℤ) -
        |PrincipalTurning.turnInteger (positivePolygonEventDiagram Q hQ)|) 0 =
      coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram d hd)
        (positivePolygonEventDiagram_nArc_pos d hd))
      (1 - ((positivePolygonEventDiagram d hd).nCrossing : ℤ) -
        |PrincipalTurning.turnInteger (positivePolygonEventDiagram d hd)|) 0 := by
    rw [hEvalQ,hcountQ,hdegreeQ]
  refine ⟨hε1,hεs1,hT,hAuxT,hleftT,hExposeT,hamp,hsum,hAmpParity,
    hSumParity,E,hlabels,hpoints,hsep,hAffected,hDaughterSecants,hU,hTrans,hC,
    Q,rfl,hQ,hAuxQ,hleftQ,hExposeQ,hcountQ,htotalQ,hdegreeQ,hEvalQ,hcoeff⟩

end DirectGLSSW.SourceTruncationScaleStability
