import WorkingAuxiliaryCertificate
import GoodlineUniformChart

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceAuxiliaryWorkingDomain

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

open DirectGLSSW.SourceTruncationScaleStability
open EdgeAffineNormalization ExtendedReturnArcGeometry InteriorEdgeEvents

/-- Complete literal product-locus characterization. -/
theorem workingAuxiliaryDomain_mul {n : ℕ}
    (a b : MvPolynomial (Fin n × Fin 2) ℝ) :
    workingAuxiliaryDomain (a*b) = workingAuxiliaryDomain a ∩ workingAuxiliaryDomain b := by
  ext r
  simp only [mem_workingAuxiliaryDomain_iff,Set.mem_inter_iff,map_mul,mul_ne_zero_iff]
  tauto

/-- The product of the two independently produced nonzero coefficients gives
ONE working locus supporting both complete histories and actual uniform charts.
No equality of existential coefficient witnesses is assumed. -/
theorem exists_working_auxiliary_domain_with_goodline_charts
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∃ c : MvPolynomial (Fin n × Fin 2) ℝ, c ≠ 0 ∧
      Dense {r : Fin n → PlanarPoint ℝ |
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0} ∧
      IsOpen {r : Fin n → PlanarPoint ℝ |
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0} ∧
      (∀ U : Set (Fin n → PlanarPoint ℝ), IsOpen U →
        (∀ r ∈ U, CyclicGeneric r) →
        U ∩ workingAuxiliaryDomain c =
          U \ {r | eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c = 0} ∧
        IsOpen (U ∩ workingAuxiliaryDomain c) ∧
        U ⊆ closure (U ∩ workingAuxiliaryDomain c) ∧
        (U.Nonempty → (U ∩ workingAuxiliaryDomain c).Nonempty)) ∧
      (∀ (r : Fin n → PlanarPoint ℝ) (hr : CyclicGeneric r),
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0 →
        ∀ (m : ℕ) (d : Fin m → PlanarPoint ℝ) (hd : CyclicGeneric d),
          LiteralCarrierPath (.inl ⟨n,r⟩) (.inl ⟨m,d⟩) →
          GeometricSmoothingWeights.auxiliaryGenericity d hd ∧ actualDaughterSecants d hd ∧
          UniversalLocus (polygonCarrierCoordinates d) ∧
          PairTransverse (polygonCarrierCoordinates d) ∧
          allCycleSecantExclusions (polygonCarrierCoordinates d) ∧
          (∀ e : Fin m,
            let P := normalizedPolygon d e ∘ cyclicVertexEquiv e
            ∃ ε : ℝ, 0 < ε ∧ ε < geometricRadius hd.size_ge_three P ∧
              Set.InjOn (CapCriticalEventGeometry.criticalRoot (extendedArc hd.size_ge_three P ε))
                ↑(CapCriticalTimes.criticalPairs (extendedArc hd.size_ge_three P ε) m) ∧
              ∀ t : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
                ∀ a b : Fin m, a.val < b.val →
                  CyclicGeneric (GlobalCapEntry.lineCapCore
                    (CapCrossingEvent.horizontalMove (extendedArc hd.size_ge_three P ε) (t+s)) a b)) ∧
          ∀ V : Set CarrierLine, IsOpen V → V.Nonempty → ∃ K ∈ V,
            UniversalLocus (canonicalAugmentedCarrier d K) ∧
            PairTransverse (canonicalAugmentedCarrier d K) ∧
            allCycleSecantExclusions (canonicalAugmentedCarrier d K)) ∧
      (∀ (r : Fin n → PlanarPoint ℝ) (hr : CyclicGeneric r),
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0 →
        ∀ (m : ℕ) (d : Fin m → PlanarPoint ℝ) (hd : CyclicGeneric d),
          LiteralCarrierPath (.inl ⟨n,r⟩) (.inl ⟨m,d⟩) →
          ∃ hAuxD : auxiliaryGenericity d hd,
          ∃ hWindows : (∀ V : Set CarrierLine, IsOpen V → V.Nonempty →
            ∃ K ∈ V, UniversalLocus (canonicalAugmentedCarrier d K) ∧
              PairTransverse (canonicalAugmentedCarrier d K) ∧
              allCycleSecantExclusions (canonicalAugmentedCarrier d K)),
          ∀ (a p : Fin m) (hp : cyclicSuccessor p = a)
            (hturn : 0 < planarDet (d a-d p) (d (cyclicSuccessor a)-d a))
            (v : PlanarPoint ℝ)
            (hexposed : ∀ i : Fin m, i ≠ a →
              0 < planarDet v (d i-d a)),
            ∃ scale : ℝ, 0 < scale ∧ ∃ δ : ℝ, 0 < δ ∧
              (∀ ε : ℝ, 0 < ε → ε < δ →
                ε < 1 ∧ ε*scale < 1 ∧
                ∃ hQ : CyclicGeneric (truncateCyclicCorner d a p scale ε),
                ∃ hAuxQ : auxiliaryGenericity (truncateCyclicCorner d a p scale ε) hQ,
                  LeftExposed (truncateCyclicCorner d a p scale ε) a.castSucc ∧
                  polygonAmplitude (truncateCyclicCorner d a p scale ε) hQ =
                    -polygonAmplitude d hd ∧
                  separatingSmoothingSum (truncateCyclicCorner d a p scale ε) hQ hAuxQ =
                    -separatingSmoothingSum d hd hAuxD ∧
                  (-1 : ℚ)^(m+1)*polygonAmplitude (truncateCyclicCorner d a p scale ε) hQ =
                    (-1 : ℚ)^m*polygonAmplitude d hd ∧
                  (-1 : ℚ)^(m+1)*separatingSmoothingSum
                      (truncateCyclicCorner d a p scale ε) hQ hAuxQ =
                    (-1 : ℚ)^m*separatingSmoothingSum d hd hAuxD ∧
                  ∃ E : PolygonCrossing d ≃ PolygonCrossing (truncateCyclicCorner d a p scale ε),
                    (∀ c : PolygonCrossing d,
                      (E c).val = (edgeLift a c.val.1,edgeLift a c.val.2)) ∧
                    (∀ c : PolygonCrossing d,
                      crossingPoint (truncateCyclicCorner d a p scale ε) (E c) =
                        crossingPoint d c) ∧
                    (∀ S : Finset (PolygonCrossing d),
                      polygonNonalternating d hd.g2 S ↔
                        polygonNonalternating (truncateCyclicCorner d a p scale ε) hQ.g2
                          (S.map E.toEmbedding)) ∧
                    (∀ (S : Finset (PolygonCrossing d))
                        (hS : polygonNonalternating d hd.g2 S),
                      ∃ hNew : CyclicGeneric (daughterVertex (truncateCyclicCorner d a p scale ε)
                        hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)),
                        polygonAmplitude (daughterVertex (truncateCyclicCorner d a p scale ε)
                          hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)) hNew =
                          -polygonAmplitude (daughterVertex d hd.g2 S (Sum.inl a))
                            (hAuxD S hS (Sum.inl a))) ∧
                  actualDaughterSecants (truncateCyclicCorner d a p scale ε) hQ ∧
                  UniversalLocus (polygonCarrierCoordinates (truncateCyclicCorner d a p scale ε)) ∧
                  PairTransverse (polygonCarrierCoordinates (truncateCyclicCorner d a p scale ε)) ∧
                  allCycleSecantExclusions (polygonCarrierCoordinates (truncateCyclicCorner d a p scale ε)))) ∧
      (∀ (r : Fin n → PlanarPoint ℝ) (hr : CyclicGeneric r),
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
                        (positivePolygonEventDiagram d hd)|) 0) := by
  obtain ⟨a,ha,hDA,hOA,hOpenA,hHistory,hFixed⟩ :=
    exists_working_auxiliary_domain_with_history_and_fixed_scale hRI q hq
  obtain ⟨b,hb,hDB,hOB,hChart⟩ :=
    exists_literal_history_goodline_uniform_exposed_chart hRI q hq
  have heq : {r : Fin n → PlanarPoint ℝ |
      eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) (a*b) ≠ 0} =
      {r | eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) a ≠ 0} ∩
      {r | eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) b ≠ 0} := by
    ext r
    simp only [Set.mem_setOf_eq,Set.mem_inter_iff,map_mul,mul_ne_zero_iff]
  have hD : Dense {r : Fin n → PlanarPoint ℝ |
      eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) (a*b) ≠ 0} := by
    rw [heq]
    exact hDA.inter_of_isOpen_left hDB hOA
  have hO : IsOpen {r : Fin n → PlanarPoint ℝ |
      eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) (a*b) ≠ 0} := by
    rw [heq]
    exact hOA.inter hOB
  have hsplit (r : Fin n → PlanarPoint ℝ)
      (h : eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) (a*b) ≠ 0) :
      eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) a ≠ 0 ∧
      eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) b ≠ 0 := by
    simpa only [map_mul,mul_ne_zero_iff] using h
  refine ⟨a*b,mul_ne_zero ha hb,hD,hO,?_,?_,?_,?_⟩
  · intro U hU hGeneric
    exact ⟨workingAuxiliaryDomain_inter_eq_diff (a*b) U hGeneric,
      workingAuxiliaryDomain_on_open (a*b) hD hO U hU hGeneric⟩
  · intro r hr hrc
    exact hHistory r hr (hsplit r hrc).1
  · intro r hr hrc
    exact hFixed r hr (hsplit r hrc).1
  · intro r hr hrc
    exact hChart r hr (hsplit r hrc).2

end DirectGLSSW.SourceAuxiliaryWorkingDomain


