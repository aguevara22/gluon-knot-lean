import LiteralHistoryCalculationCertificate
import LineWindowSupportedInventory

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.SourceTruncationScaleStability

open DirectGLSSW DirectGLSSW.CyclicCarrierClearing
  DirectGLSSW.SourceTruncationSupport
  DirectGLSSW.SourceTruncationLineWindow DirectGLSSW.TruncationDirection
  AuxiliaryCarrierChart UniversalCarrierDomain EdgeAffineNormalization
  ExtendedReturnArcGeometry InteriorEdgeEvents GeometricSmoothingWeights
  CapCriticalEventGeometry CapCriticalTimes CapCrossingEvent GlobalCapEntry
  MvPolynomial Set
open DaughterFirstReturn GeometricSmoothingWeights PermutationOrbits
open TruncationEdgeLift PolygonNonalternation TruncationDaughterEvents
open ExposedOpenPrimitive

/-- The same original-coordinate polynomial exclusion supplies source
auxiliary genericity and open augmented-carrier windows at every generic
closed endpoint of an actual literal history. Applying the recovered-scale
corner theorem then gives one scale with all-small-epsilon transport and
canonical inventory. -/
theorem exists_original_coefficient_with_supported_truncations_for_all_literal_histories
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
                  allCycleSecantExclusions (polygonCarrierCoordinates (truncateCyclicCorner d a p scale ε))) := by
  obtain ⟨c,hc,hDense,hOpen,hCertificate⟩ :=
    exists_original_coefficient_for_all_literal_history_calculations q hq
  refine ⟨c,hc,hDense,hOpen,?_⟩
  intro r hr hrc m d hd hpath
  obtain ⟨hAuxD,_hDaughtersD,_hUD,_hTD,_hCD,_hCaps,hWindows⟩ :=
    hCertificate r hr hrc m d hd hpath
  refine ⟨hAuxD,hWindows,?_⟩
  intro a p hp hturn v hexposed
  exact exists_supported_truncation_with_windows_at_scale hRI d hd hAuxD
    a p hp hturn v hexposed hWindows

end DirectGLSSW.SourceTruncationScaleStability
