import LiteralCarrierProvenance
import FiniteCalculationCertificate

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain MvPolynomial Set
open EdgeAffineNormalization ExtendedReturnArcGeometry InteriorEdgeEvents

/-- The SAME proper original-coordinate exclusion supplies the complete
calculation certificate at every generic closed endpoint of a finite literal
history. The original-carrier labels and incidences are derived from the path,
not supplied as consumer premises. No assertion of universal descent is made. -/
theorem exists_original_coefficient_for_all_literal_history_calculations {n : ℕ}
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
            allCycleSecantExclusions (canonicalAugmentedCarrier d K) := by
  obtain ⟨c,hc,hD,hO,hW⟩ := exists_original_coefficient_with_subcycle_caps_and_windows q hq
  refine ⟨c,hc,hD,hO,?_⟩
  intro r hr hrc m d hd hpath
  obtain ⟨_,_,_,hT,_,hSubcycle⟩ := hW r hr hrc
  have hProv := literalCarrierHistory_original_provenance r hT (.inl ⟨m,d⟩) hpath
  obtain ⟨f,hf,hi⟩ := (originalCarrierProvenance_closed_iff r d).mp hProv
  exact hSubcycle m d hd f hf hi

end DirectGLSSW.CyclicCarrierClearing

