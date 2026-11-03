import CyclicCarrierRealization
import AllEdgeCapRealization

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open DaughterFirstReturn GeometricSmoothingWeights AuxiliaryCarrierChart UniversalCarrierDomain
open EdgeAffineNormalization ExtendedReturnArcGeometry InteriorEdgeEvents
open Filter Topology

/-- Every edge of every retained actual daughter admits a permissible extension.
The extension is existential per daughter/edge, not universal in its parameter. -/
theorem actual_daughter_edge_cap_realization {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq) (hsec : actualDaughterSecants q hq)
    (S : Finset (PolygonCrossing q))
    (hS : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (root : PolygonEvent q) (hroot : retainedCorner q S root)
    (e : Fin (Fintype.card (CornerCoord q hq.g2 S root))) :
    let d := daughterVertex q hq.g2 S root
    let hd := hAux S hS root
    let m := Fintype.card (CornerCoord q hq.g2 S root)
    let P := normalizedPolygon d e ∘ cyclicVertexEquiv e
    ∃ ε : ℝ, 0 < ε ∧ ε < geometricRadius hd.size_ge_three P ∧
      Set.InjOn (CapCriticalEventGeometry.criticalRoot (extendedArc hd.size_ge_three P ε))
        ↑(CapCriticalTimes.criticalPairs (extendedArc hd.size_ge_three P ε) m) ∧
      ∀ t : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
        ∀ a b : Fin m, a.val < b.val →
          CyclicGeneric (GlobalCapEntry.lineCapCore
            (CapCrossingEvent.horizontalMove (extendedArc hd.size_ge_three P ε) (t+s)) a b) := by
  exact AllEdgeCapRealization.every_edge_realization _ (hAux S hS root)
    (hsec S hS root hroot).2 (hsec S hS root hroot).1 e

/-- Simultaneous original-parent-space construction. No hAux, secant exclusion,
properness, daughter genericity, or selected extension is an input. -/
theorem exists_joint_daughter_cap_realizations {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (U : Set (Fin n → PlanarPoint ℝ)) (hU : U ∈ 𝓝 q) :
    ∃ r ∈ U, ∃ hr : CyclicGeneric r, ∃ hAux : auxiliaryGenericity r hr,
      (∃ L : Fin n → CarrierLine, UniversalLocus L ∧ PairTransverse L ∧
        (∀ i, lineValue (L i) (r i) = 0 ∧ lineValue (L i) (r (cyclicSuccessor i)) = 0)) ∧
      ∀ (S : Finset (PolygonCrossing r))
        (hS : PolygonNonalternation.polygonNonalternating r hr.g2 S)
        (root : PolygonEvent r), retainedCorner r S root →
        ∀ e : Fin (Fintype.card (CornerCoord r hr.g2 S root)),
        let d := daughterVertex r hr.g2 S root
        let hd := hAux S hS root
        let m := Fintype.card (CornerCoord r hr.g2 S root)
        let P := normalizedPolygon d e ∘ cyclicVertexEquiv e
        ∃ ε : ℝ, 0 < ε ∧ ε < geometricRadius hd.size_ge_three P ∧
          Set.InjOn (CapCriticalEventGeometry.criticalRoot (extendedArc hd.size_ge_three P ε))
            ↑(CapCriticalTimes.criticalPairs (extendedArc hd.size_ge_three P ε) m) ∧
          ∀ t : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
            ∀ a b : Fin m, a.val < b.val →
              CyclicGeneric (GlobalCapEntry.lineCapCore
                (CapCrossingEvent.horizontalMove (extendedArc hd.size_ge_three P ε) (t+s)) a b) := by
  obtain ⟨r, hrU, hr, hAux, hsec, hL⟩ := exists_joint_realization q hq U hU
  refine ⟨r, hrU, hr, hAux, hL, ?_⟩
  exact actual_daughter_edge_cap_realization r hr hAux hsec

end DirectGLSSW.CyclicCarrierClearing


