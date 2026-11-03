import ActualOpenStateClosure
import CutArcSuppliedCarriers
import InitialExposedCore
import LocalCarrierPolygonRecovery
import PhysicalCalculationExists

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open ActiveArc ActiveArc.ExposedChart ActiveArc.Primitive ActiveArc.FiniteCalculation
open AuxiliaryCarrierChart UniversalCarrierDomain GeometricSmoothingWeights
open ExposedOpenPrimitive

/-- All inherited turns of the actual cut are the corresponding cyclic turns. -/
theorem actual_cut_remainingLeft {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (e : Fin (n+2))
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i)
      (cyclicTangent q (cyclicSuccessor i))) :
    TraversalClosure.RemainingLeft (cutArc q e) := by
  intro i
  change 0 < planarDet
    (cutArc q e i.castSucc.succ-cutArc q e i.castSucc.castSucc)
    (cutArc q e i.succ.succ-cutArc q e i.succ.castSucc)
  rw [cut_tangent,cut_tangent]
  have hn : edgeLabel e i.succ=cyclicSuccessor (edgeLabel e i.castSucc) :=
    edgeLabel_successor e i.castSucc
  rw [hn]
  exact hleft _

/-- The explicit good-line polygon initializes an actual finite calculation
on its literal cut. Every Domain field is produced, and the supplied family
is exactly the canonical polygon family with the deleted edge as terminal. -/
theorem actual_canonical_cut_calculation
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin (n+2))
    (he : LeftExposed q e) (hAux : auxiliaryGenericity q hq)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i)
      (cyclicTangent q (cyclicSuccessor i)))
    (hU : UniversalLocus (polygonCarrierCoordinates q))
    (hT : PairTransverse (polygonCarrierCoordinates q)) :
    ∃ D : Domain (cutArc q e),
      D.L = polygonCarrierCoordinates q ∘ cutCarrierLabel e ∧
      Calculation (cutArc q e) D := by
  obtain ⟨hL,hTrans,hinc,hterm⟩ := cutArc_universal_supplied q e
    (polygonCarrierCoordinates q) hU hT
    (fun i => ⟨polygonCarrierCoordinates_value_start q i,
      polygonCarrierCoordinates_value_successor q i⟩)
  have hG : cyclicNoncollinear (cutArc q e) := by
    intro i j k hij hjk hik
    exact hq.g1 (cyclicVertexEquiv e i) (cyclicVertexEquiv e j) (cyclicVertexEquiv e k)
      (fun h => hij ((cyclicVertexEquiv e).injective h))
      (fun h => hjk ((cyclicVertexEquiv e).injective h))
      (fun h => hik ((cyclicVertexEquiv e).injective h))
  let D : Domain (cutArc q e) :=
    ⟨cutArc_regular q e hq,hG,closedAuxiliary_of_parent q e hq he hAux,
      actual_cut_remainingLeft q e hleft,initial_exposed_all_support_core q e hq he hAux,
      polygonCarrierCoordinates q ∘ cutCarrierLabel e,hL,hTrans,hinc,hterm⟩
  exact ⟨D,rfl,calculation_exists hRI (cutArc q e) D⟩

end DirectGLSSW.CyclicCarrierClearing
