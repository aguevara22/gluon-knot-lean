import UniversalCarrierEventDomain
import UniversalCarrierCornerDomain
import UniversalCarrierStateTransport
import UniversalCarrierReconstruction
import ActiveArcNormalizedCrossingTransport
import PhysicalTraversalClosure
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace DirectGLSSW.UniversalCarrierDomain
open ActiveArc ActiveArc.Cursor ActiveArc.RetainedWords ActiveArc.Primitive
open ActiveArc.CompatibleWords ActiveArc.SingletonWords
theorem exists_normalized_first_under_supplied
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (hRI : GLSSWRootIndependence) (hAux : ClosedAuxiliary q hR)
    (hcut : c.val.2.val=a) (hG1 : cyclicNoncollinear q)
    (L : Fin (a+b+1) ⊕ Unit → AuxiliaryCarrierChart.CarrierLine)
    (hU : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (a+b+1), AuxiliaryCarrierChart.lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      AuxiliaryCarrierChart.lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : AuxiliaryCarrierChart.lineValue (L (Sum.inr ())) (q ⟨a+b+1,by omega⟩)=0)
    (hu : crossingUnder q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1)
    (hleft : TraversalClosure.RemainingLeft q) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
    ∃ (hm0 : 0≤leftParameter q c-ε) (hmc : leftParameter q c-ε<leftParameter q c)
      (hcp : leftParameter q c<leftParameter q c+ε)
      (hpb : leftParameter q c+ε<afterBound q c),
    let hB := before_first_regular (a:=a+b) (b:=0) q hR c hc _ hm0 hmc
    let ht0 : 0≤leftParameter q c+ε := (lt_trans (leftParameter_spec q c).1 hcp).le
    let hA := (regular_first_window_iff q hR c hc _ ht0 hpb).mpr (ne_of_gt hcp)
    let Q := Split.child q hR c hc.1 hcut
    let ell := (Finset.univ.filter (fun i : Fin (a+1) =>
      0<planarDet (cyclicTangent Q ((cyclicSuccessorPerm (a+1))⁻¹ i)) (cyclicTangent Q i))).card
    (-1:ℚ)^(List.ofFn (moveStart q (leftParameter q c-ε))).length *
      GammaM (moveStart q (leftParameter q c-ε)) hB
        (BeforeFirst.closedAuxiliary q hR c hc _ hm0 hmc hAux) =
    (-1:ℚ)^(List.ofFn (moveStart q (leftParameter q c+ε))).length *
      GammaM (moveStart q (leftParameter q c+ε)) hA
        (Surviving.after_first_closedAuxiliary q hR c hc _ hcp hpb hAux) -
      ((-1:ℚ)^ell * GeometricSmoothingWeights.separatingSmoothingSum Q
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
        (child_auxiliaryGenericity q hR c hc hcut hAux)) *
      ((-1:ℚ)^(List.ofFn (Split.parent q c hcut)).length *
        GammaM (Split.parent q c hcut) (Split.regular_parent q hR c hcut)
          (parent_closedAuxiliary q hR c hc hcut hAux)) := by
  apply Primitive.exists_normalized_first_under_transport q hR c hc hRI hAux hcut hG1
    (canonical_parent_far_of_supplied q hR hG1 c hcut L hU hT hinc hterminal)
    (event_domain_of_supplied q hR c hc L hU hT hinc hterminal) hu
  intro i _
  have hp : i.succ.castSucc=i.castSucc.succ := Fin.ext rfl
  rw [hp]
  exact hleft i

/-- The canonical hL obligation in actual parent geometry is discharged by the
same supplied family that is propagated to the next actual parent. -/
theorem parent_full_state_of_supplied {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (hG : cyclicNoncollinear q) (hAux : ClosedAuxiliary q hR)
    (hleft : TraversalClosure.RemainingLeft q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (L : Fin (a+b+1) ⊕ Unit → AuxiliaryCarrierChart.CarrierLine)
    (hU : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (a+b+1), AuxiliaryCarrierChart.lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      AuxiliaryCarrierChart.lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : AuxiliaryCarrierChart.lineValue (L (Sum.inr ())) (q ⟨a+b+1,by omega⟩)=0) :
    cyclicNoncollinear (Split.parent q c hcut) ∧
      ClosedAuxiliary (Split.parent q c hcut) (Split.regular_parent q hR c hcut) ∧
      TraversalClosure.RemainingLeft (Split.parent q c hcut) :=
  TraversalClosure.parent_full_state_of_parentFar q hR hG hAux hleft c hc hcut
    (canonical_parent_far_of_supplied q hR hG c hcut L hU hT hinc hterminal)
end DirectGLSSW.UniversalCarrierDomain


