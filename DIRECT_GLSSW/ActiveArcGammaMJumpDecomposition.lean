import GammaMReindex
import ActiveArcPhysicalCurrentTransport

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords EndpointEventGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Exact physical GammaM subtraction before any event-specific current
formula is used: surviving supports contribute their open-current difference,
and the selected pre-event supports disappear. All closed factors are the
original actual factors, transported by the proved component equivalences. -/
theorem GammaM_physical_jump_decomposition
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (hRI : GLSSWRootIndependence) (hAux : ClosedAuxiliary q hR)
    (ε : ℝ) (hm0 : 0≤leftParameter q c-ε)
    (hmc : leftParameter q c-ε<leftParameter q c)
    (hcp : leftParameter q c<leftParameter q c+ε)
    (hpb : leftParameter q c+ε<afterBound q c) :
    let hB := before_first_regular (a:=n) (b:=0) q hR c hc _ hm0 hmc
    let ht0 : 0≤leftParameter q c+ε :=
      (lt_trans (leftParameter_spec q c).1 hcp).le
    let hA := (regular_first_window_iff q hR c hc _ ht0 hpb).mpr (ne_of_gt hcp)
    let F := fun (U : Support q hR) (s : ℝ) =>
      OpenMarkedCurrent.entry
        (polygonSignArray (moveEndpoint (eventOpenWord q hR U c) (q 1-q 0) s))
        0 (openCount q hR U.val-1)
    let P := fun U : Support q hR =>
      ∏ D∈Finset.univ.erase (openComponent q hR.noTriple U.val),
        closedWeight q hR hAux U D
    GammaM (moveStart q (leftParameter q c+ε)) hA
        (Surviving.after_first_closedAuxiliary q hR c hc _ hcp hpb hAux) -
      GammaM (moveStart q (leftParameter q c-ε)) hB
        (BeforeFirst.closedAuxiliary q hR c hc _ hm0 hmc hAux) =
      (∑ U : {U : Support q hR // c∉U.val},
        (-1 : ℚ)^U.val.val.card * ((F U.val ε-F U.val (-ε))*P U.val)) -
      (∑ U : {U : Support q hR // c∈U.val},
        (-1 : ℚ)^U.val.val.card * (F U.val (-ε)*P U.val)) := by
  dsimp only
  rw [Surviving.GammaM_eq_reindexed_unselected_support q hR c hc _ hcp hpb hRI hAux,
    BeforeFirst.GammaM_eq_reindexed_original_support q hR c hc _ hm0 hmc hRI hAux]
  simp_rw [after_first_openCurrent_eq_event q hR c hc _ hcp hpb,
    before_first_openCurrent_eq_event q hR c hc _ hm0 hmc]
  have hp : leftParameter q c+ε-leftParameter q c=ε := by ring
  have hm : leftParameter q c-ε-leftParameter q c=-ε := by ring
  simp only [hp,hm]
  let A := fun U : Support q hR => (-1 : ℚ)^U.val.card *
    (OpenMarkedCurrent.entry
      (polygonSignArray (moveEndpoint (eventOpenWord q hR U c) (q 1-q 0) ε))
      0 (openCount q hR U.val-1) *
      ∏ D∈Finset.univ.erase (openComponent q hR.noTriple U.val),
        closedWeight q hR hAux U D)
  let B := fun U : Support q hR => (-1 : ℚ)^U.val.card *
    (OpenMarkedCurrent.entry
      (polygonSignArray (moveEndpoint (eventOpenWord q hR U c) (q 1-q 0) (-ε)))
      0 (openCount q hR U.val-1) *
      ∏ D∈Finset.univ.erase (openComponent q hR.noTriple U.val),
        closedWeight q hR hAux U D)
  have hsplit : (∑ U : Support q hR,B U) =
      (∑ U : {U : Support q hR // c∉U.val},B U.val) +
      (∑ U : {U : Support q hR // c∈U.val},B U.val) := by
    simpa only [add_comm] using
      (Fintype.sum_subtype_add_sum_subtype (fun U : Support q hR => c∈U.val) B).symm
  change (∑ U : {U : Support q hR // c∉U.val},A U.val) -
    (∑ U : Support q hR,B U) = _
  rw [hsplit,sub_add_eq_sub_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro U _
  dsimp [A,B]
  ring


end DirectGLSSW.ActiveArc.Primitive
