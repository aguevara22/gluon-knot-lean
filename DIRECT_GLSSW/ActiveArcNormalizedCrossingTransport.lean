import ActiveArcGammaMUnderOverTransport
import ActiveArcUniformChild

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords EndpointEventGeometry CompatibleWords SingletonWords
attribute [local instance] Classical.propDecidable

/-- The actual left-corner count of the child equals its vertex count. -/
theorem first_under_child_left_corner_count
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hG1 : cyclicNoncollinear q)
    (hu : crossingUnder q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1)
    (hleft : ∀ i : Fin (a+b), i.val<a →
      0<planarDet (q i.succ.castSucc-q i.castSucc.castSucc)
        (q i.succ.succ-q i.succ.castSucc)) :
    (Finset.univ.filter (fun i : Fin (a+1) =>
      0<planarDet (cyclicTangent (Split.child q hR c hc.1 hcut) ((cyclicSuccessorPerm (a+1))⁻¹ i))
        (cyclicTangent (Split.child q hR c hc.1 hcut) i))).card=a+1 := by
  have hall := Split.child_all_turns_pos q hR c hc hcut hG1 hu hleft
  have hp : ∀ i : Fin (a+1),
      0<planarDet (cyclicTangent (Split.child q hR c hc.1 hcut) ((cyclicSuccessorPerm (a+1))⁻¹ i))
        (cyclicTangent (Split.child q hR c hc.1 hcut) i) := by
    intro i
    have h := hall ((cyclicSuccessorPerm (a+1))⁻¹ i)
    change 0<planarDet _ (cyclicTangent _ ((cyclicSuccessorPerm (a+1)) ((cyclicSuccessorPerm (a+1))⁻¹ i))) at h
    simpa only [Equiv.Perm.apply_inv_self] using h
  simp [hp]

private theorem normalized_jump_parity (N C P : ℕ) (hcount : C+P=N+1)
    (u v A B : ℚ) (hj : v-u= -(A*B)) :
    (-1:ℚ)^N*u=(-1:ℚ)^N*v-(((-1:ℚ)^C*A)*((-1:ℚ)^P*B)) := by
  have hp : (-1:ℚ)^C*(-1:ℚ)^P= -(-1:ℚ)^N := by
    rw [←pow_add,hcount,pow_succ]
    ring
  calc
    (-1:ℚ)^N*u=(-1:ℚ)^N*(v+A*B) := by congr 1;linarith
    _=(-1:ℚ)^N*v-(((-1:ℚ)^C*(-1:ℚ)^P)*(A*B)) := by rw [hp];ring
    _=_ := by ring

/-- The actual source first-under recurrence after vertex-parity normalization.
The exponent on the child is its literal left-corner count. -/
theorem exists_normalized_first_under_transport
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (hRI : GLSSWRootIndependence) (hAux : ClosedAuxiliary q hR)
    (hcut : c.val.2.val=a) (hG1 : cyclicNoncollinear q)
    (hL : OpenCarrier.parentFarLocus q hR c hcut (OpenCarrier.parentChartLines q))
    (hF : ∀ U : Support q hR, c∉U.val → EventCarrierNonvanishing q hR c U)
    (hu : crossingUnder q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1)
    (hleft : ∀ i : Fin (a+b), i.val<a →
      0<planarDet (q i.succ.castSucc-q i.castSucc.castSucc)
        (q i.succ.succ-q i.succ.castSucc)) :
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
  obtain ⟨ρ,hρ,htransport⟩ := exists_GammaM_under_over_transport q hR c hc hRI hAux hcut hG1 hL hF
  refine ⟨ρ,hρ,?_⟩
  intro ε he her
  obtain ⟨hm0,hmc,hcp,hpb,hunder,hover⟩ := htransport ε he her
  refine ⟨hm0,hmc,hcp,hpb,?_⟩
  have hj := hunder hu
  dsimp only at hj ⊢
  rw [first_under_child_left_corner_count q hR c hc hcut hG1 hu hleft]
  simp only [List.length_ofFn]
  exact normalized_jump_parity (a+b+2) (a+1) (b+2) (by omega) _ _ _ _ hj



end DirectGLSSW.ActiveArc.Primitive
