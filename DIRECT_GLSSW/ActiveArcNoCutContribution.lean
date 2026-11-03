import ActiveArcCompatibleContribution
import ActiveArcCarrierDomainCurrents
import CompatiblePairUnselectedZeroPartition

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords Split SingletonWords CompatibleWords EndpointEventGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The entire actual unselected-support contribution, on the explicit
finite carrier determinant domain. Incompatible terms vanish by proved
physical event classification; compatible terms use the actual refinement. -/
theorem exists_unselected_current_contribution
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hRI : GLSSWRootIndependence) (hAux : ClosedAuxiliary q hR)
    (hF : ∀ U : Support q hR, c∉U.val → EventCarrierNonvanishing q hR c U) :
    let F := fun (U : Support q hR) (x : ℝ) => OpenMarkedCurrent.entry
      (polygonSignArray (moveEndpoint (eventOpenWord q hR U c) (q 1-q 0) x))
      0 (openCount q hR U.val-1)
    let P := fun U : Support q hR =>
      ∏ D∈Finset.univ.erase (openComponent q hR.noTriple U.val), closedWeight q hR hAux U D
    ∃ ρ : ℝ, 0<ρ ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
      (∑ U : {U : Support q hR // c∉U.val},
        (-1 : ℚ)^U.val.val.card * ((F U.val ε-F U.val (-ε))*P U.val)) =
      scalarSignValue (planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc)) *
        (GeometricSmoothingWeights.separatingSmoothingSum
          (child q hR c hc.1 hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
          (child_auxiliaryGenericity q hR c hc hcut hAux) *
          GammaM (parent q c hcut) (regular_parent q hR c hcut)
            (parent_closedAuxiliary q hR c hc hcut hAux)) := by
  classical
  intro F P
  obtain ⟨ρc,hρc,hcompatible⟩ := exists_compatible_pair_current_contribution
    q hR c hc hcut hRI hAux (by
      intro S T
      have hh := compatible_eventCarrierNonvanishing_isolated q hR c hc hcut hAux S T
        (hF ⟨pieceSelections q hR c hc hcut S.val T.val,
          (pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr
            ⟨S.property,T.property⟩⟩
          (cut_not_mem_pieceSelections q hR c hc hcut S.val T.val))
      have hm := (child_auxiliaryGenericity q hR c hc hcut hAux S.val S.property (Sum.inl 0)).size_ge_three
      dsimp only at hh
      simpa only [DaughterFirstReturn.daughterPointList,List.length_ofFn,
        Nat.sub_add_cancel (by omega : 1≤Fintype.card (DaughterFirstReturn.CornerCoord
          (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0)))] using hh)
  let E := fun (U : Support q hR) (ε : ℝ) =>
    c∉U.val → ¬Nonalternation.Nonalternating q hR (insert c U.val) → F U ε-F U (-ε)=0
  have hlocal : ∀ U : Support q hR, U∈(Finset.univ : Finset (Support q hR)) →
      ∃ r : ℝ, 0<r ∧ ∀ ε : ℝ, 0<ε → ε<r → E U ε := by
    intro U _
    by_cases hu : c∉U.val
    · by_cases hg : Nonalternation.Nonalternating q hR (insert c U.val)
      · exact ⟨1,by norm_num,fun _ _ _ _ hn => False.elim (hn hg)⟩
      · have hbad := (not_insert_nonalternating_iff_exists_incompatible
          q hR c hc hcut U hu).mp hg
        obtain ⟨r,hr,hzero⟩ := exists_incompatible_carrier_domain_current_eq
          q hR c hc U hu hbad (hF U hu)
        exact ⟨r,hr,fun ε he her _ _ => hzero ε he her⟩
    · exact ⟨1,by norm_num,fun _ _ _ h _ => False.elim (hu h)⟩
  obtain ⟨ρb,hρb,hbad⟩ := ShortEdgeSignStability.exists_finset_common_radius Finset.univ E hlocal
  refine ⟨min ρc ρb,lt_min hρc hρb,?_⟩
  intro ε he her
  have hpair := hcompatible ε he (lt_of_lt_of_le her (min_le_left _ _))
  let g := fun U : Support q hR => (-1 : ℚ)^U.val.card*((F U ε-F U (-ε))*P U)
  have hzero : ∀ U : Support q hR, c∉U.val →
      ¬Nonalternation.Nonalternating q hR (insert c U.val) → g U=0 := by
    intro U hu hn
    have hz := hbad ε he (lt_of_lt_of_le her (min_le_right _ _)) U (Finset.mem_univ _) hu hn
    simp only [g,hz,zero_mul,mul_zero]
  have hsplit := unselected_support_sum_eq_compatible_pair_sum q hR c hc hcut hAux g hzero
  rw [hsplit]
  calc
    _ = ∑ S : GeometricSmoothingWeights.SeparatingSupport (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux),
      ∑ T : Support (parent q c hcut) (regular_parent q hR c hcut),
        let U : Support q hR := ⟨pieceSelections q hR c hc hcut S.val T.val,
          (pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr
            ⟨S.property,T.property⟩⟩
        (-1 : ℚ)^(S.val.card+T.val.card)*((F U ε-F U (-ε))*P U) := by
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro T _
      dsimp only [g]
      rw [original_compatible_support_card]
      rfl
    _ = _ := hpair


end DirectGLSSW.ActiveArc.Primitive
