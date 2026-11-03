import ActiveArcLiteralTinySourceCut

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CarrierDomainSelectedCut
open Cursor Split SingletonWords Primitive CompatibleWords OpenFirstEdgeGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The selected-cut limit expressed in the same additive physical epsilon
coordinate as the before/after event window. No new geometric premise is added. -/
theorem exists_physical_selectedCut_constant
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : Primitive.ClosedAuxiliary q hR) (hRI : GLSSWRootIndependence)
    (hG1 : cyclicNoncollinear q)
    (hL : OpenCarrier.parentFarLocus q hR c hcut (OpenCarrier.parentChartLines q)) :
    ∃ (ρ : ℝ), 0<ρ ∧ ∀ (ε : ℝ), 0<ε → ε<ρ →
    ∃ (hm0 : 0≤leftParameter q c-ε) (hmc : leftParameter q c-ε<leftParameter q c),
    let t := leftParameter q c-ε
    let bounds := And.intro hm0 hmc
    let qm := moveStart q t
    let hm := before_first_regular q hR c hc t bounds.1 bounds.2
    let C := crossingFromOriginal q t (lt_trans bounds.2 (leftParameter_spec q c).2.1)
      c (survives_before_first q c hc t bounds.2 c)
    let hAm := BeforeFirst.closedAuxiliary q hR c hc t bounds.1 bounds.2 hAux
    (∑ U : {U : Primitive.Support qm hm // C ∈ U.val},
      (-1 : ℚ)^U.val.val.card *
        (Primitive.openCurrent qm hm U.val *
          ∏ D ∈ Finset.univ.erase (openComponent qm hm.noTriple U.val.val),
            Primitive.closedWeight qm hm hAm U.val D)) =
      ((1+scalarSignValue (planarDet (q 1-q 0)
        (q c.val.2.succ-q c.val.2.castSucc)))/2) *
        (GeometricSmoothingWeights.separatingSmoothingSum
          (child q hR c hc.1 hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
          (child_auxiliaryGenericity q hR c hc hcut hAux) *
          Primitive.GammaM (parent q c hcut) (regular_parent q hR c hcut)
            (parent_closedAuxiliary q hR c hc hcut hAux)) := by
  obtain ⟨r,hr,hr1,hvalue⟩ := LiteralTinyParent.exists_selectedCut_constant_from_actual_tinyParent
    q hR c hc hcut hAux hRI hG1 hL
  have htc := (leftParameter_spec q c).1
  refine ⟨leftParameter q c*r,mul_pos htc hr,?_⟩
  intro ε he her
  have hη : 0<ε/leftParameter q c := div_pos he htc
  have hηr : ε/leftParameter q c<r := (div_lt_iff₀ htc).mpr (by nlinarith)
  have hparam : leftParameter q c*(1-ε/leftParameter q c)=leftParameter q c-ε := by
    field_simp
  have hbounds := approach_parameter_bounds q c (ε/leftParameter q c) hη
    (lt_of_lt_of_le hηr hr1)
  rw [hparam] at hbounds
  refine ⟨hbounds.1,hbounds.2,?_⟩
  have hv := hvalue (ε/leftParameter q c) hη hηr
  let F : {t : ℝ // 0≤t ∧ t<leftParameter q c} → ℚ := fun x =>
    let qm := moveStart q x.val
    let hm := before_first_regular q hR c hc x.val x.property.1 x.property.2
    let C := crossingFromOriginal q x.val
      (lt_trans x.property.2 (leftParameter_spec q c).2.1) c
      (survives_before_first q c hc x.val x.property.2 c)
    let hAm := BeforeFirst.closedAuxiliary q hR c hc x.val x.property.1 x.property.2 hAux
    ∑ U : {U : Primitive.Support qm hm // C∈U.val},
      (-1 : ℚ)^U.val.val.card *
        (Primitive.openCurrent qm hm U.val *
          ∏ D∈Finset.univ.erase (openComponent qm hm.noTriple U.val.val),
            Primitive.closedWeight qm hm hAm U.val D)
  let oldPoint : {t : ℝ // 0≤t ∧ t<leftParameter q c} :=
    ⟨leftParameter q c*(1-ε/leftParameter q c),
      approach_parameter_bounds q c (ε/leftParameter q c) hη (lt_of_lt_of_le hηr hr1)⟩
  let newPoint : {t : ℝ // 0≤t ∧ t<leftParameter q c} :=
    ⟨leftParameter q c-ε,hbounds⟩
  have hpoints : oldPoint=newPoint := Subtype.ext hparam
  change F oldPoint = _ at hv
  change F newPoint = _
  rw [← hpoints]
  exact hv


end DirectGLSSW.ActiveArc.CarrierDomainSelectedCut
