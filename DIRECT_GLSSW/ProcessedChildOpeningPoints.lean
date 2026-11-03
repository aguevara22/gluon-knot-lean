import ProcessedChildOpeningOrbit
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q 0) {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

theorem opening_mappedSupport :
    mappedSupport q 0 hq he {openingCrossing q hq he h c} =
      {(crossingFin q).symm (h.crossingOrigin c)} := by
  simp only [mappedSupport,Finset.map_singleton,Equiv.toEmbedding_apply,
    openingCrossing,Equiv.apply_symm_apply]

/-- Every physical event point is the corresponding original ancestor arc's
polygon-event point; no bevel-coordinate identification is asserted. -/
theorem openingArc_point (i : Fin (detachedOrbitSize t c R-1)) :
    ActiveArc.eventPoint (cutArc q 0) (openingArc q hq he h c hc R i) =
      polygonEventPoint q ((eventFin q).symm (h.detachedOriginalArc c hc R i)) := by
  have hev : dartEventEquiv q 0 hq he {openingCrossing q hq he h c}
      (openingArc q hq he h c hc R i) =
      (eventFin q).symm (h.detachedOriginalArc c hc R i) := by
    apply (eventFin q).injective
    rw [Equiv.apply_symm_apply]
    exact openingArc_map q hq he h c hc R i
  rw [←hev,dartEventEquiv_point]

/-- Literal original polygon singleton daughter equals the actual retained
closed word in the fixed exposed opening at the transported historical root. -/
theorem originalSingleton_daughterPointList_eq :
    DaughterFirstReturn.daughterPointList q hq.g2 {(crossingFin q).symm (h.crossingOrigin c)}
      ((eventFin q).symm (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)) =
    List.ofFn (ActiveArc.RetainedWords.vertex (cutArc q 0) (cutArc_regular q 0 hq)
      {openingCrossing q hq he h c} (openingRoot q hq he h c hc R)) := by
  have hd := daughterPointList_eq_retainedWord q 0 hq he
    {openingCrossing q hq he h c} (openingRoot q hq he h c hc R)
  rw [opening_mappedSupport q hq he h c] at hd
  have hr : dartEventEquiv q 0 hq he {openingCrossing q hq he h c}
      (openingRoot q hq he h c hc R) =
      (eventFin q).symm (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) := by
    apply (eventFin q).injective
    rw [Equiv.apply_symm_apply]
    exact openingArc_map q hq he h c hc R _
  rw [hr] at hd
  exact hd

/-- The same sharp physical word is the retained filter of the actual
transported original arc interval, with all unselected visits deleted. -/
theorem opening_retainedWord_eq_interval_filter :
    List.ofFn (ActiveArc.RetainedWords.vertex (cutArc q 0) (cutArc_regular q 0 hq)
      {openingCrossing q hq he h c} (openingRoot q hq he h c hc R)) =
    ((List.ofFn (openingArc q hq he h c hc R)).filter
      (fun z => decide (ActiveArc.retained (cutArc q 0) {openingCrossing q hq he h c} z))).map
      (ActiveArc.eventPoint (cutArc q 0)) := by
  rw [active_retainedWord_eq_filtered q 0 hq,opening_orbitWord q hq he h c hc R]

/-- Original-opening auxiliary genericity supplies this actual closed retained
word, after its closed-component status has been proved. -/
theorem opening_retained_cyclicGeneric
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (cutArc q 0) (cutArc_regular q 0 hq)) :
    CyclicGeneric (ActiveArc.RetainedWords.vertex (cutArc q 0) (cutArc_regular q 0 hq)
      {openingCrossing q hq he h c} (openingRoot q hq he h c hc R)) := by
  let p := ActiveArc.incoming (cutArc q 0) (cutArc_regular q 0 hq).noTriple
    {openingCrossing q hq he h c}
  let C := componentOf p (openingRoot q hq he h c hc R)
  have hC := opening_component_ne_open q hq he h c hc R
  have hg := hAux (ActiveArc.SingletonWords.singletonSupport (a := n) (b := 0) (cutArc q 0)
    (cutArc_regular q 0 hq) (openingCrossing q hq he h c)) C hC
  have hs := (ActiveArc.closedRoot_spec (cutArc q 0) (cutArc_regular q 0 hq).noTriple
    {openingCrossing q hq he h c} C hC).1
  have hcycle := (componentOf_eq_iff _ _ _).mp hs
  have hr := ActiveArc.SingletonWords.retainedWord_isRotated_of_sameCycle (a := n) (b := 0) (cutArc q 0)
    (cutArc_regular q 0 hq) {openingCrossing q hq he h c} _ _ hcycle
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated hr hg

include he in
/-- The sharp original singleton daughter is generic on the original fixed
opening's ClosedAuxiliary domain; no rotated auxiliary domain is assumed. -/
theorem originalSingleton_daughter_cyclicGeneric
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (cutArc q 0) (cutArc_regular q 0 hq)) :
    CyclicGeneric (DaughterFirstReturn.daughterVertex q hq.g2
      {(crossingFin q).symm (h.crossingOrigin c)}
      ((eventFin q).symm (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩))) := by
  have hg := opening_retained_cyclicGeneric q hq he h c hc R hAux
  have hr : List.ofFn (ActiveArc.RetainedWords.vertex (cutArc q 0) (cutArc_regular q 0 hq)
      {openingCrossing q hq he h c} (openingRoot q hq he h c hc R)) ~r
      DaughterFirstReturn.daughterPointList q hq.g2 {(crossingFin q).symm (h.crossingOrigin c)}
        ((eventFin q).symm (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)) := by
    rw [originalSingleton_daughterPointList_eq q hq he h c hc R]
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated hr hg
end DirectGLSSW.HOMFLY.ProcessedExposedChild
