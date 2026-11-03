import HistoricalChildNonalternation
import ActiveArcExposedSupports
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
open DaughterFirstReturn
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))




variable (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hAux : ActiveArc.Primitive.ClosedAuxiliary (ActiveArc.ExposedChart.cutArc q 0)
      (ActiveArc.ExposedChart.cutArc_regular q 0 hq))


include he hAux in
/-- Every nonalternating refinement of the actual historical singleton has
closed, generic daughter words on the fixed original opening's AUX domain. -/
theorem historical_refined_daughter_cyclicGeneric
    (U : Finset (PolygonCrossing q))
    (hU : PolygonNonalternation.polygonNonalternating q hq.g2 U)
    (hsub : sharpSupport q hq h c ⊆ U)
    (x : PolygonEvent q)
    (hx : componentOf (smoothingDartPermutation q hq.g2 (sharpSupport q hq h c)) x =
      sharpIntervalComponent q hq h c hc R) :
    CyclicGeneric (daughterVertex q hq.g2 U x) := by
  let A := ActiveArc.ExposedChart.cutArc q 0
  let hA := ActiveArc.ExposedChart.cutArc_regular q 0 hq
  let T := (ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he).finsetCongr.symm U
  have hmap : ActiveArc.ExposedChart.mappedSupport q 0 hq he T=U :=
    (ActiveArc.ExposedChart.exposedCrossingEquiv q 0 hq he).finsetCongr.apply_symm_apply U
  let E := ActiveArc.ExposedChart.dartEventEquiv q 0 hq he T
  let y := E.symm x
  let p := ActiveArc.incoming A hA.noTriple T
  let C := componentOf p y
  have hT : ActiveArc.Nonalternation.Nonalternating A hA T := by
    apply (ActiveArc.ExposedChart.nonalternating_iff_parent q 0 hq he T).mpr
    rw [hmap]
    exact hU
  have hclosed : C ≠ ActiveArc.openComponent A hA.noTriple T := by
    intro hbad
    have hcycle : p.SameCycle y (ActiveArc.start A) :=
      (componentOf_eq_iff p _ _).mp hbad
    have hactual := (sameCycle_iff_of_intertwining E p
      (smoothingDartPermutation q hq.g2 (ActiveArc.ExposedChart.mappedSupport q 0 hq he T))
      (ActiveArc.ExposedChart.dartEventEquiv_intertwine q 0 hq he T) y (ActiveArc.start A)).mp hcycle
    have hxE : E y=x := E.apply_symm_apply x
    have hsE : E (ActiveArc.start A)=Sum.inl (cyclicSuccessor (0 : Fin (n+2))) := rfl
    rw [hxE,hsE,hmap] at hactual
    have hold := PolygonNonalternation.dart_refines_of_subset q hq.g2
      (sharpSupport q hq h c) U hsub hU hactual
    let B : Finset (ActiveArc.Crossing A) := {openingCrossing q hq he h c}
    let E0 := ActiveArc.ExposedChart.dartEventEquiv q 0 hq he B
    have hroot : E0 (openingRoot q hq he h c hc R) =
        sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩ := by
      apply (eventFin q).injective
      rw [show E0 (openingRoot q hq he h c hc R) =
        ActiveArc.ExposedChart.dartEventEquiv q 0 hq he B
          (openingArc q hq he h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) from rfl]
      change _ = eventFin q ((eventFin q).symm (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩))
      rw [Equiv.apply_symm_apply]
      exact openingArc_map q hq he h c hc R _
    have hrootCycle : (smoothingDartPermutation q hq.g2 (sharpSupport q hq h c)).SameCycle
        (E0 (openingRoot q hq he h c hc R)) (E0 (ActiveArc.start A)) := by
      change (smoothingDartPermutation q hq.g2 (sharpSupport q hq h c)).SameCycle
        (E0 (openingRoot q hq he h c hc R)) (Sum.inl (cyclicSuccessor (0 : Fin (n+2))))
      rw [hroot]
      exact (componentOf_eq_iff _ _ _).mp (hx.symm.trans ((componentOf_eq_iff _ _ _).mpr hold))
    have hm0 : ActiveArc.ExposedChart.mappedSupport q 0 hq he B=sharpSupport q hq h c :=
      opening_mappedSupport q hq he h c
    rw [←hm0] at hrootCycle
    have hback := (sameCycle_iff_of_intertwining E0
      (ActiveArc.incoming A hA.noTriple B)
      (smoothingDartPermutation q hq.g2 (ActiveArc.ExposedChart.mappedSupport q 0 hq he B))
      (ActiveArc.ExposedChart.dartEventEquiv_intertwine q 0 hq he B)
      (openingRoot q hq he h c hc R) (ActiveArc.start A)).mpr hrootCycle
    exact opening_component_ne_open q hq he h c hc R ((componentOf_eq_iff _ _ _).mpr hback)
  have hg := hAux ⟨T,hT⟩ C hclosed
  have hs := (ActiveArc.closedRoot_spec A hA.noTriple T C hclosed).1
  have hcycle := (componentOf_eq_iff _ _ _).mp hs
  have hr := ActiveArc.SingletonWords.retainedWord_isRotated_of_sameCycle (a := n) (b := 0)
    A hA T _ _ hcycle
  have hgy := DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated hr hg
  have hv := ActiveArc.ExposedChart.daughterPointList_eq_retainedWord q 0 hq he T y
  have hEy : E y=x := E.apply_symm_apply x
  rw [hmap,hEy] at hv
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated
    ⟨0,by simpa only [List.rotate_zero] using hv.symm⟩ hgy
end DirectGLSSW.HOMFLY.ProcessedExposedChild
