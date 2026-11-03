import PolygonSingletonCutTransport
import UniformLeftHistoryChildTurns
import ActiveArcSingletonWords
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

/-- The actual original crossing, expressed in the fixed exposed opening. -/
def openingCrossing : ActiveArc.Crossing (cutArc q 0) :=
  (exposedCrossingEquiv q 0 hq he).symm ((crossingFin q).symm (h.crossingOrigin c))

theorem openingCrossing_map :
    crossingFin q (exposedCrossingEquiv q 0 hq he (openingCrossing q hq he h c)) =
      h.crossingOrigin c := by
  simp only [openingCrossing,Equiv.apply_symm_apply]

/-- Actual opening-event labels of every produced original detached arc. -/
def openingArc (i : Fin (detachedOrbitSize t c R-1)) : ActiveArc.Event (cutArc q 0) :=
  (singletonDiagramEquiv q 0 hq he (openingCrossing q hq he h c)).symm
    (h.detachedOriginalArc c hc R i)

theorem openingArc_map (i : Fin (detachedOrbitSize t c R-1)) :
    singletonDiagramEquiv q 0 hq he (openingCrossing q hq he h c)
      (openingArc q hq he h c hc R i) = h.detachedOriginalArc c hc R i :=
  (singletonDiagramEquiv q 0 hq he (openingCrossing q hq he h c)).apply_symm_apply _

def openingRoot : ActiveArc.Event (cutArc q 0) :=
  openingArc q hq he h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩

theorem openingArc_incoming (i : Fin (detachedOrbitSize t c R-1)) :
    ActiveArc.incoming (cutArc q 0) (cutArc_regular q 0 hq).noTriple
      {openingCrossing q hq he h c} (openingArc q hq he h c hc R i) =
    openingArc q hq he h c hc R (cyclicSuccessor i) := by
  apply (singletonDiagramEquiv q 0 hq he (openingCrossing q hq he h c)).injective
  rw [singletonDiagramEquiv_step,openingCrossing_map,openingArc_map,openingArc_map]
  exact h.detachedOriginalArc_cut_successor c hc R i

/-- Literal closed-orbit event word in the original exposed opening. -/
theorem opening_orbitWord :
    orbitWord (ActiveArc.incoming (cutArc q 0) (cutArc_regular q 0 hq).noTriple
      {openingCrossing q hq he h c}) (openingRoot q hq he h c hc R) =
      List.ofFn (openingArc q hq he h c hc R) := by
  apply orbitWord_eq_of_injective_cyclicSuccessor _ (detachedOldOrbitSize_pos c R)
  · exact (singletonDiagramEquiv q 0 hq he (openingCrossing q hq he h c)).symm.injective.comp
      (h.detachedOriginalArc_injective c hc R)
  · exact openingArc_incoming q hq he h c hc R

/-- The transported historical child is an actual closed component of the
fixed original opening, not the open component or a rotated-domain assertion. -/
theorem opening_component_ne_open :
    componentOf (ActiveArc.incoming (cutArc q 0) (cutArc_regular q 0 hq).noTriple
      {openingCrossing q hq he h c}) (openingRoot q hq he h c hc R) ≠
      ActiveArc.openComponent (cutArc q 0) (cutArc_regular q 0 hq).noTriple
        {openingCrossing q hq he h c} := by
  intro heq
  have hterminal := ActiveArc.component_endpoints_eq (cutArc q 0)
    (cutArc_regular q 0 hq).noTriple {openingCrossing q hq he h c}
  have hm := (mem_orbitWord_iff _ _ _).mpr ((componentOf_eq_iff _ _ _).mp
    (heq.trans hterminal.symm))
  rw [opening_orbitWord q hq he h c hc R] at hm
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
  have hi' := congrArg (singletonDiagramEquiv q 0 hq he (openingCrossing q hq he h c)) hi
  rw [openingArc_map,singletonDiagramEquiv_terminal] at hi'
  exact h.detachedOriginalArc_ne_baseArc c hc R i hi'
end DirectGLSSW.HOMFLY.ProcessedExposedChild
