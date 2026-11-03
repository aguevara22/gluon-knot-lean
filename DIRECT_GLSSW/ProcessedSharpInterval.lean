import ProcessedChildOpeningPoints
import ProcessedChildCrossingData
import SharpDaughterCharacterization
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

def sharpSupport : Finset (PolygonCrossing q) := {(crossingFin q).symm (h.crossingOrigin c)}
def sharpIntervalEvent (i : Fin (detachedOrbitSize t c R-1)) : PolygonEvent q :=
  (eventFin q).symm (h.detachedOriginalArc c hc R i)
def sharpIntervalComponent : Component (SharpDaughter.P q hq (sharpSupport q hq h c)) :=
  componentOf _ (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)

theorem sharpIntervalEvent_step (i : Fin (detachedOrbitSize t c R-1)) :
    SharpDaughter.P q hq (sharpSupport q hq h c) (sharpIntervalEvent q hq h c hc R i) =
      sharpIntervalEvent q hq h c hc R (cyclicSuccessor i) := by
  apply (eventFin q).injective
  simp only [SharpDaughter.P,sharpSupport]
  rw [eventFin_singleton_dart_step q hq]
  simp only [sharpIntervalEvent,Equiv.apply_symm_apply]
  exact h.detachedOriginalArc_cut_successor c hc R i

theorem sharpInterval_orbitWord :
    orbitWord (SharpDaughter.P q hq (sharpSupport q hq h c))
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) =
      List.ofFn (sharpIntervalEvent q hq h c hc R) :=
  orbitWord_eq_of_injective_cyclicSuccessor _ (detachedOldOrbitSize_pos c R) _
    ((eventFin q).symm.injective.comp (h.detachedOriginalArc_injective c hc R))
    (sharpIntervalEvent_step q hq h c hc R)

/-- Membership in the actual sharp daughter arc fibre is exactly the produced
historical original interval, including both half-open boundary conventions. -/
theorem sharpInterval_mem_iff (x : PolygonEvent q) :
    componentOf (SharpDaughter.P q hq (sharpSupport q hq h c)) x =
      sharpIntervalComponent q hq h c hc R ↔
    ∃ i, h.detachedOriginalArc c hc R i = eventFin q x := by
  constructor
  · intro hx
    have hm := (mem_orbitWord_iff _ _ _).mpr ((componentOf_eq_iff _ _ _).mp hx.symm)
    rw [sharpInterval_orbitWord q hq h c hc R] at hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    exact ⟨i,by simpa only [sharpIntervalEvent,Equiv.apply_symm_apply] using congrArg (eventFin q) hi⟩
  · rintro ⟨i,hi⟩
    have hm : x ∈ orbitWord (SharpDaughter.P q hq (sharpSupport q hq h c))
        (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) := by
      rw [sharpInterval_orbitWord q hq h c hc R]
      exact List.mem_ofFn.mpr ⟨i,by simp only [sharpIntervalEvent,hi,Equiv.symm_apply_apply]⟩
    exact ((componentOf_eq_iff _ _ _).mpr ((mem_orbitWord_iff _ _ _).mp hm)).symm

/-- Actual sharp crossing labels coincide with both-port labels of the original
historical interval. Selected-crossing exclusion is derived from the first port. -/
theorem sharpCrossing_property_iff (d : Fin (positivePolygonEventDiagram q hq).nCrossing) :
    (((crossingFin q).symm d) ∉ sharpSupport q hq h c ∧
      ∀ i : Fin 2, componentOf (SharpDaughter.P q hq (sharpSupport q hq h c))
        ((eventFin q).symm ((positivePolygonEventDiagram q hq).outgoing d i)) =
          sharpIntervalComponent q hq h c hc R) ↔
    ∀ i : Fin 2, ∃ j, h.detachedOriginalArc c hc R j =
      (positivePolygonEventDiagram q hq).incoming d i := by
  constructor
  · rintro ⟨hd,hm⟩ i
    have hi := hm ((positivePolygonEventDiagram q hq).through d i)
    rw [←SharpDaughter.p_incoming q hq (sharpSupport q hq h c) d hd i,
      componentOf_apply] at hi
    simpa only [Equiv.apply_symm_apply] using
      (sharpInterval_mem_iff q hq h c hc R _).mp hi
  · intro hm
    have hd : d ≠ h.crossingOrigin c := by
      intro heq
      obtain ⟨j,hj⟩ := hm (firstVisitedBranch t.2.1 c)
      rw [heq] at hj
      exact h.detachedOriginalArc_ne_firstIncoming c hc R j hj
    have hnot : (crossingFin q).symm d ∉ sharpSupport q hq h c := by
      simp only [sharpSupport,Finset.mem_singleton]
      exact fun heq => hd ((crossingFin q).symm.injective heq)
    refine ⟨hnot,?_⟩
    intro i
    obtain ⟨j,hj⟩ := hm i
    have hi := (sharpInterval_mem_iff q hq h c hc R
      ((eventFin q).symm ((positivePolygonEventDiagram q hq).incoming d i))).mpr
      ⟨j,by simpa only [Equiv.apply_symm_apply] using hj⟩
    rw [←componentOf_apply (SharpDaughter.P q hq (sharpSupport q hq h c))
      ((eventFin q).symm ((positivePolygonEventDiagram q hq).incoming d i)),
      SharpDaughter.p_incoming q hq (sharpSupport q hq h c) d hnot i] at hi
    exact hi

def sharpCrossingIntervalEquiv :
    SharpDaughter.Crossing q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R) ≃
      DetachedIntervalCrossing h c hc R :=
  Equiv.subtypeEquiv (Equiv.refl _) (sharpCrossing_property_iff q hq h c hc R)

@[simp] theorem sharpCrossingIntervalEquiv_val
    (d : SharpDaughter.Crossing q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R)) :
    (sharpCrossingIntervalEquiv q hq h c hc R d).val = d.val := rfl
end DirectGLSSW.HOMFLY.ProcessedExposedChild
