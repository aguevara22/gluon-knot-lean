import ProcessedRetainedEventOrder
import BranchMarkedIncomingComparison
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge
  SmoothingCornerGeometry MarkedCycleGaps DaughterFirstReturn
attribute [local instance] Classical.propDecidable

private theorem next_mark_congr {α ι : Type*} [Fintype α] [Fintype ι]
    (p : Equiv.Perm α) (f g : ι → α) (hf : Function.Injective f)
    (hg : Function.Injective g) (hfg : f = g) : next p f hf = next p g hg := by
  subst g
  rfl

private theorem next_shift {α ι : Type*} [Fintype α] [Fintype ι]
    (p : Equiv.Perm α) (f : ι → α) (hf : Function.Injective f) :
    next p f hf = next p (p ∘ f) (p.injective.comp hf) :=
  next_conjugacy p p p (fun _ => rfl) f hf

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

def sharpArcCoordinate : Fin (historicalSharpDiagram q hq h c hc R).nArc ≃
    Fin (orbitCard q hq.g2 (sharpSupport q hq h c)
      (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)) :=
  (SharpDaughter.arcEquiv q hq (sharpSupport q hq h c)
    (sharpIntervalComponent q hq h c hc R)).trans
      (orbitEnumeration (SharpDaughter.P q hq (sharpSupport q hq h c))
        (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)).symm

theorem sharpArcCoordinate_step (a : Fin (historicalSharpDiagram q hq h c hc R).nArc) :
    sharpArcCoordinate q hq h c hc R ((historicalSharpDiagram q hq h c hc R).continuation a) =
      cyclicSuccessorPerm _ (sharpArcCoordinate q hq h c hc R a) := by
  let A := SharpDaughter.arcEquiv q hq (sharpSupport q hq h c)
    (sharpIntervalComponent q hq h c hc R)
  let O := orbitEnumeration (SharpDaughter.P q hq (sharpSupport q hq h c))
    (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)
  have hA : A ((historicalSharpDiagram q hq h c hc R).continuation a) =
      fibrePerm _ _ (A a) := SharpDaughter.arcEquiv_next q hq (sharpSupport q hq h c)
        (sharpIntervalComponent q hq h c hc R) a
  have hO := orbitEnumeration_successor (SharpDaughter.P q hq (sharpSupport q hq h c))
    (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) (O.symm (A a))
  have hO' : O (cyclicSuccessorPerm _ (O.symm (A a))) = fibrePerm _ _ (A a) :=
    hO.trans (congrArg (fibrePerm _ _) (O.apply_symm_apply (A a)))
  change O.symm (A ((historicalSharpDiagram q hq h c hc R).continuation a)) =
    cyclicSuccessorPerm _ (O.symm (A a))
  exact (congrArg O.symm hA).trans
    ((congrArg O.symm hO'.symm).trans (O.symm_apply_apply _))

def retainedArcCoordinate : Fin (historicalRetainedDiagram q hq h c hc R he hAux).nArc ≃
    Fin (Fintype.card (PolygonEvent (historicalSharpPolygon q hq h c hc R))) :=
  (eventFin (historicalSharpPolygon q hq h c hc R)).symm.trans
    (polygonEventEnumeration _ (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2).toEquiv.symm

theorem retainedArcCoordinate_step (a : Fin (historicalRetainedDiagram q hq h c hc R he hAux).nArc) :
    retainedArcCoordinate q hq h c hc R he hAux
      ((historicalRetainedDiagram q hq h c hc R he hAux).continuation a) =
      cyclicSuccessorPerm _ (retainedArcCoordinate q hq h c hc R he hAux a) := by
  let Q := historicalSharpPolygon q hq h c hc R
  let hQ := originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux
  letI := polygonEventOrder Q hQ.g2
  let F := polygonEventEnumeration Q hQ.g2
  have hh := polygonEventDiagram_continuation Q hQ ((eventFin Q).symm a)
  have hh' : (positivePolygonEventDiagram Q hQ).continuation a =
      eventFin Q (polygonEventSuccessor Q hQ.g2 ((eventFin Q).symm a)) := by
    simpa only [Equiv.apply_symm_apply] using hh
  change F.symm ((eventFin Q).symm ((positivePolygonEventDiagram Q hQ).continuation a)) =
    cyclicSuccessorPerm _ (F.symm ((eventFin Q).symm a))
  rw [hh',Equiv.symm_apply_apply]
  exact (congrArg F.symm (polygonEventSuccessor_apply Q hQ.g2 ((eventFin Q).symm a))).trans
    (F.symm_apply_apply _)

theorem sharpArcCoordinate_outgoing
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) (i : Fin 2) :
    sharpArcCoordinate q hq h c hc R
      ((historicalSharpDiagram q hq h c hc R).outgoing
        (historicalSharpPolygonIndexEquiv q hq h c hc R he hAux d) i) =
    retainedEventCoordinate q hq h c hc R
      (PolygonDrawing.visit _ d (historicalSharpBranchPermutation q hq h c hc R d i)) := by
  have hF : (SharpDaughter.arcEquiv q hq (sharpSupport q hq h c)
      (sharpIntervalComponent q hq h c hc R))
        ((historicalSharpDiagram q hq h c hc R).outgoing
          (historicalSharpPolygonIndexEquiv q hq h c hc R he hAux d) i) =
      (⟨retainedEventMap q hq h c hc R
        (PolygonDrawing.visit _ d (historicalSharpBranchPermutation q hq h c hc R d i)),
        retainedEventMap_mem q hq h c hc R _⟩ : SharpDaughter.Arc q hq
          (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R)) := by
    apply Subtype.ext
    change _ = retainedEventMap q hq h c hc R
      (PolygonDrawing.visit _ d (historicalSharpBranchPermutation q hq h c hc R d i))
    rw [retainedEventMap_matched_visit]
    apply (eventFin q).injective
    change SharpDaughter.oldArc q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R)
      (SharpDaughter.outgoingIndex q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R) _ _) = _
    rw [SharpDaughter.old_outgoing,historicalSharpPolygonIndexEquiv_old]
    change eventFin q (PolygonDrawing.visit q ((crossingFin q).symm
      (crossingFin q (historicalSharpPolygonCrossingMap q hq h c hc R d))) i) = _
    rw [Equiv.symm_apply_apply]
  exact congrArg (orbitEnumeration (SharpDaughter.P q hq (sharpSupport q hq h c))
    (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)).symm hF

theorem retainedArcCoordinate_outgoing
    (d : PolygonCrossing (historicalSharpPolygon q hq h c hc R)) (i : Fin 2) :
    retainedArcCoordinate q hq h c hc R he hAux
      ((historicalRetainedDiagram q hq h c hc R he hAux).outgoing (crossingFin _ d) i) =
    (polygonEventEnumeration _
      (originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux).g2).toEquiv.symm
        (PolygonDrawing.visit _ d i) := by
  change (polygonEventEnumeration _ _).toEquiv.symm
    ((eventFin _).symm (eventFin _ (PolygonDrawing.visit _ ((crossingFin _).symm (crossingFin _ d)) i))) = _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rfl

/-- Actual incoming next-mark permutations agree. Physical retained-event
order and both literal outgoing ports discharge all matching conditions. -/
theorem historicalSharpRetainedIncoming_next_eq :
    next (historicalSharpDiagram q hq h c hc R).continuation
      (fun m : PolygonCrossing (historicalSharpPolygon q hq h c hc R) × Fin 2 =>
        (historicalSharpDiagram q hq h c hc R).incoming
          (historicalSharpPolygonIndexEquiv q hq h c hc R he hAux m.1) m.2)
      (labelledIncoming_injective (historicalSharpDiagram q hq h c hc R) (historicalSharpPolygonIndexEquiv q hq h c hc R he hAux)) =
    next (historicalRetainedDiagram q hq h c hc R he hAux).continuation
      (fun m : PolygonCrossing (historicalSharpPolygon q hq h c hc R) × Fin 2 =>
        (historicalRetainedDiagram q hq h c hc R he hAux).incoming (crossingFin _ m.1)
          (historicalSharpBranchPermutation q hq h c hc R m.1 m.2))
      (branchLabelledIncoming_injective (historicalRetainedDiagram q hq h c hc R he hAux) (crossingFin (historicalSharpPolygon q hq h c hc R)) (historicalSharpBranchPermutation q hq h c hc R)) := by
  let D := historicalSharpDiagram q hq h c hc R
  let E := historicalRetainedDiagram q hq h c hc R he hAux
  let Q := historicalSharpPolygon q hq h c hc R
  let hQ := originalSingleton_daughter_cyclicGeneric q hq he h c hc R hAux
  let u := historicalSharpPolygonIndexEquiv q hq h c hc R he hAux
  let β := historicalSharpBranchPermutation q hq h c hc R
  let a := fun m : PolygonCrossing Q × Fin 2 => D.incoming (u m.1) m.2
  let b := fun m : PolygonCrossing Q × Fin 2 => E.incoming (crossingFin Q m.1) (β m.1 m.2)
  have ha : Function.Injective a := labelledIncoming_injective D u
  have hb : Function.Injective b := branchLabelledIncoming_injective E (crossingFin Q) β
  have hda (m : PolygonCrossing Q × Fin 2) :
      D.continuation (a m) = D.outgoing (u m.1) m.2 := D.continuation_crossing _ _
  have heb (m : PolygonCrossing Q × Fin 2) :
      E.continuation (b m) = E.outgoing (crossingFin Q m.1) (β m.1 m.2) := E.continuation_crossing _ _
  change next D.continuation a ha = next E.continuation b hb
  rw [next_shift D.continuation a ha,next_shift E.continuation b hb]
  apply next_eq_of_coordinate_order D.continuation E.continuation
    (sharpArcCoordinate q hq h c hc R) (retainedArcCoordinate q hq h c hc R he hAux)
    (sharpArcCoordinate_step q hq h c hc R) (retainedArcCoordinate_step q hq h c hc R he hAux)
  intro m l
  letI := polygonEventOrder Q hQ.g2
  simp only [Function.comp_apply,hda,heb]
  rw [sharpArcCoordinate_outgoing,sharpArcCoordinate_outgoing]
  rw [retainedArcCoordinate_outgoing,retainedArcCoordinate_outgoing]
  change _ ↔
    (polygonEventEnumeration Q hQ.g2).symm (PolygonDrawing.visit Q m.1 (β m.1 m.2)) <
      (polygonEventEnumeration Q hQ.g2).symm (PolygonDrawing.visit Q l.1 (β l.1 l.2))
  rw [(polygonEventEnumeration Q hQ.g2).symm.lt_iff_lt]
  exact (retainedEventCoordinate_order q hq h c hc R _ _).trans
    (polygonEvent_lt_iff Q hQ.g2 _ _).symm






end DirectGLSSW.HOMFLY.ProcessedExposedChild
