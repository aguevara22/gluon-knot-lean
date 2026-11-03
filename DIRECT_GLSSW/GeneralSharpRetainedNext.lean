import GeneralSharpRetainedBranch
import BranchMarkedIncomingComparison
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.GeneralSharpRetained
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge
  MarkedCycleGaps DaughterFirstReturn
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

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
  (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
  (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
  (hroot : retainedCorner q S root)
  (hP : CyclicGeneric (daughterVertex q hq.g2 S root))

abbrev sharpDiagram := SharpDaughter.sharpDaughterDiagram q hq S
  (componentOf (smoothingDartPermutation q hq.g2 S) root) hNA
abbrev retainedDiagram := positivePolygonEventDiagram (daughterVertex q hq.g2 S root) hP

def sharpArcCoordinate : Fin (sharpDiagram q hq S root hNA).nArc ≃
    Fin (orbitCard q hq.g2 (S)
      (root)) :=
  (SharpDaughter.arcEquiv q hq (S)
    (componentOf (smoothingDartPermutation q hq.g2 S) root)).trans
      (orbitEnumeration (SharpDaughter.P q hq (S))
        (root)).symm

theorem sharpArcCoordinate_step (a : Fin (sharpDiagram q hq S root hNA).nArc) :
    sharpArcCoordinate q hq S root hNA ((sharpDiagram q hq S root hNA).continuation a) =
      cyclicSuccessorPerm _ (sharpArcCoordinate q hq S root hNA a) := by
  let A := SharpDaughter.arcEquiv q hq (S)
    (componentOf (smoothingDartPermutation q hq.g2 S) root)
  let O := orbitEnumeration (SharpDaughter.P q hq (S))
    (root)
  have hA : A ((sharpDiagram q hq S root hNA).continuation a) =
      fibrePerm _ _ (A a) := SharpDaughter.arcEquiv_next q hq (S)
        (componentOf (smoothingDartPermutation q hq.g2 S) root) a
  have hO := orbitEnumeration_successor (SharpDaughter.P q hq (S))
    (root) (O.symm (A a))
  have hO' : O (cyclicSuccessorPerm _ (O.symm (A a))) = fibrePerm _ _ (A a) :=
    hO.trans (congrArg (fibrePerm _ _) (O.apply_symm_apply (A a)))
  change O.symm (A ((sharpDiagram q hq S root hNA).continuation a)) =
    cyclicSuccessorPerm _ (O.symm (A a))
  exact (congrArg O.symm hA).trans
    ((congrArg O.symm hO'.symm).trans (O.symm_apply_apply _))

def retainedArcCoordinate : Fin (retainedDiagram q hq S root hP).nArc ≃
    Fin (Fintype.card (PolygonEvent (daughterVertex q hq.g2 S root))) :=
  (eventFin (daughterVertex q hq.g2 S root)).symm.trans
    (polygonEventEnumeration _ (hP).g2).toEquiv.symm

theorem retainedArcCoordinate_step (a : Fin (retainedDiagram q hq S root hP).nArc) :
    retainedArcCoordinate q hq S root hP
      ((retainedDiagram q hq S root hP).continuation a) =
      cyclicSuccessorPerm _ (retainedArcCoordinate q hq S root hP a) := by
  let Q := daughterVertex q hq.g2 S root
  let hQ := hP
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
    (d : PolygonCrossing (daughterVertex q hq.g2 S root)) (i : Fin 2) :
    sharpArcCoordinate q hq S root hNA
      ((sharpDiagram q hq S root hNA).outgoing
        (crossingIndexEquiv q hq S root hNA hroot d) i) =
    DaughterLiftOrder.liftRank q hq S hNA root hroot
      (PolygonDrawing.visit _ d (branchPermutation q hq S root d i)) := by
  have hF : (SharpDaughter.arcEquiv q hq (S)
      (componentOf (smoothingDartPermutation q hq.g2 S) root))
        ((sharpDiagram q hq S root hNA).outgoing
          (crossingIndexEquiv q hq S root hNA hroot d) i) =
      (⟨DaughterEventLift.eventLift q hq S hNA root hroot
        (PolygonDrawing.visit _ d (branchPermutation q hq S root d i)),
        DaughterEventLift.eventLift_component q hq S hNA root hroot _⟩ : SharpDaughter.Arc q hq
          (S) (componentOf (smoothingDartPermutation q hq.g2 S) root)) := by
    apply Subtype.ext
    change _ = DaughterEventLift.eventLift q hq S hNA root hroot
      (PolygonDrawing.visit _ d (branchPermutation q hq S root d i))
    rw [eventLift_matched_visit]
    apply (eventFin q).injective
    change SharpDaughter.oldArc q hq (S) (componentOf (smoothingDartPermutation q hq.g2 S) root)
      (SharpDaughter.outgoingIndex q hq (S) (componentOf (smoothingDartPermutation q hq.g2 S) root) _ _) = _
    rw [SharpDaughter.old_outgoing,crossingIndexEquiv_old]
    change eventFin q (PolygonDrawing.visit q ((crossingFin q).symm
      (crossingFin q (DaughterParentCrossing.parentCrossing q hq S hNA root hroot d))) i) = _
    rw [Equiv.symm_apply_apply]
  change (orbitEnumeration (SharpDaughter.P q hq S) root).symm _ = _
  rw [hF]
  apply (orbitEnumeration (SharpDaughter.P q hq S) root).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  simpa only [orbitEventAt] using (DaughterLiftOrder.orbitEventAt_liftRank q hq S hNA root hroot
    (PolygonDrawing.visit _ d (branchPermutation q hq S root d i))).symm

theorem retainedArcCoordinate_outgoing
    (d : PolygonCrossing (daughterVertex q hq.g2 S root)) (i : Fin 2) :
    retainedArcCoordinate q hq S root hP
      ((retainedDiagram q hq S root hP).outgoing (crossingFin _ d) i) =
    (polygonEventEnumeration _
      (hP).g2).toEquiv.symm
        (PolygonDrawing.visit _ d i) := by
  change (polygonEventEnumeration _ _).toEquiv.symm
    ((eventFin _).symm (eventFin _ (PolygonDrawing.visit _ ((crossingFin _).symm (crossingFin _ d)) i))) = _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

/-- Actual incoming next-mark permutations agree. Physical retained-event
order and both literal outgoing ports discharge all matching conditions. -/
theorem incoming_next_eq :
    next (sharpDiagram q hq S root hNA).continuation
      (fun m : PolygonCrossing (daughterVertex q hq.g2 S root) × Fin 2 =>
        (sharpDiagram q hq S root hNA).incoming
          (crossingIndexEquiv q hq S root hNA hroot m.1) m.2)
      (labelledIncoming_injective (sharpDiagram q hq S root hNA) (crossingIndexEquiv q hq S root hNA hroot)) =
    next (retainedDiagram q hq S root hP).continuation
      (fun m : PolygonCrossing (daughterVertex q hq.g2 S root) × Fin 2 =>
        (retainedDiagram q hq S root hP).incoming (crossingFin _ m.1)
          (branchPermutation q hq S root m.1 m.2))
      (branchLabelledIncoming_injective (retainedDiagram q hq S root hP) (crossingFin (daughterVertex q hq.g2 S root)) (branchPermutation q hq S root)) := by
  let D := sharpDiagram q hq S root hNA
  let E := retainedDiagram q hq S root hP
  let Q := daughterVertex q hq.g2 S root
  let hQ := hP
  let u := crossingIndexEquiv q hq S root hNA hroot
  let β := branchPermutation q hq S root
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
    (sharpArcCoordinate q hq S root hNA) (retainedArcCoordinate q hq S root hP)
    (sharpArcCoordinate_step q hq S root hNA) (retainedArcCoordinate_step q hq S root hP)
  intro m l
  letI := polygonEventOrder Q hQ.g2
  simp only [Function.comp_apply,hda,heb]
  rw [sharpArcCoordinate_outgoing,sharpArcCoordinate_outgoing]
  rw [retainedArcCoordinate_outgoing,retainedArcCoordinate_outgoing]
  change _ ↔
    (polygonEventEnumeration Q hQ.g2).symm (PolygonDrawing.visit Q m.1 (β m.1 m.2)) <
      (polygonEventEnumeration Q hQ.g2).symm (PolygonDrawing.visit Q l.1 (β l.1 l.2))
  rw [(polygonEventEnumeration Q hQ.g2).symm.lt_iff_lt]
  exact (DaughterLiftOrder.liftRank_strictMono q hq S hNA root hroot).lt_iff_lt







end DirectGLSSW.HOMFLY.GeneralSharpRetained
