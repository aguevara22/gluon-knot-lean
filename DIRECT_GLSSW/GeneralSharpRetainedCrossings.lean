import DaughterLiftOrder
import SharpDaughterCharacterization
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.GeneralSharpRetained
open DirectGLSSW PermutationOrbits PolygonDrawingBridge DaughterFirstReturn
  DaughterParentCrossing DaughterVisitLift DaughterEventLift
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
  (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)

def localSharpCrossingEquiv :
    ActualLocalSupports.LocalCrossing q (smoothingDartPermutation q hq.g2 S) S
      (componentOf (smoothingDartPermutation q hq.g2 S) root) ≃
    SharpDaughter.Crossing q hq S (componentOf (smoothingDartPermutation q hq.g2 S) root) :=
  (crossingFin q).subtypeEquiv (by
    intro c
    change (c ∉ S ∧ _ ∧ _) ↔ _
    simp only [SharpDaughter.Crossing, Equiv.symm_apply_apply]
    constructor
    · rintro ⟨hn,h0,h1⟩
      refine ⟨hn,?_⟩
      intro i
      rw [SharpDaughter.outgoing_event, Equiv.symm_apply_apply]
      fin_cases i
      · simpa only [PolygonDrawing.visit, ite_true] using h0
      · simpa only [PolygonDrawing.visit, show (1 : Fin 2) ≠ 0 by decide, ite_false] using h1
    · rintro ⟨hn,h⟩
      refine ⟨hn,?_,?_⟩
      · have hh := h 0
        rw [SharpDaughter.outgoing_event, Equiv.symm_apply_apply] at hh
        simpa [PolygonDrawing.visit] using hh
      · have hh := h 1
        rw [SharpDaughter.outgoing_event, Equiv.symm_apply_apply] at hh
        simpa [PolygonDrawing.visit] using hh)

variable (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
  (hroot : retainedCorner q S root)

def crossingIndexEquiv : PolygonCrossing (daughterVertex q hq.g2 S root) ≃
    Fin (SharpDaughter.sharpDaughterDiagram q hq S
      (componentOf (smoothingDartPermutation q hq.g2 S) root) hNA).nCrossing :=
  (DaughterLocalCrossingEquiv.localCrossingEquiv q hq S hNA root hroot).trans
    ((localSharpCrossingEquiv q hq S root).trans
      (SharpDaughter.crossingEquiv q hq S
        (componentOf (smoothingDartPermutation q hq.g2 S) root)).symm)

theorem crossingIndexEquiv_old (d : PolygonCrossing (daughterVertex q hq.g2 S root)) :
    SharpDaughter.oldCrossing q hq S (componentOf (smoothingDartPermutation q hq.g2 S) root)
      (crossingIndexEquiv q hq S root hNA hroot d) =
    crossingFin q (parentCrossing q hq S hNA root hroot d) := by
  exact congrArg Subtype.val ((SharpDaughter.crossingEquiv q hq S
    (componentOf (smoothingDartPermutation q hq.g2 S) root)).apply_symm_apply _)

include hroot in
theorem crossing_count (hP : CyclicGeneric (daughterVertex q hq.g2 S root)) :
    (SharpDaughter.sharpDaughterDiagram q hq S
      (componentOf (smoothingDartPermutation q hq.g2 S) root) hNA).nCrossing =
    (positivePolygonEventDiagram (daughterVertex q hq.g2 S root) hP).nCrossing := by
  have hh := Fintype.card_congr ((crossingIndexEquiv q hq S root hNA hroot).symm.trans
    (crossingFin (daughterVertex q hq.g2 S root)))
  simpa only [Fintype.card_fin] using hh

def branchPermutation (d : PolygonCrossing (daughterVertex q hq.g2 S root)) : Equiv.Perm (Fin 2) :=
  if daughterCarrier q hq.g2 S root d.val.1 < daughterCarrier q hq.g2 S root d.val.2
  then Equiv.refl _ else Equiv.swap 0 1

theorem eventLift_matched_visit (d : PolygonCrossing (daughterVertex q hq.g2 S root)) (i : Fin 2) :
    eventLift q hq S hNA root hroot
      (PolygonDrawing.visit _ d (branchPermutation q hq S root d i)) =
    PolygonDrawing.visit q (parentCrossing q hq S hNA root hroot d) i := by
  by_cases hh : daughterCarrier q hq.g2 S root d.val.1 < daughterCarrier q hq.g2 S root d.val.2
  · fin_cases i <;> simp [branchPermutation,hh,PolygonDrawing.visit,eventLift,visitLift,parentSide]
  · fin_cases i <;> simp [branchPermutation,hh,PolygonDrawing.visit,eventLift,visitLift,parentSide]

theorem branchPermutation_carrier (d : PolygonCrossing (daughterVertex q hq.g2 S root)) (i : Fin 2) :
    daughterCarrier q hq.g2 S root
      (polygonEventEdge _ (PolygonDrawing.visit _ d (branchPermutation q hq S root d i))) =
    polygonEventEdge q (PolygonDrawing.visit q (parentCrossing q hq S hNA root hroot d) i) := by
  rw [←eventLift_matched_visit q hq S root hNA hroot d i]
  exact (eventLift_carrier q hq S hNA root hroot _).symm







end DirectGLSSW.HOMFLY.GeneralSharpRetained
