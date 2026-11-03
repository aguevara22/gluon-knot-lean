import PolygonRebaseSuccessor
import PolygonRebaseBranchData
import BranchIsoEvaluator
import FirstChildEvaluatorZero

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PolygonRebase
open HOMFLY HOMFLY.PolygonDrawingBridge HOMFLY.PolygonDrawing HOMFLY.Coefficients
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))

def arcEquiv : Fin (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)).nArc ≃
    Fin (positivePolygonEventDiagram q hq).nArc :=
  (eventFin (q ∘ ρ)).symm.trans ((eventEquiv q ρ hρ).trans (eventFin q))

def diagramCrossingEquiv :
    Fin (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)).nCrossing ≃
    Fin (positivePolygonEventDiagram q hq).nCrossing :=
  (crossingFin (q ∘ ρ)).symm.trans ((crossingEquiv q ρ hρ).trans (crossingFin q))

theorem arcEquiv_event (x : PolygonEvent (q ∘ ρ)) :
    arcEquiv q hq ρ hρ (eventFin (q ∘ ρ) x) = eventFin q (eventEquiv q ρ hρ x) := by
  change eventFin q (eventEquiv q ρ hρ ((eventFin (q ∘ ρ)).symm (eventFin (q ∘ ρ) x))) = _
  rw [(eventFin (q ∘ ρ)).symm_apply_apply]

theorem diagramCrossingEquiv_crossing (c : PolygonCrossing (q ∘ ρ)) :
    diagramCrossingEquiv q hq ρ hρ (crossingFin (q ∘ ρ) c) =
      crossingFin q (crossingEquiv q ρ hρ c) := by
  change crossingFin q (crossingEquiv q ρ hρ ((crossingFin (q ∘ ρ)).symm (crossingFin (q ∘ ρ) c))) = _
  rw [(crossingFin (q ∘ ρ)).symm_apply_apply]

theorem arcEquiv_continuation (e) :
    arcEquiv q hq ρ hρ
      ((positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)).continuation e) =
      (positivePolygonEventDiagram q hq).continuation (arcEquiv q hq ρ hρ e) := by
  obtain ⟨x,rfl⟩ := (eventFin (q ∘ ρ)).surjective e
  change arcEquiv q hq ρ hρ
      ((polygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)).continuation _) =
      (polygonEventDiagram q hq).continuation _
  rw [polygonEventDiagram_continuation,arcEquiv_event,arcEquiv_event,
    polygonEventDiagram_continuation q hq,eventEquiv_successor q hq ρ hρ]

theorem arcEquiv_outgoing (c) (i : Fin 2) :
    arcEquiv q hq ρ hρ
      ((positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)).outgoing
        (crossingFin (q ∘ ρ) c) i) =
      (positivePolygonEventDiagram q hq).outgoing
        (crossingFin q (crossingEquiv q ρ hρ c)) (branchFin q ρ c i) := by
  simp only [positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram,outgoingIndex,Equiv.symm_apply_apply]
  change arcEquiv q hq ρ hρ (eventFin (q ∘ ρ) (visit (q ∘ ρ) c i)) =
    eventFin q (visit q (crossingEquiv q ρ hρ c) (branchFin q ρ c i))
  rw [arcEquiv_event,eventEquiv_visit]

theorem arcEquiv_incoming (c) (i : Fin 2) :
    arcEquiv q hq ρ hρ
      ((positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)).incoming
        (crossingFin (q ∘ ρ) c) i) =
      (positivePolygonEventDiagram q hq).incoming
        (crossingFin q (crossingEquiv q ρ hρ c)) (branchFin q ρ c i) := by
  apply (positivePolygonEventDiagram q hq).continuation.injective
  rw [← arcEquiv_continuation]
  rw [(positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)).continuation_crossing,
    (positivePolygonEventDiagram q hq).continuation_crossing]
  exact arcEquiv_outgoing q hq ρ hρ c i

def diagramIso : BranchSignedDiagramIso
    (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq))
    (positivePolygonEventDiagram q hq) where
  arcEquiv := arcEquiv q hq ρ hρ
  crossingEquiv := diagramCrossingEquiv q hq ρ hρ
  branchEquiv c := branchFin q ρ ((crossingFin (q ∘ ρ)).symm c)
  incoming_map := by
    intro c i
    obtain ⟨c,rfl⟩ := (crossingFin (q ∘ ρ)).surjective c
    simpa only [diagramCrossingEquiv_crossing,Equiv.symm_apply_apply] using arcEquiv_incoming q hq ρ hρ c i
  outgoing_map := by
    intro c i
    obtain ⟨c,rfl⟩ := (crossingFin (q ∘ ρ)).surjective c
    simpa only [diagramCrossingEquiv_crossing,Equiv.symm_apply_apply] using arcEquiv_outgoing q hq ρ hρ c i
  continuation_map := arcEquiv_continuation q hq ρ hρ
  through_map := by intro c i; rfl
  overBranch_map := by
    intro c
    obtain ⟨c,rfl⟩ := (crossingFin (q ∘ ρ)).surjective c
    simpa only [diagramCrossingEquiv_crossing,Equiv.symm_apply_apply] using branchFin_over q ρ hρ hq c
  crossingSign_map := by
    intro c
    rw [positivePolygonEventDiagram_crossingSign,positivePolygonEventDiagram_crossingSign]

theorem normalizedEvaluator_relabel
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H) :
    H (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq))
      (positivePolygonEventDiagram_nArc_pos _ _) =
    H (positivePolygonEventDiagram q hq) (positivePolygonEventDiagram_nArc_pos _ _) :=
  (diagramIso q hq ρ hρ).normalizedEvaluator_eq H hH _ _

end DirectGLSSW.PolygonRebase
