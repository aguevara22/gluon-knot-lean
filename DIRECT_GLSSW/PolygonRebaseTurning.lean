import PolygonRebaseDiagramIso
import FramingActualRelations
import ActualTerminalFramedValue

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PolygonRebase
open HOMFLY HOMFLY.PolygonDrawingBridge HOMFLY.PolygonDrawing
  HOMFLY.PrincipalTurning HOMFLY.Coefficients LowestRowContract PermutationOrbits
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))

theorem arcVector_relabel (e) :
    arcVector (positivePolygonEventDiagram q hq) (arcEquiv q hq ρ hρ e) =
      arcVector (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)) e := by
  obtain ⟨x,rfl⟩ := (eventFin (q ∘ ρ)).surjective e
  rw [arcEquiv_event]
  simp only [arcVector,positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram]
  rw [coordinate_target,coordinate_source,coordinate_target,coordinate_source]
  simp only [Equiv.symm_apply_apply,arcSource,arcTarget,vertexPoint_eventVertex]
  rw [← eventEquiv_successor q hq ρ hρ,eventEquiv_point q ρ hρ hq,eventEquiv_point q ρ hρ hq]

theorem turn_relabel (e) :
    turn (positivePolygonEventDiagram q hq) (arcEquiv q hq ρ hρ e) =
      turn (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)) e := by
  unfold turn
  rw [← arcEquiv_continuation,arcVector_relabel,arcVector_relabel]

theorem totalTurn_relabel :
    totalTurn (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)) =
      totalTurn (positivePolygonEventDiagram q hq) := by
  unfold totalTurn
  exact Fintype.sum_equiv (arcEquiv q hq ρ hρ) _ _
    (fun e => (turn_relabel q hq ρ hρ e).symm)

theorem turnInteger_relabel :
    turnInteger (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)) =
      turnInteger (positivePolygonEventDiagram q hq) := by
  apply turnInteger_unique
  rw [totalTurn_relabel q hq ρ hρ]
  exact totalTurn_eq_turnInteger _

theorem diagramWrithe_relabel :
    diagramWrithe (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)) =
      diagramWrithe (positivePolygonEventDiagram q hq) := by
  unfold diagramWrithe
  apply Fintype.sum_equiv (diagramCrossingEquiv q hq ρ hρ)
  intro c
  unfold writheSign
  rw [(diagramIso q hq ρ hρ).crossingSign_map]
  rfl

theorem candidateEvaluator_relabel :
    Gemini.candidateEvaluator
      (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq))
      (positivePolygonEventDiagram_nArc_pos _ _) =
    Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
      (positivePolygonEventDiagram_nArc_pos _ _) :=
  normalizedEvaluator_relabel q hq ρ hρ Gemini.candidateEvaluator
    (Gemini.candidateEvaluator_isNormalized Gemini.all_lowerCrossingEvaluatorSkeinIH)

theorem framedKnotRow_relabel
    (C : diagramComponent (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)))
    (E : diagramComponent (positivePolygonEventDiagram q hq)) :
    framedKnotRow Gemini.candidateEvaluator
      (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq))
      (positivePolygonEventDiagram_nArc_pos _ _) C =
    framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
      (positivePolygonEventDiagram_nArc_pos _ _) E := by
  have hconnQ : ∀ a b : Fin (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)).nArc,
      (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)).continuation.SameCycle a b := by
    intro a b
    exact (polygonEventDiagram_isCycleOn _ _).2 (Set.mem_univ a) (Set.mem_univ b)
  have hconnq : ∀ a b : Fin (positivePolygonEventDiagram q hq).nArc,
      (positivePolygonEventDiagram q hq).continuation.SameCycle a b := by
    intro a b
    exact (polygonEventDiagram_isCycleOn _ _).2 (Set.mem_univ a) (Set.mem_univ b)
  unfold framedKnotRow
  rw [componentTurnInteger_eq_total_of_connected _ hconnQ,
    componentTurnInteger_eq_total_of_connected _ hconnq,
    diagramWrithe_relabel q hq ρ hρ,turnInteger_relabel q hq ρ hρ,candidateEvaluator_relabel q hq ρ hρ]

end DirectGLSSW.PolygonRebase
