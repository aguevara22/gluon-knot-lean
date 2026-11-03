import ActualTerminalFraming

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits PrincipalTurning Coefficients LowestRowContract
attribute [local instance] Classical.propDecidable

/-- Signed writhe, with the same positive-crossing convention as the skein equation. -/
def diagramWrithe (D : PLLinkDiagram) : ℤ :=
  ∑ c : Fin D.nCrossing, writheSign D c

/-- The source framed knot row, using the actual tangent degree of its component. -/
def framedKnotRow (H : Evaluator) (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (C : diagramComponent D) : HOMFLYCoeff :=
  aPower (diagramWrithe D + componentTurnInteger D C) *
    (aMonomial - aInvMonomial) * zRow (H D hD) 0

def framedVariable : HOMFLYCoeff := aMonomial ^ 2 - 1

theorem actual_connected_componentCount (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (hconn : ∀ a b : Fin D.nArc, D.continuation.SameCycle a b) :
    diagramComponentCount D = 1 := by
  letI : Nonempty (Fin D.nArc) := ⟨⟨0,hD⟩⟩
  letI : Fintype (diagramComponent D) := componentFintype D.continuation
  letI : Nonempty (diagramComponent D) :=
    Nonempty.map (componentOf D.continuation) inferInstance
  letI : Subsingleton (diagramComponent D) := ⟨by
    intro C E
    induction C using Quotient.inductionOn with | h a =>
      induction E using Quotient.inductionOn with | h b =>
        exact (componentOf_eq_iff _ a b).2 (hconn a b)⟩
  letI : Unique (diagramComponent D) := Classical.choice (nonempty_unique _)
  change Fintype.card (diagramComponent D) = 1
  exact Fintype.card_unique

theorem normalizedEvaluator_connected_terminal_eq_one
    (H : Evaluator) (hH : IsNormalizedDescendingSkeinEvaluator H)
    (D : PLLinkDiagram) (hD : 0 < D.nArc) (T : BasedTraversal D)
    (hconn : ∀ a b : Fin D.nArc, D.continuation.SameCycle a b)
    (hterminal : ∀ c : Fin D.nCrossing, ¬ badAt T c) : H D hD = 1 := by
  have hb : badCrossings T = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro c hc
    exact hterminal c (Finset.mem_filter.mp hc).2
  rw [hH.1 D hD T hb, actual_connected_componentCount D hD hconn]
  simp

theorem actual_exposed_descending_terminal_frame_int {D : PLLinkDiagram}
    (T : BasedTraversal D)
    (hconn : ∀ a b : Fin D.nArc, D.continuation.SameCycle a b)
    (C : diagramComponent D) (hhalf : actualRootVertexHalfplane T C)
    (hterminal : ∀ c : Fin D.nCrossing, ¬ badAt T c) :
    diagramWrithe D + componentTurnInteger D C = 1 := by
  have h := actual_exposed_descending_terminal_frame T hconn C hhalf hterminal
  have hw : ((diagramWrithe D : ℤ) : ℝ) =
      ∑ c : Fin D.nCrossing, if crossingSign D c = Sign.pos then (1 : ℝ) else -1 := by
    simp only [diagramWrithe,Int.cast_sum]
    apply Finset.sum_congr rfl
    intro c _
    cases hs : crossingSign D c <;> simp [writheSign,hs]
  rw [← hw] at h
  exact_mod_cast h

theorem zRow_one_zero : zRow (1 : HOMFLYCoeff) 0 = 1 := by
  simp [zRow,AddMonoidAlgebra.one_def]

theorem framedKnotRow_exposed_terminal
    (H : Evaluator) (hH : IsNormalizedDescendingSkeinEvaluator H)
    (D : PLLinkDiagram) (hD : 0 < D.nArc) (T : BasedTraversal D)
    (hconn : ∀ a b : Fin D.nArc, D.continuation.SameCycle a b)
    (C : diagramComponent D) (hhalf : actualRootVertexHalfplane T C)
    (hterminal : ∀ c : Fin D.nCrossing, ¬ badAt T c) :
    framedKnotRow H D hD C = framedVariable := by
  rw [framedKnotRow,actual_exposed_descending_terminal_frame_int T hconn C hhalf hterminal,
    normalizedEvaluator_connected_terminal_eq_one H hH D hD T hconn hterminal,
    zRow_one_zero,mul_one]
  change aMonomial * (aMonomial - aInvMonomial) = aMonomial ^ 2 - 1
  rw [mul_sub,aMonomial_mul_aInvMonomial,pow_two]

namespace PolygonDrawingBridge
open ExposedOpenPrimitive

theorem positivePolygon_history_terminal_framed_value
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q ⟨0,by have := hq.size_ge_three;omega⟩)
    (t : MarkedParentState)
    (h : MarkedParentTrace
      ⟨positivePolygonEventDiagram q hq,initialAnchorTraversal q hq,
        ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩ t)
    (hterminal : ∀ c : Fin t.1.nCrossing, ¬ badAt t.2.1 c)
    (C : diagramComponent t.1)
    (H : Evaluator) (hH : IsNormalizedDescendingSkeinEvaluator H) :
    framedKnotRow H t.1 (by exact Nat.zero_lt_of_lt (t.2.1.baseArc C).val.isLt) C =
      framedVariable := by
  exact framedKnotRow_exposed_terminal H hH t.1 _ t.2.1 t.2.2.connected C
    (supportingRootGeometry_actualRootVertexHalfplane t _ _
      (positivePolygon_history_supporting_root q hq he t h) C) hterminal

/-- The terminal framed identity for the already constructed, unconditional evaluator. -/
theorem positivePolygon_history_canonical_terminal_framed_value
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q ⟨0,by have := hq.size_ge_three;omega⟩)
    (t : MarkedParentState)
    (h : MarkedParentTrace
      ⟨positivePolygonEventDiagram q hq,initialAnchorTraversal q hq,
        ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩ t)
    (hterminal : ∀ c : Fin t.1.nCrossing, ¬ badAt t.2.1 c)
    (C : diagramComponent t.1) :
    framedKnotRow Gemini.candidateEvaluator t.1
      (by exact Nat.zero_lt_of_lt (t.2.1.baseArc C).val.isLt) C = framedVariable :=
  positivePolygon_history_terminal_framed_value q hq he t h hterminal C
    Gemini.candidateEvaluator
    (Gemini.candidateEvaluator_isNormalized Gemini.all_lowerCrossingEvaluatorSkeinIH)

end PolygonDrawingBridge
end DirectGLSSW.HOMFLY
