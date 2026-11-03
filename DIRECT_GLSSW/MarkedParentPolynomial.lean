import TerminalWhitneyRoute
import FramedPolynomialCorner
import ProcessedParentDescent
import FirstChildEvaluatorZero
import ProcessedBadCrossingPositive
import GeminiLowest.ComponentExtraction

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace DirectGLSSW.HOMFLY.MarkedPolynomial
open PermutationOrbits LowestRowContract FramedPolynomial PolygonDrawingBridge Coefficients PolygonDrawing
attribute [local instance] Classical.propDecidable

def row (s : MarkedParentState) (hs : 0 < s.1.nArc) : HOMFLYCoeff :=
  framedKnotRow Gemini.candidateEvaluator s.1 hs
    (componentOf s.1.continuation ⟨0,hs⟩)

theorem trace_nonempty {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (hs : 0 < s.1.nArc) : 0 < t.1.nArc := by
  induction h with
  | nil => exact hs
  | cons step tail ih =>
    apply ih
    cases step with
    | switched S c hc hgood => exact hs
    | smoothed S c hc hgood R => exact R.nonempty

def append {s t u : MarkedParentState} (h : MarkedParentTrace s t)
    (k : MarkedParentTrace t u) : MarkedParentTrace s u :=
  match h with
  | .nil _ => k
  | .cons step tail => .cons step (append tail k)

def detached (t : MarkedParentState) (c : Fin t.1.nCrossing) :
    ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)) :=
  GeminiLowest.canonicalComponentRestriction _ _

/-- Conditional on the outer crossing induction for actual detached components,
the literal parent calculation produces an ordinary integer polynomial. -/
theorem exists_polynomial_of_detached_witnesses
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : ExposedOpenPrimitive.LeftExposed q 0)
    (hchild : ∀ (u : MarkedParentState)
      (hu : MarkedParentTrace ⟨positivePolygonEventDiagram q hq,initialAnchorTraversal q hq,ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩ u)
      (c : Fin u.1.nCrossing), badAt u.2.1 c →
      ∃ F : Polynomial ℤ,
        framedKnotRow Gemini.candidateEvaluator (detached u c).diagram (detached u c).nonempty
          (componentOf (detached u c).diagram.continuation ⟨0,(detached u c).nonempty⟩) =
            framedVariable * polynomialValue F)
    (t : MarkedParentState)
    (h : MarkedParentTrace ⟨positivePolygonEventDiagram q hq,initialAnchorTraversal q hq,ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩ t) :
    ∃ F : Polynomial ℤ,
      row t (trace_nonempty h (positivePolygonEventDiagram_nArc_pos q hq)) =
        framedVariable * polynomialValue F := by
  classical
  apply markedParentStep_wellFounded.induction t
    (C := fun t => ∀ h : MarkedParentTrace
      ⟨positivePolygonEventDiagram q hq,initialAnchorTraversal q hq,ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩ t,
      ∃ F : Polynomial ℤ,
        row t (trace_nonempty h (positivePolygonEventDiagram_nArc_pos q hq)) =
          framedVariable * polynomialValue F) _ h
  intro s ih hs
  let hS : 0 < s.1.nArc := trace_nonempty hs (positivePolygonEventDiagram_nArc_pos q hq)
  by_cases hb : (badCrossings s.2.1).Nonempty
  · obtain ⟨c,hc,hgood⟩ := exists_firstBad_goodPrefix s.1 s.2.1 hb
    let sw : MarkedParentState :=
      ⟨switchCrossing s.1 c,switchTraversal s.2.1 c,s.2.2.switchStep c hc hgood⟩
    let stepW : MarkedParentStep s sw := .switched s.2.2 c hc hgood
    let hw := append hs (.cons stepW (.nil sw))
    obtain ⟨FW,hFW⟩ := ih sw ⟨stepW⟩ hw
    let R : ∀ C : diagramComponent (smoothCrossing s.1 c),
        ComponentRestriction (smoothCrossing s.1 c) C :=
      fun C => GeminiLowest.canonicalComponentRestriction _ C
    let RP := R (componentOf (smoothCrossing s.1 c).continuation
      (smoothArcEquiv s.1 (Sum.inr (firstVisitedBranch s.2.1 c))))
    let par : MarkedParentState :=
      ⟨RP.diagram,RP.basedTraversal
        (parentRootSelfSmoothingTraversal s.1 s.2.1 c (s.2.2.connected _ _)),
        s.2.2.smoothStep c hc hgood RP⟩
    let stepP : MarkedParentStep s par := .smoothed s.2.2 c hc hgood RP
    let hp := append hs (.cons stepP (.nil par))
    obtain ⟨FP,hFP⟩ := ih par ⟨stepP⟩ hp
    obtain ⟨FD,hFD⟩ := hchild s hs c hc
    have hpos : crossingSign s.1 c = Sign.pos :=
      hs.bad_crossing_positive_of_initial _ _ (positivePolygonEventDiagram_connected q hq)
        (positivePolygonEventDiagram_crossingSign q hq) s c hc
    have hskein := positive_connected_framed_knot_row s.1 hS s.2.2.connected c hpos
      (firstVisitedBranch s.2.1 c) R
    rw [rootSelfCutComponents_false] at hskein
    change row s hS = row sw hS + row par RP.nonempty *
      framedKnotRow Gemini.candidateEvaluator (detached s c).diagram (detached s c).nonempty
        (componentOf (detached s c).diagram.continuation ⟨0,(detached s c).nonempty⟩) at hskein
    refine ⟨FW + Polynomial.X * FP * FD, ?_⟩
    change row s hS = _
    rw [hskein,hFW,hFP,hFD]
    have hx : polynomialValue Polynomial.X = framedVariable := Polynomial.eval₂_X _ _
    simp only [map_add,map_mul,hx]
    ring
  · have hterminal : ∀ c : Fin s.1.nCrossing, ¬ badAt s.2.1 c := by
      intro c hc
      apply hb
      exact ⟨c,by simpa [badCrossings] using hc⟩
    refine ⟨1, ?_⟩
    have hv := positivePolygon_history_canonical_terminal_framed_value_via_general_whitney q hq he s hs
      hterminal (componentOf s.1.continuation ⟨0,hS⟩)
    simpa only [row,map_one,mul_one] using hv

end DirectGLSSW.HOMFLY.MarkedPolynomial
