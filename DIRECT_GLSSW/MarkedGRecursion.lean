import TerminalWhitneyRoute
import MarkedParentPolynomial
import PolygonPolynomialCorner

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.MarkedG
open PermutationOrbits LowestRowContract FramedPolynomial PolygonDrawingBridge Coefficients
attribute [local instance] Classical.propDecidable

/-- Literal negative constant coefficient of the existing framed row. No
evaluation homomorphism on Laurent polynomials is introduced. -/
def value (s : MarkedParentState) (hs : 0 < s.1.nArc) : ℤ :=
  -coeff (MarkedPolynomial.row s hs) 0 0

def detachedValue (s : MarkedParentState) (c : Fin s.1.nCrossing) : ℤ :=
  -coeff (framedKnotRow Gemini.candidateEvaluator
    (MarkedPolynomial.detached s c).diagram (MarkedPolynomial.detached s c).nonempty
    (componentOf (MarkedPolynomial.detached s c).diagram.continuation
      ⟨0,(MarkedPolynomial.detached s c).nonempty⟩)) 0 0

abbrev GoodBefore (s : MarkedParentState) (c : Fin s.1.nCrossing) : Prop :=
  ∀ d : Fin s.1.nCrossing,
    rankBefore (visitRank s.2.1 (s.1.incoming d (firstVisitedBranch s.2.1 d)))
      (visitRank s.2.1 (s.1.incoming c (firstVisitedBranch s.2.1 c))) → ¬ badAt s.2.1 d

def switchedState (s : MarkedParentState) (c : Fin s.1.nCrossing)
    (hc : badAt s.2.1 c) (hgood : GoodBefore s c) : MarkedParentState :=
  ⟨switchCrossing s.1 c,switchTraversal s.2.1 c,s.2.2.switchStep c hc hgood⟩

def continuingRestriction (s : MarkedParentState) (c : Fin s.1.nCrossing) :
    ComponentRestriction (smoothCrossing s.1 c)
      (componentOf (smoothCrossing s.1 c).continuation
        (smoothArcEquiv s.1 (Sum.inr (firstVisitedBranch s.2.1 c)))) :=
  GeminiLowest.canonicalComponentRestriction _ _

def continuingState (s : MarkedParentState) (c : Fin s.1.nCrossing)
    (hc : badAt s.2.1 c) (hgood : GoodBefore s c) : MarkedParentState :=
  ⟨(continuingRestriction s c).diagram,
    (continuingRestriction s c).basedTraversal
      (parentRootSelfSmoothingTraversal s.1 s.2.1 c (s.2.2.connected _ _)),
    s.2.2.smoothStep c hc hgood (continuingRestriction s c)⟩

variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : ExposedOpenPrimitive.LeftExposed q 0)

/-- The polynomial premise is exactly the smaller actual detached-child
induction obligation, shared with the parent polynomial theorem. -/
abbrev DetachedPolynomials : Prop :=
  ∀ (u : MarkedParentState)
    (_hu : MarkedParentTrace ⟨positivePolygonEventDiagram q hq,initialAnchorTraversal q hq,
      ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩ u)
    (c : Fin u.1.nCrossing), badAt u.2.1 c →
    ∃ F : Polynomial ℤ,
      framedKnotRow Gemini.candidateEvaluator (MarkedPolynomial.detached u c).diagram
        (MarkedPolynomial.detached u c).nonempty
        (componentOf (MarkedPolynomial.detached u c).diagram.continuation
          ⟨0,(MarkedPolynomial.detached u c).nonempty⟩) = framedVariable * polynomialValue F

include he

/-- All component choices and continuing-parent polynomial witnesses are
constructed. Only the explicit outer child polynomial induction remains. -/
theorem recurrence_of_detached_polynomials (hchild : DetachedPolynomials q hq)
    (t : MarkedParentState)
    (h : MarkedParentTrace ⟨positivePolygonEventDiagram q hq,initialAnchorTraversal q hq,
      ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩ t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) (hgood : GoodBefore t c) :
    value t (MarkedPolynomial.trace_nonempty h (positivePolygonEventDiagram_nArc_pos q hq)) =
      value (switchedState t c hc hgood)
        (MarkedPolynomial.trace_nonempty (t := t) h (positivePolygonEventDiagram_nArc_pos q hq)) -
      value (continuingState t c hc hgood) (continuingRestriction t c).nonempty *
        detachedValue t c := by
  let hT := MarkedPolynomial.trace_nonempty h (positivePolygonEventDiagram_nArc_pos q hq)
  let par := continuingState t c hc hgood
  let stepP : MarkedParentStep t par :=
    .smoothed t.2.2 c hc hgood (continuingRestriction t c)
  let hp := MarkedPolynomial.append h (.cons stepP (.nil par))
  obtain ⟨FP,hFP⟩ := MarkedPolynomial.exists_polynomial_of_detached_witnesses
    q hq he hchild par hp
  obtain ⟨FD,hFD⟩ := hchild t h c hc
  have hpos : crossingSign t.1 c = Sign.pos :=
    h.bad_crossing_positive_of_initial _ _ (positivePolygonEventDiagram_connected q hq)
      (positivePolygonEventDiagram_crossingSign q hq) t c hc
  let R : ∀ C : diagramComponent (smoothCrossing t.1 c),
      ComponentRestriction (smoothCrossing t.1 c) C :=
    fun C => GeminiLowest.canonicalComponentRestriction _ C
  have hskein := positive_connected_framed_knot_row t.1 hT t.2.2.connected c hpos
    (firstVisitedBranch t.2.1 c) R
  rw [rootSelfCutComponents_false] at hskein
  change MarkedPolynomial.row t hT =
    MarkedPolynomial.row (switchedState t c hc hgood) hT +
    MarkedPolynomial.row par (continuingRestriction t c).nonempty *
      framedKnotRow Gemini.candidateEvaluator (MarkedPolynomial.detached t c).diagram
        (MarkedPolynomial.detached t c).nonempty
        (componentOf (MarkedPolynomial.detached t c).diagram.continuation
          ⟨0,(MarkedPolynomial.detached t c).nonempty⟩) at hskein
  exact polynomialWitness_subtraction _ _ _ _ FP FD hFP hFD hskein

/-- The actual exposed historical terminal has g=1, with no polynomial witness
or child induction supplied. -/
theorem terminal_value (t : MarkedParentState)
    (h : MarkedParentTrace ⟨positivePolygonEventDiagram q hq,initialAnchorTraversal q hq,
      ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩ t)
    (hterminal : ∀ c : Fin t.1.nCrossing, ¬ badAt t.2.1 c) :
    value t (MarkedPolynomial.trace_nonempty h (positivePolygonEventDiagram_nArc_pos q hq)) = 1 := by
  let ht := MarkedPolynomial.trace_nonempty h (positivePolygonEventDiagram_nArc_pos q hq)
  have hv := positivePolygon_history_canonical_terminal_framed_value_via_general_whitney q hq he t h
    hterminal (componentOf t.1.continuation ⟨0,ht⟩)
  unfold value MarkedPolynomial.row
  rw [hv]
  exact framedVariable_negative_constant

/-- At the actual initial uniformly-left polygon, the same g equals the
literal prescribed coefficient, not a guessed lowest occupied degree. -/
theorem initial_value_eq_corner (hchild : DetachedPolynomials q hq)
    (hleft : ∀ e : Fin (n+2), 0 < planarDet (cyclicTangent q e)
      (cyclicTangent q (cyclicSuccessor e))) :
    value ⟨positivePolygonEventDiagram q hq,initialAnchorTraversal q hq,
      ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩
      (positivePolygonEventDiagram_nArc_pos q hq) =
    coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
      (positivePolygonEventDiagram_nArc_pos q hq))
      (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
        |PrincipalTurning.turnInteger (positivePolygonEventDiagram q hq)|) 0 := by
  let s : MarkedParentState := ⟨positivePolygonEventDiagram q hq,initialAnchorTraversal q hq,
    ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩
  obtain ⟨F,hF⟩ := MarkedPolynomial.exists_polynomial_of_detached_witnesses
    q hq he hchild s (.nil s)
  have hg := negative_constant_of_polynomialWitness (MarkedPolynomial.row s
    (positivePolygonEventDiagram_nArc_pos q hq)) F hF
  have hc := positivePolygon_polynomialWitness_corner q hq hleft F hF
  exact hg.trans hc.2.symm




end DirectGLSSW.HOMFLY.MarkedG
