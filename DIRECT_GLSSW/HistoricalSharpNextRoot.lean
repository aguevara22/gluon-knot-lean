import HistoricalSharpEvaluatorCore
import DetachedIncomingNext
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge
  SmoothingCornerGeometry Coefficients MarkedCycleGaps
attribute [local instance] Classical.propDecidable
private theorem next_mark_congr {α ι : Type*} [Fintype α] [Fintype ι]
    (p : Equiv.Perm α) (f g : ι → α) (hf : Function.Injective f)
    (hg : Function.Injective g) (hfg : f = g) : next p f hf = next p g hg := by
  subst g
  rfl
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

theorem historicalSharp_event_step (x : PolygonEvent q) :
    eventFin q (SharpDaughter.P q hq (sharpSupport q hq h c) x) =
      cutContinuation (positivePolygonEventDiagram q hq) (h.crossingOrigin c) (eventFin q x) := by
  simpa only [SharpDaughter.P,sharpSupport,Equiv.apply_symm_apply] using
    eventFin_singleton_dart_step q hq ((crossingFin q).symm (h.crossingOrigin c)) x

def historicalSharp_cutFibreEquiv :
    SharpDaughter.Arc q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R) ≃
      Fibre (cutContinuation (positivePolygonEventDiagram q hq) (h.crossingOrigin c))
        (componentOf (cutContinuation (positivePolygonEventDiagram q hq) (h.crossingOrigin c))
          (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)) :=
  Equiv.subtypeEquiv (eventFin q) (by
    intro x
    change componentOf _ x = componentOf _ (sharpIntervalEvent q hq h c hc R _) ↔ _
    rw [componentOf_eq_iff,componentOf_eq_iff]
    simpa only [sharpIntervalEvent,Equiv.apply_symm_apply] using
      sameCycle_iff_of_intertwining (eventFin q) _ _ (historicalSharp_event_step q hq h c)
        x (sharpIntervalEvent q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩))

def historicalSharp_arcCutEquiv :=
  (SharpDaughter.arcEquiv q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R)).trans
    (historicalSharp_cutFibreEquiv q hq h c hc R)

theorem historicalSharp_arcCutEquiv_step (a : Fin (historicalSharpDiagram q hq h c hc R).nArc) :
    historicalSharp_arcCutEquiv q hq h c hc R ((historicalSharpDiagram q hq h c hc R).continuation a) =
      fibrePerm _ _ (historicalSharp_arcCutEquiv q hq h c hc R a) := by
  apply Subtype.ext
  change SharpDaughter.oldArc q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R)
    (SharpDaughter.next q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R) a) = _
  rw [SharpDaughter.old_next]
  exact historicalSharp_event_step q hq h c _

theorem historicalSharp_arcCutEquiv_incoming (m : Fin R.diagram.nCrossing × Fin 2) :
    historicalSharp_arcCutEquiv q hq h c hc R
      ((historicalSharpDiagram q hq h c hc R).incoming
        (historicalSharpCrossingEquiv q hq h c hc R m.1) m.2) =
      h.detachedOriginalIncomingMark c hc R m := by
  apply Subtype.ext
  change SharpDaughter.oldArc q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R)
    (SharpDaughter.incomingIndex q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R)
      (historicalSharpCrossingEquiv q hq h c hc R m.1) m.2) = _
  rw [SharpDaughter.old_incoming,historicalSharpCrossingEquiv_origin]
  rfl

theorem historicalSharpIncoming_next_eq :
    next R.diagram.continuation
      (fun m : Fin R.diagram.nCrossing × Fin 2 => R.diagram.incoming m.1 m.2)
      (@incomingMark_injective R.diagram) =
    next (historicalSharpDiagram q hq h c hc R).continuation
      (fun m : Fin R.diagram.nCrossing × Fin 2 =>
        (historicalSharpDiagram q hq h c hc R).incoming
          (historicalSharpCrossingEquiv q hq h c hc R m.1) m.2)
      (labelledIncoming_injective _ (historicalSharpCrossingEquiv q hq h c hc R)) := by
  let mark := fun m : Fin R.diagram.nCrossing × Fin 2 =>
    (historicalSharpDiagram q hq h c hc R).incoming
      (historicalSharpCrossingEquiv q hq h c hc R m.1) m.2
  have hm : (historicalSharp_arcCutEquiv q hq h c hc R) ∘ mark =
      h.detachedOriginalIncomingMark c hc R :=
    funext (historicalSharp_arcCutEquiv_incoming q hq h c hc R)
  have he := next_conjugacy (historicalSharpDiagram q hq h c hc R).continuation
    (fibrePerm _ _) (historicalSharp_arcCutEquiv q hq h c hc R)
    (historicalSharp_arcCutEquiv_step q hq h c hc R) mark
    (labelledIncoming_injective _ (historicalSharpCrossingEquiv q hq h c hc R))
  have hh := next_mark_congr (fibrePerm _ _) _ _
    ((historicalSharp_arcCutEquiv q hq h c hc R).injective.comp
      (labelledIncoming_injective _ (historicalSharpCrossingEquiv q hq h c hc R)))
    (h.detachedOriginalIncomingMark_injective c hc R) hm
  exact (h.detachedIncoming_next_eq c hc R).trans (he.trans hh).symm

/-- Every normalized evaluator agrees on the actual historical detached child
and its exact original singleton sharp diagram. All matching data are derived. -/
theorem historicalSharpEvaluator_eq
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H) :
    H R.diagram R.nonempty = H (historicalSharpDiagram q hq h c hc R)
      (historicalSharpDiagram_nArc_pos q hq h c hc R) :=
  historicalSharpEvaluator_eq_of_next q hq h c hc R H hH
    (historicalSharpIncoming_next_eq q hq h c hc R)

theorem historicalSharpCandidateEvaluator_eq :
    Gemini.candidateEvaluator R.diagram R.nonempty =
      Gemini.candidateEvaluator (historicalSharpDiagram q hq h c hc R)
        (historicalSharpDiagram_nArc_pos q hq h c hc R) :=
  historicalSharpEvaluator_eq q hq h c hc R Gemini.candidateEvaluator
    (Gemini.candidateEvaluator_isNormalized Gemini.all_lowerCrossingEvaluatorSkeinIH)




end DirectGLSSW.HOMFLY.ProcessedExposedChild
