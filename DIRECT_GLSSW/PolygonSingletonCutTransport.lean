import ProcessedChildOriginalCutWord
import PositivePolygonAnchorTraversal
import ActiveArcCutRetainedWords
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW PermutationOrbits PolygonDrawing Equiv
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
attribute [local instance] Classical.propDecidable
local instance : DecidableEq (PolygonEvent q) :=
  inferInstanceAs (DecidableEq (Fin n ⊕ (PolygonCrossing q × Bool)))

/-- The actual cut of incoming PL arcs is the polygon singleton dart smoothing,
not the incoming-event convention. -/
theorem eventFin_singleton_dart_step (c : PolygonCrossing q) (x : PolygonEvent q) :
    eventFin q (smoothingDartPermutation q hq.g2 {c} x) =
      cutContinuation (positivePolygonEventDiagram q hq) (crossingFin q c) (eventFin q x) := by
  have hin (i : Fin 2) : (positivePolygonEventDiagram q hq).incoming (crossingFin q c) i =
      eventFin q (incoming q hq c i) := by
    simp only [positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram,incomingIndex,Equiv.symm_apply_apply]
  have hs' : polygonEventSuccessor q hq.g2 (swap (incoming q hq c 0) (incoming q hq c 1) x) =
      smoothingDartPermutation q hq.g2 {c} x := by
    rw [smoothingDartPermutation_apply,smoothingPairing_singleton]
    have h0 : polygonEventSuccessor q hq.g2 (incoming q hq c 0) = Sum.inr (c,false) := by
      simpa [visit] using incoming_successor q hq c 0
    have h1 : polygonEventSuccessor q hq.g2 (incoming q hq c 1) = Sum.inr (c,true) := by
      simpa [visit] using incoming_successor q hq c 1
    have htf : (Sum.inr (c,true) : PolygonEvent q) ≠ Sum.inr (c,false) := by
      intro he
      have hb : true = false := congrArg Prod.snd (Sum.inr.inj he)
      cases hb
    by_cases hx : x=incoming q hq c 0
    · subst x
      simp only [Equiv.swap_apply_def]
      simp [h0,h1]
    · by_cases hy : x=incoming q hq c 1
      · subst x
        simp only [Equiv.swap_apply_def]
        simp [h0,h1,hx,htf]
      · have hx' : polygonEventSuccessor q hq.g2 x ≠ Sum.inr (c,false) :=
          fun hh => hx ((polygonEventSuccessor q hq.g2).injective (hh.trans h0.symm))
        have hy' : polygonEventSuccessor q hq.g2 x ≠ Sum.inr (c,true) :=
          fun hh => hy ((polygonEventSuccessor q hq.g2).injective (hh.trans h1.symm))
        simp only [Equiv.swap_apply_def]
        simp only [hx,hy,hx',hy',if_false]
  rw [←hs']
  rw [←polygonEventDiagram_continuation]
  rw [cutContinuation,Perm.mul_apply,hin,hin]
  exact congrArg (polygonEventDiagram q hq).continuation
    ((eventFin q).injective.map_swap (incoming q hq c 0) (incoming q hq c 1) x)
end DirectGLSSW.HOMFLY.PolygonDrawingBridge

namespace DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW ExposedOpenPrimitive PermutationOrbits HOMFLY HOMFLY.PolygonDrawingBridge
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))
    (hq : CyclicGeneric q) (he : LeftExposed q e)

/-- Actual singleton incoming events of the fixed exposed opening, relabelled
as original PL arcs with the correct dart convention. -/
def singletonDiagramEquiv (c : ActiveArc.Crossing (cutArc q e)) :
    ActiveArc.Event (cutArc q e) ≃ Fin (positivePolygonEventDiagram q hq).nArc :=
  (dartEventEquiv q e hq he {c}).trans (eventFin q)

theorem singletonDiagramEquiv_step (c : ActiveArc.Crossing (cutArc q e))
    (x : ActiveArc.Event (cutArc q e)) :
    singletonDiagramEquiv q e hq he c
      (ActiveArc.incoming (cutArc q e) (cutArc_regular q e hq).noTriple {c} x) =
    cutContinuation (positivePolygonEventDiagram q hq)
      (crossingFin q (exposedCrossingEquiv q e hq he c))
      (singletonDiagramEquiv q e hq he c x) := by
  change eventFin q (dartEventEquiv q e hq he {c} (_)) = _
  rw [dartEventEquiv_intertwine]
  have hs : mappedSupport q e hq he {c} = {exposedCrossingEquiv q e hq he c} := by
    simp only [mappedSupport,Finset.map_singleton,Equiv.toEmbedding_apply]
  rw [hs,eventFin_singleton_dart_step]
  rfl

theorem singletonDiagramEquiv_terminal (c : ActiveArc.Crossing (cutArc q e)) :
    singletonDiagramEquiv q e hq he c (ActiveArc.terminal (cutArc q e)) =
      eventFin q (Sum.inl e) := by
  change eventFin q (smoothingPairing q (mappedSupport q e hq he {c}) (eventEquiv q e hq he (ActiveArc.terminal _))) = _
  rw [eventEquiv_terminal]
  rfl
end DirectGLSSW.ActiveArc.ExposedChart
