import ActiveArcCutVisits
import DirectGLSSW.SmoothingPermutations
import DirectGLSSW.DaughterFirstReturn

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW ExposedOpenPrimitive DaughterFirstReturn
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))
variable (hq : CyclicGeneric q) (he : LeftExposed q e)

def eventEquiv : ActiveArc.Event (cutArc q e) ≃ PolygonEvent q :=
  Equiv.sumCongr (cyclicVertexEquiv e) (visitEquiv q e hq he)

theorem eventEquiv_anchor (i : Fin (n+2)) :
    eventEquiv q e hq he (Sum.inl i)=Sum.inl (cyclicVertexEquiv e i) := rfl

theorem eventEquiv_visit (v : ActiveArc.Visit (cutArc q e)) :
    eventEquiv q e hq he (Sum.inr v)=Sum.inr (visitEquiv q e hq he v) := rfl

def eventLabel : ActiveArc.Event (cutArc q e) → Fin (n+2)
  | .inl i => i
  | .inr v => (ActiveArc.visitEdge (cutArc q e) v).castSucc

theorem eventLabel_val (x : ActiveArc.Event (cutArc q e)) :
    (eventLabel q e x).val=ActiveArc.edgeTag (cutArc q e) x := by cases x <;> rfl

theorem eventEquiv_edge (x : ActiveArc.Event (cutArc q e)) :
    polygonEventEdge q (eventEquiv q e hq he x)=cyclicVertexEquiv e (eventLabel q e x) := by
  cases x with
  | inl i => rfl
  | inr v => exact visitEquiv_edge q e hq he v

theorem eventEquiv_parameter (x : ActiveArc.Event (cutArc q e)) :
    polygonEventParameter q (eventEquiv q e hq he x)=ActiveArc.parameter (cutArc q e) x := by
  cases x with
  | inl i => rfl
  | inr v => exact visitEquiv_parameter q e hq he v

theorem eventEquiv_point (x : ActiveArc.Event (cutArc q e)) :
    polygonEventPoint q (eventEquiv q e hq he x)=ActiveArc.eventPoint (cutArc q e) x := by
  cases x with
  | inl i => rfl
  | inr v => exact visitEquiv_point q e hq he v

theorem eventEquiv_sameEdge_iff (x y : ActiveArc.Event (cutArc q e)) :
    polygonEventEdge q (eventEquiv q e hq he x)=polygonEventEdge q (eventEquiv q e hq he y) ↔
      ActiveArc.edgeTag (cutArc q e) x=ActiveArc.edgeTag (cutArc q e) y := by
  rw [eventEquiv_edge,eventEquiv_edge]
  constructor
  · intro hh
    have hv := congrArg Fin.val ((cyclicVertexEquiv e).injective hh)
    simpa only [eventLabel_val] using hv
  · intro hh
    apply congrArg (cyclicVertexEquiv e)
    apply Fin.ext
    simpa only [eventLabel_val] using hh

theorem eventEquiv_start : eventEquiv q e hq he (ActiveArc.start (cutArc q e))=
    Sum.inl (cyclicSuccessor e) := rfl

theorem eventEquiv_terminal : eventEquiv q e hq he (ActiveArc.terminal (cutArc q e))=
    Sum.inl e := by
  change Sum.inl (cyclicVertexIndex e (n+1))=Sum.inl e
  rw [show n+1=(n+2)-1 by omega,cyclicVertexIndex_last]

def mappedSupport (S : Finset (ActiveArc.Crossing (cutArc q e))) : Finset (PolygonCrossing q) :=
  S.map (exposedCrossingEquiv q e hq he).toEmbedding

theorem mappedSupport_mem (S : Finset (ActiveArc.Crossing (cutArc q e)))
    (c : ActiveArc.Crossing (cutArc q e)) :
    exposedCrossingEquiv q e hq he c∈mappedSupport q e hq he S ↔ c∈S := by
  classical
  simp [mappedSupport]

theorem eventEquiv_pairing (S : Finset (ActiveArc.Crossing (cutArc q e)))
    (x : ActiveArc.Event (cutArc q e)) :
    smoothingPairing q (mappedSupport q e hq he S) (eventEquiv q e hq he x)=
      eventEquiv q e hq he (ActiveArc.pairing (cutArc q e) S x) := by
  classical
  cases x with
  | inl i => rfl
  | inr v =>
    rcases v with ⟨c,b⟩
    change (if (visitEquiv q e hq he (c,b)).1∈mappedSupport q e hq he S then
      Sum.inr (crossingVisitFlip q (visitEquiv q e hq he (c,b))) else
      Sum.inr (visitEquiv q e hq he (c,b)))=
        eventEquiv q e hq he (if c∈S then Sum.inr (c,!b) else Sum.inr (c,b))
    rw [visitEquiv_crossing]
    by_cases hc : c∈S
    · rw [if_pos ((mappedSupport_mem q e hq he S c).mpr hc),if_pos hc,eventEquiv_visit]
      exact congrArg Sum.inr (visitEquiv_flip q e hq he c b).symm
    · rw [if_neg (fun hh => hc ((mappedSupport_mem q e hq he S c).mp hh)),if_neg hc]
      rfl

theorem eventEquiv_retained (S : Finset (ActiveArc.Crossing (cutArc q e)))
    (x : ActiveArc.Event (cutArc q e)) :
    retainedCorner q (mappedSupport q e hq he S) (eventEquiv q e hq he x) ↔
      ActiveArc.retained (cutArc q e) S x := by
  cases x with
  | inl i => rfl
  | inr v => exact mappedSupport_mem q e hq he S v.1

end DirectGLSSW.ActiveArc.ExposedChart
