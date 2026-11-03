import EventCursorFilter
import HistoryPhysicalCrossingEquiv
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PolygonDrawingBridge PolygonDrawing SmoothingCornerGeometry EventSegmentGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

/-- Actual original event positions give the literal physical suffix filter,
including a cursor at the source endpoint. -/
theorem original_event_physical_filter {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) (x : PolygonEvent q) (a : ℕ) (θ : ℝ)
    (hcarrier : (polygonEventEdge q x).val=a+1)
    (hlo : polygonEventParameter q x ≤ θ)
    (hhi : θ < polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three x)
    (d : ActiveArc.Crossing (cutArc q 0)) :
    (a ≤ d.val.1.val ∧ (d.val.1.val=a → θ < ActiveArc.leftParameter (cutArc q 0) d)) ↔
      ∀ i : Fin 2, visitPosition (initialAnchorTraversal q hq) (eventFin q x) ≤
        visitPosition (initialAnchorTraversal q hq)
          ((positivePolygonEventDiagram q hq).incoming (crossingFin q (exposedCrossingEquiv q 0 hq he d)) i) := by
  rw [exposed_crossing_cursor_filter q hq he]
  have H (i : Fin 2) :
      visitPosition (initialAnchorTraversal q hq) (eventFin q x) ≤
        visitPosition (initialAnchorTraversal q hq)
          ((positivePolygonEventDiagram q hq).incoming (crossingFin q (exposedCrossingEquiv q 0 hq he d)) i) ↔
      a+1 < (crossingVisitEdge q (exposedCrossingEquiv q 0 hq he d,if i=0 then false else true)).val ∨
        (a+1 = (crossingVisitEdge q (exposedCrossingEquiv q 0 hq he d,if i=0 then false else true)).val ∧
          θ < crossingVisitParameter q (exposedCrossingEquiv q 0 hq he d,if i=0 then false else true)) := by
    have H0 := initial_event_cursor_filter q hq x (exposedCrossingEquiv q 0 hq he d) i θ hlo hhi
    simp only [Fin.lt_iff_val_lt_val,Fin.ext_iff] at H0
    rw [hcarrier] at H0
    simpa only [visit,polygonEventEdge,polygonEventParameter,Fin.ext_iff] using H0
  constructor
  · intro hh i
    exact (H i).mpr (hh _)
  · intro hh v
    cases v
    · exact (H 0).mp (hh 0)
    · exact (H 1).mp (hh 1)

variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q) (he : LeftExposed q 0)
    (r : Fin (positivePolygonEventDiagram q hq).nArc) (a b : ℕ) (hs : a+b=n) (θ : ℝ)
    (hcarrier : (polygonEventEdge q ((eventFin q).symm r)).val=a+1)
    (hlo : polygonEventParameter q ((eventFin q).symm r) ≤ θ)
    (hhi : θ < polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three ((eventFin q).symm r))

/-- The physical crossing carrier at an arbitrary original arc is its complete
original two-port suffix carrier. The positive-radius/gap restrictions follow
from the actual event interval rather than being supplied independently. -/
def originalArcPhysicalCrossingEquiv :
    ActiveArc.Crossing (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ) ≃
      SuffixCrossing (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) r := by
  let x := (eventFin q).symm r
  have h0 : 0≤θ := le_trans (polygonEventParameter_bounds q x).1 hlo
  have h1 : θ<1 := lt_of_lt_of_le hhi (polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three x).2
  let C := {d : ActiveArc.Crossing (cutArc q 0) //
    a ≤ d.val.1.val ∧ (d.val.1.val=a → θ<ActiveArc.leftParameter (cutArc q 0) d)}
  let s := positivePolygonMarkedState q hq (initialAnchorTraversal q hq)
  have hfilter (d : ActiveArc.Crossing (cutArc q 0)) :
      (a ≤ d.val.1.val ∧ (d.val.1.val=a → θ<ActiveArc.leftParameter (cutArc q 0) d)) ↔
      ∀ i : Fin 2, visitPosition (initialAnchorTraversal q hq) r ≤
        visitPosition (initialAnchorTraversal q hq)
          ((positivePolygonEventDiagram q hq).incoming (crossingFin q (exposedCrossingEquiv q 0 hq he d)) i) := by
    simpa only [x,Equiv.apply_symm_apply] using original_event_physical_filter q hq he x a θ hcarrier hlo hhi d
  let f : C → SuffixCrossing s r :=
    fun d => ⟨crossingFin q (exposedCrossingEquiv q 0 hq he d.val),(hfilter d.val).mp d.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro d e hh
      apply Subtype.ext
      apply (exposedCrossingEquiv q 0 hq he).injective
      apply (crossingFin q).injective
      exact congrArg Subtype.val hh
    · intro d
      let z := (exposedCrossingEquiv q 0 hq he).symm ((crossingFin q).symm d.val)
      have hz : crossingFin q (exposedCrossingEquiv q 0 hq he z)=d.val := by
        simp only [z,Equiv.apply_symm_apply]
      have hp : a≤z.val.1.val ∧ (z.val.1.val=a → θ<ActiveArc.leftParameter (cutArc q 0) z) := by
        apply (hfilter z).mpr
        simpa only [hz] using d.property
      exact ⟨⟨z,hp⟩,Subtype.ext hz⟩
  exact (ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq) a b hs θ h0 h1).trans
    (Equiv.ofBijective f hf)

theorem originalArcPhysicalCrossingEquiv_val
    (d : ActiveArc.Crossing (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ)) :
    (originalArcPhysicalCrossingEquiv q hq he r a b hs θ hcarrier hlo hhi d).val =
      crossingFin q (exposedCrossingEquiv q 0 hq he
        ((ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq) a b hs θ
          (le_trans (polygonEventParameter_bounds q ((eventFin q).symm r)).1 hlo)
          (lt_of_lt_of_le hhi (polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three ((eventFin q).symm r)).2) d).val)) := rfl




end DirectGLSSW.HOMFLY.PhysicalCursorComparison
