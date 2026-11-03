import ExposedSuffixRegular
import HistoryCursorFilter
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PolygonDrawingBridge PolygonDrawing SmoothingCornerGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

/-- Actual original opening, original polygon corners and moving cursor. Both
physical regularity and the original port filter are produced from the history. -/
theorem exists_history_physical_suffix {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) (ξ : ℝ) (hξ0 : 0<ξ) (hξ1 : ξ<1) :
    ∃ a b : ℕ, ∃ hs : a+b=n, ∃ θ : ℝ, 0<θ ∧ θ<1 ∧
      ActiveArc.Regular (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ) ∧
      ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ 0 = historyCursorPoint t c ξ ∧
      ∀ d : ActiveArc.Crossing (cutArc q 0),
        (a ≤ d.val.1.val ∧ (d.val.1.val=a → θ < ActiveArc.leftParameter (cutArc q 0) d)) ↔
        ∀ i : Fin 2,
          visitPosition (initialAnchorTraversal q hq)
            ((positivePolygonEventDiagram q hq).incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) ≤
          visitPosition (initialAnchorTraversal q hq)
            ((positivePolygonEventDiagram q hq).incoming (crossingFin q (exposedCrossingEquiv q 0 hq he d)) i) := by
  let d0 := (crossingFin q).symm (h.crossingOrigin c)
  have hrne : d0.val.1 ≠ 0 := fun hh =>
    leftExposed_no_incident_crossing q hq 0 he d0 (Or.inl hh)
  have hrpos : 0 < d0.val.1.val := by
    by_contra hn
    apply hrne
    apply Fin.ext
    change d0.val.1.val=0
    omega
  let a := d0.val.1.val-1
  let b := n-a
  have ha : a ≤ n := by have := d0.val.1.isLt;dsimp [a];omega
  have hs : a+b=n := by dsimp [b];omega
  have har : d0.val.1.val=a+1 := by dsimp [a];omega
  have har' : (((crossingFin q).symm (h.crossingOrigin c)).val.1).val=a+1 := har
  obtain ⟨θ,h0,h1,hpoint,hno,hfilter⟩ := historyCursorPoint_future_filter q hq h c hc ξ hξ0 hξ1
  refine ⟨a,b,hs,θ,h0,h1,?_,?_,?_⟩
  · exact exposed_suffix_regular q hq he a b hs d0.val.1 har θ (le_of_lt h0) h1 hno
  · rw [ActiveArc.Cursor.moveStart_zero]
    have hv0 : ActiveArc.Split.suffixWord (cutArc q 0) a b hs 0=q d0.val.1 := by
      rw [ActiveArc.Split.suffixWord_vertex]
      unfold cutArc
      congr 1
      apply Fin.ext
      change (0+1+(a+0))%(n+2)=d0.val.1.val
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hv1 : ActiveArc.Split.suffixWord (cutArc q 0) a b hs 1=q (cyclicSuccessor d0.val.1) := by
      rw [ActiveArc.Split.suffixWord_vertex]
      unfold cutArc
      congr 1
      apply Fin.ext
      change (0+1+(a+1))%(n+2)=(d0.val.1.val+1+0)%(n+2)
      rw [har]
      congr 1
      omega
    rw [hv0,hv1]
    exact hpoint.symm
  · intro d
    rw [exposed_crossing_cursor_filter q hq he]
    apply Iff.trans ?_ (hfilter (exposedCrossingEquiv q 0 hq he d)).symm
    constructor
    · intro hh i
      fin_cases i
      · simpa only [visit,Fin.isValue,Fin.reduceEq,ite_true,ite_false,polygonEventEdge,polygonEventParameter,Fin.lt_iff_val_lt_val,Fin.ext_iff,har'] using hh false
      · simpa only [visit,Fin.isValue,Fin.reduceEq,ite_true,ite_false,polygonEventEdge,polygonEventParameter,Fin.lt_iff_val_lt_val,Fin.ext_iff,har'] using hh true
    · intro hh z
      cases z
      · simpa only [visit,Fin.isValue,Fin.reduceEq,ite_true,ite_false,polygonEventEdge,polygonEventParameter,Fin.lt_iff_val_lt_val,Fin.ext_iff,har'] using hh 0
      · simpa only [visit,Fin.isValue,Fin.reduceEq,ite_true,ite_false,polygonEventEdge,polygonEventParameter,Fin.lt_iff_val_lt_val,Fin.ext_iff,har'] using hh 1

end DirectGLSSW.HOMFLY
