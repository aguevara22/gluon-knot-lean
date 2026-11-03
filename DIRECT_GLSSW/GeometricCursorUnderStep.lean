import GeometricCursorSwitchStep
import GeometricCursorParentStep
import GeometricCursorOrientation
import PhysicalFirstGoodBefore
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PolygonDrawingBridge SmoothingCornerGeometry ExposedOpenPrimitive PhysicalParentHistory

/-- An actual first-under physical step produces both literal history branches.
Badness, first-bad admissibility, and the original-event radius are derived. -/
theorem exists_under_cursors {n a b : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) (p : Fin (a+b+2) → PlanarPoint ℝ)
    (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (C : GeometricCursor q hq p t h) (hR : ActiveArc.Regular p)
    (c : ActiveArc.Crossing p) (hc : ActiveArc.Cursor.FirstCrossing p c)
    (hcut : c.val.2.val=a)
    (hu : crossingUnder p (ActiveArc.polygonCrossingOfArc p c)=(ActiveArc.polygonCrossingOfArc p c).val.1) :
    ∃ (hb : badAt t.2.1 ((C.crossingEquiv he) c).val)
      (hg : MarkedG.GoodBefore t ((C.crossingEquiv he) c).val),
      Nonempty (GeometricCursor q hq (ActiveArc.Split.parent p c hcut)
        (MarkedG.continuingState t ((C.crossingEquiv he) c).val hb hg)
        (continuingTrace h ((C.crossingEquiv he) c).val hb hg)) ∧
      ∃ R : ℝ, 0<R ∧ ∀ ε : ℝ, 0<ε → ε<R →
        ActiveArc.leftParameter p c+ε<ActiveArc.Cursor.afterBound p c →
        Nonempty (GeometricCursor q hq
          (ActiveArc.Cursor.moveStart p (ActiveArc.leftParameter p c+ε))
          (MarkedG.switchedState t ((C.crossingEquiv he) c).val hb hg)
          (switchedTrace h ((C.crossingEquiv he) c).val hb hg)) := by
  let hb := C.under_bad he c hu
  let hg := C.first_good_before q hq he p t h c hc
  exact ⟨hb,hg,exists_parent_cursor q hq he p t h C c hcut hb hg,
    exists_switched_cursor_radius q hq he p t h C hR c hc hb hg⟩
end DirectGLSSW.HOMFLY.PhysicalCursorComparison
