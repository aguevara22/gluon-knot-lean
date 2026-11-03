import GeometricCursorGoodStep
import GeometricCursorOrientation
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PolygonDrawingBridge SmoothingCornerGeometry ExposedOpenPrimitive

/-- The actual physical over label supplies the good-state premise internally;
the derived original-event radius preserves the complete geometric cursor. -/
theorem exists_over_cursor_radius {n m : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) (p : Fin (m+2) → PlanarPoint ℝ)
    (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (C : GeometricCursor q hq p t h) (hR : ActiveArc.Regular p)
    (c : ActiveArc.Crossing p) (hc : ActiveArc.Cursor.FirstCrossing p c)
    (ho : crossingOver p (ActiveArc.polygonCrossingOfArc p c)=(ActiveArc.polygonCrossingOfArc p c).val.1) :
    ∃ R : ℝ, 0<R ∧ ∀ ε : ℝ, 0<ε → ε<R →
      ActiveArc.leftParameter p c+ε<ActiveArc.Cursor.afterBound p c →
      Nonempty (GeometricCursor q hq
        (ActiveArc.Cursor.moveStart p (ActiveArc.leftParameter p c+ε)) t h) :=
  exists_good_cursor_radius q hq he p t h C hR c hc (C.over_not_bad he c ho)
end DirectGLSSW.HOMFLY.PhysicalCursorComparison
