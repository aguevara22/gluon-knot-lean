import BoundaryPhysicalCrossingEquiv
import GeometricCursorBoundary
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PolygonDrawingBridge SmoothingCornerGeometry ActiveArc.ExposedChart ExposedOpenPrimitive

/-- A real geometric cursor supplies the complete physical/current crossing
correspondence. Only the literal word equality transports the physical carrier;
no ancestry, bijection, gap or matching gate is supplied separately. -/
def GeometricCursor.crossingEquiv {n m : ℕ}
    {q : Fin (n+2) → PlanarPoint ℝ} {hq : CyclicGeneric q}
    {p : Fin (m+2) → PlanarPoint ℝ} {t : MarkedParentState}
    {h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t}
    (G : GeometricCursor q hq p t h) (he : LeftExposed q 0) :
    ActiveArc.Crossing p ≃ SuffixCrossing t G.boundaryArc :=
  (Equiv.cast (congrArg (fun r : Fin (m+2) → PlanarPoint ℝ => ActiveArc.Crossing r) G.word)).trans
    (boundaryPhysicalCrossingEquiv q hq he h G.boundaryArc G.boundary G.offset m G.size G.parameter
      G.carrier G.afterSource G.beforeTarget)


end DirectGLSSW.HOMFLY.PhysicalCursorComparison
