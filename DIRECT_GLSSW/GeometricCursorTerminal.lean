import GeometricCursorBoundary
import GeometricCursorCrossingEquiv
import MarkedGRecursion
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PermutationOrbits PolygonDrawingBridge PolygonDrawing SmoothingCornerGeometry EventSegmentGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive

/-- A physical terminal word has one edge and hence no self-crossing. The
actual complete-suffix correspondence excludes every remaining marked bad
crossing, while the historical marked state retains its processed prefix. -/
theorem GeometricCursor.no_bad_of_terminal {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q) (he : LeftExposed q 0)
    (p : Fin 2 → PlanarPoint ℝ) (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (G : GeometricCursor (m:=0) q hq p t h) :
    ∀ c : Fin t.1.nCrossing, ¬badAt t.2.1 c := by
  intro c hc
  let E := G.crossingEquiv he
  let d := E.symm (CursorBoundary.badSuffix G.boundary c hc)
  have hlt := d.property.1
  have hleft := d.val.1.isLt
  have hright := d.val.2.isLt
  change d.val.1.val < d.val.2.val at hlt
  change d.val.1.val < 1 at hleft
  change d.val.2.val < 1 at hright
  omega

/-- The actual preserved framed knot has terminal marked value one, derived
from the physical one-edge cursor and its complete crossing correspondence. -/
theorem GeometricCursor.terminal_marked_value {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q) (he : LeftExposed q 0)
    (p : Fin 2 → PlanarPoint ℝ) (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (G : GeometricCursor (m:=0) q hq p t h) :
    MarkedG.value t (MarkedPolynomial.trace_nonempty h (positivePolygonEventDiagram_nArc_pos q hq))=1 :=
  MarkedG.terminal_value q hq he t h (G.no_bad_of_terminal q hq he p t h)



end DirectGLSSW.HOMFLY.PhysicalCursorComparison
