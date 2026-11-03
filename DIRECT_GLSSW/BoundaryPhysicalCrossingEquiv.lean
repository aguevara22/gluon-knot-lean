import BoundarySuffixCrossingEquiv
import OriginalArcPhysicalCrossingEquiv
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PolygonDrawingBridge PolygonDrawing SmoothingCornerGeometry EventSegmentGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q) (he : LeftExposed q 0)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (A : Fin t.1.nArc) (B : CursorBoundary t (visitPosition t.2.1 A))
    (a b : ℕ) (hs : a+b=n) (θ : ℝ)
    (hcarrier : (polygonEventEdge q ((eventFin q).symm (h.boundaryOrigin A B))).val=a+1)
    (hlo : polygonEventParameter q ((eventFin q).symm (h.boundaryOrigin A B)) ≤ θ)
    (hhi : θ < polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three
      ((eventFin q).symm (h.boundaryOrigin A B)))

/-- Exact physical/current crossing correspondence at any actual cursor
boundary. Original ancestry and complete suffix coverage are derived from h,B;
the cursor may be the source endpoint of its original event interval. -/
def boundaryPhysicalCrossingEquiv :
    ActiveArc.Crossing (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ) ≃
      SuffixCrossing t A :=
  (originalArcPhysicalCrossingEquiv q hq he (h.boundaryOrigin A B) a b hs θ hcarrier hlo hhi).trans
    (h.boundaryCrossingEquiv A B).symm

/-- The equivalence retains each literal original polygon crossing label. -/
theorem boundaryPhysicalCrossingEquiv_origin
    (d : ActiveArc.Crossing (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ)) :
    h.crossingOrigin (boundaryPhysicalCrossingEquiv q hq he h A B a b hs θ hcarrier hlo hhi d).val =
      crossingFin q (exposedCrossingEquiv q 0 hq he
        ((ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq) a b hs θ
          (le_trans (polygonEventParameter_bounds q ((eventFin q).symm (h.boundaryOrigin A B))).1 hlo)
          (lt_of_lt_of_le hhi (polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three
            ((eventFin q).symm (h.boundaryOrigin A B))).2) d).val)) := by
  have hp := congrArg Subtype.val ((h.boundaryCrossingEquiv A B).apply_symm_apply
    (originalArcPhysicalCrossingEquiv q hq he (h.boundaryOrigin A B) a b hs θ hcarrier hlo hhi d))
  exact hp.trans (originalArcPhysicalCrossingEquiv_val q hq he (h.boundaryOrigin A B) a b hs θ hcarrier hlo hhi d)

/-- All future over/under choices are those of the actual original crossing. -/
theorem boundaryPhysicalCrossingEquiv_bad_iff
    (d : ActiveArc.Crossing (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ)) :
    badAt t.2.1 (boundaryPhysicalCrossingEquiv q hq he h A B a b hs θ hcarrier hlo hhi d).val ↔
      badAt (initialAnchorTraversal q hq)
        (crossingFin q (exposedCrossingEquiv q 0 hq he
          ((ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq) a b hs θ
            (le_trans (polygonEventParameter_bounds q ((eventFin q).symm (h.boundaryOrigin A B))).1 hlo)
            (lt_of_lt_of_le hhi (polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three
              ((eventFin q).symm (h.boundaryOrigin A B))).2) d).val))) := by
  have H := h.boundaryCrossing_bad_iff A B
    (boundaryPhysicalCrossingEquiv q hq he h A B a b hs θ hcarrier hlo hhi d)
  rw [boundaryPhysicalCrossingEquiv_origin q hq he h A B a b hs θ hcarrier hlo hhi d] at H
  exact H




end DirectGLSSW.HOMFLY.PhysicalCursorComparison
