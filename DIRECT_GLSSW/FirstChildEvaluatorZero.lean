import ComponentRestrictionConnected
import FirstChildRestrictionCount
import NormalizedEvaluatorUniqueness
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open Coefficients

theorem normalizedEvaluator_eq_one_of_zero_crossings
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (hzero : D.nCrossing = 0) (hcomp : diagramComponentCount D = 1) :
    H D hD = 1 := by
  have hbad : badCrossings (chooseBasedTraversal D) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro c _
    exact Nat.not_lt_zero c.val (hzero ▸ c.isLt)
  rw [hH.1 D hD (chooseBasedTraversal D) hbad, hcomp]
  simp

namespace PolygonDrawingBridge
 theorem positivePolygonEventDiagram_nArc_pos {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hQ : CyclicGeneric q) :
    0 < (positivePolygonEventDiagram q hQ).nArc := by
  change 0 < (polygonEventDiagram q hQ).nArc
  rw [polygonEventDiagram_arc_card]
  have := hQ.size_ge_three
  omega
end PolygonDrawingBridge
end DirectGLSSW.HOMFLY

namespace DirectGLSSW.ActiveArc.Split
open HOMFLY HOMFLY.Coefficients HOMFLY.PolygonDrawingBridge HOMFLY.LowestRowContract

theorem firstDetachedChildRestriction_normalizedEvaluator_eq_of_zero
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (hQ : CyclicGeneric q) (hR : Regular q) (c : Crossing q)
    (hfirst : c.val.1 = 0) (hcut : c.val.2.val = a)
    (R : ComponentRestriction (smoothCrossing (positivePolygonEventDiagram q hQ)
      (crossingFin q (polygonCrossingOfArc q c)))
      (positiveSmoothedChildComponent q hQ (polygonCrossingOfArc q c)))
    (hChild : CyclicGeneric (child q hR c hfirst hcut))
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (hzero : R.diagram.nCrossing = 0) :
    H R.diagram R.nonempty =
      H (positivePolygonEventDiagram (child q hR c hfirst hcut) hChild)
        (positivePolygonEventDiagram_nArc_pos _ hChild) := by
  have hzChild : (positivePolygonEventDiagram (child q hR c hfirst hcut) hChild).nCrossing = 0 := by
    change Fintype.card (PolygonCrossing (child q hR c hfirst hcut)) = 0
    exact (firstDetachedChildRestriction_nCrossing_eq_card q hQ hR c hfirst hcut R).symm.trans hzero
  have hRone := normalizedEvaluator_eq_one_of_zero_crossings H hH R.diagram R.nonempty
    hzero R.diagramComponentCount_eq_one
  have hChildOne := normalizedEvaluator_eq_one_of_zero_crossings H hH
    (positivePolygonEventDiagram (child q hR c hfirst hcut) hChild)
    (positivePolygonEventDiagram_nArc_pos _ hChild) hzChild
    (positivePolygonEventDiagram_componentCount _ hChild)
  exact hRone.trans hChildOne.symm
end DirectGLSSW.ActiveArc.Split
