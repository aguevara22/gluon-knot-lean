import PolygonIncomingNext
import DirectGLSSW.TruncationEventOrder
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open Equiv PolygonDrawing MarkedCycleGaps TruncationDirection TruncationEdgeLift TruncationEventOrder
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hs : 0 < ε * scale) (hs1 : ε * scale < 1)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
include hp hε hε1 hs hs1 hleft hright hpoint in
theorem truncation_positive_incoming_next :
    next (positivePolygonEventDiagram q hq).continuation
      (fun m : PolygonCrossing q × Fin 2 => (positivePolygonEventDiagram q hq).incoming
        (crossingFin q m.1) m.2)
      (labelledIncoming_injective (positivePolygonEventDiagram q hq) (crossingFin q)) =
    next (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ).continuation
      (fun m : PolygonCrossing q × Fin 2 =>
        (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ).incoming
          ((E.trans (crossingFin (truncateCyclicCorner q a p scale ε))) m.1) m.2)
      (labelledIncoming_injective (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ)
        (E.trans (crossingFin (truncateCyclicCorner q a p scale ε)))) := by
  let Q := truncateCyclicCorner q a p scale ε
  have hd := polygon_incoming_next_eq_visits q hq (κ := PolygonCrossing q) (Equiv.refl (PolygonCrossing q))
  have he := polygon_incoming_next_eq_visits Q hQ (κ := PolygonCrossing q) E
  simp only [Equiv.refl_trans, Equiv.refl_apply] at hd
  apply hd.trans
  apply Eq.trans _ he.symm
  letI := polygonEventOrder q hq.g2
  letI := polygonEventOrder Q hQ.g2
  apply next_ordered_eq_of_order
  intro x y
  have h := truncationPolygonEventMap_order_iff hq.size_ge_three q a p hp scale ε
    hε hε1 hs hs1 hq hQ E hleft hright hpoint (visit q x.1 x.2) (visit q y.1 y.2)
  have hv (z : PolygonCrossing q × Fin 2) :
      truncationPolygonEventMap q a p scale ε E (visit q z.1 z.2) = visit Q (E z.1) z.2 := by
    rfl
  rw [hv,hv] at h
  exact h
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
