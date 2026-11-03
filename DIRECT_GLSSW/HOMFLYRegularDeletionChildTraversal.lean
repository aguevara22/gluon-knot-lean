import HOMFLYRegularDeletionSmoothing
import HOMFLYRegularDeletionVisitOrder
import DirectGLSSW.HOMFLY.HOMFLYSkeinEvaluator

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section
namespace SignedRegularDeletion
variable {D E : PLLinkDiagram} (R : SignedRegularDeletion D E)

/-- The source smoothing child's given order and roots are transported exactly.
This does not identify the independently chosen target child traversal. -/
def smoothTransportTraversal (c : Fin D.nCrossing)
    (T : BasedTraversal (smoothCrossing D c)) :
    BasedTraversal (smoothCrossing E (R.crossingEquiv c)) :=
  (R.smooth c).transportTraversal T

theorem smoothTransport_crossing_visit_order (c : Fin D.nCrossing)
    (T : BasedTraversal (smoothCrossing D c))
    (d e : Fin (D.nCrossing - 1)) (i j : Fin 2) :
    rankBefore
      (visitRank (R.smoothTransportTraversal c T)
        ((smoothCrossing E (R.crossingEquiv c)).incoming (R.smoothCrossingEquiv c d) i))
      (visitRank (R.smoothTransportTraversal c T)
        ((smoothCrossing E (R.crossingEquiv c)).incoming (R.smoothCrossingEquiv c e) j)) ↔
    rankBefore (visitRank T ((smoothCrossing D c).incoming d i))
      (visitRank T ((smoothCrossing D c).incoming e j)) :=
  (R.smooth c).crossing_visit_order T d e i j

theorem smoothTransport_badAt (c : Fin D.nCrossing)
    (T : BasedTraversal (smoothCrossing D c)) (d : Fin (D.nCrossing - 1)) :
    badAt (R.smoothTransportTraversal c T) (R.smoothCrossingEquiv c d) ↔ badAt T d :=
  (R.smooth c).badAt_map T d

theorem smoothArcMap_connector (i : Fin 2) :
    R.smoothArcMap (smoothArcEquiv D (Sum.inr i)) = smoothArcEquiv E (Sum.inr i) := by
  simp only [smoothArcMap, Equiv.symm_apply_apply, smoothCodeMap, Sum.map_inr, id_eq]

theorem switch_transportTraversal (T : BasedTraversal D) (c : Fin D.nCrossing) :
    (R.switch c).transportTraversal (switchTraversal T c) =
      switchTraversal (R.transportTraversal T) (R.crossingEquiv c) := by
  rfl

theorem badCrossings_card (T : BasedTraversal D) :
    (badCrossings (R.transportTraversal T)).card = (badCrossings T).card := by
  rw [R.badCrossings_map, Finset.card_map]

include R in
theorem source_nArc_pos : 0 < D.nArc := Nat.zero_lt_of_lt R.deleted.isLt
include R in
theorem target_nArc_pos : 0 < E.nArc := Nat.zero_lt_of_lt (R.arcMap R.retained).isLt

include R in
theorem descendingUnlinkValue_eq : descendingUnlinkValue D = descendingUnlinkValue E := by
  simp only [descendingUnlinkValue, Nat.ne_of_gt R.source_nArc_pos,
    Nat.ne_of_gt R.target_nArc_pos, if_false, R.componentCount_eq]

/-- The terminal case of the intended evaluator induction is unconditional. -/
theorem evaluator_eq_of_descending (T : BasedTraversal D) (h : badCrossings T = ∅) :
    descendingLaurentEvaluator D T = descendingLaurentEvaluator E (R.transportTraversal T) := by
  have ht : badCrossings (R.transportTraversal T) = ∅ := by
    rw [R.badCrossings_map, h, Finset.map_empty]
  rw [descendingLaurentEvaluator_terminal D T (by simp [h]),
    descendingLaurentEvaluator_terminal E (R.transportTraversal T) (by simp [ht])]
  exact R.descendingUnlinkValue_eq

end SignedRegularDeletion
end
end DirectGLSSW.HOMFLY











