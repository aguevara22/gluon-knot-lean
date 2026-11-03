import DirectGLSSW.HOMFLY.HOMFYSmoothingDiagram
import DirectGLSSW.HOMFLY.BasedTraversal

namespace DirectGLSSW.HOMFLY

theorem smoothCrossing_crossing_count_drop (D : PLLinkDiagram)
    (c : Fin D.nCrossing) :
    (smoothCrossing D c).nCrossing + 1 = D.nCrossing := by
  have hc : 0 < D.nCrossing := lt_of_le_of_lt (Nat.zero_le c.val) c.isLt
  simp [smoothCrossing]
  omega

theorem smoothCrossing_arc_count_add_two (D : PLLinkDiagram)
    (c : Fin D.nCrossing) :
    (smoothCrossing D c).nArc = D.nArc + 2 := rfl

theorem smoothCrossing_retained_continuation (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (d : Fin (D.nCrossing - 1)) (i : Fin 2) :
    (smoothCrossing D c).continuation ((smoothCrossing D c).incoming d i) =
      (smoothCrossing D c).outgoing d
        ((smoothCrossing D c).through d i) :=
  (smoothCrossing D c).continuation_crossing d i

theorem smoothCrossing_other_old_continuation (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hd : d ≠ c) (i : Fin 2) :
    (smoothCrossing D c).continuation
        ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨d, hd⟩) i) =
      (smoothCrossing D c).outgoing (smoothCrossingEquiv D c ⟨d, hd⟩)
        (D.through d i) := by
  simpa [smoothCrossing, smoothThrough] using
    smoothCrossing_retained_continuation D c (smoothCrossingEquiv D c ⟨d, hd⟩) i

noncomputable def smoothChildBasedTraversal (D : PLLinkDiagram)
    (c : Fin D.nCrossing) : BasedTraversal (smoothCrossing D c) :=
  chooseBasedTraversal (smoothCrossing D c)

theorem smoothChild_badCrossings_switch_reduces
    (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (T : BasedTraversal (smoothCrossing D c))
    (d : Fin (smoothCrossing D c).nCrossing)
    (hd : d ∈ badCrossings T) :
    (badCrossings (switchTraversal T d)).card + 1 = (badCrossings T).card ∧
      (switchCrossing (smoothCrossing D c) d).nCrossing + 1 = D.nCrossing := by
  constructor
  · exact badCrossings_switch_card T d hd
  · rw [switch_crossing_count]
    exact smoothCrossing_crossing_count_drop D c

theorem smoothChild_nonempty_badCrossings_has_descent
    (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (T : BasedTraversal (smoothCrossing D c))
    (hbad : (badCrossings T).Nonempty) :
    ∃ d, d ∈ badCrossings T ∧
      (badCrossings (switchTraversal T d)).card + 1 = (badCrossings T).card ∧
      (switchCrossing (smoothCrossing D c) d).nCrossing + 1 = D.nCrossing := by
  rcases hbad with ⟨d, hd⟩
  exact ⟨d, hd, smoothChild_badCrossings_switch_reduces D c T d hd⟩

theorem smoothChild_chosenTraversal_nonempty_badCrossings_has_descent
    (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hbad : (badCrossings (smoothChildBasedTraversal D c)).Nonempty) :
    ∃ d, d ∈ badCrossings (smoothChildBasedTraversal D c) ∧
      (badCrossings (switchTraversal (smoothChildBasedTraversal D c) d)).card + 1 =
        (badCrossings (smoothChildBasedTraversal D c)).card ∧
      (switchCrossing (smoothCrossing D c) d).nCrossing + 1 = D.nCrossing :=
  smoothChild_nonempty_badCrossings_has_descent D c (smoothChildBasedTraversal D c) hbad

end DirectGLSSW.HOMFLY









