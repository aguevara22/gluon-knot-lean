import ExposedWhitneyHistory

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits PrincipalTurning
attribute [local instance] Classical.propDecidable

/-- At a first-over visit the ordered determinant is the actual writhe determinant. -/
theorem firstVisit_det_eq_crossingDet_of_not_bad {D : PLLinkDiagram}
    (T : BasedTraversal D) (c : Fin D.nCrossing) (hc : ¬ badAt T c) :
    complexDet (crossingVector D c (firstVisitedBranch T c))
      (crossingVector D c (otherBranch (firstVisitedBranch T c))) = crossingDet D c := by
  have hb : firstVisitedBranch T c = D.overBranch c := not_ne_iff.mp hc
  simp only [hb, complexDet, crossingVector, crossingDet, planarDet]

theorem actual_crossingSign_pos_iff (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    crossingSign D c = Sign.pos ↔ 0 < crossingDet D c := by
  by_cases hn : crossingDet D c < 0
  · have hp : ¬ 0 < crossingDet D c := not_lt_of_gt hn
    simp [crossingSign, nonzeroScalarSign, hn, hp]
  · have hp : 0 < crossingDet D c :=
      lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (selectedDet_ne_zero D c))
    simp [crossingSign, nonzeroScalarSign, hn, hp]

/-- In a single actual continuation cycle every crossing is a self-crossing. -/
theorem actualComponentSelfCrossings_eq_univ_of_connected {D : PLLinkDiagram}
    (T : BasedTraversal D)
    (hconn : ∀ a b : Fin D.nArc, D.continuation.SameCycle a b)
    (C : diagramComponent D) : actualComponentSelfCrossings T C = Finset.univ := by
  have he (a : Fin D.nArc) : componentOf D.continuation a = C :=
    ((componentOf_eq_iff _ _ _).2 (hconn a (T.baseArc C).val)).trans (T.baseArc C).property
  ext c
  simp [actualComponentSelfCrossings, he]

/-- The terminal framing formula uses actual crossing signs and actual tangent degree. -/
theorem actual_exposed_descending_terminal_frame {D : PLLinkDiagram}
    (T : BasedTraversal D)
    (hconn : ∀ a b : Fin D.nArc, D.continuation.SameCycle a b)
    (C : diagramComponent D) (hhalf : actualRootVertexHalfplane T C)
    (hterminal : ∀ c : Fin D.nCrossing, ¬ badAt T c) :
    (∑ c : Fin D.nCrossing, if crossingSign D c = Sign.pos then (1 : ℝ) else -1) +
      (componentTurnInteger D C : ℝ) = 1 := by
  have h := actualComponent_exposed_whitney T C hhalf
  rw [actualComponentSelfCrossings_eq_univ_of_connected T hconn C] at h
  have hsum :
      (∑ c : Fin D.nCrossing,
        if 0 < complexDet (crossingVector D c (firstVisitedBranch T c))
            (crossingVector D c (otherBranch (firstVisitedBranch T c)))
        then (1 : ℝ) else -1) =
      ∑ c : Fin D.nCrossing, if crossingSign D c = Sign.pos then (1 : ℝ) else -1 := by
    apply Finset.sum_congr rfl
    intro c _
    simp only [firstVisit_det_eq_crossingDet_of_not_bad T c (hterminal c),
      ← actual_crossingSign_pos_iff D c]
  rw [hsum] at h
  linarith

namespace PolygonDrawingBridge
open ExposedOpenPrimitive

/-- Every actual terminal parent retains the source framing formula, with the
supporting halfplane and connectedness discharged by its literal history. -/
theorem positivePolygon_history_terminal_frame
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q ⟨0, by have := hq.size_ge_three; omega⟩)
    (t : MarkedParentState)
    (h : MarkedParentTrace
      ⟨positivePolygonEventDiagram q hq, initialAnchorTraversal q hq,
        ProcessedParentMarks.initial _ _ (positivePolygonEventDiagram_connected q hq)⟩ t)
    (hterminal : ∀ c : Fin t.1.nCrossing, ¬ badAt t.2.1 c)
    (C : diagramComponent t.1) :
    (∑ c : Fin t.1.nCrossing, if crossingSign t.1 c = Sign.pos then (1 : ℝ) else -1) +
      (componentTurnInteger t.1 C : ℝ) = 1 := by
  exact actual_exposed_descending_terminal_frame t.2.1 t.2.2.connected C
    (supportingRootGeometry_actualRootVertexHalfplane t _ _
      (positivePolygon_history_supporting_root q hq he t h) C) hterminal

end PolygonDrawingBridge
end DirectGLSSW.HOMFLY
