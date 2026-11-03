import SmoothingCornerTurns
import ProcessedBadCrossingPositive
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SmoothingCornerGeometry
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable

/-- Exact component extraction preserves actual arc vectors, including ports
at demoted mixed crossings. -/
theorem restriction_arcVector {D : PLLinkDiagram} {C : Component D.continuation}
    (R : ComponentRestriction D C) (a : Fin R.diagram.nArc) :
    arcVector R.diagram a = arcVector D (R.arcEquiv a).val := by
  simp only [arcVector,R.vertexPoint_eq,R.source_eq,R.target_eq]

/-- Actual continuation and geometry jointly preserve every retained turn. -/
theorem restriction_turnDet {D : PLLinkDiagram} {C : Component D.continuation}
    (R : ComponentRestriction D C) (a : Fin R.diagram.nArc) :
    turnDet R.diagram a = turnDet D (R.arcEquiv a).val := by
  simp only [turnDet,restriction_arcVector,R.continuation_eq]

/-- After an arbitrary actual processed history from a positive initial diagram,
the new detached child has two actual consecutive left corners at its new
connector. All memberships, arc identifications and signs are produced. -/
theorem actual_child_connector_left_turns
    (D : PLLinkDiagram) (T : BasedTraversal D)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (hpos : ∀ d : Fin D.nCrossing, crossingSign D d = Sign.pos)
    (t : MarkedParentState)
    (h : MarkedParentTrace ⟨D,T,ProcessedParentMarks.initial D T hconn⟩ t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true))) :
    ∃ a b : Fin R.diagram.nArc,
      (R.arcEquiv a).val = smoothArcEquiv t.1
        (Sum.inl (t.1.incoming c (otherBranch (firstVisitedBranch t.2.1 c)))) ∧
      (R.arcEquiv b).val = smoothArcEquiv t.1
        (Sum.inr (otherBranch (firstVisitedBranch t.2.1 c))) ∧
      R.diagram.continuation a = b ∧
      0 < turnDet R.diagram a ∧ 0 < turnDet R.diagram b := by
  let E := smoothCrossing t.1 c
  let i := otherBranch (firstVisitedBranch t.2.1 c)
  let C := rootSelfCutComponents t.1 c (t.2.2.connected _ _)
    (firstVisitedBranch t.2.1 c) (Sum.inl true)
  have hb : componentOf E.continuation (smoothArcEquiv t.1 (Sum.inr i)) = C :=
    (rootSelfCutComponents_true t.1 c (t.2.2.connected _ _) (firstVisitedBranch t.2.1 c)).symm
  have ha : componentOf E.continuation (smoothArcEquiv t.1 (Sum.inl (t.1.incoming c i))) = C := by
    rw [← componentOf_apply E.continuation (smoothArcEquiv t.1 (Sum.inl (t.1.incoming c i)))]
    change componentOf E.continuation ((smoothCrossing t.1 c).continuation _) = C
    rw [Gemini.smooth_step_incoming]
    exact hb
  let a : Fin R.diagram.nArc := R.arcEquiv.symm ⟨_,ha⟩
  let b : Fin R.diagram.nArc := R.arcEquiv.symm ⟨_,hb⟩
  have hma : (R.arcEquiv a).val = smoothArcEquiv t.1 (Sum.inl (t.1.incoming c i)) := by
    simp only [a,Equiv.apply_symm_apply]
  have hmb : (R.arcEquiv b).val = smoothArcEquiv t.1 (Sum.inr i) := by
    simp only [b,Equiv.apply_symm_apply]
  have hstep : R.diagram.continuation a = b := by
    apply R.arcEquiv.injective
    apply Subtype.ext
    rw [R.continuation_eq,hma,hmb]
    exact Gemini.smooth_step_incoming t.1 c i
  have hp := h.bad_crossing_positive_of_initial D T hconn hpos t c hc
  have hturn := (first_under_connector_turns t.1 t.2.1 c hc hp).1
  refine ⟨a,b,hma,hmb,hstep,?_,?_⟩
  · rw [restriction_turnDet,hma]
    exact hturn.1
  · rw [restriction_turnDet,hmb]
    exact hturn.2

end DirectGLSSW.HOMFLY.SmoothingCornerGeometry
