import ProcessedRootExposure
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract

theorem actual_initial_history_supporting_root
    (D : PLLinkDiagram) (T : BasedTraversal D)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (C0 : diagramComponent D)
    (hhalf : ∀ v, 0 ≤ planarDet
      (D.vertexPoint (D.arcTarget (T.baseArc C0).val)-D.vertexPoint (D.arcSource (T.baseArc C0).val))
      (D.vertexPoint v-D.vertexPoint (D.arcSource (T.baseArc C0).val)))
    (t : MarkedParentState)
    (h : MarkedParentTrace ⟨D,T,ProcessedParentMarks.initial D T hconn⟩ t) :
    ∀ C : diagramComponent t.1,
      (∀ θ : ℝ,
        affinePoint (t.1.vertexPoint (t.1.arcSource (t.2.1.baseArc C).val))
          (t.1.vertexPoint (t.1.arcTarget (t.2.1.baseArc C).val)) θ =
        affinePoint (D.vertexPoint (D.arcSource (T.baseArc C0).val))
          (D.vertexPoint (D.arcTarget (T.baseArc C0).val)) θ) ∧
      (∀ v, 0 ≤ planarDet
        (t.1.vertexPoint (t.1.arcTarget (t.2.1.baseArc C).val)-
          t.1.vertexPoint (t.1.arcSource (t.2.1.baseArc C).val))
        (t.1.vertexPoint v-t.1.vertexPoint (t.1.arcSource (t.2.1.baseArc C).val))) := by
  have hg := h.supportingRootGeometry _ _ (initial_supportingRootGeometry D T hconn C0 hhalf)
  intro C
  obtain ⟨hs,ht⟩ := hg.1 C
  constructor
  · intro θ
    rw [hs,ht]
  · intro v
    rw [hs,ht]
    exact hg.2 v
end DirectGLSSW.HOMFLY

#check @DirectGLSSW.HOMFLY.SupportingRootGeometry

#check @DirectGLSSW.HOMFLY.MarkedParentStep.supportingRootGeometry

#check @DirectGLSSW.HOMFLY.MarkedParentTrace.supportingRootGeometry

#check @DirectGLSSW.HOMFLY.initial_supportingRootGeometry

#check @DirectGLSSW.HOMFLY.actual_initial_history_supporting_root

