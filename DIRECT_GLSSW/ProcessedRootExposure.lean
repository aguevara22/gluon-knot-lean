import ProcessedParentHistory
import SupportingSmoothingRoot
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract SupportingGeometry

/-- Literal oriented root endpoints and the supporting half-plane of an actual state. -/
def SupportingRootGeometry (s : MarkedParentState) (p q : PlanarPoint ℝ) : Prop :=
  (∀ C : diagramComponent s.1,
    s.1.vertexPoint (s.1.arcSource (s.2.1.baseArc C).val) = p ∧
    s.1.vertexPoint (s.1.arcTarget (s.2.1.baseArc C).val) = q) ∧
  (∀ v, 0 ≤ planarDet (q-p) (s.1.vertexPoint v-p))

theorem MarkedParentStep.supportingRootGeometry {s t : MarkedParentState}
    (h : MarkedParentStep s t) (p q : PlanarPoint ℝ)
    (hs : SupportingRootGeometry s p q) : SupportingRootGeometry t p q := by
  cases h with
  | @switched D T S c hc hgood => exact hs
  | @smoothed D T S c hc hgood R =>
    let C0 := componentOf D.continuation (D.incoming c (firstVisitedBranch T c))
    let r := (T.baseArc C0).val
    have hhalf : ∀ v, 0 ≤ planarDet
        (D.vertexPoint (D.arcTarget r)-D.vertexPoint (D.arcSource r))
        (D.vertexPoint v-D.vertexPoint (D.arcSource r)) := by
      intro v
      dsimp only [r]
      rw [(hs.1 C0).1,(hs.1 C0).2]
      exact hs.2 v
    have he := smoothCrossing_supporting_arc_endpoints D c r hhalf
    constructor
    · intro C
      constructor
      · change R.diagram.vertexPoint (R.diagram.arcSource
          ((R.basedTraversal (parentRootSelfSmoothingTraversal D T c (S.connected _ _))).baseArc C).val) = p
        rw [R.basedTraversal_baseArc, R.vertexPoint_eq, R.source_eq,
          R.parentRestriction_original_root D T c (S.connected _ _)]
        exact he.1.trans (hs.1 C0).1
      · change R.diagram.vertexPoint (R.diagram.arcTarget
          ((R.basedTraversal (parentRootSelfSmoothingTraversal D T c (S.connected _ _))).baseArc C).val) = q
        rw [R.basedTraversal_baseArc, R.vertexPoint_eq, R.target_eq,
          R.parentRestriction_original_root D T c (S.connected _ _)]
        exact he.2.trans (hs.1 C0).2
    · intro v
      change 0 ≤ planarDet (q-p) (R.diagram.vertexPoint v-p)
      rw [R.vertexPoint_eq]
      exact smoothCrossing_vertices_halfplane D c p (q-p) hs.2 _

theorem MarkedParentTrace.supportingRootGeometry {s t : MarkedParentState}
    (h : MarkedParentTrace s t) (p q : PlanarPoint ℝ)
    (hs : SupportingRootGeometry s p q) : SupportingRootGeometry t p q := by
  induction h with
  | nil s => exact hs
  | cons step tail ih => exact ih (step.supportingRootGeometry p q hs)

theorem initial_supportingRootGeometry
    (D : PLLinkDiagram) (T : BasedTraversal D)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (C0 : diagramComponent D)
    (hhalf : ∀ v, 0 ≤ planarDet
      (D.vertexPoint (D.arcTarget (T.baseArc C0).val)-D.vertexPoint (D.arcSource (T.baseArc C0).val))
      (D.vertexPoint v-D.vertexPoint (D.arcSource (T.baseArc C0).val))) :
    SupportingRootGeometry ⟨D,T,ProcessedParentMarks.initial D T hconn⟩
      (D.vertexPoint (D.arcSource (T.baseArc C0).val))
      (D.vertexPoint (D.arcTarget (T.baseArc C0).val)) := by
  refine ⟨?_,hhalf⟩
  intro C
  have he : C = C0 := by
    calc
      C = componentOf D.continuation (T.baseArc C).val := (T.baseArc C).property.symm
      _ = componentOf D.continuation (T.baseArc C0).val :=
        (componentOf_eq_iff _ _ _).2 (hconn _ _)
      _ = C0 := (T.baseArc C0).property
  subst C
  exact ⟨rfl,rfl⟩
end DirectGLSSW.HOMFLY
