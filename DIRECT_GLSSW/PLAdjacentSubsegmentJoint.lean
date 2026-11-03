import ProcessedChildArcSubsegment
import ProcessedChildOriginalWord
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

/-- Two nondegenerate forward subsegments of adjacent actual arcs can meet only
at the original common vertex. This uses actual drawing disjointness, including
straight continuation joints, with no genericity or noncollinearity premise. -/
theorem adjacent_subsegment_joint (D : PLLinkDiagram) (a b : Fin D.nArc)
    (hab : D.continuation a = b) (P : PlanarPoint ℝ) (v u : ℝ)
    (hv0 : 0 < v) (hv1 : v ≤ 1) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hP : P = affinePoint (D.vertexPoint (D.arcSource a)) (D.vertexPoint (D.arcTarget a)) v)
    (hQ : P = affinePoint (D.vertexPoint (D.arcSource b)) (D.vertexPoint (D.arcTarget b)) u) :
    P = D.vertexPoint (D.arcTarget a) := by
  by_cases hv : v=1
  · simpa [hv,affinePoint] using hP
  by_cases hu : u=0
  · have h := D.continuation_incidence a
    rw [hab] at h
    simpa [hu,affinePoint,← h] using hQ
  have hne : a ≠ b := by
    intro he
    have hi := D.continuation_incidence a
    rw [hab,← he] at hi
    exact D.arc_endpoints_distinct a hi.symm
  exact (D.arc_interiors_disjoint a b hne v u hv0 (lt_of_le_of_ne hv1 hv)
    (lt_of_le_of_ne hu0 (Ne.symm hu)) hu1 (hP.symm.trans hQ)).elim

end DirectGLSSW.HOMFLY
