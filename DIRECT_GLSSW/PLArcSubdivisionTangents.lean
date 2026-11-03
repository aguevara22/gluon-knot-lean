import PLArcSubdivisionGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
attribute [local instance] Classical.propDecidable
variable (D : PLLinkDiagram) (e : Fin D.nArc) (t : ℝ)

def incomingScale (c : Fin D.nCrossing) (i : Fin 2) : ℝ := if D.incoming c i=e then 1-t else 1
def outgoingScale (c : Fin D.nCrossing) (i : Fin 2) : ℝ := if D.outgoing c i=e then t else 1

theorem incomingScale_pos (ht1 : t<1) (c : Fin D.nCrossing) (i : Fin 2) : 0 < incomingScale D e t c i := by
  unfold incomingScale;split_ifs
  · exact sub_pos.mpr ht1
  · exact zero_lt_one

theorem outgoingScale_pos (ht0 : 0<t) (c : Fin D.nCrossing) (i : Fin 2) : 0<outgoingScale D e t c i := by
  unfold outgoingScale;split_ifs
  · exact ht0
  · exact zero_lt_one

theorem incoming_tangent (c : Fin D.nCrossing) (i : Fin 2) :
    vertexPoint D e t (crossingVertex D c) - vertexPoint D e t (arcSource D (incoming D e c i)) =
      incomingScale D e t c i • strandTangent D c i := by
  by_cases h : D.incoming c i=e
  · have hv : D.arcTarget e=D.crossingVertex c := by simpa only [h] using D.incoming_target c i
    simp only [incoming,incomingScale,if_pos h,arcSource_new,crossingVertex,vertexPoint_old,vertexPoint_new]
    simpa only [strandTangent,h,←hv] using second_tangent D e t
  · simp only [incoming,incomingScale,if_neg h,arcSource_old,crossingVertex,vertexPoint_old,one_smul,strandTangent]

theorem outgoing_tangent (c : Fin D.nCrossing) (i : Fin 2) :
    vertexPoint D e t (arcTarget D e (outgoing D c i)) - vertexPoint D e t (crossingVertex D c) =
      outgoingScale D e t c i • (D.vertexPoint (D.arcTarget (D.outgoing c i))-D.vertexPoint (D.crossingVertex c)) := by
  by_cases h : D.outgoing c i=e
  · have hv : D.arcSource e=D.crossingVertex c := by simpa only [h] using D.outgoing_source c i
    simp only [outgoing,outgoingScale,arcTarget_old,if_pos h,crossingVertex,vertexPoint_old,vertexPoint_new]
    simpa only [h,←hv] using first_tangent D e t
  · simp only [outgoing,outgoingScale,arcTarget_old,if_neg h,crossingVertex,vertexPoint_old,one_smul]

theorem through_tangents_positive_collinear (ht0 : 0<t) (ht1 : t<1) (c : Fin D.nCrossing) (i : Fin 2) :
    ∃ scale : ℝ, 0<scale ∧
      vertexPoint D e t (crossingVertex D c)-vertexPoint D e t (arcSource D (incoming D e c i)) =
      scale • (vertexPoint D e t (arcTarget D e (outgoing D c (D.through c i)))-vertexPoint D e t (crossingVertex D c)) := by
  obtain ⟨r,hr,hcol⟩ := D.through_tangents_positive_collinear c i
  change strandTangent D c i = _ at hcol
  have hi:=incomingScale_pos D e t ht1 c i
  have ho:=outgoingScale_pos D e t ht0 c (D.through c i)
  refine ⟨incomingScale D e t c i*r/outgoingScale D e t c (D.through c i),div_pos (mul_pos hi hr) ho,?_⟩
  rw [incoming_tangent,outgoing_tangent,hcol,smul_smul,smul_smul,div_mul_cancel₀ _ (ne_of_gt ho)]

theorem incoming_det (c : Fin D.nCrossing) (i j : Fin 2) :
    planarDet
      (vertexPoint D e t (crossingVertex D c)-vertexPoint D e t (arcSource D (incoming D e c i)))
      (vertexPoint D e t (crossingVertex D c)-vertexPoint D e t (arcSource D (incoming D e c j))) =
      (incomingScale D e t c i*incomingScale D e t c j)*planarDet (strandTangent D c i) (strandTangent D c j) := by
  rw [incoming_tangent,incoming_tangent]
  simp [planarDet]
  ring

theorem crossing_transverse (ht1 : t<1) (c : Fin D.nCrossing) :
    planarDet
      (vertexPoint D e t (crossingVertex D c)-vertexPoint D e t (arcSource D (incoming D e c 0)))
      (vertexPoint D e t (crossingVertex D c)-vertexPoint D e t (arcSource D (incoming D e c 1))) ≠ 0 := by
  rw [incoming_det]
  exact mul_ne_zero (ne_of_gt (mul_pos (incomingScale_pos D e t ht1 c 0) (incomingScale_pos D e t ht1 c 1)))
    (D.crossing_transverse c)

theorem incoming_det_pos_iff (ht1 : t<1) (c : Fin D.nCrossing) (i j : Fin 2) :
    0 < planarDet
      (vertexPoint D e t (crossingVertex D c)-vertexPoint D e t (arcSource D (incoming D e c i)))
      (vertexPoint D e t (crossingVertex D c)-vertexPoint D e t (arcSource D (incoming D e c j))) ↔
      0 < planarDet (strandTangent D c i) (strandTangent D c j) := by
  rw [incoming_det]
  exact mul_pos_iff_of_pos_left (mul_pos (incomingScale_pos D e t ht1 c i) (incomingScale_pos D e t ht1 c j))
end DirectGLSSW.HOMFLY.ArcSubdivision
