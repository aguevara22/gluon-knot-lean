import PLArcSubdivisionAvoidance
import PLArcSubdivisionTangents
import PLArcSubdivisionIncidenceCompletion

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
variable (D : PLLinkDiagram) (e : Fin D.nArc) (t : ℝ) (ht0 : 0<t) (ht1 : t<1)

/-- Insert the actual interior point of a selected physical arc. Incoming ports
use the second half and outgoing ports the first half, including selected ports. -/
def subdivideArc : PLLinkDiagram where
  nVertex := D.nVertex+1
  nArc := D.nArc+1
  nCrossing := D.nCrossing
  vertexPoint := vertexPoint D e t
  arcSource := arcSource D
  arcTarget := arcTarget D e
  crossingVertex := crossingVertex D
  crossingVertex_injective := crossingVertex_injective D
  incoming := incoming D e
  outgoing := outgoing D
  incoming_target := incoming_target D e
  outgoing_source := outgoing_source D
  four_ports_distinct := four_ports_distinct D e
  crossing_incidence_complete := crossing_incidence_complete D e
  regular_degree_one := regular_degree_one D e
  through := D.through
  continuation := continuation D e
  continuation_incidence := continuation_incidence D e
  continuation_crossing := continuation_crossing D e
  overBranch := D.overBranch
  vertexPoint_injective := vertexPoint_injective D e t ht0 ht1
  arc_endpoints_distinct := arc_endpoints_distinct D e
  arc_interiors_disjoint := arc_interiors_disjoint D e t ht0 ht1
  vertices_avoid_arc_interiors := vertices_avoid_arc_interiors D e t ht0 ht1
  through_tangents_positive_collinear := through_tangents_positive_collinear D e t ht0 ht1
  crossing_transverse := crossing_transverse D e t ht1

@[simp] theorem subdivideArc_nVertex : (subdivideArc D e t ht0 ht1).nVertex=D.nVertex+1 := rfl
@[simp] theorem subdivideArc_nArc : (subdivideArc D e t ht0 ht1).nArc=D.nArc+1 := rfl
@[simp] theorem subdivideArc_nCrossing : (subdivideArc D e t ht0 ht1).nCrossing=D.nCrossing := rfl

theorem subdivideArc_crossingDet (c : Fin D.nCrossing) :
    crossingDet (subdivideArc D e t ht0 ht1) c =
      (incomingScale D e t c (D.overBranch c)*incomingScale D e t c (otherBranch (D.overBranch c)))*crossingDet D c :=
  incoming_det D e t c (D.overBranch c) (otherBranch (D.overBranch c))

/-- Crossing signs are preserved because both incoming tangent scales are positive. -/
theorem subdivideArc_crossingSign (c : Fin D.nCrossing) :
    crossingSign (subdivideArc D e t ht0 ht1) c = crossingSign D c := by
  have hp := mul_pos (incomingScale_pos D e t ht1 c (D.overBranch c))
    (incomingScale_pos D e t ht1 c (otherBranch (D.overBranch c)))
  have hn :
      (incomingScale D e t c (D.overBranch c)*incomingScale D e t c (otherBranch (D.overBranch c)))*crossingDet D c < 0 ↔
      crossingDet D c < 0 := by
    simpa only [mul_zero] using (mul_lt_mul_left hp (b:=crossingDet D c) (c:=0))
  simp only [crossingSign,nonzeroScalarSign,subdivideArc_crossingDet,hn]
end DirectGLSSW.HOMFLY.ArcSubdivision
