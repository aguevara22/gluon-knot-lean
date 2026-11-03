import PhysicalContinuingBadFuture
import ProcessedCrossingDataTrace
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalParentHistory
open PermutationOrbits LowestRowContract ProcessedParentMarks MarkedG
attribute [local instance] Classical.propDecidable
variable {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) (hgood : GoodBefore t c)

/-- All matched future incoming arcs are outside the produced processed prefix. -/
theorem continuingFutureCrossing_incoming_not_marked
    (d : StrictFutureCrossing (continuingState t c hc hgood) (connector t c)) (i : Fin 2) :
    (continuingState t c hc hgood).1.incoming d.val i ∉
      (continuingState t c hc hgood).2.2.marks := by
  obtain ⟨k,hk⟩ := (tailArc_range c hc hgood _).mpr (d.property i)
  rw [←hk]
  exact tailArc_not_marked c hc hgood k

/-- Through/over/sign and physical crossing points in the complete continuing
future are inherited from the original diagram, despite all processed switches. -/
theorem continuingFutureCrossing_data
    (d : StrictFutureCrossing (continuingState t c hc hgood) (connector t c)) :
    (continuingState t c hc hgood).1.through d.val =
      s.1.through ((continuingTrace h c hc hgood).crossingOrigin d.val) ∧
    (continuingState t c hc hgood).1.overBranch d.val =
      s.1.overBranch ((continuingTrace h c hc hgood).crossingOrigin d.val) ∧
    crossingSign (continuingState t c hc hgood).1 d.val =
      crossingSign s.1 ((continuingTrace h c hc hgood).crossingOrigin d.val) ∧
    (continuingState t c hc hgood).1.vertexPoint
      ((continuingState t c hc hgood).1.crossingVertex d.val) =
      s.1.vertexPoint (s.1.crossingVertex ((continuingTrace h c hc hgood).crossingOrigin d.val)) := by
  refine ⟨(continuingTrace h c hc hgood).crossingOrigin_through d.val,?_,?_,
    (continuingTrace h c hc hgood).crossingOrigin_point d.val⟩
  · rcases (continuingTrace h c hc hgood).crossingOrigin_over_or_marked d.val with he|⟨i,hi⟩
    · exact he
    · exact (continuingFutureCrossing_incoming_not_marked c hc hgood d i hi).elim
  · rcases (continuingTrace h c hc hgood).crossingOrigin_sign_or_marked d.val with he|⟨i,hi⟩
    · exact he
    · exact (continuingFutureCrossing_incoming_not_marked c hc hgood d i hi).elim
end DirectGLSSW.HOMFLY.PhysicalParentHistory
