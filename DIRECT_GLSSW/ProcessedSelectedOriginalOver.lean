import ProcessedCrossingDataTrace
import ProcessedSharpCrossingComparison
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract SmoothingCornerGeometry

/-- A current bad crossing has no processed incoming port, so its literal
over branch still equals the original one. -/
theorem MarkedParentTrace.bad_crossing_original_over {s t : MarkedParentState}
    (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) :
    t.1.overBranch c=s.1.overBranch (h.crossingOrigin c) := by
  rcases h.crossingOrigin_over_or_marked c with hh | ⟨i,hi⟩
  · exact hh
  · have hb := t.2.2.beforeBad _ hi c hc
    by_cases he : i=firstVisitedBranch t.2.1 c
    · subst i;exact (rankBefore_asymm hb hb).elim
    · have hi' : i=otherBranch (firstVisitedBranch t.2.1 c) := by
        by_contra hn
        exact (neq_otherBranch_iff _ _).mp hn he
      rw [hi'] at hb
      exact (rankBefore_asymm (firstVisitedBranch_is_first t.2.1 c) hb).elim

/-- The sharp over-to-under crossing corner is strictly left-turning. -/
theorem positive_crossing_exchange_left (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (b : Fin 2) (hb : b≠D.overBranch c) (hp : crossingSign D c=Sign.pos) :
    0<planarDet (arcVector D (D.incoming c (otherBranch b)))
      (arcVector D (D.outgoing c (D.through c b))) := by
  have hbranch : otherBranch b=D.overBranch c := by
    by_contra hn
    exact (neq_otherBranch_iff _ _).mp (Ne.symm hn) (Ne.symm hb)
  have hpos : 0<crossingDet D c := by
    apply (nonzeroScalarSign_value_pos_iff (crossingDet D c) (selectedDet_ne_zero D c)).mp
    change (crossingSign D c).value=1
    rw [hp];rfl
  have hi : arcVector D (D.incoming c (otherBranch b))=strandTangent D c (otherBranch b) := by
    simp only [arcVector,D.incoming_target,strandTangent]
  have ho : strandTangent D c b=outgoingTangentScale D c b • arcVector D (D.outgoing c (D.through c b)) := by
    simpa only [arcVector,D.outgoing_source] using outgoingTangentScale_spec D c b
  have he : crossingDet D c = outgoingTangentScale D c b *
      planarDet (arcVector D (D.incoming c (otherBranch b)))
        (arcVector D (D.outgoing c (D.through c b))) := by
    rw [crossingDet,←hbranch,otherBranch_involutive,ho,hi]
    simp [planarDet];ring
  rw [he] at hpos
  exact (mul_pos_iff_of_pos_left (outgoingTangentScale_pos D c b)).mp hpos
end DirectGLSSW.HOMFLY
