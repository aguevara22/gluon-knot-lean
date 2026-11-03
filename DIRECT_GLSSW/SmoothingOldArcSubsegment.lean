import ProcessedArcOriginTrace
import SmoothingCornerVectors
import DirectGLSSW.HOMFLY.HOMFYSmoothingCutpointInteriors
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

/-- Both actual endpoints of a surviving old arc lie in order on its old segment. -/
theorem smooth_old_arc_subsegment (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : Fin D.nArc) :
    ∃ u v : ℝ, 0 ≤ u ∧ u < v ∧ v ≤ 1 ∧
      (smoothCrossing D c).vertexPoint
        ((smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inl e))) =
        affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) u ∧
      (smoothCrossing D c).vertexPoint
        ((smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inl e))) =
        affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) v := by
  have hεr := lt_of_lt_of_le (smoothEpsilon_lt_radius D c) (smoothRadius_le_cutoff D c)
  by_cases hin : ∃ i : Fin 2, e = D.incoming c i
  · obtain ⟨i,rfl⟩ := hin
    have hsrc : D.arcSource (D.incoming c i) ≠ D.crossingVertex c := by
      intro h
      exact D.arc_endpoints_distinct _ (h.trans (D.incoming_target c i).symm)
    have hp : (smoothCrossing D c).vertexPoint
        ((smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inl (D.incoming c i)))) =
        D.vertexPoint (D.arcSource (D.incoming c i)) := by
      change smoothVertexPointGeometryCode D c (smoothEpsilon D c)
        ((smoothVertexEquiv D c).symm (smoothVertexEquiv D c
          (smoothArcSourceCode D c ((smoothArcEquiv D).symm (smoothArcEquiv D (Sum.inl (D.incoming c i))))))) = _
      simp only [Equiv.symm_apply_apply,smoothArcSourceCode,
        if_neg ((D.four_ports_distinct c).2.2 i 0),if_neg ((D.four_ports_distinct c).2.2 i 1),
        smoothVertexPointGeometryCode,if_neg hsrc]
    have ht : (smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inl (D.incoming c i))) =
        (smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inr i)) := by
      rw [← Gemini.smooth_step_incoming D c i]
      exact (smoothCrossing D c).continuation_incidence _
    obtain ⟨v,hv0,hv1,hv⟩ := smoothIncomingCutPoint_interior D c _ (smoothEpsilon_pos D c) hεr i
    refine ⟨0,v,le_rfl,hv0,hv1.le,?_,?_⟩
    · simpa [affinePoint] using hp
    · rw [ht,(connector_endpoints D c i).1]
      simpa only [D.incoming_target,smoothingCenter] using hv
  · by_cases hout : ∃ i : Fin 2, e = D.outgoing c (D.through c i)
    · obtain ⟨i,rfl⟩ := hout
      have htar : D.arcTarget (D.outgoing c (D.through c i)) ≠ D.crossingVertex c := by
        intro h
        exact D.arc_endpoints_distinct _ ((D.outgoing_source c _).trans h.symm)
      have hp : (smoothCrossing D c).vertexPoint
          ((smoothCrossing D c).arcTarget
            (smoothArcEquiv D (Sum.inl (D.outgoing c (D.through c i))))) =
          D.vertexPoint (D.arcTarget (D.outgoing c (D.through c i))) := by
        change smoothVertexPointGeometryCode D c (smoothEpsilon D c)
          ((smoothVertexEquiv D c).symm (smoothVertexEquiv D c
            (smoothArcTargetGeometryCode D c ((smoothArcEquiv D).symm
              (smoothArcEquiv D (Sum.inl (D.outgoing c (D.through c i)))))))) = _
        simp only [Equiv.symm_apply_apply,smoothArcTargetGeometryCode,smoothArcTargetCode,
          if_neg ((D.four_ports_distinct c).2.2 0 (D.through c i)).symm,
          if_neg ((D.four_ports_distinct c).2.2 1 (D.through c i)).symm,
          smoothVertexPointGeometryCode,if_neg htar]
      have hs : (smoothCrossing D c).arcSource
          (smoothArcEquiv D (Sum.inl (D.outgoing c (D.through c i)))) =
          (smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inr (otherBranch i))) := by
        have h := (smoothCrossing D c).continuation_incidence
          (smoothArcEquiv D (Sum.inr (otherBranch i)))
        rw [Gemini.smooth_step_connector,otherBranch_involutive,D.continuation_crossing] at h
        exact h.symm
      obtain ⟨u,hu0,hu1,hu⟩ := smoothOutgoingCutPoint_interior D c _ (smoothEpsilon_pos D c) hεr i
      refine ⟨u,1,hu0.le,hu1,le_rfl,?_,?_⟩
      · rw [hs,(connector_endpoints D c (otherBranch i)).2,otherBranch_involutive]
        simpa only [D.outgoing_source,smoothingCenter] using hu
      · simpa [affinePoint] using hp
    · have hout' : ¬ ∃ i : Fin 2, e = D.outgoing c i := by
        rintro ⟨i,hi⟩
        apply hout
        exact ⟨(D.through c).symm i,by simpa only [Equiv.apply_symm_apply] using hi⟩
      have hi (i : Fin 2) : e ≠ D.incoming c i := fun h => hin ⟨i,h⟩
      have ho (i : Fin 2) : e ≠ D.outgoing c i := fun h => hout' ⟨i,h⟩
      have hs : D.arcSource e ≠ D.crossingVertex c := by
        intro h
        rcases (D.crossing_incidence_complete c e).mp (Or.inl h) with h|h|h|h
        · exact hi 0 h
        · exact hi 1 h
        · exact ho 0 h
        · exact ho 1 h
      have ht : D.arcTarget e ≠ D.crossingVertex c := by
        intro h
        rcases (D.crossing_incidence_complete c e).mp (Or.inr h) with h|h|h|h
        · exact hi 0 h
        · exact hi 1 h
        · exact ho 0 h
        · exact ho 1 h
      refine ⟨0,1,le_rfl,zero_lt_one,le_rfl,?_,?_⟩
      · change smoothVertexPointGeometryCode D c (smoothEpsilon D c)
          ((smoothVertexEquiv D c).symm (smoothVertexEquiv D c
            (smoothArcSourceCode D c ((smoothArcEquiv D).symm (smoothArcEquiv D (Sum.inl e)))))) = _
        simp [smoothArcSourceCode,ho,smoothVertexPointGeometryCode,hs,affinePoint]
      · change smoothVertexPointGeometryCode D c (smoothEpsilon D c)
          ((smoothVertexEquiv D c).symm (smoothVertexEquiv D c
            (smoothArcTargetGeometryCode D c ((smoothArcEquiv D).symm (smoothArcEquiv D (Sum.inl e)))))) = _
        simp [smoothArcTargetGeometryCode,smoothArcTargetCode,hi,smoothVertexPointGeometryCode,ht,affinePoint]

end DirectGLSSW.HOMFLY.SmoothingCornerGeometry
