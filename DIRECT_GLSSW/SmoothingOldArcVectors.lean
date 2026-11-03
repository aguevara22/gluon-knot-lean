import ProcessedChildConnectorCorners
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

/-- Every old arc retains its direction with a derived strictly positive scale,
including both old incoming and outgoing selected ports. -/
theorem old_arc_vector_positive_multiple (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : Fin D.nArc) :
    ∃ a : ℝ, 0 < a ∧
      arcVector (smoothCrossing D c) (smoothArcEquiv D (Sum.inl e)) = a • arcVector D e := by
  by_cases hin : ∃ i : Fin 2, e = D.incoming c i
  · obtain ⟨i,rfl⟩ := hin
    have hbound := crossingCutoff_parameters D c (smoothEpsilon_pos D c)
      (lt_of_lt_of_le (smoothEpsilon_lt_radius D c) (smoothRadius_le_cutoff D c)) i
    refine ⟨1-smoothEpsilon D c,hbound.1,?_⟩
    rw [incoming_vector]
    simp only [arcVector,D.incoming_target,strandTangent]
  · by_cases hout : ∃ i : Fin 2, e = D.outgoing c i
    · obtain ⟨i,rfl⟩ := hout
      obtain ⟨a,ha,hv⟩ := outgoing_vector D c ((D.through c).symm i)
      simp only [Equiv.apply_symm_apply] at hv
      refine ⟨a*outgoingTangentScale D c ((D.through c).symm i),
        mul_pos ha (outgoingTangentScale_pos D c _),?_⟩
      rw [hv,outgoingTangentScale_spec,smul_smul]
      simp only [Equiv.apply_symm_apply,arcVector,D.outgoing_source,smoothingCenter]
    · have hi (i : Fin 2) : e ≠ D.incoming c i := fun h => hin ⟨i,h⟩
      have ho (i : Fin 2) : e ≠ D.outgoing c i := fun h => hout ⟨i,h⟩
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
      refine ⟨1,by norm_num,?_⟩
      change smoothVertexPointGeometryCode D c (smoothEpsilon D c)
          ((smoothVertexEquiv D c).symm (smoothVertexEquiv D c
            (smoothArcTargetGeometryCode D c ((smoothArcEquiv D).symm (smoothArcEquiv D (Sum.inl e)))))) -
        smoothVertexPointGeometryCode D c (smoothEpsilon D c)
          ((smoothVertexEquiv D c).symm (smoothVertexEquiv D c
            (smoothArcSourceCode D c ((smoothArcEquiv D).symm (smoothArcEquiv D (Sum.inl e)))))) = _
      simp only [Equiv.symm_apply_apply,smoothArcSourceCode,smoothArcTargetGeometryCode,
        smoothArcTargetCode,if_neg (hi 0),if_neg (hi 1),if_neg (ho 0),if_neg (ho 1),
        smoothVertexPointGeometryCode,if_neg hs,if_neg ht,one_smul,arcVector]

end DirectGLSSW.HOMFLY.SmoothingCornerGeometry
