import ProcessedParentHistory
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

/-- Literal directed tangent of an actual diagram arc. -/
def arcVector (D : PLLinkDiagram) (e : Fin D.nArc) : PlanarPoint ℝ :=
  D.vertexPoint (D.arcTarget e) - D.vertexPoint (D.arcSource e)

/-- Actual connector endpoints are the selected incoming and opposite outgoing cutpoints. -/
theorem connector_endpoints (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    (smoothCrossing D c).vertexPoint
      ((smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inr i))) =
        incomingCutPoint D c (smoothEpsilon D c) i ∧
    (smoothCrossing D c).vertexPoint
      ((smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inr i))) =
        outgoingCutPoint D c (smoothEpsilon D c) (otherBranch i) := by
  constructor
  · change smoothVertexPointGeometryCode D c (smoothEpsilon D c)
      ((smoothVertexEquiv D c).symm (smoothVertexEquiv D c
        (smoothArcSourceCode D c ((smoothArcEquiv D).symm (smoothArcEquiv D (Sum.inr i)))))) = _
    simp only [Equiv.symm_apply_apply]
    exact smoothArcSourceGeometryCode_connector D c _ i
  · change smoothVertexPointGeometryCode D c (smoothEpsilon D c)
      ((smoothVertexEquiv D c).symm (smoothVertexEquiv D c
        (smoothArcTargetGeometryCode D c ((smoothArcEquiv D).symm (smoothArcEquiv D (Sum.inr i)))))) = _
    simp only [Equiv.symm_apply_apply]
    exact smoothArcTargetGeometryCode_connector D c _ i

theorem connector_vector (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    arcVector (smoothCrossing D c) (smoothArcEquiv D (Sum.inr i)) =
      smoothEpsilon D c • (strandTangent D c i + strandTangent D c (otherBranch i)) := by
  rw [arcVector,(connector_endpoints D c i).1,(connector_endpoints D c i).2]
  ext <;> simp [incomingCutPoint,outgoingCutPoint] <;> ring

/-- The old incoming arc is shortened by the actual positive cutoff factor. -/
theorem incoming_vector (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    arcVector (smoothCrossing D c) (smoothArcEquiv D (Sum.inl (D.incoming c i))) =
      (1-smoothEpsilon D c) • strandTangent D c i := by
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
  rw [arcVector,hp,ht,(connector_endpoints D c i).1]
  ext <;> simp [incomingCutPoint,smoothingCenter,strandTangent] <;> ring

/-- The outgoing arc after the connector is a positive multiple of its old strand. -/
theorem outgoing_vector (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    ∃ b : ℝ, 0 < b ∧
      arcVector (smoothCrossing D c)
        (smoothArcEquiv D (Sum.inl (D.outgoing c (D.through c i)))) = b • strandTangent D c i := by
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
  have hbound := crossingCutoff_parameters D c (smoothEpsilon_pos D c)
    (lt_of_lt_of_le (smoothEpsilon_lt_radius D c) (smoothRadius_le_cutoff D c)) i
  let s := outgoingTangentScale D c i
  have hsp : 0 < s := outgoingTangentScale_pos D c i
  refine ⟨(1-smoothEpsilon D c*s)/s,div_pos (by linarith [hbound.2.2.2.2.1]) hsp,?_⟩
  rw [arcVector,hp,hs,(connector_endpoints D c (otherBranch i)).2,otherBranch_involutive]
  rw [outgoingCutPoint,outgoingTangentScale_spec,smul_smul]
  have hcancel : (1-smoothEpsilon D c*s)/s * outgoingTangentScale D c i =
      1-smoothEpsilon D c*s := by
    change (1-smoothEpsilon D c*s)/s*s = _
    exact div_mul_cancel₀ _ (ne_of_gt hsp)
  rw [smul_smul,hcancel]
  change _ = (1-smoothEpsilon D c*s) • _
  ext <;> simp [s,smul_eq_mul] <;> ring

end DirectGLSSW.HOMFLY.SmoothingCornerGeometry
