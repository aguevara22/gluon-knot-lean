import HOMFLYRegularVertexComponent
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY

/-- A regular old vertex remains a regular vertex after an actual smoothing. -/
theorem smooth_old_regular_vertex (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (v : Fin D.nVertex) (hv : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ v) :
    ∀ d : Fin (smoothCrossing D c).nCrossing,
      (smoothCrossing D c).crossingVertex d ≠ smoothVertexEquiv D c (Sum.inl v) := by
  intro d h
  exact hv ((smoothCrossingEquiv D c).symm d).val
    (Sum.inl.inj ((smoothVertexEquiv D c).injective h))

/-- Smoothing does not move an old arc's regular source endpoint. -/
theorem smooth_old_arc_regular_source (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : Fin D.nArc) (hv : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ D.arcSource e) :
    (smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inl e)) =
      smoothVertexEquiv D c (Sum.inl (D.arcSource e)) := by
  have he (i : Fin 2) : e ≠ D.outgoing c i := by
    intro h
    subst e
    exact hv c (D.outgoing_source c i).symm
  change smoothVertexEquiv D c
    (smoothArcSourceCode D c ((smoothArcEquiv D).symm (smoothArcEquiv D (Sum.inl e)))) = _
  simp only [Equiv.symm_apply_apply, smoothArcSourceCode, if_neg (he 0), if_neg (he 1)]

/-- Smoothing does not move an old arc's regular target endpoint. -/
theorem smooth_old_arc_regular_target (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : Fin D.nArc) (hv : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ D.arcTarget e) :
    (smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inl e)) =
      smoothVertexEquiv D c (Sum.inl (D.arcTarget e)) := by
  have he (i : Fin 2) : e ≠ D.incoming c i := by
    intro h
    subst e
    exact hv c (D.incoming_target c i).symm
  change smoothVertexEquiv D c
    (smoothArcTargetGeometryCode D c ((smoothArcEquiv D).symm (smoothArcEquiv D (Sum.inl e)))) = _
  simp only [Equiv.symm_apply_apply, smoothArcTargetGeometryCode, smoothArcTargetCode,
    if_neg (he 0), if_neg (he 1)]

/-- Literal component extraction cannot turn a regular ambient vertex into a crossing. -/
theorem LowestRowContract.ComponentRestriction.regular_vertex
    {D : PLLinkDiagram} {C : diagramComponent D}
    (R : LowestRowContract.ComponentRestriction D C) (v : Fin R.diagram.nVertex)
    (hv : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ (R.vertexEquiv v).val) :
    ∀ d : Fin R.diagram.nCrossing, R.diagram.crossingVertex d ≠ v := by
  intro d h
  have hm := congrArg (fun w => (R.vertexEquiv w).val) h
  dsimp only at hm
  rw [R.crossingVertex_eq] at hm
  exact hv (R.crossingEquiv d).val hm

/-- Both regular endpoints of an old marked arc remain regular after smoothing. -/
theorem smooth_old_arc_regular_endpoints (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : Fin D.nArc)
    (hs : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ D.arcSource e)
    (ht : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ D.arcTarget e) :
    (∀ d : Fin (smoothCrossing D c).nCrossing, (smoothCrossing D c).crossingVertex d ≠
      (smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inl e))) ∧
    (∀ d : Fin (smoothCrossing D c).nCrossing, (smoothCrossing D c).crossingVertex d ≠
      (smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inl e))) := by
  rw [smooth_old_arc_regular_source D c e hs, smooth_old_arc_regular_target D c e ht]
  exact ⟨smooth_old_regular_vertex D c _ hs, smooth_old_regular_vertex D c _ ht⟩

end DirectGLSSW.HOMFLY
