import SupportingBaseArc
import SupportingSmoothingHalfplane
import DirectGLSSW.HOMFLY.BasedTraversal

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.SupportingGeometry

/-- Concrete endpoint coordinates of an old nonincident arc survive smoothing. -/
theorem smoothCrossing_old_arc_endpoints (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : Fin D.nArc)
    (hin : ∀ i, e ≠ D.incoming c i) (hout : ∀ i, e ≠ D.outgoing c i)
    (hs : D.arcSource e ≠ D.crossingVertex c)
    (ht : D.arcTarget e ≠ D.crossingVertex c) :
    (smoothCrossing D c).vertexPoint
        ((smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inl e))) =
      D.vertexPoint (D.arcSource e) ∧
    (smoothCrossing D c).vertexPoint
        ((smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inl e))) =
      D.vertexPoint (D.arcTarget e) := by
  constructor
  · change smoothVertexPoint D c (smoothArcSource D c (smoothArcEquiv D (Sum.inl e))) = _
    simp [smoothVertexPoint, smoothArcSource, smoothArcSourceCode,
      smoothVertexPointGeometryCode, hout, hs]
  · change smoothVertexPoint D c (smoothArcTarget D c (smoothArcEquiv D (Sum.inl e))) = _
    simp [smoothVertexPoint, smoothArcTarget, smoothArcTargetGeometryCode,
      smoothArcTargetCode, smoothVertexPointGeometryCode, hin, ht]

/-- The actual directed supporting arc keeps both endpoint coordinates. -/
theorem smoothCrossing_supporting_arc_endpoints (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (e : Fin D.nArc)
    (hhalf : ∀ v, 0 ≤ planarDet
      (D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e))
      (D.vertexPoint v-D.vertexPoint (D.arcSource e))) :
    (smoothCrossing D c).vertexPoint
        ((smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inl e))) =
      D.vertexPoint (D.arcSource e) ∧
    (smoothCrossing D c).vertexPoint
        ((smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inl e))) =
      D.vertexPoint (D.arcTarget e) := by
  have hu : D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e) ≠ 0 := by
    intro he
    exact D.arc_endpoints_distinct e
      (D.vertexPoint_injective (sub_eq_zero.mp he).symm)
  have he := supporting_arc_endpoints_not_crossing D
    (D.vertexPoint (D.arcSource e))
    (D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e)) hu hhalf e
    (by simp [planarDet]) (by simp [planarDet, mul_comm]) c
  exact smoothCrossing_old_arc_endpoints D c e
    (fun i => (supporting_base_arc_nonincident D e hhalf c i).1)
    (fun i => (supporting_base_arc_nonincident D e hhalf c i).2) he.1 he.2

/-- Equality of the full oriented parametrization includes every midpoint germ. -/
theorem smoothCrossing_supporting_arc_affine (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (e : Fin D.nArc)
    (hhalf : ∀ v, 0 ≤ planarDet
      (D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e))
      (D.vertexPoint v-D.vertexPoint (D.arcSource e))) (t : ℝ) :
    DirectGLSSW.affinePoint
      ((smoothCrossing D c).vertexPoint
        ((smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inl e))))
      ((smoothCrossing D c).vertexPoint
        ((smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inl e)))) t =
    DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e)) t := by
  obtain ⟨hs, ht⟩ := smoothCrossing_supporting_arc_endpoints D c e hhalf
  rw [hs, ht]

/-- The oriented edge vector is unchanged, so its direction is unchanged. -/
theorem smoothCrossing_supporting_arc_vector (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (e : Fin D.nArc)
    (hhalf : ∀ v, 0 ≤ planarDet
      (D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e))
      (D.vertexPoint v-D.vertexPoint (D.arcSource e))) :
    (smoothCrossing D c).vertexPoint
      ((smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inl e))) -
    (smoothCrossing D c).vertexPoint
      ((smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inl e))) =
    D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e) := by
  obtain ⟨hs, ht⟩ := smoothCrossing_supporting_arc_endpoints D c e hhalf
  rw [hs, ht]

end DirectGLSSW.HOMFLY.SupportingGeometry




