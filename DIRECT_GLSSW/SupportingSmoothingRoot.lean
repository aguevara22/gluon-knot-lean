import SupportingSmoothingArc

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.SupportingGeometry

/-- An actual arc may be selected as the base of its actual component. -/
theorem exists_basedTraversal_rooted_at (D : PLLinkDiagram) (e : Fin D.nArc) :
    ∃ T : BasedTraversal D,
      (T.baseArc (PermutationOrbits.componentOf D.continuation e)).val = e := by
  classical
  let T0 := chooseBasedTraversal D
  let T : BasedTraversal D := {
    componentIndex := T0.componentIndex
    baseArc := fun C => if h : PermutationOrbits.componentOf D.continuation e = C
      then ⟨e, h⟩ else T0.baseArc C }
  refine ⟨T, ?_⟩
  simp [T]

/-- The old supporting arc supports every vertex of the actual smoothing,
with its original orientation and both actual endpoints. -/
theorem smoothCrossing_supporting_arc_halfplane (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (e : Fin D.nArc)
    (hhalf : ∀ v, 0 ≤ planarDet
      (D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e))
      (D.vertexPoint v-D.vertexPoint (D.arcSource e))) :
    ∀ v, 0 ≤ planarDet
      ((smoothCrossing D c).vertexPoint
        ((smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inl e))) -
       (smoothCrossing D c).vertexPoint
        ((smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inl e))))
      ((smoothCrossing D c).vertexPoint v -
       (smoothCrossing D c).vertexPoint
        ((smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inl e)))) := by
  obtain ⟨hs, ht⟩ := smoothCrossing_supporting_arc_endpoints D c e hhalf
  rw [hs, ht]
  exact smoothCrossing_vertices_halfplane D c _ _ hhalf

/-- Actual midpoint equality is an instance of the unchanged oriented edge. -/
theorem smoothCrossing_supporting_arc_midpoint (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (e : Fin D.nArc)
    (hhalf : ∀ v, 0 ≤ planarDet
      (D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e))
      (D.vertexPoint v-D.vertexPoint (D.arcSource e))) :
    DirectGLSSW.affinePoint
      ((smoothCrossing D c).vertexPoint
        ((smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inl e))))
      ((smoothCrossing D c).vertexPoint
        ((smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inl e)))) (1/2 : ℝ) =
    DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e)) (1/2 : ℝ) :=
  smoothCrossing_supporting_arc_affine D c e hhalf (1/2)

/-- The retained original root arc can be the actual base of its smoothed
component. This does not identify the old and new component sets. -/
theorem smoothCrossing_has_retained_root_traversal (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (T : BasedTraversal D) (C : diagramComponent D) :
    ∃ T' : BasedTraversal (smoothCrossing D c),
      (T'.baseArc (PermutationOrbits.componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inl (T.baseArc C).val)))).val =
      smoothArcEquiv D (Sum.inl (T.baseArc C).val) :=
  exists_basedTraversal_rooted_at (smoothCrossing D c)
    (smoothArcEquiv D (Sum.inl (T.baseArc C).val))

end DirectGLSSW.HOMFLY.SupportingGeometry




