import CanonicalRecursiveChild
import HOMFLYParentRootTraversal
import ProcessedRootExposure
import SupportingSmoothingRoot
import UniformLeftHistoryChildTurns

set_option autoImplicit false

noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild

open PermutationOrbits LowestRowContract SupportingGeometry PolygonDrawingBridge
  SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

/-- Every arc of the literal canonical detached child differs from the
smoothed actual traversal root. This includes the fresh connector: the proof
uses component membership, not historical arc labels. -/
theorem canonical_detached_current_arc_excluded
    (t : MarkedParentState) (c : Fin t.1.nCrossing) :
    ∀ e : Fin (canonicalDetachedRestriction t c).diagram.nArc,
      ((canonicalDetachedRestriction t c).arcEquiv e).val ≠
        smoothArcEquiv t.1 (Sum.inl
          (t.2.1.baseArc
            (componentOf t.1.continuation
              (t.1.incoming c (firstVisitedBranch t.2.1 c)))).val) := by
  intro e he
  let i := firstVisitedBranch t.2.1 c
  let C := componentOf t.1.continuation (t.1.incoming c i)
  let r := (t.2.1.baseArc C).val
  let S := smoothCrossing t.1 c
  let R := canonicalDetachedRestriction t c
  have hroot : componentOf S.continuation (smoothArcEquiv t.1 (Sum.inl r)) =
      rootSelfCutComponents t.1 c (t.2.2.connected _ _) i (Sum.inl false) := by
    dsimp [S, r, C, i]
    exact firstVisited_original_root_component t.1 t.2.1 c (t.2.2.connected _ _)
  have hchild : componentOf S.continuation (R.arcEquiv e).val =
      rootSelfCutComponents t.1 c (t.2.2.connected _ _) i (Sum.inl true) :=
    (R.arcEquiv e).property
  have hneq : rootSelfCutComponents t.1 c (t.2.2.connected _ _) i (Sum.inl false) ≠
      rootSelfCutComponents t.1 c (t.2.2.connected _ _) i (Sum.inl true) := by
    intro h
    have h' := (rootSelfCutComponents t.1 c (t.2.2.connected _ _) i).injective h
    cases h'
  apply hneq
  calc
    rootSelfCutComponents t.1 c (t.2.2.connected _ _) i (Sum.inl false) =
        componentOf S.continuation (smoothArcEquiv t.1 (Sum.inl r)) := hroot.symm
    _ = componentOf S.continuation (R.arcEquiv e).val :=
      congrArg (componentOf S.continuation) he.symm
    _ = rootSelfCutComponents t.1 c (t.2.2.connected _ _) i (Sum.inl true) := hchild

/-- The literal closed straight segment of every detached-child arc misses an
interior point of the actual supported root. -/
theorem canonical_detached_closed_segments_avoid_supported_root
    (t : MarkedParentState) (c : Fin t.1.nCrossing)
    (p q : PlanarPoint ℝ) (hroot : SupportingRootGeometry t p q)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∀ e : Fin (canonicalDetachedRestriction t c).diagram.nArc,
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        affinePoint p q τ ≠
          affinePoint
            ((canonicalDetachedRestriction t c).diagram.vertexPoint
              ((canonicalDetachedRestriction t c).diagram.arcSource e))
            ((canonicalDetachedRestriction t c).diagram.vertexPoint
              ((canonicalDetachedRestriction t c).diagram.arcTarget e)) u := by
  let i := firstVisitedBranch t.2.1 c
  let C := componentOf t.1.continuation (t.1.incoming c i)
  let r := (t.2.1.baseArc C).val
  let S := smoothCrossing t.1 c
  let R := canonicalDetachedRestriction t c
  have hhalf : ∀ v, 0 ≤ planarDet
      (t.1.vertexPoint (t.1.arcTarget r) - t.1.vertexPoint (t.1.arcSource r))
      (t.1.vertexPoint v - t.1.vertexPoint (t.1.arcSource r)) := by
    intro v
    rw [(hroot.1 C).2, (hroot.1 C).1]
    exact hroot.2 v
  have hroot_point :
      affinePoint (S.vertexPoint (S.arcSource (smoothArcEquiv t.1 (Sum.inl r))))
        (S.vertexPoint (S.arcTarget (smoothArcEquiv t.1 (Sum.inl r)))) τ =
      affinePoint p q τ := by
    calc
      _ = affinePoint (t.1.vertexPoint (t.1.arcSource r))
          (t.1.vertexPoint (t.1.arcTarget r)) τ :=
        smoothCrossing_supporting_arc_affine t.1 c r hhalf τ
      _ = affinePoint p q τ := by rw [(hroot.1 C).1, (hroot.1 C).2]
  intro e u hu
  have hchild_ne :
      affinePoint (R.diagram.vertexPoint (R.diagram.arcSource e))
        (R.diagram.vertexPoint (R.diagram.arcTarget e)) u ≠
      affinePoint p q τ := by
    have hseg :
      affinePoint (R.diagram.vertexPoint (R.diagram.arcSource e))
        (R.diagram.vertexPoint (R.diagram.arcTarget e)) u =
      affinePoint (S.vertexPoint (S.arcSource (R.arcEquiv e).val))
        (S.vertexPoint (S.arcTarget (R.arcEquiv e).val)) u := by
      simp only [R.vertexPoint_eq, R.source_eq, R.target_eq]
      rfl
    have hne : (R.arcEquiv e).val ≠ smoothArcEquiv t.1 (Sum.inl r) := by
      intro he
      exact canonical_detached_current_arc_excluded t c e (by
        simpa [r, C, i] using he)
    rw [hseg, ← hroot_point]
    by_cases hu0 : u = 0
    · rw [hu0, affinePoint_zero]
      exact S.vertices_avoid_arc_interiors (S.arcSource (R.arcEquiv e).val)
        (smoothArcEquiv t.1 (Sum.inl r)) τ hτ0 hτ1
    · by_cases hu1 : u = 1
      · rw [hu1, affinePoint_one]
        exact S.vertices_avoid_arc_interiors (S.arcTarget (R.arcEquiv e).val)
          (smoothArcEquiv t.1 (Sum.inl r)) τ hτ0 hτ1
      · have hu0' : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
        have hu1' : u < 1 := lt_of_le_of_ne hu.2 hu1
        exact S.arc_interiors_disjoint (R.arcEquiv e).val
          (smoothArcEquiv t.1 (Sum.inl r)) hne u τ hu0' hu1' hτ0 hτ1
  exact Ne.symm hchild_ne

/-- Source-facing specialization: the root support is derived from the actual
initial polygon trace, and the excluded point is its literal affine basepoint. -/
theorem canonical_detached_source_child_segments_avoid_basepoint
    {n : ℕ} (q : Fin (n + 2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace
      (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (he : ExposedOpenPrimitive.LeftExposed q 0)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∀ e : Fin (canonicalDetachedRestriction t c).diagram.nArc,
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        affinePoint
          ((positivePolygonEventDiagram q hq).vertexPoint
            ((positivePolygonEventDiagram q hq).arcSource
              (eventFin q (initialAnchor q hq))))
          ((positivePolygonEventDiagram q hq).vertexPoint
            ((positivePolygonEventDiagram q hq).arcTarget
              (eventFin q (initialAnchor q hq)))) τ ≠
        affinePoint
          ((canonicalDetachedRestriction t c).diagram.vertexPoint
            ((canonicalDetachedRestriction t c).diagram.arcSource e))
          ((canonicalDetachedRestriction t c).diagram.vertexPoint
            ((canonicalDetachedRestriction t c).diagram.arcTarget e)) u := by
  let p := (positivePolygonEventDiagram q hq).vertexPoint
    ((positivePolygonEventDiagram q hq).arcSource (eventFin q (initialAnchor q hq)))
  let q0 := (positivePolygonEventDiagram q hq).vertexPoint
    ((positivePolygonEventDiagram q hq).arcTarget (eventFin q (initialAnchor q hq)))
  have hroot : SupportingRootGeometry t p q0 :=
    actual_parent_original_supporting_root q hq h he
  simpa [p, q0] using
    canonical_detached_closed_segments_avoid_supported_root t c p q0 hroot τ hτ0 hτ1

end DirectGLSSW.HOMFLY.ProcessedExposedChild
end




