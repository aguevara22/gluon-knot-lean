import DetachedArcExclusion
import UniformRoundedClearance
import HOMFLYComponentPLPath

set_option autoImplicit false

noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild

open PolygonDrawingBridge SmoothingCornerGeometry PrincipalTurning

/-- The actual closed PL component of the canonical detached child stays a
uniform positive distance from the initial polygon's interior root point. The
carrier is the literal concatenation of the child's diagram arcs. -/
theorem canonical_detached_source_child_pl_clearance
    {n : ℕ} (q : Fin (n + 2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace
      (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (he : ExposedOpenPrimitive.LeftExposed q 0)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ e : Fin (canonicalDetachedRestriction t c).diagram.nArc,
        ∀ u : unitInterval,
          ρ ≤ dist
            (componentPLLoop (canonicalDetachedRestriction t c).diagram e u)
            (affinePoint
              ((positivePolygonEventDiagram q hq).vertexPoint
                ((positivePolygonEventDiagram q hq).arcSource
                  (eventFin q (initialAnchor q hq))))
              ((positivePolygonEventDiagram q hq).vertexPoint
                ((positivePolygonEventDiagram q hq).arcTarget
                  (eventFin q (initialAnchor q hq)))) τ) := by
  let R := canonicalDetachedRestriction t c
  let p := (positivePolygonEventDiagram q hq).vertexPoint
    ((positivePolygonEventDiagram q hq).arcSource (eventFin q (initialAnchor q hq)))
  let q0 := (positivePolygonEventDiagram q hq).vertexPoint
    ((positivePolygonEventDiagram q hq).arcTarget (eventFin q (initialAnchor q hq)))
  let b := affinePoint p q0 τ
  have hb : ∀ e : Fin R.diagram.nArc, ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 →
      b ≠ affinePoint (R.diagram.vertexPoint (R.diagram.arcSource e))
        (R.diagram.vertexPoint (R.diagram.arcTarget e)) u := by
    intro e u hu
    exact canonical_detached_source_child_segments_avoid_basepoint
      q hq h c he τ hτ0 hτ1 e u hu
  obtain ⟨ρ,hρ,hseg⟩ := exists_closed_arc_clearance R.diagram b hb
  refine ⟨ρ,hρ,?_⟩
  intro e u
  let z := componentPLLoop R.diagram e u
  change ρ ≤ dist z b
  have hmem : z ∈ Set.range (componentPLLoop R.diagram e) := ⟨u,rfl⟩
  obtain ⟨f,_hf,hpath⟩ := (componentPLLoop_trace R.diagram e z).mp hmem
  obtain ⟨v,hv⟩ := hpath
  rw [← hv, diagramArcPath_apply]
  exact hseg f v.val ⟨v.property.1,v.property.2⟩

end DirectGLSSW.HOMFLY.ProcessedExposedChild
end


