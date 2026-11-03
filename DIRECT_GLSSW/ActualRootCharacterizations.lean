import RootNormalCoordinates
import ActualRetainedRoot

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PositionalIndex
open DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.HOMFLY.SmoothingCornerGeometry
open DirectGLSSW.HOMFLY.ProcessedExposedChild

theorem interiorRootProbe_eq (p q : PlanarPoint ℝ) (τ ε : ℝ) :
    interiorRootProbe p q τ ε =
      ⟨p.1 + τ*(q.1-p.1) - ε*(q.2-p.2),
       p.2 + τ*(q.2-p.2) + ε*(q.1-p.1)⟩ := by
  apply Complex.ext <;> simp [interiorRootProbe, PrincipalTurning.exteriorRootProbe] <;> ring

theorem sourceRetainedBaseArc_eq {n : ℕ} (x : Fin (n+2) → PlanarPoint ℝ)
    (hx : CyclicGeneric x) {s : MarkedParentState}
    (htrace : MarkedParentTrace
      (positivePolygonMarkedState x hx (initialAnchorTraversal x hx)) s) :
    sourceRetainedBaseArc x hx htrace =
      (s.2.1.baseArc (PermutationOrbits.componentOf s.1.continuation
        ⟨0,source_parent_nArc_pos x hx htrace⟩)).val := rfl

theorem sourceRetainedBaseArc_original_endpoints {n : ℕ}
    (x : Fin (n+2) → PlanarPoint ℝ) (hx : CyclicGeneric x) {s : MarkedParentState}
    (htrace : MarkedParentTrace
      (positivePolygonMarkedState x hx (initialAnchorTraversal x hx)) s)
    (he : ExposedOpenPrimitive.LeftExposed x 0) :
    s.1.vertexPoint (s.1.arcSource (sourceRetainedBaseArc x hx htrace)) =
      (positivePolygonEventDiagram x hx).vertexPoint
        ((positivePolygonEventDiagram x hx).arcSource (eventFin x (initialAnchor x hx))) ∧
    s.1.vertexPoint (s.1.arcTarget (sourceRetainedBaseArc x hx htrace)) =
      (positivePolygonEventDiagram x hx).vertexPoint
        ((positivePolygonEventDiagram x hx).arcTarget (eventFin x (initialAnchor x hx))) := by
  exact (actual_parent_original_supporting_root x hx htrace he).1
    (PermutationOrbits.componentOf s.1.continuation ⟨0,source_parent_nArc_pos x hx htrace⟩)

end DirectGLSSW.HOMFLY.PositionalIndex



