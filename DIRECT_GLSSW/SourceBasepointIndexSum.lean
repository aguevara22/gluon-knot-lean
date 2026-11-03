import SourceParentAdjacentIndices
import ActualRootCharacterizations
set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex
open DirectGLSSW.HOMFLY.PrincipalTurning
open DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.HOMFLY.SmoothingCornerGeometry
/-- Literal sum of the two genuine positional indices; no new index definition. -/
theorem source_parent_basepoint_index_sum
    {n : ℕ} (x : Fin (n+2) → PlanarPoint ℝ) (hx : CyclicGeneric x)
    {s : MarkedParentState}
    (htrace : MarkedParentTrace
      (positivePolygonMarkedState x hx (initialAnchorTraversal x hx)) s)
    (he : ExposedOpenPrimitive.LeftExposed x 0)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    let p := (positivePolygonEventDiagram x hx).vertexPoint
      ((positivePolygonEventDiagram x hx).arcSource (eventFin x (initialAnchor x hx)))
    let q := (positivePolygonEventDiagram x hx).vertexPoint
      ((positivePolygonEventDiagram x hx).arcTarget (eventFin x (initialAnchor x hx)))
    let base := sourceRetainedBaseArc x hx htrace
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ hRight : ∀ u : I, complexPLLoop s.1 base u ≠ exteriorRootProbe p q τ ε,
      ∃ hLeft : ∀ u : I, complexPLLoop s.1 base u ≠ interiorRootProbe p q τ ε,
        unitPositionalIndex (complexPLLoop s.1 base)
          (complexPLLoop_endpoint_eq s.1 base).symm (exteriorRootProbe p q τ ε) hRight = 0 ∧
        unitPositionalIndex (complexPLLoop s.1 base)
          (complexPLLoop_endpoint_eq s.1 base).symm (interiorRootProbe p q τ ε) hLeft = 1 ∧
        unitPositionalIndex (complexPLLoop s.1 base)
          (complexPLLoop_endpoint_eq s.1 base).symm (exteriorRootProbe p q τ ε) hRight +
        unitPositionalIndex (complexPLLoop s.1 base)
          (complexPLLoop_endpoint_eq s.1 base).symm (interiorRootProbe p q τ ε) hLeft = 1 := by
  obtain ⟨ε₀,hε₀,hindices⟩ := source_parent_adjacent_indices x hx htrace he τ hτ0 hτ1
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hsmall
  obtain ⟨⟨hRight,hRightZero⟩,⟨hLeft,hLeftOne⟩⟩ := hindices ε hε hsmall
  exact ⟨hRight,hLeft,hRightZero,hLeftOne,by rw [hRightZero,hLeftOne]; norm_num⟩
end DirectGLSSW.HOMFLY.PositionalIndex

