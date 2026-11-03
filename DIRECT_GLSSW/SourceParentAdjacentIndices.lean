import ActualParentIndexOne
import ActualRetainedRoot
import PLRootUnique

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex
open DirectGLSSW.HOMFLY.PrincipalTurning
open DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.HOMFLY.SmoothingCornerGeometry
open DirectGLSSW.HOMFLY.ProcessedExposedChild

/-- Every actual stored supported root has occupied-side index one on its
literal PL loop. The entire unique-preimage premise is produced from D. -/
theorem actual_supported_parent_root_index_one
    (s : MarkedParentState) (p q : PlanarPoint ℝ)
    (h : SupportingRootGeometry s p q) (C : diagramComponent s.1)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    let base := (s.2.1.baseArc C).val
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ havoid : ∀ u : I, complexPLLoop s.1 base u ≠ interiorRootProbe p q τ ε,
        unitPositionalIndex (complexPLLoop s.1 base)
          (complexPLLoop_endpoint_eq s.1 base).symm (interiorRootProbe p q τ ε) havoid = 1 := by
  dsimp
  apply supported_pl_root_index_one_of_unique_preimage s.1 (s.2.1.baseArc C).val p q
    (h.1 C).1 (h.1 C).2 h.2 τ hτ0 hτ1
  intro u v hu hv
  have hu' := componentPLLoop_unique_interior_root_preimage s.1
    (s.2.1.baseArc C).val τ hτ0 hτ1 u (by simpa [(h.1 C).1,(h.1 C).2] using hu)
  have hv' := componentPLLoop_unique_interior_root_preimage s.1
    (s.2.1.baseArc C).val τ hτ0 hτ1 v (by simpa [(h.1 C).1,(h.1 C).2] using hv)
  exact Subtype.ext (hu'.trans hv'.symm)

/-- The actual retained parent's original exposed basepoint has adjacent
positional indices zero and one. No geometric separation, lift, uniqueness or
index assumption is added to actual ancestry and exposure. -/
theorem source_parent_adjacent_indices
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
      (∃ havoid : ∀ u : I, complexPLLoop s.1 base u ≠ exteriorRootProbe p q τ ε,
        unitPositionalIndex (complexPLLoop s.1 base)
          (complexPLLoop_endpoint_eq s.1 base).symm (exteriorRootProbe p q τ ε) havoid = 0) ∧
      (∃ havoid : ∀ u : I, complexPLLoop s.1 base u ≠ interiorRootProbe p q τ ε,
        unitPositionalIndex (complexPLLoop s.1 base)
          (complexPLLoop_endpoint_eq s.1 base).symm (interiorRootProbe p q τ ε) havoid = 1) := by
  dsimp only
  have hs := actual_parent_original_supporting_root x hx htrace he
  obtain ⟨ε₀,hε₀,hone⟩ := actual_supported_parent_root_index_one s _ _ hs
    (PermutationOrbits.componentOf s.1.continuation ⟨0,source_parent_nArc_pos x hx htrace⟩)
    τ hτ0 hτ1
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hsmall
  constructor
  · exact actual_supported_pl_exterior_index_zero s _ _ hs
      (sourceRetainedBaseArc x hx htrace) τ ε hε
  · exact hone ε hε hsmall

end DirectGLSSW.HOMFLY.PositionalIndex


