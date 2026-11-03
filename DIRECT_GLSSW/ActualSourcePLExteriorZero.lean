import ActualPLHalfplaneIndexZero
import CanonicalRecursiveChild

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex
open DirectGLSSW.HOMFLY.PrincipalTurning
open DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.HOMFLY.SupportingGeometry
open DirectGLSSW.HOMFLY.SmoothingCornerGeometry

/-- Every current arc of the actual detached restriction lies in the same
closed supporting half-plane as the parent, including its connector. -/
theorem canonical_detached_vertices_supporting_halfplane
    (s : MarkedParentState) (c : Fin s.1.nCrossing)
    (p q : PlanarPoint ℝ) (h : SupportingRootGeometry s p q) :
    ∀ v : Fin (canonicalDetachedRestriction s c).diagram.nVertex,
      0 ≤ planarDet (q-p)
        ((canonicalDetachedRestriction s c).diagram.vertexPoint v-p) := by
  intro v
  let R := canonicalDetachedRestriction s c
  change 0 ≤ planarDet (q-p) (R.diagram.vertexPoint v-p)
  rw [R.vertexPoint_eq]
  exact smoothCrossing_vertices_halfplane s.1 c p (q-p) h.2 _

/-- The literal PL loop of every actual detached child has positional index
zero at the right-side probe of its original parent's supported root. -/
theorem actual_detached_pl_exterior_index_zero
    (s : MarkedParentState) (c : Fin s.1.nCrossing)
    (p q : PlanarPoint ℝ) (h : SupportingRootGeometry s p q)
    (e : Fin (canonicalDetachedRestriction s c).diagram.nArc)
    (τ ε : ℝ) (hε : 0 < ε) :
    ∃ havoid : ∀ u : I,
      complexPLLoop (canonicalDetachedRestriction s c).diagram e u ≠
        exteriorRootProbe p q τ ε,
      unitPositionalIndex
        (complexPLLoop (canonicalDetachedRestriction s c).diagram e)
        (complexPLLoop_endpoint_eq (canonicalDetachedRestriction s c).diagram e).symm
        (exteriorRootProbe p q τ ε) havoid = 0 := by
  let R := canonicalDetachedRestriction s c
  have hpq := supportingRoot_endpoints_ne s p q h
    ((s.2.1.baseArc
      (PermutationOrbits.componentOf s.1.continuation (s.1.incoming c 0))).val)
  apply complexPLLoop_index_zero_of_vertex_halfplane R.diagram e
    (supportingRootNormal p q) (exteriorRootProbe p q τ ε)
    (supportingRootNormal p q * (⟨p.1,p.2⟩ : ℂ)).re
  · intro v
    have hv := canonical_detached_vertices_supporting_halfplane s c p q h v
    simp [planarDet] at hv
    simp [supportingRootNormal, Complex.equivRealProd_symm_apply, Complex.mul_re]
    nlinarith
  · exact exteriorRootProbe_strict_exterior p q hpq τ ε hε

/-- Source-facing form: actual recursive ancestry and left exposure determine
the supported original root; no separation or argument-lift premise is added. -/
theorem source_detached_pl_exterior_index_zero
    {n : ℕ} (x : Fin (n+2) → PlanarPoint ℝ) (hx : CyclicGeneric x)
    {s : MarkedParentState}
    (htrace : MarkedParentTrace
      (positivePolygonMarkedState x hx (initialAnchorTraversal x hx)) s)
    (c : Fin s.1.nCrossing)
    (he : ExposedOpenPrimitive.LeftExposed x 0)
    (e : Fin (canonicalDetachedRestriction s c).diagram.nArc)
    (τ ε : ℝ) (hε : 0 < ε) :
    let p := (positivePolygonEventDiagram x hx).vertexPoint
      ((positivePolygonEventDiagram x hx).arcSource
        (eventFin x (initialAnchor x hx)))
    let q := (positivePolygonEventDiagram x hx).vertexPoint
      ((positivePolygonEventDiagram x hx).arcTarget
        (eventFin x (initialAnchor x hx)))
    ∃ havoid : ∀ u : I,
      complexPLLoop (canonicalDetachedRestriction s c).diagram e u ≠
        exteriorRootProbe p q τ ε,
      unitPositionalIndex
        (complexPLLoop (canonicalDetachedRestriction s c).diagram e)
        (complexPLLoop_endpoint_eq (canonicalDetachedRestriction s c).diagram e).symm
        (exteriorRootProbe p q τ ε) havoid = 0 := by
  dsimp
  exact actual_detached_pl_exterior_index_zero s c _ _
    (actual_parent_original_supporting_root x hx htrace he) e τ ε hε

end DirectGLSSW.HOMFLY.PositionalIndex




