import UnitHalfplaneIndexZero
import ComplexPLLoop
import ExteriorRootProbe

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex
open DirectGLSSW.HOMFLY.PrincipalTurning

/-- The literal closed PL component has zero positional index at a point
strictly outside a half-plane containing every actual diagram vertex. -/
theorem complexPLLoop_index_zero_of_vertex_halfplane
    (D : PLLinkDiagram) (e : Fin D.nArc) (a z : ℂ) (b : ℝ)
    (hvertices : ∀ v : Fin D.nVertex,
      b ≤ (a * Complex.equivRealProd.symm (D.vertexPoint v)).re)
    (hz : (a * z).re < b) :
    ∃ havoid : ∀ u : I, complexPLLoop D e u ≠ z,
      unitPositionalIndex (complexPLLoop D e)
        (complexPLLoop_endpoint_eq D e).symm z havoid = 0 := by
  have hloop := complexPLLoop_affine_halfplane D e a b hvertices
  have hhalf : ∀ u : I, 0 < (a * (complexPLLoop D e u - z)).re := by
    intro u
    rw [mul_sub, Complex.sub_re]
    linarith [hloop u]
  exact unitPositionalIndex_zero_of_strict_halfplane
    (complexPLLoop D e) (complexPLLoop_endpoint_eq D e).symm z a hhalf

/-- The source supporting geometry supplies the entire vertex half-plane;
the opposite-side probe has strict separation for every positive offset. -/
theorem actual_supported_pl_exterior_index_zero
    (s : MarkedParentState) (p q : PlanarPoint ℝ)
    (h : SupportingRootGeometry s p q) (e : Fin s.1.nArc)
    (τ ε : ℝ) (hε : 0 < ε) :
    ∃ havoid : ∀ u : I,
      complexPLLoop s.1 e u ≠ exteriorRootProbe p q τ ε,
      unitPositionalIndex (complexPLLoop s.1 e)
        (complexPLLoop_endpoint_eq s.1 e).symm
        (exteriorRootProbe p q τ ε) havoid = 0 := by
  have hpq := supportingRoot_endpoints_ne s p q h e
  apply complexPLLoop_index_zero_of_vertex_halfplane s.1 e
    (supportingRootNormal p q) (exteriorRootProbe p q τ ε)
    (supportingRootNormal p q * (⟨p.1,p.2⟩ : ℂ)).re
  · intro v
    have hv := h.2 v
    simp [planarDet] at hv
    simp [supportingRootNormal, Complex.equivRealProd_symm_apply, Complex.mul_re]
    nlinarith
  · exact exteriorRootProbe_strict_exterior p q hpq τ ε hε

end DirectGLSSW.HOMFLY.PositionalIndex



