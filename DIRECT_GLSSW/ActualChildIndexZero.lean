import ActualDetachedPLClearance
import ActualSourcePLExteriorZero
import UnitIndexLocalConstancy

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex
open PrincipalTurning ProcessedExposedChild PolygonDrawingBridge SmoothingCornerGeometry

/-- The literal right-hand probe can be chosen inside any positive ball about
the root point. No nondegeneracy is needed for this distance statement. -/
theorem exists_exterior_probe_close (p q : PlanarPoint ℝ) (τ r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧
      ‖exteriorRootProbe p q τ ε - Complex.equivRealProd.symm (affinePoint p q τ)‖ < r := by
  let v : ℂ := ⟨q.2-p.2, -(q.1-p.1)⟩
  let ε : ℝ := r / (2 * (‖v‖+1))
  have hv : 0 < ‖v‖+1 := by positivity
  have hε : 0 < ε := div_pos hr (mul_pos (by norm_num) hv)
  refine ⟨ε,hε,?_⟩
  have heq : exteriorRootProbe p q τ ε -
      Complex.equivRealProd.symm (affinePoint p q τ) = ε • v := by
    apply Complex.ext <;>
      simp [exteriorRootProbe, affinePoint, Complex.equivRealProd_symm_apply,
        v, Complex.real_smul] <;> ring
  rw [heq,norm_smul,Real.norm_eq_abs,abs_of_pos hε]
  have hprod : ε * (2*(‖v‖+1)) = r := div_mul_cancel₀ r (ne_of_gt (mul_pos (by norm_num) hv))
  have hnonneg := norm_nonneg v
  nlinarith

/-- Every actual detached component has positional index zero throughout one
uniform positive neighborhood of the original interior root point. All
clearance, exterior index and local constancy premises are discharged. -/
theorem source_detached_pl_index_zero_near_basepoint
    {n : ℕ} (x : Fin (n+2) → PlanarPoint ℝ) (hx : CyclicGeneric x)
    {s : MarkedParentState}
    (htrace : MarkedParentTrace
      (positivePolygonMarkedState x hx (initialAnchorTraversal x hx)) s)
    (c : Fin s.1.nCrossing) (he : ExposedOpenPrimitive.LeftExposed x 0)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    let p := (positivePolygonEventDiagram x hx).vertexPoint
      ((positivePolygonEventDiagram x hx).arcSource (eventFin x (initialAnchor x hx)))
    let q := (positivePolygonEventDiagram x hx).vertexPoint
      ((positivePolygonEventDiagram x hx).arcTarget (eventFin x (initialAnchor x hx)))
    let b := Complex.equivRealProd.symm (affinePoint p q τ)
    ∃ r : ℝ, 0 < r ∧ ∀ e : Fin (canonicalDetachedRestriction s c).diagram.nArc,
      ∀ z : ℂ, ‖z-b‖ < r →
        ∃ havoid : ∀ u : I,
          complexPLLoop (canonicalDetachedRestriction s c).diagram e u ≠ z,
          unitPositionalIndex
            (complexPLLoop (canonicalDetachedRestriction s c).diagram e)
            (complexPLLoop_endpoint_eq (canonicalDetachedRestriction s c).diagram e).symm
            z havoid = 0 := by
  let D := (canonicalDetachedRestriction s c).diagram
  let p := (positivePolygonEventDiagram x hx).vertexPoint
    ((positivePolygonEventDiagram x hx).arcSource (eventFin x (initialAnchor x hx)))
  let q := (positivePolygonEventDiagram x hx).vertexPoint
    ((positivePolygonEventDiagram x hx).arcTarget (eventFin x (initialAnchor x hx)))
  let b := Complex.equivRealProd.symm (affinePoint p q τ)
  change ∃ r : ℝ, 0 < r ∧ ∀ e : Fin D.nArc, ∀ z : ℂ, ‖z-b‖ < r →
    ∃ havoid : ∀ u : I, complexPLLoop D e u ≠ z,
      unitPositionalIndex (complexPLLoop D e) (complexPLLoop_endpoint_eq D e).symm z havoid = 0
  obtain ⟨r,hr,hplanar⟩ := canonical_detached_source_child_pl_clearance x hx htrace c he τ hτ0 hτ1
  have hclear (e : Fin D.nArc) (u : I) : r ≤ ‖complexPLLoop D e u-b‖ := by
    have h := complexPLLoop_complex_distance_lower_bound D e u (affinePoint p q τ) r (hplanar e u)
    simpa only [dist_eq_norm] using h
  obtain ⟨ε,hε,hwball⟩ := exists_exterior_probe_close p q τ r hr
  refine ⟨r,hr,?_⟩
  intro e z hzball
  obtain ⟨hw,hwzero⟩ := source_detached_pl_exterior_index_zero x hx htrace c he e τ ε hε
  have hz : ∀ u : I, complexPLLoop D e u ≠ z := by
    intro u hu
    have h := hclear e u
    rw [hu] at h
    exact (not_lt_of_ge h) hzball
  refine ⟨hz,?_⟩
  have heq := unitPositionalIndex_constant_on_clear_ball
    (complexPLLoop D e) (complexPLLoop_endpoint_eq D e).symm b r hr
    (hclear e) z (exteriorRootProbe p q τ ε) hz hw hzball hwball
  exact heq.trans hwzero

end DirectGLSSW.HOMFLY.PositionalIndex


