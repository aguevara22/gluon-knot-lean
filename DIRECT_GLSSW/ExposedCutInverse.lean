import ActiveArcExposedAuxiliary
import UniversalCarrierReconstruction
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
open Filter Topology

/-- Exact inverse vertex reindexing for the fixed deleted edge. This adds no
vertex, arc, geometric closure assumption, or new point. -/
def uncutArc {n : ℕ} (r : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2)) :
    Fin (n+2) → PlanarPoint ℝ := r ∘ (cyclicVertexEquiv e).symm

@[simp] theorem cutArc_uncutArc {n : ℕ} (r : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2)) :
    cutArc (uncutArc r e) e=r := by
  funext i
  exact congrArg r ((cyclicVertexEquiv e).symm_apply_apply i)

@[simp] theorem uncutArc_cutArc {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2)) :
    uncutArc (cutArc q e) e=q := by
  funext i
  exact congrArg q ((cyclicVertexEquiv e).apply_symm_apply i)

theorem continuous_uncutArc {n : ℕ} (e : Fin (n+2)) :
    Continuous (fun r : Fin (n+2) → PlanarPoint ℝ => uncutArc r e) :=
  continuous_pi (fun i => continuous_apply _)

theorem continuous_cutArc {n : ℕ} (e : Fin (n+2)) :
    Continuous (fun q : Fin (n+2) → PlanarPoint ℝ => cutArc q e) :=
  continuous_pi (fun i => continuous_apply _)

/-- A genuine polygon neighborhood pulls back to the actual exposed open
word; membership reconstructs the same literal closed polygon by reindexing. -/
theorem uncutArc_preimage_mem_nhds {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (e : Fin (n+2)) (V : Set (Fin (n+2) → PlanarPoint ℝ)) (hV : V∈𝓝 q) :
    (fun r => uncutArc r e) ⁻¹' V∈𝓝 (cutArc q e) := by
  have hc := (continuous_uncutArc e).continuousAt (x:=cutArc q e)
  apply hc.preimage_mem_nhds
  simpa only [uncutArc_cutArc] using hV
end DirectGLSSW.ActiveArc.ExposedChart
