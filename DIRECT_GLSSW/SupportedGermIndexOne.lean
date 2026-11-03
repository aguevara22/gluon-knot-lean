import SupportingGermCut
import SingleCutArgument
import AffineIndexCovariance

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex

/-- A supported loop with one positively oriented affine root germ has index
one at all sufficiently small positive real probes. Geometric inputs remain
explicit here; actual PL producers discharge them in the source application. -/
theorem supported_germ_small_probe_index_one
    (g : C(I, ℂ)) (hclosed : g 1 = g 0)
    (t₀ : I) (ht₀ : 0 < t₀.val) (ht₁ : t₀.val < 1)
    (k η : ℝ) (hk : 0 < k) (hη : 0 < η)
    (hhalf : ∀ u : I, 0 ≤ (g u).re)
    (hgerm : ∀ u : I, |u.val - t₀.val| < η →
      g u = ⟨0, k * (t₀.val - u.val)⟩)
    (hunique : ∀ u : I, g u = 0 → u = t₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ havoid : ∀ u : I, g u ≠ (ε : ℂ),
        unitPositionalIndex g hclosed (ε : ℂ) havoid = 1 := by
  obtain ⟨ε₀,hε₀,hcut⟩ := exists_shifted_slitPlane_off_supporting_germ
    g t₀ k η hk hη hhalf hgerm hunique
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hsmall
  let f : C(I,ℂ) := ⟨fun u => g u - (ε : ℂ), g.continuous.sub continuous_const⟩
  have hfclosed : f 1 = f 0 := by change g 1 - (ε : ℂ) = g 0 - (ε : ℂ); rw [hclosed]
  have hfgerm : ∀ u : I, |u.val - t₀.val| < η →
      f u = ⟨-ε,k*(t₀.val-u.val)⟩ := by
    intro u hu
    change g u - (ε : ℂ) = _
    rw [hgerm u hu]
    apply Complex.ext <;> simp
  obtain ⟨hfavoid,hidx⟩ := unitPositionalIndex_one_of_single_cut
    f hfclosed t₀ ht₀ ht₁ ε k η hε hk hη (hcut ε hε hsmall) hfgerm
  have hformula : ∀ u, f u = (1:ℂ)*(g u-(ε:ℂ)) := by intro u; simp [f]
  have havoid := avoids_probe_of_affine_position g f (ε:ℂ) 1 hfavoid hformula
  refine ⟨havoid,?_⟩
  rw [← unitPositionalIndex_affine_covariance g f hclosed hfclosed (ε:ℂ) 1
    one_ne_zero havoid hfavoid hformula]
  exact hidx

end DirectGLSSW.HOMFLY.PositionalIndex

