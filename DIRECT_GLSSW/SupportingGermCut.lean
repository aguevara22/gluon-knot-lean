import UnitLoopPositionalIndex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex

/-- A unique, transverse zero of a supported closed loop is the only possible
point on the shifted negative-real cut for sufficiently small positive shifts.
The positive radius is obtained from compactness away from the zero. -/
theorem exists_shifted_slitPlane_off_supporting_germ
    (g : C(I, ℂ)) (t₀ : I) (k η : ℝ) (hk : 0 < k) (hη : 0 < η)
    (hhalf : ∀ u : I, 0 ≤ (g u).re)
    (hgerm : ∀ u : I, |u.val - t₀.val| < η →
      g u = ⟨0, k * (t₀.val - u.val)⟩)
    (hunique : ∀ u : I, g u = 0 → u = t₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : I, u ≠ t₀ → g u - (ε : ℂ) ∈ Complex.slitPlane := by
  let K : Set I := {u | η ≤ |u.val - t₀.val|}
  have hKclosed : IsClosed K := by
    have hc : Continuous (fun u : I => |u.val - t₀.val|) :=
      (continuous_subtype_val.sub continuous_const).abs
    exact isClosed_Ici.preimage hc
  have hKcompact : IsCompact K := hKclosed.isCompact
  have h0not : (0 : ℂ) ∉ g '' K := by
    rintro ⟨u,hu,hu0⟩
    have hEq : u = t₀ := hunique u hu0
    subst u
    have hAbs : |t₀.val - t₀.val| = 0 := by simp
    change η ≤ |t₀.val - t₀.val| at hu
    rw [hAbs] at hu
    linarith
  have hopen : (g '' K)ᶜ ∈ 𝓝 (0 : ℂ) :=
    (hKcompact.image g.continuous).isClosed.isOpen_compl.mem_nhds h0not
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp hopen
  refine ⟨ρ,hρ,?_⟩
  intro ε hε hερ u hune
  have hlocal_of_norm (hnorm : ‖g u‖ < ρ) : |u.val - t₀.val| < η := by
    have hnot : g u ∉ g '' K := hball (by simpa [Metric.mem_ball, dist_zero_right] using hnorm)
    have hunot : u ∉ K := by
      intro hu
      exact hnot ⟨u,hu,rfl⟩
    exact lt_of_not_ge hunot
  by_cases hright : ε < (g u).re
  · apply Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  · have hle : (g u).re ≤ ε := le_of_not_gt hright
    have him : (g u).im ≠ 0 := by
      intro him0
      have hgReal : g u = ((g u).re : ℂ) := by
        apply Complex.ext <;> simp [him0]
      have hnorm : ‖g u‖ = (g u).re := by
        conv_lhs => rw [hgReal]
        simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hhalf u)]
      have hlocal := hlocal_of_norm (by rw [hnorm]; linarith)
      have hline := hgerm u hlocal
      have himline := congrArg Complex.im hline
      change (g u).im = k * (t₀.val - u.val) at himline
      have hdiff : t₀.val - u.val = 0 := (mul_eq_zero.mp (himline.symm.trans him0)).resolve_left (ne_of_gt hk)
      apply hune
      apply Subtype.ext
      linarith
    apply Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using him

end DirectGLSSW.HOMFLY.PositionalIndex


