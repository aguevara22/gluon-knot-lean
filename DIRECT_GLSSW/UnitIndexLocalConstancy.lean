import ProbeIndexPerturbation
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex

/-- Any two probes in a ball missed by the whole curve have equal indices.
The center's index provides the common comparison; no path-invariance premise is used. -/
theorem unitPositionalIndex_constant_on_clear_ball (γ : C(I, ℂ))
    (hclosed : γ 1 = γ 0) (b : ℂ) (r : ℝ) (hr : 0 < r)
    (hclear : ∀ u, r ≤ ‖γ u-b‖) (z w : ℂ)
    (hz : ∀ u, γ u ≠ z) (hw : ∀ u, γ u ≠ w)
    (hzball : ‖z-b‖ < r) (hwball : ‖w-b‖ < r) :
    unitPositionalIndex γ hclosed z hz = unitPositionalIndex γ hclosed w hw := by
  have hb (u : I) : γ u ≠ b :=
    sub_ne_zero.mp (norm_pos_iff.mp (hr.trans_le (hclear u)))
  have hez := unitPositionalIndex_eq_of_clearance γ hclosed b z hb hz r hclear hzball
  have hew := unitPositionalIndex_eq_of_clearance γ hclosed b w hb hw r hclear hwball
  exact hez.symm.trans hew

/-- Full local constancy on the complement of a continuous closed loop.
Compactness supplies the positive clearance; the index equality is proved. -/
theorem unitPositionalIndex_locally_constant (γ : C(I, ℂ))
    (hclosed : γ 1 = γ 0) (z : ℂ) (hz : ∀ u, γ u ≠ z) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w-z‖ < r →
      ∃ hw : ∀ u, γ u ≠ w,
        unitPositionalIndex γ hclosed w hw = unitPositionalIndex γ hclosed z hz := by
  have hcont : Continuous (fun u : I => ‖γ u-z‖) :=
    (γ.continuous.sub continuous_const).norm
  obtain ⟨u₀,_,hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set I).Nonempty) hcont.continuousOn
  have hr : 0 < ‖γ u₀-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hz u₀))
  refine ⟨‖γ u₀-z‖,hr,?_⟩
  intro w hwclose
  have hsmall (u : I) : ‖w-z‖ < ‖γ u-z‖ :=
    hwclose.trans_le (hmin (Set.mem_univ u))
  have hw : ∀ u, γ u ≠ w :=
    (exists_closed_probe_argument_correction γ hclosed z w hsmall).2.1
  exact ⟨hw,(unitPositionalIndex_eq_of_small_displacement γ hclosed z w hz hw hsmall).symm⟩

end DirectGLSSW.HOMFLY.PositionalIndex


