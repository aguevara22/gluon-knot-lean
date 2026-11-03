import DirectGLSSW.CapCrossingExactEvent
import DirectGLSSW.CapVirtualEventInvariance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DirectGLSSW.CapGlobalEventJump
open DirectGLSSW.CapCrossingEvent DirectGLSSW.GlobalCapIntertwining

theorem horizontalMove_add (q : ℕ → PlanarPoint ℝ) (t s : ℝ) :
    horizontalMove (horizontalMove q t) s = horizontalMove q (t + s) := by
  funext a
  by_cases ha : a = 0
  · subst a
    ext <;> simp [horizontalMove, EndpointEventGeometry.moveEndpoint] <;> ring
  · simp [horizontalMove, EndpointEventGeometry.moveEndpoint, ha]

theorem horizontalMove_apply_positive (q : ℕ → PlanarPoint ℝ) (t : ℝ)
    (a : ℕ) (ha : 0 < a) : horizontalMove q t a = q a := by
  simp [horizontalMove, EndpointEventGeometry.moveEndpoint, ne_of_gt ha]

theorem horizontalMove_y (q : ℕ → PlanarPoint ℝ) (t : ℝ) (a : ℕ) :
    (horizontalMove q t a).2 = (q a).2 := by
  by_cases ha : a = 0
  · subst a
    simp [horizontalMove, EndpointEventGeometry.moveEndpoint]
  · simp [horizontalMove, EndpointEventGeometry.moveEndpoint, ha]

noncomputable def eventContribution (q : ℕ → PlanarPoint ℝ) (n k j : ℕ)
    (hk : 0 < k) (hkj : k < j) (hjn : j ≤ n) (τ : ℝ) :
    Matrix (Fin n) (Fin n) ℚ :=
  if τ < 0 ∧ j = k + 1 then
    fun i l => 2 * scalarSignValue (q j).2 *
      lineCapU q n i ⟨k-1, by omega⟩ * lineCapF q n ⟨j-1, by omega⟩ l
  else 0

theorem exists_isolated_lineCapJ_jump
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n k j : ℕ)
    (hk : 0 < k) (hkj : k < j) (hjn : j ≤ n)
    (τ : ℝ) (hτzero : τ ≠ 0) (hτone : τ ≠ 1)
    (hzero : (q 0).2 = 0)
    (hoff : ∀ a, 0 < a → a ≤ n → (q a).2 ≠ 0)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      (∀ a b : Fin n, a.val < b.val →
        CyclicGeneric (GlobalCapEntry.lineCapCore (horizontalMove q (-ε)) a b)) →
      lineCapJ (horizontalMove q ε) n - lineCapJ (horizontalMove q (-ε)) n =
        eventContribution q n k j hk hkj hjn τ := by
  by_cases hneg : τ < 0
  · by_cases hadj : j = k + 1
    · subst j
      have hkn : k < n := by omega
      obtain ⟨ρ, hρ, hjump⟩ := CapCrossingExactEvent.exists_lineCap_J_jump_at_event
        hRI q n k hk hkn τ hneg hzero hcollinear hoff hisolated
      refine ⟨ρ, hρ, ?_⟩
      intro ε hε hερ hcaps
      ext i l
      have he := hjump ε hε hερ
        (fun a ha => hcaps a ⟨k-1, by omega⟩ ha) i l
      simpa [eventContribution, hneg] using he
    · obtain ⟨ρ, hρ, hvirtual⟩ :=
        CapVirtualEventInvariance.exists_virtual_lineCapJ_invariant_negative_gap
          q n hk hkj (by omega) hjn τ hzero (hoff j (by omega) hjn)
          hcollinear hisolated hneg
      refine ⟨ρ, hρ, ?_⟩
      intro ε hε hερ _
      have he := (hvirtual ε hε hερ).2.2
      simp [eventContribution, hadj, he]
  · have hpos : 0 < τ := by rcases lt_or_gt_of_ne hτzero with h | h <;> linarith
    by_cases hlt : τ < 1
    · obtain ⟨ρ, hρ, hvirtual⟩ :=
        CapVirtualEventInvariance.exists_virtual_lineCapJ_invariant_positive_positive
          q n hk hkj hjn τ hzero (hoff j (by omega) hjn) hcollinear hisolated
          hpos (by linarith)
      refine ⟨ρ, hρ, ?_⟩
      intro ε hε hερ _
      have he := (hvirtual ε hε hερ).2.2
      simp [eventContribution, hneg, he]
    · have hgt : 1 < τ := by rcases lt_or_gt_of_ne hτone with h | h <;> linarith
      obtain ⟨ρ, hρ, hvirtual⟩ :=
        CapVirtualEventInvariance.exists_virtual_lineCapJ_invariant_positive_negative
          q n hk hkj hjn τ hzero (hoff j (by omega) hjn) hcollinear hisolated hgt
      refine ⟨ρ, hρ, ?_⟩
      intro ε hε hερ _
      have he := (hvirtual ε hε hερ).2.2
      simp [eventContribution, hneg, he]







end DirectGLSSW.CapGlobalEventJump
