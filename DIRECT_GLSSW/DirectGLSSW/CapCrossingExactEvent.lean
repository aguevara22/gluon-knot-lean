import DirectGLSSW.CapCrossingEvent
import DirectGLSSW.CapCrossingEventStability

set_option autoImplicit false

namespace DirectGLSSW.CapCrossingExactEvent
open DirectGLSSW.CapCrossingEvent

theorem exists_lineCap_J_jump_at_event
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n k : ℕ) (hk : 0 < k) (hkn : k < n)
    (τ : ℝ) (hτ : τ < 0) (hzero : (q 0).2 = 0)
    (hcollinear : q k = q 0 + τ • (q (k+1) - q 0))
    (hothers : ∀ l, 0 < l → l ≤ n → (q l).2 ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ k+1) → polygonHDet q a b c ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      (∀ a : Fin n, a.val < k-1 →
        CyclicGeneric (GlobalCapEntry.lineCapCore (horizontalMove q (-ε))
          a ⟨k-1, by omega⟩)) →
      ∀ i l : Fin n,
        (GlobalCapIntertwining.lineCapJ (horizontalMove q ε) n -
          GlobalCapIntertwining.lineCapJ (horizontalMove q (-ε)) n) i l =
        2 * scalarSignValue (q (k+1)).2 *
          GlobalCapIntertwining.lineCapU q n i ⟨k-1, by omega⟩ *
          GlobalCapIntertwining.lineCapF q n ⟨k, hkn⟩ l := by
  obtain ⟨ρ₁, hρ₁, hjump⟩ := CapCrossingEvent.exists_lineCap_J_jump
    hRI q n k hk hkn τ hτ hzero hcollinear hothers hisolated
  obtain ⟨ρ₂, hρ₂, hstable⟩ := CapCrossingEventStability.exists_lineCap_FU_stability_radius
    q n k hk hkn τ hτ hzero hcollinear
    (hothers (k+1) (by omega) (by omega)) hisolated
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
  intro ε hε hερ hcaps i l
  have he₁ : ε < ρ₁ := lt_of_lt_of_le hερ (min_le_left _ _)
  have he₂ : ε < ρ₂ := lt_of_lt_of_le hερ (min_le_right _ _)
  obtain ⟨hF, hU⟩ := hstable ε hε he₂
  have h := hjump ε hε he₁ hcaps i l
  have hf := (hF l).2
  have hu := (hU i).2
  change GlobalCapIntertwining.lineCapF (horizontalMove q (-ε)) n ⟨k,hkn⟩ l = _ at hf
  change GlobalCapIntertwining.lineCapU (horizontalMove q (-ε)) n i ⟨k-1,by omega⟩ = _ at hu
  rw [hf, hu] at h
  exact h



end DirectGLSSW.CapCrossingExactEvent
