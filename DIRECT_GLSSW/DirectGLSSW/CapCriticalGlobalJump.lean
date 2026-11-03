import DirectGLSSW.CapCriticalEventGeometry
import DirectGLSSW.CapGlobalEventJump

set_option autoImplicit false

namespace DirectGLSSW.CapCriticalGlobalJump

open DirectGLSSW
open DirectGLSSW.CapCrossingEvent
open DirectGLSSW.CapCriticalTimes
open DirectGLSSW.CapCriticalEventGeometry
open DirectGLSSW.CapGlobalEventJump
open DirectGLSSW.GlobalCapIntertwining
open DirectGLSSW.GlobalCapEntry

theorem criticalPair_global_event_jump
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n k j : ℕ)
    (hzero : (q 0).2 = 0)
    (hoff : ∀ a, 0 < a → a ≤ n → (q a).2 ≠ 0)
    (hdistinct : ∀ a b, 0 < a → a ≤ n → 0 < b → b ≤ n → a ≠ b → q a ≠ q b)
    (hpositive : ∀ i a b, 0 < i → i < a → a < b → b ≤ n → polygonHDet q i a b ≠ 0)
    (hroots : ∀ p r, p ∈ criticalPairs q n → r ∈ criticalPairs q n →
      criticalRoot q p = criticalRoot q r → p = r)
    (hk : 0 < k) (hkj : k < j) (hjn : j ≤ n)
    (hs : planarDet (q k - q j) (1, 0) ≠ 0) :
    let t := criticalRoot q (k, j)
    let qEvent := horizontalMove q t
    let τ := (q k).2 / (q j).2
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      (∀ a b : Fin n, a.val < b.val →
        CyclicGeneric (lineCapCore (horizontalMove qEvent (-ε)) a b)) →
      lineCapJ (horizontalMove q (t + ε)) n -
        lineCapJ (horizontalMove q (t - ε)) n =
        eventContribution qEvent n k j hk hkj hjn τ := by
  classical
  let t : ℝ := criticalRoot q (k, j)
  let qEvent : ℕ → PlanarPoint ℝ := horizontalMove q t
  let τ : ℝ := (q k).2 / (q j).2
  have hgeom := critical_event_geometry q n k j hzero hoff hdistinct hpositive
    hroots hk hkj hjn hs
  rcases hgeom with ⟨hτzero, hτone, hcollinear, hgeometryIsolated⟩
  have hzeroEvent : (qEvent 0).2 = 0 := by
    change (horizontalMove q t 0).2 = 0
    rw [horizontalMove_y]
    exact hzero
  have hoffEvent : ∀ a, 0 < a → a ≤ n → (qEvent a).2 ≠ 0 := by
    intro a ha han
    change (horizontalMove q t a).2 ≠ 0
    rw [horizontalMove_y]
    exact hoff a ha han
  have hcollinearEvent : qEvent k = qEvent 0 + τ • (qEvent j - qEvent 0) := by
    exact hcollinear
  have hisolatedEvent : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet qEvent a b c ≠ 0 := by
    intro a b c hab hbc hcn hcase
    apply hgeometryIsolated a b c hab hbc hcn
    intro htuple
    have htuple' : a = 0 ∧ b = k ∧ c = j := by
      simpa only [Prod.mk.injEq] using htuple
    rcases htuple' with ⟨ha, hb, hc⟩
    rcases hcase with ha' | hb' | hc'
    · exact ha' ha
    · exact hb' hb
    · exact hc' hc
  obtain ⟨ρ, hρ, hjump⟩ := exists_isolated_lineCapJ_jump
    hRI qEvent n k j hk hkj hjn τ hτzero hτone hzeroEvent hoffEvent
    hcollinearEvent hisolatedEvent
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ hcaps
  have hevent := hjump ε hε hερ hcaps
  have hplus : horizontalMove qEvent ε = horizontalMove q (t + ε) := by
    simpa [qEvent] using horizontalMove_add q t ε
  have hminus : horizontalMove qEvent (-ε) = horizontalMove q (t - ε) := by
    rw [sub_eq_add_neg]
    simpa [qEvent] using horizontalMove_add q t (-ε)
  rw [← hplus, ← hminus]
  exact hevent



end DirectGLSSW.CapCriticalGlobalJump
