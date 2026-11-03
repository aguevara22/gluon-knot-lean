import DirectGLSSW.CapCrossingVectors
import DirectGLSSW.CapCrossingExactEvent
import DirectGLSSW.CapVirtualEventInvariance
import DirectGLSSW.CapEventInterpretation

set_option autoImplicit false
namespace DirectGLSSW.SourceLineCrossing
open scoped BigOperators

theorem actual_rank_one_identities
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n k : ℕ) (hk : 0 < k) (hkn : k < n)
    (τ : ℝ) (hτ : τ < 0) (hzero : (q 0).2 = 0)
    (hcollinear : q k = q 0 + τ • (q (k+1) - q 0))
    (hlast : (q (k+1)).2 ≠ 0)
    (hothers : ∀ l, 0 < l → l ≤ n → (q l).2 ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ k+1) → polygonHDet q a b c ≠ 0) :
    (∑ l : Fin n,
      GlobalCapIntertwining.lineCapF q n ⟨k, hkn⟩ l *
        GlobalCapIntertwining.lineCapU q n l ⟨k - 1, by omega⟩) = 0 ∧
    (∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      (∀ a b : Fin n, a.val < b.val →
        CyclicGeneric (GlobalCapEntry.lineCapCore
          (CapCrossingEvent.horizontalMove q ε) a b)) →
      (∀ a b : Fin n, a.val < b.val →
        CyclicGeneric (GlobalCapEntry.lineCapCore
          (CapCrossingEvent.horizontalMove q (-ε)) a b)) →
      (∀ i : Fin n,
        (∑ l : Fin n,
          GlobalCapIntertwining.lineCapF q n ⟨k, hkn⟩ l *
            GlobalCapIntertwining.lineCapJ (CapCrossingEvent.horizontalMove q ε) n l i) =
          scalarSignValue (q (k+1)).2 *
            GlobalCapIntertwining.lineCapF q n ⟨k, hkn⟩ i ∧
        (∑ l : Fin n,
          GlobalCapIntertwining.lineCapF q n ⟨k, hkn⟩ l *
            GlobalCapIntertwining.lineCapJ (CapCrossingEvent.horizontalMove q (-ε)) n l i) =
          scalarSignValue (q (k+1)).2 *
            GlobalCapIntertwining.lineCapF q n ⟨k, hkn⟩ i) ∧
      (∀ i : Fin n,
        (∑ l : Fin n,
          GlobalCapIntertwining.lineCapJ (CapCrossingEvent.horizontalMove q ε) n i l *
            GlobalCapIntertwining.lineCapU q n l ⟨k-1, by omega⟩) =
          -scalarSignValue (q (k+1)).2 *
            GlobalCapIntertwining.lineCapU q n i ⟨k-1, by omega⟩ ∧
        (∑ l : Fin n,
          GlobalCapIntertwining.lineCapJ (CapCrossingEvent.horizontalMove q (-ε)) n i l *
            GlobalCapIntertwining.lineCapU q n l ⟨k-1, by omega⟩) =
          -scalarSignValue (q (k+1)).2 *
            GlobalCapIntertwining.lineCapU q n i ⟨k-1, by omega⟩)) := by
  exact ⟨CapCrossingVectors.lineCap_FU_entry_below q n k hk hkn,
    CapCrossingVectors.exists_lineCap_crossing_side_eigenidentities
      hRI q n k hk hkn τ hτ hzero hcollinear hlast hothers hisolated⟩

end DirectGLSSW.SourceLineCrossing
