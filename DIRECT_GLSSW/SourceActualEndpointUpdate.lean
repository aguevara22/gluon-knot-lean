import SourceEndpointAmplitude
import DirectGLSSW.CapCrossingEvent

set_option autoImplicit false
namespace DirectGLSSW.SourceActualEndpointUpdate
open CapCrossingEvent CapCrossingAlgebra GlobalCapIntertwining GlobalCapEntry
open EndpointCurrent SourceEndpointAmplitude

theorem actual_endpoint_update
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n k : ℕ) (hk : 0 < k) (hkn : k < n)
    (τ : ℝ) (hτ : τ < 0) (hzero : (q 0).2 = 0)
    (hcollinear : q k = q 0 + τ • (q (k+1) - q 0))
    (hlast : (q (k+1)).2 ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ k+1) → polygonHDet q a b c ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      let Q := horizontalMove q (-ε)
      ∀ hcaps : ∀ a : Fin n, a.val < k - 1 →
        CyclicGeneric (lineCapCore Q a (⟨k - 1, by omega⟩ : Fin n)),
      let A : Fin n → ℚ := fun a =>
        if ha : a.val < k - 1 then
          polygonAmplitude (lineCapCore Q a (⟨k - 1, by omega⟩ : Fin n)) (hcaps a ha)
        else if a.val = k - 1 then 1 else 0
      let N := columnUpdate A ⟨k, hkn⟩
      let s := scalarSignValue (q (k+1)).2
      lineCapF (horizontalMove q ε) n = (1 + s • N) * lineCapF Q n ∧
      lineCapF (horizontalMove q ε) n - lineCapF Q n = s • N * lineCapF Q n ∧
      N * N = 0 := by
  obtain ⟨ρ, hρ, hjump⟩ := exists_lineCap_F_jump q n k hk hkn τ hτ hzero
    hcollinear hlast hisolated
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  dsimp only
  intro hcaps
  let Q := horizontalMove q (-ε)
  let A : Fin n → ℚ := fun a =>
    if ha : a.val < k - 1 then
      polygonAmplitude (lineCapCore Q a (⟨k - 1, by omega⟩ : Fin n)) (hcaps a ha)
    else if a.val = k - 1 then 1 else 0
  let N := columnUpdate A ⟨k, hkn⟩
  have hA : (fun a : Fin n =>
      endpointMarked (lineCapNear q n) (polygonSignArray Q) a.val (k-1)) = A := by
    funext a
    by_cases ha : a.val < k - 1
    · simpa only [A, dif_pos ha] using
        prefix_marked_eq_amplitude hRI (lineCapNear q n) Q n a ⟨k-1, by omega⟩ ha (hcaps a ha)
    · by_cases heq : a.val = k - 1
      · simp only [A, dif_neg ha, if_pos heq]
        simpa [heq] using prefix_one_edge_unit (lineCapNear q n) Q a.val
      · have hnot : ¬ a.val ≤ k - 1 := by omega
        simp [A, ha, heq, endpointMarked, hnot]
  have hm := hjump ε hε hερ
  change lineCapF (horizontalMove q ε) n =
    (1 + scalarSignValue (q (k+1)).2 • columnUpdate
      (fun a : Fin n => endpointMarked (lineCapNear q n)
        (polygonSignArray Q) a.val (k-1)) ⟨k, hkn⟩) * lineCapF Q n at hm
  rw [hA] at hm
  have hAj : A ⟨k,hkn⟩ = 0 := by
    simp [A, show ¬ k < k - 1 by omega, show k ≠ k - 1 by omega]
  refine ⟨hm, ?_, ?_⟩
  · rw [hm, add_mul, one_mul]
    exact add_sub_cancel_left _ _
  · change N * N = 0
    ext a b
    simp [N, columnUpdate, Matrix.mul_apply, ite_mul, hAj]

end DirectGLSSW.SourceActualEndpointUpdate

