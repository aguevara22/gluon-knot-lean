import DirectGLSSW.GlobalCapIntertwining
import DirectGLSSW.CapCrossingAlgebra
import DirectGLSSW.EndpointGeometricMatrix
import DirectGLSSW.HorizontalShortEdge
import DirectGLSSW.EndpointMarkedCap

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW.CapCrossingEvent
open DirectGLSSW.GlobalCapIntertwining DirectGLSSW.GlobalCapAlgebra
open DirectGLSSW.EndpointCurrent DirectGLSSW.EndpointEventGeometry
open DirectGLSSW.CapCrossingAlgebra

def horizontalMove (q : ℕ → PlanarPoint ℝ) (t : ℝ) :=
  EndpointEventGeometry.moveEndpoint q (1, 0) t

private theorem horizontalMove_height (q : ℕ → PlanarPoint ℝ) (t : ℝ) (a : ℕ) :
    (horizontalMove q t a).2 = (q a).2 := by
  by_cases ha : a = 0 <;> simp [horizontalMove, moveEndpoint, ha]

private theorem horizontalMove_near (q : ℕ → PlanarPoint ℝ) (t : ℝ) (n : ℕ) :
    lineCapNear (horizontalMove q t) n = lineCapNear q n := by
  funext k
  simp only [lineCapNear, horizontalMove_height]

private theorem horizontalMove_heights (q : ℕ → PlanarPoint ℝ) (t : ℝ) (n : ℕ) :
    lineCapHeights (horizontalMove q t) n = lineCapHeights q n := by
  funext k
  simp only [lineCapHeights, horizontalMove_height]

private theorem lineCapF_apply (q : ℕ → PlanarPoint ℝ) (n : ℕ) (a b : Fin n) :
    lineCapF q n a b = endpointCurrent (lineCapNear q n) (polygonSignArray q) a.val b.val := by
  have hf : lineCapF q n =
      (fun a b : Fin n => endpointCurrent (lineCapNear q n) (polygonSignArray q) a.val b.val) := by
    rw [lineCapF_eq_finiteInverse]
    exact (endpointCurrent_eq_finiteInverse (lineCapNear q n) (polygonSignArray q) n).symm
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M a b) hf

private theorem crossing_height_relation
    (q : ℕ → PlanarPoint ℝ) (k : ℕ) (τ : ℝ) (hzero : (q 0).2 = 0)
    (hcollinear : q k = q 0 + τ • (q (k+1) - q 0)) :
    (q k).2 = τ * (q (k+1)).2 := by
  have h := congrArg (fun p : PlanarPoint ℝ => p.2) hcollinear
  simpa [hzero] using h

private theorem crossing_transverse_sign
    (q : ℕ → PlanarPoint ℝ) (k : ℕ) (τ : ℝ) (hτ : τ < 0)
    (hzero : (q 0).2 = 0)
    (hcollinear : q k = q 0 + τ • (q (k+1) - q 0))
    (hlast : (q (k+1)).2 ≠ 0) :
    planarDet (q k - q (k+1)) (1, 0) ≠ 0 ∧
      scalarSignValue (planarDet (q k - q (k+1)) (1, 0)) =
        scalarSignValue (q (k+1)).2 := by
  have hv := crossing_height_relation q k τ hzero hcollinear
  have hfac : 0 < 1 - τ := by linarith
  have hd : planarDet (q k - q (k+1)) (1, 0) = (1 - τ) * (q (k+1)).2 := by
    simp [planarDet, hv]
    ring
  rw [hd]
  exact ⟨mul_ne_zero (ne_of_gt hfac) hlast,
    HorizontalShortEdge.scalarSignValue_positive_mul (1-τ) (q (k+1)).2 hfac⟩

private theorem scalarSignValue_negative_mul (τ x : ℝ) (hτ : τ < 0) :
    scalarSignValue (τ * x) = -scalarSignValue x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hm : 0 < τ * x := mul_pos_of_neg_of_neg hτ hx
    simp [scalarSignValue, ne_of_lt hx, ne_of_gt hm, hx, not_lt_of_gt hm]
  · subst x
    simp [scalarSignValue]
  · have hm : τ * x < 0 := mul_neg_of_neg_of_pos hτ hx
    simp [scalarSignValue, ne_of_gt hx, ne_of_lt hm, not_lt_of_gt hx, hm]

theorem exists_lineCap_F_jump
    (q : ℕ → PlanarPoint ℝ) (n k : ℕ) (hk : 0 < k) (hkn : k < n)
    (τ : ℝ) (hτ : τ < 0) (hzero : (q 0).2 = 0)
    (hcollinear : q k = q 0 + τ • (q (k+1) - q 0))
    (hlast : (q (k+1)).2 ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ k+1) → polygonHDet q a b c ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      lineCapF (horizontalMove q ε) n =
        (1 + scalarSignValue (q (k+1)).2 • columnUpdate
          (fun a : Fin n => endpointMarked (lineCapNear q n)
            (polygonSignArray (horizontalMove q (-ε))) a.val (k-1)) ⟨k, hkn⟩) *
        lineCapF (horizontalMove q (-ε)) n := by
  obtain ⟨htransverse, hsign⟩ := crossing_transverse_sign q k τ hτ hzero hcollinear hlast
  obtain ⟨ρ, hρ, hdata⟩ := exists_endpoint_current_matrix_event_negative_positive
    q (1, 0) (lineCapNear q n) n hk (by omega : k < k+1) (by omega : k+1 ≤ n)
    τ hcollinear htransverse hisolated hτ
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  obtain ⟨_, _, hmat⟩ := hdata ε hε hερ
  have hcurrent (t : ℝ) (a b : Fin n) :
      endpointCurrent (lineCapNear q n) (polygonSignArray (moveEndpoint q (1, 0) t))
        a.val b.val = lineCapF (horizontalMove q t) n a b := by
    rw [lineCapF_apply, horizontalMove_near]
    rfl
  ext a i
  have h := hmat a i
  simp only [hsign, source, if_true, Nat.add_sub_cancel, mul_one] at h
  rw [hcurrent ε a i, hcurrent (-ε) a i, hcurrent (-ε) ⟨k, hkn⟩ i] at h
  have hup :
      ((1 + scalarSignValue (q (k+1)).2 • columnUpdate
          (fun a : Fin n => endpointMarked (lineCapNear q n)
            (polygonSignArray (horizontalMove q (-ε))) a.val (k-1)) ⟨k, hkn⟩) *
        lineCapF (horizontalMove q (-ε)) n) a i =
      lineCapF (horizontalMove q (-ε)) n a i +
        scalarSignValue (q (k+1)).2 *
          endpointMarked (lineCapNear q n) (polygonSignArray (horizontalMove q (-ε)))
            a.val (k-1) * lineCapF (horizontalMove q (-ε)) n ⟨k, hkn⟩ i := by
    simp only [add_mul, one_mul, smul_mul_assoc, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    simp only [Matrix.mul_apply, columnUpdate, ite_mul, zero_mul]
    simp
    ring
  rw [hup]
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

theorem exists_lineCap_J_jump
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
        (lineCapJ (horizontalMove q ε) n - lineCapJ (horizontalMove q (-ε)) n) i l =
        2 * scalarSignValue (q (k+1)).2 *
          lineCapU (horizontalMove q (-ε)) n i ⟨k-1, by omega⟩ *
          lineCapF (horizontalMove q (-ε)) n ⟨k, hkn⟩ l := by
  obtain ⟨ρ, hρ, hjump⟩ := exists_lineCap_F_jump q n k hk hkn τ hτ hzero
    hcollinear (hothers (k+1) (by omega) (by omega)) hisolated
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ hcaps
  let q₀ := horizontalMove q (-ε)
  let q₁ := horizontalMove q ε
  let b : Fin n := ⟨k-1, by omega⟩
  let j : Fin n := ⟨k, hkn⟩
  let s := scalarSignValue (q (k+1)).2
  let a : Fin n → ℚ := fun i => endpointMarked (lineCapNear q n)
    (polygonSignArray q₀) i.val (k-1)
  have hzero₀ : (q₀ 0).2 = 0 := by
    simpa only [q₀, horizontalMove_height] using hzero
  have hothers₀ : ∀ l, 0 < l → l ≤ n → (q₀ l).2 ≠ 0 := by
    simpa only [q₀, horizontalMove_height] using hothers
  have hb : lineCapHeights q₀ n b = -s := by
    have hv := crossing_height_relation q k τ hzero hcollinear
    have hi : k-1+1 = k := by omega
    simp only [lineCapHeights, q₀, b, horizontalMove_height, hi, hv]
    exact scalarSignValue_negative_mul τ (q (k+1)).2 hτ
  have hj : lineCapHeights q₀ n j = s := by
    simp only [lineCapHeights, q₀, j, horizontalMove_height, s]
  have hazero : a j = 0 := by
    have hnot : ¬ k ≤ k-1 := by omega
    simp [a, j, endpointMarked, hnot]
  have hcolumn : ∀ i : Fin n,
      (lineCapF q₀ n * lineCapU q₀ n) i b =
        ((lineCapHeights q₀ n i - s) / 2) * a i := by
    intro i
    rw [← lineCapPairing_eq_FU]
    have hcap : i.val < b.val → CyclicGeneric (GlobalCapEntry.lineCapCore q₀ i b) := by
      intro hi
      exact hcaps i hi
    rw [EndpointMarkedCap.lineCapPairing_endpointMarked hRI q₀ n hzero₀ hothers₀ i b hcap,
      hb]
    have hnear : (fun l => scalarSignValue (q₀ l).2) = lineCapNear q n := by
      funext l
      simp only [q₀, horizontalMove_height, lineCapNear]
    simp only [hnear, a, b, sub_eq_add_neg]
  have hS : lineCapS q₁ n = lineCapS q₀ n := by
    simp only [lineCapS, q₁, q₀, horizontalMove_heights]
  have heq := rank_one_conjugation_jump
    (lineCapF q₀ n) (lineCapF q₁ n) (1 + lineCapC q₀ n) (1 + lineCapC q₁ n)
    (lineCapU q₀ n) (lineCapHeights q₀ n) a b j s
    (lineCapF_right_inverse q₀ n) (lineCapF_left_inverse q₀ n)
    (lineCapF_left_inverse q₁ n) (hjump ε hε hερ) hazero hj hcolumn
  intro i l
  change (lineCapJ q₁ n - lineCapJ q₀ n) i l =
    2 * s * lineCapU q₀ n i b * lineCapF q₀ n j l
  unfold lineCapJ
  rw [hS]
  exact heq i l












end DirectGLSSW.CapCrossingEvent
