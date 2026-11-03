import DirectGLSSW.EndpointGeometricMatrix
import DirectGLSSW.HorizontalShortEdge
import DirectGLSSW.EndpointMarkedCap
import DirectGLSSW.GlobalCapIntertwining
import DirectGLSSW.CapCrossingEvent
import Mathlib.Algebra.Module.Prod

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW.CapVirtualEventInvariance

open DirectGLSSW
open DirectGLSSW.EndpointEventGeometry
open DirectGLSSW.EndpointCurrent
open DirectGLSSW.GlobalCapAlgebra
open DirectGLSSW.GlobalCapIntertwining
open DirectGLSSW.CapCrossingEvent
open DirectGLSSW.CapCrossingAlgebra

private theorem horizontalMove_height (q : ℕ → PlanarPoint ℝ) (t : ℝ) (a : ℕ) :
    (horizontalMove q t a).2 = (q a).2 := by
  by_cases ha : a = 0 <;> simp [horizontalMove, moveEndpoint, ha]

private theorem horizontalMove_near (q : ℕ → PlanarPoint ℝ) (t : ℝ) (n : ℕ) :
    lineCapNear (horizontalMove q t) n = lineCapNear q n := by
  funext k
  simp only [lineCapNear, horizontalMove_height]

private theorem lineCapF_apply (q : ℕ → PlanarPoint ℝ) (n : ℕ) (a b : Fin n) :
    lineCapF q n a b =
      endpointCurrent (lineCapNear q n) (polygonSignArray q) a.val b.val := by
  have hf : lineCapF q n =
      (fun a b : Fin n => endpointCurrent (lineCapNear q n)
        (polygonSignArray q) a.val b.val) := by
    rw [lineCapF_eq_finiteInverse]
    exact (endpointCurrent_eq_finiteInverse (lineCapNear q n)
      (polygonSignArray q) n).symm
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M a b) hf

private theorem crossing_height_relation
    (q : ℕ → PlanarPoint ℝ) (k : ℕ) (τ : ℝ) (hzero : (q 0).2 = 0)
    (hcollinear : q k = q 0 + τ • (q (k+1) - q 0)) :
    (q k).2 = τ * (q (k+1)).2 := by
  have h := congrArg (fun p : PlanarPoint ℝ => p.2) hcollinear
  simpa [hzero] using h

private theorem crossing_transverse_formula
    (q : ℕ → PlanarPoint ℝ) (k j : ℕ) (τ : ℝ)
    (hzero : (q 0).2 = 0)
    (hcollinear : q k = q 0 + τ • (q j - q 0)) :
    planarDet (q k - q j) (1, 0) = (1 - τ) * (q j).2 := by
  have hv := congrArg (fun p : PlanarPoint ℝ => p.2) hcollinear
  have hky : (q k).2 = τ * (q j).2 := by simpa [hzero] using hv
  simp [planarDet, hky]
  ring

private theorem crossing_transverse
    (q : ℕ → PlanarPoint ℝ) (k j : ℕ) (τ : ℝ)
    (hzero : (q 0).2 = 0) (hjheight : (q j).2 ≠ 0)
    (hcollinear : q k = q 0 + τ • (q j - q 0)) (hτ1 : τ ≠ 1) :
    planarDet (q k - q j) (1, 0) ≠ 0 := by
  rw [crossing_transverse_formula q k j τ hzero hcollinear]
  exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hτ1)) hjheight

private theorem scalarSignValue_pos_mul (x y : ℝ) (hx : 0 < x) :
    scalarSignValue (x * y) = scalarSignValue y := by
  exact HorizontalShortEdge.scalarSignValue_positive_mul x y hx

private theorem scalarSignValue_neg_mul (x y : ℝ) (hx : x < 0) :
    scalarSignValue (x * y) = -scalarSignValue y := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have hp : 0 < x * y := mul_pos_of_neg_of_neg hx hy
    simp [scalarSignValue, ne_of_lt hy, ne_of_gt hp, hy, not_lt_of_gt hp]
  · subst y
    simp [scalarSignValue]
  · have hn : x * y < 0 := mul_neg_of_neg_of_pos hx hy
    simp [scalarSignValue, ne_of_gt hy, ne_of_lt hn, not_lt_of_gt hy, hn]

private theorem lineCapS_horizontal_eq (q : ℕ → PlanarPoint ℝ) (t : ℝ) (n : ℕ) :
    lineCapS (horizontalMove q t) n = lineCapS q n := by
  ext i
  simp only [lineCapS, Matrix.diagonal_apply, lineCapHeights,
    horizontalMove_height]

private theorem lineCapF_horizontal_current
    (q : ℕ → PlanarPoint ℝ) (t : ℝ) (n : ℕ) (a b : Fin n) :
    lineCapF (horizontalMove q t) n a b =
      endpointCurrent (lineCapNear q n) (polygonSignArray (horizontalMove q t))
        a.val b.val := by
  rw [lineCapF_apply, horizontalMove_near]

private theorem lineCapF_horizontal_eq_of_currents
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (t : ℝ) (H : TripleArray)
    (hH : polygonSignArray (horizontalMove q t) = H) :
    lineCapF (horizontalMove q t) n =
      fun a b => endpointCurrent (lineCapNear q n) H a.val b.val := by
  ext a b
  rw [lineCapF_horizontal_current, hH]

private theorem gap_source_zero {k j : ℕ} (hgap : k + 1 < j) : source k j = 0 := by
  simp [source, show j ≠ k + 1 by omega]

private theorem horizontal_move_near_data (q : ℕ → PlanarPoint ℝ) (n : ℕ) (t : ℝ) :
    lineCapNear (horizontalMove q t) n = lineCapNear q n :=
  horizontalMove_near q t n

private theorem scalarSignValue_one (x : ℝ) (hx : 0 < x) : scalarSignValue x = 1 := by
  simp [scalarSignValue, ne_of_gt hx, not_lt_of_gt hx]

private theorem scalarSignValue_minus_one (x : ℝ) (hx : x < 0) : scalarSignValue x = -1 := by
  simp [scalarSignValue, ne_of_lt hx, hx]

private theorem height_k_eq_j_of_positive
    (q : ℕ → PlanarPoint ℝ) (k j : ℕ) (τ : ℝ)
    (hzero : (q 0).2 = 0) (hcollinear : q k = q 0 + τ • (q j - q 0))
    (hτ : 0 < τ) :
    scalarSignValue (q k).2 = scalarSignValue (q j).2 := by
  have hv := congrArg (fun p : PlanarPoint ℝ => p.2) hcollinear
  have hky : (q k).2 = τ * (q j).2 := by simpa [hzero] using hv
  rw [hky]
  exact scalarSignValue_pos_mul τ (q j).2 hτ

private theorem height_k_opposite_sign_of_negative
    (q : ℕ → PlanarPoint ℝ) (k j : ℕ) (τ : ℝ)
    (hzero : (q 0).2 = 0) (hcollinear : q k = q 0 + τ • (q j - q 0))
    (hτ : τ < 0) :
    scalarSignValue (q k).2 = -scalarSignValue (q j).2 := by
  have hv := congrArg (fun p : PlanarPoint ℝ => p.2) hcollinear
  have hky : (q k).2 = τ * (q j).2 := by simpa [hzero] using hv
  rw [hky]
  exact scalarSignValue_neg_mul τ (q j).2 hτ

private theorem transverse_sign_of_tau_between
    (q : ℕ → PlanarPoint ℝ) (k j : ℕ) (τ : ℝ)
    (hzero : (q 0).2 = 0) (hjheight : (q j).2 ≠ 0)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (hτ : 0 < τ) (hτ1 : 0 < 1 - τ) :
    scalarSignValue (planarDet (q k-q j) (1,0)) = scalarSignValue (q j).2 := by
  rw [crossing_transverse_formula q k j τ hzero hcollinear]
  exact scalarSignValue_pos_mul (1-τ) (q j).2 hτ1

private theorem transverse_sign_of_tau_above_one
    (q : ℕ → PlanarPoint ℝ) (k j : ℕ) (τ : ℝ)
    (hzero : (q 0).2 = 0) (hjheight : (q j).2 ≠ 0)
    (hcollinear : q k = q 0 + τ • (q j - q 0)) (hτ : 1 < τ) :
    scalarSignValue (planarDet (q k-q j) (1,0)) = -scalarSignValue (q j).2 := by
  rw [crossing_transverse_formula q k j τ hzero hcollinear]
  have hneg : 1-τ < 0 := by linarith
  exact scalarSignValue_neg_mul (1-τ) (q j).2 hneg

private theorem transverse_sign_of_tau_negative
    (q : ℕ → PlanarPoint ℝ) (k j : ℕ) (τ : ℝ)
    (hzero : (q 0).2 = 0) (hjheight : (q j).2 ≠ 0)
    (hcollinear : q k = q 0 + τ • (q j - q 0)) (hτ : τ < 0) :
    scalarSignValue (planarDet (q k-q j) (1,0)) = scalarSignValue (q j).2 := by
  rw [crossing_transverse_formula q k j τ hzero hcollinear]
  have hpos : 0 < 1-τ := by linarith
  exact scalarSignValue_pos_mul (1-τ) (q j).2 hpos

private theorem columnUpdate_mul_diagonal
    {n : ℕ} (a h : Fin n → ℚ) (j : Fin n) (s : ℚ) (hs : h j = s) :
    columnUpdate a j * Matrix.diagonal h = s • columnUpdate a j := by
  ext i k
  rw [Matrix.mul_diagonal]
  by_cases hk : k = j
  · subst k
    simp [columnUpdate, hs, mul_comm]
  · simp [columnUpdate, hk]

private theorem diagonal_mul_columnUpdate_of_supported_heights
    {n : ℕ} (a h : Fin n → ℚ) (j b : Fin n) (s : ℚ)
    (hs : ∀ i, a i ≠ 0 → h i = s) :
    Matrix.diagonal h * columnUpdate a j = s • columnUpdate a j := by
  ext i k
  rw [Matrix.diagonal_mul]
  by_cases hk : k = j
  · subst k
    by_cases hai : a i = 0
    · simp [columnUpdate, hai]
    · have hh := hs i hai
      simp [columnUpdate, hh]
  · simp [columnUpdate, hk]

private theorem columnUpdate_sq_zero {n : ℕ} (a : Fin n → ℚ) (j : Fin n)
    (ha : a j = 0) : columnUpdate a j * columnUpdate a j = 0 := by
  classical
  ext i k
  rw [Matrix.mul_apply]
  have hsum : (∑ l : Fin n, columnUpdate a j i l * columnUpdate a j l k) =
      columnUpdate a j i j * columnUpdate a j j k := by
    apply Finset.sum_eq_single j
    · intro l hl hlj
      simp [columnUpdate, hlj]
    · simp
  rw [hsum]
  simp [columnUpdate, ha]

private theorem columnUpdate_mul {n : ℕ} (a : Fin n → ℚ) (j : Fin n)
    (F : Matrix (Fin n) (Fin n) ℚ) (i k : Fin n) :
    (columnUpdate a j * F) i k = a i * F j k := by
  simp [Matrix.mul_apply, columnUpdate]

private theorem one_add_columnUpdate_mul {n : ℕ} (a : Fin n → ℚ) (j : Fin n)
    (F : Matrix (Fin n) (Fin n) ℚ) (i k : Fin n) :
    ((1 + columnUpdate a j) * F) i k = F i k + a i * F j k := by
  rw [add_mul, one_mul, Matrix.add_apply, columnUpdate_mul]

private theorem J_equal_of_commuting_update
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (t₀ t₁ : ℝ)
    (T : Matrix (Fin n) (Fin n) ℚ)
    (hF : lineCapF (horizontalMove q t₁) n =
      (1 + T) * lineCapF (horizontalMove q t₀) n)
    (hS : lineCapS (horizontalMove q t₁) n = lineCapS (horizontalMove q t₀) n)
    (hcomm : lineCapS (horizontalMove q t₀) n * T =
      T * lineCapS (horizontalMove q t₀) n)
    (hT2 : T * T = 0) :
    lineCapJ (horizontalMove q t₁) n = lineCapJ (horizontalMove q t₀) n := by
  let F₀ := lineCapF (horizontalMove q t₀) n
  let F₁ := lineCapF (horizontalMove q t₁) n
  let K₀ := 1 + lineCapC (horizontalMove q t₀) n
  let K₁ := 1 + lineCapC (horizontalMove q t₁) n
  let S₀ := lineCapS (horizontalMove q t₀) n
  let S₁ := lineCapS (horizontalMove q t₁) n
  have hF₀K₀ : F₀ * K₀ = 1 := by
    dsimp [F₀, K₀]
    exact lineCapF_right_inverse (horizontalMove q t₀) n
  have hK₁F₁ : K₁ * F₁ = 1 := by
    dsimp [F₁, K₁]
    exact lineCapF_left_inverse (horizontalMove q t₁) n
  have hjump : F₁ = (1 + T) * F₀ := by simpa [F₀, F₁] using hF
  have hnil : T * T = 0 := hT2
  have hquad : T * S₀ * T = 0 := by
    calc
      T * S₀ * T = (S₀ * T) * T := by rw [← hcomm]
      _ = S₀ * (T * T) := by simp [mul_assoc]
      _ = 0 := by rw [hT2]; simp
  have hconj := inverse_conjugation_change F₀ F₁ K₀ K₁ S₀ T
    hF₀K₀ hK₁F₁ hjump hnil hquad
  have hdelta : K₁ * S₀ * F₁ - K₀ * S₀ * F₀ = 0 := by
    rw [hconj]
    have hc : S₀ * T - T * S₀ = 0 := sub_eq_zero.mpr hcomm
    rw [hc]
    simp
  have hS' : S₁ = S₀ := by simpa [S₀, S₁] using hS
  change K₁ * S₁ * F₁ = K₀ * S₀ * F₀
  rw [hS']
  exact sub_eq_zero.mp hdelta

private theorem J_equal_of_F_equal
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (t₀ t₁ : ℝ)
    (hF : lineCapF (horizontalMove q t₁) n = lineCapF (horizontalMove q t₀) n)
    (hS : lineCapS (horizontalMove q t₁) n = lineCapS (horizontalMove q t₀) n) :
    lineCapJ (horizontalMove q t₁) n = lineCapJ (horizontalMove q t₀) n := by
  let F := lineCapF (horizontalMove q t₀) n
  let S := lineCapS (horizontalMove q t₀) n
  let K₀ := 1 + lineCapC (horizontalMove q t₀) n
  let K₁ := 1 + lineCapC (horizontalMove q t₁) n
  have hF₀K₀ : F * K₀ = 1 := by
    dsimp [F, K₀]
    exact lineCapF_right_inverse (horizontalMove q t₀) n
  have hK₁F₀ : K₁ * F = 1 := by
    have h := lineCapF_left_inverse (horizontalMove q t₁) n
    simpa [F, K₀, K₁, hF] using h
  have hK : K₁ = K₀ := by
    calc
      K₁ = K₁ * (F * K₀) := by rw [hF₀K₀, mul_one]
      _ = (K₁ * F) * K₀ := by simp [mul_assoc]
      _ = K₀ := by rw [hK₁F₀, one_mul]
  change K₁ * lineCapS (horizontalMove q t₁) n * lineCapF (horizontalMove q t₁) n =
    K₀ * S * F
  rw [hS, hF, hK]

theorem exists_virtual_lineCapJ_invariant_positive_positive
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (hjn : j ≤ n) (τ : ℝ)
    (hzero : (q 0).2 = 0) (hjheight : (q j).2 ≠ 0)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0)
    (hτ : 0 < τ) (hτ1 : 0 < 1 - τ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric (horizontalMove q ε) n ∧
      ShortEdgeSignStability.CoreHGeneric (horizontalMove q (-ε)) n ∧
      lineCapJ (horizontalMove q ε) n = lineCapJ (horizontalMove q (-ε)) n := by
  have htrans := crossing_transverse q k j τ hzero hjheight hcollinear (by linarith)
  obtain ⟨ρ, hρ, hevent⟩ := exists_endpoint_current_matrix_event_positive_positive
    q (1,0) (lineCapNear q n) n hk hkj hjn τ hcollinear htrans hisolated hτ hτ1
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  obtain ⟨hgplus, hgminus, hcur⟩ := hevent ε hε hερ
  let Hminus := polygonSignArray (moveEndpoint q (1,0) (-ε))
  let c : Fin n := ⟨j-1, by omega⟩
  let A : Fin n → ℚ := fun i =>
    scalarSignValue (planarDet (q k-q j) (1,0)) * source i.val k * source k j
  let T : Matrix (Fin n) (Fin n) ℚ := columnUpdate A c
  have hFjump : lineCapF (horizontalMove q ε) n =
      (1 + T) * lineCapF (horizontalMove q (-ε)) n := by
    ext a b
    have hrow : endpointCurrent (lineCapNear q n)
        (polygonSignArray (horizontalMove q ε)) a.val b.val =
        endpointCurrent (lineCapNear q n) Hminus a.val b.val +
          A a * endpointCurrent (lineCapNear q n) Hminus (j-1) b.val := by
      have hc := hcur a b
      dsimp [A]
      have hc' := sub_eq_iff_eq_add.mp hc
      calc
        _ = scalarSignValue (planarDet (q k-q j) (1,0)) * source a.val k * source k j *
              endpointCurrent (lineCapNear q n) Hminus (j-1) b.val +
              endpointCurrent (lineCapNear q n) Hminus a.val b.val := by
          simpa [Hminus, horizontalMove] using hc'
        _ = endpointCurrent (lineCapNear q n) Hminus a.val b.val +
              A a * endpointCurrent (lineCapNear q n) Hminus (j-1) b.val := by ring
    rw [lineCapF_horizontal_current]
    have hfminus : lineCapF (horizontalMove q (-ε)) n c b =
        endpointCurrent (lineCapNear q n) Hminus (j-1) b.val := by
      rw [lineCapF_horizontal_current]
      rfl
    calc
      endpointCurrent (lineCapNear q n) (polygonSignArray (horizontalMove q ε)) a.val b.val =
          endpointCurrent (lineCapNear q n) Hminus a.val b.val +
            A a * endpointCurrent (lineCapNear q n) Hminus (j-1) b.val := hrow
      _ = ((1 + T) * lineCapF (horizontalMove q (-ε)) n) a b := by
        rw [one_add_columnUpdate_mul A c (lineCapF (horizontalMove q (-ε)) n) a b]
        rw [lineCapF_horizontal_current, hfminus]
        simpa [Hminus, horizontalMove]
  have hSame : lineCapHeights (horizontalMove q (-ε)) n ⟨k-1, by omega⟩ =
      scalarSignValue (q j).2 := by
    simp [lineCapHeights, horizontalMove_height,
      Nat.sub_add_cancel (show 1 ≤ k by omega)]
    exact height_k_eq_j_of_positive q k j τ hzero hcollinear hτ
  have hCol : lineCapHeights (horizontalMove q (-ε)) n c =
      scalarSignValue (q j).2 := by
    simp [c, lineCapHeights, horizontalMove_height,
      Nat.sub_add_cancel (show 1 ≤ j by omega)]
  have hSupported : ∀ i, A i ≠ 0 →
      lineCapHeights (horizontalMove q (-ε)) n i = scalarSignValue (q j).2 := by
    classical
    intro i hi
    have hs : source i.val k ≠ 0 := by
      intro hz
      apply hi
      simp [A, hz]
    have hik : i.val + 1 = k := by
      by_cases hEq : i.val + 1 = k
      · exact hEq
      · have hsource : source i.val k = 0 := by
          simp [source, show k ≠ i.val + 1 by omega]
        exact (hs hsource).elim
    have hheight : lineCapHeights (horizontalMove q (-ε)) n i =
        scalarSignValue (q k).2 := by
      simp [lineCapHeights, horizontalMove_height, hik]
    rw [hheight]
    exact height_k_eq_j_of_positive q k j τ hzero hcollinear hτ
  have hTdiag : T * lineCapS (horizontalMove q (-ε)) n =
      scalarSignValue (q j).2 • T := by
    simpa [T, lineCapS] using columnUpdate_mul_diagonal A
      (lineCapHeights (horizontalMove q (-ε)) n) c (scalarSignValue (q j).2) hCol
  have hdiagT : lineCapS (horizontalMove q (-ε)) n * T =
      scalarSignValue (q j).2 • T := by
    simpa [T, lineCapS] using diagonal_mul_columnUpdate_of_supported_heights A
      (lineCapHeights (horizontalMove q (-ε)) n) c ⟨k-1, by omega⟩
      (scalarSignValue (q j).2) hSupported
  have hcomm : lineCapS (horizontalMove q (-ε)) n * T =
      T * lineCapS (horizontalMove q (-ε)) n := by rw [hdiagT, hTdiag]
  have hAc : A c = 0 := by
    have hjpos : 1 ≤ j := by omega
    have hjk : j ≠ k := by omega
    have hsrc : source (j-1) k = 0 := by
      simp [source, show k ≠ (j-1)+1 by
        simpa [Nat.sub_add_cancel hjpos] using Ne.symm hjk]
    simp [A, c, hsrc]
  have hT2 : T * T = 0 := by simpa [T] using columnUpdate_sq_zero A c hAc
  exact ⟨by simpa [horizontalMove] using hgplus,
    by simpa [horizontalMove] using hgminus,
    J_equal_of_commuting_update q n (-ε) ε T hFjump
      (lineCapS_horizontal_eq q ε n) hcomm hT2⟩

theorem exists_virtual_lineCapJ_invariant_positive_negative
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (hjn : j ≤ n) (τ : ℝ)
    (hzero : (q 0).2 = 0) (hjheight : (q j).2 ≠ 0)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0)
    (hτ : 1 < τ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric (horizontalMove q ε) n ∧
      ShortEdgeSignStability.CoreHGeneric (horizontalMove q (-ε)) n ∧
      lineCapJ (horizontalMove q ε) n = lineCapJ (horizontalMove q (-ε)) n := by
  have hτpos : 0 < τ := by linarith
  have htrans := crossing_transverse q k j τ hzero hjheight hcollinear (by linarith)
  obtain ⟨ρ, hρ, hevent⟩ := exists_endpoint_current_matrix_event_positive_negative
    q (1,0) (lineCapNear q n) n hk hkj hjn τ hcollinear htrans hisolated hτ
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  obtain ⟨hgplus, hgminus, hcur⟩ := hevent ε hε hερ
  let Hminus := polygonSignArray (moveEndpoint q (1,0) (-ε))
  let Hplus := polygonSignArray (moveEndpoint q (1,0) ε)
  let r : Fin n := ⟨k-1, by omega⟩
  let c : Fin n := ⟨j-1, by omega⟩
  let A : Fin n → ℚ := fun i =>
    scalarSignValue (planarDet (q k-q j) (1,0)) * source i.val k *
      markedAmplitude (fun _ l _ => lineCapNear q n l) Hminus k j
  let T : Matrix (Fin n) (Fin n) ℚ := columnUpdate A c
  have hFjump : lineCapF (horizontalMove q ε) n =
      (1 + T) * lineCapF (horizontalMove q (-ε)) n := by
    ext a b
    have hc := hcur a b
    have hrow : endpointCurrent (lineCapNear q n)
        (polygonSignArray (horizontalMove q ε)) a.val b.val =
        endpointCurrent (lineCapNear q n) Hminus a.val b.val +
          A a * endpointCurrent (lineCapNear q n) Hminus (j-1) b.val := by
      dsimp [A]
      have hc' := sub_eq_iff_eq_add.mp hc
      calc
        _ = scalarSignValue (planarDet (q k-q j) (1,0)) * source a.val k *
              markedAmplitude (fun _ l _ => lineCapNear q n l) Hminus k j *
              endpointCurrent (lineCapNear q n) Hminus (j-1) b.val +
              endpointCurrent (lineCapNear q n) Hminus a.val b.val := by
          simpa [Hminus, horizontalMove] using hc'
        _ = endpointCurrent (lineCapNear q n) Hminus a.val b.val +
              A a * endpointCurrent (lineCapNear q n) Hminus (j-1) b.val := by ring
    rw [lineCapF_horizontal_current]
    have hfminus : lineCapF (horizontalMove q (-ε)) n c b =
        endpointCurrent (lineCapNear q n) Hminus (j-1) b.val := by
      rw [lineCapF_horizontal_current]
      rfl
    calc
      endpointCurrent (lineCapNear q n) (polygonSignArray (horizontalMove q ε)) a.val b.val =
          endpointCurrent (lineCapNear q n) Hminus a.val b.val +
            A a * endpointCurrent (lineCapNear q n) Hminus (j-1) b.val := hrow
      _ = ((1 + T) * lineCapF (horizontalMove q (-ε)) n) a b := by
        rw [one_add_columnUpdate_mul A c (lineCapF (horizontalMove q (-ε)) n) a b]
        rw [lineCapF_horizontal_current, hfminus]
        simpa [Hminus, horizontalMove]
  have hSame : lineCapHeights (horizontalMove q (-ε)) n r =
      scalarSignValue (q j).2 := by
    simp [r, lineCapHeights, horizontalMove_height,
      Nat.sub_add_cancel (show 1 ≤ k by omega)]
    exact height_k_eq_j_of_positive q k j τ hzero hcollinear hτpos
  have hCol : lineCapHeights (horizontalMove q (-ε)) n c =
      scalarSignValue (q j).2 := by
    simp [c, lineCapHeights, horizontalMove_height,
      Nat.sub_add_cancel (show 1 ≤ j by omega)]
  have hSupported : ∀ i, A i ≠ 0 →
      lineCapHeights (horizontalMove q (-ε)) n i = scalarSignValue (q j).2 := by
    classical
    intro i hi
    have hs : source i.val k ≠ 0 := by
      intro hz
      apply hi
      simp [A, hz]
    have hik : i.val + 1 = k := by
      by_cases hEq : i.val + 1 = k
      · exact hEq
      · have hsource : source i.val k = 0 := by
          simp [source, show k ≠ i.val + 1 by omega]
        exact (hs hsource).elim
    have hheight : lineCapHeights (horizontalMove q (-ε)) n i =
        scalarSignValue (q k).2 := by
      simp [lineCapHeights, horizontalMove_height, hik]
    rw [hheight]
    exact height_k_eq_j_of_positive q k j τ hzero hcollinear hτpos
  have hTdiag : T * lineCapS (horizontalMove q (-ε)) n =
      scalarSignValue (q j).2 • T := by
    simpa [T, lineCapS] using columnUpdate_mul_diagonal A
      (lineCapHeights (horizontalMove q (-ε)) n) c (scalarSignValue (q j).2) hCol
  have hdiagT : lineCapS (horizontalMove q (-ε)) n * T =
      scalarSignValue (q j).2 • T := by
    simpa [T, lineCapS] using diagonal_mul_columnUpdate_of_supported_heights A
      (lineCapHeights (horizontalMove q (-ε)) n) c r (scalarSignValue (q j).2) hSupported
  have hcomm : lineCapS (horizontalMove q (-ε)) n * T =
      T * lineCapS (horizontalMove q (-ε)) n := by rw [hdiagT, hTdiag]
  have hAc : A c = 0 := by
    have hjpos : 1 ≤ j := by omega
    have hjk : j ≠ k := by omega
    have hsrc : source (j-1) k = 0 := by
      simp [source, show k ≠ (j-1)+1 by
        simpa [Nat.sub_add_cancel hjpos] using Ne.symm hjk]
    simp [A, c, hsrc]
  have hT2 : T * T = 0 := by
    simpa [T] using columnUpdate_sq_zero A c hAc
  exact ⟨by simpa [horizontalMove] using hgplus,
    by simpa [horizontalMove] using hgminus, J_equal_of_commuting_update q n (-ε) ε T
    hFjump (lineCapS_horizontal_eq q ε n) hcomm hT2⟩

theorem exists_virtual_lineCapJ_invariant_negative_gap
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (hgap : k + 1 < j) (hjn : j ≤ n) (τ : ℝ)
    (hzero : (q 0).2 = 0) (hjheight : (q j).2 ≠ 0)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0)
    (hτ : τ < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric (horizontalMove q ε) n ∧
      ShortEdgeSignStability.CoreHGeneric (horizontalMove q (-ε)) n ∧
      lineCapJ (horizontalMove q ε) n = lineCapJ (horizontalMove q (-ε)) n := by
  have htrans := crossing_transverse q k j τ hzero hjheight hcollinear (by linarith)
  obtain ⟨ρ, hρ, hevent⟩ := exists_endpoint_current_matrix_event_negative_positive
    q (1,0) (lineCapNear q n) n hk hkj hjn τ hcollinear htrans hisolated hτ
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  obtain ⟨hgplus, hgminus, hcur⟩ := hevent ε hε hερ
  let Hplus := polygonSignArray (moveEndpoint q (1,0) ε)
  let Hminus := polygonSignArray (moveEndpoint q (1,0) (-ε))
  have hcur0 (a b : Fin n) :
      endpointCurrent (lineCapNear q n) Hplus a.val b.val =
        endpointCurrent (lineCapNear q n) Hminus a.val b.val := by
    have hc := hcur a b
    have hs0 : source k j = 0 := gap_source_zero hgap
    have hformula : scalarSignValue (planarDet (q k-q j) (1,0)) *
        endpointMarked (lineCapNear q n)
          (polygonSignArray (moveEndpoint q (1,0) (-ε))) a.val (k-1) * source k j *
        endpointCurrent (lineCapNear q n)
          (polygonSignArray (moveEndpoint q (1,0) (-ε))) (j-1) b.val = 0 := by simp [hs0]
    have heq := sub_eq_iff_eq_add.mp hc
    rw [hformula] at heq
    simpa [Hplus, Hminus] using heq
  have hF : lineCapF (horizontalMove q ε) n = lineCapF (horizontalMove q (-ε)) n := by
    ext a b
    rw [lineCapF_horizontal_current, lineCapF_horizontal_current]
    exact hcur0 a b
  exact ⟨by simpa [horizontalMove] using hgplus,
    by simpa [horizontalMove] using hgminus,
    J_equal_of_F_equal q n (-ε) ε hF (lineCapS_horizontal_eq q ε n)⟩






























end DirectGLSSW.CapVirtualEventInvariance
