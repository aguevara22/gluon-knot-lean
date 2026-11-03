import DirectGLSSW.GlobalCapIntertwining
import DirectGLSSW.CapCrossingEvent
import DirectGLSSW.CapCrossingEventStability
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DirectGLSSW.CapCrossingVectors

open DirectGLSSW
open scoped BigOperators
open DirectGLSSW.GlobalCapIntertwining
open DirectGLSSW.GlobalCapAlgebra
open DirectGLSSW.CapCrossingEvent

/-- The actual selected F row and U column have zero pairing below the diagonal. -/
theorem lineCap_FU_entry_below (q : ℕ → PlanarPoint ℝ) (n k : ℕ)
    (hk : 0 < k) (hkn : k < n) :
    (∑ l : Fin n,
      GlobalCapIntertwining.lineCapF q n ⟨k, hkn⟩ l *
        GlobalCapIntertwining.lineCapU q n l ⟨k - 1, by omega⟩) = 0 := by
  have hbelow : GlobalCapAlgebra.lineCapPairing q n
      ⟨k, hkn⟩ ⟨k - 1, by omega⟩ = 0 := by
    apply GlobalCapAlgebra.lineCapPairing_below
    simp
    omega
  have hentry : (GlobalCapIntertwining.lineCapF q n *
      GlobalCapIntertwining.lineCapU q n) ⟨k, hkn⟩ ⟨k - 1, by omega⟩ = 0 := by
    rw [← GlobalCapIntertwining.lineCapPairing_eq_FU]
    exact hbelow
  simpa only [Matrix.mul_apply] using hentry

/-- The actual F row is a left eigenvector of J, from FJ=SF. -/
theorem lineCap_F_row_J_eigen (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (j i : Fin n) :
    (∑ l : Fin n,
      GlobalCapIntertwining.lineCapF q n j l *
        GlobalCapIntertwining.lineCapJ q n l i) =
      GlobalCapAlgebra.lineCapHeights q n j * GlobalCapIntertwining.lineCapF q n j i := by
  have hmatrix := GlobalCapIntertwining.lineCap_FJ_eq_SF q n
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M j i) hmatrix
  simpa [Matrix.mul_apply, GlobalCapIntertwining.lineCapS,
    GlobalCapAlgebra.lineCapHeights, Matrix.diagonal_apply] using hentry

/-- The actual U column is a right eigenvector of J, from JU=US. -/
theorem lineCap_U_column_J_eigen (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (hzero : (q 0).2 = 0)
    (hothers : ∀ l, 0 < l → l ≤ n → (q l).2 ≠ 0)
    (hcaps : ∀ a b : Fin n, a.val < b.val →
      CyclicGeneric (GlobalCapEntry.lineCapCore q a b))
    (i b : Fin n) :
    (∑ l : Fin n,
      GlobalCapIntertwining.lineCapJ q n i l *
        GlobalCapIntertwining.lineCapU q n l b) =
      GlobalCapIntertwining.lineCapU q n i b * GlobalCapAlgebra.lineCapHeights q n b := by
  have hmatrix := GlobalCapIntertwining.lineCap_JU_eq_US hRI q n hzero hothers hcaps
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M i b) hmatrix
  simpa [Matrix.mul_apply, GlobalCapIntertwining.lineCapS,
    GlobalCapAlgebra.lineCapHeights, Matrix.diagonal_apply] using hentry

private theorem horizontalMove_height (q : ℕ → PlanarPoint ℝ) (t : ℝ) (a : ℕ) :
    (CapCrossingEvent.horizontalMove q t a).2 = (q a).2 := by
  by_cases ha : a = 0 <;> simp [CapCrossingEvent.horizontalMove,
    EndpointEventGeometry.moveEndpoint, ha]

private theorem scalarSignValue_negative_mul (τ x : ℝ) (hτ : τ < 0) :
    scalarSignValue (τ * x) = -scalarSignValue x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hm : 0 < τ * x := mul_pos_of_neg_of_neg hτ hx
    simp [scalarSignValue, ne_of_lt hx, ne_of_gt hm, hx, not_lt_of_gt hm]
  · subst x
    simp [scalarSignValue]
  · have hm : τ * x < 0 := mul_neg_of_neg_of_pos hτ hx
    simp [scalarSignValue, ne_of_gt hx, ne_of_lt hm, not_lt_of_gt hx, hm]

private theorem crossing_pair_heights
    (q : ℕ → PlanarPoint ℝ) (n k : ℕ) (hk : 0 < k) (hkn : k < n)
    (τ : ℝ) (hτ : τ < 0) (hzero : (q 0).2 = 0)
    (hcollinear : q k = q 0 + τ • (q (k+1) - q 0)) :
    GlobalCapAlgebra.lineCapHeights q n ⟨k-1, by omega⟩ =
        -scalarSignValue (q (k+1)).2 ∧
    GlobalCapAlgebra.lineCapHeights q n ⟨k, hkn⟩ =
        scalarSignValue (q (k+1)).2 := by
  have hy : (q k).2 = τ * (q (k+1)).2 := by
    have hcoord := congrArg (fun p : PlanarPoint ℝ => p.2) hcollinear
    simpa [hzero] using hcoord
  have hkidx : k - 1 + 1 = k := by omega
  constructor
  · simp only [GlobalCapAlgebra.lineCapHeights, hkidx]
    rw [hy]
    exact scalarSignValue_negative_mul τ (q (k+1)).2 hτ
  · simp [GlobalCapAlgebra.lineCapHeights]

/-- On either sufficiently close moved side, the exact-event F row and U column
are eigenvectors of that side's actual J matrix. Side genericity is explicit;
no genericity is imposed at the degenerate event. -/
theorem exists_lineCap_crossing_side_eigenidentities
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n k : ℕ) (hk : 0 < k) (hkn : k < n)
    (τ : ℝ) (hτ : τ < 0) (hzero : (q 0).2 = 0)
    (hcollinear : q k = q 0 + τ • (q (k+1) - q 0))
    (hlast : (q (k+1)).2 ≠ 0)
    (hothers : ∀ l, 0 < l → l ≤ n → (q l).2 ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ k+1) → polygonHDet q a b c ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
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
            GlobalCapIntertwining.lineCapU q n i ⟨k-1, by omega⟩) := by
  have hpairs := crossing_pair_heights q n k hk hkn τ hτ hzero hcollinear
  obtain ⟨ρ, hρ, hstable⟩ :=
    CapCrossingEventStability.exists_lineCap_FU_stability_radius
      q n k hk hkn τ hτ hzero hcollinear hlast hisolated
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ hcapsPlus hcapsMinus
  have hplusZero : (CapCrossingEvent.horizontalMove q ε 0).2 = 0 :=
    horizontalMove_height q ε 0 |>.trans hzero
  have hminusZero : (CapCrossingEvent.horizontalMove q (-ε) 0).2 = 0 :=
    horizontalMove_height q (-ε) 0 |>.trans hzero
  have hplusOthers : ∀ l, 0 < l → l ≤ n →
      (CapCrossingEvent.horizontalMove q ε l).2 ≠ 0 := by
    intro l hlo hle
    simpa only [horizontalMove_height q ε l] using hothers l hlo hle
  have hminusOthers : ∀ l, 0 < l → l ≤ n →
      (CapCrossingEvent.horizontalMove q (-ε) l).2 ≠ 0 := by
    intro l hlo hle
    simpa only [horizontalMove_height q (-ε) l] using hothers l hlo hle
  have hplusStab := hstable ε hε hερ
  let j : Fin n := ⟨k, hkn⟩
  let b : Fin n := ⟨k-1, by omega⟩
  have hheightPlusJ : lineCapHeights (CapCrossingEvent.horizontalMove q ε) n j =
      scalarSignValue (q (k+1)).2 := by
    simp [j, GlobalCapAlgebra.lineCapHeights, horizontalMove_height]
  have hheightMinusJ : lineCapHeights (CapCrossingEvent.horizontalMove q (-ε)) n j =
      scalarSignValue (q (k+1)).2 := by
    simp [j, GlobalCapAlgebra.lineCapHeights, horizontalMove_height]
  have hheightPlusB : lineCapHeights (CapCrossingEvent.horizontalMove q ε) n b =
      -scalarSignValue (q (k+1)).2 := by
    simpa [b, GlobalCapAlgebra.lineCapHeights, horizontalMove_height] using hpairs.1
  have hheightMinusB : lineCapHeights (CapCrossingEvent.horizontalMove q (-ε)) n b =
      -scalarSignValue (q (k+1)).2 := by
    simpa [b, GlobalCapAlgebra.lineCapHeights, horizontalMove_height] using hpairs.1
  refine ⟨?_, ?_⟩
  · intro i
    have hFplus : ∀ l : Fin n,
        lineCapF (CapCrossingEvent.horizontalMove q ε) n j l = lineCapF q n j l :=
      fun l => (hplusStab.1 l).1
    have hFminus : ∀ l : Fin n,
        lineCapF (CapCrossingEvent.horizontalMove q (-ε)) n j l = lineCapF q n j l :=
      fun l => (hplusStab.1 l).2
    have hrowPlus := lineCap_F_row_J_eigen
      (CapCrossingEvent.horizontalMove q ε) n j i
    have hrowMinus := lineCap_F_row_J_eigen
      (CapCrossingEvent.horizontalMove q (-ε)) n j i
    constructor
    · calc
        (∑ l : Fin n, lineCapF q n j l * lineCapJ
            (CapCrossingEvent.horizontalMove q ε) n l i) =
          ∑ l : Fin n, lineCapF (CapCrossingEvent.horizontalMove q ε) n j l *
            lineCapJ (CapCrossingEvent.horizontalMove q ε) n l i := by
              apply Finset.sum_congr rfl
              intro l _
              rw [hFplus l]
        _ = lineCapHeights (CapCrossingEvent.horizontalMove q ε) n j *
            lineCapF (CapCrossingEvent.horizontalMove q ε) n j i := hrowPlus
        _ = scalarSignValue (q (k+1)).2 * lineCapF q n j i := by
              rw [hheightPlusJ, hFplus i]
    · calc
        (∑ l : Fin n, lineCapF q n j l * lineCapJ
            (CapCrossingEvent.horizontalMove q (-ε)) n l i) =
          ∑ l : Fin n, lineCapF (CapCrossingEvent.horizontalMove q (-ε)) n j l *
            lineCapJ (CapCrossingEvent.horizontalMove q (-ε)) n l i := by
              apply Finset.sum_congr rfl
              intro l _
              rw [hFminus l]
        _ = lineCapHeights (CapCrossingEvent.horizontalMove q (-ε)) n j *
            lineCapF (CapCrossingEvent.horizontalMove q (-ε)) n j i := hrowMinus
        _ = scalarSignValue (q (k+1)).2 * lineCapF q n j i := by
              rw [hheightMinusJ, hFminus i]
  · intro i
    have hUplus : ∀ l : Fin n,
        lineCapU (CapCrossingEvent.horizontalMove q ε) n l b = lineCapU q n l b :=
      fun l => (hplusStab.2 l).1
    have hUminus : ∀ l : Fin n,
        lineCapU (CapCrossingEvent.horizontalMove q (-ε)) n l b = lineCapU q n l b :=
      fun l => (hplusStab.2 l).2
    have hcolPlus := lineCap_U_column_J_eigen hRI
      (CapCrossingEvent.horizontalMove q ε) n hplusZero hplusOthers hcapsPlus i b
    have hcolMinus := lineCap_U_column_J_eigen hRI
      (CapCrossingEvent.horizontalMove q (-ε)) n hminusZero hminusOthers hcapsMinus i b
    constructor
    · calc
        (∑ l : Fin n, lineCapJ (CapCrossingEvent.horizontalMove q ε) n i l *
            lineCapU q n l b) =
          ∑ l : Fin n, lineCapJ (CapCrossingEvent.horizontalMove q ε) n i l *
            lineCapU (CapCrossingEvent.horizontalMove q ε) n l b := by
              apply Finset.sum_congr rfl
              intro l _
              rw [hUplus l]
        _ = lineCapU (CapCrossingEvent.horizontalMove q ε) n i b *
            lineCapHeights (CapCrossingEvent.horizontalMove q ε) n b := hcolPlus
        _ = -scalarSignValue (q (k+1)).2 * lineCapU q n i b := by
              rw [hUplus i, hheightPlusB]
              ring
    · calc
        (∑ l : Fin n, lineCapJ (CapCrossingEvent.horizontalMove q (-ε)) n i l *
            lineCapU q n l b) =
          ∑ l : Fin n, lineCapJ (CapCrossingEvent.horizontalMove q (-ε)) n i l *
            lineCapU (CapCrossingEvent.horizontalMove q (-ε)) n l b := by
              apply Finset.sum_congr rfl
              intro l _
              rw [hUminus l]
        _ = lineCapU (CapCrossingEvent.horizontalMove q (-ε)) n i b *
            lineCapHeights (CapCrossingEvent.horizontalMove q (-ε)) n b := hcolMinus
        _ = -scalarSignValue (q (k+1)).2 * lineCapU q n i b := by
              rw [hUminus i, hheightMinusB]
              ring









end DirectGLSSW.CapCrossingVectors
