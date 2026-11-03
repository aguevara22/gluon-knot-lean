import DirectGLSSW.GlobalCapIntertwining
import DirectGLSSW.EndpointEventGeometry
import DirectGLSSW.EndpointCurrent
import DirectGLSSW.EndpointDirectSource
import DirectGLSSW.TerminalEndpoint
import DirectGLSSW.CapActualBranches
import DirectGLSSW.GlobalCapAlgebra
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DirectGLSSW.CapCrossingEventStability

open DirectGLSSW
open DirectGLSSW.EndpointEventGeometry
open DirectGLSSW.GlobalCapIntertwining
open DirectGLSSW.CapActualBranches
open DirectGLSSW.GlobalCapAlgebra

private theorem move_eq_of_pos (q : ℕ → PlanarPoint ℝ) (t : ℝ) {x : ℕ}
    (hx : 0 < x) : EndpointEventGeometry.moveEndpoint q (1, 0) t x = q x := by
  simp [EndpointEventGeometry.moveEndpoint, Nat.ne_of_gt hx]

private theorem lineCapNear_move_eq (q : ℕ → PlanarPoint ℝ) (n : ℕ) (t : ℝ) :
    GlobalCapIntertwining.lineCapNear
        (EndpointEventGeometry.moveEndpoint q (1, 0) t) n =
      GlobalCapIntertwining.lineCapNear q n := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp [GlobalCapIntertwining.lineCapNear, EndpointEventGeometry.moveEndpoint]
  · simp [GlobalCapIntertwining.lineCapNear, EndpointEventGeometry.moveEndpoint, hx]

private theorem polygonHDet_cyclic (q : ℕ → PlanarPoint ℝ) (i k j : ℕ) :
    polygonHDet q i k j = polygonHDet q k j i := by
  simp [polygonHDet, planarDet]
  ring

private theorem polygonSignArray_cyclic (q : ℕ → PlanarPoint ℝ) (i k j : ℕ) :
    polygonSignArray q i k j = polygonSignArray q k j i := by
  unfold polygonSignArray
  rw [polygonHDet_cyclic]

private theorem capComplement_self_local (q : ℕ → PlanarPoint ℝ) :
    CapActualBranches.capComplement q (q 0) = q := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp [CapActualBranches.capComplement]
  · simp [CapActualBranches.capComplement, hx]

private theorem terminalCurrent_move_column
    (q : ℕ → PlanarPoint ℝ) (k : ℕ) (t : ℝ) (d : ℕ → ℚ)
    (hk : 0 < k) {a : ℕ} (ha : a ≤ k - 1)
    (hstable : ∀ x y, 0 < x → x < y → y ≤ k →
      polygonSignArray (EndpointEventGeometry.moveEndpoint q (1, 0) t) 0 x y =
        polygonSignArray q 0 x y) :
    TerminalEndpoint.terminalCurrent d
        (polygonSignArray (EndpointEventGeometry.moveEndpoint q (1, 0) t)) a (k - 1) =
      TerminalEndpoint.terminalCurrent d (polygonSignArray q) a (k - 1) := by
  have hz : k - 1 + 2 = k + 1 := by omega
  have hleft := TerminalEndpoint.terminalCurrent_polygon_eq
    (EndpointEventGeometry.moveEndpoint q (1, 0) t) d (a := a) (b := k - 1) ha
  have hright := TerminalEndpoint.terminalCurrent_polygon_eq q d
    (a := a) (b := k - 1) ha
  rw [hleft, hright]
  rw [hz]
  apply ordinaryCurrent_congr_interval_fixed_near _ _ _ (by omega)
  intro x y z hax hxy hyz hzb
  by_cases htop : z = k + 1
  · subst z
    have hterm := TerminalEndpoint.terminalFar_polygonSignArray_congr
      (EndpointEventGeometry.moveEndpoint q (1, 0) t)
      (i := x) (k := y) (j := k + 1) (z := k + 1)
      (by omega) (by omega) (le_rfl)
    have htermq := TerminalEndpoint.terminalFar_polygonSignArray_congr
      q (i := x) (k := y) (j := k + 1) (z := k + 1)
      (by omega) (by omega) (le_rfl)
    change polygonSignArray
        (TerminalEndpoint.terminalWord (EndpointEventGeometry.moveEndpoint q (1, 0) t)
          (k + 1)) x y (k + 1) =
      polygonSignArray (TerminalEndpoint.terminalWord q (k + 1)) x y (k + 1)
    rw [hterm, htermq]
    simp only [TerminalEndpoint.terminalFar]
    rw [← polygonSignArray_cyclic (EndpointEventGeometry.moveEndpoint q (1, 0) t) 0 x y]
    rw [← polygonSignArray_cyclic q 0 x y]
    exact hstable x y (by omega) hxy (by omega)
  · have hxpos : 0 < x := by omega
    have hypos : 0 < y := by omega
    have hzpos : 0 < z := by omega
    have hxe : x ≠ k + 1 := by omega
    have hye : y ≠ k + 1 := by omega
    have hze : z ≠ k + 1 := by omega
    have hqx : EndpointEventGeometry.moveEndpoint q (1, 0) t x = q x :=
      move_eq_of_pos q t hxpos
    have hqy : EndpointEventGeometry.moveEndpoint q (1, 0) t y = q y :=
      move_eq_of_pos q t hypos
    have hqz : EndpointEventGeometry.moveEndpoint q (1, 0) t z = q z :=
      move_eq_of_pos q t hzpos
    simp [polygonSignArray, polygonHDet, TerminalEndpoint.terminalWord,
      hxe, hye, hze, hqx, hqy, hqz]

private theorem capInternalMatrix_move_eq
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (t : ℝ) :
    CapActualBranches.capInternalMatrix
        (EndpointEventGeometry.moveEndpoint q (1, 0) t)
        (GlobalCapIntertwining.lineCapNear
          (EndpointEventGeometry.moveEndpoint q (1, 0) t) n) n =
      CapActualBranches.capInternalMatrix q
        (GlobalCapIntertwining.lineCapNear q n) n := by
  ext a b
  rw [lineCapNear_move_eq]
  by_cases hab : a.val < b.val
  · simp only [CapActualBranches.capInternalMatrix, if_pos hab]
    apply ordinaryCurrent_congr_interval_fixed_near _ _ _ (by omega)
    intro x y z hax hxy hyz hzb
    have hx : 0 < x := by omega
    have hy : 0 < y := by omega
    have hz : 0 < z := by omega
    simp [polygonSignArray, polygonHDet,
      move_eq_of_pos q t hx, move_eq_of_pos q t hy, move_eq_of_pos q t hz]
  · simp [CapActualBranches.capInternalMatrix, hab]

private theorem terminalColumn_move_eq
    (q : ℕ → PlanarPoint ℝ) (n k : ℕ) (t : ℝ)
    (hk : 0 < k) (hkn : k < n)
    (hstable : ∀ x y, 0 < x → x < y → y ≤ k →
      polygonSignArray (EndpointEventGeometry.moveEndpoint q (1, 0) t) 0 x y =
        polygonSignArray q 0 x y) :
    ∀ a : Fin n,
      CapActualBranches.capTerminalMatrix
          (EndpointEventGeometry.moveEndpoint q (1, 0) t)
          (GlobalCapIntertwining.lineCapNear
            (EndpointEventGeometry.moveEndpoint q (1, 0) t) n) n a
            ⟨k - 1, by omega⟩ =
      CapActualBranches.capTerminalMatrix
          q (GlobalCapIntertwining.lineCapNear q n) n a ⟨k - 1, by omega⟩ := by
  intro a
  rw [lineCapNear_move_eq]
  change TerminalEndpoint.terminalCurrent
      (GlobalCapIntertwining.lineCapNear q n)
      (polygonSignArray (EndpointEventGeometry.moveEndpoint q (1, 0) t))
      a.val (k - 1) =
    TerminalEndpoint.terminalCurrent
      (GlobalCapIntertwining.lineCapNear q n) (polygonSignArray q) a.val (k - 1)
  by_cases ha : a.val ≤ k - 1
  · exact terminalCurrent_move_column q k t (GlobalCapIntertwining.lineCapNear q n) hk ha hstable
  · have hbelow : k - 1 < a.val := by omega
    rw [TerminalEndpoint.terminalCurrent_below _ _ hbelow,
      TerminalEndpoint.terminalCurrent_below _ _ hbelow]

private theorem lineCapF_row_move_eq
    (q : ℕ → PlanarPoint ℝ) (n k : ℕ) (t : ℝ)
    (hkn : k < n)
    (hnear : GlobalCapIntertwining.lineCapNear
      (EndpointEventGeometry.moveEndpoint q (1, 0) t) n =
      GlobalCapIntertwining.lineCapNear q n)
    (hstable : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ k + 1) →
      polygonSignArray (EndpointEventGeometry.moveEndpoint q (1, 0) t) a b c =
        polygonSignArray q a b c) :
    ∀ i : Fin n,
      GlobalCapIntertwining.lineCapF
          (EndpointEventGeometry.moveEndpoint q (1, 0) t) n ⟨k, hkn⟩ i =
        GlobalCapIntertwining.lineCapF q n ⟨k, hkn⟩ i := by
  intro i
  change EndpointCurrent.endpointCurrent
      (GlobalCapIntertwining.lineCapNear (EndpointEventGeometry.moveEndpoint q (1, 0) t) n)
      (polygonSignArray (CapActualBranches.capComplement
        (EndpointEventGeometry.moveEndpoint q (1, 0) t)
        ((EndpointEventGeometry.moveEndpoint q (1, 0) t) 0))) k i.val =
    EndpointCurrent.endpointCurrent (GlobalCapIntertwining.lineCapNear q n)
      (polygonSignArray (CapActualBranches.capComplement q (q 0))) k i.val
  rw [capComplement_self_local, capComplement_self_local, hnear]
  by_cases hki : k ≤ i.val
  · simp only [EndpointCurrent.endpointCurrent, if_pos hki]
    apply ordinaryCurrent_congr_interval_fixed_near _ _ _ (by omega)
    intro x y z hx hxy hyz hz
    by_cases hxk : x = k
    · simp [EndpointCurrent.endpointFar, hxk]
      exact hstable 0 y z (by omega) hyz (by omega) (by
        by_cases hyk : y = k
        · right; left; omega
        · exact Or.inr (Or.inl hyk))
    · simp [EndpointCurrent.endpointFar, hxk]
      have hxpos : 0 < x := by omega
      have hypos : 0 < y := by omega
      have hzpos : 0 < z := by omega
      simp [polygonSignArray, polygonHDet,
        move_eq_of_pos q t hxpos, move_eq_of_pos q t hypos, move_eq_of_pos q t hzpos]
  · have hnot : ¬ k ≤ i.val := by omega
    simp [EndpointCurrent.endpointCurrent, hnot]

/-- The designated first-row and terminal-column vectors are stable on both
sides of an isolated horizontal event. -/
theorem exists_lineCap_FU_stability_radius
    (q : ℕ → PlanarPoint ℝ) (n k : ℕ)
    (hk : 0 < k) (hkn : k < n)
    (τ : ℝ) (hτ : τ < 0) (hzero : (q 0).2 = 0)
    (hcollinear : q k = q 0 + τ • (q (k+1) - q 0))
    (hlast : (q (k+1)).2 ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ k+1) → polygonHDet q a b c ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      (∀ i : Fin n,
        GlobalCapIntertwining.lineCapF
            (EndpointEventGeometry.moveEndpoint q (1, 0) ε) n ⟨k, hkn⟩ i =
          GlobalCapIntertwining.lineCapF q n ⟨k, hkn⟩ i ∧
        GlobalCapIntertwining.lineCapF
            (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε)) n ⟨k, hkn⟩ i =
          GlobalCapIntertwining.lineCapF q n ⟨k, hkn⟩ i) ∧
      (∀ i : Fin n,
        GlobalCapIntertwining.lineCapU
            (EndpointEventGeometry.moveEndpoint q (1, 0) ε) n i
              ⟨k-1, by omega⟩ =
          GlobalCapIntertwining.lineCapU q n i ⟨k-1, by omega⟩ ∧
        GlobalCapIntertwining.lineCapU
            (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε)) n i
              ⟨k-1, by omega⟩ =
          GlobalCapIntertwining.lineCapU q n i ⟨k-1, by omega⟩) := by
  have hzeroDet : polygonHDet q 0 k (k + 1) = 0 := by
    rw [polygonHDet, hcollinear]
    simp [planarDet, hzero]
    ring
  have htransverse : planarDet (q k - q (k + 1)) (1, 0) ≠ 0 := by
    have hy : (q k).2 = τ * (q (k + 1)).2 := by
      have hcoord := congrArg Prod.snd hcollinear
      simpa [hzero] using hcoord
    have hcoef : 1 - τ ≠ 0 := by linarith
    have hdet : planarDet (q k - q (k + 1)) (1, 0) =
        (1 - τ) * (q (k + 1)).2 := by
      simp [planarDet]
      rw [hy]
      ring
    rw [hdet]
    exact mul_ne_zero hcoef hlast
  obtain ⟨ρ, hρ, hbundle⟩ := EndpointEventGeometry.exists_endpoint_event_radius
    q (1, 0) n hk (by omega) (by omega) hzeroDet htransverse hisolated
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  obtain ⟨hgenPlus, hgenMinus, hstablePair, _hjump⟩ := hbundle ε hε hερ
  have hstablePlus (a b c : ℕ) (hab : a < b) (hbc : b < c) (hc : c ≤ n)
      (hother : a ≠ 0 ∨ b ≠ k ∨ c ≠ k + 1) :
      polygonSignArray (EndpointEventGeometry.moveEndpoint q (1, 0) ε) a b c =
        polygonSignArray q a b c := (hstablePair a b c hab hbc hc hother).1
  have hstableMinus (a b c : ℕ) (hab : a < b) (hbc : b < c) (hc : c ≤ n)
      (hother : a ≠ 0 ∨ b ≠ k ∨ c ≠ k + 1) :
      polygonSignArray (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε)) a b c =
        polygonSignArray q a b c := (hstablePair a b c hab hbc hc hother).2
  have hnearPlus := lineCapNear_move_eq q n ε
  have hnearMinus := lineCapNear_move_eq q n (-ε)
  have hFplus := lineCapF_row_move_eq q n k ε hkn hnearPlus
    (fun a b c hab hbc hc ho => hstablePlus a b c hab hbc hc ho)
  have hFminus := lineCapF_row_move_eq q n k (-ε) hkn hnearMinus
    (fun a b c hab hbc hc ho => hstableMinus a b c hab hbc hc ho)
  refine ⟨?_, ?_⟩
  · intro i
    exact ⟨hFplus i, hFminus i⟩
  · intro i
    have hheightPlus : lineCapHeights (EndpointEventGeometry.moveEndpoint q (1, 0) ε) n = lineCapHeights q n := by
      funext r
      simp [lineCapHeights, EndpointEventGeometry.moveEndpoint, Nat.ne_of_gt (by omega : 0 < r.val + 1)]
    have hheightMinus : lineCapHeights (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε)) n = lineCapHeights q n := by
      funext r
      simp [lineCapHeights, EndpointEventGeometry.moveEndpoint, Nat.ne_of_gt (by omega : 0 < r.val + 1)]
    have hSplus : lineCapS (EndpointEventGeometry.moveEndpoint q (1, 0) ε) n = lineCapS q n := by
      exact congrArg (fun f : Fin n → ℚ => Matrix.diagonal f) hheightPlus
    have hSminus : lineCapS (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε)) n = lineCapS q n := by
      exact congrArg (fun f : Fin n → ℚ => Matrix.diagonal f) hheightMinus
    have hBplus := capInternalMatrix_move_eq q n ε
    have hBminus := capInternalMatrix_move_eq q n (-ε)
    have hGplus := terminalColumn_move_eq q n k ε hk hkn
      (fun x y hx hxy hy => hstablePlus 0 x y (by omega) hxy (by omega) (Or.inr (Or.inl (by omega))))
    have hGminus := terminalColumn_move_eq q n k (-ε) hk hkn
      (fun x y hx hxy hy => hstableMinus 0 x y (by omega) hxy (by omega) (Or.inr (Or.inl (by omega))))
    let Rplus := globalCapResolvent
      (capInternalMatrix (EndpointEventGeometry.moveEndpoint q (1, 0) ε)
        (lineCapNear (EndpointEventGeometry.moveEndpoint q (1, 0) ε) n) n)
      (lineCapHeights (EndpointEventGeometry.moveEndpoint q (1, 0) ε) n)
    let Rminus := globalCapResolvent
      (capInternalMatrix (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε))
        (lineCapNear (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε)) n) n)
      (lineCapHeights (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε)) n)
    let R := globalCapResolvent
      (capInternalMatrix q (lineCapNear q n) n) (lineCapHeights q n)
    have hBplus' : capInternalMatrix (EndpointEventGeometry.moveEndpoint q (1, 0) ε)
        (lineCapNear q n) n = capInternalMatrix q (lineCapNear q n) n := by
      simpa only [lineCapNear_move_eq] using hBplus
    have hBminus' : capInternalMatrix (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε))
        (lineCapNear q n) n = capInternalMatrix q (lineCapNear q n) n := by
      simpa only [lineCapNear_move_eq] using hBminus
    have hRplus : Rplus = R := by
      simp [Rplus, R, hBplus', hheightPlus, lineCapNear_move_eq]
    have hRminus : Rminus = R := by
      simp [Rminus, R, hBminus', hheightMinus, lineCapNear_move_eq]
    have hleftPlus :
        lineCapS (EndpointEventGeometry.moveEndpoint q (1, 0) ε) n * Rplus =
          lineCapS q n * R := by rw [hSplus, hRplus]
    have hleftMinus :
        lineCapS (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε)) n * Rminus =
          lineCapS q n * R := by rw [hSminus, hRminus]
    have hUplus :
        GlobalCapIntertwining.lineCapU
          (EndpointEventGeometry.moveEndpoint q (1, 0) ε) n i ⟨k-1, by omega⟩ =
        GlobalCapIntertwining.lineCapU q n i ⟨k-1, by omega⟩ := by
      change ((lineCapS (EndpointEventGeometry.moveEndpoint q (1, 0) ε) n * Rplus) *
        capTerminalMatrix (EndpointEventGeometry.moveEndpoint q (1, 0) ε)
          (lineCapNear (EndpointEventGeometry.moveEndpoint q (1, 0) ε) n) n) i ⟨k-1, by omega⟩ = _
      rw [hleftPlus]
      calc
        ((lineCapS q n * R) * capTerminalMatrix
          (EndpointEventGeometry.moveEndpoint q (1, 0) ε)
          (lineCapNear (EndpointEventGeometry.moveEndpoint q (1, 0) ε) n) n) i ⟨k-1, by omega⟩ =
          ((lineCapS q n * R) * capTerminalMatrix q (lineCapNear q n) n) i ⟨k-1, by omega⟩ := by
            rw [Matrix.mul_apply, Matrix.mul_apply]
            apply Finset.sum_congr rfl
            intro a _
            rw [hGplus a]
        _ = GlobalCapIntertwining.lineCapU q n i ⟨k-1, by omega⟩ := rfl
    have hUminus :
        GlobalCapIntertwining.lineCapU
          (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε)) n i ⟨k-1, by omega⟩ =
        GlobalCapIntertwining.lineCapU q n i ⟨k-1, by omega⟩ := by
      change ((lineCapS (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε)) n * Rminus) *
        capTerminalMatrix (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε))
          (lineCapNear (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε)) n) n) i ⟨k-1, by omega⟩ = _
      rw [hleftMinus]
      calc
        ((lineCapS q n * R) * capTerminalMatrix
          (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε))
          (lineCapNear (EndpointEventGeometry.moveEndpoint q (1, 0) (-ε)) n) n) i ⟨k-1, by omega⟩ =
          ((lineCapS q n * R) * capTerminalMatrix q (lineCapNear q n) n) i ⟨k-1, by omega⟩ := by
            rw [Matrix.mul_apply, Matrix.mul_apply]
            apply Finset.sum_congr rfl
            intro a _
            rw [hGminus a]
        _ = GlobalCapIntertwining.lineCapU q n i ⟨k-1, by omega⟩ := rfl
    exact ⟨hUplus, hUminus⟩












end DirectGLSSW.CapCrossingEventStability
