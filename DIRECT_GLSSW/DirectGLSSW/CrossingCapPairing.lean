import DirectGLSSW.DistinctCapSubword
import DirectGLSSW.CapCrossingEvent
import DirectGLSSW.GlobalCapIntertwining
import DirectGLSSW.GlobalCapAlgebra
import DirectGLSSW.TriangularInverse
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW.CrossingCapPairing

open DirectGLSSW
open DirectGLSSW.CapActualBranches
open DirectGLSSW.CapCrossingEvent
open DirectGLSSW.DistinctCapSubword
open DirectGLSSW.GlobalCapAlgebra
open DirectGLSSW.GlobalCapIntertwining

/-- The clipped polygon with actual endpoint positions after the two horizontal
moves: cpoint, q(k+1), ..., q(l), dpoint, then closed by dpoint→cpoint. -/
def crossingClippedCapWord (q : ℕ → PlanarPoint ℝ) (c d : ℝ) (k l : ℕ) :
    Fin (((l - 1) - k + 1) + 2) → PlanarPoint ℝ :=
  let m := (l - 1) - k + 1
  fun i => capWord (CapSubwordBridge.capSubwordNat (horizontalMove q d) k m)
    (horizontalMove q c 0) m i.val

/-- The clipped subword starts at the actual c endpoint. -/
theorem crossingClippedCapWord_start
    (q : ℕ → PlanarPoint ℝ) (c d : ℝ) (k l : ℕ) :
    crossingClippedCapWord q c d k l ⟨0, by omega⟩ = horizontalMove q c 0 := by
  simp [crossingClippedCapWord, capWord]

/-- Every strict interior vertex is the corresponding actual original vertex. -/
theorem crossingClippedCapWord_internal
    (q : ℕ → PlanarPoint ℝ) (c d : ℝ) (k l : ℕ)
    (i : Fin (((l - 1) - k + 1) + 2))
    (hi : 0 < i.val) (hiend : i.val < ((l - 1) - k + 1) + 1) :
    crossingClippedCapWord q c d k l i = q (k + i.val) := by
  let m := (l - 1) - k + 1
  have hle : i.val ≤ m := by dsimp [m] at hiend ⊢; omega
  have hlast : i.val ≠ m + 1 := by dsimp [m]; omega
  have hval : i.val ≠ 0 := by omega
  have hsum_ne : k + i.val ≠ 0 := by omega
  have hpoint : CapSubwordBridge.capSubwordNat
      (horizontalMove q d) k m i.val = q (k + i.val) := by
    unfold CapSubwordBridge.capSubwordNat
    rw [dif_pos hle]
    unfold CapSubwordBridge.capSubwordFin
    rw [if_neg hval]
    change horizontalMove q d (k + i.val) = q (k + i.val)
    unfold horizontalMove EndpointEventGeometry.moveEndpoint
    rw [if_neg hsum_ne]
  change capWord (CapSubwordBridge.capSubwordNat (horizontalMove q d) k m)
    (horizontalMove q c 0) m i.val = q (k + i.val)
  unfold capWord
  simp only [if_neg hval, if_neg hlast]
  exact hpoint

/-- The clipped subword ends at the actual moved d endpoint. -/
theorem crossingClippedCapWord_end
    (q : ℕ → PlanarPoint ℝ) (c d : ℝ) (k l : ℕ) :
    crossingClippedCapWord q c d k l
      ⟨((l - 1) - k + 1) + 1, by omega⟩ = horizontalMove q d 0 := by
  simp [crossingClippedCapWord, capWord, CapSubwordBridge.capSubwordNat,
    CapSubwordBridge.capSubwordFin, horizontalMove,
    EndpointEventGeometry.moveEndpoint]

/-- Under the stated forward order, the final internal vertex is q(l). -/
theorem crossingClippedCapWord_last_internal
    (q : ℕ → PlanarPoint ℝ) (c d : ℝ) (k l : ℕ) (hkl : k < l) :
    crossingClippedCapWord q c d k l
      ⟨(l - 1 - k + 1), by omega⟩ = q l := by
  let m := l - 1 - k + 1
  have hmpos : 0 < m := by dsimp [m]; omega
  have hmle : m < m + 1 := by omega
  have hidx : (⟨m, by omega⟩ : Fin (m + 2)).val = m := rfl
  have hinner := crossingClippedCapWord_internal q c d k l
    (⟨m, by omega⟩ : Fin (m + 2)) hmpos hmle
  have hsum : k + m = l := by dsimp [m]; omega
  simpa [m, hsum] using hinner

private theorem upper_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ)
    (hA : CapMatrixRestriction.UpperTriangularBlock A)
    (hB : CapMatrixRestriction.UpperTriangularBlock B) :
    CapMatrixRestriction.UpperTriangularBlock (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hri : r.val < i.val
  · rw [hA i r hri, zero_mul]
  · rw [hB r j (by omega), mul_zero]

private theorem diagonal_upper {n : ℕ} (h : Fin n → ℚ) :
    CapMatrixRestriction.UpperTriangularBlock (Matrix.diagonal h) := by
  intro i j hij
  have hne : i ≠ j := by intro he; subst j; omega
  simp [Matrix.diagonal, hne]

private theorem weight_strictUpper {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : StrictUpper B) (h : Fin n → ℚ) :
    StrictUpper (B * Matrix.diagonal h) := by
  intro i j hji
  rw [Matrix.mul_diagonal, hB i j hji, zero_mul]

private theorem resolvent_upper {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : StrictUpper B) (h : Fin n → ℚ) :
    CapMatrixRestriction.UpperTriangularBlock (globalCapResolvent B h) := by
  intro i j hij
  unfold globalCapResolvent finiteInverse
  simp only [neg_neg, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro r _
  exact strictUpper_pow_entry_zero _ (weight_strictUpper B hB h) r i j (by omega)

private theorem cap_start_upper (q : ℕ → PlanarPoint ℝ) (p : PlanarPoint ℝ)
    (n : ℕ) :
    CapMatrixRestriction.UpperTriangularBlock
      (capStartFactor q p n) := by
  intro i j hij
  change EndpointCurrent.endpointCurrent
    (fun k => scalarSignValue (q k).2)
    (polygonSignArray (capComplement q p)) i.val j.val = 0
  exact EndpointCurrent.endpointCurrent_below _ _ (by omega)

private theorem cap_terminal_upper (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    CapMatrixRestriction.UpperTriangularBlock (capTerminalFactor q n) := by
  have hG : CapMatrixRestriction.UpperTriangularBlock
      (capTerminalMatrix q (fun k => scalarSignValue (q k).2) n) := by
    intro i j hij
    exact TerminalEndpoint.terminalCurrent_below _ _ (by omega)
  have hB : StrictUpper (capInternalMatrix q
      (fun k => scalarSignValue (q k).2) n) :=
    cap_internalMatrix_strictUpper q _ n
  have hS := diagonal_upper (GlobalCapAlgebra.lineCapHeights q n)
  have hR := resolvent_upper (capInternalMatrix q
      (fun k => scalarSignValue (q k).2) n) hB
      (GlobalCapAlgebra.lineCapHeights q n)
  unfold capTerminalFactor
  exact upper_mul _ _ (upper_mul _ _ hS hR) hG

private theorem actual_factors_eq_cap_factors
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (c d : ℝ) :
    lineCapF (horizontalMove q c) n =
        capStartFactor (horizontalMove q d) (horizontalMove q c 0) n ∧
    lineCapU (horizontalMove q d) n = capTerminalFactor (horizontalMove q d) n := by
  constructor
  · have hnear : lineCapNear (horizontalMove q c) n =
        lineCapNear (horizontalMove q d) n := by
      funext x
      by_cases hx : x = 0
      · subst x
        simp [lineCapNear, horizontalMove, EndpointEventGeometry.moveEndpoint]
      · simp [lineCapNear, horizontalMove, EndpointEventGeometry.moveEndpoint, hx]
    have hcomp : capComplement (horizontalMove q d) (horizontalMove q c 0) =
        horizontalMove q c := by
      funext x
      by_cases hx : x = 0
      · subst x
        simp [capComplement]
      · simp [capComplement, horizontalMove, EndpointEventGeometry.moveEndpoint, hx]
    have hself : capComplement (horizontalMove q c) (horizontalMove q c 0) =
        horizontalMove q c := by
      funext x
      by_cases hx : x = 0
      · subst x
        simp [capComplement]
      · simp [capComplement, horizontalMove, EndpointEventGeometry.moveEndpoint, hx]
    ext i j
    change EndpointCurrent.endpointCurrent (lineCapNear (horizontalMove q c) n)
        (polygonSignArray (capComplement (horizontalMove q c) (horizontalMove q c 0)))
        i.val j.val =
      EndpointCurrent.endpointCurrent
        (fun k => scalarSignValue (horizontalMove q d k).2)
        (polygonSignArray (capComplement (horizontalMove q d) (horizontalMove q c 0)))
        i.val j.val
    rw [hself, hcomp, hnear]
    rfl
  · rfl

/-- The two independently rooted actual factors are the start and terminal
factors of the same cap pairing. -/
theorem actual_pairing_eq_cap_factor_entry
    (q : ℕ → PlanarPoint ℝ) (n k l : ℕ) (c d : ℝ)
    (_hk : 0 < k) (hkn : k < n) (hl : 0 < l) (hln : l < n) :
    (∑ r : Fin n,
      lineCapF (horizontalMove q c) n ⟨k, hkn⟩ r *
        lineCapU (horizontalMove q d) n r ⟨l-1, by omega⟩) =
      (capStartFactor (horizontalMove q d) (horizontalMove q c 0) n *
        capTerminalFactor (horizontalMove q d) n)
        ⟨k, hkn⟩ ⟨l-1, by omega⟩ := by
  have hfac := actual_factors_eq_cap_factors q n c d
  rw [hfac.1, hfac.2]
  simp only [Matrix.mul_apply]

/-- When the second crossing time is at or before the first, actual upper
triangular support forces the two differently rooted endpoint factors to pair
 to zero. -/
theorem actual_pairing_eq_zero_of_reverse_order
    (q : ℕ → PlanarPoint ℝ) (n k l : ℕ) (c d : ℝ)
    (hk : 0 < k) (hkn : k < n) (hl : 0 < l) (hln : l < n)
    (horder : l ≤ k) :
    (∑ r : Fin n,
      lineCapF (horizontalMove q c) n ⟨k, hkn⟩ r *
        lineCapU (horizontalMove q d) n r ⟨l-1, by omega⟩) = 0 := by
  rw [actual_pairing_eq_cap_factor_entry q n k l c d hk hkn hl hln]
  have hupper := upper_mul _ _
    (cap_start_upper (horizontalMove q d) (horizontalMove q c 0) n)
    (cap_terminal_upper (horizontalMove q d) n)
  have hbelow : (⟨k, hkn⟩ : Fin n).val > (⟨l-1, by omega⟩ : Fin n).val := by
    change k > l - 1
    omega
  exact hupper ⟨k, hkn⟩ ⟨l-1, by omega⟩ hbelow

/-- For c<d, the actual F(c)-row/U(d)-column sum is the amplitude of the
explicit clipped subarc cpoint,q(k+1),...,q(l),dpoint. -/
theorem actual_pairing_eq_clipped_cap_amplitude
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n k l : ℕ) (c d : ℝ)
    (hzero : (q 0).2 = 0)
    (_hk : 0 < k) (hkn : k < n) (hl : 0 < l) (hln : l < n)
    (htime : c < d) (horder : k < l)
    (hcap : CyclicGeneric (crossingClippedCapWord q c d k l)) :
    (∑ r : Fin n,
      lineCapF (horizontalMove q c) n ⟨k, hkn⟩ r *
        lineCapU (horizontalMove q d) n r ⟨l-1, by omega⟩) =
      polygonAmplitude (crossingClippedCapWord q c d k l) hcap := by
  let qd := horizontalMove q d
  let pc := horizontalMove q c 0
  let a : Fin n := ⟨k, hkn⟩
  let b : Fin n := ⟨l-1, by omega⟩
  have hab : a.val ≤ b.val := by dsimp [a, b]; omega
  have hc0 : pc.2 = 0 := by simp [pc, horizontalMove, EndpointEventGeometry.moveEndpoint, hzero]
  have hd0 : (qd 0).2 = 0 := by simp [qd, horizontalMove, EndpointEventGeometry.moveEndpoint, hzero]
  have hpc : pc.1 = (q 0).1 + c := by
    simp [pc, horizontalMove, EndpointEventGeometry.moveEndpoint]
  have hqd : (qd 0).1 = (q 0).1 + d := by
    simp [qd, horizontalMove, EndpointEventGeometry.moveEndpoint]
  have hcd : pc.1 < (qd 0).1 := by rw [hpc, hqd]; exact add_lt_add_left htime _
  have hcap' : CyclicGeneric
      (fun i : Fin ((b.val - a.val + 1) + 2) =>
        capWord (CapSubwordBridge.capSubwordNat qd a.val
          (b.val - a.val + 1)) pc (b.val - a.val + 1) i.val) := by
    simpa only [crossingClippedCapWord, qd, pc, a, b] using hcap
  have hselected := capStart_mul_capTerminal_entry_eq_selected_cap_amplitude
    hRI qd n hd0 a b hab pc hc0 hcd hcap'
  have hfactor := actual_pairing_eq_cap_factor_entry q n k l c d _hk hkn hl hln
  calc
    (∑ r : Fin n,
      lineCapF (horizontalMove q c) n ⟨k, hkn⟩ r *
        lineCapU (horizontalMove q d) n r ⟨l-1, by omega⟩) =
      (capStartFactor qd pc n * capTerminalFactor qd n) a b := by
        simpa [qd, pc, a, b] using hfactor
    _ = polygonAmplitude (crossingClippedCapWord q c d k l) hcap := by
      simpa only [crossingClippedCapWord, qd, pc, a, b] using hselected
















end DirectGLSSW.CrossingCapPairing
