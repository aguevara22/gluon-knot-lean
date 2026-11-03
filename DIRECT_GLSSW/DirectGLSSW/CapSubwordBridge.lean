import DirectGLSSW.CapActualBranches
import DirectGLSSW.CurrentTranslation
import DirectGLSSW.CapMatrixRestriction
import DirectGLSSW.EndpointCurrent
import DirectGLSSW.TerminalEndpoint
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW.CapSubwordBridge
open DirectGLSSW

/-- Finite subword with the original initial point and a shifted positive tail. -/
def capSubwordFin (q : ℕ → PlanarPoint ℝ) (offset m : ℕ) :
    Fin (m + 1) → PlanarPoint ℝ :=
  fun r => if r.val = 0 then q 0 else q (offset + r.val)

/-- Extend the finite subword by q₀ outside its stated range. -/
def capSubwordNat (q : ℕ → PlanarPoint ℝ) (offset m : ℕ) :
    ℕ → PlanarPoint ℝ :=
  fun x => if hx : x ≤ m then
    capSubwordFin q offset m ⟨x, by omega⟩ else q 0

/-- Exact shifted near data; this is not an invariance claim. -/
def capSubwordNear (d : ℕ → ℚ) (offset : ℕ) : ℕ → ℚ :=
  fun k => d (offset + k)

private theorem capSubwordNat_zero (q : ℕ → PlanarPoint ℝ) (offset m : ℕ) :
    capSubwordNat q offset m 0 = q 0 := by
  simp [capSubwordNat, capSubwordFin]

private theorem capSubwordNat_shift (q : ℕ → PlanarPoint ℝ) (offset m x : ℕ)
    (hx : 0 < x) (hxm : x ≤ m) :
    capSubwordNat q offset m x = q (offset + x) := by
  simp [capSubwordNat, capSubwordFin, hx.ne', hxm]

private theorem endpointWord_subword_eq
    (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ) (offset m i x : ℕ)
    (hix : i ≤ x) (hxm : x ≤ m) :
    EndpointCurrent.endpointWord
      (CapActualBranches.capComplement (capSubwordNat q offset m) p') i x =
    EndpointCurrent.endpointWord
      (CapActualBranches.capComplement q p') (offset + i) (offset + x) := by
  by_cases hxi : x = i
  · subst x
    simp [EndpointCurrent.endpointWord, CapActualBranches.capComplement]
  · have hlt : i < x := by omega
    have hxpos : 0 < x := by omega
    have hxoff : offset + x ≠ offset + i := by omega
    have hxoff0 : offset + x ≠ 0 := by omega
    have hnotzero : ¬ (offset = 0 ∧ x = 0) := by omega
    have hxne : x ≠ 0 := by omega
    simp only [EndpointCurrent.endpointWord, if_neg hxi, if_neg hxoff]
    change CapActualBranches.capComplement (capSubwordNat q offset m) p' x =
      CapActualBranches.capComplement q p' (offset + x)
    simp [CapActualBranches.capComplement, hxne, hxoff0, hnotzero,
      capSubwordNat_shift q offset m x hxpos hxm]

private theorem translateNear_eq_subword (d : ℕ → ℚ) (offset : ℕ) :
    CurrentTranslation.translateTriple offset (fun _ k _ => d k) =
      (fun _ k _ => capSubwordNear d offset k) := by
  funext x k y
  simp [CurrentTranslation.translateTriple, capSubwordNear]

private theorem ordinaryCurrent_shifted_subword
    (Dlocal Dglobal Hlocal Hglobal : TripleArray)
    (offset i j : ℕ) (hij : i < j)
    (hD : Dlocal = CurrentTranslation.translateTriple offset Dglobal)
    (hH : ∀ a b c, i ≤ a → a < b → b < c → c ≤ j →
      Hlocal a b c =
        CurrentTranslation.translateTriple offset Hglobal a b c) :
    ordinaryCurrent Dlocal Hlocal i j =
      ordinaryCurrent Dglobal Hglobal (offset + i) (offset + j) := by
  have hchange := congrArg (fun E : TripleArray => ordinaryCurrent E Hlocal i j) hD
  have hlocal := ordinaryCurrent_congr_interval_fixed_near
    (CurrentTranslation.translateTriple offset Dglobal) Hlocal
    (CurrentTranslation.translateTriple offset Hglobal) hij hH
  have htrans := CurrentTranslation.ordinaryCurrent_translate
    Dglobal Hglobal offset i j hij
  exact hchange.trans (hlocal.trans htrans)

private theorem capBlock_val {n m offset : ℕ} (hbound : offset + m ≤ n)
    (i : Fin m) :
    (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound i).val =
      offset + i.val := rfl

private theorem capBlock_lt_iff {n m offset : ℕ} (hbound : offset + m ≤ n)
    (i j : Fin m) :
    (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound i).val <
      (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound j).val ↔
      i.val < j.val := by
  simp [CapMatrixRestriction.consecutiveBlockEmbedding]

private theorem endpointWord_sign_subword_eq
    (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ) (offset m i j : ℕ)
    (hjm : j < m) :
    ∀ x y z, i ≤ x → x < y → y < z → z ≤ j + 1 →
      polygonSignArray
        (EndpointCurrent.endpointWord
          (CapActualBranches.capComplement (capSubwordNat q offset m) p') i)
        x y z =
      CurrentTranslation.translateTriple offset
        (polygonSignArray
          (EndpointCurrent.endpointWord
            (CapActualBranches.capComplement q p') (offset + i))) x y z := by
  intro x y z hix hxy hyz hze
  have hx : x ≤ m := by omega
  have hy : y ≤ m := by omega
  have hz : z ≤ m := by omega
  have hpx := endpointWord_subword_eq q p' offset m i x hix hx
  have hpy := endpointWord_subword_eq q p' offset m i y (by omega) hy
  have hpz := endpointWord_subword_eq q p' offset m i z (by omega) hz
  simp [CurrentTranslation.translateTriple, polygonSignArray, polygonHDet, hpx, hpy, hpz]

private theorem polygonSign_subword_eq
    (q : ℕ → PlanarPoint ℝ) (offset m : ℕ)
    {x y z : ℕ} (hx : 0 < x) (hy : x < y) (hz : y < z) (hzm : z ≤ m) :
    polygonSignArray (capSubwordNat q offset m) x y z =
      CurrentTranslation.translateTriple offset (polygonSignArray q) x y z := by
  have hxpos : 0 < x := hx
  have hypos : 0 < y := by omega
  have hzpos : 0 < z := by omega
  have hym : y ≤ m := by omega
  have hxm : x ≤ m := by omega
  have hpx := capSubwordNat_shift q offset m x hxpos hxm
  have hpy := capSubwordNat_shift q offset m y hypos hym
  have hpz := capSubwordNat_shift q offset m z hzpos hzm
  simp [CurrentTranslation.translateTriple, polygonSignArray, polygonHDet, hpx, hpy, hpz]

theorem capEndpointMatrix_submatrix_consecutive
    (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ) (d : ℕ → ℚ)
    {n m offset : ℕ} (hbound : offset + m ≤ n) :
    (CapActualBranches.capEndpointMatrix q p' d n).submatrix
      (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound)
      (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound) =
      CapActualBranches.capEndpointMatrix
        (capSubwordNat q offset m) p' (capSubwordNear d offset) m := by
  ext i j
  change EndpointCurrent.endpointCurrent d
      (polygonSignArray (CapActualBranches.capComplement q p'))
      (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound i).val
      (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound j).val =
    EndpointCurrent.endpointCurrent (capSubwordNear d offset)
      (polygonSignArray (CapActualBranches.capComplement (capSubwordNat q offset m) p'))
      i.val j.val
  rw [capBlock_val hbound i, capBlock_val hbound j]
  by_cases hji : j.val < i.val
  · have hjiGlobal : offset + j.val < offset + i.val := by omega
    rw [EndpointCurrent.endpointCurrent_below _ _ hjiGlobal,
      EndpointCurrent.endpointCurrent_below _ _ hji]
  · have hij : i.val ≤ j.val := by omega
    have hF := EndpointCurrent.endpointCurrent_polygon_eq
      (CapActualBranches.capComplement q p') d
      (a := offset+i.val) (i := offset+j.val) (by omega)
    have hF' := EndpointCurrent.endpointCurrent_polygon_eq
      (CapActualBranches.capComplement (capSubwordNat q offset m) p')
      (capSubwordNear d offset) (a := i.val) (i := j.val) hij
    rw [hF, hF']
    have hnear := translateNear_eq_subword d offset
    have hfar : ∀ x y z, i.val ≤ x → x < y → y < z → z ≤ j.val+1 →
        polygonSignArray
          (EndpointCurrent.endpointWord
            (CapActualBranches.capComplement (capSubwordNat q offset m) p') i.val) x y z =
        CurrentTranslation.translateTriple offset
          (polygonSignArray
            (EndpointCurrent.endpointWord
              (CapActualBranches.capComplement q p') (offset+i.val))) x y z :=
      endpointWord_sign_subword_eq q p' offset m i.val j.val (by omega)
    have hcur := ordinaryCurrent_shifted_subword
      (fun _ k _ => capSubwordNear d offset k)
      (fun _ k _ => d k)
      (polygonSignArray (EndpointCurrent.endpointWord
        (CapActualBranches.capComplement (capSubwordNat q offset m) p') i.val))
      (polygonSignArray
        (EndpointCurrent.endpointWord (CapActualBranches.capComplement q p') (offset+i.val)))
      offset i.val (j.val+1) (by omega) hnear.symm hfar
    exact hcur.symm

theorem capInternalMatrix_submatrix_consecutive
    (q : ℕ → PlanarPoint ℝ) (d : ℕ → ℚ)
    {n m offset : ℕ} (hbound : offset + m ≤ n) :
    (CapActualBranches.capInternalMatrix q d n).submatrix
      (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound)
      (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound) =
      CapActualBranches.capInternalMatrix
        (capSubwordNat q offset m) (capSubwordNear d offset) m := by
  ext i j
  have hlt_iff := capBlock_lt_iff hbound i j
  change (if (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound i).val <
      (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound j).val then
      ordinaryCurrent (fun _ k _ => d k) (polygonSignArray q)
        ((CapMatrixRestriction.consecutiveBlockEmbedding offset hbound i).val+1)
        ((CapMatrixRestriction.consecutiveBlockEmbedding offset hbound j).val+1) else 0) =
    (if i.val < j.val then
      ordinaryCurrent (fun _ k _ => capSubwordNear d offset k)
        (polygonSignArray (capSubwordNat q offset m)) (i.val+1) (j.val+1) else 0)
  rw [capBlock_val hbound i, capBlock_val hbound j]
  by_cases hij : i.val < j.val
  · rw [if_pos (by omega), if_pos hij]
    have hfar : ∀ x y z, i.val+1 ≤ x → x < y → y < z → z ≤ j.val+1 →
        polygonSignArray (capSubwordNat q offset m) x y z =
          CurrentTranslation.translateTriple offset (polygonSignArray q) x y z := by
      intro x y z hx hxy hyz hz
      exact polygonSign_subword_eq q offset m (by omega) hxy hyz (by omega)
    have hnear := translateNear_eq_subword d offset
    have hcur := ordinaryCurrent_shifted_subword
      (fun _ k _ => capSubwordNear d offset k)
      (fun _ k _ => d k)
      (polygonSignArray (capSubwordNat q offset m))
      (polygonSignArray q) offset (i.val+1) (j.val+1) (by omega)
      hnear.symm hfar
    exact hcur.symm
  · have hnotBlock : ¬ (offset + i.val < offset + j.val) := by omega
    rw [if_neg hnotBlock, if_neg hij]

theorem capTerminalMatrix_submatrix_consecutive
    (q : ℕ → PlanarPoint ℝ) (d : ℕ → ℚ)
    {n m offset : ℕ} (hbound : offset + m ≤ n) :
    (CapActualBranches.capTerminalMatrix q d n).submatrix
      (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound)
      (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound) =
      CapActualBranches.capTerminalMatrix
        (capSubwordNat q offset m) (capSubwordNear d offset) m := by
  ext i j
  change TerminalEndpoint.terminalCurrent d (polygonSignArray q)
      (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound i).val
      (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound j).val =
    TerminalEndpoint.terminalCurrent (capSubwordNear d offset)
      (polygonSignArray (capSubwordNat q offset m)) i.val j.val
  rw [capBlock_val hbound i, capBlock_val hbound j]
  by_cases hji : j.val < i.val
  · have hjiGlobal : offset + j.val < offset + i.val := by omega
    rw [TerminalEndpoint.terminalCurrent_below _ _ hjiGlobal,
      TerminalEndpoint.terminalCurrent_below _ _ hji]
  · have hij : i.val ≤ j.val := by omega
    have hG := TerminalEndpoint.terminalCurrent_polygon_eq q d
      (a := offset+i.val) (b := offset+j.val) (by omega)
    have hG' := TerminalEndpoint.terminalCurrent_polygon_eq
      (capSubwordNat q offset m) (capSubwordNear d offset)
      (a := i.val) (b := j.val) hij
    rw [hG, hG']
    have hterm : ∀ x, i.val+1 ≤ x → x ≤ j.val+2 →
        TerminalEndpoint.terminalWord (capSubwordNat q offset m) (j.val+2) x =
        TerminalEndpoint.terminalWord q (offset+j.val+2) (offset+x) := by
      intro x hx hxend
      by_cases hlast : x = j.val+2
      · subst x
        have hterminal : offset + (j.val+2) = offset+j.val+2 := by omega
        simp [TerminalEndpoint.terminalWord, capSubwordNat_zero, hterminal]
      · have hxpos : 0 < x := by omega
        have hxlocal : x ≤ m := by omega
        have hnotlast : offset+x ≠ offset+j.val+2 := by omega
        simp [TerminalEndpoint.terminalWord, hlast, hnotlast,
          capSubwordNat_shift q offset m x hxpos hxlocal]
    have hfar : ∀ x y z, i.val+1 ≤ x → x < y → y < z → z ≤ j.val+2 →
        polygonSignArray
          (TerminalEndpoint.terminalWord (capSubwordNat q offset m) (j.val+2)) x y z =
        CurrentTranslation.translateTriple offset
          (polygonSignArray (TerminalEndpoint.terminalWord q (offset+j.val+2))) x y z := by
      intro x y z hx hxy hyz hz
      simp [CurrentTranslation.translateTriple, polygonSignArray, polygonHDet,
        hterm x hx (by omega), hterm y (by omega) (by omega), hterm z (by omega) hz]
    have hnear := translateNear_eq_subword d offset
    have hcur := ordinaryCurrent_shifted_subword
      (fun _ k _ => capSubwordNear d offset k)
      (fun _ k _ => d k)
      (polygonSignArray
        (TerminalEndpoint.terminalWord (capSubwordNat q offset m) (j.val+2)))
      (polygonSignArray (TerminalEndpoint.terminalWord q (offset+j.val+2)))
      offset (i.val+1) (j.val+2) (by omega) hnear.symm hfar
    exact hcur.symm

private theorem capEndpointMatrix_upper
    (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ) (d : ℕ → ℚ) (n : ℕ) :
    CapMatrixRestriction.UpperTriangularBlock
      (CapActualBranches.capEndpointMatrix q p' d n) := by
  intro i j hji
  exact EndpointCurrent.endpointCurrent_below d _ hji

private theorem capInternalMatrix_strictUpper
    (q : ℕ → PlanarPoint ℝ) (d : ℕ → ℚ) (n : ℕ) :
    StrictUpper (CapActualBranches.capInternalMatrix q d n) := by
  exact CapActualBranches.cap_internalMatrix_strictUpper q d n

private theorem capTerminalMatrix_upper
    (q : ℕ → PlanarPoint ℝ) (d : ℕ → ℚ) (n : ℕ) :
    CapMatrixRestriction.UpperTriangularBlock
      (CapActualBranches.capTerminalMatrix q d n) := by
  intro i j hji
  exact TerminalEndpoint.terminalCurrent_below d _ hji

theorem capPairing_submatrix_consecutive
    (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ) (d : ℕ → ℚ)
    {n m offset : ℕ} (hbound : offset + m ≤ n) :
    (globalCapPairing
      (CapActualBranches.capEndpointMatrix q p' d n)
      (CapActualBranches.capInternalMatrix q d n)
      (CapActualBranches.capTerminalMatrix q d n)
      (fun r => d (r.val + 1))).submatrix
      (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound)
      (CapMatrixRestriction.consecutiveBlockEmbedding offset hbound) =
    globalCapPairing
      (CapActualBranches.capEndpointMatrix
        (capSubwordNat q offset m) p' (capSubwordNear d offset) m)
      (CapActualBranches.capInternalMatrix
        (capSubwordNat q offset m) (capSubwordNear d offset) m)
      (CapActualBranches.capTerminalMatrix
        (capSubwordNat q offset m) (capSubwordNear d offset) m)
      (fun r => capSubwordNear d offset (r.val + 1)) := by
  have hF := capEndpointMatrix_upper q p' d n
  have hB := capInternalMatrix_strictUpper q d n
  have hG := capTerminalMatrix_upper q d n
  have hcore := CapMatrixRestriction.globalCapPairing_submatrix_consecutive hbound
      (CapActualBranches.capEndpointMatrix q p' d n)
      (CapActualBranches.capInternalMatrix q d n)
      (CapActualBranches.capTerminalMatrix q d n)
      (fun r => d (r.val+1)) hF hB hG
  rw [capEndpointMatrix_submatrix_consecutive q p' d hbound,
    capInternalMatrix_submatrix_consecutive q d hbound,
    capTerminalMatrix_submatrix_consecutive q d hbound] at hcore
  have hw : (fun r : Fin m => d
      ((CapMatrixRestriction.consecutiveBlockEmbedding offset hbound r).val+1)) =
      (fun r => capSubwordNear d offset (r.val+1)) := by
    funext r
    simp [capSubwordNear, capBlock_val, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [hw] at hcore
  exact hcore


















end DirectGLSSW.CapSubwordBridge
