import DirectGLSSW.GlobalCapCut
import DirectGLSSW.TerminalEndpoint
import DirectGLSSW.EndpointCurrent
import DirectGLSSW.EndpointDirectSource
import DirectGLSSW.CutIncidence
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace DirectGLSSW.CapActualBranches
open scoped BigOperators
open DirectGLSSW

/-- Replace the initial vertex q₀ by the arbitrary first cap point p'. -/
def capComplement (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ) : ℕ → PlanarPoint ℝ :=
  fun x => if x = 0 then p' else q x

/-- The cap polygon has p' first, the original internal vertices, and q₀ last. -/
def capWord (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ) (n : ℕ) : ℕ → PlanarPoint ℝ :=
  fun x => if x = 0 then p' else if x = n + 1 then q 0 else q x

/-- Actual interval current on the cap word. -/
noncomputable def capActualBranch (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ)
    (d : ℕ → ℚ) (n : ℕ) : IntervalArray :=
  fun a b => ordinaryCurrent (fun _ k _ => d k)
    (polygonSignArray (capWord q p' n)) a b

/-- First cap branches, read from the word with q₀ moved to p'. -/
noncomputable def capEndpointMatrix (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ)
    (d : ℕ → ℚ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun a b => EndpointCurrent.endpointCurrent d
    (polygonSignArray (capComplement q p')) a.val b.val

/-- Branches between two internal vertices. -/
noncomputable def capInternalMatrix (q : ℕ → PlanarPoint ℝ) (d : ℕ → ℚ)
    (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun a b => if a.val < b.val then
    ordinaryCurrent (fun _ k _ => d k) (polygonSignArray q)
      (a.val + 1) (b.val + 1) else 0

/-- Final branches returning from an internal vertex to q₀. -/
noncomputable def capTerminalMatrix (q : ℕ → PlanarPoint ℝ) (d : ℕ → ℚ)
    (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun a b => TerminalEndpoint.terminalCurrent d
    (polygonSignArray q) a.val b.val

private theorem capWord_eq_endpointWord
    (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ) {n x : ℕ}
    (hx : x ≤ n) :
    capWord q p' n x = EndpointCurrent.endpointWord (capComplement q p') 0 x := by
  by_cases hx0 : x = 0
  · subst x
    simp [capWord, capComplement, EndpointCurrent.endpointWord]
  · have hxn : x ≠ n + 1 := by omega
    simp [capWord, capComplement, EndpointCurrent.endpointWord, hx0, hxn]

private theorem capWord_eq_terminalWord
    (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ) {n x : ℕ}
    (hx : 1 ≤ x) (hxn : x ≤ n + 1) :
    capWord q p' n x = TerminalEndpoint.terminalWord q (n + 1) x := by
  by_cases hlast : x = n + 1
  · subst x
    simp [capWord, TerminalEndpoint.terminalWord]
  · have hxle : x ≤ n := by omega
    have hx0 : x ≠ 0 := by omega
    simp [capWord, TerminalEndpoint.terminalWord, hlast, hxle, hx0]

private theorem polygonSignArray_eq_of_point_eq
    (q₁ q₂ : ℕ → PlanarPoint ℝ) {i k j : ℕ}
    (hi : q₁ i = q₂ i) (hk : q₁ k = q₂ k) (hj : q₁ j = q₂ j) :
    polygonSignArray q₁ i k j = polygonSignArray q₂ i k j := by
  simp [polygonSignArray, polygonHDet, hi, hk, hj]

private theorem capBranch_first_eq
    (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ) (d : ℕ → ℚ) {n b : ℕ}
    (hn : 0 < n) (hb : 0 < b) (hbn : b ≤ n) :
    capActualBranch q p' d n 0 b =
      capEndpointMatrix q p' d n ⟨0, by omega⟩ ⟨b-1, by omega⟩ := by
  have hword : ∀ x, 0 ≤ x → x ≤ b →
      capWord q p' n x = EndpointCurrent.endpointWord (capComplement q p') 0 x := by
    intro x _ hxb
    exact capWord_eq_endpointWord q p' (le_trans hxb hbn)
  have hcur : ordinaryCurrent (fun _ k _ => d k)
      (polygonSignArray (capWord q p' n)) 0 b =
      ordinaryCurrent (fun _ k _ => d k)
        (polygonSignArray (EndpointCurrent.endpointWord (capComplement q p') 0)) 0 b := by
    apply ordinaryCurrent_congr_interval_fixed_near _ _ _ (by omega)
    intro i k j h0i hik hkj hjb
    exact polygonSignArray_eq_of_point_eq _ _ (hword i (by omega) (by omega))
      (hword k (by omega) (by omega)) (hword j (by omega) hjb)
  have hF := EndpointCurrent.endpointCurrent_polygon_eq (capComplement q p') d
    (a := 0) (i := b-1) (by omega)
  have hF' : EndpointCurrent.endpointCurrent d
      (polygonSignArray (capComplement q p')) 0 (b-1) =
      ordinaryCurrent (fun _ k _ => d k)
        (polygonSignArray (EndpointCurrent.endpointWord (capComplement q p') 0)) 0 b := by
    simpa [Nat.sub_add_cancel hb] using hF
  change ordinaryCurrent (fun _ k _ => d k) (polygonSignArray (capWord q p' n)) 0 b =
    EndpointCurrent.endpointCurrent d (polygonSignArray (capComplement q p'))
      (⟨0, by omega⟩ : Fin n).val (⟨b-1, by omega⟩ : Fin n).val
  simp only [Fin.val_mk]
  exact hcur.trans hF'.symm

private theorem capBranch_middle_eq
    (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ) (d : ℕ → ℚ) {n a b : ℕ}
    (ha : 0 < a) (hab : a < b) (hbn : b ≤ n) :
    capActualBranch q p' d n a b =
      capInternalMatrix q d n ⟨a-1, by omega⟩ ⟨b-1, by omega⟩ := by
  have hcur : ordinaryCurrent (fun _ k _ => d k)
      (polygonSignArray (capWord q p' n)) a b =
      ordinaryCurrent (fun _ k _ => d k) (polygonSignArray q) a b := by
    apply ordinaryCurrent_congr_interval_fixed_near _ _ _ (by omega)
    intro i k j hai hik hkj hjb
    have hi0 : i ≠ 0 := by omega
    have hin : i ≠ n+1 := by omega
    have hk0 : k ≠ 0 := by omega
    have hkn : k ≠ n+1 := by omega
    have hj0 : j ≠ 0 := by omega
    have hjn : j ≠ n+1 := by omega
    have hxi : capWord q p' n i = q i := by simp [capWord, hi0, hin]
    have hxk : capWord q p' n k = q k := by simp [capWord, hk0, hkn]
    have hxj : capWord q p' n j = q j := by simp [capWord, hj0, hjn]
    exact polygonSignArray_eq_of_point_eq _ _ hxi hxk hxj
  change ordinaryCurrent (fun _ k _ => d k) (polygonSignArray (capWord q p' n)) a b =
    (if (⟨a-1, by omega⟩ : Fin n).val < (⟨b-1, by omega⟩ : Fin n).val then
      ordinaryCurrent (fun _ k _ => d k) (polygonSignArray q)
        ((⟨a-1, by omega⟩ : Fin n).val+1) ((⟨b-1, by omega⟩ : Fin n).val+1) else 0)
  have haval : (⟨a-1, by omega⟩ : Fin n).val = a-1 := rfl
  have hbval : (⟨b-1, by omega⟩ : Fin n).val = b-1 := rfl
  have haadd : (a - 1) + 1 = a := Nat.sub_add_cancel (by omega)
  have hbadd : (b - 1) + 1 = b := Nat.sub_add_cancel (by omega)
  rw [haval, hbval, haadd, hbadd, if_pos (by omega)]
  exact hcur

private theorem capBranch_last_eq
    (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ) (d : ℕ → ℚ) {n a : ℕ}
    (hn : 0 < n) (ha : 0 < a) (han : a ≤ n) :
    capActualBranch q p' d n a (n+1) =
      capTerminalMatrix q d n ⟨a-1, by omega⟩ ⟨n-1, by omega⟩ := by
  have hword : ∀ x, a ≤ x → x ≤ n+1 →
      capWord q p' n x = TerminalEndpoint.terminalWord q (n+1) x := by
    intro x hax hxn
    exact capWord_eq_terminalWord q p' (by omega) hxn
  have hcur : ordinaryCurrent (fun _ k _ => d k)
      (polygonSignArray (capWord q p' n)) a (n+1) =
      ordinaryCurrent (fun _ k _ => d k)
        (polygonSignArray (TerminalEndpoint.terminalWord q (n+1))) a (n+1) := by
    apply ordinaryCurrent_congr_interval_fixed_near _ _ _ (by omega)
    intro i k j hai hik hkj hjb
    exact polygonSignArray_eq_of_point_eq _ _ (hword i hai (by omega))
      (hword k (by omega) (by omega)) (hword j (by omega) hjb)
  have hG := TerminalEndpoint.terminalCurrent_polygon_eq q d
    (a := a-1) (b := n-1) (by omega)
  change ordinaryCurrent (fun _ k _ => d k) (polygonSignArray (capWord q p' n)) a (n+1) =
    TerminalEndpoint.terminalCurrent d (polygonSignArray q)
      (⟨a-1, by omega⟩ : Fin n).val (⟨n-1, by omega⟩ : Fin n).val
  have haadd : (a - 1) + 1 = a := Nat.sub_add_cancel (by omega)
  have hnadd : (n - 1) + 2 = n + 1 := by omega
  have hG' : TerminalEndpoint.terminalCurrent d (polygonSignArray q) (a-1) (n-1) =
      ordinaryCurrent (fun _ k _ => d k)
        (polygonSignArray (TerminalEndpoint.terminalWord q (n+1))) a (n+1) := by
    simpa [haadd, hnadd] using hG
  exact hcur.trans hG'.symm

/-- Every proper cap interval branch is the corresponding global cap branch. -/
theorem cap_actual_branch_eq_globalCapBranch
    (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ) (d : ℕ → ℚ)
    {n a b : ℕ} (hn : 0 < n) (hab : a < b)
    (hb : b ≤ n + 1) (hshort : b - a < n + 1) :
    capActualBranch q p' d n a b =
      globalCapBranch (capEndpointMatrix q p' d n)
        (capInternalMatrix q d n) (capTerminalMatrix q d n)
        ⟨0, by omega⟩ ⟨n - 1, by omega⟩ a b := by
  by_cases ha : a = 0
  · subst a
    have hbpos : 0 < b := by omega
    by_cases hblast : b = n + 1
    · omega
    · have hbn : b ≤ n := by omega
      have he := capBranch_first_eq q p' d hn hbpos hbn
      simpa [globalCapBranch, capEndpointMatrix, capInternalMatrix,
        capTerminalMatrix, hbpos, hbn, hn] using he
  · have hapos : 0 < a := by omega
    by_cases hblast : b = n + 1
    · subst b
      have han : a ≤ n := by omega
      have he := capBranch_last_eq q p' d hn hapos han
      simpa [globalCapBranch, capEndpointMatrix, capInternalMatrix,
        capTerminalMatrix, hapos, ha, han, hn] using he
    · have hbn : b ≤ n := by omega
      have han : a ≤ n := by omega
      have hbpos : 0 < b := by omega
      have he := capBranch_middle_eq q p' d hapos hab hbn
      have hsub : a - 1 < b - 1 := by omega
      simpa [globalCapBranch, capEndpointMatrix, capInternalMatrix,
        capTerminalMatrix, hapos, ha, han, hbpos, hbn, hblast, hsub] using he

/-- The internal parent-current matrix is upper triangular. -/
theorem cap_internalMatrix_strictUpper
    (q : ℕ → PlanarPoint ℝ) (d : ℕ → ℚ) (n : ℕ) :
    StrictUpper (capInternalMatrix q d n) := by
  intro a b hba
  simp [capInternalMatrix, Nat.not_lt.mpr hba]

private theorem cap_actual_nonemptyCutSum_eq_globalCutSum
    (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ) (d : ℕ → ℚ) {n : ℕ}
    (hn : 0 < n) :
    weightedCutSumNonempty d (capActualBranch q p' d n) 0 (n+1) =
      weightedCutSumNonempty (globalCapNear (fun r : Fin n => d (r.val+1)))
        (globalCapBranch (capEndpointMatrix q p' d n)
          (capInternalMatrix q d n) (capTerminalMatrix q d n)
          ⟨0, by omega⟩ ⟨n-1, by omega⟩) 0 (n+1) := by
  classical
  unfold weightedCutSumNonempty
  apply Finset.sum_congr rfl
  intro S hS
  have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1
  have hsub : S ⊆ Finset.Ioo 0 (n+1) :=
    Finset.mem_powerset.mp (Finset.mem_erase.mp hS).2
  have hweights : (∏ k ∈ S, d k) =
      ∏ k ∈ S, globalCapNear (fun r : Fin n => d (r.val+1)) k := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkin := Finset.mem_Ioo.mp (hsub hk)
    let r : Fin n := ⟨k-1, by omega⟩
    have hrval : r.val + 1 = k := by dsimp [r]; omega
    rw [← hrval, globalCapNear_at_internal]
  have hbranch : branchProduct (capActualBranch q p' d n) (cutVertices 0 (n+1) S) =
      branchProduct (globalCapBranch (capEndpointMatrix q p' d n)
        (capInternalMatrix q d n) (capTerminalMatrix q d n)
        ⟨0, by omega⟩ ⟨n-1, by omega⟩) (cutVertices 0 (n+1) S) := by
    rw [branchProduct_eq_prod_cutEdges _ (by omega) hsub,
      branchProduct_eq_prod_cutEdges _ (by omega) hsub]
    apply Finset.prod_congr rfl
    intro e he
    have hpair : (e.1, e.2) ∈ (cutVertices 0 (n+1) S).zip
        (cutVertices 0 (n+1) S).tail := by
      simpa [cutEdges] using he
    have hb := cutVertices_branch_bounds (by omega) hsub hne hpair
    exact cap_actual_branch_eq_globalCapBranch q p' d
      (n := n) (a := e.1) (b := e.2) hn
      hb.2.1 hb.2.2.1 hb.2.2.2
  rw [hweights, hbranch]

theorem weightedCutSumNonempty_cap_actual_eq_globalCapPairing
    (q : ℕ → PlanarPoint ℝ) (p' : PlanarPoint ℝ)
    (d : ℕ → ℚ) {n : ℕ} (hn : 0 < n) :
    weightedCutSumNonempty d (capActualBranch q p' d n) 0 (n + 1) =
      globalCapPairing (capEndpointMatrix q p' d n)
        (capInternalMatrix q d n) (capTerminalMatrix q d n)
        (fun r => d (r.val + 1))
        ⟨0, by omega⟩ ⟨n - 1, by omega⟩ := by
  calc
    _ = weightedCutSumNonempty (globalCapNear (fun r : Fin n => d (r.val+1)))
        (globalCapBranch (capEndpointMatrix q p' d n)
          (capInternalMatrix q d n) (capTerminalMatrix q d n)
          ⟨0, by omega⟩ ⟨n-1, by omega⟩) 0 (n+1) :=
      cap_actual_nonemptyCutSum_eq_globalCutSum q p' d hn
    _ = globalCapPairing (capEndpointMatrix q p' d n)
        (capInternalMatrix q d n) (capTerminalMatrix q d n)
        (fun r => d (r.val+1)) ⟨0, by omega⟩ ⟨n-1, by omega⟩ := by
      apply weightedCutSumNonempty_globalCapPairing
        (capEndpointMatrix q p' d n) (capInternalMatrix q d n)
        (capTerminalMatrix q d n) (fun r => d (r.val+1))
        (cap_internalMatrix_strictUpper q d n)












end DirectGLSSW.CapActualBranches
