import DirectGLSSW.FirstCut
import DirectGLSSW.EndpointActualRecurrence
import DirectGLSSW.OpenMarkedCurrent

set_option autoImplicit false

namespace DirectGLSSW
open scoped BigOperators

/-- First-row propagation for the signed weighted cut resolvent. The hypotheses
state precisely that the two arrays agree on the positive-index suffix, that
below row K the parent suffix agrees with bMinus, and that only the first row
jumps, with coefficient A beginning strictly after K. -/
theorem weightedCutSum_firstRow_jump
    (bMinus bPlus bParent : IntervalArray) (A : ℚ) {K N : ℕ}
    (hKN : K < N)
    (hSuffix : ∀ i j, 0 < i → i < j → j ≤ N → bPlus i j = bMinus i j)
    (hParentSuffix : ∀ i j, K < i → i < j → j ≤ N → bParent i j = bMinus i j)
    (hrow : ∀ j, 0 < j → j ≤ N →
      bPlus 0 j - bMinus 0 j = if K < j then A * bParent K j else 0) :
    weightedCutSum (fun _ : ℕ => -1) bPlus 0 N -
        weightedCutSum (fun _ : ℕ => -1) bMinus 0 N =
      A * weightedCutSum (fun _ : ℕ => -1) bParent K N := by
  let w : ℕ → ℚ := fun _ => -1
  have h0N : 0 < N := by omega
  have hplusFirst := weightedCutSum_eq_firstCut w bPlus (show 0 < N by omega)
  have hminusFirst := weightedCutSum_eq_firstCut w bMinus (show 0 < N by omega)
  have hparentFirst := weightedCutSum_eq_firstCut w bParent hKN
  have hplusTail (j : ℕ) (hj : j ∈ Finset.Ioo 0 N) :
      weightedCutSum w bPlus j N = weightedCutSum w bMinus j N := by
    have hj' := Finset.mem_Ioo.mp hj
    apply EndpointCurrent.weightedCutSum_congr_of_branch_eq w (by omega)
    intro i k hji hik hkN
    exact hSuffix i k (by omega) hik hkN
  have hparentTail (j : ℕ) (hj : j ∈ Finset.Ioo K N) :
      weightedCutSum w bMinus j N = weightedCutSum w bParent j N := by
    have hj' := Finset.mem_Ioo.mp hj
    apply EndpointCurrent.weightedCutSum_congr_of_branch_eq w (by omega)
    intro i k hji hik hkN
    exact (hParentSuffix i k (by omega) hik hkN).symm
  have hfirstDifference :
      weightedCutSum w bPlus 0 N - weightedCutSum w bMinus 0 N =
        (bPlus 0 N - bMinus 0 N) +
          ∑ j ∈ Finset.Ioo 0 N,
            (bPlus 0 j * w j * weightedCutSum w bPlus j N -
              bMinus 0 j * w j * weightedCutSum w bMinus j N) := by
    rw [hplusFirst, hminusFirst]
    calc
      (bPlus 0 N + ∑ j ∈ Finset.Ioo 0 N,
          bPlus 0 j * w j * weightedCutSum w bPlus j N) -
        (bMinus 0 N + ∑ j ∈ Finset.Ioo 0 N,
          bMinus 0 j * w j * weightedCutSum w bMinus j N) =
        (bPlus 0 N - bMinus 0 N) +
          ((∑ j ∈ Finset.Ioo 0 N, bPlus 0 j * w j * weightedCutSum w bPlus j N) -
           ∑ j ∈ Finset.Ioo 0 N, bMinus 0 j * w j * weightedCutSum w bMinus j N) := by ring
      _ = (bPlus 0 N - bMinus 0 N) +
          ∑ j ∈ Finset.Ioo 0 N,
            (bPlus 0 j * w j * weightedCutSum w bPlus j N -
              bMinus 0 j * w j * weightedCutSum w bMinus j N) := by
        rw [← Finset.sum_sub_distrib]
  have hrowTerms :
      (∑ j ∈ Finset.Ioo 0 N,
        (bPlus 0 j * w j * weightedCutSum w bPlus j N -
          bMinus 0 j * w j * weightedCutSum w bMinus j N)) =
        A * ∑ j ∈ Finset.Ioo K N,
          bParent K j * w j * weightedCutSum w bParent j N := by
    calc
      _ = ∑ j ∈ Finset.Ioo 0 N,
          ((if K < j then A * bParent K j else 0) * w j *
            weightedCutSum w bMinus j N) := by
          apply Finset.sum_congr rfl
          intro j hj
          have htail := hplusTail j hj
          have hj' := Finset.mem_Ioo.mp hj
          rw [htail]
          calc
            bPlus 0 j * w j * weightedCutSum w bMinus j N -
                bMinus 0 j * w j * weightedCutSum w bMinus j N =
              (bPlus 0 j - bMinus 0 j) * w j * weightedCutSum w bMinus j N := by ring
            _ = (if K < j then A * bParent K j else 0) * w j *
                weightedCutSum w bMinus j N := by
              rw [hrow j hj'.1 (by omega)]
      _ = ∑ j ∈ Finset.Ioo K N,
          A * bParent K j * w j * weightedCutSum w bParent j N := by
          have hsubset : Finset.Ioo K N ⊆ Finset.Ioo 0 N := by
            intro j hj
            simp only [Finset.mem_Ioo] at hj ⊢
            omega
          have hzero : ∀ j ∈ Finset.Ioo 0 N, j ∉ Finset.Ioo K N →
              (if K < j then A * bParent K j else 0) * w j *
                weightedCutSum w bMinus j N = 0 := by
            intro j hj hjNot
            have hj' := Finset.mem_Ioo.mp hj
            have hnot : ¬ K < j := by
              intro hKj
              apply hjNot
              exact Finset.mem_Ioo.mpr ⟨hKj, hj'.2⟩
            simp [hnot]
          calc
            _ = ∑ j ∈ Finset.Ioo K N,
                (if K < j then A * bParent K j else 0) * w j *
                  weightedCutSum w bMinus j N :=
              (Finset.sum_subset hsubset hzero).symm
            _ = ∑ j ∈ Finset.Ioo K N,
                A * bParent K j * w j * weightedCutSum w bParent j N := by
              apply Finset.sum_congr rfl
              intro j hj
              have htail := hparentTail j hj
              have hj' := Finset.mem_Ioo.mp hj
              simp only [if_pos hj'.1]
              rw [htail]
      _ = A * ∑ j ∈ Finset.Ioo K N,
          bParent K j * w j * weightedCutSum w bParent j N := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
  have hrowN : bPlus 0 N - bMinus 0 N = A * bParent K N := by
    rw [hrow N h0N le_rfl]
    simp [hKN]
  calc
    weightedCutSum w bPlus 0 N - weightedCutSum w bMinus 0 N =
        (bPlus 0 N - bMinus 0 N) +
          ∑ j ∈ Finset.Ioo 0 N,
            (bPlus 0 j * w j * weightedCutSum w bPlus j N -
              bMinus 0 j * w j * weightedCutSum w bMinus j N) := hfirstDifference
    _ = A * bParent K N +
          A * ∑ j ∈ Finset.Ioo K N,
            bParent K j * w j * weightedCutSum w bParent j N := by rw [hrowN,hrowTerms]
    _ = A * (bParent K N +
          ∑ j ∈ Finset.Ioo K N,
            bParent K j * w j * weightedCutSum w bParent j N) := by ring
    _ = A * weightedCutSum w bParent K N := by rw [hparentFirst]
    _ = A * weightedCutSum (fun _ : ℕ => -1) bParent K N := by rfl

/-- The same first-row jump applies directly to the actual open marked currents
when their ordinary-current arrays satisfy the explicit suffix and row
hypotheses. Those conditions remain premises; this theorem adds no geometric
row-jump claim. -/
theorem openMarkedCurrent_entry_firstRow_jump
    (HMinus HPlus HParent : TripleArray) (A : ℚ) {K N : ℕ}
    (hKN : K < N)
    (hSuffix : ∀ i j, 0 < i → i < j → j ≤ N →
      ordinaryCurrent (fun _ _ _ => -1) HPlus i j =
        ordinaryCurrent (fun _ _ _ => -1) HMinus i j)
    (hParentSuffix : ∀ i j, K < i → i < j → j ≤ N →
      ordinaryCurrent (fun _ _ _ => -1) HParent i j =
        ordinaryCurrent (fun _ _ _ => -1) HMinus i j)
    (hrow : ∀ j, 0 < j → j ≤ N →
      ordinaryCurrent (fun _ _ _ => -1) HPlus 0 j -
        ordinaryCurrent (fun _ _ _ => -1) HMinus 0 j =
          if K < j then A * ordinaryCurrent (fun _ _ _ => -1) HParent K j else 0) :
    OpenMarkedCurrent.entry HPlus 0 N - OpenMarkedCurrent.entry HMinus 0 N =
      A * OpenMarkedCurrent.entry HParent K N := by
  unfold OpenMarkedCurrent.entry
  exact weightedCutSum_firstRow_jump
    (ordinaryCurrent (fun _ _ _ => -1) HMinus)
    (ordinaryCurrent (fun _ _ _ => -1) HPlus)
    (ordinaryCurrent (fun _ _ _ => -1) HParent) A hKN hSuffix hParentSuffix hrow




end DirectGLSSW
