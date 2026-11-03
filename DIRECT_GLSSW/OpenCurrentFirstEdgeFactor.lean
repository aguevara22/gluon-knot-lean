import DirectGLSSW.FirstCut
import DirectGLSSW.CurrentFidelity
import DirectGLSSW.OpenMarkedCurrent

set_option autoImplicit false

namespace DirectGLSSW
open scoped BigOperators

/-- Conditional first-edge factorization for the negative unit cut weight.
The endpoint row must scale by `eta` on every later cut, including the far
endpoint. -/
theorem weightedCutSum_neg_one_first_edge_factor
    (b : IntervalArray) {i j : ℕ} (eta : ℚ)
    (hij : i + 1 < j) (hadj : b i (i + 1) = 1)
    (hscale : ∀ k, i + 1 < k → k ≤ j → b i k = eta * b (i + 1) k) :
    weightedCutSum (fun _ : ℕ => -1) b i j =
      (eta - 1) * weightedCutSum (fun _ : ℕ => -1) b (i + 1) j := by
  classical
  let w : ℕ → ℚ := fun _ => -1
  let W : ℕ → ℕ → ℚ := weightedCutSum w b
  have hsplit : Finset.Ioo i j = insert (i + 1) (Finset.Ioo (i + 1) j) := by
    ext k
    simp only [Finset.mem_Ioo, Finset.mem_insert]
    omega
  have hmiddle : i + 1 ∈ Finset.Ioo i j := by
    simp only [Finset.mem_Ioo]
    omega
  have hsum : (∑ k ∈ Finset.Ioo i j, b i k * (-1 : ℚ) * W k j) =
      b i (i + 1) * (-1) * W (i + 1) j +
        ∑ k ∈ Finset.Ioo (i + 1) j, b i k * (-1 : ℚ) * W k j := by
    have hnot : i + 1 ∉ Finset.Ioo (i + 1) j := by
      simp only [Finset.mem_Ioo]
      omega
    rw [hsplit, Finset.sum_insert hnot]
  have htail : (∑ k ∈ Finset.Ioo (i + 1) j,
      b i k * (-1 : ℚ) * W k j) =
      -eta * ∑ k ∈ Finset.Ioo (i + 1) j,
        b (i + 1) k * W k j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Ioo.mp hk
    rw [hscale k hk'.1 (Nat.le_of_lt hk'.2)]
    ring
  have hfirstI := weightedCutSum_eq_firstCut w b (by omega : i < j)
  have hfirstTail := weightedCutSum_eq_firstCut w b hij
  have hfar : b i j = eta * b (i + 1) j := hscale j (by omega) le_rfl
  change W i j = (eta - 1) * W (i + 1) j
  change W i j = b i j +
    ∑ k ∈ Finset.Ioo i j, b i k * w k * W k j at hfirstI
  change W (i + 1) j = b (i + 1) j +
    ∑ k ∈ Finset.Ioo (i + 1) j,
      b (i + 1) k * w k * W k j at hfirstTail
  have hsumTail : (∑ k ∈ Finset.Ioo (i + 1) j,
      b (i + 1) k * w k * W k j) =
      -(∑ k ∈ Finset.Ioo (i + 1) j,
        b (i + 1) k * W k j) := by
    simp [w]
  calc
    W i j = b i j +
        ∑ k ∈ Finset.Ioo i j, b i k * w k * W k j := hfirstI
    _ = eta * b (i + 1) j - W (i + 1) j -
        eta * (∑ k ∈ Finset.Ioo (i + 1) j,
          b (i + 1) k * W k j) := by
          rw [hsum, hadj, htail, hfar]
          ring
    _ = (eta - 1) * W (i + 1) j := by
          rw [hsumTail] at hfirstTail
          calc
            _ = eta * (b (i + 1) j -
                (∑ k ∈ Finset.Ioo (i + 1) j,
                  b (i + 1) k * W k j)) - W (i + 1) j := by ring
            _ = eta * (b (i + 1) j +
                -(∑ k ∈ Finset.Ioo (i + 1) j,
                  b (i + 1) k * W k j)) - W (i + 1) j := by ring
            _ = eta * W (i + 1) j - W (i + 1) j := by
              rw [← hfirstTail]
            _ = (eta - 1) * W (i + 1) j := by ring

end DirectGLSSW

namespace DirectGLSSW.OpenMarkedCurrent

/-- Conditional specialization to the actual open marked-current entry, whose
interval array is the ordinary current at the auxiliary choice `D = -1`. -/
theorem entry_first_edge_factor (H : TripleArray) {i j : ℕ} (eta : ℚ)
    (hij : i + 1 < j)
    (hscale : ∀ k, i + 1 < k → k ≤ j →
      ordinaryCurrent (fun _ _ _ => -1) H i k =
        eta * ordinaryCurrent (fun _ _ _ => -1) H (i + 1) k) :
    entry H i j = (eta - 1) * entry H (i + 1) j := by
  unfold entry
  apply weightedCutSum_neg_one_first_edge_factor
  · exact hij
  · exact ordinaryCurrent_adjacent _ _ i
  · exact hscale





end DirectGLSSW.OpenMarkedCurrent
