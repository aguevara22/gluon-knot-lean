import DirectGLSSW.FirstCut
import DirectGLSSW.EndpointSingleGate
import DirectGLSSW.CurrentFidelity
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace DirectGLSSW.OpenCurrentShortFirst
open scoped BigOperators

/-- Constant near data make Phi the same literal weighted cut sum. -/
theorem phi_eq_weightedCutSum (H : TripleArray) (b : IntervalArray)
    {i j : ℕ} (hij : i<j) :
    phi (fun _ _ _ => -1) H b i j =
      weightedCutSum (fun k => (-1-H i k j)/2) b i j := by
  classical
  unfold phi weightedCutSum
  apply Finset.sum_congr rfl
  intro S hS
  unfold cutContribution
  rw [gateProduct_middleNear_eq_prod (fun _ => -1) H hij (Finset.mem_powerset.mp hS)]

theorem weightedCutSum_congr_weights (b : IntervalArray) (w v : ℕ → ℚ)
    (i j : ℕ) (h : ∀ k, i<k → k<j → w k=v k) :
    weightedCutSum w b i j=weightedCutSum v b i j := by
  classical
  unfold weightedCutSum
  apply Finset.sum_congr rfl
  intro S hS
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  have hh := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hS hk)
  exact h k hh.1 hh.2

/-- Algebraic first-edge contraction. The geometric application must prove
all bounded far-row identities; they are not extra source hypotheses. -/
theorem ordinaryCurrent_short_first (H : TripleArray) (i N : ℕ)
    (hfar : ∀ k j, i+1<k → k<j → j≤N → H i k j=H (i+1) k j)
    (j : ℕ) (hij : i+1<j) (hjN : j≤N) :
    ordinaryCurrent (fun _ _ _ => -1) H i j=
      ((1+H i (i+1) (i+2))/2) * ordinaryCurrent (fun _ _ _ => -1) H (i+1) j := by
  classical
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hbase : j=i+2
    · subst j
      rw [ordinaryCurrent_two]
      have hadj := ordinaryCurrent_adjacent (fun _ _ _ => -1) H (i+1)
      have hadj' : ordinaryCurrent (fun _ _ _ => -1) H (i+1) (i+2)=1 := by
        simpa only [Nat.add_assoc] using hadj
      rw [hadj']
      ring
    · have hlong : i+2<j := by omega
      let b := ordinaryCurrent (fun _ _ _ => -1) H
      let w : ℕ → ℚ := fun k => (-1-H i k j)/2
      let η : ℚ := (1+H i (i+1) (i+2))/2
      have hcore : weightedCutSum w b (i+1) j=0 := by
        have hc := ordinaryCurrent_phi (fun _ _ _ => -1) H (show i+1<j by omega)
        rw [phi_eq_weightedCutSum H _ (by omega)] at hc
        have he := weightedCutSum_congr_weights b w
          (fun k => (-1-H (i+1) k j)/2) (i+1) j (by
            intro k hk hkj
            dsimp [w]
            rw [hfar k j hk hkj hjN])
        rw [he]
        simpa [b,source,show j≠(i+1)+1 by omega] using hc
      have hmain : weightedCutSum w b i j=0 := by
        have hc := ordinaryCurrent_phi (fun _ _ _ => -1) H (show i<j by omega)
        rw [phi_eq_weightedCutSum H _ (by omega)] at hc
        simpa [b,w,source,show j≠i+1 by omega] using hc
      have hsplit : Finset.Ioo i j=insert (i+1) (Finset.Ioo (i+1) j) := by
        ext k
        simp only [Finset.mem_Ioo,Finset.mem_insert]
        omega
      have hnot : i+1 ∉ Finset.Ioo (i+1) j := by simp
      rw [weightedCutSum_eq_firstCut w b (show i<j by omega),hsplit,
        Finset.sum_insert hnot,hcore,mul_zero,zero_add] at hmain
      have hsum :
          (∑ k ∈ Finset.Ioo (i+1) j, b i k*w k*weightedCutSum w b k j)=
          η * ∑ k ∈ Finset.Ioo (i+1) j, b (i+1) k*w k*weightedCutSum w b k j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_Ioo.mp hk
        have hb : b i k=η*b (i+1) k := ih k hk'.2 hk'.1 (by omega)
        rw [hb]
        ring
      rw [hsum] at hmain
      rw [weightedCutSum_eq_firstCut w b (show i+1<j by omega)] at hcore
      change b i j=η*b (i+1) j
      have hmul := congrArg (fun x : ℚ => η*x) hcore
      simp only [mul_add,mul_zero] at hmul
      linarith only [hmain,hmul]

end DirectGLSSW.OpenCurrentShortFirst



