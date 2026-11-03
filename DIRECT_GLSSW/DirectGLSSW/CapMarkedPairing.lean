import DirectGLSSW.EndpointSingleGate
import DirectGLSSW.CapCutExpansion
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW
open scoped BigOperators

/-- Under zero top near gates, every nonempty actual cut term vanishes. -/
private theorem nonUnary_zero_of_top_gate
    (d : ℕ → ℚ) (H : TripleArray) (b : IntervalArray)
    {i j : ℕ} (hij : i < j)
    (htop : ∀ k, k ∈ Finset.Ioo i j → H i k j = d k) :
    nonUnary (fun _ k _ => d k) H b i j = 0 := by
  classical
  unfold nonUnary
  apply Finset.sum_eq_zero
  intro S hS
  have hnot : S ≠ ∅ := (Finset.mem_erase.mp hS).1
  have hsubset : S ⊆ Finset.Ioo i j :=
    Finset.mem_powerset.mp (Finset.mem_erase.mp hS).2
  have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hnot
  have hgate : ∏ k ∈ S, (d k - H i k j) / 2 = 0 := by
    obtain ⟨k, hk⟩ := hne
    apply Finset.prod_eq_zero hk
    rw [htop k (hsubset hk)]
    ring
  unfold cutContribution
  rw [gateProduct_middleNear_eq_prod d H hij hsubset, hgate]
  simp

/-- The ordinary top current vanishes when all its near gates vanish. -/
theorem ordinaryCurrent_zero_of_top_gate
    (d : ℕ → ℚ) (H : TripleArray) {i j : ℕ}
    (hgap : i + 1 < j)
    (htop : ∀ k, k ∈ Finset.Ioo i j → H i k j = d k) :
    ordinaryCurrent (fun _ k _ => d k) H i j = 0 := by
  have hij : i < j := by omega
  let D : TripleArray := fun _ k _ => d k
  let b : IntervalArray := fun a c =>
    if _h : c - a < j - i then ordinaryCurrent D H a c else 0
  rw [ordinaryCurrent]
  change source i j - nonUnary D H b i j = 0
  rw [nonUnary_zero_of_top_gate d H b hij htop]
  simp [source]
  omega

/-- The marked complementary word has the actual finite matrix cut expansion
under middle-only near data and zero ordinary top current. -/
theorem markedAmplitude_eq_capCutExpansion_middleNear
    (d : ℕ → ℚ) (H : TripleArray) {i j : ℕ}
    (hgap : i + 1 < j)
    (htop : ∀ k, k ∈ Finset.Ioo i j → H i k j = d k) :
    markedAmplitude (fun _ k _ => d k) H i j =
      capCutExpansion (j := j) d
        (ordinaryCurrent (fun _ k _ => d k) H) i := by
  classical
  have hij : i < j := by omega
  let D : TripleArray := fun _ k _ => d k
  let b : IntervalArray := ordinaryCurrent D H
  have hbzero : b i j = 0 := by
    exact ordinaryCurrent_zero_of_top_gate d H hgap htop
  have hnon : nonUnary D (fun a k c => -H a k c) b i j =
      weightedCutSumNonempty d b i j := by
    unfold nonUnary weightedCutSumNonempty
    apply Finset.sum_congr rfl
    intro S hS
    have hsubset : S ⊆ Finset.Ioo i j :=
      Finset.mem_powerset.mp (Finset.mem_erase.mp hS).2
    unfold cutContribution
    rw [gateProduct_middleNear_eq_prod d (fun a k c => -H a k c) hij hsubset]
    have hprod :
        (∏ k ∈ S, (d k - (-(H i k j))) / 2) = ∏ k ∈ S, d k := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [htop k (hsubset hk)]
      ring
    rw [hprod]
  unfold markedAmplitude
  rw [phi_eq_unary_add D (fun a k c => -H a k c) b i j]
  rw [hbzero, zero_add, hnon]
  exact weightedCutSumNonempty_eq_capCutExpansion d b hij





end DirectGLSSW
