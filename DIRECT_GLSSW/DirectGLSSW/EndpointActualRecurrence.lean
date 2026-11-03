import DirectGLSSW.EndpointCurrent
import DirectGLSSW.FirstCut
import DirectGLSSW.EndpointSingleGate

set_option autoImplicit false

namespace DirectGLSSW.EndpointCurrent
open DirectGLSSW
open scoped BigOperators

/-- The endpoint recurrence coefficient is the first-cut gate times the
actual parent weighted cut sum on the remaining interval. -/
def endpointCoefficient (d : ℕ → ℚ) (H : TripleArray) (k J : ℕ) : ℚ :=
  ((d k - H 0 k J) / 2) *
    weightedCutSum (fun l => (d l - H 0 l J) / 2)
      (ordinaryCurrent (fun _ l _ => d l) H) k J

/-- Weighted cut sums are unchanged when their branch arrays agree on every
interval branch. -/
theorem weightedCutSum_congr_of_branch_eq (w : ℕ → ℚ)
    {b₁ b₂ : IntervalArray} {i j : ℕ} (hij : i < j)
    (hbranches : ∀ a b, i ≤ a → a < b → b ≤ j → b₁ a b = b₂ a b) :
    weightedCutSum w b₁ i j = weightedCutSum w b₂ i j := by
  classical
  unfold weightedCutSum
  apply Finset.sum_congr rfl
  intro S hS
  have hSsub : S ⊆ Finset.Ioo i j := Finset.mem_powerset.mp hS
  have hbranch : branchProduct b₁ (cutVertices i j S) =
      branchProduct b₂ (cutVertices i j S) := by
    by_cases hSne : S.Nonempty
    · unfold branchProduct
      congr 1
      apply List.map_congr_left
      rintro ⟨a, b⟩ hab
      have hb := cutVertices_branch_bounds hij hSsub hSne hab
      exact hbranches a b hb.1 hb.2.1 hb.2.2.1
    · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
      subst S
      simp [branchProduct, cutVertices, hbranches i j le_rfl hij le_rfl]
  rw [hbranch]

/-- The actual endpoint current satisfies its upper-triangular recurrence.
The coefficient uses the parent far array and the actual full weighted
cut sum; no linearity premise is assumed. -/
theorem endpointCurrent_recurrence (d : ℕ → ℚ) (H : TripleArray)
    {a i : ℕ} (hai : a ≤ i) :
    endpointCurrent d H a i =
      source a (i + 1) -
        ∑ k ∈ Finset.Ioo a (i + 1),
          endpointCurrent d H a (k - 1) * endpointCoefficient d H k (i + 1) := by
  classical
  let D : TripleArray := fun _ l _ => d l
  let Hfar : TripleArray := endpointFar a H
  let bfar : IntervalArray := ordinaryCurrent D Hfar
  let w : ℕ → ℚ := fun l => (d l - H 0 l (i + 1)) / 2
  have hai' : a < i + 1 := by omega
  have hfull : weightedCutSum w bfar a (i + 1) = phi D Hfar bfar a (i + 1) := by
    unfold weightedCutSum phi
    apply Finset.sum_congr rfl
    intro S hS
    have hSsub : S ⊆ Finset.Ioo a (i + 1) := Finset.mem_powerset.mp hS
    rw [cutContribution, gateProduct_middleNear_eq_prod d Hfar hai' hSsub]
    have hgate : (∏ l ∈ S, (d l - Hfar a l (i + 1)) / 2) =
        ∏ l ∈ S, w l := by
      apply Finset.prod_congr rfl
      intro l hl
      simp [w, Hfar, endpointFar]
    rw [hgate]
  have hphi := ordinaryCurrent_phi D Hfar hai'
  have hfirst := weightedCutSum_eq_firstCut w bfar hai'
  have htail :
      (∑ k ∈ Finset.Ioo a (i + 1),
        bfar a k * w k * weightedCutSum w bfar k (i + 1)) =
        nonUnary D Hfar bfar a (i + 1) := by
    have hsum : bfar a (i + 1) +
        (∑ k ∈ Finset.Ioo a (i + 1),
          bfar a k * w k * weightedCutSum w bfar k (i + 1)) =
        source a (i + 1) := by
      calc
        _ = weightedCutSum w bfar a (i + 1) := hfirst.symm
        _ = phi D Hfar bfar a (i + 1) := hfull
        _ = source a (i + 1) := hphi
    have hsource : bfar a (i + 1) +
        nonUnary D Hfar bfar a (i + 1) = source a (i + 1) := by
      calc
        _ = phi D Hfar bfar a (i + 1) := (phi_eq_unary_add D Hfar bfar a (i + 1)).symm
        _ = source a (i + 1) := hphi
    exact add_left_cancel (hsum.trans hsource.symm)
  have hrec := ordinaryCurrent_recurrence D Hfar hai'
  conv_lhs => simp [endpointCurrent, hai]
  rw [hrec]
  have hsum :
      (∑ k ∈ Finset.Ioo a (i + 1),
        endpointCurrent d H a (k - 1) * endpointCoefficient d H k (i + 1)) =
      (∑ k ∈ Finset.Ioo a (i + 1),
        bfar a k * w k * weightedCutSum w bfar k (i + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Ioo.mp hk
    have hak : a ≤ k - 1 := by omega
    have hkJ : k < i + 1 := hk'.2
    have hcur : endpointCurrent d H a (k - 1) = bfar a k := by
      simp only [endpointCurrent, if_pos hak]
      rw [Nat.sub_add_cancel (show 1 ≤ k by omega)]
    have hlocal : weightedCutSum w bfar k (i + 1) =
        weightedCutSum w (ordinaryCurrent D H) k (i + 1) := by
      apply weightedCutSum_congr_of_branch_eq w hkJ
      intro x y hkx hxy hyJ
      exact ordinaryCurrent_endpointFar_core d H (by omega) hxy
    have hcoef : endpointCoefficient d H k (i + 1) =
        w k * weightedCutSum w bfar k (i + 1) := by
      simp [endpointCoefficient, w, hlocal, D]
    rw [hcur, hcoef]
    ring
  change source a (i + 1) - nonUnary D Hfar bfar a (i + 1) = _
  rw [hsum, htail]





end DirectGLSSW.EndpointCurrent
