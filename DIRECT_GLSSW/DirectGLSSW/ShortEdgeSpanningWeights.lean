import DirectGLSSW.ShortEdgeSpanning
import DirectGLSSW.ShortEdgeSpanningPullback
import DirectGLSSW.ShortEdgeSpanningBranches

namespace DirectGLSSW.ShortEdgeWeighted.SpanningWeightsImpl
open scoped BigOperators

theorem cutAtA_contribution
    (a i j L R : ℕ) (ha : 0 < a) (hiA : i < a) (hBj : a + 1 < j)
    (t : ℕ → Sign) (U : IntervalArray) (η : Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioo i (collapseAfter a j))
    (htriple : (L,a,R) ∈ cutTriples i (collapseAfter a j) S) :
    cutContribution (D1 a t D) (fun x k y => -η.value * H1 a t H x k y)
      (parentTable a ha t U) i j (ShortEdgeCutFibers.spanCandidate a S .cutAtA) =
      ((beta a t - (t R).value) / 2) *
        cutContribution (D0 a t D) (fun x k y => -η.value * H0 H x k y)
          U i (collapseAfter a j) S
 := by
  have hc : a < collapseAfter a j := by
    change a < ShortEdgeCutFibers.collapseAfter a j
    rw [ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)]
    omega
  have hij : i < collapseAfter a j := by omega
  have haS : a ∈ S := cutTriples_middle_mem hij hS htriple
  have hci : ShortEdgeCutFibers.collapseAfter a i = i :=
    ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
  have hfi : ShortEdgeCutFibers.liftAfter a i = i := by
    simp [ShortEdgeCutFibers.liftAfter, show i ≤ a by omega]
  have hfj : ShortEdgeCutFibers.liftAfter a (collapseAfter a j) = j := by
    simp only [ShortEdgeCutFibers.liftAfter, if_neg (by omega : ¬ collapseAfter a j ≤ a)]
    change ShortEdgeCutFibers.collapseAfter a j + 1 = j
    rw [ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)]
    omega
  have hword := spanCandidate_cutAtA_word a i j ha hiA hBj S haS hS
  rw [hci] at hword
  have hgate := SpanningPullbackImpl.gateProduct_liftAfter_pullback
    a t D H η i (collapseAfter a j) (cutVertices i (collapseAfter a j) S)
  rw [hfi, hfj] at hgate
  unfold cutContribution
  rw [hword, hgate, SpanningBranchesImpl.branchProduct_cutAtA
    a i (collapseAfter a j) L R ha hij t U S hS htriple]
  ring

theorem cutAtB_contribution
    (a i j L R : ℕ) (ha : 0 < a) (hiA : i < a) (hBj : a + 1 < j)
    (t : ℕ → Sign) (U : IntervalArray) (η : Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioo i (collapseAfter a j))
    (htriple : (L,a,R) ∈ cutTriples i (collapseAfter a j) S) :
    cutContribution (D1 a t D) (fun x k y => -η.value * H1 a t H x k y)
      (parentTable a ha t U) i j (ShortEdgeCutFibers.spanCandidate a S .cutAtB) =
      ((alpha a ha t - (t L).value) / 2) *
        cutContribution (D0 a t D) (fun x k y => -η.value * H0 H x k y)
          U i (collapseAfter a j) S
 := by
  have hc : a < collapseAfter a j := by
    change a < ShortEdgeCutFibers.collapseAfter a j
    rw [ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)]
    omega
  have hij : i < collapseAfter a j := by omega
  have haS : a ∈ S := cutTriples_middle_mem hij hS htriple
  have hci : ShortEdgeCutFibers.collapseAfter a i = i :=
    ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
  have hfi : SpanningPullbackImpl.liftAt a i = i := by
    simp [SpanningPullbackImpl.liftAt, hiA]
  have hfj : SpanningPullbackImpl.liftAt a (collapseAfter a j) = j := by
    simp only [SpanningPullbackImpl.liftAt,
      if_neg (by omega : ¬ collapseAfter a j < a)]
    change ShortEdgeCutFibers.collapseAfter a j + 1 = j
    rw [ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)]
    omega
  have hword := spanCandidate_cutAtB_word a i j hiA hBj S haS hS
  rw [hci] at hword
  have hgate := SpanningPullbackImpl.gateProduct_liftAt_pullback
    a t D H η i (collapseAfter a j) (cutVertices i (collapseAfter a j) S)
  rw [hfi, hfj] at hgate
  rw [show SpanningPullbackImpl.liftAt a =
    (fun x => if x < a then x else x + 1) from rfl] at hgate
  unfold cutContribution
  rw [hword, hgate, SpanningBranchesImpl.branchProduct_cutAtB
    a i (collapseAfter a j) L R ha hij t U S hS htriple]
  ring

end DirectGLSSW.ShortEdgeWeighted.SpanningWeightsImpl
