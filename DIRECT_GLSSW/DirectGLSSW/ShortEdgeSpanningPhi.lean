import DirectGLSSW.ShortEdgeSpanningWeights
import DirectGLSSW.ShortEdgeSpanningBoth
import DirectGLSSW.ShortEdgeSpanningAnnihilator
import DirectGLSSW.ShortEdgeWordMembership
import DirectGLSSW.ShortEdgeFiberSums
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace DirectGLSSW.ShortEdgeWeighted.SpanningPhiImpl
open scoped BigOperators

theorem spanContribution_threeLifts
    (a i j : ℕ) (ha : 0 < a) (hiA : i < a) (hBj : a + 1 < j)
    (t : ℕ → Sign) (U : IntervalArray) (η : Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign)
    (S : Finset ℕ) (haS : a ∈ S)
    (hS : S ⊆ Finset.Ioo i (collapseAfter a j)) :
    cutContribution (D1 a t D) (fun x k y => -η.value * H1 a t H x k y)
        (parentTable a ha t U) i j (ShortEdgeCutFibers.spanCandidate a S .cutAtA) +
      cutContribution (D1 a t D) (fun x k y => -η.value * H1 a t H x k y)
        (parentTable a ha t U) i j (ShortEdgeCutFibers.spanCandidate a S .cutAtB) +
      cutContribution (D1 a t D) (fun x k y => -η.value * H1 a t H x k y)
        (parentTable a ha t U) i j (ShortEdgeCutFibers.spanCandidate a S .cutAtBoth) =
      kappa a ha t * cutContribution (D0 a t D)
        (fun x k y => -η.value * H0 H x k y) U i (collapseAfter a j) S := by
  have hc : a < collapseAfter a j := by
    change a < ShortEdgeCutFibers.collapseAfter a j
    rw [ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)]
    omega
  have hij : i < collapseAfter a j := by omega
  obtain ⟨pre, L, R, post, hword, _, _, _, hboth⟩ :=
    SpanningBothImpl.spanCandidate_cutAtBoth_contribution_factor
      a i j ha hiA hBj t U η D H S haS hS
  have hci : ShortEdgeCutFibers.collapseAfter a i = i :=
    ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
  rw [hci] at hword hboth
  have htriple : (L,a,R) ∈ cutTriples i (collapseAfter a j) S := by
    simp only [cutTriples, List.mem_toFinset]
    rw [hword]
    exact WordMembershipImpl.triple_mem_splice pre post L a R
  rw [SpanningWeightsImpl.cutAtA_contribution a i j L R ha hiA hBj t U η D H S hS htriple,
    SpanningWeightsImpl.cutAtB_contribution a i j L R ha hiA hBj t U η D H S hS htriple,
    hboth]
  let C := cutContribution (D0 a t D) (fun x k y => -η.value * H0 H x k y)
    U i (collapseAfter a j) S
  have hkill : ((t L).value - η.value * (H i a (collapseAfter a j)).value) * C = 0 :=
    SpanningAnnihilatorImpl.coreContribution_annihilate a i (collapseAfter a j) L R
      S t η D H U (by simpa [cutTriples] using htriple)
  calc
    _ = kappa a ha t * C -
        (((t L).value - η.value * (H i a (collapseAfter a j)).value) * C) / 2 := by
          dsimp [C, kappa]
          ring
    _ = _ := by rw [hkill]; ring

theorem spanningPhi
    (a i j : ℕ) (ha : 0 < a) (hiA : i < a) (hBj : a + 1 < j)
    (t : ℕ → Sign) (U : IntervalArray) (η : Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign) :
    PhiEta η (D1 a t D) (H1 a t H) (parentTable a ha t U) i j =
      kappa a ha t * PhiEta η (D0 a t D) (H0 H) U i (collapseAfter a j) := by
  unfold PhiEta phi
  rw [ShortEdgeFiberSums.sum_parent_spanning a i j hiA hBj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub := Finset.mem_powerset.mp hS
  by_cases haS : a ∈ S
  · rw [if_pos haS]
    exact spanContribution_threeLifts a i j ha hiA hBj t U η D H S haS hsub
  · rw [if_neg haS]
    have hci : ShortEdgeCutFibers.collapseAfter a i = i :=
      ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
    simpa only [hci] using
      spanNoCoreCutContribution a i j ha hiA hBj t U η D H S hsub haS

theorem spanning_ordinary_source
    (a i j : ℕ) (ha : 0 < a) (hiA : i < a) (hBj : a + 1 < j)
    (t : ℕ → Sign) (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign) :
    phi (D1 a t D) (H1 a t H)
      (parentTable a ha t (ordinaryCurrent (D0 a t D) (H0 H))) i j = source i j := by
  have hc : a < collapseAfter a j := by
    change a < ShortEdgeCutFibers.collapseAfter a j
    rw [ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)]
    omega
  have hij : i < collapseAfter a j := by omega
  have hp :
      phi (D1 a t D) (H1 a t H)
          (parentTable a ha t (ordinaryCurrent (D0 a t D) (H0 H))) i j =
        kappa a ha t * phi (D0 a t D) (H0 H)
          (ordinaryCurrent (D0 a t D) (H0 H)) i (collapseAfter a j) := by
    simpa [PhiEta, Sign.value] using
      spanningPhi a i j ha hiA hBj t (ordinaryCurrent (D0 a t D) (H0 H)) .neg D H
  rw [hp, ordinaryCurrent_phi (D0 a t D) (H0 H) hij]
  simp [source, show collapseAfter a j ≠ i + 1 by omega, show j ≠ i + 1 by omega]

end DirectGLSSW.ShortEdgeWeighted.SpanningPhiImpl
