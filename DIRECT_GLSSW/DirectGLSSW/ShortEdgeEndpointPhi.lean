import DirectGLSSW.ShortEdgeFiberSums
import DirectGLSSW.ShortEdgeLeftEndpoint
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace DirectGLSSW.ShortEdgeWeighted.EndpointPhiImpl

open scoped BigOperators

theorem leftEndpointPhi
    (a j : ℕ) (ha : 0 < a) (hBj : a + 1 < j)
    (t : ℕ → Sign) (U : IntervalArray) (η : Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign) :
    PhiEta η (D1 a t D) (H1 a t H) (parentTable a ha t U) a j =
      ((beta a t + η.value * (t (collapseAfter a j)).value) / 2) *
        PhiEta η (D0 a t D) (H0 H) U a (collapseAfter a j)
 := by
  unfold PhiEta phi
  rw [ShortEdgeFiberSums.sum_parent_leftEndpoint a j hBj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  exact LeftEndpointImpl.leftEndpointContribution_twoLifts
    a j ha hBj t U η D H S (Finset.mem_powerset.mp hS)

theorem leftEndpoint_ordinary_source
    (a j : ℕ) (ha : 0 < a) (hBj : a + 1 < j)
    (t : ℕ → Sign) (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign) :
    phi (D1 a t D) (H1 a t H)
      (parentTable a ha t (ordinaryCurrent (D0 a t D) (H0 H))) a j =
        source a j
 := by
  have hcore : a < collapseAfter a j := by
    change a < ShortEdgeCutFibers.collapseAfter a j
    rw [ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a j (by omega)]
    omega
  have hp :
      phi (D1 a t D) (H1 a t H)
          (parentTable a ha t (ordinaryCurrent (D0 a t D) (H0 H))) a j =
        ((beta a t - (t (collapseAfter a j)).value) / 2) *
          phi (D0 a t D) (H0 H) (ordinaryCurrent (D0 a t D) (H0 H))
            a (collapseAfter a j) := by
    simpa [PhiEta, Sign.value, sub_eq_add_neg] using
      leftEndpointPhi a j ha hBj t (ordinaryCurrent (D0 a t D) (H0 H)) .neg D H
  rw [hp, ordinaryCurrent_phi (D0 a t D) (H0 H) hcore]
  have hparent : source a j = 0 := by simp [source, show j ≠ a + 1 by omega]
  rw [hparent]
  by_cases h : collapseAfter a j = a + 1
  · simp [source, h, beta]
  · simp [source, h]

end DirectGLSSW.ShortEdgeWeighted.EndpointPhiImpl
