import DirectGLSSW.ShortEdgeFiberSums
import DirectGLSSW.ShortEdgeRightEndpoint
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace DirectGLSSW.ShortEdgeWeighted.RightEndpointPhiImpl
open scoped BigOperators

theorem rightEndpointPhi
    (a i : ℕ) (ha : 0 < a) (hiA : i < a)
    (t : ℕ → Sign) (U : IntervalArray) (η : Sign)
    (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign) :
    PhiEta η (D1 a t D) (H1 a t H) (parentTable a ha t U) i (a + 1) =
      ((alpha a ha t + η.value * (t (collapseAfter a i)).value) / 2) *
        PhiEta η (D0 a t D) (H0 H) U (collapseAfter a i) a
 := by
  unfold PhiEta phi
  rw [ShortEdgeFiberSums.sum_parent_rightEndpoint a i hiA]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  exact ShortEdgeRightEndpoint.rightEndpointContribution_twoLifts
    a i ha hiA t U η D H S (Finset.mem_powerset.mp hS)

theorem rightEndpoint_ordinary_source
    (a i : ℕ) (ha : 0 < a) (hiA : i < a)
    (t : ℕ → Sign) (D : TripleArray) (H : ℕ → ℕ → ℕ → Sign) :
    phi (D1 a t D) (H1 a t H)
      (parentTable a ha t (ordinaryCurrent (D0 a t D) (H0 H))) i (a + 1) =
        source i (a + 1)
 := by
  have hci : collapseAfter a i = i :=
    ShortEdgeCutFibers.collapseAfter_eq_of_le a i (by omega)
  have hp :
      phi (D1 a t D) (H1 a t H)
          (parentTable a ha t (ordinaryCurrent (D0 a t D) (H0 H))) i (a + 1) =
        ((alpha a ha t - (t i).value) / 2) *
          phi (D0 a t D) (H0 H) (ordinaryCurrent (D0 a t D) (H0 H)) i a := by
    simpa [PhiEta, Sign.value, sub_eq_add_neg, hci] using
      rightEndpointPhi a i ha hiA t (ordinaryCurrent (D0 a t D) (H0 H)) .neg D H
  rw [hp, ordinaryCurrent_phi (D0 a t D) (H0 H) hiA]
  have hparent : source i (a + 1) = 0 := by
    simp [source, show a ≠ i by omega]
  rw [hparent]
  by_cases h : a = i + 1
  · simp [source, h, alpha]
  · simp [source, h]

end DirectGLSSW.ShortEdgeWeighted.RightEndpointPhiImpl
