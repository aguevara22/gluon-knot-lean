import OrderedActualStarBoundary

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits

theorem firstVisitedBranch_time_gap {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c (firstVisitedBranch T c)) =
      componentOf D.continuation (D.incoming c (otherBranch (firstVisitedBranch T c)))) :
    crossingVisitTime T c (firstVisitedBranch T c)+1 ≤
      crossingVisitTime T c (otherBranch (firstVisitedBranch T c)) := by
  have hp := firstVisitedBranch_is_first T c
  simp only [rankBefore,visitRank,hC,lt_self_iff_false,true_and,false_or] at hp
  have hn : visitPosition T (D.incoming c (firstVisitedBranch T c))+1 ≤
      visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c))) := hp
  have hr : (visitPosition T (D.incoming c (firstVisitedBranch T c)) : ℝ)+1 ≤
      (visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c))) : ℝ) := by exact_mod_cast hn
  unfold crossingVisitTime
  linarith

/-- The actual first/second crossing rectangle lies strictly inside the
ordered period triangle, including the first and last possible visit ranks. -/
theorem firstVisitedBranch_rectangle_inside_ordered_period {D : PLLinkDiagram}
    (T : BasedTraversal D) (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c (firstVisitedBranch T c)) =
      componentOf D.continuation (D.incoming c (otherBranch (firstVisitedBranch T c))))
    (x y : ℝ)
    (hx : x ∈ Set.Icc (-crossingStarStrictRadius D c) (2*crossingStarStrictRadius D c))
    (hy : y ∈ Set.Icc (-crossingStarStrictRadius D c) (2*crossingStarStrictRadius D c)) :
    0 < crossingVisitTime T c (firstVisitedBranch T c) +
        crossingStarCoordinateInverse D c (firstVisitedBranch T c) x ∧
    crossingVisitTime T c (firstVisitedBranch T c) +
        crossingStarCoordinateInverse D c (firstVisitedBranch T c) x <
      crossingVisitTime T c (otherBranch (firstVisitedBranch T c)) +
        crossingStarCoordinateInverse D c (otherBranch (firstVisitedBranch T c)) y ∧
    crossingVisitTime T c (otherBranch (firstVisitedBranch T c)) +
        crossingStarCoordinateInverse D c (otherBranch (firstVisitedBranch T c)) y <
      (componentArcLength D (T.baseArc (componentOf D.continuation
        (D.incoming c (firstVisitedBranch T c)))).val : ℝ) := by
  have hi := crossingVisitTime_window_inside_period T c (firstVisitedBranch T c) x hx
  have hj := crossingVisitTime_window_inside_period T c (otherBranch (firstVisitedBranch T c)) y hy
  rw [← hC] at hj
  have hu := crossingStarStrict_inverse_window D c (firstVisitedBranch T c) x hx
  have hv := crossingStarStrict_inverse_window D c (otherBranch (firstVisitedBranch T c)) y hy
  have hg := firstVisitedBranch_time_gap T c hC
  exact ⟨hi.1,by linarith [hu.2,hv.1],hj.2⟩

theorem firstVisitedBranch_actual_boundary_balance {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c (firstVisitedBranch T c)) =
      componentOf D.continuation (D.incoming c (otherBranch (firstVisitedBranch T c)))) :
    starEightTurn (basedOrderedCrossingPullback T c (firstVisitedBranch T c)
      (otherBranch (firstVisitedBranch T c))) (crossingStarStrictRadius D c) =
      if 0 < complexDet (crossingVector D c (firstVisitedBranch T c))
        (crossingVector D c (otherBranch (firstVisitedBranch T c)))
      then -(2*Real.pi) else 2*Real.pi := by
  by_cases h : firstVisitedBranch T c=0
  · rw [h,otherBranch_zero] at hC ⊢
    exact basedOrderedCrossing_boundary01 T c hC
  · have h1 : firstVisitedBranch T c=1 := by omega
    rw [h1,otherBranch_one] at hC ⊢
    exact basedOrderedCrossing_boundary10 T c hC.symm

end DirectGLSSW.HOMFLY.PrincipalTurning



