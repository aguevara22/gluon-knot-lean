import UniformPLComponent
import CrossingStarCoordinates

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open Equiv PermutationOrbits

noncomputable def crossingVisitTime {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) : ℝ := (visitPosition T (D.incoming c i) : ℝ) + 1/2

theorem crossingVisitTime_positive {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) : 0 < crossingVisitTime T c i := by
  unfold crossingVisitTime
  positivity

theorem basedUniformPLCurve_crossing_star {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) (u : ℝ) (hu : u ∈ Set.Icc (-1/2 : ℝ) (1/2)) :
    basedUniformPLCurve T (componentOf D.continuation (D.incoming c i))
      (crossingVisitTime T c i + u) = crossingStarPoint D c i u := by
  let k := visitPosition T (D.incoming c i)
  let e := (T.baseArc (componentOf D.continuation (D.incoming c i))).val
  have hk : (D.continuation ^ (k : ℤ)) e = D.incoming c i := by
    simpa only [zpow_natCast] using visitPosition_reconstruct T (D.incoming c i)
  have hk1 : (D.continuation ^ ((k : ℤ)+1)) e = D.outgoing c (D.through c i) := by
    rw [add_comm (k : ℤ) 1,zpow_add,Perm.mul_apply,zpow_one,hk,D.continuation_crossing]
  change uniformPLCurve D e (((k : ℝ)+1/2+u)+1/2) = crossingStarPoint D c i u
  by_cases h : u ≤ 0
  · have ht : (((k : ℝ)+1/2+u)+1/2) = (k : ℝ)+(1+u) := by ring
    have hc := uniformPLCurve_arc_cell D e (k : ℤ) (1+u) (by constructor <;> linarith [hu.1])
    simp only [Int.cast_natCast] at hc
    rw [ht, hc, hk]
    simp only [crossingStarPoint, if_pos h,D.incoming_target]
  · have ht : (((k : ℝ)+1/2+u)+1/2) = (((k : ℤ)+1 : ℤ) : ℝ)+u := by push_cast; ring
    rw [ht,uniformPLCurve_arc_cell D e ((k : ℤ)+1) u (by constructor <;> linarith [hu.2]),hk1]
    simp only [crossingStarPoint,if_neg h,D.outgoing_source]

theorem crossingVisitTime_order {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i j : Fin 2)
    (hC : componentOf D.continuation (D.incoming c i) = componentOf D.continuation (D.incoming c j)) :
    rankBefore (visitRank T (D.incoming c i)) (visitRank T (D.incoming c j)) ↔
      crossingVisitTime T c i < crossingVisitTime T c j := by
  simp only [rankBefore,visitRank,hC,lt_self_iff_false,true_and,false_or]
  unfold crossingVisitTime
  rw [add_lt_add_iff_right]
  exact Nat.cast_lt.symm

end DirectGLSSW.HOMFLY.PrincipalTurning



