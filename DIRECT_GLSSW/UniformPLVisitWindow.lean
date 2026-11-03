import UniformPLVisits
import CrossingStarStrictWindow

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits

theorem visitPosition_lt_actual_period {D : PLLinkDiagram} (T : BasedTraversal D)
    (e : Fin D.nArc) :
    visitPosition T e < componentArcLength D (T.baseArc (componentOf D.continuation e)).val := by
  classical
  unfold visitPosition componentArcLength
  exact Fin.isLt _

theorem crossingVisitTime_window_inside_period {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) (x : ℝ)
    (hx : x ∈ Set.Icc (-crossingStarStrictRadius D c) (2*crossingStarStrictRadius D c)) :
    0 < crossingVisitTime T c i + crossingStarCoordinateInverse D c i x ∧
      crossingVisitTime T c i + crossingStarCoordinateInverse D c i x <
        (componentArcLength D (T.baseArc (componentOf D.continuation (D.incoming c i))).val : ℝ) := by
  have hu := crossingStarStrict_inverse_window D c i x hx
  have hk := visitPosition_lt_actual_period T (D.incoming c i)
  have hk' : (visitPosition T (D.incoming c i) : ℝ) + 1 ≤
      (componentArcLength D (T.baseArc (componentOf D.continuation (D.incoming c i))).val : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hk)
  have hk0 : (0 : ℝ) ≤ (visitPosition T (D.incoming c i) : ℝ) := Nat.cast_nonneg _
  unfold crossingVisitTime
  constructor <;> linarith [hu.1,hu.2]

theorem basedUniformPLCurve_crossing_pullback {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) (x : ℝ)
    (hx : x ∈ Set.Icc (-crossingStarStrictRadius D c) (2*crossingStarStrictRadius D c)) :
    basedUniformPLCurve T (componentOf D.continuation (D.incoming c i))
      (crossingVisitTime T c i + crossingStarCoordinateInverse D c i x) =
      crossingStarPoint D c i (crossingStarCoordinateInverse D c i x) :=
  basedUniformPLCurve_crossing_star T c i _ (Set.Ioo_subset_Icc_self
    (crossingStarStrict_inverse_window D c i x hx))

theorem firstVisitedBranch_time_first {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c (firstVisitedBranch T c)) =
      componentOf D.continuation (D.incoming c (otherBranch (firstVisitedBranch T c)))) :
    crossingVisitTime T c (firstVisitedBranch T c) <
      crossingVisitTime T c (otherBranch (firstVisitedBranch T c)) :=
  (crossingVisitTime_order T c _ _ hC).mp (firstVisitedBranch_is_first T c)

end DirectGLSSW.HOMFLY.PrincipalTurning




