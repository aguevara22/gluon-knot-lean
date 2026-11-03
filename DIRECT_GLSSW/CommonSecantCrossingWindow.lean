import FiniteSecantAxis

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits

theorem secantMeshEpsilon_le_half_radius (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    secantMeshEpsilon D ≤ crossingStarStrictRadius D c / 2 := by
  have hle : (secantMeshRadiusSet D).min' (secantMeshRadiusSet_nonempty D) ≤
      crossingStarStrictRadius D c := Finset.min'_le _ _ (by simp [secantMeshRadiusSet])
  unfold secantMeshEpsilon
  linarith

theorem crossingStarCoordinateInverse_half (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) (x : ℝ) :
    crossingStarCoordinateInverse D c i (x/2) = crossingStarCoordinateInverse D c i x / 2 := by
  by_cases hx : x ≤ 0
  · have hx' : x/2 ≤ 0 := by linarith
    simp [crossingStarCoordinateInverse,hx,hx']
  · have hx' : ¬ x/2 ≤ 0 := by linarith
    simp only [crossingStarCoordinateInverse,if_neg hx,if_neg hx']
    ring

theorem secantMesh_inverse_window (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) (x : ℝ)
    (hx : x ∈ Set.Icc (-secantMeshEpsilon D) (2*secantMeshEpsilon D)) :
    crossingStarCoordinateInverse D c i x ∈ Set.Ioo (-1/4 : ℝ) (1/4) := by
  have hε := secantMeshEpsilon_le_half_radius D c
  have he := crossingStarStrict_inverse_endpoints D c i
  have hm := crossingStarCoordinate_strictMono D c i
  have hlo : crossingStarCoordinateInverse D c i ((-crossingStarStrictRadius D c)/2) ≤
      crossingStarCoordinateInverse D c i x := hm.le_iff_le.mp (by
        simp only [crossingStarCoordinate_inverse]
        linarith [hx.1])
  have hhi : crossingStarCoordinateInverse D c i x ≤
      crossingStarCoordinateInverse D c i ((2*crossingStarStrictRadius D c)/2) := hm.le_iff_le.mp (by
        simp only [crossingStarCoordinate_inverse]
        linarith [hx.2])
  rw [crossingStarCoordinateInverse_half] at hlo hhi
  constructor <;> linarith [he.1,he.2.2.2]

theorem secantMesh_visit_window_inside_margin {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) (x : ℝ)
    (hx : x ∈ Set.Icc (-secantMeshEpsilon D) (2*secantMeshEpsilon D)) :
    crossingVisitTime T c i + crossingStarCoordinateInverse D c i x ∈
      Set.Ioo (1/4 : ℝ)
        ((componentArcLength D (T.baseArc (componentOf D.continuation (D.incoming c i))).val : ℝ)-1/4) := by
  have hu := secantMesh_inverse_window D c i x hx
  have hk := visitPosition_lt_actual_period T (D.incoming c i)
  have hkr : (visitPosition T (D.incoming c i) : ℝ)+1 ≤
      (componentArcLength D (T.baseArc (componentOf D.continuation (D.incoming c i))).val : ℝ) := by
    exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (visitPosition T (D.incoming c i) : ℝ) := by positivity
  unfold crossingVisitTime
  constructor <;> linarith [hu.1,hu.2]

theorem firstVisitedBranch_common_rectangle_gap {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c (firstVisitedBranch T c)) =
      componentOf D.continuation (D.incoming c (otherBranch (firstVisitedBranch T c))))
    (x y : ℝ)
    (hx : x ∈ Set.Icc (-secantMeshEpsilon D) (2*secantMeshEpsilon D))
    (hy : y ∈ Set.Icc (-secantMeshEpsilon D) (2*secantMeshEpsilon D)) :
    1/2 < (crossingVisitTime T c (otherBranch (firstVisitedBranch T c)) +
      crossingStarCoordinateInverse D c (otherBranch (firstVisitedBranch T c)) y) -
      (crossingVisitTime T c (firstVisitedBranch T c) +
      crossingStarCoordinateInverse D c (firstVisitedBranch T c) x) := by
  have hu := secantMesh_inverse_window D c (firstVisitedBranch T c) x hx
  have hv := secantMesh_inverse_window D c (otherBranch (firstVisitedBranch T c)) y hy
  have hg := firstVisitedBranch_time_gap T c hC
  linarith [hu.2,hv.1]

theorem basedOrderedCrossing_common_boundary01 {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c 0) = componentOf D.continuation (D.incoming c 1)) :
    starEightTurn (basedOrderedCrossingPullback T c 0 1) (secantMeshEpsilon D) =
      if 0 < complexDet (crossingVector D c 0) (crossingVector D c 1)
      then -(2*Real.pi) else 2*Real.pi := by
  have hr := secantMeshEpsilon_lt_radius D c
  rw [starEightTurn_congr_rectangle _ (crossingStarPullback D c) _
    (secantMeshEpsilon_positive D) (by
      intro x y hx hy
      apply basedOrderedCrossingPullback01 T c hC x y <;>
        constructor <;> linarith [hx.1,hx.2,hy.1,hy.2])]
  exact actualStar_boundary_breakpoint_balance_at_radius D c _ (secantMeshEpsilon_positive D)

theorem basedOrderedCrossing_common_boundary10 {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c 0) = componentOf D.continuation (D.incoming c 1)) :
    starEightTurn (basedOrderedCrossingPullback T c 1 0) (secantMeshEpsilon D) =
      if 0 < complexDet (crossingVector D c 1) (crossingVector D c 0)
      then -(2*Real.pi) else 2*Real.pi := by
  have hr := secantMeshEpsilon_lt_radius D c
  rw [starEightTurn_congr_rectangle _ (fun x y => -crossingStarPullback D c y x) _
    (secantMeshEpsilon_positive D) (by
      intro x y hx hy
      apply basedOrderedCrossingPullback10 T c hC x y <;>
        constructor <;> linarith [hx.1,hx.2,hy.1,hy.2])]
  exact actualStar_boundary_balance10 D c _ (secantMeshEpsilon_positive D)

theorem firstVisitedBranch_common_boundary_balance {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c (firstVisitedBranch T c)) =
      componentOf D.continuation (D.incoming c (otherBranch (firstVisitedBranch T c)))) :
    starEightTurn (basedOrderedCrossingPullback T c (firstVisitedBranch T c)
      (otherBranch (firstVisitedBranch T c))) (secantMeshEpsilon D) =
      if 0 < complexDet (crossingVector D c (firstVisitedBranch T c))
        (crossingVector D c (otherBranch (firstVisitedBranch T c)))
      then -(2*Real.pi) else 2*Real.pi := by
  by_cases h : firstVisitedBranch T c=0
  · rw [h,otherBranch_zero] at hC ⊢
    exact basedOrderedCrossing_common_boundary01 T c hC
  · have h1 : firstVisitedBranch T c=1 := by omega
    rw [h1,otherBranch_one] at hC ⊢
    exact basedOrderedCrossing_common_boundary10 T c hC.symm

end DirectGLSSW.HOMFLY.PrincipalTurning








