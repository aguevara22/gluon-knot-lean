import CrossingStarBoundaryAtRadius
import UniformPLSecants
import UniformPLVisitWindow

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

noncomputable def starEightTurn (Z : ℝ → ℝ → ℂ) (ε : ℝ) : ℝ :=
  Complex.arg (Z 0 (-ε) / Z (-ε) (-ε)) +
  Complex.arg (Z (2*ε) (-ε) / Z 0 (-ε)) +
  Complex.arg (Z (2*ε) 0 / Z (2*ε) (-ε)) +
  Complex.arg (Z (2*ε) (2*ε) / Z (2*ε) 0) +
  Complex.arg (Z 0 (2*ε) / Z (2*ε) (2*ε)) +
  Complex.arg (Z (-ε) (2*ε) / Z 0 (2*ε)) +
  Complex.arg (Z (-ε) 0 / Z (-ε) (2*ε)) +
  Complex.arg (Z (-ε) (-ε) / Z (-ε) 0)

theorem crossingStarLinear_det_pair (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (x y u v : ℝ) :
    complexDet (crossingStarLinear D c x y) (crossingStarLinear D c u v) =
      (y*u-x*v)*complexDet (crossingVector D c 0) (crossingVector D c 1) := by
  simp [crossingStarLinear,complexDet]
  ring

theorem actualStar_boundary_reflection (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (hε : 0 < ε) :
    starEightTurn (fun x y => -crossingStarPullback D c y x) ε =
      -starEightTurn (crossingStarPullback D c) ε := by
  have hd := crossingStar_actual_det_ne_zero D c
  have hε2 := sq_pos_of_pos hε
  have rev (x y u v : ℝ) (h : y*u-x*v ≠ 0) :
      Complex.arg (crossingStarLinear D c x y / crossingStarLinear D c u v) =
        -Complex.arg (crossingStarLinear D c u v / crossingStarLinear D c x y) := by
    have hn : complexDet (crossingStarLinear D c x y) (crossingStarLinear D c u v) ≠ 0 := by
      rw [crossingStarLinear_det_pair]
      exact mul_ne_zero h hd
    have hr := reciprocal_turns_cancel_of_det (crossingStarLinear D c x y)
      (crossingStarLinear D c u v) hn
    linarith
  have rAE := rev (-ε) (-ε) 0 (-ε) (by nlinarith)
  have rEB := rev 0 (-ε) (2*ε) (-ε) (by nlinarith)
  have rBF := rev (2*ε) (-ε) (2*ε) 0 (by nlinarith)
  have rFC := rev (2*ε) 0 (2*ε) (2*ε) (by nlinarith)
  have rCG := rev (2*ε) (2*ε) 0 (2*ε) (by nlinarith)
  have rGV := rev 0 (2*ε) (-ε) (2*ε) (by nlinarith)
  have rVH := rev (-ε) (2*ε) (-ε) 0 (by nlinarith)
  have rHA := rev (-ε) 0 (-ε) (-ε) (by nlinarith)
  simp only [starEightTurn,neg_div_neg_eq,crossingStarPullback_eq_linear]
  linarith

theorem actualStar_boundary_balance10 (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (hε : 0 < ε) :
    starEightTurn (fun x y => -crossingStarPullback D c y x) ε =
      if 0 < complexDet (crossingVector D c 1) (crossingVector D c 0)
      then -(2*Real.pi) else 2*Real.pi := by
  rw [actualStar_boundary_reflection D c ε hε]
  have h01 := actualStar_boundary_breakpoint_balance_at_radius D c ε hε
  change starEightTurn (crossingStarPullback D c) ε = _ at h01
  rw [h01]
  have hswap : complexDet (crossingVector D c 1) (crossingVector D c 0) =
      -complexDet (crossingVector D c 0) (crossingVector D c 1) := by unfold complexDet; ring
  rw [hswap]
  have hd := crossingStar_actual_det_ne_zero D c
  by_cases hpos : 0 < complexDet (crossingVector D c 0) (crossingVector D c 1)
  · simp [hpos, show ¬0 < -complexDet (crossingVector D c 0) (crossingVector D c 1) by linarith]
  · have hneg : complexDet (crossingVector D c 0) (crossingVector D c 1) < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hd
    simp [hpos,show 0 < -complexDet (crossingVector D c 0) (crossingVector D c 1) by linarith]

theorem crossingStarCoordinateInverse_strictMono (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) : StrictMono (crossingStarCoordinateInverse D c i) := by
  intro x y hxy
  exact (crossingStarCoordinate_strictMono D c i).lt_iff_lt.mp (by
    simpa only [crossingStarCoordinate_inverse] using hxy)

theorem crossingVisitAxis_strictMono {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) :
    StrictMono (fun x => crossingVisitTime T c i + crossingStarCoordinateInverse D c i x) := by
  intro x y hxy
  exact add_lt_add_left (crossingStarCoordinateInverse_strictMono D c i hxy) _

end DirectGLSSW.HOMFLY.PrincipalTurning





