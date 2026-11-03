import CrossingStarWindow

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Half the old radius: literally crossingCutoffRadius / 8. -/
noncomputable def crossingStarStrictRadius (D : PLLinkDiagram) (c : Fin D.nCrossing) : ℝ :=
  crossingStarRadius D c / 2

theorem crossingStarStrictRadius_pos (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    0 < crossingStarStrictRadius D c := div_pos (crossingStarRadius_pos D c) (by norm_num)

theorem crossingStarStrict_inverse_endpoints (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) :
    -1/2 < crossingStarCoordinateInverse D c i (-crossingStarStrictRadius D c) ∧
      crossingStarCoordinateInverse D c i (-crossingStarStrictRadius D c) < 0 ∧
    0 < crossingStarCoordinateInverse D c i (2*crossingStarStrictRadius D c) ∧
      crossingStarCoordinateInverse D c i (2*crossingStarStrictRadius D c) < 1/2 := by
  have he := crossingStar_inverse_endpoints D c i
  have hε := crossingStarRadius_pos D c
  have hs := crossingStarStrictRadius_pos D c
  simp only [crossingStarCoordinateInverse, if_pos (by linarith : -crossingStarRadius D c ≤ 0),
    if_neg (by linarith : ¬ 2*crossingStarRadius D c ≤ 0)] at he
  simp only [crossingStarCoordinateInverse, if_pos (by linarith : -crossingStarStrictRadius D c ≤ 0),
    if_neg (by linarith : ¬ 2*crossingStarStrictRadius D c ≤ 0)]
  dsimp [crossingStarStrictRadius]
  constructor
  · linarith [he.1]
  constructor
  · linarith
  constructor
  · nlinarith [he.2.2.1]
  · nlinarith [he.2.2.2]

theorem crossingStarStrict_inverse_window (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) (x : ℝ)
    (hx : x ∈ Set.Icc (-crossingStarStrictRadius D c) (2*crossingStarStrictRadius D c)) :
    crossingStarCoordinateInverse D c i x ∈ Set.Ioo (-1/2 : ℝ) (1/2) := by
  have hm := crossingStarCoordinate_strictMono D c i
  have hlo : crossingStarCoordinateInverse D c i (-crossingStarStrictRadius D c) ≤
      crossingStarCoordinateInverse D c i x := hm.le_iff_le.mp (by
        simpa only [crossingStarCoordinate_inverse] using hx.1)
  have hhi : crossingStarCoordinateInverse D c i x ≤
      crossingStarCoordinateInverse D c i (2*crossingStarStrictRadius D c) := hm.le_iff_le.mp (by
        simpa only [crossingStarCoordinate_inverse] using hx.2)
  have he := crossingStarStrict_inverse_endpoints D c i
  exact ⟨lt_of_lt_of_le he.1 hlo,lt_of_le_of_lt hhi he.2.2.2⟩

end DirectGLSSW.HOMFLY.PrincipalTurning



