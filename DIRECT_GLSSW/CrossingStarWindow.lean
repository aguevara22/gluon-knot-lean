import CrossingStarBox

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

noncomputable def crossingStarRadius (D : PLLinkDiagram) (c : Fin D.nCrossing) : ℝ :=
  crossingCutoffRadius D c / 4

theorem crossingStarRadius_pos (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    0 < crossingStarRadius D c := div_pos (crossingCutoffRadius_pos D c) (by norm_num)

theorem crossingStar_inverse_endpoints (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) :
    -1 < crossingStarCoordinateInverse D c i (-crossingStarRadius D c) ∧
      crossingStarCoordinateInverse D c i (-crossingStarRadius D c) < 0 ∧
    0 < crossingStarCoordinateInverse D c i (2*crossingStarRadius D c) ∧
      crossingStarCoordinateInverse D c i (2*crossingStarRadius D c) < 1 := by
  have hρ := crossingCutoffRadius_pos D c
  have hε := crossingStarRadius_pos D c
  have htwo : 2*crossingStarRadius D c < crossingCutoffRadius D c := by
    dsimp [crossingStarRadius]; linarith
  have hp := crossingCutoff_parameters D c (mul_pos (by norm_num) hε) htwo i
  have hle : crossingCutoffRadius D c ≤ 1 := min_le_left _ _
  have hε1 : crossingStarRadius D c < 1 := by dsimp [crossingStarRadius]; linarith
  simp only [crossingStarCoordinateInverse, if_pos (by linarith : -crossingStarRadius D c ≤ 0),
    if_neg (by linarith : ¬ 2*crossingStarRadius D c ≤ 0)]
  exact ⟨by linarith, by linarith, by nlinarith [hp.2.2.2.1], by nlinarith [hp.2.2.2.2.1]⟩

theorem crossingStar_inverse_window (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) (x : ℝ) (hx : x ∈ Set.Icc (-crossingStarRadius D c) (2*crossingStarRadius D c)) :
    crossingStarCoordinateInverse D c i x ∈ Set.Ioo (-1) 1 := by
  have hm := crossingStarCoordinate_strictMono D c i
  have hlo : crossingStarCoordinateInverse D c i (-crossingStarRadius D c) ≤
      crossingStarCoordinateInverse D c i x := hm.le_iff_le.mp (by
        simpa only [crossingStarCoordinate_inverse] using hx.1)
  have hhi : crossingStarCoordinateInverse D c i x ≤
      crossingStarCoordinateInverse D c i (2*crossingStarRadius D c) := hm.le_iff_le.mp (by
        simpa only [crossingStarCoordinate_inverse] using hx.2)
  have he := crossingStar_inverse_endpoints D c i
  exact ⟨lt_of_lt_of_le he.1 hlo, lt_of_le_of_lt hhi he.2.2.2⟩

/-- The literal actual two-arc secant, pulled back through the derived inverse
speeds; no replacement curve or genericity certificate is used. -/
noncomputable def crossingStarPullback (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (x y : ℝ) : ℂ := crossingStarSecant D c
      (crossingStarCoordinateInverse D c 0 x) (crossingStarCoordinateInverse D c 1 y)

theorem crossingStarPullback_eq_linear (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (x y : ℝ) : crossingStarPullback D c x y = crossingStarLinear D c x y := by
  rw [crossingStarPullback, crossingStarSecant_coordinates,
    crossingStarCoordinate_inverse, crossingStarCoordinate_inverse]
  rfl

theorem crossingStarPullback_eq_zero_iff (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (x y : ℝ) : crossingStarPullback D c x y = 0 ↔ x = 0 ∧ y = 0 := by
  rw [crossingStarPullback_eq_linear, crossingStarLinear_eq_zero_iff]

end DirectGLSSW.HOMFLY.PrincipalTurning





