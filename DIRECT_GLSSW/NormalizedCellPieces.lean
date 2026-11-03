import NormalizedCrossingOrientation
import NormalizedRetainedCell

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Aggregate Gate5: actual normalized corner phase, with exact unit clock. -/
theorem normalizedRoundedCell_corner_piece (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (s : ℝ) (hs : s ∈ Set.Icc 0 (2 * δ.val)) :
    ∃ q : ℝ, q ∈ Set.Icc 0 1 ∧ 2 * δ.val * q = s ∧
      normalizedRoundedCell D e δ s = roundedCorner D e δ.val q := by
  have hp : 0 < 2 * δ.val := by linarith [δ.property.1]
  have hq : s / (2 * δ.val) ∈ Set.Icc 0 1 := by
    refine ⟨div_nonneg hs.1 hp.le,?_⟩
    apply (div_le_iff₀ hp).mpr
    nlinarith [hs.2]
  have htime : 2 * δ.val * (s / (2 * δ.val)) = s := by field_simp [ne_of_gt hp]
  refine ⟨s / (2 * δ.val),hq,htime,?_⟩
  simp only [normalizedRoundedCell,roundedStep,hq.2,if_true]

/-- Aggregate Gate5: the open straight part has strict unit parameters,
so no corner contact can hide at a cut endpoint or the integer seam. -/
theorem normalizedRoundedCell_straight_piece (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (s : ℝ) (hs : s ∈ Set.Ioo (2 * δ.val) 1) :
    ∃ u : ℝ, u ∈ Set.Ioo 0 1 ∧ 2 * δ.val + (1 - 2 * δ.val) * u = s ∧
      Complex.equivRealProd (normalizedRoundedCell D e δ s) =
        retainedArcPoint D (D.continuation e) δ u := by
  have hc : 0 < 1 - 2 * δ.val := by linarith [δ.property.2]
  let u : ℝ := (s - 2 * δ.val) / (1 - 2 * δ.val)
  have hu : u ∈ Set.Ioo 0 1 := by
    refine ⟨div_pos (by linarith [hs.1]) hc,?_⟩
    apply (div_lt_iff₀ hc).mpr
    linarith [hs.2]
  have htime : 2 * δ.val + (1 - 2 * δ.val) * u = s := by
    dsimp only [u]
    field_simp [ne_of_gt hc] <;> ring
  refine ⟨u,hu,htime,?_⟩
  have h := normalizedRoundedCell_retained_unit D e δ u ⟨hu.1.le,hu.2.le⟩
  rw [htime] at h
  exact h

end DirectGLSSW.HOMFLY.PrincipalTurning


