import RoundingCutoffLocalization

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- A concrete finite uniform cutoff keeps every actual corner in its vertex
ball, while retaining any prescribed interior basepoint parameter. -/
theorem exists_small_rounding_fraction (D : PLLinkDiagram) (r τ : ℝ)
    (hr : 0 < r) (hτ : τ ∈ Set.Ioo 0 1) :
    ∃ δ : RoundingFraction, δ.val < τ ∧ δ.val < 1 - τ ∧
      ∀ e : Fin D.nArc, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        dist (Complex.equivRealProd (roundedCorner D e δ.val t))
          (D.vertexPoint (D.arcTarget e)) < r := by
  let M : Fin D.nArc → ℝ := fun e =>
    ‖arcVector D e‖ + ‖arcVector D (D.continuation e)‖
  have hM : ∀ e, 0 ≤ M e := fun e => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hpos : ∀ e, 0 < r / (M e + 1) := fun e =>
    div_pos hr (by linarith [hM e])
  obtain ⟨B,hB,hbounds⟩ := TruncationCommonRadius.exists_positive_common_lower_bound
    (fun e => r / (M e + 1)) hpos
  let d : ℝ := min (1 / 4) (min (τ / 2) (min ((1 - τ) / 2) (B / 2)))
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (by norm_num) (lt_min (by linarith [hτ.1])
      (lt_min (by linarith [hτ.2]) (by linarith)))
  have hd1 : d ≤ 1 / 4 := min_le_left _ _
  have hdτ : d ≤ τ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hdτ' : d ≤ (1 - τ) / 2 := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdB : d ≤ B / 2 := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨⟨d,hd,by linarith⟩,by linarith [hτ.1],by linarith [hτ.2],?_⟩
  intro e t ht
  have hdb : d < r / (M e + 1) := lt_of_lt_of_le (by linarith) (hbounds e)
  have hprod : d * (M e + 1) < r :=
    (lt_div_iff₀ (by linarith [hM e])).mp hdb
  have hsmall : d * M e < r := by nlinarith
  exact lt_of_le_of_lt (le_trans (roundedCorner_planar_dist_le D e d t)
    (roundedCorner_displacement_bound D e d t hd.le ht)) hsmall

/-- The actual basepoint is nonvertex, so the preceding radius theorem applies
without an additional diagram hypothesis. -/
theorem interior_basepoint_nonvertex (D : PLLinkDiagram) (e : Fin D.nArc)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 1) :
    ∀ v, D.vertexPoint v ≠ affinePoint (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e)) τ := by
  intro v
  exact D.vertices_avoid_arc_interiors v e τ hτ.1 hτ.2

end DirectGLSSW.HOMFLY.PrincipalTurning


