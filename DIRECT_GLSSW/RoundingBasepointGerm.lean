import SmallRoundingFraction

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- The retained part is literally the original affine arc, with its explicit
cell parameter shift. -/
theorem normalizedRoundedCell_retained_arc (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (s : ℝ) (hs : δ.val < s) :
    Complex.equivRealProd
      (normalizedRoundedCell D (D.continuation.symm e) δ (s + δ.val)) =
      affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) s := by
  have hp : 0 < 2 * δ.val := by linarith [δ.property.1]
  have hn : ¬ (s + δ.val) / (2 * δ.val) ≤ 1 := by
    apply not_le.mpr
    apply (lt_div_iff₀ hp).mpr
    linarith
  have hi := congrArg D.vertexPoint (D.continuation_incidence (D.continuation.symm e))
  simp only [Equiv.apply_symm_apply] at hi
  simp only [normalizedRoundedCell, roundedStep, hn, if_false, roundingStraight,
    Equiv.apply_symm_apply, cornerCenter, arcVector, Complex.real_smul,
    Complex.equivRealProd_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero, zero_add]
  rw [hi]
  apply Prod.ext <;> simp only [affinePoint, Prod.fst, Prod.snd] <;>
    field_simp [ne_of_gt hp] <;> ring

/-- A positive affine parameter neighborhood of the basepoint survives as the
same actual straight germ inside the normalized rounded cell. -/
theorem normalizedRoundedCell_basepoint_germ (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (τ : ℝ) (hleft : δ.val < τ) (hright : δ.val < 1 - τ) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, |s| < η →
      (τ + s + δ.val) ∈ Set.Ioo (2 * δ.val) 1 ∧
      Complex.equivRealProd (normalizedRoundedCell D (D.continuation.symm e) δ
        (τ + s + δ.val)) = affinePoint (D.vertexPoint (D.arcSource e))
          (D.vertexPoint (D.arcTarget e)) (τ + s) := by
  let η : ℝ := min ((τ - δ.val) / 2) ((1 - δ.val - τ) / 2)
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have hl : η ≤ (τ - δ.val) / 2 := min_le_left _ _
  have hr : η ≤ (1 - δ.val - τ) / 2 := min_le_right _ _
  refine ⟨η,hη,?_⟩
  intro s hs
  obtain ⟨hsl,hsr⟩ := abs_lt.mp hs
  have hδs : δ.val < τ + s := by linarith
  refine ⟨⟨by linarith,by linarith⟩,?_⟩
  exact normalizedRoundedCell_retained_arc D e δ (τ + s) hδs

end DirectGLSSW.HOMFLY.PrincipalTurning


