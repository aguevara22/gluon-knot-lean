import SmallRoundingFraction

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Exact secant factorization of the actual quadratic corner by its midpoint
velocity; this supplies local simplicity without an embedding premise. -/
theorem roundedCorner_secant (D : PLLinkDiagram) (e : Fin D.nArc) (δ s t : ℝ) :
    roundedCorner D e δ t - roundedCorner D e δ s =
      (t - s) • roundedCornerDerivative D e δ ((s + t) / 2) := by
  simp only [roundedCorner, roundedCornerDerivative, cornerTangent, Complex.real_smul]
  push_cast
  ring

theorem roundedCorner_injOn (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : ℝ) (hδ : 0 < δ) :
    Set.InjOn (roundedCorner D e δ) (Set.Icc 0 1) := by
  intro s hs t ht heq
  have hmid : (s + t) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hs.1,ht.1],by linarith [hs.2,ht.2]⟩
  have hz : (t - s) • roundedCornerDerivative D e δ ((s + t) / 2) = 0 := by
    rw [← roundedCorner_secant, heq, sub_self]
  rcases smul_eq_zero.mp hz with h | h
  · linarith
  · exact False.elim (roundedCorner_regular D e δ _ hδ hmid h)

end DirectGLSSW.HOMFLY.PrincipalTurning


