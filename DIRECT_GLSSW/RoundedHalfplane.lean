import PositionalArgumentHalfplane
import ProcessedRootExposure

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Three nonnegative barycentric weights preserve a literal affine half-plane. -/
theorem complex_halfplane_combination (a x y z : ℂ) (b r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s ≤ 1)
    (hx : b ≤ (a*x).re) (hy : b ≤ (a*y).re) (hz : b ≤ (a*z).re) :
    b ≤ (a * (r • x + (1-r-s) • y + s • z)).re := by
  have h := add_nonneg
    (add_nonneg (mul_nonneg hr (sub_nonneg.mpr hx))
      (mul_nonneg (show 0 ≤ 1-r-s by linarith) (sub_nonneg.mpr hy)))
    (mul_nonneg hs (sub_nonneg.mpr hz))
  have heq : (a * (r • x + (1-r-s) • y + s • z)).re - b =
      r*((a*x).re-b) + (1-r-s)*((a*y).re-b) + s*((a*z).re-b) := by
    simp [Complex.real_smul, Complex.mul_re, Complex.mul_im]
    <;> ring
  exact sub_nonneg.mp (heq.symm ▸ h)

/-- Every literal rounded corner stays in the half-plane of its three actual
vertices. The sole size input is the existing RoundingFraction bound. -/
theorem roundedCorner_halfplane (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (a : ℂ) (b t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (hv : ∀ v, b ≤ (a * (⟨(D.vertexPoint v).1, (D.vertexPoint v).2⟩ : ℂ)).re) :
    b ≤ (a * roundedCorner D e δ.val t).re := by
  have h0 : b ≤ (a * (cornerCenter D e - arcVector D e)).re := by
    have heq : cornerCenter D e - arcVector D e =
        (⟨(D.vertexPoint (D.arcSource e)).1, (D.vertexPoint (D.arcSource e)).2⟩ : ℂ) := by
      apply Complex.ext <;> simp [cornerCenter, arcVector]
    rw [heq]
    exact hv _
  have h1 : b ≤ (a * cornerCenter D e).re := hv _
  have h2 : b ≤ (a * (cornerCenter D e + arcVector D (D.continuation e))).re := by
    rw [← cornerCenter_continuation]
    exact hv _
  have hsum : (1-t)^2 + t^2 ≤ 1 := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have hw : δ.val*(1-t)^2 + δ.val*t^2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hsum δ.property.1.le
    nlinarith [δ.property.2]
  have h := complex_halfplane_combination a
    (cornerCenter D e - arcVector D e) (cornerCenter D e)
    (cornerCenter D e + arcVector D (D.continuation e)) b
    (δ.val*(1-t)^2) (δ.val*t^2)
    (mul_nonneg δ.property.1.le (sq_nonneg _))
    (mul_nonneg δ.property.1.le (sq_nonneg _)) hw h0 h1 h2
  have heq : roundedCorner D e δ.val t =
      (δ.val*(1-t)^2) • (cornerCenter D e - arcVector D e) +
      (1-δ.val*(1-t)^2-δ.val*t^2) • cornerCenter D e +
      (δ.val*t^2) • (cornerCenter D e + arcVector D (D.continuation e)) := by
    apply Complex.ext <;> simp [roundedCorner, Complex.real_smul] <;> ring
  rw [heq]
  exact h

/-- The normalized cell uses a corner or a convex subsegment of the next arc. -/
theorem normalizedRoundedCell_halfplane (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (a : ℂ) (b t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (hv : ∀ v, b ≤ (a * (⟨(D.vertexPoint v).1, (D.vertexPoint v).2⟩ : ℂ)).re) :
    b ≤ (a * normalizedRoundedCell D e δ t).re := by
  have hp : 0 < 2*δ.val := mul_pos (by norm_num) δ.property.1
  unfold normalizedRoundedCell roundedStep
  split_ifs with hc
  · exact roundedCorner_halfplane D e δ a b _ ⟨div_nonneg ht.1 hp.le,hc⟩ hv
  · have htδ : 2*δ.val < t := by
      have hh := (lt_div_iff₀ hp).mp (lt_of_not_ge hc)
      nlinarith
    have hs : 0 ≤ t-δ.val := by linarith [δ.property.1]
    have hle : t-δ.val ≤ 1 := by linarith [ht.2,δ.property.1]
    have h1 : b ≤ (a * cornerCenter D e).re := hv _
    have h2 : b ≤ (a * (cornerCenter D e + arcVector D (D.continuation e))).re := by
      rw [← cornerCenter_continuation]
      exact hv _
    have h := complex_halfplane_combination a (cornerCenter D e) (cornerCenter D e)
      (cornerCenter D e + arcVector D (D.continuation e)) b 0 (t-δ.val)
      le_rfl hs (by simpa using hle) h1 h1 h2
    have heq : roundingStraight D e δ (t/(2*δ.val)) =
        (0:ℝ) • cornerCenter D e + (1-0-(t-δ.val)) • cornerCenter D e +
        (t-δ.val) • (cornerCenter D e + arcVector D (D.continuation e)) := by
      have hscale : (t / (2*δ.val) - 1) * (2*δ.val) = t - 2*δ.val := by
        rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hp), one_mul]
      rw [roundingStraight, smul_smul, hscale]
      apply Complex.ext <;> simp [Complex.real_smul] <;> ring
    rw [heq]
    exact h

/-- All times and all components; no component membership or rounding-support
assumption is added to the all-vertex half-plane premise. -/
theorem roundedComponentCurve_halfplane_of_vertices (D : PLLinkDiagram)
    (e : Fin D.nArc) (δ : RoundingFraction) (a : ℂ) (b : ℝ)
    (hv : ∀ v, b ≤ (a * (⟨(D.vertexPoint v).1, (D.vertexPoint v).2⟩ : ℂ)).re)
    (t : ℝ) : b ≤ (a * roundedComponentCurve D e δ t).re :=
  normalizedRoundedCell_halfplane D _ δ a b (Int.fract t)
    ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩ hv

/-- Literal determinant-to-complex-coordinate bridge from the actual retained
parent geometry. The linear functional is det(q-p, ·), with no unit scaling. -/
theorem SupportingRootGeometry.rounded_halfplane
    (s : MarkedParentState) (p q : PlanarPoint ℝ)
    (h : SupportingRootGeometry s p q) (e : Fin s.1.nArc)
    (δ : RoundingFraction) (t : ℝ) :
    ( (⟨-(q-p).2, -(q-p).1⟩ : ℂ) * (⟨p.1,p.2⟩ : ℂ)).re ≤
      ((⟨-(q-p).2, -(q-p).1⟩ : ℂ) * roundedComponentCurve s.1 e δ t).re := by
  apply roundedComponentCurve_halfplane_of_vertices
  intro v
  have hv := h.2 v
  simp [planarDet] at hv
  simp [Complex.mul_re]
  nlinarith

end DirectGLSSW.HOMFLY.PrincipalTurning


