import RoundingLocalInjectivity

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- The actual adjacent arc vectors generate a pointed positive cone. -/
theorem corner_positive_cone_ne_zero (D : PLLinkDiagram) (e : Fin D.nArc)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    a • arcVector D e + b • arcVector D (D.continuation e) ≠ 0 := by
  intro hz
  by_cases hb0 : b = 0
  · simp only [hb0, zero_smul, add_zero] at hz
    rcases smul_eq_zero.mp hz with h | h
    · exact (ne_of_gt ha) h
    · exact arcVector_ne_zero D e h
  · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have heq : arcVector D (D.continuation e) = (-a / b) • arcVector D e := by
      calc
        arcVector D (D.continuation e) = (1 / b) • (b • arcVector D (D.continuation e)) := by
          rw [smul_smul, one_div_mul_cancel hb0, one_smul]
        _ = (1 / b) • (-(a • arcVector D e)) := by
          rw [eq_neg_of_add_eq_zero_right hz]
        _ = (-a / b) • arcVector D e := by
          rw [smul_neg, smul_smul, ← neg_smul]
          congr 1
          ring
    apply adjacent_not_negative_multiple D e (a / b) (div_pos ha hbp)
    simpa only [Complex.real_smul, neg_div, Complex.ofReal_neg] using heq

/-- Except at its incoming cut endpoint, an actual rounded corner misses the
entire retained incoming ray. -/
theorem roundedCorner_ne_retained_incoming (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ t s : ℝ) (hδ : 0 < δ) (ht : t ∈ Set.Ioc 0 1) (hs : δ ≤ s) :
    roundedCorner D e δ t ≠ cornerCenter D e - s • arcVector D e := by
  have hsq : (1 - t) ^ 2 < 1 := by nlinarith [ht.1,ht.2]
  have ha : 0 < s - δ * (1 - t) ^ 2 := by
    nlinarith [mul_pos hδ (sub_pos.mpr hsq)]
  have hb : 0 ≤ δ * t ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
  have heq : roundedCorner D e δ t - (cornerCenter D e - s • arcVector D e) =
      (s - δ * (1 - t) ^ 2) • arcVector D e +
        (δ * t ^ 2) • arcVector D (D.continuation e) := by
    simp only [roundedCorner, Complex.real_smul]
    push_cast
    ring
  intro h
  have hz := sub_eq_zero.mpr h
  rw [heq] at hz
  exact corner_positive_cone_ne_zero D e _ _ ha hb hz

/-- Except at its outgoing cut endpoint, an actual rounded corner misses the
entire retained outgoing ray. -/
theorem roundedCorner_ne_retained_outgoing (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ t s : ℝ) (hδ : 0 < δ) (ht : t ∈ Set.Ico 0 1) (hs : δ ≤ s) :
    roundedCorner D e δ t ≠ cornerCenter D e + s • arcVector D (D.continuation e) := by
  have hsq : t ^ 2 < 1 := by nlinarith [ht.1,ht.2]
  have ha : 0 < δ * (1 - t) ^ 2 := mul_pos hδ (sq_pos_of_pos (by linarith [ht.2]))
  have hb : 0 ≤ s - δ * t ^ 2 := by nlinarith [mul_pos hδ (sub_pos.mpr hsq)]
  have heq : (cornerCenter D e + s • arcVector D (D.continuation e)) - roundedCorner D e δ t =
      (δ * (1 - t) ^ 2) • arcVector D e +
        (s - δ * t ^ 2) • arcVector D (D.continuation e) := by
    simp only [roundedCorner, Complex.real_smul]
    push_cast
    ring
  intro h
  have hz := sub_eq_zero.mpr h.symm
  rw [heq] at hz
  exact corner_positive_cone_ne_zero D e _ _ ha hb hz

end DirectGLSSW.HOMFLY.PrincipalTurning



