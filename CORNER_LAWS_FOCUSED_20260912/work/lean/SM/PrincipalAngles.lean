import SM.RegularPairs

/-! Existence and uniqueness for precisely the source cosine/sign
specification on (-pi,pi). Existence itself excludes zero vectors and
antiparallel directions, rather than assuming the desired regular domain. -/

namespace SM

def PrincipalAngleSpec (u v : Plane) (θ : ℝ) : Prop :=
  (-Real.pi < θ ∧ θ < Real.pi) ∧
  Real.cos θ = planeDot u v / (euclideanLength u * euclideanLength v) ∧
  SignType.sign θ = SignType.sign (det u v)

theorem principalAngle_spec {u v : Plane} (h : RegularPair u v) :
    PrincipalAngleSpec u v (principalAngle u v) :=
  ⟨principalAngle_bounds h, principalAngle_cos h, principalAngle_sign h⟩

theorem angle_eq_of_cos_sign {a b : ℝ}
    (ha : -Real.pi < a ∧ a < Real.pi) (hb : -Real.pi < b ∧ b < Real.pi)
    (hc : Real.cos a = Real.cos b) (hs : SignType.sign a = SignType.sign b) : a = b := by
  have haa : |a| < Real.pi := abs_lt.mpr ⟨by linarith [ha.1], ha.2⟩
  have hbb : |b| < Real.pi := abs_lt.mpr ⟨by linarith [hb.1], hb.2⟩
  have hab : |a| = |b| := Real.injOn_cos ⟨abs_nonneg a, haa.le⟩
    ⟨abs_nonneg b, hbb.le⟩ (by simpa only [Real.cos_abs] using hc)
  calc
    a = (SignType.sign a : ℝ) * |a| := (sign_mul_abs a).symm
    _ = (SignType.sign b : ℝ) * |b| := by rw [hs, hab]
    _ = b := sign_mul_abs b

theorem principalAngleSpec_unique {u v : Plane} {a b : ℝ}
    (ha : PrincipalAngleSpec u v a) (hb : PrincipalAngleSpec u v b) : a = b :=
  angle_eq_of_cos_sign ha.1 hb.1 (ha.2.1.trans hb.2.1.symm) (ha.2.2.trans hb.2.2.symm)

theorem principalAngleSpec_nonzero {u v : Plane} {θ : ℝ}
    (h : PrincipalAngleSpec u v θ) : u ≠ 0 ∧ v ≠ 0 := by
  constructor
  · intro hu
    have hz : SignType.sign θ = 0 := by simpa [hu, det] using h.2.2
    have ht := sign_eq_zero_iff.mp hz
    have hc := h.2.1
    rw [ht, hu] at hc
    norm_num [planeDot, euclideanLength, planeComplex] at hc
  · intro hv
    have hz : SignType.sign θ = 0 := by simpa [hv, det] using h.2.2
    have ht := sign_eq_zero_iff.mp hz
    have hc := h.2.1
    rw [ht, hv] at hc
    norm_num [planeDot, euclideanLength, planeComplex] at hc

theorem regularPair_of_principalAngleSpec {u v : Plane} {θ : ℝ}
    (h : PrincipalAngleSpec u v θ) : RegularPair u v := by
  obtain ⟨hu, hv⟩ := principalAngleSpec_nonzero h
  refine ⟨hu, hv, ?_⟩
  intro hn
  obtain ⟨hdot, hdet⟩ := (negativeScalar_iff_dot_det hu).mp hn
  have hz : SignType.sign θ = 0 := by simpa only [hdet, sign_zero] using h.2.2
  have ht := sign_eq_zero_iff.mp hz
  have hneg : planeDot u v / (euclideanLength u * euclideanLength v) < 0 :=
    div_neg_of_neg_of_pos hdot (mul_pos (euclideanLength_pos hu) (euclideanLength_pos hv))
  rw [← h.2.1, ht, Real.cos_zero] at hneg
  norm_num at hneg

theorem principalAngle_existsUnique_iff (u v : Plane) :
    (∃! θ, PrincipalAngleSpec u v θ) ↔ RegularPair u v := by
  constructor
  · rintro ⟨θ, hθ, _⟩
    exact regularPair_of_principalAngleSpec hθ
  · intro h
    exact ⟨principalAngle u v, principalAngle_spec h,
      fun _ hθ => principalAngleSpec_unique hθ (principalAngle_spec h)⟩

end SM
