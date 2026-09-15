import SM.EuclideanPlane

/-! The complete two-edge regular domain: both vectors nonzero, with only
negative scalar multiples excluded. Positive collinear directions are allowed. -/

namespace SM

def RegularPair (u v : Plane) : Prop :=
  u ≠ 0 ∧ v ≠ 0 ∧ ¬ ∃ r : ℝ, r < 0 ∧ v = r • u

theorem negativeScalar_iff_dot_det {u v : Plane} (hu : u ≠ 0) :
    (∃ r : ℝ, r < 0 ∧ v = r • u) ↔ planeDot u v < 0 ∧ det u v = 0 := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    rw [planeDot_smul_right, det_smul_self]
    exact ⟨mul_neg_of_neg_of_pos hr (planeDot_self_pos hu), rfl⟩
  · rintro ⟨hr, hd⟩
    exact ⟨planeDot u v / planeDot u u,
      div_neg_of_neg_of_pos hr (planeDot_self_pos hu), scalar_of_det_zero hu hd⟩

theorem positiveScalar_iff_dot_det {u v : Plane} (hu : u ≠ 0) :
    (∃ r : ℝ, 0 < r ∧ v = r • u) ↔ 0 < planeDot u v ∧ det u v = 0 := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    rw [planeDot_smul_right, det_smul_self]
    exact ⟨mul_pos hr (planeDot_self_pos hu), rfl⟩
  · rintro ⟨hr, hd⟩
    exact ⟨planeDot u v / planeDot u u,
      div_pos hr (planeDot_self_pos hu), scalar_of_det_zero hu hd⟩

theorem regularPair_slitPlane {u v : Plane} (h : RegularPair u v) :
    cornerRotor u v ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff_arg.mpr
  refine ⟨?_, cornerRotor_ne_zero h.1 h.2.1⟩
  intro he
  have hz := Complex.arg_eq_pi_iff.mp he
  rw [cornerRotor_re, cornerRotor_im] at hz
  exact h.2.2 ((negativeScalar_iff_dot_det h.1).mpr hz)

theorem regularPair_iff_slitPlane (u v : Plane) : RegularPair u v ↔
    u ≠ 0 ∧ v ≠ 0 ∧ cornerRotor u v ∈ Complex.slitPlane := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, regularPair_slitPlane h⟩
  · rintro ⟨hu, hv, hz⟩
    refine ⟨hu, hv, ?_⟩
    intro hr
    have h := (negativeScalar_iff_dot_det hu).mp hr
    have ha : (cornerRotor u v).arg = Real.pi := by
      apply Complex.arg_eq_pi_iff.mpr
      simpa only [cornerRotor_re, cornerRotor_im] using h
    exact (Complex.slitPlane_arg_ne_pi hz) ha

noncomputable def principalAngle (u v : Plane) : ℝ := (cornerRotor u v).arg

theorem principalAngle_bounds {u v : Plane} (h : RegularPair u v) :
    -Real.pi < principalAngle u v ∧ principalAngle u v < Real.pi := by
  exact ⟨Complex.neg_pi_lt_arg _, (Complex.arg_le_pi _).lt_iff_ne.mpr
    (Complex.slitPlane_arg_ne_pi (regularPair_slitPlane h))⟩

theorem principalAngle_cos {u v : Plane} (h : RegularPair u v) :
    Real.cos (principalAngle u v) = planeDot u v / (euclideanLength u * euclideanLength v) := by
  rw [principalAngle, Complex.cos_arg (cornerRotor_ne_zero h.1 h.2.1),
    cornerRotor_re, cornerRotor_norm]

theorem principalAngle_neg_iff (u v : Plane) :
    principalAngle u v < 0 ↔ det u v < 0 := by
  rw [principalAngle, Complex.arg_neg_iff, cornerRotor_im]

theorem principalAngle_eq_zero_iff {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) :
    principalAngle u v = 0 ↔ ∃ r : ℝ, 0 < r ∧ v = r • u := by
  rw [principalAngle, Complex.arg_eq_zero_iff, cornerRotor_re, cornerRotor_im,
    positiveScalar_iff_dot_det hu]
  constructor
  · rintro ⟨hd, hdet⟩
    refine ⟨hd.lt_of_ne ?_, hdet⟩
    intro he
    apply cornerRotor_ne_zero hu hv
    apply Complex.ext
    · simpa only [cornerRotor_re, Complex.zero_re] using he.symm
    · simpa only [cornerRotor_im, Complex.zero_im] using hdet
  · rintro ⟨hd, hdet⟩
    exact ⟨hd.le, hdet⟩

theorem principalAngle_zero_iff_det_zero {u v : Plane} (h : RegularPair u v) :
    principalAngle u v = 0 ↔ det u v = 0 := by
  rw [principalAngle, Complex.arg_eq_zero_iff, cornerRotor_re, cornerRotor_im]
  constructor
  · exact And.right
  · intro hd
    refine ⟨le_of_not_gt ?_, hd⟩
    intro hneg
    exact h.2.2 ((negativeScalar_iff_dot_det h.1).mpr ⟨hneg, hd⟩)

theorem principalAngle_sign {u v : Plane} (h : RegularPair u v) :
    SignType.sign (principalAngle u v) = SignType.sign (det u v) := by
  rcases lt_trichotomy (principalAngle u v) 0 with ht | ht | ht
  · rw [sign_eq_neg_one_iff.mpr ht,
      sign_eq_neg_one_iff.mpr ((principalAngle_neg_iff u v).mp ht)]
  · rw [ht, (principalAngle_zero_iff_det_zero h).mp ht]
  · have hn : ¬ det u v < 0 := fun hd => lt_asymm ht ((principalAngle_neg_iff u v).mpr hd)
    have hz : det u v ≠ 0 := fun hd => ht.ne' ((principalAngle_zero_iff_det_zero h).mpr hd)
    have hd : 0 < det u v := (le_of_not_gt hn).lt_of_ne hz.symm
    rw [sign_eq_one_iff.mpr ht, sign_eq_one_iff.mpr hd]

end SM
