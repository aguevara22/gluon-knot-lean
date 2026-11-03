import CornerConeAngle

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Elementary chord geometry: opposite nonzero real rays force a zero
on the closed chord. This is not an exposedness assertion about a diagram. -/
theorem zeroFreeChord_not_opposite_args (z w : ℂ)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((1-t : ℝ) : ℂ)*z+(t : ℂ)*w≠0) :
    ¬(Complex.arg z=0 ∧ Complex.arg w=Real.pi) := by
  rintro ⟨haz,haw⟩
  have hz : z≠0 := by simpa using hseg 0 ⟨le_rfl,by norm_num⟩
  obtain ⟨hzre,hzim⟩ := Complex.arg_eq_zero_iff.mp haz
  obtain ⟨hwre,hwim⟩ := Complex.arg_eq_pi_iff.mp haw
  have hzpos : 0<z.re := by
    by_contra hn
    have hzre0 : z.re=0 := le_antisymm (le_of_not_gt hn) hzre
    apply hz
    exact Complex.ext hzre0 hzim
  have hd : 0<z.re-w.re := by linarith
  let t : ℝ := z.re/(z.re-w.re)
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact (div_pos hzpos hd).le
    · exact (div_le_one hd).mpr (by linarith)
  apply hseg t ht
  apply Complex.ext
  · simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero,Complex.zero_re]
    dsimp [t]
    field_simp [ne_of_gt hd]
    <;> ring
  · simp [hzim,hwim]

/-- A zero-free chord in the closed upper half-plane has no principal-arg
wrap. Later consumers must derive the half-plane condition from actual
source supporting geometry; this lemma supplies no such condition. -/
theorem upperHalfPlane_chord_ratio_arg (z w : ℂ) (hz : 0≤z.im) (hw : 0≤w.im)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((1-t : ℝ) : ℂ)*z+(t : ℂ)*w≠0) :
    Complex.arg (w/z)=Complex.arg w-Complex.arg z := by
  have hzn : z≠0 := by simpa using hseg 0 ⟨le_rfl,by norm_num⟩
  have hwn : w≠0 := by simpa using hseg 1 ⟨by norm_num,le_rfl⟩
  have haz := Complex.arg_nonneg_iff.mpr hz
  have haw := Complex.arg_nonneg_iff.mpr hw
  have hzp := Complex.arg_le_pi z
  have hwp := Complex.arg_le_pi w
  have hforward := zeroFreeChord_not_opposite_args z w hseg
  have hseg' : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((1-t : ℝ) : ℂ)*w+(t : ℂ)*z≠0 := by
    intro t ht
    have h := hseg (1-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
    simpa only [sub_sub_cancel,add_comm] using h
  have hreverse := zeroFreeChord_not_opposite_args w z hseg'
  have hdiff : -Real.pi<Complex.arg w-Complex.arg z ∧
      Complex.arg w-Complex.arg z<Real.pi := by
    constructor
    · by_contra hn
      apply hreverse
      constructor <;> linarith
    · by_contra hn
      apply hforward
      constructor <;> linarith
  have hangle : (Complex.arg (w/z) : Real.Angle) =
      ((Complex.arg w-Complex.arg z : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub]
    exact Complex.arg_div_coe_angle hwn hzn
  have hreal := congrArg Real.Angle.toReal hangle
  rw [Complex.arg_coe_angle_toReal_eq_arg,
    Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hdiff.1,hdiff.2.le⟩] at hreal
  exact hreal

end DirectGLSSW.HOMFLY.PrincipalTurning


