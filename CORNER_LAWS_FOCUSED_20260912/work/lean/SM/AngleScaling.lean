import SM.RegularDefinition

/-! Positive independent rescaling preserves actual principal angles and
their full regular domain. Used for actual edge-interior vertex insertion. -/

namespace SM

theorem cornerRotor_smul (r s : ℝ) (u v : Plane) :
    cornerRotor (r • u) (s • v) = ((r * s : ℝ) : ℂ) * cornerRotor u v := by
  apply Complex.ext <;> simp [cornerRotor, planeComplex] <;> ring

theorem principalAngle_smul {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (u v : Plane) :
    principalAngle (r • u) (s • v) = principalAngle u v := by
  unfold principalAngle
  rw [cornerRotor_smul, Complex.arg_real_mul _ (mul_pos hr hs)]

theorem regularPair_smul {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {u v : Plane} (h : RegularPair u v) : RegularPair (r • u) (s • v) := by
  have hu : r • u ≠ 0 := smul_ne_zero hr.ne' h.1
  have hv : s • v ≠ 0 := smul_ne_zero hs.ne' h.2.1
  apply (regularPair_iff_slitPlane _ _).mpr
  refine ⟨hu, hv, Complex.mem_slitPlane_iff_arg.mpr ⟨?_, cornerRotor_ne_zero hu hv⟩⟩
  change principalAngle (r • u) (s • v) ≠ Real.pi
  rw [principalAngle_smul hr hs]
  exact (principalAngle_bounds h).2.ne

theorem regularPair_self {u : Plane} (hu : u ≠ 0) : RegularPair u u := by
  refine ⟨hu, hu, ?_⟩
  intro hn
  have hp := planeDot_self_pos hu
  have hm := ((negativeScalar_iff_dot_det hu).mp hn).1
  exact lt_asymm hp hm

theorem principalAngle_self {u : Plane} (hu : u ≠ 0) : principalAngle u u = 0 :=
  (principalAngle_eq_zero_iff hu hu).mpr ⟨1, zero_lt_one, by simp⟩

end SM
