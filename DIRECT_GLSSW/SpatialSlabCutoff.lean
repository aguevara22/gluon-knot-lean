import LayerwiseAffineAmbient

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial

def slabParameter (H : ℝ) : C(ℝ,unitInterval) where
  toFun z := ⟨min (max (H+1-z) 0) 1,⟨le_min (le_max_right _ _) (by norm_num),min_le_right _ _⟩⟩
  continuous_toFun := by fun_prop

theorem slabParameter_apply (H z : ℝ) :
    (slabParameter H z).val = min (max (H+1-z) 0) 1 := rfl

theorem slabParameter_on_slab (H : ℝ) (t : unitInterval) :
    slabParameter H (H+1-t.val) = t := by
  apply Subtype.ext
  rw [slabParameter_apply,show H+1-(H+1-t.val)=t.val by ring,
    max_eq_left t.property.1,min_eq_left t.property.2]

/-- Fixed half-unit height buffers; the cutoff is literal, not a chosen support. -/
def slabCutoff (H : ℝ) : C(ℝ,ℝ) where
  toFun z := max 0 (min 1 (2*min (z-H+1/2) (H+3/2-z)))
  continuous_toFun := by fun_prop

theorem slabCutoff_apply (H z : ℝ) :
    slabCutoff H z = max 0 (min 1 (2*min (z-H+1/2) (H+3/2-z))) := rfl

theorem slabCutoff_bounds (H z : ℝ) : 0 ≤ slabCutoff H z ∧ slabCutoff H z ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem slabCutoff_on_slab (H : ℝ) (t : unitInterval) :
    slabCutoff H (H+1-t.val) = 1 := by
  have hmin : 1/2 ≤ min ((H+1-t.val)-H+1/2) (H+3/2-(H+1-t.val)) := by
    apply le_min <;> linarith [t.property.1,t.property.2]
  rw [slabCutoff_apply,min_eq_left (by linarith :
    (1:ℝ) ≤ 2*min ((H+1-t.val)-H+1/2) (H+3/2-(H+1-t.val)))]
  norm_num

theorem slabCutoff_outside (H z : ℝ) (h : z ≤ H-1/2 ∨ H+3/2 ≤ z) :
    slabCutoff H z = 0 := by
  have hmin : min (z-H+1/2) (H+3/2-z) ≤ 0 := by
    rcases h with h | h
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  have hm : min 1 (2*min (z-H+1/2) (H+3/2-z)) ≤ 0 :=
    (min_le_right _ _).trans (by linarith)
  exact max_eq_left hm

theorem positive_affine_scale (s ℓ : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) (hℓ : 0 < ℓ) :
    0 < 1-s+s*ℓ := by
  by_cases h : s = 1
  · subst s
    simpa using hℓ
  · have hlt : s < 1 := lt_of_le_of_ne hs.2 h
    exact add_pos_of_pos_of_nonneg (by linarith) (mul_nonneg hs.1 hℓ.le)

end DirectGLSSW.DescendingSpatial







