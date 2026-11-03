import SpatialSlabCutoff
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial

/-- A literal similarity on the entire closed slab, tapered to identity in
fixed height buffers, gives actual ambient homeomorphisms of the whole space. -/
theorem exists_localized_slab_similarity (β : C(unitInterval,ℂ))
    (ℓ θ : C(unitInterval,ℝ)) (hℓ : ∀ t, 0 < ℓ t) (b : ℂ) (H : ℝ) :
    ∃ F : unitInterval → ((ℂ × ℝ) ≃ₜ (ℂ × ℝ)),
      F 0 = Homeomorph.refl (ℂ × ℝ) ∧
      Continuous (fun p : unitInterval × (ℂ × ℝ) => F p.1 p.2) ∧
      Continuous (fun p : unitInterval × (ℂ × ℝ) => (F p.1).symm p.2) ∧
      (∀ s x, (F s x).2 = x.2) ∧
      (∀ s x, x.2 ≤ H-1/2 ∨ H+3/2 ≤ x.2 → F s x = x) ∧
      ∀ s (t : unitInterval) (x : ℂ),
        F s (x,H+1-t.val) =
          (β t + (s.val:ℂ)*(b-β t) +
            ((1-s.val+s.val*ℓ t:ℝ):ℂ)*
              Complex.exp (-((s.val*θ t:ℝ):ℂ)*Complex.I)*(x-β t), H+1-t.val) := by
  let A : C(unitInterval × ℝ,ℂ) :=
    { toFun := fun p =>
        ((1-p.1.val*slabCutoff H p.2+p.1.val*slabCutoff H p.2*ℓ (slabParameter H p.2):ℝ):ℂ)*
          Complex.exp (-((p.1.val*slabCutoff H p.2*θ (slabParameter H p.2):ℝ):ℂ)*Complex.I)
      continuous_toFun := by fun_prop }
  let B : C(unitInterval × ℝ,ℂ) :=
    { toFun := fun p => β (slabParameter H p.2) +
        ((p.1.val*slabCutoff H p.2:ℝ):ℂ)*(b-β (slabParameter H p.2)) -
          A p*β (slabParameter H p.2)
      continuous_toFun := by fun_prop }
  have hA : ∀ s z, A (s,z) ≠ 0 := by
    intro s z
    have hc := slabCutoff_bounds H z
    have hs : s.val*slabCutoff H z ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · exact mul_nonneg s.property.1 hc.1
      · simpa using mul_le_mul s.property.2 hc.2 hc.1 (by norm_num : (0:ℝ) ≤ 1)
    have hp := positive_affine_scale _ _ hs (hℓ (slabParameter H z))
    change _ * Complex.exp _ ≠ 0
    exact mul_ne_zero (by exact_mod_cast ne_of_gt hp) (Complex.exp_ne_zero _)
  have hA0 : ∀ z, A (0,z) = 1 := by intro z; simp [A]
  have hB0 : ∀ z, B (0,z) = 0 := by intro z; simp [B,hA0]
  obtain ⟨F,hF0,hF,hInv,hCont,hInvCont⟩ := exists_layerwise_affine_ambient A B hA hA0 hB0
  refine ⟨F,hF0,hCont,hInvCont,?_,?_,?_⟩
  · intro s x
    rw [hF]
  · intro s x hx
    have hc := slabCutoff_outside H x.2 hx
    rw [hF]
    simp [A,B,hc]
  · intro s t x
    rw [hF]
    have ht := slabParameter_on_slab H t
    have hc := slabCutoff_on_slab H t
    apply Prod.ext
    · dsimp only [A,B,ContinuousMap.coe_mk,Prod.fst,Prod.snd]
      rw [ht,hc]
      push_cast
      ring
    · rfl

end DirectGLSSW.DescendingSpatial

