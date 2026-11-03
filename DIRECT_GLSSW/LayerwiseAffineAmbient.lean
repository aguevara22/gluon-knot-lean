import DescendingHeightArcs
import Mathlib.Topology.Homeomorph.Defs

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial

/-- Explicit horizontal affine homeomorphisms, with jointly continuous
forward and inverse maps. No isotopy extension theorem is used. -/
theorem exists_layerwise_affine_ambient
    (A B : C(unitInterval × ℝ,ℂ))
    (hA : ∀ s z, A (s,z) ≠ 0)
    (hA0 : ∀ z, A (0,z) = 1) (hB0 : ∀ z, B (0,z) = 0) :
    ∃ F : unitInterval → ((ℂ × ℝ) ≃ₜ (ℂ × ℝ)),
      F 0 = Homeomorph.refl (ℂ × ℝ) ∧
      (∀ s x, F s x = (A (s,x.2)*x.1+B (s,x.2),x.2)) ∧
      (∀ s x, (F s).symm x = ((x.1-B (s,x.2))/A (s,x.2),x.2)) ∧
      Continuous (fun p : unitInterval × (ℂ × ℝ) => F p.1 p.2) ∧
      Continuous (fun p : unitInterval × (ℂ × ℝ) => (F p.1).symm p.2) := by
  let F : unitInterval → ((ℂ × ℝ) ≃ₜ (ℂ × ℝ)) := fun s =>
    { toEquiv :=
        { toFun := fun x => (A (s,x.2)*x.1+B (s,x.2),x.2)
          invFun := fun x => ((x.1-B (s,x.2))/A (s,x.2),x.2)
          left_inv := by
            intro x
            apply Prod.ext
            · dsimp
              field_simp [hA s x.2] <;> ring
            · rfl
          right_inv := by
            intro x
            apply Prod.ext
            · dsimp
              field_simp [hA s x.2] <;> ring
            · rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by
        apply Continuous.prod_mk
        · apply Continuous.div
          · fun_prop
          · fun_prop
          · intro x
            exact hA s x.2
        · fun_prop }
  refine ⟨F,?_,fun _ _ => rfl,fun _ _ => rfl,?_,?_⟩
  · apply Homeomorph.ext
    intro x
    apply Prod.ext
    · change A (0,x.2)*x.1+B (0,x.2)=x.1
      rw [hA0,hB0,one_mul,add_zero]
    · rfl
  · change Continuous (fun p : unitInterval × (ℂ × ℝ) =>
      (A (p.1,p.2.2)*p.2.1+B (p.1,p.2.2),p.2.2))
    fun_prop
  · change Continuous (fun p : unitInterval × (ℂ × ℝ) =>
      ((p.2.1-B (p.1,p.2.2))/A (p.1,p.2.2),p.2.2))
    apply Continuous.prod_mk
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro p
        exact hA p.1 p.2.2
    · fun_prop

end DirectGLSSW.DescendingSpatial

