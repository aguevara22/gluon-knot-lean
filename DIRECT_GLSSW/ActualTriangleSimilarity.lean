import ActualSplitArgumentLift
import RotationByArgumentLift
import LocalizedSlabSimilarity

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY

theorem actual_rotation_scale_to_tent (D : PLLinkDiagram) (e : Fin D.nArc)
    (θ : C(unitInterval,ℝ))
    (hθ : ∀ t, (θ t:Real.Angle) = ((clampedDifference D e t).arg:Real.Angle))
    (t : unitInterval) :
    (clampedTentScale D e t:ℂ)*Complex.exp (-(θ t:ℂ)*Complex.I)*
      (splitMainComplex D e t-splitBeta D e t) = (min t.val (1-t.val)/2:ℝ) := by
  obtain ⟨ρ,hρ,hw,hr⟩ := split_difference_clamp_proportional D e t
  have hrot := rotation_by_argument_lift (clampedDifference D e t) (θ t) (hθ t)
  calc
    (clampedTentScale D e t:ℂ)*Complex.exp (-(θ t:ℂ)*Complex.I)*
        (splitMainComplex D e t-splitBeta D e t) =
      (clampedTentScale D e t:ℂ)*(ρ:ℂ)*
        (Complex.exp (-(θ t:ℂ)*Complex.I)*clampedDifference D e t) := by
          rw [hw,Complex.real_smul]
          ring
    _ = (clampedTentScale D e t:ℂ)*(ρ:ℂ)*(‖clampedDifference D e t‖:ℂ) := by rw [hrot]
    _ = ((clampedTentScale D e t * ‖splitMainComplex D e t-splitBeta D e t‖:ℝ):ℂ) := by
      rw [hw,norm_smul,Real.norm_eq_abs,abs_of_nonneg hρ]
      push_cast
      ring
    _ = (min t.val (1-t.val)/2:ℝ) := by rw [clampedTentScale_norm_identity]

/-- Actual ambient straightening, fixed outside the stated height band.
All scale/direction inputs have been produced from the actual diagram. -/
theorem exists_actual_triangle_similarity (D : PLLinkDiagram) (e : Fin D.nArc)
    (b : ℂ) (H : ℝ) :
    ∃ F : unitInterval → ((ℂ × ℝ) ≃ₜ (ℂ × ℝ)),
      F 0 = Homeomorph.refl (ℂ × ℝ) ∧
      Continuous (fun p : unitInterval × (ℂ × ℝ) => F p.1 p.2) ∧
      Continuous (fun p : unitInterval × (ℂ × ℝ) => (F p.1).symm p.2) ∧
      (∀ s x, (F s x).2 = x.2) ∧
      (∀ s x, x.2 ≤ H-1/2 ∨ H+3/2 ≤ x.2 → F s x = x) ∧
      (∀ t : unitInterval, F 1 (descendingMain D e H t) =
        (b+(min t.val (1-t.val)/2:ℝ),H+1-t.val)) ∧
      ∀ t : unitInterval, F 1 (ascendingClosure D e H t) = (b,H+t.val) := by
  obtain ⟨θ,hθ0,hθ,hθInterior⟩ := exists_actual_split_argument_lift D e
  obtain ⟨F,h0,hCont,hInvCont,hHeight,hOutside,hFormula⟩ :=
    exists_localized_slab_similarity (splitBeta D e) (clampedTentScale D e) θ
      (clampedTentScale_pos D e) b H
  refine ⟨F,h0,hCont,hInvCont,hHeight,hOutside,?_,?_⟩
  · intro t
    rw [descendingMain_apply,hFormula]
    apply Prod.ext
    · change splitBeta D e t + (1:ℂ)*(b-splitBeta D e t) +
        ((1-1+1*clampedTentScale D e t:ℝ):ℂ)*
          Complex.exp (-((1*θ t:ℝ):ℂ)*Complex.I)*
            (splitMainComplex D e t-splitBeta D e t) = b+(min t.val (1-t.val)/2:ℝ)
      simp only [one_mul,sub_self,zero_add]
      rw [actual_rotation_scale_to_tent D e θ hθ t]
      ring
    · rfl
  · intro t
    let u : unitInterval := ⟨1-t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩
    have hp : ascendingClosure D e H t = (splitBeta D e u,H+1-u.val) := by
      apply Prod.ext
      · apply Complex.ext <;>
          simp [ascendingClosure,splitBeta_apply,u,Complex.equivRealProd_symm_apply,affinePoint] <;> ring
      · dsimp [ascendingClosure,u]
        ring
    rw [hp,hFormula]
    apply Prod.ext
    · change splitBeta D e u + (1:ℂ)*(b-splitBeta D e u) + _*(splitBeta D e u-splitBeta D e u) = b
      simp
    · dsimp [u]
      ring

end DirectGLSSW.DescendingSpatial


