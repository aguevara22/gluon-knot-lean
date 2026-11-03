import SegmentLiftIncrement
import Mathlib.Topology.Path

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Restricting a real argument lift of concatenated actual paths gives
lifts of each path whose increments add exactly. -/
theorem path_trans_argument_lift_split {a b c : ℂ}
    (γ : Path a b) (η : Path b c) (z : ℂ)
    (θ : C(unitInterval, ℝ))
    (hθ : ∀ t, (θ t : Real.Angle) = (((γ.trans η) t - z).arg : Real.Angle)) :
    ∃ L R : C(unitInterval, ℝ),
      (∀ t, (L t : Real.Angle) = ((γ t-z).arg : Real.Angle)) ∧
      (∀ t, (R t : Real.Angle) = ((η t-z).arg : Real.Angle)) ∧
      θ 1-θ 0 = (L 1-L 0)+(R 1-R 0) := by
  let l : C(unitInterval, unitInterval) :=
    { toFun := fun t => ⟨t.val/2, by constructor <;> linarith [t.property.1,t.property.2]⟩
      continuous_toFun := by fun_prop }
  let r : C(unitInterval, unitInterval) :=
    { toFun := fun t => ⟨(1+t.val)/2, by constructor <;> linarith [t.property.1,t.property.2]⟩
      continuous_toFun := by fun_prop }
  have hl (t : unitInterval) : (γ.trans η) (l t) = γ t := by
    rw [Path.trans_apply]
    split_ifs with h
    · congr 1
      apply Subtype.ext
      dsimp [l]
      ring
    · have ht := t.property.2
      change ¬ t.val/2 ≤ 1/2 at h
      linarith
  have hr (t : unitInterval) : (γ.trans η) (r t) = η t := by
    rw [Path.trans_apply]
    split_ifs with h
    · have ht : t = 0 := by
        apply Subtype.ext
        change (1+t.val)/2 ≤ 1/2 at h
        have ht0 := t.property.1
        change t.val = 0
        linarith
      subst t
      have harg : (⟨2*(r 0).val, by dsimp [r]; norm_num⟩ : unitInterval) = 1 := by
        apply Subtype.ext
        dsimp [r]
        norm_num
      rw [harg,γ.target,η.source]
    · congr 1
      apply Subtype.ext
      dsimp [r]
      ring
  refine ⟨θ.comp l,θ.comp r,?_,?_,?_⟩
  · intro t
    simpa only [ContinuousMap.comp_apply,hl] using hθ (l t)
  · intro t
    simpa only [ContinuousMap.comp_apply,hr] using hθ (r t)
  · have hl0 : l 0 = 0 := by apply Subtype.ext; dsimp [l]; norm_num
    have hr1 : r 1 = 1 := by apply Subtype.ext; dsimp [r]; norm_num
    have hlr : l 1 = r 0 := by apply Subtype.ext; dsimp [l,r]; norm_num
    simp only [ContinuousMap.comp_apply,hl0,hr1,hlr]
    ring

end DirectGLSSW.HOMFLY.PrincipalTurning

