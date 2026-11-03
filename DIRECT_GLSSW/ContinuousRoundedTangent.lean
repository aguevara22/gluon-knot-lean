import RoundedComponentRegularity
import Mathlib.Topology.Piecewise

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open scoped Topology

/-- Gluing continuous unit cells with their actual matching endpoints. -/
theorem continuous_integer_cells {Y : Type*} [TopologicalSpace Y]
    (f : ℤ → ℝ → Y) (hf : ∀ k, Continuous (f k))
    (hj : ∀ k, f (k - 1) 1 = f k 0) :
    Continuous (fun t : ℝ => f (Int.floor t) (Int.fract t)) := by
  let g := fun t : ℝ => f (Int.floor t) (Int.fract t)
  have hcell (k : ℤ) (t : ℝ) (ht : t ∈ Set.Ico (k : ℝ) (k + 1)) :
      g t = f k (t - k) := by
    have h := Int.floor_eq_on_Ico k t ht
    simp only [g, Int.fract, h]
  have hprev (k : ℤ) (t : ℝ) (ht : t ∈ Set.Ioc ((k : ℝ) - 1) k) :
      g t = f (k - 1) (t - (k - 1 : ℤ)) := by
    rcases lt_or_eq_of_le ht.2 with h | h
    · apply hcell
      simp only [Int.cast_sub, Int.cast_one]
      exact ⟨ht.1.le,by linarith⟩
    · subst t
      simp only [g, Int.floor_intCast, Int.fract_intCast, Int.cast_sub, Int.cast_one]
      rw [show (k : ℝ) - ((k : ℝ) - 1) = 1 by ring, hj]
  have hi (k : ℤ) : ContinuousAt g (k : ℝ) := by
    have hl : ContinuousWithinAt g (Set.Ioc ((k : ℝ) - 1) k) k := by
      apply ((hf (k - 1)).comp (continuous_id.sub continuous_const)).continuousAt.continuousWithinAt.congr_of_mem
      · intro t ht
        exact hprev k t ht
      · exact ⟨by linarith,le_rfl⟩
    have hr : ContinuousWithinAt g (Set.Ico (k : ℝ) (k + 1)) k := by
      apply ((hf k).comp (continuous_id.sub continuous_const)).continuousAt.continuousWithinAt.congr_of_mem
      · intro t ht
        exact hcell k t ht
      · exact ⟨le_rfl,by linarith⟩
    apply (hl.union hr).continuousAt
    apply Filter.mem_of_superset (Ioo_mem_nhds (show (k : ℝ) - 1 < k by linarith)
      (show (k : ℝ) < k + 1 by linarith))
    intro t ht
    by_cases h : t ≤ (k : ℝ)
    · exact Or.inl ⟨ht.1,h⟩
    · exact Or.inr ⟨(not_le.mp h).le,ht.2⟩
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases h : t = (Int.floor t : ℝ)
  · rw [h]
    exact hi (Int.floor t)
  · have hlo : (Int.floor t : ℝ) < t := (Int.floor_le t).lt_of_ne (Ne.symm h)
    have hhi : t < (Int.floor t : ℝ) + 1 := Int.lt_floor_add_one t
    have hw : ContinuousWithinAt g (Set.Ico (Int.floor t : ℝ) (Int.floor t + 1)) t := by
      apply ((hf (Int.floor t)).comp (continuous_id.sub continuous_const)).continuousAt.continuousWithinAt.congr_of_mem
      · intro x hx
        exact hcell (Int.floor t) x hx
      · exact ⟨hlo.le,hhi⟩
    exact hw.continuousAt (Ico_mem_nhds hlo hhi)

theorem roundedStepVelocity_continuous (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) : Continuous (roundedStepVelocity D e δ) := by
  unfold roundedStepVelocity
  apply Continuous.if
  · intro t ht
    have heq : t = 1 := frontier_Iic_subset 1 ht
    subst t
    exact roundedStep_join_derivative D e δ
  · unfold roundedCornerDerivative cornerTangent
    fun_prop
  · exact continuous_const

theorem normalizedRoundedVelocity_continuous (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) : Continuous (normalizedRoundedVelocity D e δ) := by
  unfold normalizedRoundedVelocity
  exact ((roundedStepVelocity_continuous D e δ).comp
    (continuous_id.div_const (2 * δ.val))).const_smul (1 / (2 * δ.val))

theorem roundedComponentVelocity_continuous (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) : Continuous (roundedComponentVelocity D e δ) := by
  apply continuous_integer_cells (fun k => normalizedRoundedVelocity D ((D.continuation ^ k) e) δ)
  · intro k
    exact normalizedRoundedVelocity_continuous D _ δ
  · intro k
    rw [(normalizedRoundedVelocity_endpoints D _ δ).2,
      continuation_previous_integer, (normalizedRoundedVelocity_endpoints D _ δ).1]

end DirectGLSSW.HOMFLY.PrincipalTurning




