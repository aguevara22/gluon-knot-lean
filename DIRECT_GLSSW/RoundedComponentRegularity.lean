import GlobalRoundedCurve
import Mathlib.Topology.Algebra.Order.Floor

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open scoped Topology

noncomputable def roundedComponentVelocity (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) : ℂ :=
  normalizedRoundedVelocity D ((D.continuation ^ Int.floor t) e) δ (Int.fract t)

noncomputable def roundedIntegerCell (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (k : ℤ) (t : ℝ) : ℂ :=
  normalizedRoundedCell D ((D.continuation ^ k) e) δ (t - k)

theorem roundedComponentCurve_on_cell (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (k : ℤ) (t : ℝ)
    (ht : t ∈ Set.Ico (k : ℝ) ((k : ℝ) + 1)) :
    roundedComponentCurve D e δ t = roundedIntegerCell D e δ k t := by
  have hf := Int.floor_eq_on_Ico k t ht
  simp only [roundedComponentCurve, roundedIntegerCell, Int.fract, hf]

theorem roundedComponentCurve_int (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (k : ℤ) :
    roundedComponentCurve D e δ k = normalizedRoundedCell D ((D.continuation ^ k) e) δ 0 := by
  simp [roundedComponentCurve]

theorem continuation_previous_integer (D : PLLinkDiagram) (e : Fin D.nArc) (k : ℤ) :
    D.continuation ((D.continuation ^ (k - 1)) e) = (D.continuation ^ k) e := by
  have he : 1 + (k - 1) = k := by omega
  calc
    D.continuation ((D.continuation ^ (k - 1)) e) =
        ((D.continuation ^ (1 : ℤ)) * (D.continuation ^ (k - 1))) e := by
          simp only [zpow_one, Equiv.Perm.mul_apply]
    _ = (D.continuation ^ k) e := by rw [← zpow_add, he]

theorem roundedComponentCurve_on_previous_cell (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (k : ℤ) (t : ℝ)
    (ht : t ∈ Set.Ioc ((k : ℝ) - 1) (k : ℝ)) :
    roundedComponentCurve D e δ t = roundedIntegerCell D e δ (k - 1) t := by
  rcases lt_or_eq_of_le ht.2 with h | h
  · apply roundedComponentCurve_on_cell
    simp only [Int.cast_sub, Int.cast_one]
    exact ⟨ht.1.le, by linarith⟩
  · subst t
    rw [roundedComponentCurve_int]
    simp only [roundedIntegerCell, Int.cast_sub, Int.cast_one]
    rw [show (k : ℝ) - ((k : ℝ) - 1) = 1 by ring,
      normalizedRoundedCell_join, continuation_previous_integer]

theorem roundedIntegerCell_hasDerivAt (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (k : ℤ) (t : ℝ) :
    HasDerivAt (roundedIntegerCell D e δ k)
      (normalizedRoundedVelocity D ((D.continuation ^ k) e) δ (t - k)) t := by
  simpa only [roundedIntegerCell, one_smul] using
    (normalizedRoundedCell_hasDerivAt D ((D.continuation ^ k) e) δ (t - k)).scomp t
      ((hasDerivAt_id t).sub_const (k : ℝ))

theorem roundedComponentCurve_hasDerivAt_int (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (k : ℤ) :
    HasDerivAt (roundedComponentCurve D e δ) (arcVector D ((D.continuation ^ k) e)) k := by
  have hl0 := roundedIntegerCell_hasDerivAt D e δ (k - 1) (k : ℝ)
  have hr0 := roundedIntegerCell_hasDerivAt D e δ k (k : ℝ)
  have hlv : normalizedRoundedVelocity D ((D.continuation ^ (k - 1)) e) δ
      ((k : ℝ) - (k - 1 : ℤ)) = arcVector D ((D.continuation ^ k) e) := by
    simp only [Int.cast_sub, Int.cast_one]
    rw [show (k : ℝ) - ((k : ℝ) - 1) = 1 by ring,
      (normalizedRoundedVelocity_endpoints D _ δ).2, continuation_previous_integer]
  have hrv : normalizedRoundedVelocity D ((D.continuation ^ k) e) δ
      ((k : ℝ) - k) = arcVector D ((D.continuation ^ k) e) := by
    rw [sub_self, (normalizedRoundedVelocity_endpoints D _ δ).1]
  rw [hlv] at hl0
  rw [hrv] at hr0
  have hl : HasDerivWithinAt (roundedComponentCurve D e δ)
      (arcVector D ((D.continuation ^ k) e)) (Set.Ioc ((k : ℝ) - 1) k) k := by
    apply hl0.hasDerivWithinAt.congr_of_mem
    · intro t ht
      exact roundedComponentCurve_on_previous_cell D e δ k t ht
    · exact ⟨by linarith, le_rfl⟩
  have hr : HasDerivWithinAt (roundedComponentCurve D e δ)
      (arcVector D ((D.continuation ^ k) e)) (Set.Ico (k : ℝ) (k + 1)) k := by
    apply hr0.hasDerivWithinAt.congr_of_mem
    · intro t ht
      exact roundedComponentCurve_on_cell D e δ k t ht
    · exact ⟨le_rfl, by linarith⟩
  apply (hl.union hr).hasDerivAt
  apply Filter.mem_of_superset (Ioo_mem_nhds (show (k : ℝ) - 1 < k by linarith)
    (show (k : ℝ) < k + 1 by linarith))
  intro t ht
  by_cases h : t ≤ (k : ℝ)
  · exact Or.inl ⟨ht.1,h⟩
  · exact Or.inr ⟨(not_le.mp h).le,ht.2⟩

theorem roundedComponentCurve_hasDerivAt (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) :
    HasDerivAt (roundedComponentCurve D e δ) (roundedComponentVelocity D e δ t) t := by
  by_cases h : t = (Int.floor t : ℝ)
  · rw [h]
    simpa [roundedComponentVelocity, (normalizedRoundedVelocity_endpoints D _ δ).1] using
      roundedComponentCurve_hasDerivAt_int D e δ (Int.floor t)
  · have hlo : (Int.floor t : ℝ) < t := (Int.floor_le t).lt_of_ne (Ne.symm h)
    have hhi : t < (Int.floor t : ℝ) + 1 := Int.lt_floor_add_one t
    have hc := roundedIntegerCell_hasDerivAt D e δ (Int.floor t) t
    have hw : HasDerivWithinAt (roundedComponentCurve D e δ)
        (normalizedRoundedVelocity D ((D.continuation ^ Int.floor t) e) δ
          (t - Int.floor t)) (Set.Ico (Int.floor t : ℝ) (Int.floor t + 1)) t := by
      apply hc.hasDerivWithinAt.congr_of_mem
      · intro x hx
        exact roundedComponentCurve_on_cell D e δ (Int.floor t) x hx
      · exact ⟨hlo.le,hhi⟩
    simpa only [roundedComponentVelocity, Int.fract] using
      hw.hasDerivAt (Ico_mem_nhds hlo hhi)

theorem roundedComponentVelocity_ne_zero (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) : roundedComponentVelocity D e δ t ≠ 0 :=
  normalizedRoundedVelocity_ne_zero D _ δ _ ⟨Int.fract_nonneg t,(Int.fract_lt_one t).le⟩

theorem roundedComponentCurve_continuous (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) : Continuous (roundedComponentCurve D e δ) :=
  continuous_iff_continuousAt.mpr (fun t => (roundedComponentCurve_hasDerivAt D e δ t).continuousAt)

end DirectGLSSW.HOMFLY.PrincipalTurning




