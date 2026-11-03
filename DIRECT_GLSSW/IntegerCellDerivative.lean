import ContinuousRoundedTangent

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open scoped Topology

/-- Glue actual derivatives across every integer cell. The inputs are local
all-real formulas and matching positions and velocities at each join. -/
theorem integer_cell_hasDerivAt (F V : ℤ → ℝ → ℂ)
    (hderiv : ∀ k t, HasDerivAt (F k) (V k t) t)
    (hF : ∀ k, F (k - 1) 1 = F k 0)
    (hV : ∀ k, V (k - 1) 1 = V k 0)
    (t : ℝ) :
    HasDerivAt (fun x : ℝ => F (Int.floor x) (Int.fract x))
      (V (Int.floor t) (Int.fract t)) t := by
  let g := fun x : ℝ => F (Int.floor x) (Int.fract x)
  have hcell (k : ℤ) (x : ℝ) (hx : x ∈ Set.Ico (k : ℝ) (k + 1)) :
      g x = F k (x - k) := by
    have hf := Int.floor_eq_on_Ico k x hx
    simp only [g, Int.fract, hf]
  have hprev (k : ℤ) (x : ℝ) (hx : x ∈ Set.Ioc ((k : ℝ) - 1) k) :
      g x = F (k - 1) (x - (k - 1 : ℤ)) := by
    rcases lt_or_eq_of_le hx.2 with h | h
    · apply hcell
      simp only [Int.cast_sub, Int.cast_one]
      exact ⟨hx.1.le, by linarith⟩
    · subst x
      simp only [g, Int.floor_intCast, Int.fract_intCast, Int.cast_sub, Int.cast_one]
      rw [show (k : ℝ) - ((k : ℝ) - 1) = 1 by ring, hF]
  have hshift (k : ℤ) (x : ℝ) :
      HasDerivAt (fun y : ℝ => F k (y - (k : ℝ)))
        (V k (x - (k : ℝ))) x := by
    simpa only [one_smul] using
      (hderiv k (x - (k : ℝ))).scomp x
        ((hasDerivAt_id x).sub_const (k : ℝ))
  have hint (k : ℤ) : HasDerivAt g (V k 0) (k : ℝ) := by
    have hl0 := hshift (k - 1) (k : ℝ)
    have hlv : V (k - 1) ((k : ℝ) - (k - 1 : ℤ)) = V k 0 := by
      simp only [Int.cast_sub, Int.cast_one]
      rw [show (k : ℝ) - ((k : ℝ) - 1) = 1 by ring, hV]
    have hl : HasDerivWithinAt g (V k 0)
        (Set.Ioc ((k : ℝ) - 1) k) k := by
      apply (show HasDerivAt (fun x : ℝ => F (k - 1) (x - (k - 1 : ℤ)))
        (V k 0) (k : ℝ) from by simpa only [hlv, one_smul] using hl0).hasDerivWithinAt.congr_of_mem
      · intro x hx
        exact hprev k x hx
      · exact ⟨by linarith, le_rfl⟩
    have hr0 := hshift k (k : ℝ)
    have hr : HasDerivWithinAt g (V k 0) (Set.Ico (k : ℝ) (k + 1)) k := by
      apply (show HasDerivAt (fun x : ℝ => F k (x - k)) (V k 0) (k : ℝ) from by
        simpa only [sub_self, one_smul] using hr0).hasDerivWithinAt.congr_of_mem
      · intro x hx
        exact hcell k x hx
      · exact ⟨le_rfl, by linarith⟩
    apply (hl.union hr).hasDerivAt
    apply Filter.mem_of_superset (Ioo_mem_nhds (show (k : ℝ) - 1 < k by linarith)
      (show (k : ℝ) < k + 1 by linarith))
    intro x hx
    by_cases h : x ≤ (k : ℝ)
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨(not_le.mp h).le, hx.2⟩
  by_cases ht : t = (Int.floor t : ℝ)
  · rw [ht]
    simpa only [g, Int.floor_intCast, Int.fract_intCast] using hint (Int.floor t)
  · have hlo : (Int.floor t : ℝ) < t := (Int.floor_le t).lt_of_ne (Ne.symm ht)
    have hhi : t < (Int.floor t : ℝ) + 1 := Int.lt_floor_add_one t
    have hc := hshift (Int.floor t) t
    have hw : HasDerivWithinAt g (V (Int.floor t) (Int.fract t))
        (Set.Ico (Int.floor t : ℝ) (Int.floor t + 1)) t := by
      apply (show HasDerivAt (fun x : ℝ => F (Int.floor t) (x - Int.floor t))
        (V (Int.floor t) (Int.fract t)) t from by
          simpa only [Int.fract, one_smul] using hc).hasDerivWithinAt.congr_of_mem
      · intro x hx
        exact hcell (Int.floor t) x hx
      · exact ⟨hlo.le, hhi⟩
    exact hw.hasDerivAt (Ico_mem_nhds hlo hhi)

theorem continuous_integer_cell_velocity (V : ℤ → ℝ → ℂ)
    (hcontinuous : ∀ k, Continuous (V k))
    (hV : ∀ k, V (k - 1) 1 = V k 0) :
    Continuous (fun t : ℝ => V (Int.floor t) (Int.fract t)) :=
  continuous_integer_cells V hcontinuous hV

end DirectGLSSW.HOMFLY.PrincipalTurning


