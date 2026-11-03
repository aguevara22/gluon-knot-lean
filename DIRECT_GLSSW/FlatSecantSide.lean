import ShortSecantCone
import ActualRectangleBoundaryChain

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Chords in one literal affine source arc differ by a positive real factor. -/
theorem basedUniformSecant_same_arc_ratio_arg_zero {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (k : ℤ) (s t s' t' : ℝ)
    (hs : s ∈ Set.Icc ((k : ℝ)-1/2) ((k : ℝ)+1/2))
    (ht : t ∈ Set.Icc ((k : ℝ)-1/2) ((k : ℝ)+1/2))
    (hs' : s' ∈ Set.Icc ((k : ℝ)-1/2) ((k : ℝ)+1/2))
    (ht' : t' ∈ Set.Icc ((k : ℝ)-1/2) ((k : ℝ)+1/2))
    (hst : s<t) (hst' : s'<t') :
    Complex.arg (basedUniformSecant T C s' t'/basedUniformSecant T C s t)=0 := by
  rw [basedUniformSecant_same_arc_cell T C k s t hs ht,
    basedUniformSecant_same_arc_cell T C k s' t' hs' ht',
    mul_div_mul_right _ _ (arcVector_ne_zero D _),←Complex.ofReal_div]
  exact Complex.arg_ofReal_of_nonneg (div_nonneg (sub_pos.mpr hst').le (sub_pos.mpr hst).le)

/-- Actual retained-side increments vanish when their two endpoint chords
lie in the same original affine arc cell. -/
theorem rectangleSideIncrement_zero_of_arc_cell {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C) (k : ℤ)
    (hss : (rectangleSideStart e).1 ∈ Set.Icc ((k : ℝ)-1/2) ((k : ℝ)+1/2))
    (hst : (rectangleSideStart e).2 ∈ Set.Icc ((k : ℝ)-1/2) ((k : ℝ)+1/2))
    (hfs : (rectangleSideFinish e).1 ∈ Set.Icc ((k : ℝ)-1/2) ((k : ℝ)+1/2))
    (hft : (rectangleSideFinish e).2 ∈ Set.Icc ((k : ℝ)-1/2) ((k : ℝ)+1/2)) :
    rectangleSideIncrement e=0 := by
  classical
  have hc := retainedRectangle_axis_cells e.1
  have horder := (Finset.mem_filter.mp e.1.property).2.1
  have hs : (rectangleSideStart e).1 < (rectangleSideStart e).2 := by
    rcases e with ⟨r,s⟩
    fin_cases s <;> simp [rectangleSideStart] <;> linarith [hc.1.2.2.1,hc.2.2.2.1]
  have hf : (rectangleSideFinish e).1 < (rectangleSideFinish e).2 := by
    rcases e with ⟨r,s⟩
    fin_cases s <;> simp [rectangleSideFinish] <;> linarith [hc.1.2.2.1,hc.2.2.2.1]
  exact basedUniformSecant_same_arc_ratio_arg_zero T C k _ _ _ _ hss hst hfs hft hs hf

end DirectGLSSW.HOMFLY.PrincipalTurning


