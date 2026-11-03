import ActualAxisInterval

set_option autoImplicit false
noncomputable section
open DirectGLSSW

namespace DirectGLSSW.HOMFLY.PLWinding

/-- The two literal endpoint times of every nonbase actual polygon edge
are members of the source's finite secant-axis cut set. -/
theorem actualWord_nonbase_endpoint_cuts {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D)
    (j : Fin (componentArcLength D (T.baseArc C).val))
    (hj : j ≠ (⟨0, componentArcLength_pos D (T.baseArc C).val⟩ :
      Fin (componentArcLength D (T.baseArc C).val))) :
    (j.val : ℝ) - 1/2 ∈ PrincipalTurning.secantAxisCuts T C ∧
      (j.val : ℝ) + 1/2 ∈ PrincipalTurning.secantAxisCuts T C := by
  have hpos : 0 < j.val := by
    by_contra hn
    have hzero : j.val = 0 := Nat.eq_zero_of_not_pos hn
    exact hj (Fin.ext hzero)
  have hprev : j.val - 1 < componentArcLength D (T.baseArc C).val := by
    omega
  have hL := PrincipalTurning.secantAxisCuts_original_knot T C
    (j.val - 1) hprev
  have htime : (((j.val - 1 : ℕ) : ℝ) + 1/2) = (j.val : ℝ) - 1/2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ j.val)]
    push_cast
    ring
  rw [htime] at hL
  exact ⟨hL, PrincipalTurning.secantAxisCuts_original_knot T C j.val j.isLt⟩

/-- The nonbase edge telescope with its endpoint-cut obligations
discharged from the actual source cut geometry. -/
theorem actualWord_nonbase_axis_interval_sum_actual {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D)
    (j : Fin (componentArcLength D (T.baseArc C).val))
    (hj : j ≠ (⟨0, componentArcLength_pos D (T.baseArc C).val⟩ :
      Fin (componentArcLength D (T.baseArc C).val))) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    let L : ℝ := (j.val : ℝ) - 1/2
    let R : ℝ := (j.val : ℝ) + 1/2
    (∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
      (fun ab => L ≤ ab.1 ∧ ab.2 ≤ R),
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.2)) =
      -Complex.arg ((q (cyclicSuccessorPerm m j) - normalAtEdgeMidpoint q i₀ 0) /
        (q j - normalAtEdgeMidpoint q i₀ 0)) := by
  exact actualWord_nonbase_axis_interval_sum T C j hj
    (actualWord_nonbase_endpoint_cuts T C j hj).1
    (actualWord_nonbase_endpoint_cuts T C j hj).2

end DirectGLSSW.HOMFLY.PLWinding
