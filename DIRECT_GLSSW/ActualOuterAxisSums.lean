import ActualAxisNonbaseSum
import OuterBoundaryRegrouping
import OuterAxisEndpoints

set_option autoImplicit false
noncomputable section
open DirectGLSSW
attribute [local instance] Classical.propDecidable

namespace DirectGLSSW.HOMFLY.PLWinding

/-- The literal top exterior cell sum agrees with the full interior
secant-axis sum; its one omitted returning-base cell has zero increment. -/
theorem actualOuterTop_arg_sum_eq_axisInterior {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    (∑ ab : ↥(PrincipalTurning.actualOuterTopCells T C),
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.val.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.val.2)) =
    ∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
      (fun ab => (1/4 : ℝ) ≤ ab.1 ∧
        ab.2 ≤ (componentArcLength D (T.baseArc C).val : ℝ)-1/4),
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.2) := by
  let E := (PrincipalTurning.secantAxisCells T C).filter
    (fun ab => (1/4 : ℝ) ≤ ab.1 ∧
      ab.2 ≤ (componentArcLength D (T.baseArc C).val : ℝ)-1/4)
  have hL := (PrincipalTurning.secantAxisAdjacent_first T C).2.1
  have hsub : PrincipalTurning.actualOuterTopCells T C ⊆ E := by
    intro ab hab
    have hm := Finset.mem_filter.mp hab
    have hc := (Finset.mem_filter.mp hm.1).2
    have ha : 1/4 ≤ ab.1 := by
      by_contra hn
      exact hc.2.2.2 _ hL (lt_of_not_ge hn) hm.2.1
    exact Finset.mem_filter.mpr ⟨hm.1,ha,hm.2.2.le⟩
  have hz : ∀ ab ∈ E, ab ∉ PrincipalTurning.actualOuterTopCells T C →
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.2) = 0 := by
    intro ab hab hn
    have hm := (Finset.mem_filter.mp hab).2
    have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hab).1).2
    have hwidth := PrincipalTurning.secantAxisAdjacent_width T C _ _ hc
    have hb : ab.2 = (componentArcLength D (T.baseArc C).val : ℝ)-1/4 := by
      apply le_antisymm hm.2
      by_contra hnot
      apply hn
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hab).1,
        by linarith [hc.2.2.1],lt_of_not_ge hnot⟩
    exact return_base_secant_cell_arg_zero T C ab.1 ab.2
      (by linarith [hwidth,hb]) hc.2.2.1.le (by linarith [hb])
  rw [Finset.sum_coe_sort (PrincipalTurning.actualOuterTopCells T C)
    (fun ab : ℝ × ℝ => Complex.arg
      (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.2))]
  exact Finset.sum_subset hsub hz

/-- The literal left exterior cell sum also agrees with the full
interior axis sum; its omitted initial-base cell has zero increment. -/
theorem actualOuterLeft_arg_sum_eq_axisInterior {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    (∑ ab : ↥(PrincipalTurning.actualOuterLeftCells T C),
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.val.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.val.2)) =
    ∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
      (fun ab => (1/4 : ℝ) ≤ ab.1 ∧
        ab.2 ≤ (componentArcLength D (T.baseArc C).val : ℝ)-1/4),
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.2) := by
  let E := (PrincipalTurning.secantAxisCells T C).filter
    (fun ab => (1/4 : ℝ) ≤ ab.1 ∧
      ab.2 ≤ (componentArcLength D (T.baseArc C).val : ℝ)-1/4)
  have hR := (PrincipalTurning.secantAxisAdjacent_last T C).1
  have hsub : PrincipalTurning.actualOuterLeftCells T C ⊆ E := by
    intro ab hab
    have hm := Finset.mem_filter.mp hab
    have hc := (Finset.mem_filter.mp hm.1).2
    have hb : ab.2 ≤ (componentArcLength D (T.baseArc C).val : ℝ)-1/4 := by
      by_contra hn
      exact hc.2.2.2 _ hR hm.2.2 (lt_of_not_ge hn)
    exact Finset.mem_filter.mpr ⟨hm.1,hm.2.1.le,hb⟩
  have hz : ∀ ab ∈ E, ab ∉ PrincipalTurning.actualOuterLeftCells T C →
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.2) = 0 := by
    intro ab hab hn
    have hm := (Finset.mem_filter.mp hab).2
    have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hab).1).2
    have hwidth := PrincipalTurning.secantAxisAdjacent_width T C _ _ hc
    have ha : ab.1 = 1/4 := by
      apply le_antisymm ?_ hm.1
      by_contra hnot
      apply hn
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hab).1,
        lt_of_not_ge hnot,by linarith [hc.2.2.1]⟩
    exact initial_base_secant_cell_arg_zero T C ab.1 ab.2
      (by linarith [ha]) hc.2.2.1.le (by linarith [hwidth,ha])
  rw [Finset.sum_coe_sort (PrincipalTurning.actualOuterLeftCells T C)
    (fun ab : ℝ × ℝ => Complex.arg
      (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.2))]
  exact Finset.sum_subset hsub hz

end DirectGLSSW.HOMFLY.PLWinding
