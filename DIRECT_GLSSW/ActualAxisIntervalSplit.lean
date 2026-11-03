import ActualAxisEndpointCuts

set_option autoImplicit false
noncomputable section
open DirectGLSSW
attribute [local instance] Classical.propDecidable

namespace DirectGLSSW.HOMFLY.PLWinding

/-- An actual cut splits an axis interval into two disjoint sets of
adjacent cells. This is a finite combinatorial fact, independent of the
angle summand. -/
theorem actualAxis_interval_sum_split {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D)
    (L M R : ℝ) (hLM : L < M) (hMR : M < R)
    (hM : M ∈ PrincipalTurning.secantAxisCuts T C)
    (f : ℝ × ℝ → ℝ) :
    (∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
      (fun ab => L ≤ ab.1 ∧ ab.2 ≤ R), f ab) =
    (∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
      (fun ab => L ≤ ab.1 ∧ ab.2 ≤ M), f ab) +
    (∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
      (fun ab => M ≤ ab.1 ∧ ab.2 ≤ R), f ab) := by
  let E := PrincipalTurning.secantAxisCells T C
  let EL := E.filter (fun ab => L ≤ ab.1 ∧ ab.2 ≤ M)
  let ER := E.filter (fun ab => M ≤ ab.1 ∧ ab.2 ≤ R)
  have hdisj : Disjoint EL ER := by
    apply Finset.disjoint_left.mpr
    intro ab habL habR
    have hc : PrincipalTurning.secantAxisAdjacent T C ab.1 ab.2 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp habL).1).2
    have hbL := (Finset.mem_filter.mp habL).2.2
    have haR := (Finset.mem_filter.mp habR).2.1
    linarith [hc.2.2.1]
  have hunion : E.filter (fun ab => L ≤ ab.1 ∧ ab.2 ≤ R) = EL ∪ ER := by
    ext ab
    constructor
    · intro hab
      have hE := (Finset.mem_filter.mp hab).1
      have hb := (Finset.mem_filter.mp hab).2
      have hc : PrincipalTurning.secantAxisAdjacent T C ab.1 ab.2 :=
        (Finset.mem_filter.mp hE).2
      by_cases hbefore : ab.2 ≤ M
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hE,hb.1,hbefore⟩)
      · have hafter : M ≤ ab.1 := by
          by_contra hn
          exact hc.2.2.2 M hM (lt_of_not_ge hn) (lt_of_not_ge hbefore)
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hE,hafter,hb.2⟩)
    · intro hab
      rcases Finset.mem_union.mp hab with habL | habR
      · have hh := (Finset.mem_filter.mp habL)
        exact Finset.mem_filter.mpr ⟨hh.1,hh.2.1,le_trans hh.2.2 hMR.le⟩
      · have hh := (Finset.mem_filter.mp habR)
        exact Finset.mem_filter.mpr ⟨hh.1,le_trans hLM.le hh.2.1,hh.2.2⟩
  change (∑ ab ∈ E.filter (fun ab => L ≤ ab.1 ∧ ab.2 ≤ R), f ab) =
    (∑ ab ∈ EL, f ab) + (∑ ab ∈ ER, f ab)
  rw [hunion, Finset.sum_union hdisj]

end DirectGLSSW.HOMFLY.PLWinding
