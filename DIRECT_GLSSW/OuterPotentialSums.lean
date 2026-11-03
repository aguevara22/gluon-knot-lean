import RootHalfArcChords
import OuterBoundaryRegrouping
import ActualAxisPotentialSum

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Principal chord-angle potential. Its differences are not identified
with actual side increments until the supporting half-plane is proved. -/
def actualRootChordAngle {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (t : ℝ) : ℝ :=
  Complex.arg (basedUniformSecant T C 0 t/arcVector D (T.baseArc C).val)

theorem actualRootChordAngle_interval_sum {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    (∑ ab ∈ (secantAxisCells T C).filter (fun ab => (1/4 : ℝ)≤ab.1 ∧
      ab.2≤(componentArcLength D (T.baseArc C).val : ℝ)-1/4),
      (actualRootChordAngle T C ab.1-actualRootChordAngle T C ab.2)) = -Real.pi := by
  have hm : (1 : ℝ)≤(componentArcLength D (T.baseArc C).val : ℝ) := by
    exact_mod_cast basedComponent_period_positive T C
  have hL := (secantAxisAdjacent_first T C).2.1
  have hR := (secantAxisAdjacent_last T C).1
  have h := actualAxis_interval_potential_sum T C (1/4)
    ((componentArcLength D (T.baseArc C).val : ℝ)-1/4) hL hR (by linarith)
    (actualRootChordAngle T C)
  have h0 : actualRootChordAngle T C (1/4)=0 :=
    basedUniformSecant_initial_relative_arg T C _ ⟨by norm_num,by norm_num⟩
  have hpi : actualRootChordAngle T C ((componentArcLength D (T.baseArc C).val : ℝ)-1/4)=Real.pi :=
    basedUniformSecant_return_relative_arg T C _ ⟨by linarith,by linarith⟩
  rw [h0,hpi,sub_zero,Finset.sum_sub_distrib] at h
  rw [Finset.sum_sub_distrib]
  linarith

/-- Pure potential telescope on the literal top cell set. This does not
yet evaluate the actual outer side increments in an arbitrary traversal. -/
theorem actualOuterTop_potential_sum {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    (∑ ab : ↥(actualOuterTopCells T C),
      (actualRootChordAngle T C ab.val.1-actualRootChordAngle T C ab.val.2)) = -Real.pi := by
  let E := (secantAxisCells T C).filter (fun ab => (1/4 : ℝ)≤ab.1 ∧
    ab.2≤(componentArcLength D (T.baseArc C).val : ℝ)-1/4)
  have hL := (secantAxisAdjacent_first T C).2.1
  have hsub : actualOuterTopCells T C ⊆ E := by
    intro ab hab
    have hm := Finset.mem_filter.mp hab
    have hc := (Finset.mem_filter.mp hm.1).2
    have ha : 1/4≤ab.1 := by
      by_contra hn
      exact hc.2.2.2 _ hL (lt_of_not_ge hn) hm.2.1
    exact Finset.mem_filter.mpr ⟨hm.1,ha,hm.2.2.le⟩
  have hz : ∀ ab ∈ E, ab ∉ actualOuterTopCells T C →
      actualRootChordAngle T C ab.1-actualRootChordAngle T C ab.2=0 := by
    intro ab hab hn
    have hm := (Finset.mem_filter.mp hab).2
    have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hab).1).2
    have hwidth := secantAxisAdjacent_width T C _ _ hc
    have hb : ab.2=(componentArcLength D (T.baseArc C).val : ℝ)-1/4 := by
      apply le_antisymm hm.2
      by_contra hnot
      apply hn
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hab).1,
        by linarith [hc.2.2.1],lt_of_not_ge hnot⟩
    have haarg : actualRootChordAngle T C ab.1=Real.pi := by
      apply basedUniformSecant_return_relative_arg T C
      constructor <;> linarith [hc.2.2.1]
    have hbarg : actualRootChordAngle T C ab.2=Real.pi := by
      apply basedUniformSecant_return_relative_arg T C
      constructor <;> linarith
    rw [haarg,hbarg,sub_self]
  rw [Finset.sum_coe_sort (actualOuterTopCells T C)
    (fun ab : ℝ × ℝ => actualRootChordAngle T C ab.1-actualRootChordAngle T C ab.2)]
  exact (Finset.sum_subset hsub hz).trans (actualRootChordAngle_interval_sum T C)

/-- Pure potential telescope on the literal left cell set. Actual exposed
outer evaluation still requires the source supporting geometry. -/
theorem actualOuterLeft_potential_sum {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    (∑ ab : ↥(actualOuterLeftCells T C),
      (actualRootChordAngle T C ab.val.1-actualRootChordAngle T C ab.val.2)) = -Real.pi := by
  let E := (secantAxisCells T C).filter (fun ab => (1/4 : ℝ)≤ab.1 ∧
    ab.2≤(componentArcLength D (T.baseArc C).val : ℝ)-1/4)
  have hR := (secantAxisAdjacent_last T C).1
  have hsub : actualOuterLeftCells T C ⊆ E := by
    intro ab hab
    have hm := Finset.mem_filter.mp hab
    have hc := (Finset.mem_filter.mp hm.1).2
    have hb : ab.2≤(componentArcLength D (T.baseArc C).val : ℝ)-1/4 := by
      by_contra hn
      exact hc.2.2.2 _ hR hm.2.2 (lt_of_not_ge hn)
    exact Finset.mem_filter.mpr ⟨hm.1,hm.2.1.le,hb⟩
  have hz : ∀ ab ∈ E, ab ∉ actualOuterLeftCells T C →
      actualRootChordAngle T C ab.1-actualRootChordAngle T C ab.2=0 := by
    intro ab hab hn
    have hm := (Finset.mem_filter.mp hab).2
    have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hab).1).2
    have hwidth := secantAxisAdjacent_width T C _ _ hc
    have ha : ab.1=1/4 := by
      apply le_antisymm ?_ hm.1
      by_contra hnot
      apply hn
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hab).1,
        lt_of_not_ge hnot,by linarith [hc.2.2.1]⟩
    have haarg : actualRootChordAngle T C ab.1=0 := by
      apply basedUniformSecant_initial_relative_arg T C
      constructor <;> linarith
    have hbarg : actualRootChordAngle T C ab.2=0 := by
      apply basedUniformSecant_initial_relative_arg T C
      constructor <;> linarith [hc.2.2.1]
    rw [haarg,hbarg,sub_self]
  rw [Finset.sum_coe_sort (actualOuterLeftCells T C)
    (fun ab : ℝ × ℝ => actualRootChordAngle T C ab.1-actualRootChordAngle T C ab.2)]
  exact (Finset.sum_subset hsub hz).trans (actualRootChordAngle_interval_sum T C)

end
end DirectGLSSW.HOMFLY.PrincipalTurning



