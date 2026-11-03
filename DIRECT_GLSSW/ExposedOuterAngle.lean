import ExposedRootChords

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

theorem actualRootChord_axis_zeroFree {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b : ℝ) (hc : secantAxisAdjacent T C a b)
    (ha : 0<a) (hb : b<(componentArcLength D (T.baseArc C).val : ℝ)) :
    ∀ r ∈ Set.Icc (0 : ℝ) 1,
      ((1-r : ℝ) : ℂ)*(basedUniformSecant T C 0 a/arcVector D (T.baseArc C).val)+
      (r : ℂ)*(basedUniformSecant T C 0 b/arcVector D (T.baseArc C).val)≠0 := by
  intro r hr
  rw [←actualRootChord_axis_affine T C a b r hc hr]
  have hab := hc.2.2.1.le
  have ht := weighted_three_mem_interval a b a b a (1-r) r 0
    ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ ⟨le_rfl,hab⟩ (by linarith [hr.2]) hr.1 le_rfl (by ring)
  simp only [zero_mul,add_zero] at ht
  exact div_ne_zero (actualRootChord_ne_zero T C _ ⟨lt_of_lt_of_le ha ht.1,
    lt_of_le_of_lt ht.2 hb⟩) (arcVector_ne_zero D _)

theorem actualRootChord_axis_ratio_arg {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (hhalf : actualRootVertexHalfplane T C)
    (a b : ℝ) (hc : secantAxisAdjacent T C a b)
    (ha : 0<a) (hb : b<(componentArcLength D (T.baseArc C).val : ℝ)) :
    Complex.arg (basedUniformSecant T C 0 a/basedUniformSecant T C 0 b) =
      actualRootChordAngle T C a-actualRootChordAngle T C b := by
  have hseg := actualRootChord_axis_zeroFree T C a b hc ha hb
  have hseg' : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      ((1-r : ℝ) : ℂ)*(basedUniformSecant T C 0 b/arcVector D (T.baseArc C).val)+
      (r : ℂ)*(basedUniformSecant T C 0 a/arcVector D (T.baseArc C).val)≠0 := by
    intro r hr
    have h := hseg (1-r) ⟨by linarith [hr.2],by linarith [hr.1]⟩
    simpa only [sub_sub_cancel,add_comm] using h
  have h := upperHalfPlane_chord_ratio_arg
    (basedUniformSecant T C 0 b/arcVector D (T.baseArc C).val)
    (basedUniformSecant T C 0 a/arcVector D (T.baseArc C).val)
    (actualRootVertexHalfplane_relative_im T C hhalf b)
    (actualRootVertexHalfplane_relative_im T C hhalf a) hseg'
  have he : (basedUniformSecant T C 0 a/arcVector D (T.baseArc C).val)/
      (basedUniformSecant T C 0 b/arcVector D (T.baseArc C).val) =
      basedUniformSecant T C 0 a/basedUniformSecant T C 0 b := by
    exact div_div_div_cancel_right₀ (arcVector_ne_zero D _) _ _
  rw [he] at h
  exact h

theorem actualOuterTop_exposed_sum {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (hhalf : actualRootVertexHalfplane T C) :
    (∑ ab : ↥(actualOuterTopCells T C), Complex.arg
      (basedUniformSecant T C 0 ab.val.1/basedUniformSecant T C 0 ab.val.2)) = -Real.pi := by
  rw [←actualOuterTop_potential_sum T C]
  apply Finset.sum_congr rfl
  intro ab _
  have hm := Finset.mem_filter.mp ab.property
  have hc := (Finset.mem_filter.mp hm.1).2
  have hw := secantAxisAdjacent_width T C _ _ hc
  exact actualRootChord_axis_ratio_arg T C hhalf _ _ hc
    (by linarith [hm.2.1]) (by linarith [hm.2.2])

theorem actualOuterLeft_exposed_sum {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (hhalf : actualRootVertexHalfplane T C) :
    (∑ ab : ↥(actualOuterLeftCells T C), Complex.arg
      (basedUniformSecant T C 0 ab.val.1/basedUniformSecant T C 0 ab.val.2)) = -Real.pi := by
  rw [←actualOuterLeft_potential_sum T C]
  apply Finset.sum_congr rfl
  intro ab _
  have hm := Finset.mem_filter.mp ab.property
  have hc := (Finset.mem_filter.mp hm.1).2
  have hw := secantAxisAdjacent_width T C _ _ hc
  exact actualRootChord_axis_ratio_arg T C hhalf _ _ hc
    (by linarith [hm.2.1]) (by linarith [hm.2.2])

end
end DirectGLSSW.HOMFLY.PrincipalTurning




