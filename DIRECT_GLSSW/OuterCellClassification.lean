import OuterAxisEndpoints

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

theorem secantAxisAdjacent_first {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) : secantAxisAdjacent T C 0 (1/4) := by
  have hm : (0 : ℝ)<(componentArcLength D (T.baseArc C).val : ℝ) := by
    exact_mod_cast basedComponent_period_positive T C
  obtain ⟨b,hb⟩ := secantAxis_successor_exists T C 0 (secantAxisCuts_zero T C) hm
  have he := secantAxisAdjacent_initial_endpoint T C b hb
  simpa only [he] using hb

theorem secantAxisAdjacent_last {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    secantAxisAdjacent T C ((componentArcLength D (T.baseArc C).val : ℝ)-1/4)
      (componentArcLength D (T.baseArc C).val : ℝ) := by
  have hm : (0 : ℝ)<(componentArcLength D (T.baseArc C).val : ℝ) := by
    exact_mod_cast basedComponent_period_positive T C
  obtain ⟨a,ha⟩ := secantAxis_predecessor_exists T C _ (secantAxisCuts_period T C) hm
  have he := secantAxisAdjacent_final_endpoint T C a ha
  simpa only [he] using ha

/-- Exact retained top-row cells, including all source removal tests. -/
theorem secantRetainedRectangles_top_row {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b : ℝ) :
    ((a,b),((componentArcLength D (T.baseArc C).val : ℝ)-1/4,
      (componentArcLength D (T.baseArc C).val : ℝ))) ∈ secantRetainedRectangles T C ↔
    secantAxisAdjacent T C a b ∧ 1/4<b ∧
      b<(componentArcLength D (T.baseArc C).val : ℝ)-1/4 := by
  constructor
  · intro hr
    have h := (Finset.mem_filter.mp hr).2
    have hx := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hr).1).1).2
    refine ⟨hx,?_,h.1⟩
    by_contra hn
    exact h.2.1 ⟨le_of_not_gt hn,le_rfl⟩
  · rintro ⟨hx,hb,ho⟩
    have hy := secantAxisAdjacent_last T C
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,ho,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx.1,hx.2.1⟩,hx⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy.1,hy.2.1⟩,hy⟩
    · rintro ⟨hbad,_⟩
      linarith
    · intro hstar
      have hmargin := secantStarCell_quarter_margin T C _ _ _ _ hstar
      linarith

/-- Exact retained left-column cells, including all source removal tests. -/
theorem secantRetainedRectangles_left_column {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (u v : ℝ) :
    ((0,1/4),(u,v)) ∈ secantRetainedRectangles T C ↔
    secantAxisAdjacent T C u v ∧ 1/4<u ∧
      u<(componentArcLength D (T.baseArc C).val : ℝ)-1/4 := by
  constructor
  · intro hr
    have h := (Finset.mem_filter.mp hr).2
    have hy := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hr).1).2).2
    refine ⟨hy,h.1,?_⟩
    by_contra hn
    exact h.2.1 ⟨le_rfl,le_of_not_gt hn⟩
  · rintro ⟨hy,hu,ho⟩
    have hx := secantAxisAdjacent_first T C
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hu,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx.1,hx.2.1⟩,hx⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy.1,hy.2.1⟩,hy⟩
    · rintro ⟨_,hbad⟩
      linarith
    · intro hstar
      have hmargin := secantStarCell_quarter_margin T C _ _ _ _ hstar
      linarith

end
end DirectGLSSW.HOMFLY.PrincipalTurning




