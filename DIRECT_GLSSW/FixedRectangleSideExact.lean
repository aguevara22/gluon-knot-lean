import FixedRectangleSideClassification

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

theorem rectangleSide_exterior_or_removed_implies_fixed {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) (e : RetainedRectangleSide T C)
    (h : rectangleExteriorSide e ∨ rectangleRemovedNeighbour e) : rectangleSideReverse e=e := by
  apply (rectangleSide_fixed_iff_missing_retainedNeighbour e).mpr
  intro hn
  have hc := retainedRectangle_axis_cells e.1
  rcases e with ⟨r,k⟩
  fin_cases k
  · simp [rectangleExteriorSide,rectangleRemovedNeighbour] at h
    simp only [rectangleHasRetainedNeighbour,if_pos rfl] at hn
    obtain ⟨l,hl,hr⟩ := h
    obtain ⟨l',hh⟩ := hn
    have hq := retainedRectangle_axis_cells
      (⟨((r.val.1.1,r.val.1.2),(l',r.val.2.1)),hh⟩ : RetainedRectangleIndex T C)
    have he : l=l' := secantAxisAdjacent_right_unique T C _ _ _ hl hq.2
    have hnot := (secantCellPair_not_retained_iff T C _ _ _ _ hc.1 hl).mpr hr
    rw [he] at hnot
    exact hnot hh
  · simp [rectangleExteriorSide,rectangleRemovedNeighbour] at h
    simp only [rectangleHasRetainedNeighbour,show (1 : Fin 4) ≠ 0 by decide,if_false,if_pos rfl] at hn
    obtain ⟨w,hw,hr⟩ := h
    obtain ⟨w',hh⟩ := hn
    have hq := retainedRectangle_axis_cells
      (⟨((r.val.1.2,w'),(r.val.2.1,r.val.2.2)),hh⟩ : RetainedRectangleIndex T C)
    have he : w=w' := secantAxisAdjacent_left_unique T C _ _ _ hw hq.1
    have hnot := (secantCellPair_not_retained_iff T C _ _ _ _ hw hc.2).mpr hr
    rw [he] at hnot
    exact hnot hh
  · simp [rectangleExteriorSide,rectangleRemovedNeighbour] at h
    simp only [rectangleHasRetainedNeighbour,show (2 : Fin 4) ≠ 0 by decide,
      show (2 : Fin 4) ≠ 1 by decide,if_false,if_pos rfl] at hn
    obtain ⟨w',hh⟩ := hn
    have hq := retainedRectangle_axis_cells
      (⟨((r.val.1.1,r.val.1.2),(r.val.2.2,w')),hh⟩ : RetainedRectangleIndex T C)
    rcases h with hm | ⟨w,hw,hr⟩
    · have hb := secantAxisCuts_bounds T C w' hq.2.2.1
      have hg := hq.2.2.2.1
      change r.val.2.2<w' at hg
      linarith [hb.2]
    · have he : w=w' := secantAxisAdjacent_left_unique T C _ _ _ hw hq.2
      have hnot := (secantCellPair_not_retained_iff T C _ _ _ _ hc.1 hw).mpr hr
      rw [he] at hnot
      exact hnot hh
  · simp [rectangleExteriorSide,rectangleRemovedNeighbour] at h
    simp only [rectangleHasRetainedNeighbour,show (3 : Fin 4) ≠ 0 by decide,
      show (3 : Fin 4) ≠ 1 by decide,show (3 : Fin 4) ≠ 2 by decide,if_false] at hn
    obtain ⟨l',hh⟩ := hn
    have hq := retainedRectangle_axis_cells
      (⟨((l',r.val.1.1),(r.val.2.1,r.val.2.2)),hh⟩ : RetainedRectangleIndex T C)
    rcases h with ha | ⟨l,hl,hr⟩
    · have hb := secantAxisCuts_bounds T C l' hq.1.1
      have hg := hq.1.2.2.1
      change l'<r.val.1.1 at hg
      linarith [hb.1]
    · have he : l=l' := secantAxisAdjacent_right_unique T C _ _ _ hl hq.1
      have hnot := (secantCellPair_not_retained_iff T C _ _ _ _ hl hc.2).mpr hr
      rw [he] at hnot
      exact hnot hh

/-- Exact literal geometric fixed-side classification, including outer
period sides. This does not yet regroup or evaluate each boundary sum. -/
theorem fixedRectangleSide_exact_classification {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C) :
    rectangleSideReverse e=e ↔ rectangleExteriorSide e ∨ rectangleRemovedNeighbour e :=
  ⟨fixedRectangleSide_exterior_or_removed T C e,
    rectangleSide_exterior_or_removed_implies_fixed T C e⟩

end
end DirectGLSSW.HOMFLY.PrincipalTurning


