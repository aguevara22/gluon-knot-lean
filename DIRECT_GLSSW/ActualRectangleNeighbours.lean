import SecantAxisCoverage

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Literal neighboring retained rectangle across each directed side. -/
def rectangleHasRetainedNeighbour {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (e : RetainedRectangleSide T C) : Prop :=
  if e.2=0 then ∃ l, ((e.1.val.1.1,e.1.val.1.2),(l,e.1.val.2.1)) ∈ secantRetainedRectangles T C
  else if e.2=1 then ∃ w, ((e.1.val.1.2,w),(e.1.val.2.1,e.1.val.2.2)) ∈ secantRetainedRectangles T C
  else if e.2=2 then ∃ w, ((e.1.val.1.1,e.1.val.1.2),(e.1.val.2.2,w)) ∈ secantRetainedRectangles T C
  else ∃ l, ((l,e.1.val.1.1),(e.1.val.2.1,e.1.val.2.2)) ∈ secantRetainedRectangles T C

theorem rectangleReverseRelation_iff_retainedNeighbour {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (e : RetainedRectangleSide T C) :
    (∃ f, rectangleReverseRelation e f) ↔ rectangleHasRetainedNeighbour e := by
  constructor
  · rintro ⟨⟨q,j⟩,h⟩
    have hr := retainedRectangle_axis_cells e.1
    have hq := retainedRectangle_axis_cells q
    have hsx := congrArg Prod.fst h.1
    have hsy := congrArg Prod.snd h.1
    have hfx := congrArg Prod.fst h.2
    have hfy := congrArg Prod.snd h.2
    rcases e with ⟨r,i⟩
    fin_cases i <;> fin_cases j <;>
      simp [rectangleSideStart,rectangleSideFinish] at hsx hsy hfx hfy
    all_goals try (exfalso; linarith [hr.1.2.2.1,hr.2.2.2.1,hq.1.2.2.1,hq.2.2.2.1])
    · simp only [rectangleHasRetainedNeighbour,if_pos rfl]
      refine ⟨q.val.2.1,?_⟩
      simpa only [← hfx,← hsx,← hsy] using q.property
    · simp only [rectangleHasRetainedNeighbour,show (1 : Fin 4) ≠ 0 by decide,if_false,if_pos rfl]
      refine ⟨q.val.1.2,?_⟩
      simpa only [← hsx,← hfy,← hsy] using q.property
    · simp only [rectangleHasRetainedNeighbour,show (2 : Fin 4) ≠ 0 by decide,
        show (2 : Fin 4) ≠ 1 by decide,if_false,if_pos rfl]
      refine ⟨q.val.2.2,?_⟩
      simpa only [← hsx,← hfx,← hsy] using q.property
    · simp only [rectangleHasRetainedNeighbour,show (3 : Fin 4) ≠ 0 by decide,
        show (3 : Fin 4) ≠ 1 by decide,show (3 : Fin 4) ≠ 2 by decide,if_false]
      refine ⟨q.val.1.1,?_⟩
      simpa only [← hsx,← hsy,← hfy] using q.property
  · rcases e with ⟨r,k⟩
    fin_cases k
    · intro h
      simp only [rectangleHasRetainedNeighbour,if_pos rfl] at h
      obtain ⟨l,hl⟩ := h
      refine ⟨(⟨((r.val.1.1,r.val.1.2),(l,r.val.2.1)),hl⟩,2),?_⟩
      simp [rectangleReverseRelation,rectangleSideStart,rectangleSideFinish]
    · intro h
      simp only [rectangleHasRetainedNeighbour,show (1 : Fin 4) ≠ 0 by decide,if_false,if_pos rfl] at h
      obtain ⟨w,hw⟩ := h
      refine ⟨(⟨((r.val.1.2,w),(r.val.2.1,r.val.2.2)),hw⟩,3),?_⟩
      simp [rectangleReverseRelation,rectangleSideStart,rectangleSideFinish]
    · intro h
      simp only [rectangleHasRetainedNeighbour,show (2 : Fin 4) ≠ 0 by decide,show (2 : Fin 4) ≠ 1 by decide,if_false,if_pos rfl] at h
      obtain ⟨w,hw⟩ := h
      refine ⟨(⟨((r.val.1.1,r.val.1.2),(r.val.2.2,w)),hw⟩,0),?_⟩
      simp [rectangleReverseRelation,rectangleSideStart,rectangleSideFinish]
    · intro h
      simp only [rectangleHasRetainedNeighbour,show (3 : Fin 4) ≠ 0 by decide,show (3 : Fin 4) ≠ 1 by decide,show (3 : Fin 4) ≠ 2 by decide,if_false] at h
      obtain ⟨l,hl⟩ := h
      refine ⟨(⟨((l,r.val.1.1),(r.val.2.1,r.val.2.2)),hl⟩,1),?_⟩
      simp [rectangleReverseRelation,rectangleSideStart,rectangleSideFinish]

theorem rectangleSide_fixed_iff_missing_retainedNeighbour {D : PLLinkDiagram}
    {T : BasedTraversal D} {C : diagramComponent D} (e : RetainedRectangleSide T C) :
    rectangleSideReverse e=e ↔ ¬rectangleHasRetainedNeighbour e := by
  rw [rectangleSideReverse_fixed_iff,rectangleReverseRelation_iff_retainedNeighbour]

end
end DirectGLSSW.HOMFLY.PrincipalTurning


