import ActualRectangleNeighbours

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

def secantRemovedCellReason {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b u v : ℝ) : Prop :=
  u≤b ∨ (b≤1/4 ∧ (componentArcLength D (T.baseArc C).val : ℝ)-1/4≤u) ∨
    secantRectangleInsideStar T C a b u v

theorem secantCellPair_not_retained_iff {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b u v : ℝ)
    (h1 : secantAxisAdjacent T C a b) (h2 : secantAxisAdjacent T C u v) :
    ((a,b),(u,v)) ∉ secantRetainedRectangles T C ↔ secantRemovedCellReason T C a b u v := by
  have hm1 : (a,b) ∈ secantAxisCells T C := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨h1.1,h1.2.1⟩,h1⟩
  have hm2 : (u,v) ∈ secantAxisCells T C := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨h2.1,h2.2.1⟩,h2⟩
  have hp : ((a,b),(u,v)) ∈ (secantAxisCells T C).product (secantAxisCells T C) :=
    Finset.mem_product.mpr ⟨hm1,hm2⟩
  simp only [secantRetainedRectangles,Finset.mem_filter,hp,true_and,
    secantRemovedCellReason,not_and_or,not_or,not_not,not_lt]

/-- The only exterior sides possible for this actual ordered retained region. -/
def rectangleExteriorSide {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (e : RetainedRectangleSide T C) : Prop :=
  (e.2=2 ∧ e.1.val.2.2=(componentArcLength D (T.baseArc C).val : ℝ)) ∨
    (e.2=3 ∧ e.1.val.1.1=0)

def rectangleRemovedNeighbour {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (e : RetainedRectangleSide T C) : Prop :=
  if e.2=0 then ∃ l, secantAxisAdjacent T C l e.1.val.2.1 ∧
    secantRemovedCellReason T C e.1.val.1.1 e.1.val.1.2 l e.1.val.2.1
  else if e.2=1 then ∃ w, secantAxisAdjacent T C e.1.val.1.2 w ∧
    secantRemovedCellReason T C e.1.val.1.2 w e.1.val.2.1 e.1.val.2.2
  else if e.2=2 then ∃ w, secantAxisAdjacent T C e.1.val.2.2 w ∧
    secantRemovedCellReason T C e.1.val.1.1 e.1.val.1.2 e.1.val.2.2 w
  else ∃ l, secantAxisAdjacent T C l e.1.val.1.1 ∧
    secantRemovedCellReason T C l e.1.val.1.1 e.1.val.2.1 e.1.val.2.2

/-- Literal forward classification: every actual fixed side is an outer
s=0 / t=period side, or touches an actual neighboring cell removed by the
explicit diagonal/periodic-corner/crossing-star filter. No boundary package. -/
theorem fixedRectangleSide_exterior_or_removed {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C)
    (hfixed : rectangleSideReverse e=e) :
    rectangleExteriorSide e ∨ rectangleRemovedNeighbour e := by
  have hmissing := (rectangleSide_fixed_iff_missing_retainedNeighbour e).mp hfixed
  have hc := retainedRectangle_axis_cells e.1
  have hp := (Finset.mem_filter.mp e.1.property).2.1
  have ha := secantAxisCuts_bounds T C e.1.val.1.1 hc.1.1
  have hb := secantAxisCuts_bounds T C e.1.val.1.2 hc.1.2.1
  have hu := secantAxisCuts_bounds T C e.1.val.2.1 hc.2.1
  have hv := secantAxisCuts_bounds T C e.1.val.2.2 hc.2.2.1
  rcases e with ⟨r,k⟩
  fin_cases k
  · simp [rectangleExteriorSide,rectangleRemovedNeighbour]
    change ¬∃ l, ((r.val.1.1,r.val.1.2),(l,r.val.2.1)) ∈ secantRetainedRectangles T C at hmissing
    obtain ⟨l,hl⟩ := secantAxis_predecessor_exists T C _ hc.2.1 (by linarith [hb.1])
    refine ⟨l,hl,(secantCellPair_not_retained_iff T C _ _ _ _ hc.1 hl).mp ?_⟩
    intro hh
    exact hmissing ⟨l,hh⟩
  · simp [rectangleExteriorSide,rectangleRemovedNeighbour]
    change ¬∃ w, ((r.val.1.2,w),(r.val.2.1,r.val.2.2)) ∈ secantRetainedRectangles T C at hmissing
    obtain ⟨w,hw⟩ := secantAxis_successor_exists T C _ hc.1.2.1 (by linarith [hu.2])
    refine ⟨w,hw,(secantCellPair_not_retained_iff T C _ _ _ _ hw hc.2).mp ?_⟩
    intro hh
    exact hmissing ⟨w,hh⟩
  · simp [rectangleExteriorSide,rectangleRemovedNeighbour]
    change ¬∃ w, ((r.val.1.1,r.val.1.2),(r.val.2.2,w)) ∈ secantRetainedRectangles T C at hmissing
    by_cases hm : r.val.2.2=(componentArcLength D (T.baseArc C).val : ℝ)
    · exact Or.inl hm
    · right
      obtain ⟨w,hw⟩ := secantAxis_successor_exists T C _ hc.2.2.1 (lt_of_le_of_ne hv.2 hm)
      refine ⟨w,hw,(secantCellPair_not_retained_iff T C _ _ _ _ hc.1 hw).mp ?_⟩
      intro hh
      exact hmissing ⟨w,hh⟩
  · simp [rectangleExteriorSide,rectangleRemovedNeighbour]
    change ¬∃ l, ((l,r.val.1.1),(r.val.2.1,r.val.2.2)) ∈ secantRetainedRectangles T C at hmissing
    by_cases ha0 : r.val.1.1=0
    · exact Or.inl ha0
    · right
      obtain ⟨l,hl⟩ := secantAxis_predecessor_exists T C _ hc.1.1 (lt_of_le_of_ne ha.1 (Ne.symm ha0))
      refine ⟨l,hl,(secantCellPair_not_retained_iff T C _ _ _ _ hl hc.2).mp ?_⟩
      intro hh
      exact hmissing ⟨l,hh⟩

end
end DirectGLSSW.HOMFLY.PrincipalTurning


