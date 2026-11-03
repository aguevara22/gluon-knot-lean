import DiagonalNeighbourGeometry
import PeriodicSecantCorner
import ActualRectangleBoundaryChain

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The literal periodic-corner removal branch of the actual neighbouring cell. -/
def rectanglePeriodicNeighbour {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (e : RetainedRectangleSide T C) : Prop :=
  let m : ℝ := componentArcLength D (T.baseArc C).val
  if e.2=0 then ∃ l, secantAxisAdjacent T C l e.1.val.2.1 ∧ e.1.val.1.2≤1/4 ∧ m-1/4≤l
  else if e.2=1 then ∃ w, secantAxisAdjacent T C e.1.val.1.2 w ∧ w≤1/4 ∧ m-1/4≤e.1.val.2.1
  else if e.2=2 then ∃ w, secantAxisAdjacent T C e.1.val.2.2 w ∧ e.1.val.1.2≤1/4 ∧ m-1/4≤e.1.val.2.2
  else ∃ l, secantAxisAdjacent T C l e.1.val.1.1 ∧ e.1.val.1.1≤1/4 ∧ m-1/4≤e.1.val.2.1

/-- Every literal periodic-cut side has zero argument increment, from the
actual common negative base-arc direction. -/
theorem rectanglePeriodicNeighbour_increment_zero {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C)
    (h : rectanglePeriodicNeighbour e) : rectangleSideIncrement e=0 := by
  have hc := retainedRectangle_axis_cells e.1
  have hret := (Finset.mem_filter.mp e.1.property).2.2.1
  have ha := secantAxisCuts_bounds T C e.1.val.1.1 hc.1.1
  have hb := secantAxisCuts_bounds T C e.1.val.1.2 hc.1.2.1
  have hu := secantAxisCuts_bounds T C e.1.val.2.1 hc.2.1
  have hv := secantAxisCuts_bounds T C e.1.val.2.2 hc.2.2.1
  have hwx := secantAxisAdjacent_width T C _ _ hc.1
  have hwy := secantAxisAdjacent_width T C _ _ hc.2
  rcases e with ⟨r,s⟩
  fin_cases s
  · simp only [rectanglePeriodicNeighbour,ite_true] at h
    obtain ⟨l,hl,hbq,hml⟩ := h
    exact False.elim (hret ⟨hbq,by linarith [hl.2.2.1]⟩)
  · simp only [rectanglePeriodicNeighbour, show (1 : Fin 4) ≠ 0 by decide, ite_false, ite_true] at h
    obtain ⟨w,hw,hwq,hmu⟩ := h
    exact False.elim (hret ⟨by linarith [hw.2.2.1],hmu⟩)
  · simp only [rectanglePeriodicNeighbour, show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide, ite_false, ite_true] at h
    obtain ⟨w,hw,hbq,hmv⟩ := h
    have hult : r.val.2.1 < (componentArcLength D (T.baseArc C).val : ℝ)-1/4 := by
      by_contra hn
      exact hret ⟨hbq,le_of_not_gt hn⟩
    have hvlt : r.val.2.2 < (componentArcLength D (T.baseArc C).val : ℝ) := by
      linarith
    change Complex.arg (basedUniformSecant T C r.val.1.1 r.val.2.2 /
      basedUniformSecant T C r.val.1.2 r.val.2.2)=0
    apply basedUniformSecant_base_corner_ratio_arg T C
    · exact ⟨hb.1,hbq⟩
    · exact ⟨hmv,hv.2⟩
    · exact ⟨ha.1,by linarith [hc.1.2.2.1]⟩
    · exact ⟨hmv,hv.2⟩
    · rintro ⟨_,he⟩;linarith
    · rintro ⟨_,he⟩;linarith
  · simp only [rectanglePeriodicNeighbour, show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide, ite_false, ite_true] at h
    obtain ⟨l,hl,haq,hmu⟩ := h
    have hbgt : 1/4<r.val.1.2 := by
      by_contra hn
      exact hret ⟨le_of_not_gt hn,hmu⟩
    have hapos : 0<r.val.1.1 := by linarith
    change Complex.arg (basedUniformSecant T C r.val.1.1 r.val.2.1 /
      basedUniformSecant T C r.val.1.1 r.val.2.2)=0
    apply basedUniformSecant_base_corner_ratio_arg T C
    · exact ⟨ha.1,haq⟩
    · exact ⟨by linarith [hc.2.2.2.1],hv.2⟩
    · exact ⟨ha.1,haq⟩
    · exact ⟨hmu,hu.2⟩
    · rintro ⟨he,_⟩;linarith
    · rintro ⟨he,_⟩;linarith

end
end DirectGLSSW.HOMFLY.PrincipalTurning

