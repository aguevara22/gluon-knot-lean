import GlobalHoleBoundary

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem orderedCrossingBranches_first {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j) :
    i=firstVisitedBranch T c ∧ j=otherBranch (firstVisitedBranch T c) := by
  have hpair : ∀ a b : Fin 2, a≠b → otherBranch a=b := by decide
  have hif : i=firstVisitedBranch T c := by
    by_contra hne
    have hfi : otherBranch (firstVisitedBranch T c)=i := hpair _ _ (Ne.symm hne)
    have hij' : otherBranch i=j := hpair _ _ hij
    have hjf : j=firstVisitedBranch T c := by
      rw [←hfi] at hij'
      simpa only [otherBranch_involutive] using hij'.symm
    have hself : componentOf D.continuation (D.incoming c (firstVisitedBranch T c))=
        componentOf D.continuation (D.incoming c (otherBranch (firstVisitedBranch T c))) := by
      rw [hfi,←hjf,hi,hj]
    have hgap := firstVisitedBranch_time_gap T c hself
    rw [hfi,←hjf] at hgap
    linarith
  exact ⟨hif,by rw [←hif]; exact (hpair i j hij).symm⟩

/-- The source star-removal test on actual axis cells is exactly membership
in one of the actual component's ordered four-cell crossing holes. -/
theorem secantRectangleInsideStar_iff_hole_cell {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b u v : ℝ)
    (hx : secantAxisAdjacent T C a b) (hy : secantAxisAdjacent T C u v) :
    secantRectangleInsideStar T C a b u v ↔
      ∃ c ∈ actualComponentSelfCrossings T C,
        ((a,b),(u,v)) ∈ secantCrossingHoleCells T C c (firstVisitedBranch T c)
          (otherBranch (firstVisitedBranch T c)) := by
  constructor
  · rintro ⟨c,i,j,hij,hi,hj,horder,hal,hbr,hul,hvr⟩
    obtain ⟨rfl,rfl⟩ := orderedCrossingBranches_first T C c i j hij hi hj horder
    refine ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hj⟩,?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hal,hbr,hul,hvr⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx.1,hx.2.1⟩,hx⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy.1,hy.2.1⟩,hy⟩
  · rintro ⟨c,hc,hcell⟩
    have hm := (Finset.mem_filter.mp hc).2
    have hb := (Finset.mem_filter.mp hcell).2
    refine ⟨c,firstVisitedBranch T c,otherBranch (firstVisitedBranch T c),
      crossingHole_branch_ne_other _,hm.1,hm.2,?_,hb⟩
    have hgap := firstVisitedBranch_time_gap T c (hm.1.trans hm.2.symm)
    linarith

end
end DirectGLSSW.HOMFLY.PrincipalTurning


