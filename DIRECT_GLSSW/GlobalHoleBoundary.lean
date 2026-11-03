import HoleBoundaryRegrouping
import HoleTouchDisjointness

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem crossingHole_actual_retainedBoundary_regrouping {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    : (∑ e ∈ (Finset.univ : Finset (RetainedRectangleSide T C)).filter
        (rectangleTouchesCrossingHole T C c i j), rectangleSideIncrement e) =
      -crossingHoleGridBoundarySum T C c i j := by
  obtain ⟨a,b,u,v,ha,hb,hu,hv,_⟩ := crossingHole_retainedNeighbours_exist T C c i j hij hi hj horder
  exact crossingHole_retainedBoundary_regrouping T C c i j hij hi hj horder a b u v ha hb hu hv

/-- Actual self-crossings of this component, in the traversal's first/other order. -/
def actualComponentSelfCrossings {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) : Finset (Fin D.nCrossing) :=
  Finset.univ.filter (fun c =>
    componentOf D.continuation (D.incoming c (firstVisitedBranch T c))=C ∧
    componentOf D.continuation (D.incoming c (otherBranch (firstVisitedBranch T c)))=C)

/-- Literal global regrouping of all crossing-hole sides in the retained
boundary. Diagonal, periodic and outer sides are separate remaining terms. -/
theorem actualComponent_holeBoundary_regrouping {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    (∑ e ∈ (Finset.univ : Finset (RetainedRectangleSide T C)).filter
      (fun e => ∃ c ∈ actualComponentSelfCrossings T C,
        rectangleTouchesCrossingHole T C c (firstVisitedBranch T c)
          (otherBranch (firstVisitedBranch T c)) e), rectangleSideIncrement e) =
    -∑ c ∈ actualComponentSelfCrossings T C,
      crossingHoleGridBoundarySum T C c (firstVisitedBranch T c)
        (otherBranch (firstVisitedBranch T c)) := by
  let crossings := actualComponentSelfCrossings T C
  let holes : Fin D.nCrossing → Finset (RetainedRectangleSide T C) := fun c =>
    Finset.univ.filter (rectangleTouchesCrossingHole T C c (firstVisitedBranch T c)
      (otherBranch (firstVisitedBranch T c)))
  have hdisj : Set.PairwiseDisjoint (↑crossings) holes := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro e he he'
    have hcm := (Finset.mem_filter.mp (show c∈actualComponentSelfCrossings T C from hc)).2
    have hdm := (Finset.mem_filter.mp (show d∈actualComponentSelfCrossings T C from hd)).2
    apply hcd
    apply rectangleTouchesCrossingHole_unique_crossing T C c d
      (firstVisitedBranch T c) (otherBranch (firstVisitedBranch T c))
      (firstVisitedBranch T d) (otherBranch (firstVisitedBranch T d))
      (crossingHole_branch_ne_other _) (crossingHole_branch_ne_other _)
      hcm.1 hcm.2 hdm.1 hdm.2
      (by have hg := firstVisitedBranch_time_gap T c (hcm.1.trans hcm.2.symm);linarith)
      (by have hg := firstVisitedBranch_time_gap T d (hdm.1.trans hdm.2.symm);linarith)
      e (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp he').2
  have hset : (Finset.univ : Finset (RetainedRectangleSide T C)).filter
      (fun e => ∃ c ∈ actualComponentSelfCrossings T C,
        rectangleTouchesCrossingHole T C c (firstVisitedBranch T c)
          (otherBranch (firstVisitedBranch T c)) e) = crossings.biUnion holes := by
    ext e
    simp [crossings,holes]
  rw [hset,Finset.sum_biUnion hdisj]
  simp only [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  have hcm := (Finset.mem_filter.mp (show c∈actualComponentSelfCrossings T C from hc)).2
  exact crossingHole_actual_retainedBoundary_regrouping T C c (firstVisitedBranch T c)
    (otherBranch (firstVisitedBranch T c)) (crossingHole_branch_ne_other _) hcm.1 hcm.2
    (by have hg := firstVisitedBranch_time_gap T c (hcm.1.trans hcm.2.symm);linarith)

end
end DirectGLSSW.HOMFLY.PrincipalTurning


