import GlobalHoleBoundary

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The global literal hole-boundary contribution is the actual ordered
first-visit determinant sum, with the clockwise retained orientation. -/
theorem actualComponent_holeBoundary_signed_balance {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    (∑ e ∈ (Finset.univ : Finset (RetainedRectangleSide T C)).filter
      (fun e => ∃ c ∈ actualComponentSelfCrossings T C,
        rectangleTouchesCrossingHole T C c (firstVisitedBranch T c)
          (otherBranch (firstVisitedBranch T c)) e), rectangleSideIncrement e) =
    (2*Real.pi) * ∑ c ∈ actualComponentSelfCrossings T C,
      if 0<complexDet (crossingVector D c (firstVisitedBranch T c))
        (crossingVector D c (otherBranch (firstVisitedBranch T c)))
      then (1 : ℝ) else -1 := by
  rw [actualComponent_holeBoundary_regrouping,Finset.mul_sum]
  simp only [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  have hcm := (Finset.mem_filter.mp hc).2
  have hp := firstVisited_crossingHoleGridBoundary_balance T c (hcm.1.trans hcm.2.symm)
  rw [hcm.1] at hp
  rw [hp]
  split_ifs <;> ring

end
end DirectGLSSW.HOMFLY.PrincipalTurning

