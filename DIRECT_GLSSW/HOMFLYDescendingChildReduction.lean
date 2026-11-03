import DirectGLSSW.HOMFLY.HOMFYSmoothingTraversalBridge

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

/-- Exact final reduction from retained first-branch transport to a descending
actual smoothing. This lemma does not assume or establish evaluator invariance. -/
theorem smooth_badCrossings_empty_of_retained_firstBranch
    (D : PLLinkDiagram) (T : BasedTraversal D) (c : Fin D.nCrossing)
    (U : BasedTraversal (smoothCrossing D c))
    (horder : ∀ (d : Fin D.nCrossing) (hd : d ≠ c),
      firstVisitedBranch U (smoothCrossingEquiv D c ⟨d, hd⟩) = firstVisitedBranch T d)
    (hgood : ∀ d : Fin D.nCrossing, d ≠ c → ¬ badAt T d) :
    badCrossings U = ∅ := by
  apply (badCrossings_eq_empty_iff_firstVisited_over U).2
  intro d
  obtain ⟨x, rfl⟩ := (smoothCrossingEquiv D c).surjective d
  have hg : firstVisitedBranch T x.val = D.overBranch x.val := by
    exact Classical.not_not.mp (hgood x.val x.property)
  change firstVisitedBranch U (smoothCrossingEquiv D c x) =
    D.overBranch (((smoothCrossingEquiv D c).symm (smoothCrossingEquiv D c x)).val)
  rw [Equiv.symm_apply_apply]
  exact (horder x.val x.property).trans hg

end DirectGLSSW.HOMFLY


