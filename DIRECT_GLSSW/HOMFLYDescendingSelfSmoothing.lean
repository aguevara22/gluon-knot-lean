import HOMFLYRetainedRankComparison
import HOMFLYDescendingChildReduction
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _

theorem rootSelf_firstVisitedBranch (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2)
    (hroot : (T.baseArc (componentOf D.continuation (D.incoming c i))).val = D.incoming c i)
    (d : Fin D.nCrossing) (hd : d ≠ c) :
    firstVisitedBranch (rootSelfSmoothingTraversal D T c hself i)
      (smoothCrossingEquiv D c ⟨d,hd⟩) = firstVisitedBranch T d := by
  apply firstVisitedBranch_smooth_eq_of_rankBefore
  exact rootSelf_retained_rankBefore_iff D T c hself i hroot
    (D.incoming d 0) (D.incoming d 1)
    (incoming_ne_of_crossing_ne D c d hd 0 i)
    (incoming_ne_of_crossing_ne D c d hd 0 (otherBranch i))
    (incoming_ne_of_crossing_ne D c d hd 1 i)
    (incoming_ne_of_crossing_ne D c d hd 1 (otherBranch i))

/-- Internal terminal traversal helper. This constructs a concrete descending
smoothing when the only possible bad crossing is the self-crossing met at
the chosen base arc. It does not assert evaluator or Reidemeister invariance. -/
theorem smoothCrossing_exists_descending_of_baseArc
    (D : PLLinkDiagram) (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i : Fin 2)
    (hbase : D.incoming c i = (T.baseArc C).val)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (hgood : ∀ d : Fin D.nCrossing, d ≠ c → ¬ badAt T d) :
    ∃ U : BasedTraversal (smoothCrossing D c), badCrossings U = ∅ := by
  have hC : componentOf D.continuation (D.incoming c i) = C := by
    rw [hbase]
    exact (T.baseArc C).property
  have hroot : (T.baseArc (componentOf D.continuation (D.incoming c i))).val = D.incoming c i := by
    rw [hC]
    exact hbase.symm
  refine ⟨rootSelfSmoothingTraversal D T c hself i, ?_⟩
  exact smooth_badCrossings_empty_of_retained_firstBranch D T c _
    (rootSelf_firstVisitedBranch D T c hself i hroot) hgood

end
end DirectGLSSW.HOMFLY


