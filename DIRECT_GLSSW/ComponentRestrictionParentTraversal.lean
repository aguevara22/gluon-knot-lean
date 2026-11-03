import ComponentRestrictionVisits
import HOMFLYParentRootTraversal
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.LowestRowContract.ComponentRestriction
open PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- Extracting the actual continuing parent keeps the original exposed root
as its old physical arc, even after inserting the smoothing connector. -/
theorem parentRestriction_original_root (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (R : ComponentRestriction (smoothCrossing D c)
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))) :
    (R.arcEquiv (R.traversalRoot (parentRootSelfSmoothingTraversal D T c hself))).val =
      smoothArcEquiv D (Sum.inl
        (T.baseArc (componentOf D.continuation
          (D.incoming c (firstVisitedBranch T c)))).val) :=
  (R.traversalRoot_map (parentRootSelfSmoothingTraversal D T c hself)).trans
    (parentRootSelfSmoothingTraversal_continuing_root D T c hself)

end DirectGLSSW.HOMFLY.LowestRowContract.ComponentRestriction
