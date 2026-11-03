import HOMFLYRootSelfSmoothingTraversal
import SplitOrderCrossComparison
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _

theorem finEquivCast_val {n m : ℕ} (h : n = m) (x : Fin n) :
    (Equiv.cast (congrArg Fin h) x).val = x.val := by subst m; rfl

theorem rootSelfCutOrder_val (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i : Fin 2) (l : RootSelfCutLabels D c i) :
    (rootSelfCutOrder D T c hself i l).val =
      (splitSumToFinMiddleFirst T.componentIndex
        (componentOf D.continuation (D.incoming c i)) l).val := by
  exact finEquivCast_val (smooth_componentCount_self D c hself).symm _

theorem rootSelfCutOrder_lt_iff (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i : Fin 2) (l r : RootSelfCutLabels D c i) :
    rootSelfCutOrder D T c hself i l < rootSelfCutOrder D T c hself i r ↔
      splitSumToFinMiddleFirst T.componentIndex (componentOf D.continuation (D.incoming c i)) l <
      splitSumToFinMiddleFirst T.componentIndex (componentOf D.continuation (D.incoming c i)) r := by
  change (rootSelfCutOrder D T c hself i l).val < (rootSelfCutOrder D T c hself i r).val ↔ _
  rw [rootSelfCutOrder_val, rootSelfCutOrder_val]
  rfl

theorem rootSelfCutOrder_selected_val (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i : Fin 2) (b : Bool) :
    (rootSelfCutOrder D T c hself i (Sum.inl b)).val =
      (T.componentIndex (componentOf D.continuation (D.incoming c i))).val + (if b then 0 else 1) := by
  rw [rootSelfCutOrder_val]
  cases b
  · exact congrArg Fin.val (splitSumToFinMiddleFirst_false T.componentIndex
      (componentOf D.continuation (D.incoming c i)))
  · simpa only [if_true, Nat.add_zero] using congrArg Fin.val
      (splitSumToFinMiddleFirst_true T.componentIndex
        (componentOf D.continuation (D.incoming c i)))


end
end DirectGLSSW.HOMFLY



