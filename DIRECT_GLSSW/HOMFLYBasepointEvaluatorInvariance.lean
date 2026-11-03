import HOMFLYRootSelfEvaluatorInduction
import HOMFLYBasepointShift
import DirectGLSSW.HOMFLY.HOMFLYTraversalOrderChanges
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits

theorem descendingEvaluator_advanceBase_eq {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (D : PLLinkDiagram) (hD : D.nCrossing = n)
    (T : BasedTraversal D) (C : diagramComponent D) :
    descendingLaurentEvaluator D T =
      descendingLaurentEvaluator D (advanceBaseTraversal T C) := by
  classical
  by_cases hall : ∀ c, firstVisitedBranch T c = firstVisitedBranch (advanceBaseTraversal T C) c
  · exact innerSameBranchEvaluator_all outer ((badCrossings T).card + 1)
      hD T (advanceBaseTraversal T C) (Nat.lt_succ_self _) hall
  · push_neg at hall
    obtain ⟨c,hc⟩ := hall
    have hs := branchChange_advanceBase_support T C c (Ne.symm hc)
    have hcase (i : Fin 2) (hport : D.incoming c i = (T.baseArc C).val)
        (hcomp : componentOf D.continuation (D.incoming c 0) =
          componentOf D.continuation (D.incoming c 1)) :
        descendingLaurentEvaluator D T =
          descendingLaurentEvaluator D (advanceBaseTraversal T C) := by
      have hC : componentOf D.continuation (D.incoming c i) = C := by
        rw [hport]
        exact (T.baseArc C).property
      have hroot : (T.baseArc (componentOf D.continuation (D.incoming c i))).val = D.incoming c i := by
        rw [hC]
        exact hport.symm
      apply rootSelf_singleBranch_evaluator_eq outer D hD T (advanceBaseTraversal T C) c i hroot
        ((componentOf_eq_iff _ _ _).1 hcomp)
      intro d hdc
      by_contra hchange
      have hd := branchChange_advanceBase_support T C d (Ne.symm hchange)
      rcases hd with ⟨hd0,_⟩ | ⟨hd1,_⟩
      · exact incoming_ne_of_crossing_ne D c d hdc 0 i (hd0.trans hport.symm)
      · exact incoming_ne_of_crossing_ne D c d hdc 1 i (hd1.trans hport.symm)
    rcases hs with ⟨h0,hcomp⟩ | ⟨h1,hcomp⟩
    · exact hcase 0 h0 hcomp
    · exact hcase 1 h1 hcomp

end DirectGLSSW.HOMFLY

