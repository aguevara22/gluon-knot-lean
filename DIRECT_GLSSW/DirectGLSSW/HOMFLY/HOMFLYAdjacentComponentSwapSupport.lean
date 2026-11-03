import DirectGLSSW.HOMFLY.HOMFLYAdjacentComponentSwap

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

def adjacentSwapAffectedCrossing {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (c : Fin D.nCrossing) : Prop :=
  (T.componentIndex (PermutationOrbits.componentOf D.continuation (D.incoming c 0)) = r ∧
    (T.componentIndex
      (PermutationOrbits.componentOf D.continuation (D.incoming c 1))).val = r.val + 1) ∨
  ((T.componentIndex
      (PermutationOrbits.componentOf D.continuation (D.incoming c 0))).val = r.val + 1 ∧
    T.componentIndex (PermutationOrbits.componentOf D.continuation (D.incoming c 1)) = r)

theorem adjacentSwapAffectedCrossing_iff_branch_changes
    {D : PLLinkDiagram} (T : BasedTraversal D) (r : Fin (diagramComponentCount D))
    (hr : r.val + 1 < diagramComponentCount D) (c : Fin D.nCrossing) :
    adjacentSwapAffectedCrossing T r c ↔
      firstVisitedBranch (reindexTraversalComponents T (adjacentComponentSwap r hr)) c ≠
        firstVisitedBranch T c := by
  constructor
  · intro h
    rcases h with h | h
    · rw [firstVisitedBranch_reindex_adjacent_components_of_mixed T r hr c h.1 h.2]
      intro heq
      have hfixed (x : Fin 2) : Equiv.swap (0 : Fin 2) 1 x ≠ x := by
        fin_cases x <;> simp
      exact hfixed (firstVisitedBranch T c) heq
    · rw [firstVisitedBranch_reindex_adjacent_components_of_mixed_reverse T r hr c h.1 h.2]
      intro heq
      have hfixed (x : Fin 2) : Equiv.swap (0 : Fin 2) 1 x ≠ x := by
        fin_cases x <;> simp
      exact hfixed (firstVisitedBranch T c) heq
  · intro hchange
    by_cases hp : adjacentSwapAffectedCrossing T r c
    · exact hp
    · have heq :
          firstVisitedBranch (reindexTraversalComponents T (adjacentComponentSwap r hr)) c =
            firstVisitedBranch T c :=
        firstVisitedBranch_reindex_adjacent_components_of_not_mixed T r hr c
          (by simpa [adjacentSwapAffectedCrossing] using hp)
      exact False.elim (hchange heq)

end DirectGLSSW.HOMFLY



