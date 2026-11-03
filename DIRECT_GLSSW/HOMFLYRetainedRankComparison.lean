import HOMFLYRootSelfRankData
import HOMFLYRootSelfUnaffectedRanks
import HOMFLYRootSelfOrderArithmetic
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _

theorem rootSelf_retained_rankBefore_iff (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2)
    (hroot : (T.baseArc (componentOf D.continuation (D.incoming c i))).val = D.incoming c i)
    (x y : Fin D.nArc)
    (hxa : x ≠ D.incoming c i) (hxb : x ≠ D.incoming c (otherBranch i))
    (hya : y ≠ D.incoming c i) (hyb : y ≠ D.incoming c (otherBranch i)) :
    rankBefore
      (visitRank (rootSelfSmoothingTraversal D T c hself i) (smoothArcEquiv D (Sum.inl x)))
      (visitRank (rootSelfSmoothingTraversal D T c hself i) (smoothArcEquiv D (Sum.inl y))) ↔
      rankBefore (visitRank T x) (visitRank T y) := by
  by_cases hx : componentOf D.continuation x = componentOf D.continuation (D.incoming c i)
  · obtain ⟨b,j,hj,hox,hnx⟩ := rootSelf_selected_rank_data D T c hself i hroot x hx hxa hxb
    by_cases hy : componentOf D.continuation y = componentOf D.continuation (D.incoming c i)
    · obtain ⟨d,l,hl,hoy,hny⟩ := rootSelf_selected_rank_data D T c hself i hroot y hy hya hyb
      rw [hnx,hny,hox,hoy]
      rw [rootSelf_selected_rankBefore_iff D T c hself i b d _ j l hj hl]
      simp [rankBefore]
    · let C : {C : diagramComponent D // C ≠ componentOf D.continuation (D.incoming c i)} :=
        ⟨componentOf D.continuation y,hy⟩
      have hny := rootSelf_unaffected_visitRank D T c hself i C y rfl
      rw [hnx,hny,hox]
      exact rootSelf_selected_other_rankBefore_iff D T c hself i b C _ j _ _
  · let C : {C : diagramComponent D // C ≠ componentOf D.continuation (D.incoming c i)} :=
      ⟨componentOf D.continuation x,hx⟩
    have hnx := rootSelf_unaffected_visitRank D T c hself i C x rfl
    by_cases hy : componentOf D.continuation y = componentOf D.continuation (D.incoming c i)
    · obtain ⟨d,l,hl,hoy,hny⟩ := rootSelf_selected_rank_data D T c hself i hroot y hy hya hyb
      rw [hnx,hny,hoy]
      exact rootSelf_other_selected_rankBefore_iff D T c hself i d C _ _ _ l
    · let E : {C : diagramComponent D // C ≠ componentOf D.continuation (D.incoming c i)} :=
        ⟨componentOf D.continuation y,hy⟩
      have hny := rootSelf_unaffected_visitRank D T c hself i E y rfl
      rw [hnx,hny]
      exact rootSelf_other_other_rankBefore_iff D T c hself i C E _ _

end
end DirectGLSSW.HOMFLY

