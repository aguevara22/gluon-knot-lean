import ComponentRestrictionTraversal
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.LowestRowContract.ComponentRestriction
open PermutationOrbits
variable {D : PLLinkDiagram} {C : diagramComponent D}

/-- Component extraction preserves the actual order of every pair of visits. -/
theorem basedTraversal_rankBefore (R : ComponentRestriction D C)
    (T : BasedTraversal D) (a b : Fin R.diagram.nArc) :
    rankBefore (visitRank (R.basedTraversal T) a) (visitRank (R.basedTraversal T) b) ↔
      rankBefore (visitRank T (R.arcEquiv a).val) (visitRank T (R.arcEquiv b).val) := by
  have hr : componentOf R.diagram.continuation a = componentOf R.diagram.continuation b :=
    (componentOf_eq_iff _ _ _).2 (R.continuation_sameCycle a b)
  have hd : componentOf D.continuation (R.arcEquiv a).val =
      componentOf D.continuation (R.arcEquiv b).val :=
    (R.arcEquiv a).property.trans (R.arcEquiv b).property.symm
  simp only [rankBefore,visitRank,hr,hd,lt_self_iff_false,true_and,false_or,
    R.basedTraversal_visitPosition]

/-- Every retained self-crossing is first encountered on its original branch. -/
theorem basedTraversal_firstVisitedBranch (R : ComponentRestriction D C)
    (T : BasedTraversal D) (c : Fin R.diagram.nCrossing) :
    firstVisitedBranch (R.basedTraversal T) c =
      firstVisitedBranch T (R.crossingEquiv c).val := by
  have h := R.basedTraversal_rankBefore T (R.diagram.incoming c 0) (R.diagram.incoming c 1)
  rw [R.incoming_eq,R.incoming_eq] at h
  unfold firstVisitedBranch
  rw [h]

/-- Extraction neither creates nor removes badness of a retained self-crossing. -/
theorem basedTraversal_badAt (R : ComponentRestriction D C)
    (T : BasedTraversal D) (c : Fin R.diagram.nCrossing) :
    badAt (R.basedTraversal T) c ↔ badAt T (R.crossingEquiv c).val := by
  unfold badAt
  rw [R.basedTraversal_firstVisitedBranch,R.overBranch_eq]

/-- The actual finite bad-crossing set agrees on every retained label. -/
theorem basedTraversal_mem_badCrossings (R : ComponentRestriction D C)
    (T : BasedTraversal D) (c : Fin R.diagram.nCrossing) :
    c ∈ badCrossings (R.basedTraversal T) ↔ (R.crossingEquiv c).val ∈ badCrossings T := by
  classical
  simp only [badCrossings,Finset.mem_filter,Finset.mem_univ,true_and,R.basedTraversal_badAt]

end DirectGLSSW.HOMFLY.LowestRowContract.ComponentRestriction
