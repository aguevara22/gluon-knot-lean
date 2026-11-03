import ComponentRestrictionOrbits
import ComponentRestrictionConnected
import HOMFLYOrbitTraversalCoordinates
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.LowestRowContract.ComponentRestriction
open PermutationOrbits ComponentRestrictionComparison
variable {D : PLLinkDiagram} {C : diagramComponent D}

/-- The actual restricted arc at the original component root. -/
def traversalRoot (R : ComponentRestriction D C) (T : BasedTraversal D) :
    Fin R.diagram.nArc := R.arcEquiv.symm (T.baseArc C)

/-- Restrict an actual traversal while preserving its original component root. -/
def basedTraversal (R : ComponentRestriction D C) (T : BasedTraversal D) :
    BasedTraversal R.diagram where
  componentIndex := (chooseBasedTraversal R.diagram).componentIndex
  baseArc K := ⟨R.traversalRoot T,
    ((componentOf_eq_iff _ _ _).2
      (R.continuation_sameCycle (R.traversalRoot T)
        ((chooseBasedTraversal R.diagram).baseArc K).val)).trans
      ((chooseBasedTraversal R.diagram).baseArc K).property⟩

@[simp] theorem basedTraversal_baseArc (R : ComponentRestriction D C)
    (T : BasedTraversal D) (K : diagramComponent R.diagram) :
    ((R.basedTraversal T).baseArc K).val = R.traversalRoot T := rfl

@[simp] theorem traversalRoot_map (R : ComponentRestriction D C) (T : BasedTraversal D) :
    (R.arcEquiv (R.traversalRoot T)).val = (T.baseArc C).val := by
  exact congrArg Subtype.val (R.arcEquiv.apply_symm_apply (T.baseArc C))

/-- Actual ordinal visit positions are unchanged by extracting the component. -/
theorem basedTraversal_visitPosition (R : ComponentRestriction D C)
    (T : BasedTraversal D) (a : Fin R.diagram.nArc) :
    visitPosition (R.basedTraversal T) a = visitPosition T (R.arcEquiv a).val := by
  let r := R.traversalRoot T
  let x : Fibre R.diagram.continuation (componentOf R.diagram.continuation r) :=
    ⟨a,(componentOf_eq_iff _ _ _).2 (R.continuation_sameCycle a r)⟩
  have hx := rootedOrbitPosition_transport R r x
  have hm : arcEmbedding R r = (T.baseArc C).val := R.traversalRoot_map T
  have hbase : (T.baseArc (componentOf D.continuation (arcEmbedding R a))).val =
      arcEmbedding R r := by
    change (T.baseArc (componentOf D.continuation (R.arcEquiv a).val)).val = arcEmbedding R r
    rw [(R.arcEquiv a).property,hm]
  have hcomp : componentOf D.continuation (arcEmbedding R a) =
      componentOf D.continuation (arcEmbedding R r) := by
    simpa only [rootedFibreEquiv_val] using (rootedFibreEquiv R r x).property
  rw [visitPosition_eq_orbitPosition_of_baseArc (R.basedTraversal T) a r rfl x.property]
  change _ = visitPosition T (arcEmbedding R a)
  rw [visitPosition_eq_orbitPosition_of_baseArc T (arcEmbedding R a)
    (arcEmbedding R r) hbase hcomp]
  exact hx.symm

/-- Retained incoming ports have their original visit positions. -/
theorem basedTraversal_incoming_visitPosition (R : ComponentRestriction D C)
    (T : BasedTraversal D) (c : Fin R.diagram.nCrossing) (i : Fin 2) :
    visitPosition (R.basedTraversal T) (R.diagram.incoming c i) =
      visitPosition T (D.incoming (R.crossingEquiv c).val i) := by
  rw [R.basedTraversal_visitPosition,R.incoming_eq]

end DirectGLSSW.HOMFLY.LowestRowContract.ComponentRestriction
