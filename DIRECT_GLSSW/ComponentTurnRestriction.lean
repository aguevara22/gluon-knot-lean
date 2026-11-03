import ComponentTurning
import LowestRowContract.Contract

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits LowestRowContract
open scoped BigOperators

/-- A literal component restriction preserves each physical arc displacement. -/
theorem arcVector_restriction {D : PLLinkDiagram} {C : diagramComponent D}
    (R : ComponentRestriction D C) (e : Fin R.diagram.nArc) :
    arcVector R.diagram e = arcVector D (R.arcEquiv e).val := by
  simp only [arcVector, R.vertexPoint_eq, R.target_eq, R.source_eq]

/-- Exact continuation and endpoint transport preserve the actual principal turn. -/
theorem turn_restriction {D : PLLinkDiagram} {C : diagramComponent D}
    (R : ComponentRestriction D C) (e : Fin R.diagram.nArc) :
    turn R.diagram e = turn D (R.arcEquiv e).val := by
  unfold turn
  rw [arcVector_restriction, arcVector_restriction, R.continuation_eq]

/-- Total actual tangent turn of the extracted diagram equals the ambient
component's turn, reindexed by the literal component arc equivalence. -/
theorem totalTurn_restriction {D : PLLinkDiagram} {C : diagramComponent D}
    (R : ComponentRestriction D C) :
    totalTurn R.diagram = componentTotalTurn D C := by
  unfold totalTurn componentTotalTurn
  let E : Fin R.diagram.nArc ≃ Fibre D.continuation C := R.arcEquiv
  exact Fintype.sum_equiv E _ _ (fun e => turn_restriction R e)

/-- Integer transport follows from the proved unique total-turn characterization. -/
theorem turnInteger_restriction {D : PLLinkDiagram} {C : diagramComponent D}
    (R : ComponentRestriction D C) :
    turnInteger R.diagram = componentTurnInteger D C := by
  apply turnInteger_unique
  rw [totalTurn_restriction R]
  exact componentTotalTurn_eq_integer D C

end DirectGLSSW.HOMFLY.PrincipalTurning
