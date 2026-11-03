import LowestRowContract.Contract

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.LowestRowContract.ComponentRestriction
open DirectGLSSW
variable {D : PLLinkDiagram} {C : diagramComponent D} (R : ComponentRestriction D C)

theorem strandTangent_eq (c : Fin R.diagram.nCrossing) (i : Fin 2) :
    strandTangent R.diagram c i = strandTangent D (R.crossingEquiv c).val i := by
  unfold strandTangent
  rw [R.vertexPoint_eq, R.vertexPoint_eq, R.crossingVertex_eq, R.source_eq, R.incoming_eq]

theorem crossingDet_eq (c : Fin R.diagram.nCrossing) :
    crossingDet R.diagram c = crossingDet D (R.crossingEquiv c).val := by
  unfold crossingDet
  rw [R.strandTangent_eq, R.strandTangent_eq, R.overBranch_eq]

theorem crossingSign_eq (c : Fin R.diagram.nCrossing) :
    crossingSign R.diagram c = crossingSign D (R.crossingEquiv c).val := by
  unfold crossingSign
  congr 1
  exact R.crossingDet_eq c

end DirectGLSSW.HOMFLY.LowestRowContract.ComponentRestriction
