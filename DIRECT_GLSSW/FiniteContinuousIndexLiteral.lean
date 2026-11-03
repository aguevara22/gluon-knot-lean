import FiniteContinuousIndex

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- The literal coordinate body of the source-orbit starting vertex. -/
theorem orbitWordSource_eq_literal (D : PLLinkDiagram) (e : Fin D.nArc) (k : ℕ) :
    orbitWordSource D e k =
      Complex.equivRealProd.symm
        (D.vertexPoint (D.arcSource ((D.continuation ^ k) e))) := rfl

/-- The literal coordinate body of the source-orbit ending vertex. -/
theorem orbitWordTarget_eq_literal (D : PLLinkDiagram) (e : Fin D.nArc) (k : ℕ) :
    orbitWordTarget D e k =
      Complex.equivRealProd.symm
        (D.vertexPoint (D.arcTarget ((D.continuation ^ k) e))) := rfl

end DirectGLSSW.HOMFLY.PrincipalTurning
