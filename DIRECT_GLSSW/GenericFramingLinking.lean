import GenericFramedSkein
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.LowestRowContract
open DirectGLSSW PermutationOrbits Coefficients PrincipalTurning
theorem positive_framing_with_linking (D : PLLinkDiagram)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (c : Fin D.nCrossing) (hc : crossingSign D c = Sign.pos) (i : Fin 2)
    (R : ∀ C : diagramComponent (smoothCrossing D c), ComponentRestriction (smoothCrossing D c) C) :
    diagramWrithe (switchCrossing D c) = diagramWrithe D - 2 ∧
    turnInteger (switchCrossing D c) = turnInteger D ∧
    diagramWrithe D - 1 =
      diagramWrithe (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl false))).diagram +
      diagramWrithe (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl true))).diagram +
      2 * _root_.GeminiLowest.totalLinking (smoothCrossing D c) ∧
    turnInteger D =
      turnInteger (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl false))).diagram +
      turnInteger (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl true))).diagram := by
  simpa only [_root_.GeminiLowest.two_mul_totalLinking_eq_mixedWrithe] using
    actual_positive_framing_relations D hconn c hc i R

end DirectGLSSW.HOMFLY.LowestRowContract
