import FramingActualRelationsProbe
import FramedSkeinAlgebra

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.HOMFLY.FramingSkeinIntegration
open LowestRowContract Coefficients PermutationOrbits PrincipalTurning

/-- Combine the actual initial-history framing equations with a current-row
skein identity. The coefficient identity remains the sole row-level premise. -/
theorem actual_framed_skein_from_current_row
    (D : PLLinkDiagram) (T : BasedTraversal D)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (hpos : ∀ d : Fin D.nCrossing, crossingSign D d = Sign.pos)
    (t : MarkedParentState)
    (htrace : MarkedParentTrace ⟨D, T, ProcessedParentMarks.initial D T hconn⟩ t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (Restr : ∀ C : diagramComponent (smoothCrossing t.1 c),
      ComponentRestriction (smoothCrossing t.1 c) C)
    (row switchedRow leftRow rightRow : HOMFLYCoeff)
    (hs : aMonomial * row - aInvMonomial * switchedRow =
      aPower (-mixedWrithe (smoothCrossing t.1 c)) *
        (aMonomial - aInvMonomial) * leftRow * rightRow) :
    let cut := rootSelfCutComponents t.1 c (t.2.2.connected _ _)
      (firstVisitedBranch t.2.1 c)
    aPower (diagramWrithe t.1 + turnInteger t.1) *
        (aMonomial - aInvMonomial) * row =
      aPower (diagramWrithe (switchCrossing t.1 c) +
          turnInteger (switchCrossing t.1 c)) *
        (aMonomial - aInvMonomial) * switchedRow +
        (aPower (diagramWrithe (Restr (cut (Sum.inl false))).diagram +
            turnInteger (Restr (cut (Sum.inl false))).diagram) *
            (aMonomial - aInvMonomial) * leftRow) *
          (aPower (diagramWrithe (Restr (cut (Sum.inl true))).diagram +
              turnInteger (Restr (cut (Sum.inl true))).diagram) *
            (aMonomial - aInvMonomial) * rightRow) := by
  let cut := rootSelfCutComponents t.1 c (t.2.2.connected _ _)
    (firstVisitedBranch t.2.1 c)
  rcases FramingActualRelationsProbe.actual_initial_history_framing
      D T hconn hpos t htrace c hc Restr with ⟨hWswitch, hTswitch, hWsplit, hTsplit⟩
  have hnormalized := LowestRowContract.framed_skein_normalization
    row switchedRow leftRow rightRow
    (diagramWrithe t.1) (turnInteger t.1)
    (diagramWrithe (Restr (cut (Sum.inl false))).diagram)
    (turnInteger (Restr (cut (Sum.inl false))).diagram)
    (diagramWrithe (Restr (cut (Sum.inl true))).diagram)
    (turnInteger (Restr (cut (Sum.inl true))).diagram)
    (mixedWrithe (smoothCrossing t.1 c)) hs hWsplit hTsplit
  have hexp : diagramWrithe t.1 - 2 + turnInteger t.1 =
      diagramWrithe (switchCrossing t.1 c) + turnInteger (switchCrossing t.1 c) := by
    rw [hWswitch, hTswitch]
  simpa only [hexp] using hnormalized

end DirectGLSSW.HOMFLY.FramingSkeinIntegration
