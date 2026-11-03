import FramingActualRelations
import ProcessedBadCrossingPositive
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.FramingActualRelationsProbe
open LowestRowContract PrincipalTurning

theorem actual_initial_history_framing
    (D : PLLinkDiagram) (T : BasedTraversal D)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (hpos : ∀ d : Fin D.nCrossing, crossingSign D d = Sign.pos)
    (t : MarkedParentState)
    (h : MarkedParentTrace ⟨D,T,ProcessedParentMarks.initial D T hconn⟩ t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ∀ C : diagramComponent (smoothCrossing t.1 c), ComponentRestriction (smoothCrossing t.1 c) C) :
    diagramWrithe (switchCrossing t.1 c) = diagramWrithe t.1 - 2 ∧
    turnInteger (switchCrossing t.1 c) = turnInteger t.1 ∧
    diagramWrithe t.1 - 1 =
      diagramWrithe (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl false))).diagram +
      diagramWrithe (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true))).diagram +
      mixedWrithe (smoothCrossing t.1 c) ∧
    turnInteger t.1 =
      turnInteger (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl false))).diagram +
      turnInteger (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true))).diagram :=
  actual_positive_framing_relations t.1 t.2.2.connected c
    (h.bad_crossing_positive_of_initial D T hconn hpos t c hc) (firstVisitedBranch t.2.1 c) R
end DirectGLSSW.HOMFLY.FramingActualRelationsProbe
set_option pp.all true
#check @DirectGLSSW.HOMFLY.sum_actual_two_smoothing_components

#check @DirectGLSSW.HOMFLY.diagramWrithe_positive_two_smoothing

#check @DirectGLSSW.HOMFLY.componentTurnInteger_switch

#check @DirectGLSSW.HOMFLY.componentTurnInteger_eq_total_of_connected

#check @DirectGLSSW.HOMFLY.actual_positive_framing_relations

#check @DirectGLSSW.HOMFLY.FramingActualRelationsProbe.actual_initial_history_framing

