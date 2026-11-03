import HOMFLYRowExtractionProbe
import ActualFramedSkein
import TwoComponentRowProduct
import ComponentRestrictionConnected
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.LowestRowContract
open DirectGLSSW PermutationOrbits Coefficients PrincipalTurning
open scoped BigOperators
local instance (D : PLLinkDiagram) : Fintype (diagramComponent D) :=
  componentFintype D.continuation

theorem restriction_component_turn_total {D : PLLinkDiagram}
    {C : diagramComponent D} (R : ComponentRestriction D C) :
    componentTurnInteger R.diagram
      (componentOf R.diagram.continuation ⟨0, R.nonempty⟩) = turnInteger R.diagram := by
  exact componentTurnInteger_eq_total_of_connected R.diagram
    R.continuation_sameCycle _

theorem actual_initial_history_framed_knot_row
    (D : PLLinkDiagram) (T : BasedTraversal D)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (hpos : ∀ d : Fin D.nCrossing, crossingSign D d = Sign.pos)
    (t : MarkedParentState)
    (htrace : MarkedParentTrace ⟨D,T,ProcessedParentMarks.initial D T hconn⟩ t)
    (ht : 0 < t.1.nArc) (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ∀ C : diagramComponent (smoothCrossing t.1 c),
      ComponentRestriction (smoothCrossing t.1 c) C)
    (Λ : ℤ)
    (hfactor : zRow
      (Gemini.candidateEvaluator (smoothCrossing t.1 c)
        (by change 0 < t.1.nArc + 2; omega))
      (1 - (diagramComponentCount (smoothCrossing t.1 c) : ℤ)) =
        aPower (-2 * Λ) *
          (aMonomial - aInvMonomial) ^
            (diagramComponentCount (smoothCrossing t.1 c) - 1) *
          componentRowProduct Gemini.candidateEvaluator (smoothCrossing t.1 c) R)
    (hLambda : 2 * Λ = mixedWrithe (smoothCrossing t.1 c)) :
    DirectGLSSW.HOMFLY.framedKnotRow Gemini.candidateEvaluator t.1 ht
        (componentOf t.1.continuation ⟨0, ht⟩) =
      DirectGLSSW.HOMFLY.framedKnotRow Gemini.candidateEvaluator
        (switchCrossing t.1 c) ht
        (componentOf (switchCrossing t.1 c).continuation ⟨0, ht⟩) +
      DirectGLSSW.HOMFLY.framedKnotRow Gemini.candidateEvaluator
        (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
          (firstVisitedBranch t.2.1 c) (Sum.inl false))).diagram
        (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
          (firstVisitedBranch t.2.1 c) (Sum.inl false))).nonempty
        (componentOf
          (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
            (firstVisitedBranch t.2.1 c) (Sum.inl false))).diagram.continuation
          ⟨0, (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
            (firstVisitedBranch t.2.1 c) (Sum.inl false))).nonempty⟩) *
      DirectGLSSW.HOMFLY.framedKnotRow Gemini.candidateEvaluator
        (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
          (firstVisitedBranch t.2.1 c) (Sum.inl true))).diagram
        (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
          (firstVisitedBranch t.2.1 c) (Sum.inl true))).nonempty
        (componentOf
          (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
            (firstVisitedBranch t.2.1 c) (Sum.inl true))).diagram.continuation
          ⟨0, (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
            (firstVisitedBranch t.2.1 c) (Sum.inl true))).nonempty⟩) := by
  classical
  let cut := rootSelfCutComponents t.1 c (t.2.2.connected _ _)
    (firstVisitedBranch t.2.1 c)
  let H : Evaluator := Gemini.candidateEvaluator
  let hsm : 0 < (smoothCrossing t.1 c).nArc := by
    change 0 < t.1.nArc + 2
    omega
  have hcount : diagramComponentCount (smoothCrossing t.1 c) = 2 := by
    change Fintype.card (diagramComponent (smoothCrossing t.1 c)) = 2
    exact smoothCrossing_component_count_of_connected t.1 t.2.2.connected c
      (firstVisitedBranch t.2.1 c)
  have hproduct := componentRowProduct_actual_two_smoothing_components
    H t.1 t.2.2.connected c (firstVisitedBranch t.2.1 c) R
  have hpow : -(2 * Λ) = -mixedWrithe (smoothCrossing t.1 c) := by omega
  have hfac := hfactor
  rw [hcount] at hfac
  norm_num at hfac
  rw [hpow, hproduct] at hfac
  have hsrow :
      aMonomial * zRow (H t.1 ht) 0 -
        aInvMonomial * zRow (H (switchCrossing t.1 c) ht) 0 =
        aPower (-mixedWrithe (smoothCrossing t.1 c)) *
          (aMonomial - aInvMonomial) *
            zRow (H (R (cut (Sum.inl false))).diagram
              (R (cut (Sum.inl false))).nonempty) 0 *
            zRow (H (R (cut (Sum.inl true))).diagram
              (R (cut (Sum.inl true))).nonempty) 0 := by
    rw [HOMFLYRowExtractionProbe.actual_initial_history_row
      D T hconn hpos t htrace ht c hc]
    simpa only [H, mul_assoc] using hfac
  have hmain := FramingSkeinIntegration.actual_framed_skein_from_current_row
    D T hconn hpos t htrace c hc R
    (zRow (H t.1 ht) 0)
    (zRow (H (switchCrossing t.1 c) ht) 0)
    (zRow (H (R (cut (Sum.inl false))).diagram
      (R (cut (Sum.inl false))).nonempty) 0)
    (zRow (H (R (cut (Sum.inl true))).diagram
      (R (cut (Sum.inl true))).nonempty) 0)
    hsrow
  have hframe := FramingActualRelationsProbe.actual_initial_history_framing
    D T hconn hpos t htrace c hc R
  rcases hframe with ⟨_, hTswitch, _, _⟩
  let Cbase := componentOf t.1.continuation ⟨0, ht⟩
  have hturnCurrent : componentTurnInteger t.1 Cbase = turnInteger t.1 :=
    componentTurnInteger_eq_total_of_connected t.1 t.2.2.connected Cbase
  have hturnSwitch : componentTurnInteger (switchCrossing t.1 c) Cbase =
      turnInteger (switchCrossing t.1 c) := by
    calc
      componentTurnInteger (switchCrossing t.1 c) Cbase =
          componentTurnInteger t.1 Cbase := componentTurnInteger_switch t.1 c Cbase
      _ = turnInteger t.1 := hturnCurrent
      _ = turnInteger (switchCrossing t.1 c) := hTswitch.symm
  have hCswitch : componentOf (switchCrossing t.1 c).continuation ⟨0, ht⟩ = Cbase := rfl
  have hturnLeft := restriction_component_turn_total (R (cut (Sum.inl false)))
  have hturnRight := restriction_component_turn_total (R (cut (Sum.inl true)))
  unfold DirectGLSSW.HOMFLY.framedKnotRow
  rw [hCswitch, hturnCurrent, hturnSwitch, hturnLeft, hturnRight]
  simpa [H, cut, mul_assoc] using hmain


end DirectGLSSW.HOMFLY.LowestRowContract
