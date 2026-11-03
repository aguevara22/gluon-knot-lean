import LowestRowConsumers
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.LowestRowContract
open DirectGLSSW PermutationOrbits Coefficients PrincipalTurning
open scoped BigOperators
local instance (D : PLLinkDiagram) : Fintype (diagramComponent D) := componentFintype D.continuation

theorem positive_framed_skein_from_row
    (D : PLLinkDiagram)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (c : Fin D.nCrossing) (hpos : crossingSign D c = Sign.pos) (b : Fin 2)
    (Restr : ∀ C : diagramComponent (smoothCrossing D c),
      ComponentRestriction (smoothCrossing D c) C)
    (row switchedRow leftRow rightRow : HOMFLYCoeff)
    (hs : aMonomial * row - aInvMonomial * switchedRow =
      aPower (-mixedWrithe (smoothCrossing D c)) *
        (aMonomial - aInvMonomial) * leftRow * rightRow) :
    let cut := rootSelfCutComponents D c (hconn _ _)
      (b)
    aPower (diagramWrithe D + turnInteger D) *
        (aMonomial - aInvMonomial) * row =
      aPower (diagramWrithe (switchCrossing D c) +
          turnInteger (switchCrossing D c)) *
        (aMonomial - aInvMonomial) * switchedRow +
        (aPower (diagramWrithe (Restr (cut (Sum.inl false))).diagram +
            turnInteger (Restr (cut (Sum.inl false))).diagram) *
            (aMonomial - aInvMonomial) * leftRow) *
          (aPower (diagramWrithe (Restr (cut (Sum.inl true))).diagram +
              turnInteger (Restr (cut (Sum.inl true))).diagram) *
            (aMonomial - aInvMonomial) * rightRow) := by
  let cut := rootSelfCutComponents D c (hconn _ _)
    (b)
  rcases actual_positive_framing_relations D hconn c hpos b Restr with ⟨hWswitch, hTswitch, hWsplit, hTsplit⟩
  have hnormalized := LowestRowContract.framed_skein_normalization
    row switchedRow leftRow rightRow
    (diagramWrithe D) (turnInteger D)
    (diagramWrithe (Restr (cut (Sum.inl false))).diagram)
    (turnInteger (Restr (cut (Sum.inl false))).diagram)
    (diagramWrithe (Restr (cut (Sum.inl true))).diagram)
    (turnInteger (Restr (cut (Sum.inl true))).diagram)
    (mixedWrithe (smoothCrossing D c)) hs hWsplit hTsplit
  have hexp : diagramWrithe D - 2 + turnInteger D =
      diagramWrithe (switchCrossing D c) + turnInteger (switchCrossing D c) := by
    rw [hWswitch, hTswitch]
  simpa only [hexp] using hnormalized


theorem positive_connected_framed_knot_row
    (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (c : Fin D.nCrossing) (hpos : crossingSign D c = Sign.pos) (b : Fin 2)
    (R : ∀ C : diagramComponent (smoothCrossing D c),
      ComponentRestriction (smoothCrossing D c) C)
 :
    DirectGLSSW.HOMFLY.framedKnotRow Gemini.candidateEvaluator D hD
        (componentOf D.continuation ⟨0, hD⟩) =
      DirectGLSSW.HOMFLY.framedKnotRow Gemini.candidateEvaluator
        (switchCrossing D c) hD
        (componentOf (switchCrossing D c).continuation ⟨0, hD⟩) +
      DirectGLSSW.HOMFLY.framedKnotRow Gemini.candidateEvaluator
        (R (rootSelfCutComponents D c (hconn _ _)
          (b) (Sum.inl false))).diagram
        (R (rootSelfCutComponents D c (hconn _ _)
          (b) (Sum.inl false))).nonempty
        (componentOf
          (R (rootSelfCutComponents D c (hconn _ _)
            (b) (Sum.inl false))).diagram.continuation
          ⟨0, (R (rootSelfCutComponents D c (hconn _ _)
            (b) (Sum.inl false))).nonempty⟩) *
      DirectGLSSW.HOMFLY.framedKnotRow Gemini.candidateEvaluator
        (R (rootSelfCutComponents D c (hconn _ _)
          (b) (Sum.inl true))).diagram
        (R (rootSelfCutComponents D c (hconn _ _)
          (b) (Sum.inl true))).nonempty
        (componentOf
          (R (rootSelfCutComponents D c (hconn _ _)
            (b) (Sum.inl true))).diagram.continuation
          ⟨0, (R (rootSelfCutComponents D c (hconn _ _)
            (b) (Sum.inl true))).nonempty⟩) := by
  classical
  let cut := rootSelfCutComponents D c (hconn _ _)
    (b)
  let H : Evaluator := Gemini.candidateEvaluator
  let hsm : 0 < (smoothCrossing D c).nArc := by
    change 0 < D.nArc + 2
    omega
  obtain ⟨Λ, hLambda, hfactor⟩ := lowest_row_for_restrictions (smoothCrossing D c) hsm R
  have hcount : diagramComponentCount (smoothCrossing D c) = 2 := by
    change Fintype.card (diagramComponent (smoothCrossing D c)) = 2
    exact smoothCrossing_component_count_of_connected D hconn c
      (b)
  have hproduct := componentRowProduct_actual_two_smoothing_components
    H D hconn c (b) R
  have hpow : -(2 * Λ) = -mixedWrithe (smoothCrossing D c) := by omega
  have hfac := hfactor
  rw [hcount] at hfac
  norm_num at hfac
  rw [hpow, hproduct] at hfac
  have hsrow :
      aMonomial * zRow (H D hD) 0 -
        aInvMonomial * zRow (H (switchCrossing D c) hD) 0 =
        aPower (-mixedWrithe (smoothCrossing D c)) *
          (aMonomial - aInvMonomial) *
            zRow (H (R (cut (Sum.inl false))).diagram
              (R (cut (Sum.inl false))).nonempty) 0 *
            zRow (H (R (cut (Sum.inl true))).diagram
              (R (cut (Sum.inl true))).nonempty) 0 := by
    rw [candidateEvaluator_positive_skein_row D hD c hpos 0]
    simpa only [H, mul_assoc] using hfac
  have hmain := positive_framed_skein_from_row D hconn c hpos b R
    (zRow (H D hD) 0)
    (zRow (H (switchCrossing D c) hD) 0)
    (zRow (H (R (cut (Sum.inl false))).diagram
      (R (cut (Sum.inl false))).nonempty) 0)
    (zRow (H (R (cut (Sum.inl true))).diagram
      (R (cut (Sum.inl true))).nonempty) 0)
    hsrow
  have hframe := actual_positive_framing_relations D hconn c hpos b R
  rcases hframe with ⟨_, hTswitch, _, _⟩
  let Cbase := componentOf D.continuation ⟨0, hD⟩
  have hturnCurrent : componentTurnInteger D Cbase = turnInteger D :=
    componentTurnInteger_eq_total_of_connected D hconn Cbase
  have hturnSwitch : componentTurnInteger (switchCrossing D c) Cbase =
      turnInteger (switchCrossing D c) := by
    calc
      componentTurnInteger (switchCrossing D c) Cbase =
          componentTurnInteger D Cbase := componentTurnInteger_switch D c Cbase
      _ = turnInteger D := hturnCurrent
      _ = turnInteger (switchCrossing D c) := hTswitch.symm
  have hCswitch : componentOf (switchCrossing D c).continuation ⟨0, hD⟩ = Cbase := rfl
  have hturnLeft := restriction_component_turn_total (R (cut (Sum.inl false)))
  have hturnRight := restriction_component_turn_total (R (cut (Sum.inl true)))
  unfold DirectGLSSW.HOMFLY.framedKnotRow
  rw [hCswitch, hturnCurrent, hturnSwitch, hturnLeft, hturnRight]
  simpa [H, cut, mul_assoc] using hmain
end DirectGLSSW.HOMFLY.LowestRowContract
