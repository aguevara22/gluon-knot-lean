import FramingWrithePartition
import ComponentTurnFamily
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open LowestRowContract PrincipalTurning PermutationOrbits
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : Fintype (diagramComponent D) :=
  componentFintype D.continuation
local instance (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    Fintype (RootSelfCutLabels D c i) := by
  unfold RootSelfCutLabels
  infer_instance

theorem sum_actual_two_smoothing_components (D : PLLinkDiagram)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (c : Fin D.nCrossing) (i : Fin 2)
    (f : diagramComponent (smoothCrossing D c) → ℤ) :
    (∑ C : diagramComponent (smoothCrossing D c), f C) =
      f (rootSelfCutComponents D c (hconn _ _) i (Sum.inl false)) +
      f (rootSelfCutComponents D c (hconn _ _) i (Sum.inl true)) := by
  letI : IsEmpty {C : diagramComponent D // C ≠ componentOf D.continuation (D.incoming c i)} := ⟨by
    intro C
    let e : Fibre D.continuation C.val := Classical.choice inferInstance
    exact C.property (e.property.symm.trans ((componentOf_eq_iff _ _ _).mpr (hconn _ _)))⟩
  let E := rootSelfCutComponents D c (hconn _ _) i
  have hs := Fintype.sum_equiv E (fun l => f (E l)) f (fun _ => rfl)
  rw [← hs]
  simp [E,Fintype.sum_sum_type,add_comm]

theorem diagramWrithe_positive_two_smoothing (D : PLLinkDiagram)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (c : Fin D.nCrossing) (hc : crossingSign D c = Sign.pos) (i : Fin 2)
    (R : ∀ C : diagramComponent (smoothCrossing D c), ComponentRestriction (smoothCrossing D c) C) :
    diagramWrithe D - 1 =
      diagramWrithe (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl false))).diagram +
      diagramWrithe (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl true))).diagram +
      mixedWrithe (smoothCrossing D c) := by
  rw [← diagramWrithe_smooth_positive D c hc,diagramWrithe_component_partition (smoothCrossing D c) R]
  rw [sum_actual_two_smoothing_components D hconn c i]

theorem componentTurnInteger_switch (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (C : diagramComponent D) :
    componentTurnInteger (switchCrossing D c) C = componentTurnInteger D C := rfl

theorem componentTurnInteger_eq_total_of_connected (D : PLLinkDiagram)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (C : diagramComponent D) : componentTurnInteger D C = turnInteger D := by
  have heq (E : diagramComponent D) : E = C := by
    let e : Fibre D.continuation E := Classical.choice inferInstance
    let c : Fibre D.continuation C := Classical.choice inferInstance
    exact e.property.symm.trans (((componentOf_eq_iff _ _ _).mpr (hconn _ _)).trans c.property)
  rw [turnInteger_eq_sum_components]
  symm
  apply Finset.sum_eq_single C
  · intro E _ hEC; exact (hEC (heq E)).elim
  · simp

theorem actual_positive_framing_relations (D : PLLinkDiagram)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (c : Fin D.nCrossing) (hc : crossingSign D c = Sign.pos) (i : Fin 2)
    (R : ∀ C : diagramComponent (smoothCrossing D c), ComponentRestriction (smoothCrossing D c) C) :
    diagramWrithe (switchCrossing D c) = diagramWrithe D - 2 ∧
    turnInteger (switchCrossing D c) = turnInteger D ∧
    diagramWrithe D - 1 =
      diagramWrithe (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl false))).diagram +
      diagramWrithe (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl true))).diagram +
      mixedWrithe (smoothCrossing D c) ∧
    turnInteger D =
      turnInteger (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl false))).diagram +
      turnInteger (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl true))).diagram :=
  ⟨diagramWrithe_switch_positive D c hc,turnInteger_switch D c,
    diagramWrithe_positive_two_smoothing D hconn c hc i R,
    turnInteger_eq_two_smooth_restrictions D hconn c i R⟩






end DirectGLSSW.HOMFLY
