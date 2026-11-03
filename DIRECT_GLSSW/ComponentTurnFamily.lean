import ComponentTurnRestriction
import SmoothingTurning
import HOMFLYRootSelfSmoothingTraversal

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits LowestRowContract
open scoped BigOperators
local instance (D : PLLinkDiagram) : Fintype (diagramComponent D) :=
  componentFintype D.continuation
local instance (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    Fintype (RootSelfCutLabels D c i) := by
  classical
  unfold RootSelfCutLabels
  infer_instance

/-- The sum of turns of all exact restrictions is the actual diagram's turn. -/
theorem turnInteger_eq_sum_restrictions (D : PLLinkDiagram)
    (R : ∀ C : diagramComponent D, ComponentRestriction D C) :
    turnInteger D = ∑ C : diagramComponent D, turnInteger (R C).diagram := by
  rw [turnInteger_eq_sum_components]
  apply Finset.sum_congr rfl
  intro C _
  exact (turnInteger_restriction (R C)).symm

/-- Actual smoothing preserves the total integer, hence the sum of all actual
restricted smoothed components equals the integer before smoothing. -/
theorem turnInteger_eq_sum_smooth_restrictions (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (R : ∀ C : diagramComponent (smoothCrossing D c), ComponentRestriction (smoothCrossing D c) C) :
    turnInteger D = ∑ C : diagramComponent (smoothCrossing D c), turnInteger (R C).diagram := by
  calc
    turnInteger D = turnInteger (smoothCrossing D c) := (turnInteger_smoothCrossing D c).symm
    _ = _ := turnInteger_eq_sum_restrictions (smoothCrossing D c) R

/-- For an actual connected diagram, the proved root-oriented cut equivalence
has precisely its false/true components. Unaffected components are ruled out by
actual connectedness, not by an assumed two-component decomposition. -/
theorem turnInteger_eq_two_smooth_restrictions (D : PLLinkDiagram)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (c : Fin D.nCrossing) (i : Fin 2)
    (R : ∀ C : diagramComponent (smoothCrossing D c), ComponentRestriction (smoothCrossing D c) C) :
    turnInteger D =
      turnInteger (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl false))).diagram +
      turnInteger (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl true))).diagram := by
  classical
  letI : IsEmpty {C : diagramComponent D // C ≠ componentOf D.continuation (D.incoming c i)} := ⟨by
    intro C
    let e : Fibre D.continuation C.val := Classical.choice inferInstance
    exact C.property (e.property.symm.trans ((componentOf_eq_iff _ _ _).mpr (hconn _ _)))⟩
  let E := rootSelfCutComponents D c (hconn _ _) i
  have hs := Fintype.sum_equiv E
    (fun l => turnInteger (R (E l)).diagram)
    (fun C => turnInteger (R C).diagram) (fun _ => rfl)
  rw [turnInteger_eq_sum_smooth_restrictions D c R, ← hs]
  simp [E, Fintype.sum_sum_type, add_comm]

end DirectGLSSW.HOMFLY.PrincipalTurning
