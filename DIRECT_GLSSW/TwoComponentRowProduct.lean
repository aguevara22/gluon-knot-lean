import FramingActualRelations
import LowestRowContract.Contract
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.LowestRowContract
open DirectGLSSW PermutationOrbits
open scoped BigOperators
attribute [local instance] Classical.propDecidable

local instance (D : PLLinkDiagram) : Fintype (diagramComponent D) :=
  componentFintype D.continuation
local instance (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    Fintype (RootSelfCutLabels D c i) := by
  unfold RootSelfCutLabels
  infer_instance

theorem smoothCrossing_component_count_of_connected (D : PLLinkDiagram)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (c : Fin D.nCrossing) (i : Fin 2) :
    Fintype.card (diagramComponent (smoothCrossing D c)) = 2 := by
  classical
  letI : IsEmpty {C : diagramComponent D //
      C ≠ componentOf D.continuation (D.incoming c i)} := ⟨by
    intro C
    let e : Fibre D.continuation C.val := Classical.choice inferInstance
    exact C.property (e.property.symm.trans
      ((componentOf_eq_iff _ _ _).mpr (hconn _ _)))⟩
  let E := rootSelfCutComponents D c (hconn _ _) i
  calc
    Fintype.card (diagramComponent (smoothCrossing D c)) =
        Fintype.card (RootSelfCutLabels D c i) := Fintype.card_congr E.symm
    _ = 2 := by simp [RootSelfCutLabels]

theorem componentRowProduct_actual_two_smoothing_components
    (H : Evaluator) (D : PLLinkDiagram)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (c : Fin D.nCrossing) (i : Fin 2)
    (R : ∀ C : diagramComponent (smoothCrossing D c),
      ComponentRestriction (smoothCrossing D c) C) :
    componentRowProduct H (smoothCrossing D c) R =
      zRow (H (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl false))).diagram
        (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl false))).nonempty) 0 *
      zRow (H (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl true))).diagram
        (R (rootSelfCutComponents D c (hconn _ _) i (Sum.inl true))).nonempty) 0 := by
  classical
  letI : IsEmpty {C : diagramComponent D //
      C ≠ componentOf D.continuation (D.incoming c i)} := ⟨by
    intro C
    let e : Fibre D.continuation C.val := Classical.choice inferInstance
    exact C.property (e.property.symm.trans
      ((componentOf_eq_iff _ _ _).mpr (hconn _ _)))⟩
  let E := rootSelfCutComponents D c (hconn _ _) i
  unfold componentRowProduct
  have hp := Fintype.prod_equiv E
    (fun l : RootSelfCutLabels D c i =>
      zRow (H (R (E l)).diagram (R (E l)).nonempty) 0)
    (fun C : diagramComponent (smoothCrossing D c) =>
      zRow (H (R C).diagram (R C).nonempty) 0)
    (fun _ => rfl)
  rw [← hp]
  simp [E, Fintype.prod_sum_type]
  exact mul_comm _ _


end DirectGLSSW.HOMFLY.LowestRowContract
