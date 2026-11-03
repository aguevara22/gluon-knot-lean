import ActiveArcTinyParentClosedAuxiliary

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive OpenFirstEdgeGeometry Nonalternation RetainedWords PhysicalSegments PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (η : ℝ) (hη : 0<η) (hη1 : η<1)

open scoped BigOperators

/-- Actual matched closed amplitudes are preserved under the derived cyclic rebase. -/
theorem tinyParent_closedWeight_eq (hRI : GLSSWRootIndependence)
    (hAux : ClosedAuxiliary (ParentArc q c hcut) (ParentRegular q hR c hcut))
    (T : Nonalternation.Support (ParentArc q c hcut) (ParentRegular q hR c hcut))
    (D : {D : Components (ParentArc q c hcut) (ParentRegular q hR c hcut) T //
      D ≠ openComponent (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val}) :
    let C := tinyParentClosedComponentEquiv q hR c hc hcut η hη hη1 T D
    closedWeight (ParentArc q c hcut) (ParentRegular q hR c hcut) hAux T D.val =
      closedWeight (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
        (tinyParent_closedAuxiliary q hR c hc hcut η hη hη1 hAux)
        (tinySupportOfParent q hR c hc hcut η hη hη1 T) C.val := by
  dsimp only
  let C := tinyParentClosedComponentEquiv q hR c hc hcut η hη hη1 T D
  have hC : (tinyParentClosedComponentEquiv q hR c hc hcut η hη hη1 T D).val ≠
      openComponent (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1).noTriple
        (tinySupportOfParent q hR c hc hcut η hη hη1 T).val := C.property
  rw [closedWeight,dif_pos D.property,closedWeight,dif_pos hC]
  exact DaughterRootAmplitude.polygonAmplitude_ofFn_isRotated hRI
    (hAux T D.val D.property)
    (tinyParent_closed_word_isRotated q hR c hc hcut η hη hη1 T D)

/-- The complete erased-open product, reindexed by the actual closed-component equivalence. -/
theorem tinyParent_closedWeight_product_eq (hRI : GLSSWRootIndependence)
    (hAux : ClosedAuxiliary (ParentArc q c hcut) (ParentRegular q hR c hcut))
    (T : Nonalternation.Support (ParentArc q c hcut) (ParentRegular q hR c hcut)) :
    (∏ D ∈ Finset.univ.erase (openComponent (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val),
      closedWeight (ParentArc q c hcut) (ParentRegular q hR c hcut) hAux T D) =
    (∏ C ∈ Finset.univ.erase (openComponent (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1).noTriple
        (parentTinySelection q c hcut η T.val)),
      closedWeight (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
        (tinyParent_closedAuxiliary q hR c hc hcut η hη hη1 hAux)
        (tinySupportOfParent q hR c hc hcut η hη hη1 T) C) := by
  rw [Finset.prod_subtype (p := fun D => D ≠ openComponent (ParentArc q c hcut)
    (ParentRegular q hR c hcut).noTriple T.val)
    (Finset.univ.erase (openComponent (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val)) (fun D => by simp)]
  rw [Finset.prod_subtype (p := fun C => C ≠ openComponent (TinyArc q c hcut η)
    (TinyRegular q hR c hc hcut η hη hη1).noTriple (parentTinySelection q c hcut η T.val))
    (Finset.univ.erase (openComponent (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1).noTriple
      (parentTinySelection q c hcut η T.val))) (fun C => by simp)]
  apply Fintype.prod_equiv (tinyParentClosedComponentEquiv q hR c hc hcut η hη hη1 T)
  intro D
  exact tinyParent_closedWeight_eq q hR c hc hcut η hη hη1 hRI hAux T D

/-- Source original auxiliary data discharges the parent auxiliary input. -/
theorem tinyParent_closedWeight_product_eq_from_original (hRI : GLSSWRootIndependence)
    (hAux : ClosedAuxiliary q hR)
    (T : Nonalternation.Support (ParentArc q c hcut) (ParentRegular q hR c hcut)) :
    (∏ D ∈ Finset.univ.erase (openComponent (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val),
      closedWeight (ParentArc q c hcut) (ParentRegular q hR c hcut)
        (CompatibleWords.parent_closedAuxiliary q hR c hc hcut hAux) T D) =
    (∏ C ∈ Finset.univ.erase (openComponent (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1).noTriple
        (parentTinySelection q c hcut η T.val)),
      closedWeight (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
        (tinyParent_closedAuxiliary_from_original q hR c hc hcut η hη hη1 hAux)
        (tinySupportOfParent q hR c hc hcut η hη hη1 T) C) :=
  tinyParent_closedWeight_product_eq q hR c hc hcut η hη hη1 hRI
    (CompatibleWords.parent_closedAuxiliary q hR c hc hcut hAux) T

end DirectGLSSW.ActiveArc.LiteralTinyParent
