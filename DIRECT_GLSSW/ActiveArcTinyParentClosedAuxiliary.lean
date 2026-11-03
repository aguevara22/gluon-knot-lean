import ActiveArcTinyParentClosedWords
import ActiveArcParentClosedAuxiliary
import DirectGLSSW.DaughterRootAmplitude

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive OpenFirstEdgeGeometry Nonalternation RetainedWords PhysicalSegments PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (η : ℝ) (hη : 0<η) (hη1 : η<1)

/-- Actual canonical closed words are generic using only the parent auxiliary domain. -/
theorem tinyParent_closed_cyclicGeneric
    (hAux : ClosedAuxiliary (ParentArc q c hcut) (ParentRegular q hR c hcut))
    (T : Nonalternation.Support (ParentArc q c hcut) (ParentRegular q hR c hcut))
    (C : Components (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (tinySupportOfParent q hR c hc hcut η hη hη1 T))
    (hC : C ≠ openComponent (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1).noTriple
      (parentTinySelection q c hcut η T.val)) :
    CyclicGeneric (ClosedVertex (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (tinySupportOfParent q hR c hc hcut η hη hη1 T) C hC) := by
  let E := tinyParentClosedComponentEquiv q hR c hc hcut η hη hη1 T
  let D := E.symm ⟨C,hC⟩
  have hg := hAux T D.val D.property
  have hrot := tinyParent_closed_word_isRotated q hR c hc hcut η hη hη1 T D
  have he : E D = ⟨C,hC⟩ := E.apply_symm_apply ⟨C,hC⟩
  change List.ofFn (ClosedVertex (ParentArc q c hcut) (ParentRegular q hR c hcut) T D.val D.property) ~r
    List.ofFn (ClosedVertex (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (tinySupportOfParent q hR c hc hcut η hη hη1 T) (E D).val (E D).property) at hrot
  rw [he] at hrot
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated hrot hg

/-- All tiny supports are covered by the actual support equivalence. -/
theorem tinyParent_closedAuxiliary
    (hAux : ClosedAuxiliary (ParentArc q c hcut) (ParentRegular q hR c hcut)) :
    ClosedAuxiliary (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1) := by
  intro V
  obtain ⟨T,hT⟩ := (tinyParentSupportEquiv q hR c hc hcut η hη hη1).symm.surjective V
  have he : tinySupportOfParent q hR c hc hcut η hη hη1 T = V := hT
  subst V
  exact tinyParent_closed_cyclicGeneric q hR c hc hcut η hη hη1 hAux T

/-- The source original auxiliary package supplies the parent domain internally. -/
theorem tinyParent_closedAuxiliary_from_original (hAux : ClosedAuxiliary q hR) :
    ClosedAuxiliary (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1) :=
  tinyParent_closedAuxiliary q hR c hc hcut η hη hη1
    (CompatibleWords.parent_closedAuxiliary q hR c hc hcut hAux)

end DirectGLSSW.ActiveArc.LiteralTinyParent
