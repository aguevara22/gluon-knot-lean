import ActiveArcTinyParentIndexedWord

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive OpenFirstEdgeGeometry Nonalternation RetainedWords PhysicalSegments PermutationOrbits
attribute [local instance] Classical.propDecidable

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (η : ℝ) (hη : 0<η) (hη1 : η<1)

/-- Inserting the actual tiny start identifies all actual incoming components. -/
def tinyParentComponentEquiv (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) :
    Components (ParentArc q c hcut) (ParentRegular q hR c hcut) T ≃
      Components (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
        (tinySupportOfParent q hR c hc hcut η hη hη1 T) :=
  PermutationInsertion.insertedComponentEquiv
    (incoming (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val)
    (incoming (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1).noTriple
      (parentTinySelection q c hcut η T.val))
    (start (ParentArc q c hcut)) (start (TinyArc q c hcut η))
    (tinyParentEventInsertionEquiv (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1))
    (tinyParent_incoming_start (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T)
    (tinyParent_incoming_step (q:=q) (hR:=hR) (c:=c) (hc:=hc)
      (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T)

theorem tinyParentComponentEquiv_componentOf (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) (x : Event (ParentArc q c hcut)) :
    tinyParentComponentEquiv q hR c hc hcut η hη hη1 T
      (componentOf (incoming (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val) x) =
    componentOf (incoming (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1).noTriple
      (parentTinySelection q c hcut η T.val)) (parentEventIntoTiny q c hcut η x) := rfl

theorem tinyParentComponentEquiv_open (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) :
    tinyParentComponentEquiv q hR c hc hcut η hη hη1 T
      (openComponent (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val) =
    openComponent (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1).noTriple
      (parentTinySelection q c hcut η T.val) := by
  exact PermutationInsertion.insertedComponentEquiv_extra _ _ _ _ _ _ _

/-- The actual component equivalence restricts to all non-open components. -/
def tinyParentClosedComponentEquiv (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) :
    {C : Components (ParentArc q c hcut) (ParentRegular q hR c hcut) T //
      C ≠ openComponent (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val} ≃
    {C : Components (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (tinySupportOfParent q hR c hc hcut η hη hη1 T) //
      C ≠ openComponent (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1).noTriple
        (parentTinySelection q c hcut η T.val)} :=
  (tinyParentComponentEquiv q hR c hc hcut η hη hη1 T).subtypeEquiv (by
    intro C
    rw [← tinyParentComponentEquiv_open q hR c hc hcut η hη hη1 T]
    exact ((tinyParentComponentEquiv q hR c hc hcut η hη hη1 T).injective.ne_iff).symm)

end DirectGLSSW.ActiveArc.LiteralTinyParent
