import ActiveArcCornerPointWords

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Primitive RetainedWords PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)

/-- Inserting the actual original start identifies all actual incoming components. -/
def cornerComponentEquiv (T : Nonalternation.Support (suffix q)
    (regular_suffix q hR)) :
    Components (suffix q) (regular_suffix q hR) T ≃
      Components q hR
        (firstEdgeFreeSupportEquiv q hfree hR T) :=
  PermutationInsertion.insertedComponentEquiv
    (incoming (suffix q) (regular_suffix q hR).noTriple T.val)
    (incoming q hR.noTriple
      (firstEdgeFreeSupportEquiv q hfree hR T).val)
    (start (suffix q)) (start q)
    (cornerEventInsertionEquiv (q:=q) (hR:=hR) (hfree:=hfree))
    (corner_incoming_start (q:=q) (hR:=hR) (hfree:=hfree) T)
    (corner_incoming_step (q:=q) (hR:=hR) (hfree:=hfree) T)

theorem cornerComponentEquiv_componentOf (T : Nonalternation.Support (suffix q)
    (regular_suffix q hR)) (x : Event (suffix q)) :
    cornerComponentEquiv q hR hfree T
      (componentOf (incoming (suffix q) (regular_suffix q hR).noTriple T.val) x) =
    componentOf (incoming q hR.noTriple
      (firstEdgeFreeSupportEquiv q hfree hR T).val) (suffixEventIntoOriginal q hfree x) := rfl

theorem cornerComponentEquiv_open (T : Nonalternation.Support (suffix q)
    (regular_suffix q hR)) :
    cornerComponentEquiv q hR hfree T
      (openComponent (suffix q) (regular_suffix q hR).noTriple T.val) =
    openComponent q hR.noTriple
      (firstEdgeFreeSupportEquiv q hfree hR T).val := by
  exact PermutationInsertion.insertedComponentEquiv_extra _ _ _ _ _ _ _

/-- The actual component equivalence restricts to all non-open components. -/
def cornerClosedComponentEquiv (T : Nonalternation.Support (suffix q)
    (regular_suffix q hR)) :
    {C : Components (suffix q) (regular_suffix q hR) T //
      C ≠ openComponent (suffix q) (regular_suffix q hR).noTriple T.val} ≃
    {C : Components q hR
      (firstEdgeFreeSupportEquiv q hfree hR T) //
      C ≠ openComponent q hR.noTriple
        (firstEdgeFreeSupportEquiv q hfree hR T).val} :=
  (cornerComponentEquiv q hR hfree T).subtypeEquiv (by
    intro C
    rw [← cornerComponentEquiv_open q hR hfree T]
    exact ((cornerComponentEquiv q hR hfree T).injective.ne_iff).symm)

end DirectGLSSW.ActiveArc.Split
