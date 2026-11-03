import ActiveArcParentRetainedEquiv
import ActiveArcOrderedInsertion

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

abbrev ParentRetained := {x : Event (parent q c hcut) // retained (parent q c hcut) T x}
abbrev ComplementRetained := {x : Event q //
  retained q (insert c (pieceSelections q hR c hc hcut S T)) x ∧
  (Nonalternation.eventEnumeration q hR).symm x ∈ complementSide (leftRank q hR c) (rightRank q hR c)}

def parentRetainedStart : ParentRetained q c hcut T :=
  ⟨start (parent q c hcut),(endpoints_retained _ T).1⟩

def complementRetainedStart : ComplementRetained q hR c hc hcut S T :=
  ⟨start q,(retained_complement_range q hR c hc hcut S T (start q)).mpr (Or.inl rfl)⟩

def parentRetainedOrderIso :
    letI := eventOrder q hR.noTriple
    letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
    ParentRetained q c hcut T ≃o
      {y : ComplementRetained q hR c hc hcut S T // y≠complementRetainedStart q hR c hc hcut S T} := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
  let F : {x : Event q // retained q (insert c (pieceSelections q hR c hc hcut S T)) x ∧
      (Nonalternation.eventEnumeration q hR).symm x ∈ complementSide (leftRank q hR c) (rightRank q hR c) ∧
      x≠start q} ≃ {y : ComplementRetained q hR c hc hcut S T // y≠complementRetainedStart q hR c hc hcut S T} :=
    { toFun := fun x => ⟨⟨x.val,x.property.1,x.property.2.1⟩,
        fun he => x.property.2.2 (congrArg Subtype.val he)⟩
      invFun := fun y => ⟨y.val.val,y.val.property.1,y.val.property.2,
        fun he => y.property (Subtype.ext he)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  refine { toEquiv := (parentRetainedEquiv q hR c hc hcut S T).trans F
           map_rel_iff' := ?_ }
  intro x y
  change (parentEventMap q hR c hc hcut x.val≤parentEventMap q hR c hc hcut y.val) ↔ x.val≤y.val
  simpa only [not_lt] using not_congr (parentEventMap_lt q hR c hc hcut y.val x.val)

theorem parentRetainedOrderIso_val (x : ParentRetained q c hcut T) :
    (parentRetainedOrderIso q hR c hc hcut S T x).val.val=parentEventMap q hR c hc hcut x.val := rfl

theorem parentRetainedStart_le :
    letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
    ∀ x : ParentRetained q c hcut T, parentRetainedStart q c hcut T≤x := by
  intro x
  exact start_le (parent q c hcut) (regular_parent q hR c hcut).noTriple x.val

theorem complementRetainedStart_le :
    letI := eventOrder q hR.noTriple
    ∀ x : ComplementRetained q hR c hc hcut S T, complementRetainedStart q hR c hc hcut S T≤x := by
  intro x
  exact start_le q hR.noTriple x.val

/-- The extra literal initial anchor precedes exactly the mapped parent start
in the reduced singleton-complement order. This is an unsmoothed carrier step. -/
theorem complementRetained_successor_start :
    letI := eventOrder q hR.noTriple
    letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
    orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T)
      (complementRetainedStart q hR c hc hcut S T)=
      (parentRetainedOrderIso q hR c hc hcut S T (parentRetainedStart q c hcut T)).val := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
  exact OrderedInsertion.successor_extra (parentRetainedStart q c hcut T)
    (complementRetainedStart q hR c hc hcut S T) (parentRetainedOrderIso q hR c hc hcut S T)
    (parentRetainedStart_le q hR c hcut T) (complementRetainedStart_le q hR c hc hcut S T)

/-- Every other reduced ordered step intertwines, with the exact extra-anchor
wrap. Smoothing is not inferred solely from this order statement. -/
theorem complementRetained_successor_image (x : ParentRetained q c hcut T) :
    letI := eventOrder q hR.noTriple
    letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
    orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T)
      (parentRetainedOrderIso q hR c hc hcut S T x).val=
      if orderedCyclicSuccessor (ParentRetained q c hcut T) x=parentRetainedStart q c hcut T then
        complementRetainedStart q hR c hc hcut S T
      else (parentRetainedOrderIso q hR c hc hcut S T
        (orderedCyclicSuccessor (ParentRetained q c hcut T) x)).val := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
  have hh := OrderedInsertion.successor_image (parentRetainedStart q c hcut T)
    (complementRetainedStart q hR c hc hcut S T) (parentRetainedOrderIso q hR c hc hcut S T)
    (parentRetainedStart_le q hR c hcut T) (complementRetainedStart_le q hR c hc hcut S T) x
  by_cases he : orderedCyclicSuccessor (ParentRetained q c hcut T) x=parentRetainedStart q c hcut T
  · simpa only [if_pos he] using hh
  · simpa only [if_neg he] using hh

end DirectGLSSW.ActiveArc.CompatibleWords
