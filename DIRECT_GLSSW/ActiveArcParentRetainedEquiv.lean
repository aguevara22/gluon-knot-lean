import ActiveArcParentRetainedRange
import ActiveArcParentEventOrder

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

/-- Exact reduced retained-event correspondence, excluding only the extra
original initial anchor. This is not a bijection of the full event carriers. -/
def parentRetainedEquiv :
    {x : Event (parent q c hcut) // retained (parent q c hcut) T x} ≃
    {x : Event q // retained q (insert c (pieceSelections q hR c hc hcut S T)) x ∧
      (Nonalternation.eventEnumeration q hR).symm x ∈ complementSide (leftRank q hR c) (rightRank q hR c) ∧
      x≠start q} :=
  Equiv.ofBijective (fun x => ⟨parentEventMap q hR c hc hcut x.val,
    (parentEventMap_retained q hR c hc hcut S T x.val).mpr x.property,
    parentEventMap_in_complement q hR c hc hcut x.val,
    parentEventMap_ne_start q hR c hc hcut x.val⟩) ⟨by
    intro x y he
    exact Subtype.ext (parentEventMap_injective q hR c hc hcut (congrArg Subtype.val he)),by
    intro y
    rcases (retained_complement_range q hR c hc hcut S T y.val).mp
      ⟨y.property.1,y.property.2.1⟩ with he|⟨x,hx,hxy⟩
    · exact False.elim (y.property.2.2 he)
    · exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩⟩

theorem parentRetainedEquiv_point
    (x : {x : Event (parent q c hcut) // retained (parent q c hcut) T x}) :
    eventPoint q (parentRetainedEquiv q hR c hc hcut S T x).val=eventPoint (parent q c hcut) x.val :=
  parentEventMap_point q hR c hc hcut x.val

theorem parentRetainedEquiv_lt
    (x y : {x : Event (parent q c hcut) // retained (parent q c hcut) T x}) :
    (eventOrder q hR.noTriple).lt (parentRetainedEquiv q hR c hc hcut S T x).val
      (parentRetainedEquiv q hR c hc hcut S T y).val ↔
    (eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple).lt x.val y.val :=
  parentEventMap_lt q hR c hc hcut x.val y.val

/-- Parent support membership transfers along its literal crossing map. -/
theorem pieceSelections_parent_pairing (x : Event (parent q c hcut)) :
    pairing q (pieceSelections q hR c hc hcut S T) (parentEventMap q hR c hc hcut x)=
      parentEventMap q hR c hc hcut (pairing (parent q c hcut) T x) := by
  cases x with
  | inl i =>
    by_cases hi : i=0
    · have hn : c∉pieceSelections q hR c hc hcut S T := by
        intro hh
        have hp := (pieceSelections_range q hR c hc hcut _).mp ⟨S,T,rfl⟩ c hh
        exact hp.1 rfl
      simp [pairing,pairingMap,parentEventMap,hi,hn]
    · simp [pairing,pairingMap,parentEventMap,hi]
  | inr v =>
    change (if parentCrossingToOriginal q c hcut v.1∈pieceSelections q hR c hc hcut S T then
      (Sum.inr (parentCrossingToOriginal q c hcut v.1,!v.2) : Event q) else
      Sum.inr (parentCrossingToOriginal q c hcut v.1,v.2))=
      parentEventMap q hR c hc hcut
        (if v.1∈T then Sum.inr (v.1,!v.2) else Sum.inr v)
    simp only [pieceSelections_parent_mem q hR c hc hcut S T]
    split_ifs <;> rfl

end DirectGLSSW.ActiveArc.CompatibleWords
