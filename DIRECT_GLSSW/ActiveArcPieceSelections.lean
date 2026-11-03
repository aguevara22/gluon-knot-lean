import ActiveArcCrossingPartition
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Preimage

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Cursor
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)

/-- Union of the actual two pieces' selected physical crossing labels. -/
def pieceSelections
    (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
    (T : Finset (Crossing (parent q c hcut))) : Finset (Crossing q) :=
  (S.disjSum T).map ⟨pieceCrossingToOriginal q hR c hc hcut,
    pieceCrossingToOriginal_injective q hR c hc hcut⟩

theorem pieceSelections_card
    (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
    (T : Finset (Crossing (parent q c hcut))) :
    (pieceSelections q hR c hc hcut S T).card=S.card+T.card := by
  rw [pieceSelections,Finset.card_map,Finset.card_disjSum]

theorem pieceSelections_injective : Function.Injective
    (fun p : Finset (PolygonCrossing (child q hR c hc.1 hcut)) ×
      Finset (Crossing (parent q c hcut)) => pieceSelections q hR c hc hcut p.1 p.2) := by
  intro x y h
  have hm:=Finset.map_injective ⟨pieceCrossingToOriginal q hR c hc hcut,
    pieceCrossingToOriginal_injective q hR c hc hcut⟩ h
  have hp:=Finset.disjSum_inj.mp hm
  exact Prod.ext hp.1 hp.2

/-- Range is an elementwise compatibility restriction only. Pairwise
nonalternation within the selected sets is not asserted by this helper. -/
theorem pieceSelections_range (U : Finset (Crossing q)) :
    (∃ S T, pieceSelections q hR c hc hcut S T=U) ↔
      ∀ d∈U, d≠c ∧ Compatible q hR c d := by
  constructor
  · rintro ⟨S,T,rfl⟩ d hd
    obtain ⟨e,_,he⟩:=Finset.mem_map.mp hd
    exact (pieceCrossing_range q hR c hc hcut d).mp ⟨e,he⟩
  · intro hU
    let f := pieceCrossingToOriginal q hR c hc hcut
    have hf := pieceCrossingToOriginal_injective q hR c hc hcut
    let V := U.preimage f hf.injOn
    refine ⟨V.toLeft,V.toRight,?_⟩
    unfold pieceSelections
    rw [Finset.toLeft_disjSum_toRight]
    apply Finset.ext
    intro d
    constructor
    · intro hd
      obtain ⟨e,he,hed⟩:=Finset.mem_map.mp hd
      have hm:=Finset.mem_preimage.mp he
      exact hed ▸ hm
    · intro hd
      obtain ⟨e,he⟩:=(pieceCrossing_range q hR c hc hcut d).mpr (hU d hd)
      apply Finset.mem_map.mpr
      refine ⟨e,Finset.mem_preimage.mpr ?_,he⟩
      change pieceCrossingToOriginal q hR c hc hcut e∈U
      rw [he]
      exact hd

/-- Exact cardinal-preserving partition of compatible finite selections.
Restricting it to pairwise nonalternating supports remains a separate theorem. -/
def compatibleSelectionEquiv :
    (Finset (PolygonCrossing (child q hR c hc.1 hcut)) × Finset (Crossing (parent q c hcut))) ≃
      {U : Finset (Crossing q) // ∀ d∈U, d≠c ∧ Compatible q hR c d} :=
  Equiv.ofBijective (fun p => ⟨pieceSelections q hR c hc hcut p.1 p.2,
    (pieceSelections_range q hR c hc hcut _).mp ⟨p.1,p.2,rfl⟩⟩) ⟨by
    intro p r h
    exact pieceSelections_injective q hR c hc hcut (congrArg Subtype.val h),by
    intro U
    obtain ⟨S,T,hST⟩:=(pieceSelections_range q hR c hc hcut U.val).mpr U.property
    exact ⟨(S,T),Subtype.ext hST⟩⟩

end DirectGLSSW.ActiveArc.Split
