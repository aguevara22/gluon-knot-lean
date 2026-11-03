import ActiveArcSupportNonalternation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)

theorem child_parent_compatible
    (d : PolygonCrossing (child q hR c hc.1 hcut)) (e : Crossing (parent q c hcut)) :
    Compatible q hR (childCrossingToOriginal q hR c hc.1 hcut d) (parentCrossingToOriginal q c hcut e) := by
  have hd:=childCrossingToOriginal_inChild q hR c hc.1 hcut d
  have he:=parentCrossingToOriginal_inParent q hR c hcut e
  have hdc : childCrossingToOriginal q hR c hc.1 hcut d≠c := by
    intro hh;rw [hh] at hd;exact crossing_not_inChild q c hc.1 hd
  have hleft:=(right_visit_before_cut_iff q hR c hc hcut _ hdc).mpr hd
  have hright:=(cut_before_left_visit_iff q hR c hcut _).mpr he
  apply compatible_of_separated q hR
  letI : LinearOrder (Event q) := eventOrder q hR.noTriple
  exact lt_trans hleft hright

/-- Restriction of the actual compatible selection split to pairwise
nonalternating supports, with literal polygon/open-arc predicates. -/
theorem pieceSelections_nonalternating_iff
    (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
    (T : Finset (Crossing (parent q c hcut))) :
    Nonalternation.Nonalternating q hR (pieceSelections q hR c hc hcut S T) ↔
      PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S ∧
      Nonalternation.Nonalternating (parent q c hcut) (regular_parent q hR c hcut) T := by
  rw [child_nonalternating_iff,parent_nonalternating_iff]
  constructor
  · intro h
    constructor
    · intro d hd e he hde
      apply h (childCrossingToOriginal q hR c hc.1 hcut d)
        (Finset.mem_map.mpr ⟨Sum.inl d,Finset.inl_mem_disjSum.mpr hd,rfl⟩)
        (childCrossingToOriginal q hR c hc.1 hcut e)
        (Finset.mem_map.mpr ⟨Sum.inl e,Finset.inl_mem_disjSum.mpr he,rfl⟩)
      exact fun hh => hde (childCrossingToOriginal_injective q hR c hc.1 hcut hh)
    · intro d hd e he hde
      apply h (parentCrossingToOriginal q c hcut d)
        (Finset.mem_map.mpr ⟨Sum.inr d,Finset.inr_mem_disjSum.mpr hd,rfl⟩)
        (parentCrossingToOriginal q c hcut e)
        (Finset.mem_map.mpr ⟨Sum.inr e,Finset.inr_mem_disjSum.mpr he,rfl⟩)
      exact fun hh => hde (parentCrossingToOriginal_injective q c hcut hh)
  · rintro ⟨hS,hT⟩ d hd e he hde
    obtain ⟨x,hx,rfl⟩:=Finset.mem_map.mp hd
    obtain ⟨y,hy,rfl⟩:=Finset.mem_map.mp he
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact hS x (Finset.inl_mem_disjSum.mp hx) y (Finset.inl_mem_disjSum.mp hy)
          (fun hh => hde (congrArg (childCrossingToOriginal q hR c hc.1 hcut) hh))
      | inr y => exact child_parent_compatible q hR c hc hcut x y
    | inr x =>
      cases y with
      | inl y =>
        exact (compatible_symm q hR _ _).mpr (child_parent_compatible q hR c hc hcut y x)
      | inr y =>
        exact hT x (Finset.inr_mem_disjSum.mp hx) y (Finset.inr_mem_disjSum.mp hy)
          (fun hh => hde (congrArg (parentCrossingToOriginal q c hcut) hh))

theorem cut_not_mem_pieceSelections
    (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
    (T : Finset (Crossing (parent q c hcut))) : c∉pieceSelections q hR c hc hcut S T := by
  intro hm
  exact ((pieceSelections_range q hR c hc hcut _).mp ⟨S,T,rfl⟩ c hm).1 rfl

theorem insert_pieceSelections_nonalternating_iff
    (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
    (T : Finset (Crossing (parent q c hcut))) :
    Nonalternation.Nonalternating q hR (insert c (pieceSelections q hR c hc hcut S T)) ↔
      PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S ∧
      Nonalternation.Nonalternating (parent q c hcut) (regular_parent q hR c hcut) T := by
  rw [nonalternating_insert_iff q hR c _ (cut_not_mem_pieceSelections q hR c hc hcut S T)]
  have hcompat : ∀ d∈pieceSelections q hR c hc hcut S T, Compatible q hR c d := by
    intro d hd
    exact ((pieceSelections_range q hR c hc hcut _).mp ⟨S,T,rfl⟩ d hd).2
  rw [and_iff_left hcompat,pieceSelections_nonalternating_iff]

/-- Exact physical source support refinement after inserting the first cut.
Its target excludes the already inserted label c and uses the original literal
nonalternation predicate. No retained-word or amplitude conclusion is assumed. -/
def nonalternatingSelectionEquiv :
    ({S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
      PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S} ×
     {T : Finset (Crossing (parent q c hcut)) //
      Nonalternation.Nonalternating (parent q c hcut) (regular_parent q hR c hcut) T}) ≃
    {U : Finset (Crossing q) // c∉U ∧ Nonalternation.Nonalternating q hR (insert c U)} :=
  Equiv.ofBijective (fun p => ⟨pieceSelections q hR c hc hcut p.1.val p.2.val,
    cut_not_mem_pieceSelections q hR c hc hcut p.1.val p.2.val,
    (insert_pieceSelections_nonalternating_iff q hR c hc hcut p.1.val p.2.val).mpr
      ⟨p.1.property,p.2.property⟩⟩) ⟨by
    intro p r h
    have hp : (p.1.val,p.2.val)=(r.1.val,r.2.val) :=
      pieceSelections_injective q hR c hc hcut (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hp)) (Subtype.ext (congrArg Prod.snd hp)),by
    intro U
    have h:= (nonalternating_insert_iff q hR c U.val U.property.1).mp U.property.2
    have hr : ∀ d∈U.val, d≠c ∧ Compatible q hR c d := by
      intro d hd
      exact ⟨fun hh => U.property.1 (hh ▸ hd),h.2 d hd⟩
    obtain ⟨S,T,hST⟩ := (pieceSelections_range q hR c hc hcut U.val).mpr hr
    have hpieces := (pieceSelections_nonalternating_iff q hR c hc hcut S T).mp (hST.symm ▸ h.1)
    exact ⟨(⟨S,hpieces.1⟩,⟨T,hpieces.2⟩),Subtype.ext hST⟩⟩

theorem nonalternatingSelectionEquiv_card
    (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
      PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S})
    (T : {T : Finset (Crossing (parent q c hcut)) //
      Nonalternation.Nonalternating (parent q c hcut) (regular_parent q hR c hcut) T}) :
    (nonalternatingSelectionEquiv q hR c hc hcut (S,T)).val.card=S.val.card+T.val.card :=
  pieceSelections_card q hR c hc hcut S.val T.val

end DirectGLSSW.ActiveArc.Split
