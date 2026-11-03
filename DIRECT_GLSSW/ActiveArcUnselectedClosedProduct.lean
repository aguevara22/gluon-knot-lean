import ActiveArcUnselectedSpectatorWeights

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW PermutationOrbits SingletonWords Split Cursor
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
variable (hRI : GLSSWRootIndependence)
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (hAux : Primitive.ClosedAuxiliary q hR)
variable (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
  PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
    (child_noTriple q hR c hc.1 hcut) S})
variable (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))
include hRI

/-- The distinguished selected closed factor is the literal child daughter
at anchor zero, with genericity derived from original ClosedAuxiliary. -/
theorem selected_cut_child_closedWeight :
    let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
    let I : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
    Primitive.closedWeight q hR hAux I
      (componentOf (incoming q hR.noTriple I.val) (Sum.inr (c,true))) =
    polygonAmplitude (DaughterFirstReturn.daughterVertex (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0))
      (child_auxiliaryGenericity q hR c hc hcut hAux S.val S.property (Sum.inl 0)) := by
  intro V I
  let C := componentOf (incoming q hR.noTriple I.val) (Sum.inr (c,true))
  have hC : C≠openComponent q hR.noTriple I.val :=
    selected_right_visit_closed q hR c hc hcut S.val T.val
  have hrot := retainedWord_isRotated_of_sameCycle q hR I.val
    (closedRoot q hR.noTriple I.val C hC) (Sum.inr (c,true))
    ((componentOf_eq_iff _ _ _).mp (closedRoot_spec q hR.noTriple I.val C hC).1)
  have hw := selected_child_word_at_cut q hR c hc hcut S.val T.val
  change List.ofFn (RetainedWords.vertex q hR I.val (Sum.inr (c,true))) =
    DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0) at hw
  rw [hw] at hrot
  change Primitive.closedWeight q hR hAux I C=_
  rw [Primitive.closedWeight,dif_pos hC]
  exact DaughterRootAmplitude.polygonAmplitude_ofFn_isRotated hRI (hAux I C hC) hrot

/-- Multiplication-only unsmoothing factorization on actual original closed
components. No amplitude is assumed nonzero and no division is used. -/
theorem unselected_closedWeight_product_insert :
    let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
    let U : Primitive.Support q hR := ⟨V.val,(pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr ⟨S.property,T.property⟩⟩
    let I : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
    polygonAmplitude (DaughterFirstReturn.daughterVertex (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0))
      (child_auxiliaryGenericity q hR c hc hcut hAux S.val S.property (Sum.inl 0)) *
      (∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple U.val),Primitive.closedWeight q hR hAux U D) =
      ∏ C ∈ Finset.univ.erase (openComponent q hR.noTriple I.val),Primitive.closedWeight q hR hAux I C := by
  intro V U I
  let p := incoming q hR.noTriple I.val
  let r := incoming q hR.noTriple U.val
  have hab := selected_cut_visits_separated q hR c hc hcut S.val T.val
  have hr := incoming_unselected_eq_swap q hR c U.val V.property.1
  have hleft : componentOf p (Sum.inr (c,false))=openComponent q hR.noTriple I.val :=
    selected_left_visit_open q hR c hc hcut S.val T.val
  have hleftU : componentOf r (Sum.inr (c,false))=openComponent q hR.noTriple U.val :=
    (unselected_cut_visits_open q hR c hc hcut S.val T.val).1
  have hp := join_spectator_product p r (Sum.inr (c,false)) (Sum.inr (c,true)) hab hr
    (Primitive.closedWeight q hR hAux I) (Primitive.closedWeight q hR hAux U)
    (fun C ha hb => unselected_spectator_closedWeight hRI q hR c hc hcut hAux S T C
      (fun h => ha (h.trans hleft.symm)) hb)
  have hw := selected_cut_child_closedWeight hRI q hR c hc hcut hAux S T
  change Primitive.closedWeight q hR hAux I (componentOf p (Sum.inr (c,true))) = _ at hw
  rw [hw] at hp
  simpa only [hleft,hleftU] using hp

/-- Full actual compatible closed-factor identity used by the unselected
support contribution: distinguished child A times all old closed factors
is the full child component product times the parent's closed product. -/
theorem compatible_unselected_closedWeight_product :
    let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
    let U : Primitive.Support q hR := ⟨V.val,(pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr ⟨S.property,T.property⟩⟩
    polygonAmplitude (DaughterFirstReturn.daughterVertex (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0))
      (child_auxiliaryGenericity q hR c hc hcut hAux S.val S.property (Sum.inl 0)) *
      (∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple U.val),Primitive.closedWeight q hR hAux U D) =
      GeometricSmoothingWeights.componentAmplitudeProduct (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux) S.val
        (child_auxiliaryGenericity q hR c hc hcut hAux) S.property *
      (∏ C ∈ Finset.univ.erase (openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T.val),
        Primitive.closedWeight (parent q c hcut) (regular_parent q hR c hcut)
          (parent_closedAuxiliary q hR c hc hcut hAux) T C) := by
  exact (unselected_closedWeight_product_insert hRI q hR c hc hcut hAux S T).trans
    (compatible_closedWeight_product hRI q hR c hc hcut hAux S T)

end DirectGLSSW.ActiveArc.CompatibleWords
