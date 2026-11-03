import ActiveArcUnselectedSpectatorWords
import OrbitJoinSpectatorProduct
import ActiveArcCompatibleClosedProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW PermutationOrbits SingletonWords Split Cursor
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

/-- Actual closed spectator weights are unchanged when the compatible cut
is unselected. Root rotation is the only use of RI. -/
theorem unselected_spectator_closedWeight :
    let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
    let U : Primitive.Support q hR := ⟨V.val,(pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr ⟨S.property,T.property⟩⟩
    let I : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
    let p := incoming q hR.noTriple I.val
    let r := incoming q hR.noTriple U.val
    let hab := selected_cut_visits_separated q hR c hc hcut S.val T.val
    let hr := incoming_unselected_eq_swap q hR c U.val V.property.1
    ∀ C : Component p, C≠openComponent q hR.noTriple I.val →
      C≠componentOf p (Sum.inr (c,true)) →
      Primitive.closedWeight q hR hAux U
        (joinComponentMapTo p r (Sum.inr (c,false)) (Sum.inr (c,true)) hab hr C) =
      Primitive.closedWeight q hR hAux I C := by
  intro V U I p r hab hr C hC hCb
  let D := joinComponentMapTo p r (Sum.inr (c,false)) (Sum.inr (c,true)) hab hr C
  have hleft : componentOf p (Sum.inr (c,false))=openComponent q hR.noTriple I.val :=
    selected_left_visit_open q hR c hc hcut S.val T.val
  have hleftU : componentOf r (Sum.inr (c,false))=openComponent q hR.noTriple U.val :=
    (unselected_cut_visits_open q hR c hc hcut S.val T.val).1
  have hCa : C≠componentOf p (Sum.inr (c,false)) := by simpa only [hleft] using hC
  have hD : D≠openComponent q hR.noTriple U.val := by
    rw [← hleftU]
    intro h
    exact ((joinComponentMapTo_eq_joined_iff p r _ _ hab hr C).mp h).elim hCa hCb
  let x := closedRoot q hR.noTriple I.val C hC
  have hx : componentOf p x=C := (closedRoot_spec q hR.noTriple I.val C hC).1
  have hxD : componentOf r x=D := by
    change componentOf r x=joinComponentMapTo p r _ _ hab hr C
    rw [← hx,joinComponentMapTo_componentOf]
  have ha : ¬p.SameCycle x (Sum.inr (c,false)) :=
    fun h => hCa (hx.symm.trans ((componentOf_eq_iff _ _ _).mpr h))
  have hb : ¬p.SameCycle x (Sum.inr (c,true)) :=
    fun h => hCb (hx.symm.trans ((componentOf_eq_iff _ _ _).mpr h))
  have hword := unselected_spectator_pointWord_eq q hR c hc hcut S.val T.val x ha hb
  have hrot := retainedWord_isRotated_of_sameCycle q hR U.val
    (closedRoot q hR.noTriple U.val D hD) x
    ((componentOf_eq_iff _ _ _).mp ((closedRoot_spec q hR.noTriple U.val D hD).1.trans hxD.symm))
  change List.ofFn (RetainedWords.vertex q hR U.val x)=
    List.ofFn (RetainedWords.vertex q hR I.val x) at hword
  rw [hword] at hrot
  change Primitive.closedWeight q hR hAux U D=Primitive.closedWeight q hR hAux I C
  rw [Primitive.closedWeight,dif_pos hD,Primitive.closedWeight,dif_pos hC]
  exact DaughterRootAmplitude.polygonAmplitude_ofFn_isRotated hRI (hAux U D hD) hrot

end DirectGLSSW.ActiveArc.CompatibleWords
