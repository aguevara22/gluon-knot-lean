import ActiveArcCompatibleRightGap
import ActiveArcOutgoingCarrier

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW Cursor RetainedWords PhysicalSegments OpenCarrier Split SingletonWords
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (hAux : Primitive.ClosedAuxiliary q hR)
variable (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
  PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
    (child_noTriple q hR c hc.1 hcut) S})
variable (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))
include hAux

/-- Among every actual nonalternating retained side, the crossed physical
carrier occurs exactly at the final side of the distinguished child prefix.
No event-isolation or determinant nonvanishing premise is used. -/
theorem compatible_crossed_carrier_iff :
    let U : Primitive.Support q hR := ⟨pieceSelections q hR c hc hcut S.val T.val,
      (pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr ⟨S.property,T.property⟩⟩
    let k := (DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0)).length-1
    ∀ i : Fin (openCount q hR U.val-1),
      openSideCarrier q hR U.val i=c.val.2 ↔ i.val=k := by
  intro U k
  obtain ⟨hk,hkn,hv0,hv1⟩ := compatible_right_visit_gap q hR c hc hcut hAux S T
  change 0<k at hk
  change k+1<openCount q hR U.val at hkn
  let j : Fin (openCount q hR U.val-1) := ⟨k,by omega⟩
  let i : Fin (openCount q hR U.val) := ⟨k,by omega⟩
  let z := enumeration q hR U.val (start q) i
  have hz : eventAt q hR U.val (start q) z.val ≠ terminal q :=
    open_nonlast_ne_terminal q hR U.val i hkn
  have hv1' : (eventOrder q hR.noTriple).lt (Sum.inr (c,true))
      (eventAt q hR U.val (start q) (nextCorner q hR U.val (start q) z).val) := by
    rw [open_nextCorner_event q hR U.val i hkn]
    exact hv1
  have hj : openSideCarrier q hR U.val j=c.val.2 :=
    retained_visit_interval_outgoingEdge q hR U.val (start q) z hz (c,true) hv0 hv1'
  intro r
  constructor
  · intro hr
    have he := openSideCarrier_injective q hR U.val U.property (hr.trans hj.symm)
    exact congrArg Fin.val he
  · intro hr
    have he : r=j := Fin.ext hr
    exact he ▸ hj


end DirectGLSSW.ActiveArc.CompatibleWords
