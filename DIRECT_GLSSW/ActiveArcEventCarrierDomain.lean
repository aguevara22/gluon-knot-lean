import ActiveArcUniqueCrossedCarrier
import ActiveArcOpenSideGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW RetainedWords OpenCarrier

/-- The finite auxiliary determinant family on an actual unselected event word.
Only the triple consisting of the moved endpoint and the endpoints of an
actual side on the right crossing carrier is permitted to vanish. This is a
geometric domain condition, not a jump or density assertion. -/
def EventCarrierNonvanishing {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hR : Regular q) (c : Crossing q) (U : Support q hR) : Prop :=
  ∀ (i j l : ℕ) (hij : i<j) (hjl : j<l) (hlN : l≤openCount q hR U.val-1),
    (i≠0 ∨ l≠j+1 ∨
      openSideCarrier q hR U.val ⟨j,lt_of_lt_of_le hjl hlN⟩≠c.val.2) →
    polygonHDet (eventOpenWord q hR U c) i j l≠0

/-- With no retained side on the crossed carrier the finite domain condition
is ordinary genericity of the entire actual event word. -/
theorem eventCarrierNonvanishing_core_of_no_carrier
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (U : Support q hR)
    (hF : EventCarrierNonvanishing q hR c U)
    (hno : ∀ i : Fin (openCount q hR U.val-1), openSideCarrier q hR U.val i≠c.val.2) :
    ShortEdgeSignStability.CoreHGeneric (eventOpenWord q hR U c) (openCount q hR U.val-1) := by
  intro i j l hij hjl hlN
  exact hF i j l hij hjl hlN (Or.inr (Or.inr (hno _)))

/-- Carrier injectivity makes any permitted carrier event isolated among
all sorted triples of the actual event word. -/
theorem eventCarrierNonvanishing_isolated_of_carrier
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (U : Support q hR)
    (hF : EventCarrierNonvanishing q hR c U)
    (k : Fin (openCount q hR U.val-1)) (hk : openSideCarrier q hR U.val k=c.val.2) :
    ∀ i j l, i<j → j<l → l≤openCount q hR U.val-1 →
      (i≠0 ∨ j≠k.val ∨ l≠k.val+1) → polygonHDet (eventOpenWord q hR U c) i j l≠0 := by
  intro i j l hij hjl hlN hexc
  apply hF i j l hij hjl hlN
  by_cases hi : i=0
  · right
    by_cases hl : l=j+1
    · right
      intro hcarr
      have hjk := congrArg Fin.val
        (openSideCarrier_injective q hR U.val U.property (hcarr.trans hk.symm))
      rcases hexc with h|h|h
      · exact h hi
      · exact h hjk
      · exact h (hl.trans (congrArg (fun t : ℕ => t+1) hjk))
    · exact Or.inl hl
  · exact Or.inl hi

end DirectGLSSW.ActiveArc.Primitive

namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW Cursor RetainedWords OpenCarrier Split SingletonWords Primitive

/-- The literal finite carrier-domain condition supplies the exact isolation
premise of the compiled compatible actual-current jump. -/
theorem compatible_eventCarrierNonvanishing_isolated
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : ClosedAuxiliary q hR)
    (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
      PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S})
    (T : Support (parent q c hcut) (regular_parent q hR c hcut)) :
    let U : Support q hR := ⟨pieceSelections q hR c hc hcut S.val T.val,
      (pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr ⟨S.property,T.property⟩⟩
    let k := (DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0)).length-1
    EventCarrierNonvanishing q hR c U →
      ∀ i j l, i<j → j<l → l≤openCount q hR U.val-1 →
        (i≠0 ∨ j≠k ∨ l≠k+1) → polygonHDet (eventOpenWord q hR U c) i j l≠0 := by
  intro U k hF
  obtain ⟨hk,hkn,_⟩ := compatible_right_visit_gap q hR c hc hcut hAux S T
  change k+1<openCount q hR U.val at hkn
  let z : Fin (openCount q hR U.val-1) := ⟨k,by omega⟩
  have hz : openSideCarrier q hR U.val z=c.val.2 :=
    (compatible_crossed_carrier_iff q hR c hc hcut hAux S T z).mpr rfl
  exact eventCarrierNonvanishing_isolated_of_carrier q hR c U hF z hz

end DirectGLSSW.ActiveArc.CompatibleWords
