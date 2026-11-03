import ActiveArcParentClosedAmplitude

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable

/-- The product of actual original closed-component weights whose canonical
retained roots lie in the singleton complement is the product over the actual
closed components of the shortened parent. -/
theorem parentClosedComplement_closedWeight_product
    (hRI : GLSSWRootIndependence)
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : Primitive.ClosedAuxiliary q hR)
    (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
      PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S})
    (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut)) :
    let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
    let U : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
    (∏ D : {D : {D : Primitive.Components q hR U //
        D ≠ openComponent q hR.noTriple U.val} //
        (Nonalternation.eventEnumeration q hR).symm
          (closedRoot q hR.noTriple U.val D.val D.property) ∈
          complementSide (leftRank q hR c) (rightRank q hR c)},
      Primitive.closedWeight q hR hAux U D.val.val) =
    ∏ C : {C : Primitive.Components (parent q c hcut) (regular_parent q hR c hcut) T //
        C ≠ openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T.val},
      Primitive.closedWeight (parent q c hcut) (regular_parent q hR c hcut)
        (parent_closedAuxiliary q hR c hc hcut hAux) T C.val := by
  let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
  let U : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
  let E := parentClosedComplementEquiv q hR c hc hcut S.val T.val
  let originalWeight := fun D : {D : {D : Primitive.Components q hR U //
      D ≠ openComponent q hR.noTriple U.val} //
      (Nonalternation.eventEnumeration q hR).symm
        (closedRoot q hR.noTriple U.val D.val D.property) ∈
        complementSide (leftRank q hR c) (rightRank q hR c)} =>
    Primitive.closedWeight q hR hAux U D.val.val
  let parentWeight := fun C : {C : Primitive.Components
      (parent q c hcut) (regular_parent q hR c hcut) T //
      C ≠ openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T.val} =>
    Primitive.closedWeight (parent q c hcut) (regular_parent q hR c hcut)
      (parent_closedAuxiliary q hR c hc hcut hAux) T C.val
  calc
    (∏ D, originalWeight D) = ∏ C, originalWeight (E C) := by
      exact (Fintype.prod_equiv E (fun C => originalWeight (E C)) originalWeight
        (by intro C; rfl)).symm
    _ = ∏ C, parentWeight C := by
      apply Finset.prod_congr rfl
      intro C hC
      have hweight := parentClosedComponentMap_closedWeight hRI q hR c hc hcut hAux S T C
      simpa only [parentClosedComplementEquiv_val] using hweight

end DirectGLSSW.ActiveArc.CompatibleWords
