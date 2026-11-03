import ActiveArcParentClosedAuxiliary

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable

/-- An actual closed parent component contributes the same amplitude to the
original selected-cut support and to the actual shortened parent. Both
auxiliary proofs are supplied by the original auxiliary condition. -/
theorem parentClosedComponentMap_closedWeight
    (hRI : GLSSWRootIndependence)
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : Primitive.ClosedAuxiliary q hR)
    (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
      PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S})
    (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))
    (C : {C : Primitive.Components (parent q c hcut) (regular_parent q hR c hcut) T //
      C ≠ openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T.val}) :
    let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
    let U : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
    let D := parentClosedComponentMap q hR c hc hcut S.val T.val C
    Primitive.closedWeight q hR hAux U D.val =
      Primitive.closedWeight (parent q c hcut) (regular_parent q hR c hcut)
        (parent_closedAuxiliary q hR c hc hcut hAux) T C.val := by
  let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
  let U : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
  let D := parentClosedComponentMap q hR c hc hcut S.val T.val C
  change Primitive.closedWeight q hR hAux U D.val = _
  have hD : D.val ≠ openComponent q hR.noTriple U.val := D.property
  rw [Primitive.closedWeight, dif_pos hD,
    Primitive.closedWeight, dif_pos C.property]
  exact DaughterRootAmplitude.polygonAmplitude_ofFn_isRotated hRI
    (hAux U D.val D.property)
    (parentClosedComponentMap_word_isRotated q hR c hc hcut S.val T.val C)

end DirectGLSSW.ActiveArc.CompatibleWords
