import ActiveArcChildAuxiliary

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable

/-- Under RI, an actual child component contributes the same closed amplitude
to the original selected-cut support. Both genericity proofs are derived
from the explicit original auxiliary condition. -/
theorem childComponentMap_closedWeight
    (hRI : GLSSWRootIndependence)
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : Primitive.ClosedAuxiliary q hR)
    (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
      PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S})
    (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))
    (C : Component (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S.val)) :
    let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
    let U : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
    let D := childComponentMap q hR c hc hcut hAux S.val T.val C
    Primitive.closedWeight q hR hAux U D.val=
      GeometricSmoothingWeights.componentAmplitude (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux) S.val
        (child_auxiliaryGenericity q hR c hc hcut hAux) S.property C := by
  let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
  let U : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
  let D := childComponentMap q hR c hc hcut hAux S.val T.val C
  change Primitive.closedWeight q hR hAux U D.val=_
  have hD : D.val≠openComponent q hR.noTriple U.val := D.property
  rw [Primitive.closedWeight,dif_pos hD]
  exact DaughterRootAmplitude.polygonAmplitude_ofFn_isRotated hRI
    (hAux U D.val D.property)
    (childComponentMap_word_isRotated q hR c hc hcut hAux S.val T.val C)

end DirectGLSSW.ActiveArc.CompatibleWords
