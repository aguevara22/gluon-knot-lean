import ActiveArcParentClosedRange
import ActiveArcNonalternatingRefinement
import DirectGLSSW.DaughterRootAmplitude

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable

/-- Source closed auxiliary genericity transfers to the actual shortened parent.
For each parent nonalternating support, insert the first crossing with empty
child support; every actual closed parent component has a proved cyclically
identical actual original closed retained word. No daughter genericity is
assumed. -/
theorem parent_closedAuxiliary
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : Primitive.ClosedAuxiliary q hR) :
    Primitive.ClosedAuxiliary (parent q c hcut) (regular_parent q hR c hcut) := by
  intro T C hC
  have hEmpty : PolygonNonalternation.polygonNonalternating
      (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) ∅ := by
    intro d hd
    exact False.elim (Finset.not_mem_empty d hd)
  let V := nonalternatingSelectionEquiv q hR c hc hcut (⟨∅,hEmpty⟩,T)
  let U : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
  let D := parentClosedComponentMap q hR c hc hcut ∅ T.val ⟨C,hC⟩
  have hOriginal := hAux U D.val D.property
  have hrot := parentClosedComponentMap_word_isRotated q hR c hc hcut ∅ T.val ⟨C,hC⟩
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated hrot hOriginal

end DirectGLSSW.ActiveArc.CompatibleWords
