import ActiveArcChildClosedRange

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable

/-- Original closed auxiliary implies the actual child's literal all-supports,
all-roots auxiliary condition. Child CyclicGeneric is already derived from
that same original premise; it is not an independent assumption. -/
theorem child_auxiliaryGenericity
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : Primitive.ClosedAuxiliary q hR) :
    GeometricSmoothingWeights.auxiliaryGenericity (child q hR c hc.1 hcut)
      (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux) := by
  intro S hS root
  have hEmpty : Nonalternation.Nonalternating (parent q c hcut) (regular_parent q hR c hcut) ∅ := by
    intro d hd
    exact False.elim (Finset.not_mem_empty d hd)
  let V := nonalternatingSelectionEquiv q hR c hc hcut (⟨S,hS⟩,⟨∅,hEmpty⟩)
  let U : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
  let C := componentOf (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S) root
  let D := childComponentMap q hR c hc hcut hAux S ∅ C
  have hOriginal := hAux U D.val D.property
  have hrot := childComponentMap_word_isRotated q hR c hc hcut hAux S ∅ C
  have hg := DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated hrot hOriginal
  let r := GeometricSmoothingWeights.componentRoot (child q hR c hc.1 hcut)
    (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux) S C
  have hr : (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S).SameCycle r root :=
    (componentOf_eq_iff _ _ _).mp (GeometricSmoothingWeights.componentRoot_sameComponent _ _ _ C)
  have hrotRoot := DaughterRootRotation.daughterPointList_isRotated_of_sameCycle
    (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S r root hr
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated hrotRoot hg

end DirectGLSSW.ActiveArc.CompatibleWords
