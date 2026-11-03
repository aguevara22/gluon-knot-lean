import ActiveArcChildRootWords
import DirectGLSSW.GeometricSmoothingWeights

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (hAux : Primitive.ClosedAuxiliary q hR)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

/-- The existing canonical child component root, converted to incoming labels.
Its CyclicGeneric argument is derived from original ClosedAuxiliary. -/
def childCanonicalIncomingRoot
    (C : Component (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S)) :
    ChildRetained q hR c hc hcut S :=
  ⟨smoothingPairing (child q hR c hc.1 hcut) S
      (GeometricSmoothingWeights.componentRoot (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux) S C),
    (DaughterFirstReturn.pairing_preserves_retained _ _ _).mpr
      (GeometricSmoothingWeights.componentRoot_retainedCorner _ _ _ _)⟩

theorem childCanonicalIncomingRoot_pair
    (C : Component (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S)) :
    smoothingPairing (child q hR c hc.1 hcut) S (childCanonicalIncomingRoot q hR c hc hcut hAux S C).val=
      GeometricSmoothingWeights.componentRoot (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux) S C :=
  (smoothingPairing (child q hR c hc.1 hcut) S).left_inv _

theorem childCanonicalIncomingRoot_component
    (C : Component (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S)) :
    componentOf (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S)
      (smoothingPairing (child q hR c hc.1 hcut) S (childCanonicalIncomingRoot q hR c hc hcut hAux S C).val)=C := by
  rw [childCanonicalIncomingRoot_pair]
  exact GeometricSmoothingWeights.componentRoot_sameComponent _ _ _ _

/-- Actual closed child components map to actual original closed components. -/
def childComponentMap :
    Component (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S) →
    {D : Component (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) //
      D≠openComponent q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))} := fun C =>
  ⟨componentOf (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
    (childEventMap q hR c hc hcut (childCanonicalIncomingRoot q hR c hc hcut hAux S C).val),
    child_root_closed q hR c hc hcut S T (childCanonicalIncomingRoot q hR c hc hcut hAux S C)⟩

theorem childComponentMap_componentOf
    (C : Component (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S))
    (x : ChildRetained q hR c hc hcut S)
    (hx : componentOf (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S)
      (smoothingPairing (child q hR c hc.1 hcut) S x.val)=C) :
    componentOf (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
      (childEventMap q hR c hc hcut x.val)=(childComponentMap q hR c hc hcut hAux S T C).val := by
  apply (componentOf_eq_iff _ _ _).mpr
  apply (mapped_child_dart_sameCycle_iff q hR c hc hcut S T x (childCanonicalIncomingRoot q hR c hc hcut hAux S C)).mpr
  apply (componentOf_eq_iff _ _ _).mp
  rw [hx,childCanonicalIncomingRoot_component]

theorem childComponentMap_injective : Function.Injective (childComponentMap q hR c hc hcut hAux S T) := by
  intro C D he
  have hs := (componentOf_eq_iff _ _ _).mp (congrArg Subtype.val he)
  have hh := (mapped_child_dart_sameCycle_iff q hR c hc hcut S T
    (childCanonicalIncomingRoot q hR c hc hcut hAux S C) (childCanonicalIncomingRoot q hR c hc hcut hAux S D)).mp hs
  have hh := (componentOf_eq_iff _ _ _).mpr hh
  simpa only [childCanonicalIncomingRoot_component] using hh

/-- Canonical original closed retained words agree cyclically with the
existing actual child component polygons. Child genericity is derived. -/
theorem childComponentMap_word_isRotated
    (C : Component (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S)) :
    let D := childComponentMap q hR c hc hcut hAux S T C
    List.ofFn (RetainedWords.vertex q hR (insert c (pieceSelections q hR c hc hcut S T))
      (closedRoot q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) D.val D.property)) ~r
      List.ofFn (GeometricSmoothingWeights.componentPolygon (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux) S C) := by
  let x := childCanonicalIncomingRoot q hR c hc hcut hAux S C
  let D := childComponentMap q hR c hc hcut hAux S T C
  have hs := (closedRoot_spec q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) D.val D.property).1
  have hr := retainedWord_isRotated_of_sameCycle q hR (insert c (pieceSelections q hR c hc hcut S T))
    (closedRoot q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) D.val D.property)
    (childEventMap q hR c hc hcut x.val) ((componentOf_eq_iff _ _ _).mp hs)
  have hw := child_root_word q hR c hc hcut S T x
  change List.ofFn (RetainedWords.vertex q hR (insert c (pieceSelections q hR c hc hcut S T))
      (childEventMap q hR c hc hcut x.val))=
    DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S
      (smoothingPairing (child q hR c hc.1 hcut) S (childCanonicalIncomingRoot q hR c hc hcut hAux S C).val) at hw
  rw [childCanonicalIncomingRoot_pair] at hw
  rw [hw] at hr
  exact hr

end DirectGLSSW.ActiveArc.CompatibleWords
