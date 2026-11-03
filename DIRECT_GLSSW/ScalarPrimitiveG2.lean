import DaughterG2Inheritance
import DirectGLSSW.GeometricSmoothingWeights
import DirectGLSSW.DaughterRootRotation
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
namespace DirectGLSSW.FullScalarInversion
open scoped BigOperators
open DirectGLSSW.GeometricSmoothingWeights DirectGLSSW.PolygonNonalternation
open DirectGLSSW.PermutationOrbits

/-- A scalar of unbased oriented cyclic polygons, represented by its value on
an actual finite vertex word and an explicit cyclic-root invariance law. -/
structure CyclicScalar (R : Type*) where
  toFun : List (PlanarPoint ℝ) → R
  rotation_invariant : ∀ L M, L ~r M → toFun L = toFun M

abbrev SeparatingSupportG2 {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) :=
  {S : Finset (PolygonCrossing q) // polygonNonalternating q hG2 S}

/-- Raw root-independence on the literal daughter words, proved before any
selected component-word or scalar primitive is defined. -/
theorem scalar_daughter_root_invariant {R : Type*} (X : CyclicScalar R)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (x y : PolygonEvent q)
    (hxy : (smoothingDartPermutation q hG2 S).SameCycle x y) :
    X.toFun (DaughterFirstReturn.daughterPointList q hG2 S x) =
      X.toFun (DaughterFirstReturn.daughterPointList q hG2 S y) :=
  X.rotation_invariant _ _
    (DirectGLSSW.DaughterRootRotation.daughterPointList_isRotated_of_sameCycle
      q hG2 S x y hxy)

/-- The literal oriented cyclic vertex word of an actual smoothing component.
The quotient representative only chooses a starting point for the word. -/
noncomputable def componentWord {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (C : Component (smoothingDartPermutation q hG2 S)) :
    List (PlanarPoint ℝ) :=
  DaughterFirstReturn.daughterPointList q hG2 S (Quotient.out C)

noncomputable def componentProduct {R : Type*} [CommRing R] {n : ℕ}
    (X : CyclicScalar R) (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) : R :=
  ∏ C : Component (smoothingDartPermutation q hG2 S), X.toFun (componentWord q hG2 S C)

/-- The source's exact alternating separating-smoothing primitive on the G2
support geometry. No amplitude, root-independence, or auxiliary genericity. -/
noncomputable def primitive {R : Type*} [CommRing R] {n : ℕ}
    (X : CyclicScalar R) (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) : R := by
  classical
  exact ∑ S : SeparatingSupportG2 q hG2,
    (-1 : R) ^ S.1.card * componentProduct X q hG2 S.1

end DirectGLSSW.FullScalarInversion





