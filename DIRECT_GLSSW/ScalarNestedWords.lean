import ScalarFamilyLocality
import DaughterNestedPointList

set_option autoImplicit false
namespace DirectGLSSW.FullScalarInversion
open DirectGLSSW.PermutationOrbits DirectGLSSW.PolygonNonalternation
open DirectGLSSW.DaughterFirstReturn DirectGLSSW.DaughterPairingLift
open DirectGLSSW.DaughterEventLift DirectGLSSW.DaughterAffectedComponents
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 4000000 in
/-- An arbitrary cyclic scalar evaluates equally on a nested daughter
component and its actual final parent component. The underlying rooted
vertex words are literally equal; root invariance handles representatives. -/
theorem scalar_nested_component_eq {R : Type*} (X : CyclicScalar R)
    {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
    (root : PolygonEvent P) (hroot : retainedCorner P S root)
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (C : Component (daughterDart P hP S hS root T)) :
    X.toFun (componentWord (daughterVertex P hP.g2 S root)
      (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections P hP.g2 S
        hP.size_ge_three hS root) T C) =
    X.toFun (componentWord P hP.g2
      (S ∪ liftedSupport P hP S hS root hroot T)
      (componentEquivAffected P hP S hS root hroot T C).val) := by
  classical
  let Q := daughterVertex P hP.g2 S root
  let hQ := DaughterG2Inheritance.daughter_cyclicNoTripleIntersections P hP.g2 S
    hP.size_ge_three hS root
  let U := S ∪ liftedSupport P hP S hS root hroot T
  induction C using Quotient.inductionOn with
  | h x =>
    change X.toFun (componentWord Q hQ T (componentOf _ x)) =
      X.toFun (componentWord P hP.g2 U
        (componentOf _ (eventLift P hP S hS root hroot x)))
    calc
      X.toFun (componentWord Q hQ T (componentOf _ x)) =
          X.toFun (daughterPointList Q hQ T x) :=
        scalar_component_eq_at_root X Q hQ T _ x rfl
      _ = X.toFun (daughterPointList P hP.g2 U
            (eventLift P hP S hS root hroot x)) := by
          exact congrArg X.toFun
            (DirectGLSSW.DaughterNestedPointList.daughterPointList_nested_eq
              P hP S hS root hroot T x)
      _ = X.toFun (componentWord P hP.g2 U
            (componentOf _ (eventLift P hP S hS root hroot x))) :=
        (scalar_component_eq_at_root X P hP.g2 U _ _ rfl).symm

set_option maxHeartbeats 4000000 in
/-- Generic scalar product over nested components reindexed by the actual
affected final parent components. This is a proved geometric reindexing, not
an assumed expansion identity. -/
theorem scalar_nested_componentProduct_eq_affected {R : Type*} [CommRing R]
    (X : CyclicScalar R)
    {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
    (root : PolygonEvent P) (hroot : retainedCorner P S root)
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root))) :
    componentProduct X (daughterVertex P hP.g2 S root)
      (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections P hP.g2 S
        hP.size_ge_three hS root) T =
    ∏ C : AffectedFinal P hP S hS root hroot T,
      X.toFun (componentWord P hP.g2
        (S ∪ liftedSupport P hP S hS root hroot T) C.val) := by
  classical
  unfold componentProduct
  exact Fintype.prod_equiv (componentEquivAffected P hP S hS root hroot T) _ _
    (scalar_nested_component_eq X P hP S hS root hroot T)

theorem scalar_component_eq_of_support_eq {R : Type*} (X : CyclicScalar R)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q)
    {U V : Finset (PolygonCrossing q)} (hUV : U = V)
    (C : Component (smoothingDartPermutation q hG2 U)) :
    X.toFun (componentWord q hG2 U C) =
      X.toFun (componentWord q hG2 V
        ((componentEquivOfIntertwining (Equiv.refl _)
          (smoothingDartPermutation q hG2 U) (smoothingDartPermutation q hG2 V)
          (by cases hUV; intro x; rfl)) C)) := by
  subst V
  let e := componentEquivOfIntertwining (Equiv.refl _)
    (smoothingDartPermutation q hG2 U) (smoothingDartPermutation q hG2 U)
    (by intro x; rfl)
  have he : ∀ C, e C = C := by
    intro C
    refine Quotient.inductionOn C ?_
    intro x
    rfl
  change X.toFun (componentWord q hG2 U C) =
    X.toFun (componentWord q hG2 U (e C))
  rw [he C]

end DirectGLSSW.FullScalarInversion

