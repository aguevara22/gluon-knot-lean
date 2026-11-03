import CyclicCarrierCharacterizations
import DaughterNestedWeights

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open DaughterFirstReturn DaughterEventLift DaughterPairingLift DaughterNestedPointList
open DaughterUnionNonalternation GeometricSmoothingWeights PolygonNonalternation

 theorem secants_of_pointList_eq {n m : ℕ}
    (q : Fin n → PlanarPoint ℝ) (r : Fin m → PlanarPoint ℝ)
    (h : List.ofFn q = List.ofFn r)
    (hs : (∀ l : Fin 4 → Fin n, Function.Injective l →
      OriginalOuterProperness.outerNumerator (q ∘ l) ≠ 0) ∧
      (∀ l : Fin 6 → Fin n, Function.Injective l →
      OriginalSecantProperness.secantNumerator (q ∘ l) ≠ 0)) :
    (∀ l : Fin 4 → Fin m, Function.Injective l →
      OriginalOuterProperness.outerNumerator (r ∘ l) ≠ 0) ∧
    (∀ l : Fin 6 → Fin m, Function.Injective l →
      OriginalSecantProperness.secantNumerator (r ∘ l) ≠ 0) := by
  have hnm : n = m := by simpa using congrArg List.length h
  subst m
  have hqr : q = r := List.ofFn_injective h
  simpa only [hqr] using hs

/-- The SAME original finite inventory covers the literal next-stage daughters.
The union support, retained root, and point list are all established actual APIs. -/
 theorem actualDaughterSecants_daughter {n : ℕ}
    (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (hAux : auxiliaryGenericity P hP) (hsec : actualDaughterSecants P hP)
    (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
    (root : PolygonEvent P) (hroot : retainedCorner P S root) :
    actualDaughterSecants (daughterVertex P hP.g2 S root) (hAux S hS root) := by
  classical
  intro T hT x hx
  have hU := (polygonNonalternating_union_liftedSupport_iff P hP S hS root hroot T).mpr hT
  have hx' := (eventLift_retained_union_iff P hP S hS root hroot T x).mp hx
  have hs := hsec (S ∪ liftedSupport P hP S hS root hroot T) hU
    (eventLift P hP S hS root hroot x) hx'
  exact secants_of_pointList_eq _ _
    (daughterPointList_nested_eq P hP S hS root hroot T x).symm hs

end DirectGLSSW.CyclicCarrierClearing


