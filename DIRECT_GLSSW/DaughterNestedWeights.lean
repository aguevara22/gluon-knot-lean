import DaughterNestedPointList
import DaughterUnionNonalternation
import DirectGLSSW.TruncationPointListAdapter
import DirectGLSSW.TruncationComponentWeights

set_option autoImplicit false
namespace DirectGLSSW.DaughterNestedWeights
open DaughterFirstReturn DaughterEventLift DaughterPairingLift DaughterG2Inheritance
  DaughterNestedPointList DaughterAffectedComponents DaughterUnionNonalternation
  PolygonNonalternation PermutationOrbits GeometricSmoothingWeights
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

include hroot in
/-- Parent auxiliary genericity already covers all actual nested daughters. -/
theorem daughter_auxiliaryGenericity (hAux : auxiliaryGenericity P hP) :
    auxiliaryGenericity (daughterVertex P hP.g2 S root) (hAux S hS root) := by
  intro T hT x
  have hU := (polygonNonalternating_union_liftedSupport_iff P hP S hS root hroot T).mpr hT
  exact TruncationPointListAdapter.cyclicGeneric_of_pointList_eq _ _
    (hAux _ hU (eventLift P hP S hS root hroot x))
    (daughterPointList_nested_eq P hP S hS root hroot T x).symm

theorem nested_rooted_amplitude_eq (hAux : auxiliaryGenericity P hP)
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (hT : polygonNonalternating (daughterVertex P hP.g2 S root) (hAux S hS root).g2 T)
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    polygonAmplitude (daughterVertex (daughterVertex P hP.g2 S root)
      (hAux S hS root).g2 T x) (daughter_auxiliaryGenericity P hP S hS root hroot hAux T hT x) =
    polygonAmplitude (daughterVertex P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T)
      (eventLift P hP S hS root hroot x))
      (hAux _ ((polygonNonalternating_union_liftedSupport_iff P hP S hS root hroot T).mpr hT) _) := by
  apply TruncationPointListAdapter.polygonAmplitude_eq_of_pointList_eq
  exact daughterPointList_nested_eq P hP S hS root hroot T x

theorem componentAmplitude_nested_eq (hRI : GLSSWRootIndependence)
    (hAux : auxiliaryGenericity P hP)
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (hT : polygonNonalternating (daughterVertex P hP.g2 S root) (hAux S hS root).g2 T)
    (C : Component (smoothingDartPermutation (daughterVertex P hP.g2 S root) (hAux S hS root).g2 T)) :
    componentAmplitude (daughterVertex P hP.g2 S root) (hAux S hS root) T
      (daughter_auxiliaryGenericity P hP S hS root hroot hAux) hT C =
    componentAmplitude P hP (S ∪ liftedSupport P hP S hS root hroot T) hAux
      ((polygonNonalternating_union_liftedSupport_iff P hP S hS root hroot T).mpr hT)
      (componentEquivAffected P hP S hS root hroot T C).val := by
  induction C using Quotient.inductionOn with
  | h x =>
    change componentAmplitude _ _ _ _ _ (componentOf _ x) =
      componentAmplitude _ _ _ _ _ (componentOf _ (eventLift P hP S hS root hroot x))
    rw [TruncationComponentWeights.componentAmplitude_eq_at_root hRI _ _ _ _ _ _ x rfl,
      TruncationComponentWeights.componentAmplitude_eq_at_root hRI _ _ _ _ _ _
        (eventLift P hP S hS root hroot x) rfl]
    exact nested_rooted_amplitude_eq P hP S hS root hroot hAux T hT x

theorem componentAmplitudeProduct_eq_affected (hRI : GLSSWRootIndependence)
    (hAux : auxiliaryGenericity P hP)
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))
    (hT : polygonNonalternating (daughterVertex P hP.g2 S root) (hAux S hS root).g2 T) :
    componentAmplitudeProduct (daughterVertex P hP.g2 S root) (hAux S hS root) T
      (daughter_auxiliaryGenericity P hP S hS root hroot hAux) hT =
    ∏ C : AffectedFinal P hP S hS root hroot T,
      componentAmplitude P hP (S ∪ liftedSupport P hP S hS root hroot T) hAux
        ((polygonNonalternating_union_liftedSupport_iff P hP S hS root hroot T).mpr hT) C.val := by
  unfold componentAmplitudeProduct
  exact Fintype.prod_equiv (componentEquivAffected P hP S hS root hroot T) _ _
    (componentAmplitude_nested_eq P hP S hS root hroot hRI hAux T hT)





end
end DirectGLSSW.DaughterNestedWeights
