import PrimitiveDaughterRows
import PolygonUniformity
import AllOnEdgeSignedRow

set_option autoImplicit false
namespace DirectGLSSW.NonuniformPrimitive
open PrimitiveEdgeGrouping PrimitiveSpectatorRows PrimitiveDaughterRows
  DaughterUncutIncidence DaughterEdgeCompletion DaughterNestedWeights
  GeometricSmoothingWeights AllOnEdgeSignedRow PolygonUniformity
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (e : Fin n) (hAux : auxiliaryGenericity P hP)

/-- The actual affected daughter row vanishes by its inherited mixed-edge recurrence. -/
theorem affectedRow_eq_zero (hRI : GLSSWRootIndependence)
    (hturn : planarDet (cyclicTangent P e) (cyclicTangent P (cyclicSuccessor e)) *
      planarDet (cyclicTangent P (cyclicVertexIndex e (n-2))) (cyclicTangent P e) < 0)
    (U : OffEdgeSupport P hP e) :
    (∑ T : EdgeCompletion P hP e U, (-1 : ℚ)^T.val.card *
      affectedFactor P hP e hAux U T) = 0 := by
  rw [affectedRow_eq_daughterRow P hP e U hAux hRI]
  change allOnEdgeSignedRow (edgeDaughter P hP e U)
    (hAux U.val U.property.1 (Sum.inl e)) (daughterChosenEdge P hP e U)
    (daughter_auxiliaryGenericity P hP U.val U.property.1 (Sum.inl e) (by trivial) hAux) = 0
  rw [allOnEdgeSignedRow_eq_amplitude_sub_chosenEdgeSmoothingSum hRI]
  rw [edgeDaughter_mixed_recursion P hP e U hAux hRI hturn]
  exact sub_self _

/-- Source mixed-edge cancellation for the original full separating primitive.
Only parent auxiliary daughter genericity is supplied; nested genericity is derived. -/
theorem separatingSmoothingSum_eq_zero_of_opposite_edge (hRI : GLSSWRootIndependence)
    (hturn : planarDet (cyclicTangent P e) (cyclicTangent P (cyclicSuccessor e)) *
      planarDet (cyclicTangent P (cyclicVertexIndex e (n-2))) (cyclicTangent P e) < 0) :
    separatingSmoothingSum P hP hAux = 0 := by
  rw [separatingSmoothingSum_factored P hP e hAux hRI]
  apply Finset.sum_eq_zero
  intro U _
  rw [affectedRow_eq_zero P hP e hAux hRI hturn U,mul_zero]

/-- The GLSSW separating primitive vanishes on every nonuniform polygon in
its explicit auxiliary domain. Root independence is an argument. -/
theorem separatingSmoothingSum_eq_zero_of_not_uniform (hRI : GLSSWRootIndependence)
    (hnu : ¬ PolygonUniform P) : separatingSmoothingSum P hP hAux = 0 := by
  obtain ⟨e,hturn⟩ := exists_opposite_edge_of_not_uniform P hP hnu
  exact separatingSmoothingSum_eq_zero_of_opposite_edge P hP e hAux hRI hturn




end
end DirectGLSSW.NonuniformPrimitive
