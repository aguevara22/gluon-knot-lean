import DirectGLSSW.SpectatorProductFactorization

set_option autoImplicit false
namespace DirectGLSSW.PrimitiveSpectatorRows
open PrimitiveEdgeGrouping SpectatorProductFactorization GeometricSmoothingWeights
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (e : Fin n) (hAux : auxiliaryGenericity P hP)

def spectatorFactor (U : OffEdgeSupport P hP e) : ℚ :=
  ∏ B : OldSpectator P hP e U, componentAmplitude P hP U.val hAux U.property.1 B.val

def affectedFactor (U : OffEdgeSupport P hP e) (T : EdgeCompletion P hP e U) : ℚ :=
  ∏ C : AffectedFinal P hP e U T,
    componentAmplitude P hP (U.val ∪ T.val) hAux T.property.2 C.val

theorem row_factor_spectators (hRI : GLSSWRootIndependence) (U : OffEdgeSupport P hP e) :
    (∑ T : EdgeCompletion P hP e U, (-1 : ℚ)^T.val.card *
      componentAmplitudeProduct P hP (U.val ∪ T.val) hAux T.property.2) =
    spectatorFactor P hP e hAux U *
      ∑ T : EdgeCompletion P hP e U, (-1 : ℚ)^T.val.card * affectedFactor P hP e hAux U T := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [componentAmplitudeProduct_factor_spectators P hP e U T hRI hAux]
  change (-1 : ℚ)^T.val.card * (spectatorFactor P hP e hAux U * affectedFactor P hP e hAux U T) = _
  ring

/-- Exact source grouping with the unchanged spectator amplitudes factored out.
Identification of the affected row with the geometric daughter recurrence remains separate. -/
theorem separatingSmoothingSum_factored (hRI : GLSSWRootIndependence) :
    separatingSmoothingSum P hP hAux =
      ∑ U : OffEdgeSupport P hP e,
        (-1 : ℚ)^U.val.card * spectatorFactor P hP e hAux U *
          ∑ T : EdgeCompletion P hP e U,
            (-1 : ℚ)^T.val.card * affectedFactor P hP e hAux U T := by
  rw [separatingSmoothingSum_grouped P hP e hAux]
  apply Finset.sum_congr rfl
  intro U _
  rw [row_factor_spectators P hP e hAux hRI U]
  ring





end
end DirectGLSSW.PrimitiveSpectatorRows
