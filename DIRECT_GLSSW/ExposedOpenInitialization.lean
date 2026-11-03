import ExposedEdgeDaughter
import DirectGLSSW.OpenMarkedCurrent
import DirectGLSSW.NearData

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DirectGLSSW.ExposedOpenPrimitive
open DaughterFirstReturn PrimitiveEdgeGrouping GeometricSmoothingWeights
open SpectatorProductFactorization PermutationOrbits

/-- Signed ordinary-current cuts of the actual complement of a physical edge. -/
def openedEdgeCurrent {n : ℕ} (q : Fin n → PlanarPoint ℝ) (e : Fin n) : ℚ :=
  OpenMarkedCurrent.entry (polygonSignArray (rootedPolygonWord q e)) 0 (n-1)

/-- Actual source M=A at an exposed physical closing edge. -/
theorem openedEdgeCurrent_eq_amplitude {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (he : LeftExposed q e) (hRI : GLSSWRootIndependence) :
    openedEdgeCurrent q e = polygonAmplitude q hq := by
  have hn : 0<n-1 := by have := hq.size_ge_three;omega
  rw [openedEdgeCurrent, OpenMarkedCurrent.entry_eq_markedAmplitude_of_topFarSigns
    (polygonSignArray (rootedPolygonWord q e)) _ hn
    (leftExposed_root_far_sign q hq e he)]
  rw [← markedTreeSum_eq_markedAmplitude _ _ hn,
    ← rootedSpinorAmplitude_eq_markedTreeSum hq.size_ge_three q hq.g1 e]
  exact (polygonAmplitude_eq_rootedSpinorAmplitude hRI q hq e).symm

/-- The single open member of the smoothing is the component containing the deleted edge.
All other factors are closed actual component amplitudes; no crossing of the deleted
edge is selectable. This is the cyclic-generic initialization chart, not the later
universal active-cursor domain. -/
def openAtEdgeSum {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq) (e : Fin n) : ℚ := by
  classical
  exact ∑ U : OffEdgeSupport q hq e, (-1 : ℚ)^U.val.card *
    (openedEdgeCurrent (rootDaughter q hq e U) (daughterEdge q hq e U) *
      ∏ C ∈ (Finset.univ.erase (edgeComponent q hq e U)),
        componentAmplitude q hq U.val hAux U.property.1 C)

def exposedSupportEquiv {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (he : LeftExposed q e) :
    OffEdgeSupport q hq e ≃ SeparatingSupport q hq where
  toFun U := ⟨U.val,U.property.1⟩
  invFun S := ⟨S.val,S.property,fun c _ => leftExposed_no_incident_crossing q hq e he c⟩
  left_inv U := by apply Subtype.ext;rfl
  right_inv S := by apply Subtype.ext;rfl

/-- Source un:initial, with every open current and inherited exposure derived. -/
theorem exposed_openAtEdgeSum_eq_separatingSmoothingSum {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq) (e : Fin n) (he : LeftExposed q e)
    (hRI : GLSSWRootIndependence) :
    openAtEdgeSum q hq hAux e = separatingSmoothingSum q hq hAux := by
  classical
  unfold openAtEdgeSum separatingSmoothingSum
  apply Fintype.sum_equiv (exposedSupportEquiv q hq e he)
  intro U
  change (-1 : ℚ)^U.val.card * _ = (-1 : ℚ)^U.val.card * _
  congr 1
  rw [openedEdgeCurrent_eq_amplitude (rootDaughter q hq e U)
    (hAux U.val U.property.1 (Sum.inl e)) (daughterEdge q hq e U)
    (leftExposed_rootDaughter q hq hAux e he U) hRI]
  rw [rootDaughter_amplitude_eq_component q hq hAux hRI e U]
  exact Finset.mul_prod_erase _ _ (Finset.mem_univ (edgeComponent q hq e U))

end DirectGLSSW.ExposedOpenPrimitive
