import ExposedEdgeGeometry
import UncutDaughterEdge
import DirectGLSSW.DaughterRootAmplitude
import DirectGLSSW.PrimitiveSpectatorRows

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ExposedOpenPrimitive
open DaughterFirstReturn PrimitiveEdgeGrouping GeometricSmoothingWeights
open SpectatorProductFactorization PermutationOrbits

abbrev rootDaughter {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (U : OffEdgeSupport q hq e) :=
  daughterVertex q hq.g2 U.val (Sum.inl e)

def daughterEdge {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (U : OffEdgeSupport q hq e) :
    Fin (Fintype.card (CornerCoord q hq.g2 U.val (Sum.inl e))) :=
  ⟨0, by
    have hc := DaughterTurns.daughterVertexCount_ge_three q hq.g2 U.val
      hq.size_ge_three hq.g1 (Sum.inl e) (by trivial)
    omega⟩

theorem daughterEdge_event {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (U : OffEdgeSupport q hq e) :
    orbitEventAt q hq.g2 U.val (Sum.inl e)
      (cornerEnumeration q hq.g2 U.val (Sum.inl e) (daughterEdge q hq e U)).val = Sum.inl e := by
  unfold daughterEdge
  rw [cornerEnumeration_zero_eq_rootcoord q hq.g2 U.val (Sum.inl e) (by trivial)]
  simp [orbitEventAt]

theorem daughterEdge_vertices {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (U : OffEdgeSupport q hq e) :
    rootDaughter q hq e U (daughterEdge q hq e U) = q e ∧
    rootDaughter q hq e U (cyclicSuccessor (daughterEdge q hq e U)) = q (cyclicSuccessor e) :=
  UncutDaughterEdge.uncut_anchor_vertices q hq.g2 hq.size_ge_three U.val (Sum.inl e)
    (by trivial) e U.property.2 (daughterEdge q hq e U) (daughterEdge_event q hq e U)

/-- Exposure of the inherited physical edge follows from event geometry and daughter G1. -/
theorem leftExposed_rootDaughter {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq) (e : Fin n) (he : LeftExposed q e)
    (U : OffEdgeSupport q hq e) :
    LeftExposed (rootDaughter q hq e U) (daughterEdge q hq e U) := by
  intro i hi hs
  let Q := rootDaughter q hq e U
  let j := daughterEdge q hq e U
  have hQ : CyclicGeneric Q := hAux U.val U.property.1 (Sum.inl e)
  have hv := daughterEdge_vertices q hq e U
  have ht : cyclicTangent Q j = cyclicTangent q e := by
    unfold cyclicTangent
    change rootDaughter q hq e U (cyclicSuccessor (daughterEdge q hq e U)) -
      rootDaughter q hq e U (daughterEdge q hq e U) = _
    rw [hv.1,hv.2]
  have hn : 0 ≤ planarDet (cyclicTangent Q j) (Q i-Q j) := by
    rw [ht]
    change 0 ≤ planarDet (cyclicTangent q e)
      (rootDaughter q hq e U i-rootDaughter q hq e U (daughterEdge q hq e U))
    rw [hv.1]
    exact leftExposed_event_nonneg q e he _
  have hz := cyclic_vertex_carrier_det_ne_zero hQ.size_ge_three Q hQ.g1 j i hi hs
  exact lt_of_le_of_ne hn (Ne.symm hz)

/-- Choice of the component root does not change its actual polygon amplitude. -/
theorem rootDaughter_amplitude_eq_component {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq) (hRI : GLSSWRootIndependence)
    (e : Fin n) (U : OffEdgeSupport q hq e) :
    polygonAmplitude (rootDaughter q hq e U) (hAux U.val U.property.1 (Sum.inl e)) =
      componentAmplitude q hq U.val hAux U.property.1 (edgeComponent q hq e U) := by
  let r := componentRoot q hq U.val (edgeComponent q hq e U)
  have hr : componentOf (smoothingDartPermutation q hq.g2 U.val) r =
      componentOf (smoothingDartPermutation q hq.g2 U.val) (Sum.inl e) :=
    componentRoot_sameComponent q hq U.val (edgeComponent q hq e U)
  have hc := (componentOf_eq_iff (smoothingDartPermutation q hq.g2 U.val) _ _).mp hr.symm
  exact DaughterRootAmplitude.daughterPolygonAmplitude_eq_of_sameCycle hRI q hq.g2 U.val
    (Sum.inl e) r hc (hAux U.val U.property.1 (Sum.inl e))

end DirectGLSSW.ExposedOpenPrimitive
