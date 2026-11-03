import SourceMixedEdgeContinuation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceMixedEdgeFull
open DirectGLSSW GeometricSmoothingWeights ChosenEdgeNormalization PermutationOrbits
open SourceMixedEdgeContinuation MixedEdgeDensityRecursion CrossingIncidenceNeighborhood
open ActualAuxiliaryDensity CrossingRationalParameters Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The unique whole-expression continuation of the literal chosen-edge RHS.
No individual nongeneric daughter amplitude is assigned a value. -/
def mixedEdgeRHS (hRI : GLSSWRootIndependence) (n : ℕ) (e : Fin n) :
    (q : Fin n → PlanarPoint ℝ) → CyclicGeneric q →
      (planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
        planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0) → ℚ :=
  Classical.choose (existsUnique_mixed_edge_rhs_continuation hRI n e)

theorem mixedEdgeRHS_eq_choice (hRI : GLSSWRootIndependence) (n : ℕ) (e : Fin n) :
    mixedEdgeRHS hRI n e =
      Classical.choose (existsUnique_mixed_edge_rhs_continuation hRI n e) := rfl

/-- Complete defining characterization, including the literal finite products
on their original domain and uniqueness among locally constant extensions. -/
theorem mixedEdgeRHS_characterization (hRI : GLSSWRootIndependence)
    (n : ℕ) (e : Fin n) :
    (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
        planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0),
      ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r)
        (htr : planarDet (cyclicTangent r e) (cyclicTangent r (cyclicSuccessor e)) *
          planarDet (cyclicTangent r (cyclicVertexIndex e (n-2))) (cyclicTangent r e) < 0),
        mixedEdgeRHS hRI n e r hr htr = mixedEdgeRHS hRI n e q hq ht) ∧
    (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
        planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0)
      (hAux : auxiliaryGenericity q hq),
      mixedEdgeRHS hRI n e q hq ht = ∑ T : ChosenEdgeSeparatingSupport q hq e,
        (-1 : ℚ)^((T.val.image Subtype.val).card+1) *
          ∏ c : Component (smoothingDartPermutation q hq.g2 (T.val.image Subtype.val)),
            polygonAmplitude (componentPolygon q hq (T.val.image Subtype.val) c)
              (hAux _ T.property.2 (componentRoot q hq _ c))) ∧
    (∀ Φ : (q : Fin n → PlanarPoint ℝ) → CyclicGeneric q →
        (planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
          planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0) → ℚ,
      (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
        (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
          planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0),
        ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r)
          (htr : planarDet (cyclicTangent r e) (cyclicTangent r (cyclicSuccessor e)) *
            planarDet (cyclicTangent r (cyclicVertexIndex e (n-2))) (cyclicTangent r e) < 0),
          Φ r hr htr = Φ q hq ht) →
      (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
        (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
          planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0)
        (hAux : auxiliaryGenericity q hq),
        Φ q hq ht = ∑ T : ChosenEdgeSeparatingSupport q hq e,
          (-1 : ℚ)^((T.val.image Subtype.val).card+1) *
            ∏ c : Component (smoothingDartPermutation q hq.g2 (T.val.image Subtype.val)),
              polygonAmplitude (componentPolygon q hq (T.val.image Subtype.val) c)
                (hAux _ T.property.2 (componentRoot q hq _ c))) →
      Φ = mixedEdgeRHS hRI n e) := by
  have h := Classical.choose_spec (existsUnique_mixed_edge_rhs_continuation hRI n e)
  exact ⟨h.1.1,h.1.2,fun Φ hlocal hagree => h.2 Φ ⟨hlocal,hagree⟩⟩

/-- The full generic mixed-edge identity, using the source's explicit
whole-formula continuation and leaving all existing partial definitions intact. -/
theorem mixed_edge_formula_full (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
      planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0) :
    polygonAmplitude q hq = mixedEdgeRHS hRI n e q hq ht := by
  have h := mixedEdgeRHS_characterization hRI n e
  exact (mixed_edge_rhs_continuation_eq_amplitude hRI n e
    (mixedEdgeRHS hRI n e) h.1 h.2.1 q hq ht).symm

/-- An uncrossed opposite-turn edge forces zero amplitude on the full G1/G2
domain. Auxiliary daughter genericity is produced nearby and then discharged. -/
theorem uncrossed_mixed_edge_amplitude_zero (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
      planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0)
    (hno : ∀ c : EdgeChord q e, False) : polygonAmplitude q hq = 0 := by
  classical
  obtain ⟨δA,hδA,hA⟩ := exists_configurationNeighborhood_cyclicGeneric_and_signs_amplitude q hq
  obtain ⟨δT,hδT,hT⟩ := exists_endpoint_turn_negative_radius q e ht
  have hinc : ∀ᶠ r in 𝓝 q, ∀ i j : Fin n, cyclicNoncollinear r →
      (edgeIntersection r i j ↔ edgeIntersection q i j) :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr
      (fun j => eventually_edgeIntersection_iff q hq i j))
  have hBoth : ∀ᶠ r in 𝓝 q,
      CoordClose δA r q ∧ CoordClose δT r q ∧
      ∀ i j : Fin n, cyclicNoncollinear r →
        (edgeIntersection r i j ↔ edgeIntersection q i j) := by
    filter_upwards [Metric.ball_mem_nhds q hδA, Metric.ball_mem_nhds q hδT,hinc]
      with r hAr hTr hir
    have hclose {δ : ℝ} (hδ : 0 < δ) (hball : r ∈ Metric.ball q δ) :
        CoordClose δ r q := by
      rw [Metric.mem_ball,dist_pi_lt_iff hδ] at hball
      intro i
      simpa only [Prod.dist_eq,Real.dist_eq,max_lt_iff] using hball i
    exact ⟨hclose hδA hAr,hclose hδT hTr,hir⟩
  obtain ⟨r,hrBoth,hr,hAux,_⟩ := exists_auxiliaryGenericity_mem_nhds q hq _ hBoth
  obtain ⟨hr',_,hamp⟩ := hA r hrBoth.1
  have hamp' : polygonAmplitude r hr = polygonAmplitude q hq :=
    (Subsingleton.elim hr hr') ▸ hamp
  have htr := hT r hrBoth.2.1
  have hnor : ∀ c : EdgeChord r e, False := by
    intro c
    let cq : PolygonCrossing q :=
      ⟨c.val.val, c.val.property.1,
        (hrBoth.2.2 _ _ hr.g1).mp c.val.property.2⟩
    exact hno ⟨cq,c.property⟩
  rw [← hamp',SourceMixedEdgeFormula.mixed_edge_formula hRI r hr e htr hAux]
  apply Finset.sum_eq_zero
  intro T _
  obtain ⟨c,_⟩ := T.property.1
  exact (hnor c).elim

end DirectGLSSW.SourceMixedEdgeFull
