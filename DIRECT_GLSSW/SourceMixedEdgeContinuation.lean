import SourceMixedEdgeFormula

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceMixedEdgeContinuation
open DirectGLSSW GeometricSmoothingWeights ChosenEdgeNormalization PermutationOrbits
open DirectGLSSW.SourceMixedEdgeFormula DirectGLSSW.MixedEdgeDensityRecursion
open DirectGLSSW.CrossingIncidenceNeighborhood DirectGLSSW.ActualAuxiliaryDensity
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private theorem amplitude_locally_constant {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ r in 𝓝 q, ∀ hr : CyclicGeneric r,
      polygonAmplitude r hr = polygonAmplitude q hq := by
  obtain ⟨δ,hδ,hlocal⟩ := exists_configurationNeighborhood_cyclicGeneric_and_signs_amplitude q hq
  filter_upwards [Metric.ball_mem_nhds q hδ] with r hrball
  have hclose : CrossingIncidenceNeighborhood.CoordClose δ r q := by
    rw [Metric.mem_ball, dist_pi_lt_iff hδ] at hrball
    intro i
    simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff] using hrball i
  obtain ⟨hr',_,hamp⟩ := hlocal r hclose
  intro hr
  exact (Subsingleton.elim hr hr') ▸ hamp

private theorem opposite_turns_eventually {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (e : Fin n)
    (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
      planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0) :
    ∀ᶠ r in 𝓝 q,
      planarDet (cyclicTangent r e) (cyclicTangent r (cyclicSuccessor e)) *
        planarDet (cyclicTangent r (cyclicVertexIndex e (n-2))) (cyclicTangent r e) < 0 := by
  obtain ⟨δ,hδ,hlocal⟩ := exists_endpoint_turn_negative_radius q e ht
  filter_upwards [Metric.ball_mem_nhds q hδ] with r hrball
  apply hlocal r
  rw [Metric.mem_ball, dist_pi_lt_iff hδ] at hrball
  intro i
  simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff] using hrball i

/-- On the actual opposite-turn G1/G2 locus, the literal auxiliary chosen-edge
smoothing sum has a unique locally constant continuation. The continuation
is the already-defined GLSSW polygon amplitude, rather than a new value. -/
theorem existsUnique_mixed_edge_rhs_continuation (hRI : GLSSWRootIndependence)
    (n : ℕ) (e : Fin n) :
    ∃! Φ : (q : Fin n → PlanarPoint ℝ) → CyclicGeneric q →
        (planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
          planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0) → ℚ,
      (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
        (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
          planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0),
        ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r)
          (htr : planarDet (cyclicTangent r e) (cyclicTangent r (cyclicSuccessor e)) *
            planarDet (cyclicTangent r (cyclicVertexIndex e (n-2))) (cyclicTangent r e) < 0),
          Φ r hr htr = Φ q hq ht) ∧
      (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
        (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
          planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0)
        (hAux : auxiliaryGenericity q hq),
        Φ q hq ht = ∑ T : ChosenEdgeSeparatingSupport q hq e,
          (-1 : ℚ)^((T.val.image Subtype.val).card+1) *
            ∏ c : Component (smoothingDartPermutation q hq.g2 (T.val.image Subtype.val)),
              polygonAmplitude (componentPolygon q hq (T.val.image Subtype.val) c)
                (hAux _ T.property.2 (componentRoot q hq _ c))) := by
  let Φ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (_ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
        planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0) : ℚ :=
    polygonAmplitude q hq
  have hlocal (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
        planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0) :
      ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r)
        (htr : planarDet (cyclicTangent r e) (cyclicTangent r (cyclicSuccessor e)) *
          planarDet (cyclicTangent r (cyclicVertexIndex e (n-2))) (cyclicTangent r e) < 0),
        Φ r hr htr = Φ q hq ht := by
    filter_upwards [amplitude_locally_constant q hq] with r hr
    intro hrg hrt
    exact hr hrg
  have hagree (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
        planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0)
      (hAux : auxiliaryGenericity q hq) :
      Φ q hq ht = ∑ T : ChosenEdgeSeparatingSupport q hq e,
        (-1 : ℚ)^((T.val.image Subtype.val).card+1) *
          ∏ c : Component (smoothingDartPermutation q hq.g2 (T.val.image Subtype.val)),
            polygonAmplitude (componentPolygon q hq (T.val.image Subtype.val) c)
              (hAux _ T.property.2 (componentRoot q hq _ c)) := by
    exact mixed_edge_formula hRI q hq e ht hAux
  refine ⟨Φ,⟨hlocal,hagree⟩,?_⟩
  intro F hF
  funext q hq ht
  have hEv : ∀ᶠ r in 𝓝 q,
      ∀ (hr : CyclicGeneric r)
        (htr : planarDet (cyclicTangent r e) (cyclicTangent r (cyclicSuccessor e)) *
          planarDet (cyclicTangent r (cyclicVertexIndex e (n-2))) (cyclicTangent r e) < 0),
        F r hr htr = F q hq ht ∧ Φ r hr htr = Φ q hq ht := by
    filter_upwards [hF.1 q hq ht,hlocal q hq ht] with r hFr hΦr
    intro hr htr
    exact ⟨hFr hr htr,hΦr hr htr⟩
  have hTurn := opposite_turns_eventually q e ht
  have hBoth : ∀ᶠ r in 𝓝 q,
      ∃ htr : planarDet (cyclicTangent r e) (cyclicTangent r (cyclicSuccessor e)) *
          planarDet (cyclicTangent r (cyclicVertexIndex e (n-2))) (cyclicTangent r e) < 0,
        ∀ hr : CyclicGeneric r,
          F r hr htr = F q hq ht ∧ Φ r hr htr = Φ q hq ht := by
    filter_upwards [hTurn,hEv] with r htr hr
    exact ⟨htr,fun hrg => hr hrg htr⟩
  obtain ⟨r,hrS,hr,hAux,_⟩ :=
    exists_auxiliaryGenericity_mem_nhds q hq _ hBoth
  obtain ⟨htr,hFconst⟩ := hrS
  calc
    F q hq ht = F r hr htr := (hFconst hr).1.symm
    _ = ∑ T : ChosenEdgeSeparatingSupport r hr e,
          (-1 : ℚ)^((T.val.image Subtype.val).card+1) *
            ∏ c : Component (smoothingDartPermutation r hr.g2 (T.val.image Subtype.val)),
              polygonAmplitude (componentPolygon r hr (T.val.image Subtype.val) c)
                (hAux _ T.property.2 (componentRoot r hr _ c)) := hF.2 r hr htr hAux
    _ = Φ r hr htr := (hagree r hr htr hAux).symm
    _ = Φ q hq ht := (hFconst hr).2

/-- Every locally constant extension agreeing with the literal auxiliary
chosen-edge sum has exactly the original polygon-amplitude value. -/
theorem mixed_edge_rhs_continuation_eq_amplitude (hRI : GLSSWRootIndependence)
    (n : ℕ) (e : Fin n)
    (Φ : (q : Fin n → PlanarPoint ℝ) → CyclicGeneric q →
      (planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
        planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0) → ℚ)
    (hlocal : ∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
        planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0),
      ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r)
        (htr : planarDet (cyclicTangent r e) (cyclicTangent r (cyclicSuccessor e)) *
          planarDet (cyclicTangent r (cyclicVertexIndex e (n-2))) (cyclicTangent r e) < 0),
        Φ r hr htr = Φ q hq ht)
    (hagree : ∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
        planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0)
      (hAux : auxiliaryGenericity q hq),
      Φ q hq ht = ∑ T : ChosenEdgeSeparatingSupport q hq e,
        (-1 : ℚ)^((T.val.image Subtype.val).card+1) *
          ∏ c : Component (smoothingDartPermutation q hq.g2 (T.val.image Subtype.val)),
            polygonAmplitude (componentPolygon q hq (T.val.image Subtype.val) c)
              (hAux _ T.property.2 (componentRoot q hq _ c)))
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (ht : planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
      planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0) :
    Φ q hq ht = polygonAmplitude q hq := by
  let A : (q : Fin n → PlanarPoint ℝ) → CyclicGeneric q →
      (planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
        planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0) → ℚ :=
    fun r hr _ => polygonAmplitude r hr
  have hAlocal : ∀ (r : Fin n → PlanarPoint ℝ) (hr : CyclicGeneric r)
      (htr : planarDet (cyclicTangent r e) (cyclicTangent r (cyclicSuccessor e)) *
        planarDet (cyclicTangent r (cyclicVertexIndex e (n-2))) (cyclicTangent r e) < 0),
      ∀ᶠ s in 𝓝 r, ∀ (hs : CyclicGeneric s)
        (hts : planarDet (cyclicTangent s e) (cyclicTangent s (cyclicSuccessor e)) *
          planarDet (cyclicTangent s (cyclicVertexIndex e (n-2))) (cyclicTangent s e) < 0),
        A s hs hts = A r hr htr := by
    intro r hr htr
    filter_upwards [amplitude_locally_constant r hr] with s h
    intro hs hts
    exact h hs
  have hAagree : ∀ (r : Fin n → PlanarPoint ℝ) (hr : CyclicGeneric r)
      (htr : planarDet (cyclicTangent r e) (cyclicTangent r (cyclicSuccessor e)) *
        planarDet (cyclicTangent r (cyclicVertexIndex e (n-2))) (cyclicTangent r e) < 0)
      (hAux : auxiliaryGenericity r hr),
      A r hr htr = ∑ T : ChosenEdgeSeparatingSupport r hr e,
        (-1 : ℚ)^((T.val.image Subtype.val).card+1) *
          ∏ c : Component (smoothingDartPermutation r hr.g2 (T.val.image Subtype.val)),
            polygonAmplitude (componentPolygon r hr (T.val.image Subtype.val) c)
              (hAux _ T.property.2 (componentRoot r hr _ c)) := by
    intro r hr htr hAux
    exact mixed_edge_formula hRI r hr e htr hAux
  obtain ⟨F,hF,huniq⟩ := existsUnique_mixed_edge_rhs_continuation hRI n e
  have hΦF : Φ = F := huniq Φ ⟨hlocal,hagree⟩
  have hAF : A = F := huniq A ⟨hAlocal,hAagree⟩
  calc
    Φ q hq ht = F q hq ht := congrArg (fun f => f q hq ht) hΦF
    _ = A q hq ht := (congrArg (fun f => f q hq ht) hAF).symm
    _ = polygonAmplitude q hq := rfl



end DirectGLSSW.SourceMixedEdgeContinuation
