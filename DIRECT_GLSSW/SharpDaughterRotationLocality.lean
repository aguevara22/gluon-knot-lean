import SharpDaughterTurnContinuity

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SharpDaughterRotationLocality
open PermutationOrbits PrincipalTurning PolygonDrawingBridge SharpDaughter SharpDaughterRotation
open LocalCrossingTransport LocalSupportConjugacy Filter Topology
open scoped BigOperators

/-- One actual sharp component's source rotation integer is locally fixed under
any label/order-preserving transport. Original or nearby daughter G1 is not
required. The integer gap is derived from the actual total-turn characterization. -/
theorem eventually_sharpDaughterRotationInteger {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S) :
    ∀ᶠ q' in 𝓝 q, ∀ (hq' : CyclicGeneric q')
      (E : PolygonCrossing q ≃ PolygonCrossing q')
      (hlabels : ∀ c, (E c).val = c.val)
      (horder : ∀ x y : PolygonEvent q,
        (letI := polygonEventOrder q hq.g2; x < y) ↔
        (letI := polygonEventOrder q' hq'.g2;
          polygonEventMapEquiv E x < polygonEventMapEquiv E y)),
      sharpDaughterRotationInteger q hq S C hNA =
        sharpDaughterRotationInteger q' hq' (S.map E.toEmbedding)
          (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)
          ((polygonNonalternating_map_iff q q' hq hq' E hlabels horder S).mp hNA) := by
  let F := fun r : Fin n → PlanarPoint ℝ => ∑ a : Arc q hq S C,
    Complex.arg (polygonEdgeVector r (polygonEventEdge q (P q hq S a.val)) /
      polygonEdgeVector r (polygonEventEdge q a.val))
  have hF : ContinuousAt F q := continuousAt_fixed_event_turn_sum q hq S C hNA
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have he : ∀ᶠ q' in 𝓝 q, |F q' - F q| < 2 * Real.pi :=
    ((hF.sub continuousAt_const).abs).eventually
      (isOpen_Iio.mem_nhds (by simpa using hp))
  have hFq : F q = (sharpDaughterRotationInteger q hq S C hNA : ℝ) * (2 * Real.pi) := by
    have hsum : totalTurn (sharpDaughterDiagram q hq S C hNA) = F q :=
      Fintype.sum_equiv (arcEquiv q hq S C) _ _ (actual_turn q hq S C hNA)
    exact hsum.symm.trans (sharpDaughterRotationInteger_spec q hq S C hNA).1
  filter_upwards [he] with q' hnear
  intro hq' E hlabels horder
  let C' := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C
  let hNA' := (polygonNonalternating_map_iff q q' hq hq' E hlabels horder S).mp hNA
  let r := sharpDaughterRotationInteger q hq S C hNA
  let r' := sharpDaughterRotationInteger q' hq' (S.map E.toEmbedding) C' hNA'
  have hFq' : F q' = (r' : ℝ) * (2 * Real.pi) :=
    (totalTurn_eq_fixed_event_sum q q' hq hq' E hlabels horder S C hNA).symm.trans
      (sharpDaughterRotationInteger_spec q' hq' (S.map E.toEmbedding) C' hNA').1
  change r = r'
  rw [hFq, hFq', ← sub_mul, abs_mul, abs_of_pos hp] at hnear
  have hsmall : |(r' : ℝ) - (r : ℝ)| < 1 := by
    apply (mul_lt_mul_right hp).mp
    simpa only [one_mul] using hnear
  have hi : |r' - r| < (1 : ℤ) := by exact_mod_cast hsmall
  have hi' := abs_lt.mp hi
  omega

/-- One common neighborhood controls every actual separating support and every
sharp component. The quantification over the transport is universal, so callers
can use the same map as their signed-diagram and uniform-support consumers. -/
theorem eventually_all_sharpDaughterRotationIntegers {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ q' in 𝓝 q, ∀ (hq' : CyclicGeneric q')
      (E : PolygonCrossing q ≃ PolygonCrossing q')
      (hlabels : ∀ c, (E c).val = c.val)
      (horder : ∀ x y : PolygonEvent q,
        (letI := polygonEventOrder q hq.g2; x < y) ↔
        (letI := polygonEventOrder q' hq'.g2;
          polygonEventMapEquiv E x < polygonEventMapEquiv E y))
      (S : Finset (PolygonCrossing q))
      (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
      (C : Component (P q hq S)),
      sharpDaughterRotationInteger q hq S C hNA =
        sharpDaughterRotationInteger q' hq' (S.map E.toEmbedding)
          (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)
          ((polygonNonalternating_map_iff q q' hq hq' E hlabels horder S).mp hNA) := by
  classical
  have hS : ∀ S : Finset (PolygonCrossing q), ∀ᶠ q' in 𝓝 q,
      ∀ (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
        (C : Component (P q hq S)) (hq' : CyclicGeneric q')
        (E : PolygonCrossing q ≃ PolygonCrossing q')
        (hlabels : ∀ c, (E c).val = c.val)
        (horder : ∀ x y : PolygonEvent q,
          (letI := polygonEventOrder q hq.g2; x < y) ↔
          (letI := polygonEventOrder q' hq'.g2;
            polygonEventMapEquiv E x < polygonEventMapEquiv E y)),
      sharpDaughterRotationInteger q hq S C hNA =
        sharpDaughterRotationInteger q' hq' (S.map E.toEmbedding)
          (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)
          ((polygonNonalternating_map_iff q q' hq hq' E hlabels horder S).mp hNA) := by
    intro S
    by_cases hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S
    · have hC := Filter.eventually_all.mpr
        (fun C : Component (P q hq S) => eventually_sharpDaughterRotationInteger q hq S C hNA)
      filter_upwards [hC] with q' h
      intro hNA' C hq' E hlabels horder
      exact h C hq' E hlabels horder
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hNA h))
  filter_upwards [Filter.eventually_all.mpr hS] with q' h
  intro hq' E hlabels horder S hNA C
  exact h S hNA C hq' E hlabels horder

/-- Actual nearby G1/G2 configurations admit one common labels/order transport
preserving every sharp daughter rotation integer. No conditional transport
existence or rotation equality is left as an assumption. -/
theorem eventually_configuration_rotation_transport {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ q' in 𝓝 q, ∃ hq' : CyclicGeneric q',
      ∃ E : PolygonCrossing q ≃ PolygonCrossing q',
      ∃ hlabels : ∀ c, (E c).val = c.val,
      ∃ horder : ∀ x y : PolygonEvent q,
        (letI := polygonEventOrder q hq.g2; x < y) ↔
        (letI := polygonEventOrder q' hq'.g2;
          polygonEventMapEquiv E x < polygonEventMapEquiv E y),
      ∀ (S : Finset (PolygonCrossing q))
        (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
        (C : Component (P q hq S)),
      sharpDaughterRotationInteger q hq S C hNA =
        sharpDaughterRotationInteger q' hq' (S.map E.toEmbedding)
          (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)
          ((polygonNonalternating_map_iff q q' hq hq' E hlabels horder S).mp hNA) := by
  filter_upwards [ConfigurationEventLocality.eventually_configuration_event_order q hq,
    eventually_all_sharpDaughterRotationIntegers q hq] with q' he hr
  obtain ⟨hq', E, hlabels, horder⟩ := he
  exact ⟨hq', E, hlabels, horder, hr hq' E hlabels horder⟩




end DirectGLSSW.HOMFLY.SharpDaughterRotationLocality
