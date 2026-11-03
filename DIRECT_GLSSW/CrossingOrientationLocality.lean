import ActualAuxiliaryDensityTransport

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CrossingOrientationLocality
open LocalCrossingTransport DaughterFirstReturn LocalDaughterTransport
open GeometricSmoothingWeights Filter Topology

/-- Every old actual crossing has the same ordered tangent orientation in a
common configuration-space neighborhood. No daughter genericity is required. -/
theorem eventually_crossing_tangent_pos_iff {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ q' in 𝓝 q, ∀ c : PolygonCrossing q,
      (0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2) ↔
        0 < planarDet (cyclicTangent q' c.val.1) (cyclicTangent q' c.val.2)) := by
  classical
  apply Filter.eventually_all.mpr
  intro c
  have htan (i : Fin n) : Continuous
      (fun q' : Fin n → PlanarPoint ℝ => cyclicTangent q' i) :=
    (continuous_apply (cyclicSuccessor i)).sub (continuous_apply i)
  have hc : Continuous (fun q' : Fin n → PlanarPoint ℝ =>
      planarDet (cyclicTangent q' c.val.1) (cyclicTangent q' c.val.2)) :=
    ((htan c.val.1).fst.mul (htan c.val.2).snd).sub
      ((htan c.val.1).snd.mul (htan c.val.2).fst)
  have hnz := crossing_transverse hq.size_ge_three q hq.g1 c
  by_cases hp : 0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2)
  · filter_upwards [hc.continuousAt.eventually (isOpen_Ioi.mem_nhds hp)] with q' hpos
    exact ⟨fun _ => hpos, fun _ => hp⟩
  · have hn : planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hp) hnz
    filter_upwards [hc.continuousAt.eventually (isOpen_Iio.mem_nhds hn)] with q' hneg
    exact ⟨fun h => False.elim (hp h),
      fun h => False.elim (not_lt_of_ge (le_of_lt hneg) h)⟩

/-- The actual event-order neighborhood can be chosen to preserve ordered
crossing orientation as well. This supplies the over-branch datum required by
a signed-diagram isomorphism of positive diagrams. -/
theorem eventually_configuration_oriented_event_order {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ q' in 𝓝 q, ∃ hq' : CyclicGeneric q',
      ∃ E : PolygonCrossing q ≃ PolygonCrossing q',
        (∀ c, (E c).val = c.val) ∧
        (∀ x y : PolygonEvent q,
          ((polygonEventOrder q hq.g2).lt x y ↔
            (polygonEventOrder q' hq'.g2).lt
              (polygonEventMapEquiv E x) (polygonEventMapEquiv E y))) ∧
        ∀ c : PolygonCrossing q,
          (0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2) ↔
            0 < planarDet (cyclicTangent q' (E c).val.1)
              (cyclicTangent q' (E c).val.2)) := by
  filter_upwards [ConfigurationEventLocality.eventually_configuration_event_order q hq,
    eventually_crossing_tangent_pos_iff q hq] with q' he hp
  obtain ⟨hq', E, hlabels, horder⟩ := he
  refine ⟨hq', E, hlabels, horder, ?_⟩
  intro c
  rw [hlabels c]
  exact hp c

/-- Actual daughter density with the missing orientation datum derived inside
its proof. One nearby polygon simultaneously preserves labels, event order,
ordered crossing orientation, and all support/root daughter point-list formulas. -/
theorem exists_oriented_auxiliary_daughter_transport_mem_nhds {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (U : Set (Fin n → PlanarPoint ℝ)) (hU : U ∈ 𝓝 q) :
    ∃ q' ∈ U, ∃ hq' : CyclicGeneric q',
      auxiliaryGenericity q' hq' ∧
      ∃ E : PolygonCrossing q ≃ PolygonCrossing q',
        (∀ c, (E c).val = c.val) ∧
        (∀ x y : PolygonEvent q,
          ((polygonEventOrder q hq.g2).lt x y ↔
            (polygonEventOrder q' hq'.g2).lt
              (polygonEventMapEquiv E x) (polygonEventMapEquiv E y))) ∧
        (∀ c : PolygonCrossing q,
          (0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2) ↔
            0 < planarDet (cyclicTangent q' (E c).val.1)
              (cyclicTangent q' (E c).val.2))) ∧
        ∀ (S : Finset (PolygonCrossing q)) (root : PolygonEvent q),
          daughterPointList q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root) =
            List.ofFn (daughterVertexFormula q hq.g2 S root q') := by
  obtain ⟨q', hnear, hq', hAux', E, hlabels, horder, hlists⟩ :=
    ActualAuxiliaryDensity.exists_auxiliaryGenericity_daughter_transport_mem_nhds q hq
      (U ∩ {q' | ∀ c : PolygonCrossing q,
        (0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2) ↔
          0 < planarDet (cyclicTangent q' c.val.1) (cyclicTangent q' c.val.2))})
      (Filter.inter_mem hU (eventually_crossing_tangent_pos_iff q hq))
  refine ⟨q', hnear.1, hq', hAux', E, hlabels, horder, ?_, hlists⟩
  intro c
  rw [hlabels c]
  exact hnear.2 c




end DirectGLSSW.CrossingOrientationLocality
