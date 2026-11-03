import UniformDaughterSupportCharacterization

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.UniformDaughterSupportLocality
open TruncationDirection DaughterFirstReturn PermutationOrbits LocalCrossingTransport LocalSupportConjugacy Filter Topology

private theorem retained_map_iff {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (E : PolygonCrossing q ≃ PolygonCrossing q') (S : Finset (PolygonCrossing q))
    (x : PolygonEvent q) : retainedCorner q S x ↔
      retainedCorner q' (S.map E.toEmbedding) (polygonEventMapEquiv E x) := by
  classical
  cases x with
  | inl e => rfl
  | inr v =>
    rcases v with ⟨c, b⟩
    change c ∈ S ↔ E c ∈ S.map E.toEmbedding
    simp

private theorem carrier_labels {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val) (x : PolygonEvent q) :
    incomingCarrier q' (polygonEventMapEquiv E x) = incomingCarrier q x ∧
    polygonEventEdge q' (polygonEventMapEquiv E x) = polygonEventEdge q x := by
  cases x with
  | inl e => exact ⟨rfl, rfl⟩
  | inr v =>
    rcases v with ⟨c, b⟩
    constructor
    · cases b with
      | false => exact congrArg Prod.snd (hlabels c)
      | true => exact congrArg Prod.fst (hlabels c)
    · exact crossingVisit_mapEquiv_edge_eq q q' E hlabels (c, b)

/-- Exact orbit-and-retained-event universal transport, with no choice of root. -/
private theorem forall_retained_orbit_map_iff {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2;
        polygonEventMapEquiv E x < polygonEventMapEquiv E y))
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (R : PolygonEvent q → Prop) (R' : PolygonEvent q' → Prop)
    (hR : ∀ x, R x ↔ R' (polygonEventMapEquiv E x)) :
    (∀ x, retainedCorner q S x →
      componentOf (smoothingDartPermutation q hq.g2 S) x =
        componentOf (smoothingDartPermutation q hq.g2 S) root → R x) ↔
    (∀ y, retainedCorner q' (S.map E.toEmbedding) y →
      componentOf (smoothingDartPermutation q' hq'.g2 (S.map E.toEmbedding)) y =
        componentOf (smoothingDartPermutation q' hq'.g2 (S.map E.toEmbedding))
          (polygonEventMapEquiv E root) → R' y) := by
  let F := polygonEventMapEquiv E
  let CE := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S
  have hcomp (x : PolygonEvent q) :
      CE (componentOf (smoothingDartPermutation q hq.g2 S) x) =
      componentOf (smoothingDartPermutation q' hq'.g2 (S.map E.toEmbedding)) (F x) := rfl
  constructor
  · intro h y hy hc
    obtain ⟨x, rfl⟩ := F.surjective y
    apply (hR x).mp
    apply h x ((retained_map_iff q q' E S x).mpr hy)
    apply CE.injective
    exact (hcomp x).trans (hc.trans (hcomp root).symm)
  · intro h x hx hc
    apply (hR x).mpr
    apply h (F x) ((retained_map_iff q q' E S x).mp hx)
    exact (hcomp x).symm.trans ((congrArg CE hc).trans (hcomp root))

/-- Internal conditional helper. Its sign premise is discharged by finite continuity below. -/
theorem daughterUniform_map_iff_of_carrier_signs {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2;
        polygonEventMapEquiv E x < polygonEventMapEquiv E y))
    (hsign : ∀ x : PolygonEvent q,
      (0 < carrierCornerDet q x ↔ 0 < carrierCornerDet q' (polygonEventMapEquiv E x)) ∧
      (carrierCornerDet q x < 0 ↔ carrierCornerDet q' (polygonEventMapEquiv E x) < 0))
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (hroot : retainedCorner q S root) :
    daughterUniform q hq S root ↔
      daughterUniform q' hq' (S.map E.toEmbedding) (polygonEventMapEquiv E root) := by
  rw [daughterUniform_iff_carrier q hq S root hroot,
    daughterUniform_iff_carrier q' hq' (S.map E.toEmbedding) (polygonEventMapEquiv E root)
      ((retained_map_iff q q' E S root).mp hroot)]
  exact or_congr
    (forall_retained_orbit_map_iff q q' hq hq' E hlabels horder S root _ _
      (fun x => (hsign x).1))
    (forall_retained_orbit_map_iff q q' hq hq' E hlabels horder S root _ _
      (fun x => (hsign x).2))

private theorem uniformDaughterSupport_map_iff_of_carrier_signs {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2;
        polygonEventMapEquiv E x < polygonEventMapEquiv E y))
    (hsign : ∀ x : PolygonEvent q,
      (0 < carrierCornerDet q x ↔ 0 < carrierCornerDet q' (polygonEventMapEquiv E x)) ∧
      (carrierCornerDet q x < 0 ↔ carrierCornerDet q' (polygonEventMapEquiv E x) < 0))
    (S : Finset (PolygonCrossing q)) :
    uniformDaughterSupport q hq S ↔ uniformDaughterSupport q' hq' (S.map E.toEmbedding) := by
  let F := polygonEventMapEquiv E
  let CE := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S
  have hcomp (x : PolygonEvent q) :
      CE (componentOf (smoothingDartPermutation q hq.g2 S) x) =
      componentOf (smoothingDartPermutation q' hq'.g2 (S.map E.toEmbedding)) (F x) := rfl
  constructor
  · rintro ⟨hNA, hCs⟩
    refine ⟨(polygonNonalternating_map_iff q q' hq hq' E hlabels horder S).mp hNA, ?_⟩
    intro C'
    obtain ⟨C, rfl⟩ := CE.surjective C'
    obtain ⟨root, hr, hc, hu⟩ := hCs C
    refine ⟨F root, (retained_map_iff q q' E S root).mp hr, ?_, ?_⟩
    · exact (hcomp root).symm.trans (congrArg CE hc)
    · exact (daughterUniform_map_iff_of_carrier_signs q q' hq hq' E hlabels horder
        hsign S root hr).mp hu
  · rintro ⟨hNA, hCs⟩
    refine ⟨(polygonNonalternating_map_iff q q' hq hq' E hlabels horder S).mpr hNA, ?_⟩
    intro C
    obtain ⟨root', hr', hc', hu'⟩ := hCs (CE C)
    obtain ⟨root, rfl⟩ := F.surjective root'
    have hr := (retained_map_iff q q' E S root).mpr hr'
    refine ⟨root, hr, ?_, ?_⟩
    · apply CE.injective
      exact (hcomp root).trans hc'
    · exact (daughterUniform_map_iff_of_carrier_signs q q' hq hq' E hlabels horder
        hsign S root hr).mpr hu'

private theorem carrierCornerDet_ne_zero {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (x : PolygonEvent q) : carrierCornerDet q x ≠ 0 := by
  cases x with
  | inl e =>
    have hsucc : cyclicSuccessor ((cyclicSuccessorPerm n)⁻¹ e) = e :=
      Equiv.apply_symm_apply (cyclicSuccessorPerm n) e
    have h := cyclic_turn_det_ne_zero hq.size_ge_three q hq.g1 ((cyclicSuccessorPerm n)⁻¹ e)
    simpa only [carrierCornerDet, incomingCarrier, polygonEventEdge, hsucc] using h
  | inr v =>
    rcases v with ⟨c, b⟩
    have h := crossing_transverse hq.size_ge_three q hq.g1 c
    cases b with
    | false =>
      change planarDet (cyclicTangent q c.val.2) (cyclicTangent q c.val.1) ≠ 0
      rw [planarDet_swap]
      exact neg_ne_zero.mpr h
    | true => exact h

private theorem eventually_carrier_signs {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) :
    ∀ᶠ q' in 𝓝 q, ∀ x : PolygonEvent q,
      let d := planarDet (cyclicTangent q' (incomingCarrier q x))
        (cyclicTangent q' (polygonEventEdge q x))
      (0 < carrierCornerDet q x ↔ 0 < d) ∧
      (carrierCornerDet q x < 0 ↔ d < 0) := by
  have h (x : PolygonEvent q) : ∀ᶠ q' in 𝓝 q,
      let d := planarDet (cyclicTangent q' (incomingCarrier q x))
        (cyclicTangent q' (polygonEventEdge q x))
      (0 < carrierCornerDet q x ↔ 0 < d) ∧
      (carrierCornerDet q x < 0 ↔ d < 0) := by
    let f := fun r : Fin n → PlanarPoint ℝ =>
      planarDet (cyclicTangent r (incomingCarrier q x))
        (cyclicTangent r (polygonEventEdge q x))
    have ht (e : Fin n) : Continuous (fun r : Fin n → PlanarPoint ℝ => cyclicTangent r e) :=
      (continuous_apply (cyclicSuccessor e)).sub (continuous_apply e)
    have hf : ContinuousAt f q :=
      (((ht _).fst.mul (ht _).snd).sub ((ht _).snd.mul (ht _).fst)).continuousAt
    have hn : f q ≠ 0 := carrierCornerDet_ne_zero q hq x
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · have he : ∀ᶠ q' in 𝓝 q, f q' < 0 := hf.eventually (isOpen_Iio.mem_nhds hneg)
      filter_upwards [he] with q' hd
      exact ⟨iff_of_false (not_lt_of_ge (le_of_lt hneg)) (not_lt_of_ge (le_of_lt hd)),
        iff_of_true hneg hd⟩
    · have he : ∀ᶠ q' in 𝓝 q, 0 < f q' := hf.eventually (isOpen_Ioi.mem_nhds hpos)
      filter_upwards [he] with q' hd
      exact ⟨iff_of_true hpos hd,
        iff_of_false (not_lt_of_ge (le_of_lt hpos)) (not_lt_of_ge (le_of_lt hd))⟩
  exact Filter.eventually_all.mpr h

/-- Full-parent locality of the exact uniform separating support predicate.
The transport is universally quantified so it is the SAME E used for the actual
daughter diagrams, rotations and final corner-sum reindexing. -/
theorem eventually_uniformDaughterSupport_map_iff {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ q' in 𝓝 q, ∀ (hq' : CyclicGeneric q')
      (E : PolygonCrossing q ≃ PolygonCrossing q')
      (hlabels : ∀ c, (E c).val = c.val)
      (horder : ∀ x y : PolygonEvent q,
        (letI := polygonEventOrder q hq.g2; x < y) ↔
        (letI := polygonEventOrder q' hq'.g2;
          polygonEventMapEquiv E x < polygonEventMapEquiv E y))
      (S : Finset (PolygonCrossing q)),
      uniformDaughterSupport q hq S ↔ uniformDaughterSupport q' hq' (S.map E.toEmbedding) := by
  filter_upwards [eventually_carrier_signs q hq] with q' hs
  intro hq' E hlabels horder S
  apply uniformDaughterSupport_map_iff_of_carrier_signs q q' hq hq' E hlabels horder
  intro x
  have h := hs x
  have hl := carrier_labels q q' E hlabels x
  simpa only [carrierCornerDet, hl.1, hl.2] using h

/-- Existence of a single common label/order transport, with the actual uniform
support equivalence discharged on the full parent G1/G2 domain. -/
theorem eventually_configuration_uniform_support_transport {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ q' in 𝓝 q, ∃ hq' : CyclicGeneric q',
      ∃ E : PolygonCrossing q ≃ PolygonCrossing q',
      ∃ hlabels : ∀ c, (E c).val = c.val,
      ∃ horder : ∀ x y : PolygonEvent q,
        (letI := polygonEventOrder q hq.g2; x < y) ↔
        (letI := polygonEventOrder q' hq'.g2;
          polygonEventMapEquiv E x < polygonEventMapEquiv E y),
      ∀ S : Finset (PolygonCrossing q),
        uniformDaughterSupport q hq S ↔ uniformDaughterSupport q' hq' (S.map E.toEmbedding) := by
  filter_upwards [ConfigurationEventLocality.eventually_configuration_event_order q hq,
    eventually_uniformDaughterSupport_map_iff q hq] with q' he hu
  obtain ⟨hq', E, hlabels, horder⟩ := he
  exact ⟨hq', E, hlabels, horder, hu hq' E hlabels horder⟩

/-- Unfolded consumer-facing statement: the literal final Supports predicate,
including every component and its existential retained root, is locally transported. -/
theorem eventually_literal_uniform_support_map_iff {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ q' in 𝓝 q, ∀ (hq' : CyclicGeneric q')
      (E : PolygonCrossing q ≃ PolygonCrossing q')
      (hlabels : ∀ c, (E c).val = c.val)
      (horder : ∀ x y : PolygonEvent q,
        (letI := polygonEventOrder q hq.g2; x < y) ↔
        (letI := polygonEventOrder q' hq'.g2;
          polygonEventMapEquiv E x < polygonEventMapEquiv E y))
      (S : Finset (PolygonCrossing q)),
      (PolygonNonalternation.polygonNonalternating q hq.g2 S ∧
        ∀ C : Component (smoothingDartPermutation q hq.g2 S),
          ∃ root : PolygonEvent q, retainedCorner q S root ∧
            componentOf (smoothingDartPermutation q hq.g2 S) root = C ∧
            ((∀ i : Fin (Fintype.card (CornerCoord q hq.g2 S root)),
              0 < planarDet
                (daughterSideVector q hq.g2 S root
                  ((cyclicSuccessorPerm (Fintype.card (CornerCoord q hq.g2 S root)))⁻¹ i))
                (daughterSideVector q hq.g2 S root i)) ∨
             (∀ i : Fin (Fintype.card (CornerCoord q hq.g2 S root)),
              planarDet
                (daughterSideVector q hq.g2 S root
                  ((cyclicSuccessorPerm (Fintype.card (CornerCoord q hq.g2 S root)))⁻¹ i))
                (daughterSideVector q hq.g2 S root i) < 0))) ↔
      (PolygonNonalternation.polygonNonalternating q' hq'.g2 (S.map E.toEmbedding) ∧
        ∀ C : Component (smoothingDartPermutation q' hq'.g2 (S.map E.toEmbedding)),
          ∃ root : PolygonEvent q', retainedCorner q' (S.map E.toEmbedding) root ∧
            componentOf (smoothingDartPermutation q' hq'.g2 (S.map E.toEmbedding)) root = C ∧
            ((∀ i : Fin (Fintype.card (CornerCoord q' hq'.g2 (S.map E.toEmbedding) root)),
              0 < planarDet
                (daughterSideVector q' hq'.g2 (S.map E.toEmbedding) root
                  ((cyclicSuccessorPerm (Fintype.card (CornerCoord q' hq'.g2 (S.map E.toEmbedding) root)))⁻¹ i))
                (daughterSideVector q' hq'.g2 (S.map E.toEmbedding) root i)) ∨
             (∀ i : Fin (Fintype.card (CornerCoord q' hq'.g2 (S.map E.toEmbedding) root)),
              planarDet
                (daughterSideVector q' hq'.g2 (S.map E.toEmbedding) root
                  ((cyclicSuccessorPerm (Fintype.card (CornerCoord q' hq'.g2 (S.map E.toEmbedding) root)))⁻¹ i))
                (daughterSideVector q' hq'.g2 (S.map E.toEmbedding) root i) < 0))) := by
  exact eventually_uniformDaughterSupport_map_iff q hq

end DirectGLSSW.UniformDaughterSupportLocality
