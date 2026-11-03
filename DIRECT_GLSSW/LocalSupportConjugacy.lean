import DirectGLSSW.PolygonNonalternation
import LocalPolygonEventOrder

set_option autoImplicit false

namespace DirectGLSSW.LocalSupportConjugacy

open DirectGLSSW
open DirectGLSSW.TruncationDirection
open DirectGLSSW.LocalCrossingTransport
open DirectGLSSW.PermutationOrbits

/-- A pair-label-preserving, order-preserving crossing equivalence transports
literal actual-event nonalternation of every selected support. -/
theorem polygonNonalternating_map_iff {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; polygonEventMapEquiv E x < polygonEventMapEquiv E y))
    (S : Finset (PolygonCrossing q)) :
    PolygonNonalternation.polygonNonalternating q hq.g2 S ↔
      PolygonNonalternation.polygonNonalternating q' hq'.g2 (S.map E.toEmbedding) := by
  let F := polygonEventMapEquiv E
  letI : LinearOrder (Fin n ⊕ (PolygonCrossing q × Bool)) := by
    change LinearOrder (Fin n ⊕ CrossingVisit q)
    exact polygonEventOrder q hq.g2
  letI : LinearOrder (Fin n ⊕ (PolygonCrossing q' × Bool)) := by
    change LinearOrder (Fin n ⊕ CrossingVisit q')
    exact polygonEventOrder q' hq'.g2
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := by
    change LinearOrder (Fin n ⊕ CrossingVisit q)
    exact polygonEventOrder q hq.g2
  letI : LinearOrder (Fin n ⊕ CrossingVisit q') := polygonEventOrder q' hq'.g2
  letI : LinearOrder (PolygonEvent q') := by
    change LinearOrder (Fin n ⊕ CrossingVisit q')
    exact polygonEventOrder q' hq'.g2
  have hcyc (x y z : PolygonEvent q) :
      FiniteCycleOrder.strictCyclicBetween x y z ↔
        FiniteCycleOrder.strictCyclicBetween (F x) (F y) (F z) := by
    simp [FiniteCycleOrder.strictCyclicBetween, F, horder]
  constructor
  · intro hS
    change ∀ c ∈ S.map E.toEmbedding, ∀ d ∈ S.map E.toEmbedding, c ≠ d →
      (FiniteCycleOrder.strictCyclicBetween (Sum.inr (c, false))
        (Sum.inr (d, false)) (Sum.inr (c, true)) ↔
       FiniteCycleOrder.strictCyclicBetween (Sum.inr (c, false))
        (Sum.inr (d, true)) (Sum.inr (c, true)))
    intro c hc d hd hcd
    rcases Finset.mem_map.mp hc with ⟨c₀, hc₀, rfl⟩
    rcases Finset.mem_map.mp hd with ⟨d₀, hd₀, rfl⟩
    have hcd₀ : c₀ ≠ d₀ := fun heq => hcd (congrArg E heq)
    have hab := hS c₀ hc₀ d₀ hd₀ hcd₀
    change (FiniteCycleOrder.strictCyclicBetween (Sum.inr (c₀, false))
        (Sum.inr (d₀, false)) (Sum.inr (c₀, true)) ↔
      FiniteCycleOrder.strictCyclicBetween (Sum.inr (c₀, false))
        (Sum.inr (d₀, true)) (Sum.inr (c₀, true))) at hab
    have h₁ := hcyc (Sum.inr (c₀, false)) (Sum.inr (d₀, false)) (Sum.inr (c₀, true))
    have h₂ := hcyc (Sum.inr (c₀, false)) (Sum.inr (d₀, true)) (Sum.inr (c₀, true))
    simpa [F, polygonEventMapEquiv, crossingVisit_mapEquiv] using
      ⟨fun h => h₂.mp (hab.mp (h₁.mpr h)),
       fun h => h₁.mp (hab.mpr (h₂.mpr h))⟩
  · intro hS
    change ∀ c ∈ S, ∀ d ∈ S, c ≠ d →
      (FiniteCycleOrder.strictCyclicBetween (Sum.inr (c, false))
        (Sum.inr (d, false)) (Sum.inr (c, true)) ↔
       FiniteCycleOrder.strictCyclicBetween (Sum.inr (c, false))
        (Sum.inr (d, true)) (Sum.inr (c, true)))
    intro c hc d hd hcd
    have hc' : E c ∈ S.map E.toEmbedding := Finset.mem_map.mpr ⟨c, hc, rfl⟩
    have hd' : E d ∈ S.map E.toEmbedding := Finset.mem_map.mpr ⟨d, hd, rfl⟩
    have hcd' : E c ≠ E d := fun heq => hcd (E.injective heq)
    have hab := hS (E c) hc' (E d) hd' hcd'
    change (FiniteCycleOrder.strictCyclicBetween (Sum.inr (E c, false))
        (Sum.inr (E d, false)) (Sum.inr (E c, true)) ↔
      FiniteCycleOrder.strictCyclicBetween (Sum.inr (E c, false))
        (Sum.inr (E d, true)) (Sum.inr (E c, true))) at hab
    have h₁ := hcyc (Sum.inr (c, false)) (Sum.inr (d, false)) (Sum.inr (c, true))
    have h₂ := hcyc (Sum.inr (c, false)) (Sum.inr (d, true)) (Sum.inr (c, true))
    simpa [F, polygonEventMapEquiv, crossingVisit_mapEquiv] using
      ⟨fun h => h₂.mpr (hab.mp (h₁.mp h)),
       fun h => h₁.mpr (hab.mpr (h₂.mp h))⟩

private theorem smoothingPairing_map {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ) (E : PolygonCrossing q ≃ PolygonCrossing q')
    (S : Finset (PolygonCrossing q)) (S' : Finset (PolygonCrossing q'))
    (hmem : ∀ c, c ∈ S ↔ E c ∈ S') (x : PolygonEvent q) :
    polygonEventMapEquiv E (smoothingPairing q S x) =
      smoothingPairing q' S' (polygonEventMapEquiv E x) := by
  classical
  cases x with
  | inl e => rfl
  | inr v =>
    rcases v with ⟨c, b⟩
    have hF (c : PolygonCrossing q) (b : Bool) :
        polygonEventMapEquiv E (Sum.inr (c, b)) = Sum.inr (E c, b) := rfl
    rw [smoothingPairing_apply, smoothingPairing_apply]
    simp only [smoothingPairingMap]
    by_cases hc : c ∈ S
    · have hEc : E c ∈ S' := (hmem c).mp hc
      simp only [if_pos hc]
      conv_rhs => rw [hF c b]
      simp only [if_pos hEc]
      exact hF c (!b)
    · have hEc : E c ∉ S' := fun h => hc ((hmem c).mpr h)
      simp only [if_neg hc]
      conv_rhs => rw [hF c b]
      simp only [if_neg hEc]
      exact hF c b

/-- The actual dart permutation commutes with event relabelling, including
both the selected crossing pairing and the cyclic successor. -/
theorem smoothingDartPermutation_map {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; polygonEventMapEquiv E x < polygonEventMapEquiv E y))
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    polygonEventMapEquiv E (smoothingDartPermutation q hq.g2 S x) =
      smoothingDartPermutation q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E x) := by
  let F := polygonEventMapEquiv E
  letI : LinearOrder (Fin n ⊕ (PolygonCrossing q × Bool)) := by
    change LinearOrder (Fin n ⊕ CrossingVisit q)
    exact polygonEventOrder q hq.g2
  letI : LinearOrder (Fin n ⊕ (PolygonCrossing q' × Bool)) := by
    change LinearOrder (Fin n ⊕ CrossingVisit q')
    exact polygonEventOrder q' hq'.g2
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := by
    change LinearOrder (Fin n ⊕ CrossingVisit q)
    exact polygonEventOrder q hq.g2
  letI : LinearOrder (Fin n ⊕ CrossingVisit q') := polygonEventOrder q' hq'.g2
  letI : LinearOrder (PolygonEvent q') := by
    change LinearOrder (Fin n ⊕ CrossingVisit q')
    exact polygonEventOrder q' hq'.g2
  let e : PolygonEvent q ≃o PolygonEvent q' := {
    toEquiv := F
    map_rel_iff' := by
      intro a b
      constructor
      · intro hab
        apply le_of_not_gt
        intro hba
        exact (not_lt_of_ge hab) ((horder b a).mp hba)
      · intro hab
        apply le_of_not_gt
        intro hba
        exact (not_lt_of_ge hab) ((horder b a).mpr hba)
  }
  have hsucc (y : PolygonEvent q) :
      F (polygonEventSuccessor q hq.g2 y) = polygonEventSuccessor q' hq'.g2 (F y) := by
    simpa [F, polygonEventSuccessor] using
      (orderedCyclicSuccessor_naturality (PolygonEvent q) e y).symm
  have hmem (c : PolygonCrossing q) :
      c ∈ S ↔ E c ∈ S.map E.toEmbedding := by
    simp
  rw [smoothingDartPermutation_apply, smoothingDartPermutation_apply]
  rw [smoothingPairing_map q q' E S (S.map E.toEmbedding) hmem]
  rw [hsucc]

/-- The relabelling induces an equivalence of the full actual smoothing orbit
quotients, preserving the chosen representative map exactly. -/
noncomputable def smoothingComponentMapEquiv {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; polygonEventMapEquiv E x < polygonEventMapEquiv E y))
    (S : Finset (PolygonCrossing q)) :
    Component (smoothingDartPermutation q hq.g2 S) ≃
      Component (smoothingDartPermutation q' hq'.g2 (S.map E.toEmbedding)) :=
  componentEquivOfIntertwining (polygonEventMapEquiv E)
    (smoothingDartPermutation q hq.g2 S)
    (smoothingDartPermutation q' hq'.g2 (S.map E.toEmbedding))
    (smoothingDartPermutation_map q q' hq hq' E hlabels horder S)

@[simp] theorem smoothingComponentMapEquiv_componentOf {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; polygonEventMapEquiv E x < polygonEventMapEquiv E y))
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    smoothingComponentMapEquiv q q' hq hq' E hlabels horder S
      (componentOf (smoothingDartPermutation q hq.g2 S) x) =
    componentOf (smoothingDartPermutation q' hq'.g2 (S.map E.toEmbedding))
      (polygonEventMapEquiv E x) := rfl

end DirectGLSSW.LocalSupportConjugacy





