import DirectGLSSW.ChordNonalternation
import DirectGLSSW.SmoothingPermutations
import DirectGLSSW.OrbitNormalization

set_option autoImplicit false

namespace DirectGLSSW.PolygonNonalternation

open FiniteCycleOrder PermutationOrbits
attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] [LinearOrder K] {n : ℕ}

/-- The increasing enumeration identifies actual events with their finite ordered coordinates. -/
noncomputable def eventEnumeration (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) :
    Fin (Fintype.card (PolygonEvent q)) ≃ PolygonEvent q :=
  (polygonEventEnumeration q hq).toEquiv

/-- The chord endpoints are their actual false/true visits in event order. -/
noncomputable def actualEndpoint (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) :
    PolygonCrossing q × Bool → Fin (Fintype.card (PolygonEvent q)) :=
  fun v => (eventEnumeration q hq).symm (Sum.inr v)

@[simp] theorem eventEnumeration_actualEndpoint (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (c : PolygonCrossing q) (b : Bool) :
    eventEnumeration q hq (actualEndpoint q hq (c, b)) = Sum.inr (c, b) := by
  simp [actualEndpoint, eventEnumeration]

theorem actualEndpoint_injective (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) :
    Function.Injective (actualEndpoint q hq) := by
  intro a b hab
  rcases a with ⟨ca, ba⟩
  rcases b with ⟨cb, bb⟩
  have h := congrArg (eventEnumeration q hq) hab
  rw [eventEnumeration_actualEndpoint q hq ca ba,
    eventEnumeration_actualEndpoint q hq cb bb] at h
  exact Sum.inr.inj h

private noncomputable def actualEventStrictCyclicBetween (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (x y z : PolygonEvent q) : Prop := by
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq
  exact strictCyclicBetween x y z

/-- Pairwise nonalternation in the literal order of actual polygon events. Anchors remain in this ordered event circle. -/
def polygonNonalternating (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) : Prop := by
  exact ∀ c ∈ S, ∀ d ∈ S, c ≠ d →
    (actualEventStrictCyclicBetween q hq (Sum.inr (c, false))
        (Sum.inr (d, false)) (Sum.inr (c, true)) ↔
     actualEventStrictCyclicBetween q hq (Sum.inr (c, false))
        (Sum.inr (d, true)) (Sum.inr (c, true)))

theorem polygonNonalternating_iff_abstract (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) :
    polygonNonalternating q hq S ↔
      ChordNonalternation.Nonalternating (actualEndpoint q hq) S := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
  letI : LinearOrder (PolygonEvent q) := by
    change LinearOrder (Fin n ⊕ CrossingVisit q)
    exact polygonEventOrder q hq
  constructor
  · intro h
    change (∀ c ∈ S, ∀ d ∈ S, c ≠ d → _) at h
    intro c hc d hd hcd
    have ha := h c hc d hd hcd
    have h₁ :
        actualEventStrictCyclicBetween q hq (Sum.inr (c, false))
          (Sum.inr (d, false)) (Sum.inr (c, true)) ↔
        strictCyclicBetween (actualEndpoint q hq (c, false))
          (actualEndpoint q hq (d, false)) (actualEndpoint q hq (c, true)) := by
      simpa [eventEnumeration, actualEndpoint] using
        (@strictCyclicBetween_orderIso (Fin (Fintype.card (PolygonEvent q)))
          (PolygonEvent q) inferInstance (polygonEventOrder q hq)
          (polygonEventEnumeration q hq) (actualEndpoint q hq (c, false))
          (actualEndpoint q hq (d, false)) (actualEndpoint q hq (c, true)) )
    have h₂ :
        actualEventStrictCyclicBetween q hq (Sum.inr (c, false))
          (Sum.inr (d, true)) (Sum.inr (c, true)) ↔
        strictCyclicBetween (actualEndpoint q hq (c, false))
          (actualEndpoint q hq (d, true)) (actualEndpoint q hq (c, true)) := by
      simpa [eventEnumeration, actualEndpoint] using
        (@strictCyclicBetween_orderIso (Fin (Fintype.card (PolygonEvent q)))
          (PolygonEvent q) inferInstance (polygonEventOrder q hq)
          (polygonEventEnumeration q hq) (actualEndpoint q hq (c, false))
          (actualEndpoint q hq (d, true)) (actualEndpoint q hq (c, true)) )
    exact ⟨fun h => h₂.mp (ha.mp (h₁.mpr h)),
      fun h => h₁.mp (ha.mpr (h₂.mpr h))⟩
  · intro h
    change (∀ c ∈ S, ∀ d ∈ S, c ≠ d →
      (actualEventStrictCyclicBetween q hq (Sum.inr (c, false))
        (Sum.inr (d, false)) (Sum.inr (c, true)) ↔
       actualEventStrictCyclicBetween q hq (Sum.inr (c, false))
        (Sum.inr (d, true)) (Sum.inr (c, true))))
    intro c hc d hd hcd
    have hh := h c hc d hd hcd
    have h₁ :
        actualEventStrictCyclicBetween q hq (Sum.inr (c, false))
          (Sum.inr (d, false)) (Sum.inr (c, true)) ↔
        strictCyclicBetween (actualEndpoint q hq (c, false))
          (actualEndpoint q hq (d, false)) (actualEndpoint q hq (c, true)) := by
      simpa [eventEnumeration, actualEndpoint] using
        (@strictCyclicBetween_orderIso (Fin (Fintype.card (PolygonEvent q)))
          (PolygonEvent q) inferInstance (polygonEventOrder q hq)
          (polygonEventEnumeration q hq) (actualEndpoint q hq (c, false))
          (actualEndpoint q hq (d, false)) (actualEndpoint q hq (c, true)) )
    have h₂ :
        actualEventStrictCyclicBetween q hq (Sum.inr (c, false))
          (Sum.inr (d, true)) (Sum.inr (c, true)) ↔
        strictCyclicBetween (actualEndpoint q hq (c, false))
          (actualEndpoint q hq (d, true)) (actualEndpoint q hq (c, true)) := by
      simpa [eventEnumeration, actualEndpoint] using
        (@strictCyclicBetween_orderIso (Fin (Fintype.card (PolygonEvent q)))
          (PolygonEvent q) inferInstance (polygonEventOrder q hq)
          (polygonEventEnumeration q hq) (actualEndpoint q hq (c, false))
          (actualEndpoint q hq (d, true)) (actualEndpoint q hq (c, true)) )
    exact ⟨fun h₁v => h₂.mpr (hh.mp (h₁.mp h₁v)),
      fun h₂v => h₁.mpr (hh.mpr (h₂.mp h₂v))⟩

/-- A singleton actual cut is the conjugate of the actual visit pairing. -/
theorem singletonSwap_intertwines (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (c : PolygonCrossing q)
    (i : Fin (Fintype.card (PolygonEvent q))) :
    eventEnumeration q hq (ChordNonalternation.chordSwap (actualEndpoint q hq) c i) =
      smoothingPairing q {c} (eventEnumeration q hq i) := by
  classical
  rw [ChordNonalternation.chordSwap, smoothingPairing_singleton]
  have h0 := eventEnumeration_actualEndpoint q hq c false
  have h1 := eventEnumeration_actualEndpoint q hq c true
  by_cases h0i : i = actualEndpoint q hq (c, false)
  · subst i
    simp [Equiv.swap_apply_def, h0, h1]
  · by_cases h1i : i = actualEndpoint q hq (c, true)
    · subst i
      simp [Equiv.swap_apply_def, h0, h1]
    · have h0i' : eventEnumeration q hq i ≠ Sum.inr (c, false) := by
        intro heq
        apply h0i
        apply (eventEnumeration q hq).injective
        exact heq.trans h0.symm
      have h1i' : eventEnumeration q hq i ≠ Sum.inr (c, true) := by
        intro heq
        apply h1i
        apply (eventEnumeration q hq).injective
        exact heq.trans h1.symm
      simp [Equiv.swap_apply_def, h0, h1, h0i, h1i, h0i', h1i']

theorem smoothingPairing_insert (q : Fin n → PlanarPoint K)
    [DecidableEq (PolygonCrossing q)] (S : Finset (PolygonCrossing q))
    (c : PolygonCrossing q) (hc : c ∉ S) :
    smoothingPairing q (insert c S) = smoothingPairing q {c} * smoothingPairing q S := by
  classical
  ext x
  cases x with
  | inl e => rfl
  | inr v =>
      rcases v with ⟨d, b⟩
      by_cases hdc : d = c
      · subst d
        cases b <;> simp [smoothingPairing, smoothingPairingMap, hc,
          crossingVisitFlip, Equiv.Perm.mul_apply]
      · by_cases hds : d ∈ S
        · cases b <;> simp [smoothingPairing, smoothingPairingMap, hds,
            hdc, crossingVisitFlip, Equiv.Perm.mul_apply]
        · cases b <;> simp [smoothingPairing, smoothingPairingMap, hds,
            hdc, crossingVisitFlip, Equiv.Perm.mul_apply]

/-- The finite abstract transposition product is exactly the actual selected visit pairing under the increasing event enumeration. -/
theorem swapProduct_intertwines (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (i : Fin (Fintype.card (PolygonEvent q))) :
    eventEnumeration q hq
        (ChordNonalternation.swapProduct (actualEndpoint q hq)
          (actualEndpoint_injective q hq) S i) =
      smoothingPairing q S (eventEnumeration q hq i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [ChordNonalternation.swapProduct_empty, smoothingPairing_empty]
  | @insert c S hc ih =>
      rw [ChordNonalternation.swapProduct_insert (actualEndpoint q hq)
        (actualEndpoint_injective q hq) S c hc, Equiv.Perm.mul_apply]
      rw [singletonSwap_intertwines q hq c,
        smoothingPairing_insert q S c hc, Equiv.Perm.mul_apply, ih]

/-- Increasing-order coordinates preserve the original oriented event successor. -/
theorem successor_intertwines (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q)
    (i : Fin (Fintype.card (PolygonEvent q))) :
    eventEnumeration q hq (cyclicSuccessorPerm (Fintype.card (PolygonEvent q)) i) =
      polygonEventSuccessor q hq (eventEnumeration q hq i) := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
  rw [polygonEventSuccessor_apply]
  simp [eventEnumeration, polygonEventEnumeration, cyclicSuccessorPerm_apply]

theorem incoming_intertwines (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (i : Fin (Fintype.card (PolygonEvent q))) :
    eventEnumeration q hq (ChordNonalternation.smoothing (actualEndpoint q hq)
        (actualEndpoint_injective q hq) S i) =
      smoothingIncomingPermutation q hq S (eventEnumeration q hq i) := by
  simp only [ChordNonalternation.smoothing, Equiv.Perm.mul_apply,
    smoothingIncomingPermutation_apply]
  rw [successor_intertwines, swapProduct_intertwines]

theorem dart_intertwines (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (i : Fin (Fintype.card (PolygonEvent q))) :
    eventEnumeration q hq (ChordNonalternation.dartSmoothing (actualEndpoint q hq)
        (actualEndpoint_injective q hq) S i) =
      smoothingDartPermutation q hq S (eventEnumeration q hq i) := by
  simp only [ChordNonalternation.dartSmoothing, Equiv.Perm.mul_apply,
    smoothingDartPermutation_apply]
  rw [swapProduct_intertwines, successor_intertwines]


/-- The component map has the prescribed increasing-event representative. -/
noncomputable def incomingComponentEquiv (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) :
    Component (ChordNonalternation.smoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S) ≃
      Component (smoothingIncomingPermutation q hq S) :=
  componentEquivOfIntertwining (eventEnumeration q hq)
    (ChordNonalternation.smoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S)
    (smoothingIncomingPermutation q hq S) (incoming_intertwines q hq S)

@[simp] theorem incomingComponentEquiv_componentOf (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (i : Fin (Fintype.card (PolygonEvent q))) :
    incomingComponentEquiv q hq S
      (componentOf (ChordNonalternation.smoothing (actualEndpoint q hq)
        (actualEndpoint_injective q hq) S) i) =
      componentOf (smoothingIncomingPermutation q hq S) (eventEnumeration q hq i) := rfl

/-- The dart component map uses the same actual event enumeration on representatives. -/
noncomputable def dartComponentEquiv (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) :
    Component (ChordNonalternation.dartSmoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S) ≃
      Component (smoothingDartPermutation q hq S) :=
  componentEquivOfIntertwining (eventEnumeration q hq)
    (ChordNonalternation.dartSmoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S)
    (smoothingDartPermutation q hq S) (dart_intertwines q hq S)

@[simp] theorem dartComponentEquiv_componentOf (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (i : Fin (Fintype.card (PolygonEvent q))) :
    dartComponentEquiv q hq S
      (componentOf (ChordNonalternation.dartSmoothing (actualEndpoint q hq)
        (actualEndpoint_injective q hq) S) i) =
      componentOf (smoothingDartPermutation q hq S) (eventEnumeration q hq i) := rfl

@[simp] theorem incomingComponentEquiv_symm_componentOf (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (x : PolygonEvent q) :
    (incomingComponentEquiv q hq S).symm
      (componentOf (smoothingIncomingPermutation q hq S) x) =
      componentOf (ChordNonalternation.smoothing (actualEndpoint q hq)
        (actualEndpoint_injective q hq) S) ((eventEnumeration q hq).symm x) := rfl

@[simp] theorem dartComponentEquiv_symm_componentOf (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (x : PolygonEvent q) :
    (dartComponentEquiv q hq S).symm
      (componentOf (smoothingDartPermutation q hq S) x) =
      componentOf (ChordNonalternation.dartSmoothing (actualEndpoint q hq)
        (actualEndpoint_injective q hq) S) ((eventEnumeration q hq).symm x) := rfl

private theorem eventCard_neZero (q : Fin n → PlanarPoint K) (hn : 0 < n) :
    NeZero (Fintype.card (PolygonEvent q)) := by
  refine ⟨? _⟩
  have hpos : 0 < Fintype.card (PolygonEvent q) :=
    Fintype.card_pos_iff.mpr ⟨Sum.inl ⟨0, hn⟩⟩
  omega

theorem incoming_sameCycle_iff (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (x y : PolygonEvent q) :
    (ChordNonalternation.smoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S).SameCycle
        ((eventEnumeration q hq).symm x) ((eventEnumeration q hq).symm y) ↔
      (smoothingIncomingPermutation q hq S).SameCycle x y := by
  simpa using (sameCycle_iff_of_intertwining (eventEnumeration q hq)
    (ChordNonalternation.smoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S)
    (smoothingIncomingPermutation q hq S) (incoming_intertwines q hq S)
    ((eventEnumeration q hq).symm x) ((eventEnumeration q hq).symm y))

theorem dart_sameCycle_iff (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (x y : PolygonEvent q) :
    (ChordNonalternation.dartSmoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S).SameCycle
        ((eventEnumeration q hq).symm x) ((eventEnumeration q hq).symm y) ↔
      (smoothingDartPermutation q hq S).SameCycle x y := by
  simpa using (sameCycle_iff_of_intertwining (eventEnumeration q hq)
    (ChordNonalternation.dartSmoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S)
    (smoothingDartPermutation q hq S) (dart_intertwines q hq S)
    ((eventEnumeration q hq).symm x) ((eventEnumeration q hq).symm y))

theorem incoming_componentCount_eq (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) :
    componentCount (ChordNonalternation.smoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S) =
      componentCount (smoothingIncomingPermutation q hq S) :=
  componentCount_eq_of_intertwining (eventEnumeration q hq)
    (ChordNonalternation.smoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S)
    (smoothingIncomingPermutation q hq S) (incoming_intertwines q hq S)

theorem dart_componentCount_eq (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) :
    componentCount (ChordNonalternation.dartSmoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S) =
      componentCount (smoothingDartPermutation q hq S) :=
  componentCount_eq_of_intertwining (eventEnumeration q hq)
    (ChordNonalternation.dartSmoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S)
    (smoothingDartPermutation q hq S) (dart_intertwines q hq S)

/-- On the actual event circle, incoming orbit count is maximal exactly for actual-order nonalternation. -/
theorem polygonNonalternating_iff_incoming_count (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (hn : 3 ≤ n) (S : Finset (PolygonCrossing q)) :
    polygonNonalternating q hq S ↔
      componentCount (smoothingIncomingPermutation q hq S) = S.card + 1 := by
  letI := eventCard_neZero q (by omega)
  rw [← componentCount_eq_of_intertwining (eventEnumeration q hq)
    (ChordNonalternation.smoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S)
    (smoothingIncomingPermutation q hq S) (incoming_intertwines q hq S)]
  exact (polygonNonalternating_iff_abstract q hq S).trans
    (ChordNonalternation.nonalternating_iff_componentCount
      (actualEndpoint q hq) (actualEndpoint_injective q hq) S)

/-- The same actual-order criterion counts the actual outgoing-dart components. -/
theorem polygonNonalternating_iff_dart_count (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (hn : 3 ≤ n) (S : Finset (PolygonCrossing q)) :
    polygonNonalternating q hq S ↔
      componentCount (smoothingDartPermutation q hq S) = S.card + 1 := by
  letI := eventCard_neZero q (by omega)
  rw [← componentCount_eq_of_intertwining (eventEnumeration q hq)
    (ChordNonalternation.dartSmoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S)
    (smoothingDartPermutation q hq S) (dart_intertwines q hq S)]
  exact (polygonNonalternating_iff_abstract q hq S).trans
    (ChordNonalternation.nonalternating_iff_dart_componentCount
      (actualEndpoint q hq) (actualEndpoint_injective q hq) S)

/-- Actual event-order nonalternation is inherited by every selected subset. -/
theorem polygonNonalternating_mono (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) {S T : Finset (PolygonCrossing q)}
    (hT : polygonNonalternating q hq T) (hST : S ⊆ T) : polygonNonalternating q hq S := by
  rw [polygonNonalternating_iff_abstract] at hT ⊢
  exact ChordNonalternation.Nonalternating.mono (actualEndpoint q hq) hT hST

/-- Each allowed actual incoming insertion increases the full orbit count by one. -/
theorem incoming_componentCount_insert (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (hn : 3 ≤ n)
    (S : Finset (PolygonCrossing q)) (c : PolygonCrossing q) (hc : c ∉ S)
    (hS : polygonNonalternating q hq (insert c S)) :
    componentCount (smoothingIncomingPermutation q hq (insert c S)) =
      componentCount (smoothingIncomingPermutation q hq S) + 1 := by
  have hbase : polygonNonalternating q hq S :=
    polygonNonalternating_mono q hq hS (Finset.subset_insert c S)
  rw [(polygonNonalternating_iff_incoming_count q hq hn (insert c S)).mp hS,
    (polygonNonalternating_iff_incoming_count q hq hn S).mp hbase,
    Finset.card_insert_of_not_mem hc]

/-- Each allowed actual outgoing-dart insertion increases the full orbit count by one. -/
theorem dart_componentCount_insert (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (hn : 3 ≤ n)
    (S : Finset (PolygonCrossing q)) (c : PolygonCrossing q) (hc : c ∉ S)
    (hS : polygonNonalternating q hq (insert c S)) :
    componentCount (smoothingDartPermutation q hq (insert c S)) =
      componentCount (smoothingDartPermutation q hq S) + 1 := by
  have hbase : polygonNonalternating q hq S :=
    polygonNonalternating_mono q hq hS (Finset.subset_insert c S)
  rw [(polygonNonalternating_iff_dart_count q hq hn (insert c S)).mp hS,
    (polygonNonalternating_iff_dart_count q hq hn S).mp hbase,
    Finset.card_insert_of_not_mem hc]

/-- An allowed actual incoming insertion sees its two actual visits in one old component. -/
theorem incoming_sameCycle_before_insert (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (c : PolygonCrossing q) (hc : c ∉ S)
    (hS : polygonNonalternating q hq (insert c S)) :
    (smoothingIncomingPermutation q hq S).SameCycle (Sum.inr (c, false)) (Sum.inr (c, true)) := by
  have habstract := (polygonNonalternating_iff_abstract q hq (insert c S)).1 hS
  have hcoord := ChordNonalternation.sameCycle_before_insert (actualEndpoint q hq)
    (actualEndpoint_injective q hq) S c hc habstract
  have hactual := (sameCycle_iff_of_intertwining (eventEnumeration q hq)
    (ChordNonalternation.smoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S)
    (smoothingIncomingPermutation q hq S) (incoming_intertwines q hq S)
    (actualEndpoint q hq (c, false)) (actualEndpoint q hq (c, true))).mp hcoord
  simpa only [eventEnumeration_actualEndpoint] using hactual

/-- An allowed actual outgoing-dart insertion has its visits in one old component. -/
theorem dart_sameCycle_before_insert (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (c : PolygonCrossing q) (hc : c ∉ S)
    (hS : polygonNonalternating q hq (insert c S)) :
    (smoothingDartPermutation q hq S).SameCycle (Sum.inr (c, false)) (Sum.inr (c, true)) := by
  have habstract := (polygonNonalternating_iff_abstract q hq (insert c S)).1 hS
  have hcoord := ChordNonalternation.dart_sameCycle_before_insert (actualEndpoint q hq)
    (actualEndpoint_injective q hq) S c hc habstract
  have hactual := (sameCycle_iff_of_intertwining (eventEnumeration q hq)
    (ChordNonalternation.dartSmoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S)
    (smoothingDartPermutation q hq S) (dart_intertwines q hq S)
    (actualEndpoint q hq (c, false)) (actualEndpoint q hq (c, true))).mp hcoord
  simpa only [eventEnumeration_actualEndpoint] using hactual

/-- Adding selected nonalternating crossings refines the actual incoming orbit partition. -/
theorem incoming_refines_of_subset (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S T : Finset (PolygonCrossing q))
    (hST : S ⊆ T) (hT : polygonNonalternating q hq T)
    {x y : PolygonEvent q}
    (hxy : (smoothingIncomingPermutation q hq T).SameCycle x y) :
    (smoothingIncomingPermutation q hq S).SameCycle x y := by
  have habs := (polygonNonalternating_iff_abstract q hq T).1 hT
  have hcoord := (sameCycle_iff_of_intertwining (eventEnumeration q hq)
    (ChordNonalternation.smoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) T)
    (smoothingIncomingPermutation q hq T) (incoming_intertwines q hq T)
    ((eventEnumeration q hq).symm x) ((eventEnumeration q hq).symm y)).mpr
      (by simpa using hxy)
  have href := ChordNonalternation.smoothing_refines_of_subset
    (actualEndpoint q hq) (actualEndpoint_injective q hq) S T hST habs hcoord
  have hactual := (sameCycle_iff_of_intertwining (eventEnumeration q hq)
    (ChordNonalternation.smoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S)
    (smoothingIncomingPermutation q hq S) (incoming_intertwines q hq S)
    ((eventEnumeration q hq).symm x) ((eventEnumeration q hq).symm y)).mp href
  simpa using hactual

/-- Adding selected nonalternating crossings refines the actual outgoing-dart orbit partition. -/
theorem dart_refines_of_subset (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S T : Finset (PolygonCrossing q))
    (hST : S ⊆ T) (hT : polygonNonalternating q hq T)
    {x y : PolygonEvent q}
    (hxy : (smoothingDartPermutation q hq T).SameCycle x y) :
    (smoothingDartPermutation q hq S).SameCycle x y := by
  have habs := (polygonNonalternating_iff_abstract q hq T).1 hT
  have hcoord := (sameCycle_iff_of_intertwining (eventEnumeration q hq)
    (ChordNonalternation.dartSmoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) T)
    (smoothingDartPermutation q hq T) (dart_intertwines q hq T)
    ((eventEnumeration q hq).symm x) ((eventEnumeration q hq).symm y)).mpr
      (by simpa using hxy)
  have href := ChordNonalternation.dartSmoothing_refines_of_subset
    (actualEndpoint q hq) (actualEndpoint_injective q hq) S T hST habs hcoord
  have hactual := (sameCycle_iff_of_intertwining (eventEnumeration q hq)
    (ChordNonalternation.dartSmoothing (actualEndpoint q hq)
      (actualEndpoint_injective q hq) S)
    (smoothingDartPermutation q hq S) (dart_intertwines q hq S)
    ((eventEnumeration q hq).symm x) ((eventEnumeration q hq).symm y)).mp href
  simpa using hactual

end DirectGLSSW.PolygonNonalternation
