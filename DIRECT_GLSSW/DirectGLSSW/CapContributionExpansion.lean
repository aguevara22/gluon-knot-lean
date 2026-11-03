import DirectGLSSW.OrderedCapEvents
import DirectGLSSW.CapGlobalTelescope
import DirectGLSSW.CapSandwichAlgebra
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW.CapContributionExpansion

open DirectGLSSW
open DirectGLSSW.CapCriticalTimes
open DirectGLSSW.CapCriticalEventGeometry
open DirectGLSSW.CapGlobalTelescope
open DirectGLSSW.CapGlobalEventJump
open DirectGLSSW.OrderedCapEvents
open scoped BigOperators

/-- At an ordered actual event, the telescope contribution has the entrywise
rank-one factorization dictated by its selected edge. -/
theorem contributionAt_event_entry
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (hroots : Set.InjOn (criticalRoot q) ↑(criticalPairs q n))
    (c : EventIndex q n) (i j : Fin n) :
    contributionAt q n (eventTime q n c) i j =
      2 * eventSign q n c * eventColumn q n c i * eventRow q n c j := by
  classical
  let p := eventPair q n c
  let k := p.1
  let l := p.2
  have hb := eventPair_bounds q n c
  have hroot := (eventPair_spec q n c).2
  have hroots' : ∀ a b, a ∈ criticalPairs q n → b ∈ criticalPairs q n →
      criticalRoot q a = criticalRoot q b → a = b := by
    intro a b ha hb' hab
    exact hroots ha hb' hab
  have hkj : k < l := by dsimp [k,l,p]; omega
  have hln : l ≤ n := by dsimp [k,l,p]; omega
  have hcontrib := CapGlobalTelescope.contributionAt_eq_eventContribution
    q n k l hroots' (by dsimp [k,l,p]; exact hb.1) hkj hln
      (by dsimp [k,l,p]; exact hb.2.2.2.2)
  have hratio : (q k).2 / (q l).2 < 0 := by
    simpa [k,l,p] using hb.2.2.2.1
  have hadj : l = k + 1 := by
    simpa [k,l,p] using hb.2.2.1
  have hratio' : (q k).2 / (q (k + 1)).2 < 0 := by
    simpa [hadj] using hratio
  have hpair : eventPair q n c =
      ((eventPair q n c).1, (eventPair q n c).1 + 1) := by
    apply Prod.ext
    · rfl
    · exact hb.2.2.1
  simp only [eventSign, eventColumn, eventRow]
  rw [← hroot]
  rw [hcontrib]
  simp [eventContribution, hratio', hadj, k, l, p]
  rw [← hpair]
  rw [horizontalMove_y]

/-- A critical time that is not selected by an adjacent negative-ratio pair
has zero telescope contribution. -/
theorem contributionAt_zero_outside_actualTimes
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (t : ℝ)
    (_ht : t ∈ criticalTimes q n) (hnot : t ∉ actualTimes q n) :
    contributionAt q n t = 0 := by
  classical
  unfold contributionAt
  apply Finset.sum_eq_zero
  intro p hp
  have hp' : p ∈ criticalPairs q n ∧ criticalRoot q p = t := by
    simpa only [Finset.mem_filter] using hp
  have hvirtual : ¬ (p.2 = p.1 + 1 ∧ (q p.1).2 / (q p.2).2 < 0) := by
    intro hactual
    apply hnot
    change t ∈ (actualPairs q n).image (criticalRoot q)
    exact Finset.mem_image.mpr ⟨p,
      Finset.mem_filter.mpr ⟨hp'.1, hactual⟩, hp'.2⟩
  have hvirtual' : ¬ ((q p.1).2 / (q p.2).2 < 0 ∧ p.2 = p.1 + 1) := by
    intro h
    exact hvirtual ⟨h.2, h.1⟩
  simp [criticalPairContribution, hp'.1, eventContribution, hvirtual']

/-- Reindex the sandwiched telescope contribution from critical times to the
ordered actual events. Nonactual events vanish, and actual jumps factor by
finite rank-one expansion. -/
theorem ordered_actual_sandwich_reindex
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (hroots : Set.InjOn (criticalRoot q) ↑(criticalPairs q n))
    (c d : EventIndex q n) :
    (∑ t ∈ (criticalTimes q n).filter
        (fun t => eventTime q n c < t ∧ t < eventTime q n d),
      ∑ i : Fin n, ∑ j : Fin n,
        eventRow q n c i * (contributionAt q n t) i j * eventColumn q n d j) =
    2 * ∑ e ∈ Finset.univ.filter (fun e => c < e ∧ e < d),
      eventSign q n e * eventPairing q n c e * eventPairing q n e d := by
  classical
  let intervalTime : ℝ → Prop := fun t => eventTime q n c < t ∧ t < eventTime q n d
  let intervalEvent : EventIndex q n → Prop := fun e => c < e ∧ e < d
  let T := (criticalTimes q n).filter intervalTime
  let A := (actualTimes q n).filter intervalTime
  let I := Finset.univ.filter intervalEvent
  let sand : ℝ → ℚ := fun t =>
    ∑ i : Fin n, ∑ j : Fin n,
      eventRow q n c i * (contributionAt q n t) i j * eventColumn q n d j
  have hactualSubset : actualTimes q n ⊆ criticalTimes q n := by
    intro t ht
    change t ∈ (actualPairs q n).image (criticalRoot q) at ht
    rcases Finset.mem_image.mp ht with ⟨p, hp, rfl⟩
    have hfilter : p ∈ (criticalPairs q n).filter
        (fun p => p.2 = p.1 + 1 ∧ (q p.1).2 / (q p.2).2 < 0) := by
      simpa [actualPairs] using hp
    have hpcrit := (Finset.mem_filter.mp hfilter).1
    change criticalRoot q p ∈ (criticalPairs q n).image (criticalRoot q)
    exact Finset.mem_image.mpr ⟨p, hpcrit, rfl⟩
  have hsub : A ⊆ T := by
    intro t ht
    rcases Finset.mem_filter.mp ht with ⟨ha, hinterval⟩
    exact Finset.mem_filter.mpr ⟨hactualSubset ha, hinterval⟩
  have hTsum : (∑ t ∈ T, sand t) = ∑ t ∈ A, sand t := by
    apply (Finset.sum_subset hsub ?_).symm
    intro t htT htNotA
    have htparts := Finset.mem_filter.mp htT
    have hnotActual : t ∉ actualTimes q n := by
      intro htActual
      exact htNotA (Finset.mem_filter.mpr ⟨htActual, htparts.2⟩)
    have hzero := contributionAt_zero_outside_actualTimes q n t htparts.1 hnotActual
    simp [sand, hzero]
  have hsurj : Finset.image (eventTime q n)
      (Finset.univ : Finset (EventIndex q n)) = actualTimes q n := by
    change Finset.image (⇑((actualTimes q n).orderEmbOfFin rfl)) Finset.univ =
      actualTimes q n
    exact Finset.image_orderEmbOfFin_univ (actualTimes q n)
      (k := (actualTimes q n).card) rfl
  have himage : I.image (eventTime q n) = A := by
    ext t
    constructor
    · intro ht
      rcases Finset.mem_image.mp ht with ⟨e, he, rfl⟩
      rcases Finset.mem_filter.mp he with ⟨_, heint⟩
      refine Finset.mem_filter.mpr ⟨eventTime_mem_actualTimes q n e, ?_⟩
      exact ⟨eventTime_strictMono q n heint.1, eventTime_strictMono q n heint.2⟩
    · intro ht
      rcases Finset.mem_filter.mp ht with ⟨htime, htint⟩
      have htimage : t ∈ Finset.image (eventTime q n)
          (Finset.univ : Finset (EventIndex q n)) := by
        rw [hsurj]
        exact htime
      rcases Finset.mem_image.mp htimage with ⟨e, he, htimeEq⟩
      refine Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, htimeEq⟩
      constructor
      · have hlt : eventTime q n c < eventTime q n e := by simpa [htimeEq] using htint.1
        exact (Finset.orderEmbOfFin (actualTimes q n) rfl).lt_iff_lt.mp hlt
      · have hlt : eventTime q n e < eventTime q n d := by simpa [htimeEq] using htint.2
        exact (Finset.orderEmbOfFin (actualTimes q n) rfl).lt_iff_lt.mp hlt
  have hinj : ∀ e ∈ I, ∀ f ∈ I, eventTime q n e = eventTime q n f → e = f := by
    intro e he f hf hEq
    exact (eventTime_strictMono q n).injective hEq
  have hsumImage : (∑ t ∈ A, sand t) = ∑ e ∈ I, sand (eventTime q n e) := by
    rw [← himage]
    exact Finset.sum_image hinj
  have hterm : ∀ e ∈ I,
      sand (eventTime q n e) =
        2 * eventSign q n e * eventPairing q n c e * eventPairing q n e d := by
    intro e he
    unfold sand
    calc
      (∑ i : Fin n, ∑ j : Fin n,
          eventRow q n c i * (contributionAt q n (eventTime q n e)) i j *
            eventColumn q n d j) =
          ∑ i : Fin n, ∑ j : Fin n,
            eventRow q n c i *
              (2 * eventSign q n e * eventColumn q n e i * eventRow q n e j) *
              eventColumn q n d j := by
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro j hj
                rw [contributionAt_event_entry q n hroots e i j]
      _ = (2 * eventSign q n e) *
          (∑ i : Fin n, eventRow q n c i * eventColumn q n e i) *
          (∑ j : Fin n, eventRow q n e j * eventColumn q n d j) := by
            simpa using finiteRankOneSandwich
              (eventRow q n c) (eventRow q n e)
              (eventColumn q n e) (eventColumn q n d)
              (2 * eventSign q n e)
      _ = 2 * eventSign q n e * eventPairing q n c e * eventPairing q n e d := by
            simp [eventPairing]
  calc
    (∑ t ∈ T, sand t) = ∑ t ∈ A, sand t := hTsum
    _ = ∑ e ∈ I, sand (eventTime q n e) := hsumImage
    _ = ∑ e ∈ I,
        2 * eventSign q n e * eventPairing q n c e * eventPairing q n e d := by
          apply Finset.sum_congr rfl
          intro e he
          exact hterm e he
    _ = 2 * ∑ e ∈ I,
        eventSign q n e * eventPairing q n c e * eventPairing q n e d := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          ring





end DirectGLSSW.CapContributionExpansion
