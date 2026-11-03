import DirectGLSSW.CapCriticalGlobalJump
import DirectGLSSW.CapChamberConstancy
import DirectGLSSW.FiniteJumpTelescope

import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DirectGLSSW.CapGlobalTelescope

open DirectGLSSW
open DirectGLSSW.CapCrossingEvent
open DirectGLSSW.CapCriticalTimes
open DirectGLSSW.CapCriticalEventGeometry
open DirectGLSSW.CapGlobalEventJump
open DirectGLSSW.CapCriticalGlobalJump
open DirectGLSSW.CapChamberConstancy
open DirectGLSSW.GlobalCapEntry
open DirectGLSSW.GlobalCapIntertwining
open DirectGLSSW.ShortEdgeSignStability

noncomputable def criticalPairContribution
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (t : ℝ) (p : ℕ × ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  if hp : p ∈ criticalPairs q n then
    eventContribution (horizontalMove q t) n p.1 p.2
      (by have h := hp; simp [criticalPairs] at h; omega)
      (by have h := hp; simp [criticalPairs] at h; omega)
      (by have h := hp; simp [criticalPairs] at h; omega)
      ((q p.1).2 / (q p.2).2)
  else 0

noncomputable def contributionAt
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℚ :=
  ∑ p ∈ (criticalPairs q n).filter
    (fun p => criticalRoot q p = t), criticalPairContribution q n t p

theorem contributionAt_eq_eventContribution
    (q : ℕ → PlanarPoint ℝ) (n k j : ℕ)
    (hroots : ∀ p r, p ∈ criticalPairs q n → r ∈ criticalPairs q n →
      criticalRoot q p = criticalRoot q r → p = r)
    (hk : 0 < k) (hkj : k < j) (hjn : j ≤ n)
    (hs : planarDet (q k - q j) (1, 0) ≠ 0) :
    contributionAt q n (criticalRoot q (k, j)) =
      eventContribution (horizontalMove q (criticalRoot q (k, j)))
        n k j hk hkj hjn ((q k).2 / (q j).2) := by
  classical
  have hpair : (k, j) ∈ criticalPairs q n := by
    simp [criticalPairs, hk, hkj, hjn, hs,
      show k < n + 1 by omega, show j < n + 1 by omega]
  have hfilter :
      (criticalPairs q n).filter (fun p => criticalRoot q p = criticalRoot q (k, j)) =
        {(k, j)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hroot⟩
      have hEq := hroots p (k, j) hp hpair hroot
      simpa [hEq]
    · intro hEq
      subst p
      exact ⟨hpair, rfl⟩
  unfold contributionAt
  rw [hfilter]
  simp [criticalPairContribution, hpair]

theorem lineCapJ_criticalTimes_telescope
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) {x y : ℝ} (hxy : x < y)
    (hzero : (q 0).2 = 0)
    (hoff : ∀ a, 0 < a → a ≤ n → (q a).2 ≠ 0)
    (hdistinct : ∀ a b, 0 < a → a ≤ n → 0 < b → b ≤ n → a ≠ b → q a ≠ q b)
    (hpositive : ∀ i a b, 0 < i → i < a → a < b → b ≤ n → polygonHDet q i a b ≠ 0)
    (hroots : ∀ p r, p ∈ criticalPairs q n → r ∈ criticalPairs q n →
      criticalRoot q p = criticalRoot q r → p = r)
    (hx : x ∉ criticalTimes q n)
    (hy : y ∉ criticalTimes q n)
    (hlocalCaps : ∀ t, t ∈ criticalTimes q n →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
        ∀ a b : Fin n, a.val < b.val →
          CyclicGeneric (lineCapCore (horizontalMove q (t + s)) a b)) :
    lineCapJ (horizontalMove q y) n - lineCapJ (horizontalMove q x) n =
      ∑ t ∈ (criticalTimes q n).filter
        (fun t => x < t ∧ t < y), contributionAt q n t := by
  classical
  let J : ℝ → Matrix (Fin n) (Fin n) ℚ := fun s => lineCapJ (horizontalMove q s) n
  let D : ℝ → Matrix (Fin n) (Fin n) ℚ := contributionAt q n
  have hconst : ∀ a b : ℝ, a ≤ b →
      (∀ t, t ∈ criticalTimes q n → t < a ∨ b < t) → J a = J b := by
    intro a b hab hout
    by_cases habEq : a = b
    · subst b
      rfl
    · have hablt : a < b := lt_of_le_of_ne hab habEq
      have hchamber : ∀ s, s ∈ Set.Icc a b → ∀ i k j,
          i < k → k < j → j ≤ n → polygonHDet (horizontalMove q s) i k j ≠ 0 := by
        intro s hs i k j hik hkj hjn
        have hsnot : s ∉ criticalTimes q n := by
          intro hsT
          rcases hout s hsT with hsleft | hsright
          · exact (not_lt_of_ge hs.1) hsleft
          · exact (not_lt_of_ge hs.2) hsright
        have hcore : CoreHGeneric (horizontalMove q s) n :=
          (horizontalMove_coreHGeneric_iff_not_critical q n hzero hoff
            hdistinct hpositive s).2 hsnot
        exact hcore i k j hik hkj hjn
      have hconstant := lineCapFCJ_constant_on_horizontal_chamber q n hablt hchamber
      exact hconstant.2.2
  have hjump : ∀ t, t ∈ criticalTimes q n →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
        J (t + ε) - J (t - ε) = D t := by
    intro t ht
    obtain ⟨k, j, hk, hkj, hjn, hs, htime⟩ :=
      (mem_criticalTimes_iff q n t).mp ht
    have htimeRoot : t = criticalRoot q (k, j) := by
      simpa [criticalRoot] using htime
    have hpairJump := criticalPair_global_event_jump hRI q n k j
      hzero hoff hdistinct hpositive hroots hk hkj hjn hs
    obtain ⟨ρjump, hρjump, hjumpConditional⟩ := hpairJump
    obtain ⟨δ, hδ, hcapsLocal⟩ := hlocalCaps t ht
    have hD : D t = eventContribution (horizontalMove q (criticalRoot q (k, j)))
        n k j hk hkj hjn ((q k).2 / (q j).2) := by
      simpa [D, htimeRoot] using
        contributionAt_eq_eventContribution q n k j hroots hk hkj hjn hs
    refine ⟨min ρjump δ, lt_min hρjump hδ, ?_⟩
    intro ε hε hεmin
    have hεjump : ε < ρjump := lt_of_lt_of_le hεmin (min_le_left _ _)
    have hεδ : ε < δ := lt_of_lt_of_le hεmin (min_le_right _ _)
    have hcaps : ∀ a b : Fin n, a.val < b.val →
        CyclicGeneric (lineCapCore
          (horizontalMove (horizontalMove q (criticalRoot q (k, j))) (-ε)) a b) := by
      intro a b hab
      have hcaps' := hcapsLocal (-ε)
        (by rw [abs_neg, abs_of_pos hε]; exact hε)
        (by rw [abs_neg, abs_of_pos hε]; exact hεδ) a b hab
      rw [htimeRoot] at hcaps'
      rw [horizontalMove_add q (criticalRoot q (k, j)) (-ε)]
      simpa [sub_eq_add_neg] using hcaps'
    have hjump' := hjumpConditional ε hε hεjump hcaps
    have hglobal : J (t + ε) - J (t - ε) =
        eventContribution (horizontalMove q (criticalRoot q (k, j)))
          n k j hk hkj hjn ((q k).2 / (q j).2) := by
      simpa [J, htimeRoot] using hjump'
    rw [hD]
    exact hglobal
  have htel := finiteJumpTelescope J D (criticalTimes q n) hconst hjump hxy hx hy
  simpa [J, D] using htel






end DirectGLSSW.CapGlobalTelescope
