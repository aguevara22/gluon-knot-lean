import DirectGLSSW.CapCrossingEvent
import DirectGLSSW.EndpointEventGeometry
import DirectGLSSW.ShortEdgeSignStability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DirectGLSSW.CapCriticalTimes

open DirectGLSSW
open DirectGLSSW.CapCrossingEvent
open DirectGLSSW.ShortEdgeSignStability
open DirectGLSSW.EndpointEventGeometry

noncomputable def criticalPairs (q : ℕ → PlanarPoint ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter fun p =>
    0 < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ n ∧
      planarDet (q p.1 - q p.2) (1, 0) ≠ 0

noncomputable def criticalTimes (q : ℕ → PlanarPoint ℝ) (n : ℕ) : Finset ℝ :=
  (criticalPairs q n).image fun p =>
    -polygonHDet q 0 p.1 p.2 / planarDet (q p.1 - q p.2) (1, 0)

theorem mem_criticalTimes_iff (q : ℕ → PlanarPoint ℝ) (n : ℕ) (t : ℝ) :
    t ∈ criticalTimes q n ↔
      ∃ k j, 0 < k ∧ k < j ∧ j ≤ n ∧
        planarDet (q k - q j) (1, 0) ≠ 0 ∧
        t = -polygonHDet q 0 k j / planarDet (q k - q j) (1, 0) := by
  classical
  simp only [criticalTimes, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, ht⟩
    rcases p with ⟨k, j⟩
    have hp' : 0 < k ∧ k < j ∧ j ≤ n ∧
        planarDet (q k - q j) (1, 0) ≠ 0 := by
      have hps := hp
      simp only [criticalPairs, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hps
      exact ⟨hps.2.1, hps.2.2.1, hps.2.2.2.1, hps.2.2.2.2⟩
    exact ⟨k, j, hp'.1, hp'.2.1, hp'.2.2.1, hp'.2.2.2, ht.symm⟩
  · rintro ⟨k, j, hk, hkj, hjn, hs, ht⟩
    have hmem : (k, j) ∈ criticalPairs q n := by
      simp [criticalPairs, show k < n + 1 by omega,
        show j < n + 1 by omega, hk, hkj, hjn, hs]
    exact ⟨(k, j), hmem, ht.symm⟩

theorem zeroSlope_base_ne
    (q : ℕ → PlanarPoint ℝ) (n k j : ℕ)
    (hzero : (q 0).2 = 0)
    (hoff : ∀ a, 0 < a → a ≤ n → (q a).2 ≠ 0)
    (hdistinct : ∀ a b, 0 < a → a ≤ n → 0 < b → b ≤ n → a ≠ b → q a ≠ q b)
    (hk : 0 < k) (hkj : k < j) (hjn : j ≤ n)
    (hs : planarDet (q k - q j) (1, 0) = 0) :
    polygonHDet q 0 k j ≠ 0 := by
  have hy : (q k).2 = (q j).2 := by
    simp [planarDet] at hs
    linarith
  have hx : (q k).1 ≠ (q j).1 := by
    intro heq
    have hq := hdistinct k j hk (by omega) (by omega) hjn (by omega)
    apply hq
    exact Prod.ext heq hy
  have hbase : polygonHDet q 0 k j = -((q k).1 - (q j).1) * (q j).2 := by
    simp [polygonHDet, planarDet, hzero, hy]
    ring
  rw [hbase]
  exact mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr hx)) (hoff j (by omega) hjn)

theorem horizontalMove_coreHGeneric_iff_not_critical
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (hzero : (q 0).2 = 0)
    (hoff : ∀ k, 0 < k → k ≤ n → (q k).2 ≠ 0)
    (hdistinct : ∀ k j, 0 < k → k ≤ n → 0 < j → j ≤ n → k ≠ j → q k ≠ q j)
    (hpositive : ∀ i k j, 0 < i → i < k → k < j → j ≤ n →
      polygonHDet q i k j ≠ 0)
    (t : ℝ) :
    CoreHGeneric (horizontalMove q t) n ↔ t ∉ criticalTimes q n := by
  constructor
  · intro hgeneric ht
    obtain ⟨k, j, hk, hkj, hjn, hs, hroot⟩ :=
      (mem_criticalTimes_iff q n t).mp ht
    have hdet := hgeneric 0 k j (by omega) hkj hjn
    have hmove : polygonHDet (horizontalMove q t) 0 k j =
        polygonHDet q 0 k j + t * planarDet (q k - q j) (1, 0) := by
      simpa [horizontalMove] using moveEndpoint_farDet q (1, 0) hk hkj t
    have hz : polygonHDet (horizontalMove q t) 0 k j = 0 := by
      rw [hmove, hroot]
      field_simp [hs]
    exact hdet hz
  · intro hnot i k j hik hkj hjn
    by_cases hi : i = 0
    · subst i
      let s := planarDet (q k - q j) (1, 0)
      by_cases hs : s = 0
      · have hbase := zeroSlope_base_ne q n k j hzero hoff hdistinct
          (by omega) hkj hjn hs
        have hmove : polygonHDet (horizontalMove q t) 0 k j =
            polygonHDet q 0 k j + t * s := by
          simpa [s, horizontalMove] using moveEndpoint_farDet q (1, 0) (by omega) hkj t
        rw [hmove, hs, mul_zero, add_zero]
        exact hbase
      · have hmove : polygonHDet (horizontalMove q t) 0 k j =
            polygonHDet q 0 k j + t * s := by
          simpa [s, horizontalMove] using moveEndpoint_farDet q (1, 0) (by omega) hkj t
        intro hdet
        have hlin : polygonHDet q 0 k j + t * s = 0 := by
          rw [← hmove]
          exact hdet
        have hroot : t = -polygonHDet q 0 k j / s := by
          field_simp [hs] at hlin ⊢
          linarith
        apply hnot
        apply (mem_criticalTimes_iff q n t).mpr
        exact ⟨k, j, by omega, hkj, hjn, hs, hroot⟩
    · have hi' : 0 < i := Nat.pos_of_ne_zero hi
      have hbase := hpositive i k j hi' hik hkj hjn
      have hmove : polygonHDet (horizontalMove q t) i k j = polygonHDet q i k j := by
        simp [horizontalMove, EndpointEventGeometry.moveEndpoint, polygonHDet,
          ne_of_gt hi', ne_of_gt (by omega : 0 < k), ne_of_gt (by omega : 0 < j)]
      rw [hmove]
      exact hbase







end DirectGLSSW.CapCriticalTimes
