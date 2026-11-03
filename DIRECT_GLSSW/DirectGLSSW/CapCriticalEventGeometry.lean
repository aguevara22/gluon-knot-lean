import DirectGLSSW.CapCriticalTimes
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DirectGLSSW.CapCriticalEventGeometry

open DirectGLSSW
open DirectGLSSW.CapCrossingEvent
open DirectGLSSW.EndpointEventGeometry
open DirectGLSSW.CapCriticalTimes

noncomputable def criticalRoot (q : ℕ → PlanarPoint ℝ) (p : ℕ × ℕ) : ℝ :=
  -polygonHDet q 0 p.1 p.2 / planarDet (q p.1 - q p.2) (1, 0)

theorem critical_event_geometry
    (q : ℕ → PlanarPoint ℝ) (n k j : ℕ)
    (hzero : (q 0).2 = 0)
    (hoff : ∀ a, 0 < a → a ≤ n → (q a).2 ≠ 0)
    (hdistinct : ∀ a b, 0 < a → a ≤ n → 0 < b → b ≤ n → a ≠ b → q a ≠ q b)
    (hpositive : ∀ i a b, 0 < i → i < a → a < b → b ≤ n → polygonHDet q i a b ≠ 0)
    (hroots : ∀ p r, p ∈ criticalPairs q n → r ∈ criticalPairs q n →
      criticalRoot q p = criticalRoot q r → p = r)
    (hk : 0 < k) (hkj : k < j) (hjn : j ≤ n)
    (hs : planarDet (q k - q j) (1, 0) ≠ 0) :
    let t := criticalRoot q (k, j)
    let q' := horizontalMove q t
    let τ := (q k).2 / (q j).2
    τ ≠ 0 ∧ τ ≠ 1 ∧ q' k = q' 0 + τ • (q' j - q' 0) ∧
      ∀ i a b, i < a → a < b → b ≤ n → (i, a, b) ≠ (0, k, j) →
        polygonHDet q' i a b ≠ 0 := by
  classical
  let t : ℝ := criticalRoot q (k, j)
  let q' : ℕ → PlanarPoint ℝ := horizontalMove q t
  let τ : ℝ := (q k).2 / (q j).2
  have hj : 0 < j := by omega
  have hjne : j ≠ 0 := by omega
  have hkne : k ≠ 0 := by omega
  have hdenj : (q j).2 ≠ 0 := hoff j hj hjn
  have hdenk : (q k).2 ≠ 0 := hoff k hk (by omega)
  have hmove : polygonHDet q' 0 k j =
      polygonHDet q 0 k j + t * planarDet (q k - q j) (1, 0) := by
    dsimp [q', t, horizontalMove]
    exact moveEndpoint_farDet q (1, 0) hk hkj _
  have hevent : polygonHDet q' 0 k j = 0 := by
    rw [hmove]
    dsimp [t, criticalRoot]
    field_simp [hs]
  have htau0 : τ ≠ 0 := by
    dsimp [τ]
    exact div_ne_zero hdenk hdenj
  have hyne : (q k).2 ≠ (q j).2 := by
    intro heq
    apply hs
    simp [planarDet, heq]
  have htau1 : τ ≠ 1 := by
    intro h
    have heq : (q k).2 = (q j).2 := by
      dsimp [τ] at h
      field_simp [hdenj] at h
      linarith
    exact hyne heq
  have htriple : q' k = q' 0 + τ • (q' j - q' 0) := by
    apply Prod.ext
    · dsimp [q', τ, horizontalMove, EndpointEventGeometry.moveEndpoint]
      simp only [if_pos rfl, if_neg hkne, if_neg hjne]
      simp only [PlanarPoint] at *
      have hz := hevent
      simp [polygonHDet, planarDet, q', horizontalMove,
        EndpointEventGeometry.moveEndpoint, hzero, ne_of_gt hk, ne_of_gt hj] at hz
      field_simp [hdenj] at hz ⊢
      nlinarith
    · dsimp [q', τ, horizontalMove, EndpointEventGeometry.moveEndpoint]
      simp only [if_pos rfl, if_neg hkne, if_neg hjne]
      rw [hzero]
      field_simp [hdenj]
  have hpair : (k, j) ∈ criticalPairs q n := by
    simp [criticalPairs, hk, hkj, hjn, hs, show k < n + 1 by omega,
      show j < n + 1 by omega]
  refine ⟨htau0, htau1, htriple, ?_⟩
  intro i a b hi hia hab hne hzeroTrip
  by_cases hia0 : i = 0
  · subst i
    have hzeroTrip' : polygonHDet q' 0 a b = 0 := by simpa [q', t] using hzeroTrip
    by_cases hsab : planarDet (q a - q b) (1, 0) = 0
    · have hbase := zeroSlope_base_ne q n a b hzero hoff hdistinct
        (by omega) hia hab hsab
      have hmoveab : polygonHDet q' 0 a b =
          polygonHDet q 0 a b + t * planarDet (q a - q b) (1, 0) := by
        dsimp [q', horizontalMove]
        exact moveEndpoint_farDet q (1, 0) (by omega) (by omega) t
      rw [hmoveab, hsab, mul_zero, add_zero] at hzeroTrip'
      exact hbase hzeroTrip'
    · have hmoveab : polygonHDet q' 0 a b =
          polygonHDet q 0 a b + t * planarDet (q a - q b) (1, 0) := by
        dsimp [q', horizontalMove]
        exact moveEndpoint_farDet q (1, 0) (by omega) (by omega) t
      have hlinear : polygonHDet q 0 a b +
          t * planarDet (q a - q b) (1, 0) = 0 := by
        rw [← hmoveab]
        exact hzeroTrip'
      have hrootab : t = criticalRoot q (a, b) := by
        dsimp [criticalRoot]
        dsimp [t, criticalRoot] at *
        field_simp [hsab] at hlinear ⊢
        linarith
      have habmem : (a, b) ∈ criticalPairs q n := by
        simp [criticalPairs, (by omega : 0 < a), (by omega : a < b), (by omega : b ≤ n), hsab,
          show a < n + 1 by omega, show b < n + 1 by omega]
      have hp := hroots (a, b) (k, j) habmem hpair (by simpa [t] using hrootab.symm)
      have hEq : (0, a, b) = (0, k, j) := by simpa [hp]
      exact hne hEq
  · have hipos : 0 < i := Nat.pos_of_ne_zero hia0
    have hpos := hpositive i a b hipos hi hia hab
    have hiq : moveEndpoint q (1, 0) (criticalRoot q (k, j)) i = q i := by
      change (if i = 0 then q 0 + criticalRoot q (k, j) • (1, 0) else q i) = q i
      rw [if_neg (ne_of_gt hipos)]
    have haq : moveEndpoint q (1, 0) (criticalRoot q (k, j)) a = q a := by
      change (if a = 0 then q 0 + criticalRoot q (k, j) • (1, 0) else q a) = q a
      rw [if_neg (by omega : a ≠ 0)]
    have hbq : moveEndpoint q (1, 0) (criticalRoot q (k, j)) b = q b := by
      change (if b = 0 then q 0 + criticalRoot q (k, j) • (1, 0) else q b) = q b
      rw [if_neg (by omega : b ≠ 0)]
    change polygonHDet (moveEndpoint q (1, 0) (criticalRoot q (k, j))) i a b = 0 at hzeroTrip
    simp only [polygonHDet] at hzeroTrip
    rw [hiq, haq, hbq] at hzeroTrip
    change polygonHDet q i a b = 0 at hzeroTrip
    exact hpos hzeroTrip




end DirectGLSSW.CapCriticalEventGeometry
