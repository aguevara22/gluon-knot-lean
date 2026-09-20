import SM.EuclideanPlane
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.Order.Round

/-! Towards lem:transport-angle-interval (sm-5-transport.tex:133). Written 2026-09-13 by a Claude Code prover subagent of the pod
executor (workflow prove-transport-lane / prove:angle-interval), checked with `lake env lean` (placeholder-free, standard axioms) and
ported verbatim from work/drafts/AngleInterval.lean (only this header added and #print lines removed). -/

/-! # SM15, `lem:transport-angle-interval` (lifting a semicircle to one real interval)

Source: reference/SM/sm-5-transport.tex, lines 133–148.

A finite real sequence `θ_0, …, θ_N` with `|θ_{i+1} − θ_i| < π` whose unit directions
`(cos θ_i, sin θ_i)` all lie in one closed semicircle has all its entries in one real
interval of length `π`; conversely, entries in one interval of length `π` give unit
directions in one closed semicircle.

Encoding. The sequence is `θ : Fin (N+1) → ℝ`, steps are `|θ i.succ − θ i.castSucc| < π`
for `i : Fin N`. "The unit directions lie in a closed semicircle" is
`InClosedSemicircle θ`: some unit vector `v : Plane` (`planeDot v v = 1`) has
`planeDot v (unitDir (θ i)) ≥ 0` for all `i`, where `unitDir θ = (cos θ, sin θ)`; the
equivalent angular form `∃ α, ∀ i, 0 ≤ cos (θ i − α)` is proved
(`inClosedSemicircle_iff`). "All entries lie in one interval of length `π`" is
`∃ c, ∀ i, c ≤ θ i ∧ θ i ≤ c + π`. -/

open Real

namespace SM

/-- The unit direction of the angle `θ`. -/
noncomputable def unitDir (θ : ℝ) : Plane := (Real.cos θ, Real.sin θ)

/-- The unit directions of the family `θ` lie in one closed semicircle: some unit vector
`v` has nonnegative inner product with every direction `(cos (θ i), sin (θ i))`. -/
def InClosedSemicircle {ι : Type*} (θ : ι → ℝ) : Prop :=
  ∃ v : Plane, planeDot v v = 1 ∧ ∀ i, 0 ≤ planeDot v (unitDir (θ i))

theorem planeDot_unitDir (v : Plane) (θ : ℝ) :
    planeDot v (unitDir θ) = v.1 * Real.cos θ + v.2 * Real.sin θ := rfl

theorem planeDot_unitDir_unitDir (α θ : ℝ) :
    planeDot (unitDir α) (unitDir θ) = Real.cos (θ - α) := by
  rw [planeDot_unitDir, Real.cos_sub]
  simp only [unitDir]
  ring

theorem planeDot_unitDir_self (α : ℝ) : planeDot (unitDir α) (unitDir α) = 1 := by
  rw [planeDot_unitDir_unitDir, sub_self, Real.cos_zero]

/-- Every unit vector of the plane is the unit direction of some angle. -/
theorem exists_unitDir_eq {v : Plane} (hv : planeDot v v = 1) : ∃ α : ℝ, unitDir α = v := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp [planeDot] at hv
  have hn : ‖planeComplex v‖ = 1 := by
    have h1 := euclideanLength_formula v
    rw [euclideanLength] at h1
    rw [h1]
    have h2 : v.1 * v.1 + v.2 * v.2 = 1 := hv
    rw [h2, Real.sqrt_one]
  refine ⟨Complex.arg (planeComplex v), ?_⟩
  have hc := Complex.cos_arg (planeComplex_ne_zero hv0)
  have hs := Complex.sin_arg (planeComplex v)
  rw [hn, div_one] at hc hs
  exact Prod.ext hc hs

/-- The two readings of "in a closed semicircle" agree: a unit vector with nonnegative
inner products against all directions, or an angle `α` with `cos (θ i − α) ≥ 0` for all `i`. -/
theorem inClosedSemicircle_iff {ι : Type*} (θ : ι → ℝ) :
    InClosedSemicircle θ ↔ ∃ α : ℝ, ∀ i, 0 ≤ Real.cos (θ i - α) := by
  constructor
  · rintro ⟨v, hv, h⟩
    obtain ⟨α, rfl⟩ := exists_unitDir_eq hv
    exact ⟨α, fun i => by rw [← planeDot_unitDir_unitDir]; exact h i⟩
  · rintro ⟨α, h⟩
    exact ⟨unitDir α, planeDot_unitDir_self α,
      fun i => by rw [planeDot_unitDir_unitDir]; exact h i⟩

/-- The inverse image of the closed right half-plane under `x ↦ (cos x, sin x)` is the
union of the intervals `[−π/2 + 2πk, π/2 + 2πk]`. -/
theorem exists_int_of_cos_nonneg {x : ℝ} (hx : 0 ≤ Real.cos x) :
    ∃ k : ℤ, -(π / 2) + k * (2 * π) ≤ x ∧ x ≤ π / 2 + k * (2 * π) := by
  set k : ℤ := round (x / (2 * π)) with hk
  have h2π : 0 < 2 * π := by positivity
  have hr : |x / (2 * π) - k| ≤ 1 / 2 := abs_sub_round _
  have hy : |x - k * (2 * π)| ≤ π := by
    have h1 : x - k * (2 * π) = (x / (2 * π) - k) * (2 * π) := by
      field_simp
    rw [h1, abs_mul, abs_of_pos h2π]
    calc |x / (2 * π) - k| * (2 * π) ≤ 1 / 2 * (2 * π) := by gcongr
      _ = π := by ring
  have hcos : 0 ≤ Real.cos (x - k * (2 * π)) := by
    rw [Real.cos_sub_int_mul_two_pi]; exact hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  refine ⟨k, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have h1 : π / 2 < -(x - k * (2 * π)) := by linarith
    have h2 : -(x - k * (2 * π)) < π + π / 2 := by linarith [Real.pi_pos]
    have h3 := Real.cos_neg_of_pi_div_two_lt_of_lt h1 h2
    rw [Real.cos_neg] at h3
    linarith
  · by_contra hlt
    push Not at hlt
    have h1 : π / 2 < x - k * (2 * π) := by linarith
    have h2 : x - k * (2 * π) < π + π / 2 := by linarith [Real.pi_pos]
    have h3 := Real.cos_neg_of_pi_div_two_lt_of_lt h1 h2
    linarith

/-- Distinct intervals `[−π/2 + 2πk, π/2 + 2πk]` are separated by gaps of length `π`,
so a step of absolute size `< π` cannot move from one to another. -/
theorem int_eq_of_step_lt_pi {x y : ℝ} {k l : ℤ}
    (hx : -(π / 2) + k * (2 * π) ≤ x ∧ x ≤ π / 2 + k * (2 * π))
    (hy : -(π / 2) + l * (2 * π) ≤ y ∧ y ≤ π / 2 + l * (2 * π))
    (h : |y - x| < π) : l = k := by
  have h2π : 0 < 2 * π := by positivity
  obtain ⟨hlo, hhi⟩ := abs_lt.mp h
  rcases lt_trichotomy l k with hlt | heq | hgt
  · exfalso
    have h1 : (l : ℝ) + 1 ≤ k := by exact_mod_cast Int.add_one_le_iff.mpr hlt
    have h2 := mul_le_mul_of_nonneg_right h1 h2π.le
    linarith [hx.1, hy.2]
  · exact heq
  · exfalso
    have h1 : (k : ℝ) + 1 ≤ l := by exact_mod_cast Int.add_one_le_iff.mpr hgt
    have h2 := mul_le_mul_of_nonneg_right h1 h2π.le
    linarith [hx.2, hy.1]

/-- SM15 `lem:transport-angle-interval`, forward direction, angular form of the
semicircle hypothesis: if `|θ_{i+1} − θ_i| < π` and some `α` has `cos (θ_i − α) ≥ 0`
for all `i`, then all `θ_i` lie in one interval `[c, c + π]`. -/
theorem transport_angle_interval_of_cos {N : ℕ} (θ : Fin (N + 1) → ℝ)
    (hstep : ∀ i : Fin N, |θ i.succ - θ i.castSucc| < π)
    (hsemi : ∃ α : ℝ, ∀ i, 0 ≤ Real.cos (θ i - α)) :
    ∃ c : ℝ, ∀ i, c ≤ θ i ∧ θ i ≤ c + π := by
  obtain ⟨α, hα⟩ := hsemi
  choose k hk using fun i => exists_int_of_cos_nonneg (hα i)
  have hconst : ∀ i, k i = k 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      rw [← ih]
      apply int_eq_of_step_lt_pi (hk i.castSucc) (hk i.succ)
      have h := hstep i
      rwa [sub_sub_sub_cancel_right]
  refine ⟨α - π / 2 + k 0 * (2 * π), fun i => ?_⟩
  obtain ⟨h1, h2⟩ := hk i
  rw [hconst i] at h1 h2
  constructor <;> linarith

/-- SM15 `lem:transport-angle-interval`, converse, angular form: entries in one interval
`[c, c + π]` have `cos (θ_i − α) ≥ 0` for `α = c + π/2`. No step hypothesis is needed. -/
theorem transport_angle_interval_converse_cos {ι : Type*} (θ : ι → ℝ)
    (h : ∃ c : ℝ, ∀ i, c ≤ θ i ∧ θ i ≤ c + π) :
    ∃ α : ℝ, ∀ i, 0 ≤ Real.cos (θ i - α) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c + π / 2, fun i => ?_⟩
  obtain ⟨h1, h2⟩ := hc i
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith

/-- SM15 `lem:transport-angle-interval` (lifting a semicircle to one real interval),
forward direction. If the finite real sequence `θ_0, …, θ_N` has `|θ_{i+1} − θ_i| < π`
and all its unit directions `(cos θ_i, sin θ_i)` lie in a closed semicircle, then all its
entries lie in one interval of length `π`. -/
theorem transport_angle_interval {N : ℕ} (θ : Fin (N + 1) → ℝ)
    (hstep : ∀ i : Fin N, |θ i.succ - θ i.castSucc| < π)
    (hsemi : InClosedSemicircle θ) :
    ∃ c : ℝ, ∀ i, c ≤ θ i ∧ θ i ≤ c + π :=
  transport_angle_interval_of_cos θ hstep ((inClosedSemicircle_iff θ).mp hsemi)

/-- SM15 `lem:transport-angle-interval`, converse. Containment of all entries in one
interval of length `π` puts their unit directions in a closed semicircle. -/
theorem transport_angle_interval_converse {ι : Type*} (θ : ι → ℝ)
    (h : ∃ c : ℝ, ∀ i, c ≤ θ i ∧ θ i ≤ c + π) : InClosedSemicircle θ :=
  (inClosedSemicircle_iff θ).mpr (transport_angle_interval_converse_cos θ h)

/-- SM15 `lem:transport-angle-interval`, both directions, for a sequence with all steps of
absolute size `< π`. -/
theorem transport_angle_interval_iff {N : ℕ} (θ : Fin (N + 1) → ℝ)
    (hstep : ∀ i : Fin N, |θ i.succ - θ i.castSucc| < π) :
    InClosedSemicircle θ ↔ ∃ c : ℝ, ∀ i, c ≤ θ i ∧ θ i ≤ c + π :=
  ⟨transport_angle_interval θ hstep, transport_angle_interval_converse θ⟩

end SM
