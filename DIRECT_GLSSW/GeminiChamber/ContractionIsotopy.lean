import ChamberContract.Contract
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false
open scoped BigOperators Classical Topology
open Filter

namespace DirectGLSSW.GeminiChamber

/-!
# Banach Contraction Perturbations and Composition of Ambient Plane Isotopies

This module provides:
1. Reflexivity and composition (`AmbientPlaneIsotopy.refl`, `AmbientPlaneIsotopy.trans`)
   for `AmbientPlaneIsotopy`.
2. A self-contained Banach contraction perturbation constructor
   `AmbientPlaneIsotopy.ofContractionPerturbation` showing that any family
   `z ↦ z + g t z` on `Plane = ℝ × ℝ` with `g` jointly continuous, `g start z = 0`,
   and `g t` uniformly `(1/2)`-Lipschitz in `z` defines an `AmbientPlaneIsotopy`.
-/

namespace AmbientPlaneIsotopy

/-- Identity ambient plane isotopy. -/
def refl : AmbientPlaneIsotopy where
  motion _ := Homeomorph.refl Plane
  at_start := rfl
  forward_continuous := continuous_snd
  inverse_continuous := continuous_snd

@[simp]
theorem refl_motion_apply (t : Time) (z : Plane) :
    refl.motion t z = z := rfl

/-- Composition of two ambient plane isotopies: first `I₁`, then `I₂`. -/
def trans (I₁ I₂ : AmbientPlaneIsotopy) : AmbientPlaneIsotopy where
  motion t := (I₁.motion t).trans (I₂.motion t)
  at_start := by
    rw [I₁.at_start, I₂.at_start]
    rfl
  forward_continuous :=
    I₂.forward_continuous.comp (continuous_fst.prodMk I₁.forward_continuous)
  inverse_continuous :=
    I₁.inverse_continuous.comp (continuous_fst.prodMk I₂.inverse_continuous)

@[simp]
theorem trans_motion_apply (I₁ I₂ : AmbientPlaneIsotopy) (t : Time) (z : Plane) :
    (I₁.trans I₂).motion t z = I₂.motion t (I₁.motion t z) := rfl

end AmbientPlaneIsotopy

section PlaneMetricLemmas

theorem plane_dist_eq (x y : Plane) :
    dist x y = max |x.1 - y.1| |x.2 - y.2| := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]

theorem plane_fst_sub_le_dist (x y : Plane) :
    |x.1 - y.1| ≤ dist x y := by
  rw [plane_dist_eq]
  exact le_max_left _ _

theorem plane_snd_sub_le_dist (x y : Plane) :
    |x.2 - y.2| ≤ dist x y := by
  rw [plane_dist_eq]
  exact le_max_right _ _

theorem plane_dist_le_iff (x y : Plane) (r : ℝ) :
    dist x y ≤ r ↔ |x.1 - y.1| ≤ r ∧ |x.2 - y.2| ≤ r := by
  rw [plane_dist_eq, max_le_iff]

theorem plane_dist_sub_self_left (w x y : Plane) :
    dist (w - x) (w - y) = dist x y := by
  rw [plane_dist_eq, plane_dist_eq]
  have h1 : (w - x).1 - (w - y).1 = -(x.1 - y.1) := by dsimp; ring
  have h2 : (w - x).2 - (w - y).2 = -(x.2 - y.2) := by dsimp; ring
  rw [h1, h2, abs_neg, abs_neg]

theorem plane_dist_add_self_left (w x y : Plane) :
    dist (w + x) (w + y) = dist x y := by
  rw [plane_dist_eq, plane_dist_eq]
  have h1 : (w + x).1 - (w + y).1 = x.1 - y.1 := by dsimp; ring
  have h2 : (w + x).2 - (w + y).2 = x.2 - y.2 := by dsimp; ring
  rw [h1, h2]

theorem plane_dist_sub_le (a b c d : Plane) :
    dist (a - b) (c - d) ≤ dist a c + dist b d := by
  rw [plane_dist_le_iff]
  have h1 : (a - b).1 - (c - d).1 = (a.1 - c.1) - (b.1 - d.1) := by dsimp; ring
  have h2 : (a - b).2 - (c - d).2 = (a.2 - c.2) - (b.2 - d.2) := by dsimp; ring
  constructor
  · rw [h1]
    exact (abs_sub _ _).trans (add_le_add (plane_fst_sub_le_dist a c) (plane_fst_sub_le_dist b d))
  · rw [h2]
    exact (abs_sub _ _).trans (add_le_add (plane_snd_sub_le_dist a c) (plane_snd_sub_le_dist b d))

theorem plane_dist_add_le (a b c d : Plane) :
    dist (a + b) (c + d) ≤ dist a c + dist b d := by
  rw [plane_dist_le_iff]
  have h1 : (a + b).1 - (c + d).1 = (a.1 - c.1) + (b.1 - d.1) := by dsimp; ring
  have h2 : (a + b).2 - (c + d).2 = (a.2 - c.2) + (b.2 - d.2) := by dsimp; ring
  constructor
  · rw [h1]
    exact (abs_add _ _).trans (add_le_add (plane_fst_sub_le_dist a c) (plane_fst_sub_le_dist b d))
  · rw [h2]
    exact (abs_add _ _).trans (add_le_add (plane_snd_sub_le_dist a c) (plane_snd_sub_le_dist b d))

theorem plane_dist_smul (r : ℝ) (x y : Plane) :
    dist (r • x) (r • y) = |r| * dist x y := by
  rw [plane_dist_eq, plane_dist_eq]
  have h1 : (r • x).1 - (r • y).1 = r * (x.1 - y.1) := by dsimp [smul_eq_mul]; ring
  have h2 : (r • x).2 - (r • y).2 = r * (x.2 - y.2) := by dsimp [smul_eq_mul]; ring
  rw [h1, h2, abs_mul, abs_mul, ← mul_max_of_nonneg _ _ (abs_nonneg r)]

end PlaneMetricLemmas

section ContractionFixedPoint

/-- Any `(1/2)`-contraction on `Plane = ℝ × ℝ` has a fixed point. -/
theorem contraction_half_fixedPoint (h : Plane → Plane)
    (hh : ∀ x y : Plane, dist (h x) (h y) ≤ (1 / 2 : ℝ) * dist x y) :
    ∃ z : Plane, h z = z := by
  have hcont : Continuous h := by
    rw [Metric.continuous_iff]
    intro x ε hε
    refine ⟨ε, hε, fun y hy => ?_⟩
    have hle := hh y x
    have hnonneg : 0 ≤ dist y x := dist_nonneg
    linarith
  let seq : ℕ → Plane := fun n => h^[n] 0
  have hstep : ∀ n : ℕ, dist (seq n) (seq (n + 1)) ≤ (2 * dist (0 : Plane) (h 0)) / 2 / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      change dist (0 : Plane) (h 0) ≤ (2 * dist (0 : Plane) (h 0)) / 2 / 2 ^ 0
      rw [pow_zero]
      linarith
    | succ n ih =>
      have hsucc1 : seq (n + 1) = h (seq n) := Function.iterate_succ_apply' h n 0
      have hsucc2 : seq (n + 2) = h (seq (n + 1)) := Function.iterate_succ_apply' h (n + 1) 0
      rw [hsucc1, hsucc2]
      calc
        dist (h (seq n)) (h (seq (n + 1)))
            ≤ (1 / 2 : ℝ) * dist (seq n) (seq (n + 1)) := hh (seq n) (seq (n + 1))
        _ ≤ (1 / 2 : ℝ) * ((2 * dist (0 : Plane) (h 0)) / 2 / 2 ^ n) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 * dist (0 : Plane) (h 0)) / 2 / 2 ^ (n + 1) := by
          rw [pow_succ]
          ring
  have hcauchy : CauchySeq seq :=
    cauchySeq_of_le_geometric_two (C := 2 * dist (0 : Plane) (h 0)) hstep
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hz_shift : Tendsto (fun n => seq (n + 1)) atTop (𝓝 z) :=
    (tendsto_add_atTop_iff_nat 1).mpr hz
  have hz_image : Tendsto (fun n => seq (n + 1)) atTop (𝓝 (h z)) := by
    have heq : (fun n => seq (n + 1)) = (fun n => h (seq n)) := by
      funext n
      exact Function.iterate_succ_apply' h n 0
    rw [heq]
    exact (hcont.tendsto z).comp hz
  exact ⟨z, tendsto_nhds_unique hz_image hz_shift⟩

theorem perturbation_dist_le_two_mul_dist (g : Plane → Plane)
    (hg : ∀ x y : Plane, dist (g x) (g y) ≤ (1 / 2 : ℝ) * dist x y)
    (x y : Plane) :
    dist x y ≤ 2 * dist (x + g x) (y + g y) := by
  have hx : x = (x + g x) - g x := by abel
  have hy : y = (y + g y) - g y := by abel
  have htri : dist x y ≤ dist (x + g x) (y + g y) + dist (g x) (g y) := by
     conv_lhs => rw [hx, hy]
     exact plane_dist_sub_le (x + g x) (g x) (y + g y) (g y)
  have hlip := hg x y
  linarith

theorem perturbation_bijective (g : Plane → Plane)
    (hg : ∀ x y : Plane, dist (g x) (g y) ≤ (1 / 2 : ℝ) * dist x y) :
    Function.Bijective (fun z : Plane => z + g z) := by
  constructor
  · intro x y hxy
    dsimp at hxy
    have hle := perturbation_dist_le_two_mul_dist g hg x y
    rw [hxy, dist_self, mul_zero] at hle
    exact dist_le_zero.mp hle
  · intro w
    obtain ⟨z, hz⟩ := contraction_half_fixedPoint (fun z => w - g z) (by
      intro x y
      rw [plane_dist_sub_self_left]
      exact hg x y)
    refine ⟨z, ?_⟩
    calc
      z + g z = (w - g z) + g z := by rw [hz]
      _ = w := sub_add_cancel w (g z)

/-- Construct an `AmbientPlaneIsotopy` from a `(1/2)`-Lipschitz perturbation of the identity. -/
noncomputable def AmbientPlaneIsotopy.ofContractionPerturbation
    (g : Time → Plane → Plane)
    (hg_cont : Continuous (fun p : Time × Plane => g p.1 p.2))
    (hg_start : ∀ z : Plane, g start z = 0)
    (hg_lip : ∀ (t : Time) (x y : Plane), dist (g t x) (g t y) ≤ (1 / 2 : ℝ) * dist x y) :
    AmbientPlaneIsotopy := by
  let Φ : Time → Plane ≃ Plane := fun t =>
    Equiv.ofBijective (fun z => z + g t z) (perturbation_bijective (g t) (hg_lip t))
  have hΦ_apply : ∀ (t : Time) (z : Plane), Φ t z = z + g t z := fun _ _ => rfl
  have hΦ_symm_spec : ∀ (t : Time) (w : Plane), Φ t ((Φ t).symm w) = w :=
    fun t w => (Φ t).apply_symm_apply w
  have hfwd_cont : Continuous (fun p : Time × Plane => Φ p.1 p.2) :=
    continuous_snd.add hg_cont
  have hinv_bound : ∀ (t t₀ : Time) (w w₀ : Plane),
      dist ((Φ t).symm w) ((Φ t₀).symm w₀) ≤
        2 * dist w w₀ + 2 * dist (g t ((Φ t₀).symm w₀)) (g t₀ ((Φ t₀).symm w₀)) := by
    intro t t₀ w w₀
    let z := (Φ t).symm w
    let z₀ := (Φ t₀).symm w₀
    change dist z z₀ ≤ 2 * dist w w₀ + 2 * dist (g t z₀) (g t₀ z₀)
    have h1 : dist z z₀ ≤ 2 * dist (Φ t z) (Φ t z₀) :=
      perturbation_dist_le_two_mul_dist (g t) (hg_lip t) z z₀
    have h2 : Φ t z = w := hΦ_symm_spec t w
    have h3 : Φ t₀ z₀ = w₀ := hΦ_symm_spec t₀ w₀
    have h4 : dist (Φ t z) (Φ t z₀) ≤ dist w w₀ + dist (Φ t₀ z₀) (Φ t z₀) := by
      rw [h2, ← h3]
      exact dist_triangle w (Φ t₀ z₀) (Φ t z₀)
    have h5 : dist (Φ t₀ z₀) (Φ t z₀) = dist (g t z₀) (g t₀ z₀) := by
      rw [hΦ_apply, hΦ_apply, plane_dist_add_self_left, dist_comm]
    linarith
  have hinv_cont : Continuous (fun p : Time × Plane => (Φ p.1).symm p.2) := by
    rw [continuous_iff_continuousAt]
    rintro ⟨t₀, w₀⟩
    rw [Metric.continuousAt_iff]
    intro ε hε
    let z₀ := (Φ t₀).symm w₀
    have hgt_cont : Continuous (fun t : Time => g t z₀) :=
      hg_cont.comp (continuous_id.prodMk continuous_const)
    have hε4 : 0 < ε / 4 := by linarith
    obtain ⟨δ₁, hδ₁, hδ₁_spec⟩ := Metric.continuousAt_iff.mp hgt_cont.continuousAt (ε / 4) hε4
    refine ⟨min δ₁ (ε / 4), lt_min hδ₁ hε4, ?_⟩
    rintro ⟨t, w⟩ hdist
    have hdt : dist t t₀ < δ₁ :=
      lt_of_le_of_lt (le_max_left (dist t t₀) (dist w w₀))
        (lt_of_lt_of_le (by simpa [Prod.dist_eq] using hdist) (min_le_left _ _))
    have hdw : dist w w₀ < ε / 4 :=
      lt_of_le_of_lt (le_max_right (dist t t₀) (dist w w₀))
        (lt_of_lt_of_le (by simpa [Prod.dist_eq] using hdist) (min_le_right _ _))
    have hdg : dist (g t z₀) (g t₀ z₀) < ε / 4 := hδ₁_spec hdt
    have hb := hinv_bound t t₀ w w₀
    dsimp [z₀] at hdg ⊢
    linarith
  refine
    { motion := fun t =>
        { toEquiv := Φ t
          continuous_toFun := hfwd_cont.comp (continuous_const.prodMk continuous_id)
          continuous_invFun := hinv_cont.comp (continuous_const.prodMk continuous_id) }
      at_start := ?_
      forward_continuous := hfwd_cont
      inverse_continuous := hinv_cont }
  ext z : 1
  change z + g start z = z
  rw [hg_start z, add_zero]

@[simp]
theorem AmbientPlaneIsotopy.ofContractionPerturbation_apply
    (g : Time → Plane → Plane)
    (hg_cont : Continuous (fun p : Time × Plane => g p.1 p.2))
    (hg_start : ∀ z : Plane, g start z = 0)
    (hg_lip : ∀ (t : Time) (x y : Plane), dist (g t x) (g t y) ≤ (1 / 2 : ℝ) * dist x y)
    (t : Time) (z : Plane) :
    (AmbientPlaneIsotopy.ofContractionPerturbation g hg_cont hg_start hg_lip).motion t z =
      z + g t z := rfl

end ContractionFixedPoint

end DirectGLSSW.GeminiChamber
