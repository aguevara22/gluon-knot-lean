/-
RPC_Skeleton.lean — proof skeleton for `SM.RegularPoleCount` (fd:regular-pole-count, sm-3:2894-2897),
the isolated hypothesis of row 88 fd:linking-calculus.  Written 2026-09-14 by the feasibility-probe
agent after the FEASIBLE verdict (work/drafts/fd/REGULAR_POLE_COUNT_FEASIBILITY.md).  Plan and
per-leaf notes: work/drafts/fd/RPC_PLAN.md.

ROUTE ("bump primitive").  For a unit `N` and smooth doubly periodic `G : ℝ² → S²`, with
`D = ⟪G, G_u × G_v⟫` and `Z = ⟪G, N⟫`:
* for ANY smooth `k : ℝ → ℝ` the 1-form `G^*(k(Z)·(N × x)·dx)` has exterior derivative
  `D · m_k(Z) du∧dv`, `m_k(Z) = 2Z k(Z) − (1 − Z²) k'(Z)`  (U-A, `fderiv_oneForm_antisymm`);
  `k = −1/(4π(1−Z))` is the printed `λ_N` with `m_k ≡ 1/(4π)`;
* exactness + periodicity give `∫∫ D · m_k(Z) = 0`  (U-A, `integral_triple_mul_mk_eq_zero`);
* with the smooth cutoff `k_χ = (χ−1)/(4π(1−Z))`, `χ` a `ContDiffBump` at `Z = 1`:
  `m_{k_χ} = 1/(4π) − φ'(Z)`, `φ = (1+Z)χ/(4π)`, hence `gaussIntegral P G = ∫∫ D · φ'(Z)`;
* `φ'(Z∘G)` is supported in the inverse image of a small cap, which lies in disjoint inverse-function
  neighbourhoods of the preimages (U-B); on each, the change of variables through the chart
  `F = (⟪G,e₁⟫, ⟪G,e₂⟫)` (`det DF = D·Z`) gives `sign(D p) · ∫_{ℝ²} ψ`, and `∫ ψ = 1` by polar
  coordinates (U-C); a shift of the fundamental domain removes boundary preimages (U-D).
No winding number, no degree theory, no limit `h → 0`.

Leaves are marked `-- LEAF <unit><n>`; everything else is proved.  Units: U-A algebra/exactness,
U-B frame/IFT/neighbourhoods, U-C change of variables/polar integral, U-D assembly.
-/
import SM.LinkingCalculus
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.PolarCoord

namespace SM

open scoped RealInnerProductSpace ContDiff
open Set Function Filter Topology Real MeasureTheory
open LinkingCalculus

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace RPC

/-! ## Shared definitions -/

/-- `(1, 0)` in `ℝ × ℝ`. -/
def eu2 : ℝ × ℝ := (1, 0)
/-- `(0, 1)` in `ℝ × ℝ`. -/
def ev2 : ℝ × ℝ := (0, 1)

/-- The pulled-back 1-form coefficient `G^*(k(Z)·(N × x)·dx)(w) = k(⟪G x, N⟫) ⟪N × G x, G'(x) w⟫`.
With `k = −1/(4π(1−Z))` this is the printed `λ_N = −(X dY − Y dX)/(4π(1−Z))` (sm-3:2871). -/
def oneForm (k : ℝ → ℝ) (N : E3) (G : ℝ × ℝ → E3) (x w : ℝ × ℝ) : ℝ :=
  k ⟪G x, N⟫ * ⟪cross N (G x), fderiv ℝ G x w⟫

/-- `m_k(Z) = 2 Z k(Z) − (1 − Z²) k'(Z)`. -/
def mk (k : ℝ → ℝ) (Z : ℝ) : ℝ := 2 * Z * k Z - (1 - Z ^ 2) * deriv k Z

/-- The smooth cutoff primitive coefficient `k_χ(Z) = (χ(Z) − 1)/(4π(1 − Z))`; `χ ≡ 1` near `Z = 1`
so `k_χ ≡ 0` there, and `k_χ = −1/(4π(1−Z))` (the printed `λ_N`) where `χ = 0`. -/
def cutoffK (χ : ContDiffBump (1 : ℝ)) (Z : ℝ) : ℝ := (χ Z - 1) / (4 * π * (1 - Z))

/-- The bump potential `φ(Z) = (1 + Z) χ(Z)/(4π)`: `φ'(Z)·dA` is the smooth 2-form of mass `1`
supported in the cap `Z > 1 − rOut` with `d(k_χ(Z)(N×x)·dx) = ω − φ'(Z) dA`. -/
def bumpPhi (χ : ContDiffBump (1 : ℝ)) (Z : ℝ) : ℝ := (1 + Z) * χ Z / (4 * π)

/-- The chart at `N`: orthogonal projection to `N^⊥` in a positive orthonormal frame `(e₁, e₂, N)`. -/
def chart (e₁ e₂ : E3) (G : ℝ × ℝ → E3) (x : ℝ × ℝ) : ℝ × ℝ := (⟪e₁, G x⟫, ⟪e₂, G x⟫)

/-- The derivative of the chart, as a continuous linear map. -/
def chartDeriv (e₁ e₂ : E3) (G : ℝ × ℝ → E3) (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ((innerSL ℝ e₁).comp (fderiv ℝ G x)).prod ((innerSL ℝ e₂).comp (fderiv ℝ G x))

/-- The bump density in the chart: `ψ(w) = φ'(√(1 − |w|²))/√(1 − |w|²)` on the open unit disc. -/
def chartDensity (χ : ContDiffBump (1 : ℝ)) (w : ℝ × ℝ) : ℝ :=
  if w.1 ^ 2 + w.2 ^ 2 < 1 then
    deriv (bumpPhi χ) (√(1 - (w.1 ^ 2 + w.2 ^ 2))) / √(1 - (w.1 ^ 2 + w.2 ^ 2)) else 0

/-- A system of inverse-function neighbourhoods for the finite preimage set `S` of `N` inside the
closed box `[a,a+P]×[b,b+P]`: disjoint open `V p ∋ p` inside the open box on which the chart is
injective, `Z > 0`, `sign D` is constant, and whose chart images contain a common ball `B(0,r)`;
off `⋃ V p` (within the closed box) `Z` stays below `1 − δ`. -/
structure NhdSystem (e₁ e₂ N : E3) (G : ℝ × ℝ → E3) (a b P : ℝ) (S : Finset (ℝ × ℝ)) where
  V : ℝ × ℝ → Set (ℝ × ℝ)
  r : ℝ
  δ : ℝ
  r_pos : 0 < r
  δ_pos : 0 < δ
  V_isOpen : ∀ p ∈ S, IsOpen (V p)
  mem_V : ∀ p ∈ S, p ∈ V p
  V_subset : ∀ p ∈ S, V p ⊆ Ioo a (a + P) ×ˢ Ioo b (b + P)
  injOn_V : ∀ p ∈ S, InjOn (chart e₁ e₂ G) (V p)
  pos_V : ∀ p ∈ S, ∀ x ∈ V p, 0 < ⟪G x, N⟫
  sign_V : ∀ p ∈ S, ∀ x ∈ V p,
    Real.sign (Family.triple G eu2 ev2 x) = Real.sign (Family.triple G eu2 ev2 p)
  ball_subset : ∀ p ∈ S, Metric.ball (0 : ℝ × ℝ) r ⊆ chart e₁ e₂ G '' V p
  disjoint_V : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint (V p) (V q)
  small : ∀ x ∈ Icc a (a + P) ×ˢ Icc b (b + P), x ∉ ⋃ p ∈ S, V p → ⟪G x, N⟫ < 1 - δ

/-! ## U-A. Algebra and exactness -/
section UA

/-- Binet–Cauchy in `ℝ³`. (PROVED) -/
theorem inner_cross_cross' (a b c d : E3) :
    ⟪cross a b, cross c d⟫ = ⟪a, c⟫ * ⟪b, d⟫ - ⟪a, d⟫ * ⟪b, c⟫ := by
  simp only [inner_eq_sum, cross_apply0, cross_apply1, cross_apply2]; ring

/-- The algebraic core of `d(G^*λ_k) = D · m_k(Z)`: `g = G x`, `gu, gv` the partials,
`n = N`, `gu × gv = D • g`. (PROVED) -/
theorem core_algebra (g gu gv n : E3) (k k' D : ℝ) (hg : ‖g‖ = 1) (hn : ‖n‖ = 1)
    (hD : cross gu gv = D • g) :
    k' * (⟪gu, n⟫ * ⟪cross n g, gv⟫ - ⟪gv, n⟫ * ⟪cross n g, gu⟫)
      + k * (⟪cross n gu, gv⟫ - ⟪cross n gv, gu⟫)
      = D * (2 * ⟪g, n⟫ * k - (1 - ⟪g, n⟫ ^ 2) * k') := by
  have h1 : ⟪gu, n⟫ * ⟪cross n g, gv⟫ - ⟪gv, n⟫ * ⟪cross n g, gu⟫
      = ⟪cross n (cross n g), cross gu gv⟫ := by
    rw [inner_cross_cross']
    simp only [real_inner_comm n gu, real_inner_comm n gv]
  have h2 : ⟪cross n gu, gv⟫ - ⟪cross n gv, gu⟫ = 2 * ⟪n, cross gu gv⟫ := by
    rw [real_inner_comm gv (cross n gu), inner_cross_cyclic, real_inner_comm gu (cross n gv),
      inner_cross_cyclic, inner_cross_swap]; ring
  have hgg : ⟪g, g⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hg]; norm_num
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  rw [h1, h2, hD, cross_cross_eq, hnn, one_smul]
  simp only [inner_sub_left, real_inner_smul_left, real_inner_smul_right, hgg, real_inner_comm g n]
  ring

/-- `gaussDensity` is `Family.triple` of the uncurried map. (PROVED) -/
theorem gaussDensity_eq_triple' {G : ℝ → ℝ → E3} (hG : ContDiff ℝ ∞ (uncurry G)) (u v : ℝ) :
    gaussDensity G u v = Family.triple (uncurry G) eu2 ev2 (u, v) := by
  have hd : DifferentiableAt ℝ (uncurry G) (u, v) := hG.differentiable (by simp) (u, v)
  simp only [gaussDensity, Family.triple, pderivU_eq_fderiv hd, pderivV_eq_fderiv hd, eu2, ev2,
    uncurry_apply_pair]

/-- The density is doubly periodic (no smoothness needed). (PROVED) -/
theorem gaussDensity_periodic {G : ℝ → ℝ → E3} {P : ℝ}
    (hpu : ∀ v, Periodic (fun u => G u v) P) (hpv : ∀ u, Periodic (G u) P) (u v : ℝ) :
    gaussDensity G (u + P) v = gaussDensity G u v ∧
      gaussDensity G u (v + P) = gaussDensity G u v := by
  have hGu : ∀ u v, G (u + P) v = G u v := fun u v => hpu v u
  have hGv : ∀ u v, G u (v + P) = G u v := fun u v => hpv u v
  have hU1 : pderivU G (u + P) v = pderivU G u v := by
    unfold pderivU
    rw [← deriv_comp_add_const]
    congr 1; funext u'; exact hGu u' v
  have hV1 : pderivV G (u + P) v = pderivV G u v := by
    unfold pderivV
    congr 1; funext v'; exact hGu u v'
  have hU2 : pderivU G u (v + P) = pderivU G u v := by
    unfold pderivU
    congr 1; funext u'; exact hGv u' v
  have hV2 : pderivV G u (v + P) = pderivV G u v := by
    unfold pderivV
    rw [← deriv_comp_add_const]
    congr 1; funext v'; exact hGv u v'
  constructor
  · simp only [gaussDensity, hU1, hV1, hGu]
  · simp only [gaussDensity, hU2, hV2, hGv]

-- LEAF A1
/-- `G_a × G_b = D_{ab} • G` when `‖G‖ ≡ 1` (both partials are orthogonal to `G`). -/
theorem cross_fderiv_eq_smul {G : ℝ × ℝ → E3} (hG : ContDiff ℝ ∞ G) (hn : ∀ y, ‖G y‖ = 1)
    (x a b : ℝ × ℝ) :
    cross (fderiv ℝ G x a) (fderiv ℝ G x b) = Family.triple G a b x • G x := by
  sorry

-- LEAF A2
/-- Derivative of the 1-form coefficient (analogue of `Family.fderiv_triple_apply`). -/
theorem fderiv_oneForm_apply {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (N : E3) {G : ℝ × ℝ → E3}
    (hG : ContDiff ℝ ∞ G) (x w c : ℝ × ℝ) :
    fderiv ℝ (fun y => oneForm k N G y w) x c
      = deriv k ⟪G x, N⟫ * ⟪fderiv ℝ G x c, N⟫ * ⟪cross N (G x), fderiv ℝ G x w⟫
        + k ⟪G x, N⟫ * (⟪cross N (fderiv ℝ G x c), fderiv ℝ G x w⟫
            + ⟪cross N (G x), fderiv ℝ (fderiv ℝ G) x c w⟫) := by
  sorry

-- LEAF A3
/-- Smoothness of the 1-form coefficient. -/
theorem contDiff_oneForm {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (N : E3) {G : ℝ × ℝ → E3}
    (hG : ContDiff ℝ ∞ G) (w : ℝ × ℝ) : ContDiff ℝ ∞ (fun y => oneForm k N G y w) := by
  sorry

/-- Periodicity of the 1-form coefficient. (PROVED) -/
theorem periodic_oneForm (k : ℝ → ℝ) (N : E3) {G : ℝ × ℝ → E3} {T : ℝ × ℝ} (h : Periodic G T)
    (w : ℝ × ℝ) : Periodic (fun y => oneForm k N G y w) T := by
  intro y
  simp only [oneForm, h y, Family.periodic_fderiv_apply h w y]

-- LEAF A4
/-- THE EXTERIOR DERIVATIVE: `∂_u B − ∂_v A = D · m_k(Z)` for `A = oneForm · eu2`, `B = oneForm · ev2`.
From `fderiv_oneForm_apply` twice, `Family.fderiv_fderiv_symm` (the `G''` terms cancel),
`cross_fderiv_eq_smul`, and `core_algebra`. -/
theorem fderiv_oneForm_antisymm {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) {N : E3} (hN : ‖N‖ = 1)
    {G : ℝ × ℝ → E3} (hG : ContDiff ℝ ∞ G) (hn : ∀ y, ‖G y‖ = 1) (x : ℝ × ℝ) :
    fderiv ℝ (fun y => oneForm k N G y ev2) x eu2
      - fderiv ℝ (fun y => oneForm k N G y eu2) x ev2
      = Family.triple G eu2 ev2 x * mk k ⟪G x, N⟫ := by
  sorry

-- LEAF A5
/-- Green on the period box, `u`-direction: `∫∫ ∂_u F = 0` (swap, FTC per slice, periodicity);
two-variable copy of `Family.integral_fderiv1_eq_zero`. -/
theorem integral_fderiv_eu_eq_zero {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {P : ℝ}
    (hper : Periodic F (P, 0)) (a b : ℝ) :
    ∫ u in a..a + P, ∫ v in b..b + P, fderiv ℝ F (u, v) eu2 = 0 := by
  sorry

-- LEAF A6
/-- Green on the period box, `v`-direction (FTC on the inner integral, periodicity). -/
theorem integral_fderiv_ev_eq_zero {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {P : ℝ}
    (hper : Periodic F (0, P)) (a b : ℝ) :
    ∫ u in a..a + P, ∫ v in b..b + P, fderiv ℝ F (u, v) ev2 = 0 := by
  sorry

-- LEAF A7
/-- EXACTNESS: `∫∫ D · m_k(Z) = 0` on any period box, for every smooth `k`. -/
theorem integral_triple_mul_mk_eq_zero {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) {N : E3} (hN : ‖N‖ = 1)
    {G : ℝ × ℝ → E3} (hG : ContDiff ℝ ∞ G) (hn : ∀ y, ‖G y‖ = 1) {P : ℝ}
    (hpu : Periodic G (P, 0)) (hpv : Periodic G (0, P)) (a b : ℝ) :
    ∫ u in a..a + P, ∫ v in b..b + P,
      Family.triple G eu2 ev2 (u, v) * mk k ⟪G (u, v), N⟫ = 0 := by
  sorry

/-- The bump is differentiable. (PROVED) -/
theorem hasDerivAt_bump (χ : ContDiffBump (1 : ℝ)) (Z : ℝ) :
    HasDerivAt (fun z => χ z) (deriv (fun z => χ z) Z) Z :=
  ((χ.contDiff (n := 1)).differentiable one_ne_zero Z).hasDerivAt

/-- `φ'(Z) = (χ(Z) + (1+Z) χ'(Z))/(4π)`. (PROVED) -/
theorem deriv_bumpPhi (χ : ContDiffBump (1 : ℝ)) (Z : ℝ) :
    deriv (bumpPhi χ) Z = (χ Z + (1 + Z) * deriv (fun z => χ z) Z) / (4 * π) := by
  have h : HasDerivAt (fun z => (1 + z) * χ z)
      (1 * χ Z + (1 + Z) * deriv (fun z => χ z) Z) Z :=
    ((hasDerivAt_id Z).const_add 1).mul (hasDerivAt_bump χ Z)
  rw [show bumpPhi χ = fun z => ((1 + z) * χ z) / (4 * π) from rfl, deriv_div_const, h.deriv]
  ring

-- LEAF A8
/-- `k_χ` is smooth on `ℝ`: a smooth quotient on `{Z < 1}` and on `{Z > 1}`, identically `0` on
`ball 1 rIn` (where `χ = 1`); glue with `contDiff_iff_contDiffAt`. -/
theorem contDiff_cutoffK (χ : ContDiffBump (1 : ℝ)) : ContDiff ℝ ∞ (cutoffK χ) := by
  sorry

/-- The cutoff identity away from `Z = 1`. (PROVED) -/
theorem mk_cutoffK_of_ne (χ : ContDiffBump (1 : ℝ)) {Z : ℝ} (hZ : Z ≠ 1) :
    mk (cutoffK χ) Z = 1 / (4 * π) - deriv (bumpPhi χ) Z := by
  have hden : 4 * π * (1 - Z) ≠ 0 := by
    have := Real.pi_pos; intro h; apply hZ; nlinarith [mul_eq_zero.mp h]
  have hd : HasDerivAt (cutoffK χ)
      ((deriv (fun z => χ z) Z * (4 * π * (1 - Z)) - (χ Z - 1) * (4 * π * (-1))) /
        (4 * π * (1 - Z)) ^ 2) Z := by
    have h1 : HasDerivAt (fun z => χ z - 1) (deriv (fun z => χ z) Z) Z :=
      (hasDerivAt_bump χ Z).sub_const 1
    have h2 : HasDerivAt (fun z : ℝ => 4 * π * (1 - z)) (4 * π * (-1)) Z := by
      have := ((hasDerivAt_id Z).const_sub 1).const_mul (4 * π)
      simpa using this
    exact h1.div h2 hden
  rw [mk, hd.deriv, deriv_bumpPhi, cutoffK]
  field_simp
  ring

-- LEAF A9
/-- The cutoff identity at `Z = 1`: both sides vanish (`k_χ ≡ 0` and `χ ≡ 1` near `1`, so
`deriv (fun z => χ z) 1 = 0`; note `(1 - 1^2) = 0` kills the `deriv (cutoffK χ)` term). -/
theorem mk_cutoffK_one (χ : ContDiffBump (1 : ℝ)) :
    mk (cutoffK χ) 1 = 1 / (4 * π) - deriv (bumpPhi χ) 1 := by
  sorry

/-- The cutoff identity `m_{k_χ}(Z) = 1/(4π) − φ'(Z)` everywhere. (PROVED from A9) -/
theorem mk_cutoffK (χ : ContDiffBump (1 : ℝ)) (Z : ℝ) :
    mk (cutoffK χ) Z = 1 / (4 * π) - deriv (bumpPhi χ) Z := by
  by_cases hZ : Z = 1
  · subst hZ; exact mk_cutoffK_one χ
  · exact mk_cutoffK_of_ne χ hZ

-- LEAF A10
/-- Shift of the fundamental domain for `gaussIntegral` (periodicity of the density in each variable,
`Function.Periodic.intervalIntegral_add_eq`) and `gaussDensity = triple`. -/
theorem gaussIntegral_eq_shift {G : ℝ → ℝ → E3} (hG : ContDiff ℝ ∞ (uncurry G)) {P : ℝ}
    (hpu : ∀ v, Periodic (fun u => G u v) P) (hpv : ∀ u, Periodic (G u) P) (a b : ℝ) :
    gaussIntegral P G
      = (1 / (4 * π)) * ∫ u in a..a + P, ∫ v in b..b + P,
          Family.triple (uncurry G) eu2 ev2 (u, v) := by
  sorry

-- LEAF A11
/-- STEP 1 CONCLUSION: `gaussIntegral P G = ∫∫ D · φ'(Z)` on any period box.  From
`gaussIntegral_eq_shift`, the pointwise `D/(4π) = D · m_{k_χ}(Z) + D · φ'(Z)` (`mk_cutoffK`),
linearity of the iterated integral, and `integral_triple_mul_mk_eq_zero` with `k = cutoffK χ`. -/
theorem gaussIntegral_eq_integral_bump (χ : ContDiffBump (1 : ℝ)) {N : E3} (hN : ‖N‖ = 1)
    {G : ℝ → ℝ → E3} (hG : ContDiff ℝ ∞ (uncurry G)) (hn : ∀ u v, ‖G u v‖ = 1) {P : ℝ}
    (hpu : ∀ v, Periodic (fun u => G u v) P) (hpv : ∀ u, Periodic (G u) P) (a b : ℝ) :
    gaussIntegral P G
      = ∫ u in a..a + P, ∫ v in b..b + P,
          Family.triple (uncurry G) eu2 ev2 (u, v) * deriv (bumpPhi χ) ⟪G u v, N⟫ := by
  sorry

end UA

/-! ## U-B. Frame, chart Jacobian, inverse-function neighbourhoods, compactness -/
section UB

-- LEAF B1
/-- A positive orthonormal frame `(e₁, e₂, N)` completing a unit vector `N`. -/
theorem exists_frame {N : E3} (hN : ‖N‖ = 1) :
    ∃ e₁ e₂ : E3, ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧ ⟪e₁, e₂⟫ = 0 ∧ cross e₁ e₂ = N := by
  sorry

-- LEAF B2
/-- Parseval for the frame: `⟪x,e₁⟫² + ⟪x,e₂⟫² + ⟪x,N⟫² = ‖x‖²`. -/
theorem frame_parseval {e₁ e₂ N : E3} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : ⟪e₁, e₂⟫ = 0)
    (hN : cross e₁ e₂ = N) (x : E3) :
    ⟪x, e₁⟫ ^ 2 + ⟪x, e₂⟫ ^ 2 + ⟪x, N⟫ ^ 2 = ‖x‖ ^ 2 := by
  sorry

/-- The chart is differentiable with derivative `chartDeriv`. (PROVED) -/
theorem hasFDerivAt_chart (e₁ e₂ : E3) {G : ℝ × ℝ → E3} (hG : ContDiff ℝ ∞ G) (x : ℝ × ℝ) :
    HasFDerivAt (chart e₁ e₂ G) (chartDeriv e₁ e₂ G x) x := by
  have hd : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by simp) x).hasFDerivAt
  exact ((innerSL ℝ e₁).hasFDerivAt.comp x hd).prodMk ((innerSL ℝ e₂).hasFDerivAt.comp x hd)

-- LEAF B4
/-- Determinant of a linear map of `ℝ × ℝ` in the standard basis
(`LinearMap.det_toMatrix (Basis.finTwoProd ℝ)`, `Matrix.det_fin_two`). -/
theorem det_eq_fin_two (f : ℝ × ℝ →L[ℝ] ℝ × ℝ) :
    f.det = (f (1, 0)).1 * (f (0, 1)).2 - (f (0, 1)).1 * (f (1, 0)).2 := by
  sorry

-- LEAF B5
/-- Jacobian of the chart: `det DF = ⟪e₁ × e₂, G_u × G_v⟫ = D · Z`
(`det_eq_fin_two`, `inner_cross_cross'`, `cross_fderiv_eq_smul`). -/
theorem det_chartDeriv {e₁ e₂ N : E3} (hN : cross e₁ e₂ = N) {G : ℝ × ℝ → E3}
    (hG : ContDiff ℝ ∞ G) (hn : ∀ y, ‖G y‖ = 1) (x : ℝ × ℝ) :
    (chartDeriv e₁ e₂ G x).det = Family.triple G eu2 ev2 x * ⟪G x, N⟫ := by
  sorry

-- LEAF B6
/-- At a regular preimage the chart has an invertible strict derivative
(`det_chartDeriv` gives `det = D p ≠ 0`; `LinearMap.equivOfDetNeZero`,
`LinearEquiv.toContinuousLinearEquiv`, `ContDiffAt.hasStrictFDerivAt`, `hasFDerivAt_chart`). -/
theorem exists_strict_equiv_chart {e₁ e₂ N : E3} (hN : cross e₁ e₂ = N) (hNu : ‖N‖ = 1)
    {G : ℝ × ℝ → E3} (hG : ContDiff ℝ ∞ G) (hn : ∀ y, ‖G y‖ = 1) {p : ℝ × ℝ} (hp : G p = N)
    (hD : Family.triple G eu2 ev2 p ≠ 0) :
    ∃ e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      HasStrictFDerivAt (chart e₁ e₂ G) (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
  sorry

-- LEAF B7
/-- Inverse-function neighbourhood at a regular preimage: an open `V ∋ p` inside a prescribed
neighbourhood `U`, with the chart injective on `V`, `Z > 0` and `sign D` constant on `V`, and the
chart image containing a ball around `chart p = 0` (`HasStrictFDerivAt.toOpenPartialHomeomorph`,
`map_nhds_eq_of_equiv`, `Metric.mem_nhds_iff`). -/
theorem exists_regular_nhd {e₁ e₂ N : E3} (hN : cross e₁ e₂ = N) (hNu : ‖N‖ = 1)
    {G : ℝ × ℝ → E3} (hG : ContDiff ℝ ∞ G) (hn : ∀ y, ‖G y‖ = 1) {p : ℝ × ℝ} (hp : G p = N)
    (hD : Family.triple G eu2 ev2 p ≠ 0) {U : Set (ℝ × ℝ)} (hU : U ∈ 𝓝 p) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ InjOn (chart e₁ e₂ G) V ∧
      (∀ x ∈ V, 0 < ⟪G x, N⟫) ∧
      (∀ x ∈ V, Real.sign (Family.triple G eu2 ev2 x) = Real.sign (Family.triple G eu2 ev2 p)) ∧
      ∃ r > 0, Metric.ball (0 : ℝ × ℝ) r ⊆ chart e₁ e₂ G '' V := by
  sorry

-- LEAF B8
/-- Disjoint balls of a common radius around the points of a finite set, inside an open set. -/
theorem exists_disjoint_balls (S : Finset (ℝ × ℝ)) {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hSW : ∀ p ∈ S, p ∈ W) :
    ∃ r > 0, (∀ p ∈ S, Metric.ball p r ⊆ W) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint (Metric.ball p r) (Metric.ball q r) := by
  sorry

/-- Compactness: a continuous `Z < 1` on a compact set is `< 1 − δ` for some `δ > 0`. (PROVED) -/
theorem exists_delta_of_compact {G : ℝ × ℝ → E3} (hG : Continuous G) {N : E3}
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hZ : ∀ x ∈ K, ⟪G x, N⟫ < 1) :
    ∃ δ > 0, ∀ x ∈ K, ⟪G x, N⟫ < 1 - δ := by
  have hf : Continuous fun x => ⟪G x, N⟫ := hG.inner continuous_const
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, by simp [hKe]⟩
  obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hKne hf.continuousOn
  refine ⟨(1 - ⟪G x₀, N⟫) / 2, by linarith [hZ x₀ hx₀], fun x hx => ?_⟩
  have := hmax hx
  simp only [mem_ofPred_eq] at this
  linarith [hZ x₀ hx₀]

/-- For unit vectors, `⟪g, N⟫ < 1` unless `g = N`. (PROVED) -/
theorem inner_lt_one_of_ne {g N : E3} (hg : ‖g‖ = 1) (hN : ‖N‖ = 1) (h : g ≠ N) : ⟪g, N⟫ < 1 := by
  have h1 : ⟪g, N⟫ ≤ ‖g‖ * ‖N‖ := real_inner_le_norm g N
  rw [hg, hN, mul_one] at h1
  refine lt_of_le_of_ne h1 fun heq => h ?_
  have := (inner_eq_norm_mul_iff_real (x := g) (y := N)).mp (by rw [hg, hN, mul_one]; exact heq)
  rwa [hg, hN, one_smul, one_smul] at this

-- LEAF B9
/-- THE NEIGHBOURHOOD SYSTEM: from `exists_disjoint_balls` (inside the open box), `exists_regular_nhd`
(with `U = ball p r₀`), a common `r` (minimum over the finite `S`), and `exists_delta_of_compact` on
the compact `K = closed box ∖ ⋃ V p` where `G ≠ N` (`inner_lt_one_of_ne`). -/
theorem exists_nhdSystem {e₁ e₂ N : E3} (hN : cross e₁ e₂ = N) (hNu : ‖N‖ = 1)
    {G : ℝ × ℝ → E3} (hG : ContDiff ℝ ∞ G) (hn : ∀ y, ‖G y‖ = 1) {P a b : ℝ} (hP : 0 < P)
    (S : Finset (ℝ × ℝ))
    (hS : ∀ x ∈ Icc a (a + P) ×ˢ Icc b (b + P), G x = N ↔ x ∈ S)
    (hSint : ∀ x ∈ S, x ∈ Ioo a (a + P) ×ˢ Ioo b (b + P))
    (hreg : ∀ x ∈ S, Family.triple G eu2 ev2 x ≠ 0) :
    Nonempty (NhdSystem e₁ e₂ N G a b P S) := by
  sorry

end UB

/-! ## U-C. Change of variables on one neighbourhood; the polar normalisation -/
section UC

-- LEAF C1
/-- `φ'` vanishes strictly below the cap (`χ = 0` on a neighbourhood, `ContDiffBump.zero_of_le_dist`,
`Filter.EventuallyEq.deriv_eq`). -/
theorem deriv_bumpPhi_eq_zero_of_lt (χ : ContDiffBump (1 : ℝ)) {Z : ℝ} (hZ : Z < 1 - χ.rOut) :
    deriv (bumpPhi χ) Z = 0 := by
  have h : bumpPhi χ =ᶠ[𝓝 Z] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hZ] with z hz
    have hz' : z < 1 - χ.rOut := hz
    have hχ : χ z = 0 := by
      apply χ.zero_of_le_dist
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [χ.rOut_pos])]
      linarith
    simp [bumpPhi, hχ]
  rw [h.deriv_eq, deriv_const]

-- LEAF C2
/-- The chart density along the chart: `ψ(F x) = φ'(Z)/Z` when `Z > 0` (`frame_parseval` gives
`|F x|² = 1 − Z²`, so `√(1 − |F x|²) = Z`). -/
theorem chartDensity_chart {e₁ e₂ N : E3} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : ⟪e₁, e₂⟫ = 0)
    (hN : cross e₁ e₂ = N) (χ : ContDiffBump (1 : ℝ)) {G : ℝ × ℝ → E3} (hn : ∀ y, ‖G y‖ = 1)
    {x : ℝ × ℝ} (hx : 0 < ⟪G x, N⟫) :
    chartDensity χ (chart e₁ e₂ G x) = deriv (bumpPhi χ) ⟪G x, N⟫ / ⟪G x, N⟫ := by
  have hP := frame_parseval h₁ h₂ h₁₂ hN (G x)
  rw [hn x, one_pow] at hP
  have hs : (chart e₁ e₂ G x).1 ^ 2 + (chart e₁ e₂ G x).2 ^ 2 = 1 - ⟪G x, N⟫ ^ 2 := by
    simp only [chart, real_inner_comm (G x) e₁, real_inner_comm (G x) e₂]
    linarith
  have hlt : (chart e₁ e₂ G x).1 ^ 2 + (chart e₁ e₂ G x).2 ^ 2 < 1 := by
    rw [hs]; nlinarith
  have h1 : 1 - (1 - ⟪G x, N⟫ ^ 2) = ⟪G x, N⟫ ^ 2 := by ring
  rw [chartDensity, ite_eq_left hlt, hs, h1, Real.sqrt_sq hx.le]

-- LEAF C3
/-- Support of the chart density: `ψ(w) ≠ 0 → |w|² < 2·rOut`, so `w ∈ ball 0 r` once `2·rOut ≤ r²`
(`deriv_bumpPhi_eq_zero_of_lt`; the sup norm on `ℝ × ℝ` is `≤` the Euclidean one). -/
theorem chartDensity_mem_ball (χ : ContDiffBump (1 : ℝ)) {r : ℝ} (hr₀ : 0 < r)
    (hr : 2 * χ.rOut ≤ r ^ 2) {w : ℝ × ℝ} (hw : chartDensity χ w ≠ 0) :
    w ∈ Metric.ball (0 : ℝ × ℝ) r := by
  have hs1 : w.1 ^ 2 + w.2 ^ 2 < 1 := by
    by_contra h
    exact hw (by rw [chartDensity, ite_eq_right h])
  have hd : deriv (bumpPhi χ) (√(1 - (w.1 ^ 2 + w.2 ^ 2))) ≠ 0 := by
    intro h0
    exact hw (by rw [chartDensity, ite_eq_left hs1, h0, zero_div])
  have hge : 1 - χ.rOut ≤ √(1 - (w.1 ^ 2 + w.2 ^ 2)) := by
    by_contra h
    exact hd (deriv_bumpPhi_eq_zero_of_lt χ (not_le.mp h))
  have hsr : w.1 ^ 2 + w.2 ^ 2 < r ^ 2 := by
    rcases le_or_gt 0 (1 - χ.rOut) with h | h
    · have := (Real.le_sqrt h (by linarith)).mp hge
      nlinarith [χ.rOut_pos]
    · linarith
  have h1 : w.1 ^ 2 < r ^ 2 := by nlinarith [sq_nonneg w.2]
  have h2 : w.2 ^ 2 < r ^ 2 := by nlinarith [sq_nonneg w.1]
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
    max_lt_iff]
  exact ⟨abs_lt_of_sq_lt_sq h1 hr₀.le, abs_lt_of_sq_lt_sq h2 hr₀.le⟩

/-- `|t| = sign t · t` on `ℝ`. -/
theorem uc_abs_eq_sign_mul (t : ℝ) : |t| = Real.sign t * t := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [abs_of_neg h, Real.sign_of_neg h]; ring
  · rw [h, abs_zero, Real.sign_zero, mul_zero]
  · rw [abs_of_pos h, Real.sign_of_pos h]; ring

/-- `sign t · sign t = 1` for `t ≠ 0`. -/
theorem uc_sign_mul_sign {t : ℝ} (ht : t ≠ 0) : Real.sign t * Real.sign t = 1 := by
  rcases Real.sign_apply_eq_of_ne_zero t ht with h | h <;> rw [h] <;> norm_num

-- LEAF C4
/-- CHANGE OF VARIABLES on one neighbourhood: `∫_V D·φ'(Z) = sign(D p) · ∫_{ℝ²} ψ`
(`setIntegral_eq_integral_of_forall_compl_eq_zero` to shrink `ℝ²` to `chart '' V`,
`integral_image_eq_integral_abs_det_fderiv_smul` with `hasFDerivAt_chart`, `det_chartDeriv`,
`chartDensity_chart`; `|D·Z| · φ'(Z)/Z = sign(D p) · D · φ'(Z)` as `Z > 0`, `sign D = sign D p`). -/
theorem integral_bump_on_nhd (χ : ContDiffBump (1 : ℝ)) {e₁ e₂ N : E3} (h₁ : ‖e₁‖ = 1)
    (h₂ : ‖e₂‖ = 1) (h₁₂ : ⟪e₁, e₂⟫ = 0) (hN : cross e₁ e₂ = N) {G : ℝ × ℝ → E3}
    (hG : ContDiff ℝ ∞ G) (hn : ∀ y, ‖G y‖ = 1) {p : ℝ × ℝ} (hD : Family.triple G eu2 ev2 p ≠ 0)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V) (hinj : InjOn (chart e₁ e₂ G) V)
    (hZ : ∀ x ∈ V, 0 < ⟪G x, N⟫)
    (hsgn : ∀ x ∈ V, Real.sign (Family.triple G eu2 ev2 x) = Real.sign (Family.triple G eu2 ev2 p))
    {r : ℝ} (hr : Metric.ball (0 : ℝ × ℝ) r ⊆ chart e₁ e₂ G '' V)
    (hsupp : ∀ w : ℝ × ℝ, chartDensity χ w ≠ 0 → w ∈ Metric.ball (0 : ℝ × ℝ) r) :
    ∫ x in V, Family.triple G eu2 ev2 x * deriv (bumpPhi χ) ⟪G x, N⟫
      = Real.sign (Family.triple G eu2 ev2 p) * ∫ w, chartDensity χ w := by
  -- shrink `ℝ²` to the chart image
  have h1 : ∫ w, chartDensity χ w = ∫ w in chart e₁ e₂ G '' V, chartDensity χ w := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    by_contra hne
    exact hw (hr (hsupp w hne))
  -- change of variables through the chart
  have h2 : ∫ w in chart e₁ e₂ G '' V, chartDensity χ w
      = ∫ x in V, |(chartDeriv e₁ e₂ G x).det| • chartDensity χ (chart e₁ e₂ G x) :=
    integral_image_eq_integral_abs_det_fderiv_smul volume hV.measurableSet
      (fun x _ => (hasFDerivAt_chart e₁ e₂ hG x).hasFDerivWithinAt) hinj (chartDensity χ)
  -- the pointwise identity on `V`
  have h3 : EqOn (fun x => |(chartDeriv e₁ e₂ G x).det| • chartDensity χ (chart e₁ e₂ G x))
      (fun x => Real.sign (Family.triple G eu2 ev2 p) *
        (Family.triple G eu2 ev2 x * deriv (bumpPhi χ) ⟪G x, N⟫)) V := by
    intro x hx
    have hZx := hZ x hx
    simp only
    rw [det_chartDeriv hN hG hn x, chartDensity_chart h₁ h₂ h₁₂ hN χ hn hZx, smul_eq_mul,
      abs_mul, abs_of_pos hZx, ← hsgn x hx, uc_abs_eq_sign_mul]
    field_simp
  rw [h1, h2, setIntegral_congr_fun hV.measurableSet h3, integral_const_mul, ← mul_assoc,
    uc_sign_mul_sign hD, one_mul]


/-- Rotational invariance of `chartDensity`: it depends on `w` only through `w.1² + w.2²`. -/
theorem uc_chartDensity_polar (χ : ContDiffBump (1 : ℝ)) (ρ θ : ℝ) :
    chartDensity χ (ρ * cos θ, ρ * sin θ) = chartDensity χ (ρ, 0) := by
  have h : (ρ * cos θ) ^ 2 + (ρ * sin θ) ^ 2 = ρ ^ 2 + 0 ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, cos_sq_add_sin_sq]; ring
  simp only [chartDensity]
  rw [h]

-- LEAF C5
/-- Radial reduction of the plane integral (`integral_comp_polarCoord_symm`, `polarCoord_target`,
Fubini on `Ioi 0 ×ˢ Ioo (−π) π`; `ψ` depends only on `|w|²`; `rOut < 1` keeps `ψ` bounded). -/
theorem integral_chartDensity_eq_radial (χ : ContDiffBump (1 : ℝ)) (hχ : χ.rOut < 1) :
    ∫ w : ℝ × ℝ, chartDensity χ w = (2 * π) * ∫ ρ in Ioi (0:ℝ), ρ * chartDensity χ (ρ, 0) := by
  -- `hχ` is not needed: `setIntegral_prod_mul` needs no integrability, so no bound on `ψ` is used.
  have _ := hχ
  rw [← integral_comp_polarCoord_symm (chartDensity χ), polarCoord_target]
  have h : ∀ p : ℝ × ℝ, p.1 • chartDensity χ (polarCoord.symm p)
      = (fun ρ => ρ * chartDensity χ (ρ, 0)) p.1 * (fun _ : ℝ => (1 : ℝ)) p.2 := by
    intro p
    simp only [polarCoord_symm_apply, uc_chartDensity_polar, smul_eq_mul, mul_one]
  have hprod := setIntegral_prod_mul (μ := volume) (ν := volume)
    (fun ρ : ℝ => ρ * chartDensity χ (ρ, 0)) (fun _ : ℝ => (1 : ℝ)) (Ioi 0) (Ioo (-π) π)
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p _ => h p),
    Measure.volume_eq_prod, hprod, setIntegral_const, measureReal_def,
    Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), smul_eq_mul, mul_one,
    sub_neg_eq_add, two_mul, mul_comm]

/-- `bumpPhi χ` is smooth. -/
theorem uc_contDiff_bumpPhi (χ : ContDiffBump (1 : ℝ)) : ContDiff ℝ ∞ (bumpPhi χ) := by
  show ContDiff ℝ ∞ fun z => (1 + z) * χ z / (4 * π)
  exact ((contDiff_const.add contDiff_id).mul χ.contDiff).div_const _

/-- `bumpPhi χ` has derivative `deriv (bumpPhi χ)` everywhere. -/
theorem uc_hasDerivAt_bumpPhi (χ : ContDiffBump (1 : ℝ)) (z : ℝ) :
    HasDerivAt (bumpPhi χ) (deriv (bumpPhi χ) z) z :=
  ((uc_contDiff_bumpPhi χ).differentiable (by simp) z).hasDerivAt

/-- The radial primitive `ρ ↦ −φ(√(1 − ρ²))` has derivative `ρ φ'(√(1−ρ²))/√(1−ρ²)` for `ρ² < 1`. -/
theorem uc_hasDerivAt_radial (χ : ContDiffBump (1 : ℝ)) {ρ : ℝ} (hρ : ρ ^ 2 < 1) :
    HasDerivAt (fun ρ => -bumpPhi χ (√(1 - ρ ^ 2)))
      (ρ * (deriv (bumpPhi χ) (√(1 - ρ ^ 2)) / √(1 - ρ ^ 2))) ρ := by
  have hpos : 0 < 1 - ρ ^ 2 := by linarith
  have hsq : √(1 - ρ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have h1 : HasDerivAt (fun ρ : ℝ => 1 - ρ ^ 2) (-(2 * ρ)) ρ := by
    have := (hasDerivAt_pow 2 ρ).const_sub 1
    simpa using this
  have h2 : HasDerivAt (fun ρ : ℝ => √(1 - ρ ^ 2)) (-(2 * ρ) / (2 * √(1 - ρ ^ 2))) ρ :=
    h1.sqrt hpos.ne'
  have h3 := ((uc_hasDerivAt_bumpPhi χ (√(1 - ρ ^ 2))).comp ρ h2).neg
  refine h3.congr_deriv ?_
  field_simp

-- LEAF C6
/-- The radial integral: `∫_0^∞ ρ φ'(√(1−ρ²))/√(1−ρ²) dρ = φ(1) − 0 = 1/(2π)`.  The integrand is
`−d/dρ φ(√(1−ρ²))` on `[0, ρ₁]`, `ρ₁ = √(1 − (1−rOut)²) < 1`, and vanishes for `ρ > ρ₁`
(`deriv_bumpPhi_eq_zero_of_lt`) and for `ρ ≥ 1` (definition).  FTC:
`intervalIntegral.integral_eq_sub_of_hasDerivAt`, `Real.hasDerivAt_sqrt`; `φ(1) = 2χ(1)/(4π)`,
`χ 1 = 1` (`ContDiffBump.one_of_mem_closedBall`), `φ(1 − rOut) = 0` (`zero_of_le_dist`). -/
theorem integral_radial (χ : ContDiffBump (1 : ℝ)) (hχ : χ.rOut < 1) :
    ∫ ρ in Ioi (0:ℝ), ρ * chartDensity χ (ρ, 0) = 1 / (2 * π) := by
  have hr0 : 0 < 1 - χ.rOut := by linarith
  have hr1 : (1 - χ.rOut) ^ 2 < 1 := by nlinarith [χ.rOut_pos]
  set ρ₁ := √(1 - (1 - χ.rOut) ^ 2) with hρ₁
  have hρ₁sq : ρ₁ ^ 2 = 1 - (1 - χ.rOut) ^ 2 := Real.sq_sqrt (by linarith)
  have hρ₁pos : 0 < ρ₁ := Real.sqrt_pos.mpr (by linarith)
  have hρ₁lt : ρ₁ ^ 2 < 1 := by rw [hρ₁sq]; nlinarith
  -- the integrand vanishes for `ρ > ρ₁`
  have hzero : ∀ ρ ∈ Ioi (0:ℝ) \ Ioc 0 ρ₁, ρ * chartDensity χ (ρ, 0) = 0 := by
    rintro ρ ⟨hρ, hρ'⟩
    have hρ₁ρ : ρ₁ < ρ := by
      simp only [mem_Ioc, not_and, not_le] at hρ'
      exact hρ' hρ
    have hρ0 : (0:ℝ) < ρ := hρ
    simp only [chartDensity]
    split_ifs with h
    · have h1 : √(1 - (ρ ^ 2 + 0 ^ 2)) < 1 - χ.rOut := by
        rw [Real.sqrt_lt' hr0]
        nlinarith [mul_pos (sub_pos.mpr hρ₁ρ) (add_pos hρ0 hρ₁pos)]
      rw [deriv_bumpPhi_eq_zero_of_lt χ h1, zero_div, mul_zero]
    · simp
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self hzero,
    ← intervalIntegral.integral_of_le hρ₁pos.le]
  -- on `[0, ρ₁]` the integrand is `ρ φ'(√(1−ρ²))/√(1−ρ²)`
  have hsq : ∀ ρ ∈ uIcc (0:ℝ) ρ₁, ρ ^ 2 < 1 := by
    intro ρ hρ
    rw [uIcc_of_le hρ₁pos.le, mem_Icc] at hρ
    nlinarith
  have heq : EqOn (fun ρ => ρ * chartDensity χ (ρ, 0))
      (fun ρ => ρ * (deriv (bumpPhi χ) (√(1 - ρ ^ 2)) / √(1 - ρ ^ 2))) (uIcc 0 ρ₁) := by
    intro ρ hρ
    have := hsq ρ hρ
    simp only [chartDensity, zero_pow two_ne_zero, add_zero]
    rw [ite_eq_left this]
  rw [intervalIntegral.integral_congr heq]
  -- FTC
  have hcont : ContinuousOn (fun ρ => ρ * (deriv (bumpPhi χ) (√(1 - ρ ^ 2)) / √(1 - ρ ^ 2)))
      (uIcc 0 ρ₁) := by
    have hnum : Continuous fun ρ : ℝ => deriv (bumpPhi χ) (√(1 - ρ ^ 2)) :=
      ((uc_contDiff_bumpPhi χ).continuous_deriv (by simp)).comp
        (Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2)))
    have hden : Continuous fun ρ : ℝ => √(1 - ρ ^ 2) :=
      Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))
    refine continuousOn_id.mul (hnum.continuousOn.div hden.continuousOn ?_)
    intro ρ hρ
    exact (Real.sqrt_pos.mpr (by linarith [hsq ρ hρ])).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun ρ hρ => uc_hasDerivAt_radial χ (hsq ρ hρ)) hcont.intervalIntegrable]
  -- the boundary values
  have hχ1 : χ 1 = 1 := χ.one_of_mem_closedBall (Metric.mem_closedBall_self χ.rIn_pos.le)
  have hχr : χ (1 - χ.rOut) = 0 := by
    apply χ.zero_of_le_dist
    rw [Real.dist_eq, show 1 - χ.rOut - 1 = -χ.rOut by ring, abs_neg, abs_of_pos χ.rOut_pos]
  have hv1 : √(1 - ρ₁ ^ 2) = 1 - χ.rOut := by
    rw [hρ₁sq, sub_sub_cancel, Real.sqrt_sq hr0.le]
  simp only [hv1, zero_pow two_ne_zero, sub_zero, Real.sqrt_one, bumpPhi, hχ1, hχr]
  have := Real.pi_pos
  field_simp
  ring

/-- NORMALISATION: `∫_{ℝ²} ψ = 1`. (PROVED from C5, C6) -/
theorem integral_chartDensity (χ : ContDiffBump (1 : ℝ)) (hχ : χ.rOut < 1) :
    ∫ w : ℝ × ℝ, chartDensity χ w = 1 := by
  rw [integral_chartDensity_eq_radial χ hχ, integral_radial χ hχ]
  have := Real.pi_pos
  field_simp

end UC

/-! ## U-D. Assembly -/
section UD

-- LEAF D1
/-- Iterated interval integral = set integral over the closed box, for a continuous integrand
(`intervalIntegral.integral_of_le`, `setIntegral_congr_set Ioc_ae_eq_Icc`, `setIntegral_prod`;
pattern of `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:530-540`). -/
theorem integral_box_eq_setIntegral {f : ℝ × ℝ → ℝ} (hf : Continuous f) {a a' b b' : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') :
    ∫ u in a..a', ∫ v in b..b', f (u, v) = ∫ x in Icc a a' ×ˢ Icc b b', f x := by
  sorry

-- LEAF D2
/-- Localisation to a finite disjoint family of open subsets on which the integrand lives
(`setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`, `integral_biUnion_finset`,
`Continuous.integrableOn_Icc`-type integrability). -/
theorem setIntegral_box_eq_sum {f : ℝ × ℝ → ℝ} (hf : Continuous f) {a a' b b' : ℝ}
    (S : Finset (ℝ × ℝ)) (V : ℝ × ℝ → Set (ℝ × ℝ)) (hVo : ∀ p ∈ S, IsOpen (V p))
    (hVsub : ∀ p ∈ S, V p ⊆ Icc a a' ×ˢ Icc b b')
    (hdisj : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint (V p) (V q))
    (hzero : ∀ x ∈ Icc a a' ×ˢ Icc b b', x ∉ ⋃ p ∈ S, V p → f x = 0) :
    ∫ x in Icc a a' ×ˢ Icc b b', f x = ∑ p ∈ S, ∫ x in V p, f x := by
  sorry

-- LEAF D3
/-- MAIN LEMMA on the box, given a neighbourhood system and a bump with `rOut < 1`, `rOut ≤ δ`,
`2·rOut ≤ r²`: `∫∫ D · φ'(Z) = ∑_{p ∈ S} sign(D p)`.  Steps: `integral_box_eq_setIntegral`;
`setIntegral_box_eq_sum` with `V = sys.V` (the integrand vanishes off `⋃ V p` by `sys.small` and
`deriv_bumpPhi_eq_zero_of_lt`); per `p`: `integral_bump_on_nhd` (support via `chartDensity_mem_ball`)
and `integral_chartDensity`. -/
theorem integral_bump_eq_sum_of_system {e₁ e₂ N : E3} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : ⟪e₁, e₂⟫ = 0) (hN : cross e₁ e₂ = N) {G : ℝ × ℝ → E3} (hG : ContDiff ℝ ∞ G)
    (hn : ∀ y, ‖G y‖ = 1) {P a b : ℝ} (hP : 0 < P) {S : Finset (ℝ × ℝ)}
    (hreg : ∀ x ∈ S, Family.triple G eu2 ev2 x ≠ 0)
    (sys : NhdSystem e₁ e₂ N G a b P S) (χ : ContDiffBump (1 : ℝ)) (hχ₁ : χ.rOut < 1)
    (hχδ : χ.rOut ≤ sys.δ) (hχr : 2 * χ.rOut ≤ sys.r ^ 2) :
    ∫ u in a..a + P, ∫ v in b..b + P,
        Family.triple G eu2 ev2 (u, v) * deriv (bumpPhi χ) ⟪G (u, v), N⟫
      = ∑ p ∈ S, Real.sign (Family.triple G eu2 ev2 p) := by
  sorry

-- LEAF D4
/-- SHIFT of the fundamental domain: choose `a, b ∈ (0,P)` avoiding the finitely many coordinates of
the preimages; then no preimage lies on the boundary of `[a,a+P]×[b,b+P]`, the preimages in the closed
box are exactly `S = τ '' hfin.toFinset` with `τ p = p + (P·[p.1 < a], P·[p.2 < b])`, and the signed
sums agree (`Finset.sum_image`, `gaussDensity_periodic`). -/
theorem exists_shift {G : ℝ → ℝ → E3} {N : E3} {P : ℝ} (hP : 0 < P)
    (hpu : ∀ v, Periodic (fun u => G u v) P) (hpv : ∀ u, Periodic (G u) P)
    (hfin : {p : ℝ × ℝ | p ∈ Ico (0:ℝ) P ×ˢ Ico (0:ℝ) P ∧ G p.1 p.2 = N}.Finite) :
    ∃ a b : ℝ, ∃ S : Finset (ℝ × ℝ),
      (∀ x ∈ Icc a (a + P) ×ˢ Icc b (b + P), uncurry G x = N ↔ x ∈ S) ∧
      (∀ x ∈ S, x ∈ Ioo a (a + P) ×ˢ Ioo b (b + P)) ∧
      ∑ x ∈ S, Real.sign (gaussDensity G x.1 x.2)
        = ∑ p ∈ hfin.toFinset, Real.sign (gaussDensity G p.1 p.2) := by
  sorry

end UD

end RPC

open RPC in
/-- **fd:regular-pole-count** (sm-3:2894-2897): the degree formula for a regular value, proved from
the leaves along the bump-primitive route. -/
theorem regularPoleCount : RegularPoleCount := by
  intro P G N hP hG hpu hpv hn hNu hreg hfin
  obtain ⟨a, b, S, hS, hSint, hsum⟩ := exists_shift hP hpu hpv hfin
  obtain ⟨e₁, e₂, h₁, h₂, h₁₂, hN⟩ := exists_frame hNu
  have hn' : ∀ y, ‖uncurry G y‖ = 1 := fun y => hn y.1 y.2
  have htriple : ∀ x : ℝ × ℝ, gaussDensity G x.1 x.2 = Family.triple (uncurry G) eu2 ev2 x := by
    intro x; exact gaussDensity_eq_triple' hG x.1 x.2
  have hreg' : ∀ x ∈ S, Family.triple (uncurry G) eu2 ev2 x ≠ 0 := by
    intro x hx
    have hxbox : x ∈ Icc a (a + P) ×ˢ Icc b (b + P) := by
      obtain ⟨hx1, hx2⟩ := hSint x hx
      exact ⟨Ioo_subset_Icc_self hx1, Ioo_subset_Icc_self hx2⟩
    have hGx : G x.1 x.2 = N := (hS x hxbox).mpr hx
    rw [← htriple x]
    exact hreg x.1 x.2 hGx
  obtain ⟨sys⟩ := exists_nhdSystem hN hNu hG hn' hP S hS hSint hreg'
  -- the bump: `rOut = ε ≤ min δ (r²/2) (1/2)`
  set ε : ℝ := min (min sys.δ (sys.r ^ 2 / 2)) (1 / 2) with hε_def
  have hε : 0 < ε := by
    have hδ := sys.δ_pos; have hr := sys.r_pos
    exact lt_min (lt_min hδ (by positivity)) (by norm_num)
  have hεδ : ε ≤ sys.δ := (min_le_left _ _).trans (min_le_left _ _)
  have hεr : ε ≤ sys.r ^ 2 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  let χ : ContDiffBump (1 : ℝ) := ⟨ε / 2, ε, by positivity, by linarith⟩
  rw [gaussIntegral_eq_integral_bump χ hNu hG hn hpu hpv a b, ← hsum]
  have hmain := integral_bump_eq_sum_of_system h₁ h₂ h₁₂ hN hG hn' hP hreg' sys χ
    (by show ε < 1; linarith) (by show ε ≤ sys.δ; exact hεδ)
    (by show 2 * ε ≤ sys.r ^ 2; linarith)
  refine hmain.trans (Finset.sum_congr rfl fun x _ => ?_)
  rw [htriple x]

/-- COROLLARY: the crossing formula sm-3:2802-2804 with the isolated hypothesis discharged. -/
theorem crossing_formula_unconditional {P : ℝ} {C₁ C₂ : ℝ → E3} {ν : E3}
    (h : DisjointPair P C₁ C₂) (hν : GenericDirection C₁ C₂ ν) :
    linking P C₁ C₂ = (1 / 2) * ∑ᶠ p ∈ mixedCrossings P C₁ C₂ ν, lcCrossingSign C₁ C₂ ν p :=
  crossing_formula_of_regularPoleCount regularPoleCount h hν

end

end SM
