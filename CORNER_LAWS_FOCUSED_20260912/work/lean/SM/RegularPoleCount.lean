-- Ported 10:15Z 2026-09-14 from work/drafts/fd/RPC_Assembled.lean (RegularPoleCount lane: probe skeleton + units A/B/C/D + assembler) by the pod executor; body verbatim.
/-
RPC_Assembled.lean — `SM.regularPoleCount : RegularPoleCount` (fd:regular-pole-count, sm-3:2894-2897),
the isolated hypothesis of row 88 fd:linking-calculus, completely proved, together with the corollary
`SM.crossing_formula_unconditional` (the crossing formula sm-3:2802-2804 with that hypothesis
discharged).  Assembled 2026-09-14 from `RPC_Skeleton.lean` (feasibility probe:
work/drafts/fd/REGULAR_POLE_COUNT_FEASIBILITY.md; plan: work/drafts/fd/RPC_PLAN.md) and the four unit
files `RPC_U_{A,B,C,D}.lean`; the assembly is documented in work/drafts/fd/RPC_ASSEMBLY_REPORT.md.

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

STRUCTURE.  Namespace `SM.RPC` holds the shared definitions (`oneForm`, `mk`, `cutoffK`, `bumpPhi`,
`chart`, `chartDeriv`, `chartDensity`, `NhdSystem`) and four sections:
* U-A algebra and exactness (`cross_fderiv_eq_smul` … `gaussIntegral_eq_integral_bump`);
* U-B frame, chart Jacobian, inverse-function neighbourhoods (`exists_frame` … `exists_nhdSystem`);
* U-C change of variables on one neighbourhood and the polar normalisation
  (`deriv_bumpPhi_eq_zero_of_lt` … `integral_chartDensity`);
* U-D assembly on the period box and the shift of the fundamental domain
  (`integral_box_eq_setIntegral` … `exists_shift`).
The `-- LEAF <unit><n>` markers and the `(PROVED)` tags are inherited from the skeleton: the 29 marked
declarations were the units' proof obligations, and each is now proved with its skeleton statement
unchanged; the helper lemmas added by the units carry the prefixes `ua_`, `ub_`, `uc_`, `ud_`.
Every declaration of this file depends only on `propext`, `Classical.choice`, `Quot.sound`.
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
  set c := cross (fderiv ℝ G x a) (fderiv ℝ G x b) with hc
  have ha : ⟪G x, fderiv ℝ G x a⟫ = 0 := Family.inner_fderiv_eq_zero hG hn x a
  have hb : ⟪G x, fderiv ℝ G x b⟫ = 0 := Family.inner_fderiv_eq_zero hG hn x b
  have hgg : ⟪G x, G x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn x]; norm_num
  have h1 : cross (G x) c = 0 := by
    rw [hc, cross_cross_eq, hb, ha, zero_smul, zero_smul, sub_zero]
  have h2 : cross (G x) (cross (G x) c) = ⟪G x, c⟫ • G x - ⟪G x, G x⟫ • c := cross_cross_eq _ _ _
  rw [h1, cross_zero_right, hgg, one_smul, eq_comm, sub_eq_zero] at h2
  exact h2.symm

-- LEAF A2
/-- Derivative of the 1-form coefficient (analogue of `Family.fderiv_triple_apply`). -/
theorem fderiv_oneForm_apply {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (N : E3) {G : ℝ × ℝ → E3}
    (hG : ContDiff ℝ ∞ G) (x w c : ℝ × ℝ) :
    fderiv ℝ (fun y => oneForm k N G y w) x c
      = deriv k ⟪G x, N⟫ * ⟪fderiv ℝ G x c, N⟫ * ⟪cross N (G x), fderiv ℝ G x w⟫
        + k ⟪G x, N⟫ * (⟪cross N (fderiv ℝ G x c), fderiv ℝ G x w⟫
            + ⟪cross N (G x), fderiv ℝ (fderiv ℝ G) x c w⟫) := by
  have hG1 : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by simp) x).hasFDerivAt
  have hZ : HasFDerivAt (fun y => ⟪G y, N⟫)
      ((fderivInnerCLM ℝ (G x, N)).comp ((fderiv ℝ G x).prod (0 : ℝ × ℝ →L[ℝ] E3))) x :=
    hG1.inner ℝ (hasFDerivAt_const N x)
  have hk1 : HasDerivAt k (deriv k ⟪G x, N⟫) ⟪G x, N⟫ :=
    ((hk.differentiable (by simp)) _).hasDerivAt
  have hkZ : HasFDerivAt (fun y => k ⟪G y, N⟫) _ x := hk1.comp_hasFDerivAt x hZ
  have hw := Family.hasFDerivAt_fderiv_apply hG x w
  have hcr : HasFDerivAt (fun y => cross N (G y)) _ x := (hasFDerivAt_const N x).cross hG1
  have hin := hcr.inner ℝ hw
  have h := hkZ.mul hin
  have h' : HasFDerivAt (fun y => oneForm k N G y w) _ x := h
  rw [h'.fderiv]
  simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply,
    add_apply, ContinuousLinearMap.flip_apply, crossL_apply, zero_apply, smul_apply, smul_eq_mul,
    map_zero, inner_zero_right, zero_add, add_zero]
  ring

-- LEAF A3
/-- Smoothness of the 1-form coefficient. -/
theorem contDiff_oneForm {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (N : E3) {G : ℝ × ℝ → E3}
    (hG : ContDiff ℝ ∞ G) (w : ℝ × ℝ) : ContDiff ℝ ∞ (fun y => oneForm k N G y w) := by
  have h1 : ContDiff ℝ ∞ (fun y => k ⟪G y, N⟫) := hk.comp (hG.inner ℝ contDiff_const)
  have h2 : ContDiff ℝ ∞ (fun y => ⟪cross N (G y), fderiv ℝ G y w⟫) :=
    (contDiff_const.cross hG).inner ℝ (Family.contDiff_fderiv_apply hG w)
  exact h1.mul h2

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
  rw [fderiv_oneForm_apply hk N hG x ev2 eu2, fderiv_oneForm_apply hk N hG x eu2 ev2,
    Family.fderiv_fderiv_symm hG x eu2 ev2]
  have hcore := core_algebra (G x) (fderiv ℝ G x eu2) (fderiv ℝ G x ev2) N (k ⟪G x, N⟫)
    (deriv k ⟪G x, N⟫) (Family.triple G eu2 ev2 x) (hn x) hN (cross_fderiv_eq_smul hG hn x eu2 ev2)
  rw [mk]
  linear_combination hcore

/-- Fubini for a continuous integrand on a rectangle, for arbitrary (possibly reversed) bounds:
the four sign cases of `integral_integral_swap_of_continuous`. -/
theorem ua_integral_integral_swap {f : ℝ → ℝ → ℝ} (hf : Continuous (uncurry f)) (a b c d : ℝ) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
  · exact integral_integral_swap_of_continuous hf hab hcd
  · have h := integral_integral_swap_of_continuous hf hab hcd
    simp only [intervalIntegral.integral_symm d c, intervalIntegral.integral_neg, h]
  · have h := integral_integral_swap_of_continuous hf hab hcd
    simp only [intervalIntegral.integral_symm b a, intervalIntegral.integral_neg, h]
  · have h := integral_integral_swap_of_continuous hf hab hcd
    simp only [intervalIntegral.integral_symm b a, intervalIntegral.integral_symm d c,
      intervalIntegral.integral_neg, h, neg_neg]

-- LEAF A5
/-- Green on the period box, `u`-direction: `∫∫ ∂_u F = 0` (swap, FTC per slice, periodicity);
two-variable copy of `Family.integral_fderiv1_eq_zero`. -/
theorem integral_fderiv_eu_eq_zero {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {P : ℝ}
    (hper : Periodic F (P, 0)) (a b : ℝ) :
    ∫ u in a..a + P, ∫ v in b..b + P, fderiv ℝ F (u, v) eu2 = 0 := by
  have hc : Continuous fun x => fderiv ℝ F x eu2 := (Family.contDiff_fderiv_apply hF eu2).continuous
  have hc' : Continuous (uncurry fun u v => fderiv ℝ F (u, v) eu2) :=
    hc.comp (continuous_fst.prodMk continuous_snd)
  rw [ua_integral_integral_swap hc' a (a + P) b (b + P)]
  have h3 : ∀ v, ∫ u in a..a + P, fderiv ℝ F (u, v) eu2 = 0 := by
    intro v
    have hftc : ∫ u in a..a + P, fderiv ℝ F (u, v) eu2 = F (a + P, v) - F (a, v) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => F (u, v)) ?_ ?_
      · intro u _; exact hasDerivAt_sliceU (hF.differentiable (by simp) _)
      · exact (hc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    rw [hftc]
    have := hper (a, v)
    simp only [Prod.mk_add_mk, add_zero] at this
    rw [this, sub_self]
  simp only [h3, intervalIntegral.integral_zero]

-- LEAF A6
/-- Green on the period box, `v`-direction (FTC on the inner integral, periodicity). -/
theorem integral_fderiv_ev_eq_zero {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {P : ℝ}
    (hper : Periodic F (0, P)) (a b : ℝ) :
    ∫ u in a..a + P, ∫ v in b..b + P, fderiv ℝ F (u, v) ev2 = 0 := by
  have hc : Continuous fun x => fderiv ℝ F x ev2 := (Family.contDiff_fderiv_apply hF ev2).continuous
  have h3 : ∀ u, ∫ v in b..b + P, fderiv ℝ F (u, v) ev2 = 0 := by
    intro u
    have hftc : ∫ v in b..b + P, fderiv ℝ F (u, v) ev2 = F (u, b + P) - F (u, b) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun v => F (u, v)) ?_ ?_
      · intro v _; exact hasDerivAt_sliceV (hF.differentiable (by simp) _)
      · exact (hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    rw [hftc]
    have := hper (u, b)
    simp only [Prod.mk_add_mk, add_zero] at this
    rw [this, sub_self]
  simp only [h3, intervalIntegral.integral_zero]

-- LEAF A7
/-- EXACTNESS: `∫∫ D · m_k(Z) = 0` on any period box, for every smooth `k`. -/
theorem integral_triple_mul_mk_eq_zero {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) {N : E3} (hN : ‖N‖ = 1)
    {G : ℝ × ℝ → E3} (hG : ContDiff ℝ ∞ G) (hn : ∀ y, ‖G y‖ = 1) {P : ℝ}
    (hpu : Periodic G (P, 0)) (hpv : Periodic G (0, P)) (a b : ℝ) :
    ∫ u in a..a + P, ∫ v in b..b + P,
      Family.triple G eu2 ev2 (u, v) * mk k ⟪G (u, v), N⟫ = 0 := by
  set B : ℝ × ℝ → ℝ := fun x => fderiv ℝ (fun y => oneForm k N G y ev2) x eu2 with hBdef
  set A : ℝ × ℝ → ℝ := fun x => fderiv ℝ (fun y => oneForm k N G y eu2) x ev2 with hAdef
  have hB : Continuous B := (Family.contDiff_fderiv_apply (contDiff_oneForm hk N hG ev2) eu2).continuous
  have hA : Continuous A := (Family.contDiff_fderiv_apply (contDiff_oneForm hk N hG eu2) ev2).continuous
  have hBu : ∀ u, IntervalIntegrable (fun v => B (u, v)) volume b (b + P) := fun u =>
    (hB.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hAu : ∀ u, IntervalIntegrable (fun v => A (u, v)) volume b (b + P) := fun u =>
    (hA.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hBo : IntervalIntegrable (fun u => ∫ v in b..b + P, B (u, v)) volume a (a + P) :=
    (continuous_parametric_integral (f := fun u v => B (u, v))
      (hB.comp (continuous_fst.prodMk continuous_snd)) b (b + P)).intervalIntegrable _ _
  have hAo : IntervalIntegrable (fun u => ∫ v in b..b + P, A (u, v)) volume a (a + P) :=
    (continuous_parametric_integral (f := fun u v => A (u, v))
      (hA.comp (continuous_fst.prodMk continuous_snd)) b (b + P)).intervalIntegrable _ _
  have h1 : ∀ u v, Family.triple G eu2 ev2 (u, v) * mk k ⟪G (u, v), N⟫ = B (u, v) - A (u, v) :=
    fun u v => (fderiv_oneForm_antisymm hk hN hG hn (u, v)).symm
  calc ∫ u in a..a + P, ∫ v in b..b + P, Family.triple G eu2 ev2 (u, v) * mk k ⟪G (u, v), N⟫
      = ∫ u in a..a + P, ∫ v in b..b + P, (B (u, v) - A (u, v)) := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        exact intervalIntegral.integral_congr fun v _ => h1 u v
    _ = ∫ u in a..a + P, ((∫ v in b..b + P, B (u, v)) - ∫ v in b..b + P, A (u, v)) :=
        intervalIntegral.integral_congr fun u _ => intervalIntegral.integral_sub (hBu u) (hAu u)
    _ = (∫ u in a..a + P, ∫ v in b..b + P, B (u, v)) - ∫ u in a..a + P, ∫ v in b..b + P, A (u, v) :=
        intervalIntegral.integral_sub hBo hAo
    _ = 0 := by
        rw [hBdef, hAdef,
          integral_fderiv_eu_eq_zero (contDiff_oneForm hk N hG ev2) (periodic_oneForm k N hpu ev2) a b,
          integral_fderiv_ev_eq_zero (contDiff_oneForm hk N hG eu2) (periodic_oneForm k N hpv eu2) a b,
          sub_zero]

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
  rw [contDiff_iff_contDiffAt]
  intro Z
  by_cases hZ : Z = 1
  · subst hZ
    have hev : cutoffK χ =ᶠ[𝓝 (1 : ℝ)] fun _ => (0 : ℝ) := by
      filter_upwards [χ.eventuallyEq_one] with z hz
      simp only [cutoffK, hz, Pi.one_apply, sub_self, zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hden : 4 * π * (1 - Z) ≠ 0 :=
      mul_ne_zero (by positivity) (sub_ne_zero.mpr (Ne.symm hZ))
    have h1 : ContDiffAt ℝ ∞ (fun z => χ z - 1) Z := (χ.contDiff.sub contDiff_const).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun z : ℝ => 4 * π * (1 - z)) Z :=
      (contDiff_const.mul (contDiff_const.sub contDiff_id)).contDiffAt
    exact h1.div h2 hden

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
  have hχ1 : χ 1 = 1 := χ.one_of_mem_closedBall (Metric.mem_closedBall_self χ.rIn_pos.le)
  have hd : deriv (fun z => χ z) 1 = 0 := by
    have hev : (fun z => χ z) =ᶠ[𝓝 (1 : ℝ)] fun _ => (1 : ℝ) := χ.eventuallyEq_one
    rw [hev.deriv_eq, deriv_const]
  have hk1 : cutoffK χ 1 = 0 := by simp [cutoffK, hχ1]
  rw [mk, deriv_bumpPhi, hk1, hd, hχ1]
  ring

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
  unfold gaussIntegral
  congr 1
  have hin : ∀ u, ∫ v in (0:ℝ)..P, gaussDensity G u v = ∫ v in b..b + P, gaussDensity G u v := by
    intro u
    have hp : Periodic (fun v => gaussDensity G u v) P :=
      fun v => (gaussDensity_periodic hpu hpv u v).2
    have := hp.intervalIntegral_add_eq 0 b
    rwa [zero_add] at this
  have hout : Periodic (fun u => ∫ v in b..b + P, gaussDensity G u v) P := by
    intro u
    exact intervalIntegral.integral_congr fun v _ => (gaussDensity_periodic hpu hpv u v).1
  calc ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, gaussDensity G u v
      = ∫ u in (0:ℝ)..P, ∫ v in b..b + P, gaussDensity G u v :=
        intervalIntegral.integral_congr fun u _ => hin u
    _ = ∫ u in a..a + P, ∫ v in b..b + P, gaussDensity G u v := by
        have := hout.intervalIntegral_add_eq 0 a
        rwa [zero_add] at this
    _ = ∫ u in a..a + P, ∫ v in b..b + P, Family.triple (uncurry G) eu2 ev2 (u, v) := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        exact intervalIntegral.integral_congr fun v _ => gaussDensity_eq_triple' hG u v

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
  have hn' : ∀ y, ‖uncurry G y‖ = 1 := fun y => hn y.1 y.2
  have hpu' : Periodic (uncurry G) (P, 0) := by
    intro y
    show G (y.1 + P) (y.2 + 0) = G y.1 y.2
    rw [add_zero]; exact hpu y.2 y.1
  have hpv' : Periodic (uncurry G) (0, P) := by
    intro y
    show G (y.1 + 0) (y.2 + P) = G y.1 y.2
    rw [add_zero]; exact hpv y.1 y.2
  set T : ℝ × ℝ → ℝ := Family.triple (uncurry G) eu2 ev2 with hTdef
  have hT : Continuous T := (Family.contDiff_triple hG eu2 ev2).continuous
  have hZ : Continuous fun y : ℝ × ℝ => ⟪uncurry G y, N⟫ := hG.continuous.inner continuous_const
  have hφs : ContDiff ℝ ∞ (bumpPhi χ) :=
    ((contDiff_const.add contDiff_id).mul χ.contDiff).div_const _
  have hφ : Continuous (deriv (bumpPhi χ)) := hφs.continuous_deriv (by simp)
  have hmk : Continuous fun Z => mk (cutoffK χ) Z := by
    have : (fun Z => mk (cutoffK χ) Z) = fun Z => 1 / (4 * π) - deriv (bumpPhi χ) Z :=
      funext (mk_cutoffK χ)
    rw [this]; exact continuous_const.sub hφ
  have hc1 : Continuous fun p : ℝ × ℝ => T p * mk (cutoffK χ) ⟪uncurry G p, N⟫ :=
    hT.mul (hmk.comp hZ)
  have hc2 : Continuous fun p : ℝ × ℝ => T p * deriv (bumpPhi χ) ⟪uncurry G p, N⟫ :=
    hT.mul (hφ.comp hZ)
  have h1u : ∀ u, IntervalIntegrable (fun v => T (u, v) * mk (cutoffK χ) ⟪uncurry G (u, v), N⟫)
      volume b (b + P) := fun u =>
    (hc1.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have h2u : ∀ u, IntervalIntegrable (fun v => T (u, v) * deriv (bumpPhi χ) ⟪G u v, N⟫)
      volume b (b + P) := fun u =>
    (hc2.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have h1o : IntervalIntegrable
      (fun u => ∫ v in b..b + P, T (u, v) * mk (cutoffK χ) ⟪uncurry G (u, v), N⟫) volume a (a + P) :=
    (continuous_parametric_integral (f := fun u v => T (u, v) * mk (cutoffK χ) ⟪uncurry G (u, v), N⟫)
      (hc1.comp (continuous_fst.prodMk continuous_snd)) b (b + P)).intervalIntegrable _ _
  have h2o : IntervalIntegrable
      (fun u => ∫ v in b..b + P, T (u, v) * deriv (bumpPhi χ) ⟪G u v, N⟫) volume a (a + P) :=
    (continuous_parametric_integral (f := fun u v => T (u, v) * deriv (bumpPhi χ) ⟪G u v, N⟫)
      (hc2.comp (continuous_fst.prodMk continuous_snd)) b (b + P)).intervalIntegrable _ _
  have hzero := integral_triple_mul_mk_eq_zero (contDiff_cutoffK χ) hN hG hn' hpu' hpv' a b
  have hpt : ∀ u v, (1 / (4 * π)) * T (u, v)
      = T (u, v) * mk (cutoffK χ) ⟪uncurry G (u, v), N⟫
        + T (u, v) * deriv (bumpPhi χ) ⟪G u v, N⟫ := by
    intro u v
    rw [mk_cutoffK]
    show (1 / (4 * π)) * T (u, v)
      = T (u, v) * (1 / (4 * π) - deriv (bumpPhi χ) ⟪G u v, N⟫)
        + T (u, v) * deriv (bumpPhi χ) ⟪G u v, N⟫
    ring
  rw [gaussIntegral_eq_shift hG hpu hpv a b]
  calc (1 / (4 * π)) * ∫ u in a..a + P, ∫ v in b..b + P, T (u, v)
      = ∫ u in a..a + P, ∫ v in b..b + P, (1 / (4 * π)) * T (u, v) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun u _ => ?_
        rw [← intervalIntegral.integral_const_mul]
    _ = ∫ u in a..a + P, ∫ v in b..b + P,
          (T (u, v) * mk (cutoffK χ) ⟪uncurry G (u, v), N⟫
            + T (u, v) * deriv (bumpPhi χ) ⟪G u v, N⟫) := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        exact intervalIntegral.integral_congr fun v _ => hpt u v
    _ = (∫ u in a..a + P, ∫ v in b..b + P, T (u, v) * mk (cutoffK χ) ⟪uncurry G (u, v), N⟫)
          + ∫ u in a..a + P, ∫ v in b..b + P, T (u, v) * deriv (bumpPhi χ) ⟪G u v, N⟫ := by
        rw [← intervalIntegral.integral_add h1o h2o]
        exact intervalIntegral.integral_congr fun u _ => intervalIntegral.integral_add (h1u u) (h2u u)
    _ = ∫ u in a..a + P, ∫ v in b..b + P, T (u, v) * deriv (bumpPhi χ) ⟪G u v, N⟫ := by
        rw [hzero, zero_add]

end UA

/-! ## U-B. Frame, chart Jacobian, inverse-function neighbourhoods, compactness -/
section UB

/-- A unit vector orthogonal to a given unit vector (helper for B1): some coordinate vector `v` has
`⟪N, v⟫² < 1`, and `N × v` normalised does the job. -/
theorem ub_exists_unit_orth {N : E3} (hN : ‖N‖ = 1) : ∃ e : E3, ‖e‖ = 1 ∧ ⟪N, e⟫ = 0 := by
  have hsum : N 0 ^ 2 + N 1 ^ 2 + N 2 ^ 2 = 1 := by
    have h := real_inner_self_eq_norm_sq N
    rw [hN, inner_eq_sum] at h
    nlinarith [h]
  obtain ⟨v, hv1, hv2⟩ : ∃ v : E3, ‖v‖ = 1 ∧ ⟪N, v⟫ ^ 2 < 1 := by
    by_cases h0 : N 0 ^ 2 < 1
    · refine ⟨EuclideanSpace.single 0 1, by simp, ?_⟩
      rw [EuclideanSpace.inner_single_right]; simpa using h0
    · refine ⟨EuclideanSpace.single 1 1, by simp, ?_⟩
      rw [EuclideanSpace.inner_single_right]
      have : N 1 = 0 := by nlinarith [sq_nonneg (N 1), sq_nonneg (N 2)]
      simp [this]
  set w := cross N v with hw
  have hw2 : ‖w‖ ^ 2 = 1 - ⟪N, v⟫ ^ 2 := by rw [hw, norm_cross_sq, hN, hv1]; ring
  have hwpos : 0 < ‖w‖ := by
    have h2 : 0 < ‖w‖ ^ 2 := by rw [hw2]; linarith
    rcases (norm_nonneg w).lt_or_eq with h | h
    · exact h
    · rw [← h] at h2; simp at h2
  have hwne : w ≠ 0 := norm_pos_iff.mp hwpos
  refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
  · exact norm_smul_inv_norm hwne
  · rw [real_inner_smul_right, hw, inner_cross_self_left, mul_zero]

-- LEAF B1
/-- A positive orthonormal frame `(e₁, e₂, N)` completing a unit vector `N`. -/
theorem exists_frame {N : E3} (hN : ‖N‖ = 1) :
    ∃ e₁ e₂ : E3, ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧ ⟪e₁, e₂⟫ = 0 ∧ cross e₁ e₂ = N := by
  obtain ⟨e₁, h₁, hN₁⟩ := ub_exists_unit_orth hN
  have h₁N : ⟪e₁, N⟫ = 0 := by rw [real_inner_comm]; exact hN₁
  refine ⟨e₁, cross N e₁, h₁, ?_, inner_cross_self_right N e₁, ?_⟩
  · have h : ‖cross N e₁‖ ^ 2 = 1 := by rw [norm_cross_sq, hN, h₁, hN₁]; norm_num
    have h0 := norm_nonneg (cross N e₁)
    nlinarith
  · rw [cross_cross_eq, real_inner_self_eq_norm_sq, h₁, h₁N, zero_smul, sub_zero, one_pow, one_smul]

-- LEAF B2
/-- Parseval for the frame: `⟪x,e₁⟫² + ⟪x,e₂⟫² + ⟪x,N⟫² = ‖x‖²`. -/
theorem frame_parseval {e₁ e₂ N : E3} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : ⟪e₁, e₂⟫ = 0)
    (hN : cross e₁ e₂ = N) (x : E3) :
    ⟪x, e₁⟫ ^ 2 + ⟪x, e₂⟫ ^ 2 + ⟪x, N⟫ ^ 2 = ‖x‖ ^ 2 := by
  have hNn : ‖N‖ ^ 2 = 1 := by rw [← hN, norm_cross_sq, h₁, h₂, h₁₂]; norm_num
  -- Lagrange: `‖x × N‖² = ‖x‖²‖N‖² − ⟪x,N⟫²`
  have hL := norm_cross_sq x N
  rw [hNn, mul_one] at hL
  -- BAC-CAB: `x × N = x × (e₁ × e₂) = ⟪x,e₂⟫ e₁ − ⟪x,e₁⟫ e₂`
  have hc : cross x N = ⟪x, e₂⟫ • e₁ - ⟪x, e₁⟫ • e₂ := by rw [← hN, cross_cross_eq]
  have hn : ‖cross x N‖ ^ 2 = ⟪x, e₂⟫ ^ 2 + ⟪x, e₁⟫ ^ 2 := by
    rw [hc, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      h₁₂, h₁, h₂]
    simp only [Real.norm_eq_abs, mul_one, sq_abs, mul_zero, sub_zero]
  linarith

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
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),
    Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one,
    Module.Basis.coe_finTwoProd_repr, ContinuousLinearMap.coe_coe]
  simp

-- LEAF B5
/-- Jacobian of the chart: `det DF = ⟪e₁ × e₂, G_u × G_v⟫ = D · Z`
(`det_eq_fin_two`, `inner_cross_cross'`, `cross_fderiv_eq_smul`). -/
theorem det_chartDeriv {e₁ e₂ N : E3} (hN : cross e₁ e₂ = N) {G : ℝ × ℝ → E3}
    (hG : ContDiff ℝ ∞ G) (hn : ∀ y, ‖G y‖ = 1) (x : ℝ × ℝ) :
    (chartDeriv e₁ e₂ G x).det = Family.triple G eu2 ev2 x * ⟪G x, N⟫ := by
  have key := inner_cross_cross' e₁ e₂ (fderiv ℝ G x eu2) (fderiv ℝ G x ev2)
  rw [hN, cross_fderiv_eq_smul hG hn x eu2 ev2, real_inner_smul_right, real_inner_comm (G x) N]
    at key
  rw [det_eq_fin_two]
  simp only [chartDeriv, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply]
  exact key.symm

/-- The chart is smooth (helper for B6). -/
theorem ub_contDiff_chart (e₁ e₂ : E3) {G : ℝ × ℝ → E3} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (chart e₁ e₂ G) :=
  (contDiff_const.inner ℝ hG).prodMk (contDiff_const.inner ℝ hG)

-- LEAF B6
/-- At a regular preimage the chart has an invertible strict derivative
(`det_chartDeriv` gives `det = D p ≠ 0`; `LinearMap.equivOfDetNeZero`,
`LinearEquiv.toContinuousLinearEquiv`, `ContDiffAt.hasStrictFDerivAt`, `hasFDerivAt_chart`). -/
theorem exists_strict_equiv_chart {e₁ e₂ N : E3} (hN : cross e₁ e₂ = N) (hNu : ‖N‖ = 1)
    {G : ℝ × ℝ → E3} (hG : ContDiff ℝ ∞ G) (hn : ∀ y, ‖G y‖ = 1) {p : ℝ × ℝ} (hp : G p = N)
    (hD : Family.triple G eu2 ev2 p ≠ 0) :
    ∃ e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      HasStrictFDerivAt (chart e₁ e₂ G) (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
  have hdet : (chartDeriv e₁ e₂ G p).det ≠ 0 := by
    rw [det_chartDeriv hN hG hn p, hp, real_inner_self_eq_norm_sq, hNu]; simpa using hD
  refine ⟨(chartDeriv e₁ e₂ G p).toContinuousLinearEquivOfDetNeZero hdet, ?_⟩
  rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
  exact (ub_contDiff_chart e₁ e₂ hG).contDiffAt.hasStrictFDerivAt' (hasFDerivAt_chart e₁ e₂ hG p)
    (by simp)

/-- Replica of Mathlib's `HasStrictFDerivAt.approximates_deriv_on_nhds` (the module
`Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv` is not among the imports; only the
`ApproximatesLinearOn` layer is). -/
theorem ub_approximates_deriv_on_nhds {f : ℝ × ℝ → ℝ × ℝ} {f' : ℝ × ℝ →L[ℝ] ℝ × ℝ} {a : ℝ × ℝ}
    (hf : HasStrictFDerivAt f f' a) {c : NNReal} (hc : 0 < c) :
    ∃ s ∈ 𝓝 a, ApproximatesLinearOn f f' s c := by
  have := hf.isLittleO.def hc
  rw [nhds_prod_eq, Filter.Eventually, mem_prod_same_iff] at this
  rcases this with ⟨s, has, hs⟩
  exact ⟨s, has, fun x hx y hy => hs (mk_mem_prod hx hy)⟩

/-- An open neighbourhood on which the sign of a continuous nonvanishing function is constant
(helper for B7). -/
theorem ub_exists_sign_nhd {D : ℝ × ℝ → ℝ} (hD : Continuous D) {p : ℝ × ℝ} (hp : D p ≠ 0) :
    ∃ W : Set (ℝ × ℝ), IsOpen W ∧ p ∈ W ∧ ∀ x ∈ W, Real.sign (D x) = Real.sign (D p) := by
  rcases hp.lt_or_gt with hneg | hpos
  · refine ⟨{x | D x < 0}, isOpen_lt hD continuous_const, hneg, fun x hx => ?_⟩
    rw [Real.sign_of_neg hx, Real.sign_of_neg hneg]
  · refine ⟨{x | 0 < D x}, isOpen_lt continuous_const hD, hpos, fun x hx => ?_⟩
    rw [Real.sign_of_pos hx, Real.sign_of_pos hpos]

/-- The chart vanishes at a preimage of `N` (helper for B7). -/
theorem ub_chart_eq_zero {e₁ e₂ N : E3} (hN : cross e₁ e₂ = N) {G : ℝ × ℝ → E3} {p : ℝ × ℝ}
    (hp : G p = N) : chart e₁ e₂ G p = 0 := by
  simp only [chart, hp, ← hN, inner_cross_self_left, inner_cross_self_right]
  rfl

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
  obtain ⟨e, he⟩ := exists_strict_equiv_chart hN hNu hG hn hp hD
  -- the approximation constant `c = ‖e⁻¹‖⁻¹ / 2`
  have hNpos : 0 < ‖(e.symm : ℝ × ℝ →L[ℝ] ℝ × ℝ)‖₊ := by
    rcases e.subsingleton_or_nnnorm_symm_pos with h | h
    · exact absurd h (not_subsingleton _)
    · exact h
  have hc0 : (0 : NNReal) < ‖(e.symm : ℝ × ℝ →L[ℝ] ℝ × ℝ)‖₊⁻¹ / 2 := half_pos (inv_pos.2 hNpos)
  have hcN : ‖(e.symm : ℝ × ℝ →L[ℝ] ℝ × ℝ)‖₊⁻¹ / 2 < ‖(e.symm : ℝ × ℝ →L[ℝ] ℝ × ℝ)‖₊⁻¹ :=
    NNReal.half_lt_self (ne_of_gt (inv_pos.2 hNpos))
  obtain ⟨s, hs_nhds, hs⟩ := ub_approximates_deriv_on_nhds he hc0
  obtain ⟨s', hs's, hs'open, hps'⟩ := mem_nhds_iff.mp hs_nhds
  obtain ⟨U', hU'U, hU'open, hpU'⟩ := mem_nhds_iff.mp hU
  have hZcont : Continuous fun x => ⟪G x, N⟫ := hG.continuous.inner continuous_const
  have hpZ : 0 < ⟪G p, N⟫ := by rw [hp, real_inner_self_eq_norm_sq, hNu]; norm_num
  obtain ⟨W, hWopen, hpW, hWsign⟩ :=
    ub_exists_sign_nhd (Family.contDiff_triple hG eu2 ev2).continuous hD
  set V : Set (ℝ × ℝ) := s' ∩ U' ∩ {x | 0 < ⟪G x, N⟫} ∩ W with hVdef
  have hVopen : IsOpen V :=
    ((hs'open.inter hU'open).inter (isOpen_lt continuous_const hZcont)).inter hWopen
  have hpV : p ∈ V := ⟨⟨⟨hps', hpU'⟩, hpZ⟩, hpW⟩
  have hVs : V ⊆ s := fun x hx => hs's hx.1.1.1
  refine ⟨V, hVopen, hpV, fun x hx => hU'U hx.1.1.2, (hs.injOn (Or.inr hcN)).mono hVs,
    fun x hx => hx.1.2, fun x hx => hWsign x hx.2, ?_⟩
  have himg : IsOpen (chart e₁ e₂ G '' V) :=
    (hs.mono_set hVs).open_image e.toNonlinearRightInverse hVopen (Or.inr hcN)
  have hmem : chart e₁ e₂ G p ∈ chart e₁ e₂ G '' V := mem_image_of_mem _ hpV
  rw [ub_chart_eq_zero hN hp] at hmem
  exact Metric.mem_nhds_iff.mp (himg.mem_nhds hmem)

/-- A positive lower bound for finitely many positive reals (helper for B8, B9). -/
theorem ub_exists_pos_le {α : Type*} (T : Finset α) (f : α → ℝ) (hf : ∀ t ∈ T, 0 < f t) :
    ∃ r > 0, ∀ t ∈ T, r ≤ f t := by
  rcases T.eq_empty_or_nonempty with hT | hT
  · exact ⟨1, one_pos, fun t ht => by simp [hT] at ht⟩
  · obtain ⟨t₀, ht₀, hmin⟩ := T.exists_min_image f hT
    exact ⟨f t₀, hf t₀ ht₀, hmin⟩

-- LEAF B8
/-- Disjoint balls of a common radius around the points of a finite set, inside an open set. -/
theorem exists_disjoint_balls (S : Finset (ℝ × ℝ)) {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hSW : ∀ p ∈ S, p ∈ W) :
    ∃ r > 0, (∀ p ∈ S, Metric.ball p r ⊆ W) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint (Metric.ball p r) (Metric.ball q r) := by
  have hε : ∀ p : ℝ × ℝ, ∃ ε > 0, p ∈ S → Metric.ball p ε ⊆ W := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW p (hSW p hp)
      exact ⟨ε, hε, fun _ => hball⟩
    · exact ⟨1, one_pos, fun h => absurd h hp⟩
  choose ε hεpos hεW using hε
  obtain ⟨r₁, hr₁, hr₁le⟩ := ub_exists_pos_le S ε (fun p _ => hεpos p)
  set T := (S ×ˢ S).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) => q.1 ≠ q.2) with hT
  obtain ⟨r₂, hr₂, hr₂le⟩ := ub_exists_pos_le T (fun q => dist q.1 q.2 / 2) (by
    intro q hq
    rw [hT, Finset.mem_filter] at hq
    exact half_pos (dist_pos.mpr hq.2))
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun p hp => ?_, fun p hp q hq hpq => ?_⟩
  · exact (Metric.ball_subset_ball ((min_le_left _ _).trans (hr₁le p hp))).trans (hεW p hp)
  · apply Metric.ball_disjoint_ball
    have h1 := hr₂le (p, q) (by
      rw [hT, Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hp, hq⟩, hpq⟩)
    have h2 := min_le_right r₁ r₂
    simp only at h1
    linarith

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
  obtain ⟨r₀, hr₀, hball, hdisj⟩ := exists_disjoint_balls S (isOpen_Ioo.prod isOpen_Ioo) hSint
  have hbox : ∀ p ∈ S, p ∈ Icc a (a + P) ×ˢ Icc b (b + P) := fun p hp =>
    ⟨Ioo_subset_Icc_self (hSint p hp).1, Ioo_subset_Icc_self (hSint p hp).2⟩
  -- the neighbourhoods
  have hV : ∀ p : ℝ × ℝ, ∃ V : Set (ℝ × ℝ), p ∈ S →
      (IsOpen V ∧ p ∈ V ∧ V ⊆ Metric.ball p r₀ ∧ InjOn (chart e₁ e₂ G) V ∧
        (∀ x ∈ V, 0 < ⟪G x, N⟫) ∧
        (∀ x ∈ V, Real.sign (Family.triple G eu2 ev2 x) = Real.sign (Family.triple G eu2 ev2 p)) ∧
        ∃ r > 0, Metric.ball (0 : ℝ × ℝ) r ⊆ chart e₁ e₂ G '' V) := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨V, hV⟩ := exists_regular_nhd hN hNu hG hn ((hS p (hbox p hp)).mpr hp) (hreg p hp)
        (Metric.ball_mem_nhds p hr₀)
      exact ⟨V, fun _ => hV⟩
    · exact ⟨∅, fun h => absurd h hp⟩
  choose V hV using hV
  -- the radii and their minimum
  have hr : ∀ p : ℝ × ℝ, ∃ r : ℝ, p ∈ S →
      (0 < r ∧ Metric.ball (0 : ℝ × ℝ) r ⊆ chart e₁ e₂ G '' V p) := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨r, hr, hrV⟩ := (hV p hp).2.2.2.2.2.2
      exact ⟨r, fun _ => ⟨hr, hrV⟩⟩
    · exact ⟨1, fun h => absurd h hp⟩
  choose r hr using hr
  obtain ⟨rmin, hrmin, hrmin_le⟩ := ub_exists_pos_le S r (fun p hp => (hr p hp).1)
  -- the compact complement and `δ`
  have hKc : IsCompact ((Icc a (a + P) ×ˢ Icc b (b + P)) \ ⋃ p ∈ S, V p) :=
    (isCompact_Icc.prod isCompact_Icc).diff
      (isOpen_iUnion fun p => isOpen_iUnion fun hp => (hV p hp).1)
  have hKZ : ∀ x ∈ (Icc a (a + P) ×ˢ Icc b (b + P)) \ ⋃ p ∈ S, V p, ⟪G x, N⟫ < 1 := by
    intro x hx
    refine inner_lt_one_of_ne (hn x) hNu fun hGx => hx.2 ?_
    have hxS : x ∈ S := (hS x hx.1).mp hGx
    exact mem_iUnion₂.mpr ⟨x, hxS, (hV x hxS).2.1⟩
  obtain ⟨δ, hδ, hδK⟩ := exists_delta_of_compact hG.continuous hKc hKZ
  exact ⟨{
    V := V, r := rmin, δ := δ, r_pos := hrmin, δ_pos := hδ
    V_isOpen := fun p hp => (hV p hp).1
    mem_V := fun p hp => (hV p hp).2.1
    V_subset := fun p hp => (hV p hp).2.2.1.trans (hball p hp)
    injOn_V := fun p hp => (hV p hp).2.2.2.1
    pos_V := fun p hp => (hV p hp).2.2.2.2.1
    sign_V := fun p hp => (hV p hp).2.2.2.2.2.1
    ball_subset := fun p hp => (Metric.ball_subset_ball (hrmin_le p hp)).trans (hr p hp).2
    disjoint_V := fun p hp q hq hpq =>
      (hdisj p hp q hq hpq).mono (hV p hp).2.2.1 (hV q hq).2.2.1
    small := fun x hx hxU => hδK x ⟨hx, hxU⟩ }⟩

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
  have hI : IntegrableOn f (Icc a a' ×ˢ Icc b b') volume :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  calc ∫ u in a..a', ∫ v in b..b', f (u, v)
      = ∫ u in Icc a a', ∫ v in Icc b b', f (u, v) := by
        simp only [intervalIntegral.integral_of_le, ha, hb,
          setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
    _ = ∫ x in Icc a a' ×ˢ Icc b b', f x := (setIntegral_prod _ hI).symm

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
  have hI : IntegrableOn f (Icc a a' ×ˢ Icc b b') volume :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hsub : (⋃ p ∈ S, V p) ⊆ Icc a a' ×ˢ Icc b b' := iUnion₂_subset hVsub
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_Icc.prod measurableSet_Icc) hsub (fun x hx => hzero x hx.1 hx.2)]
  exact integral_biUnion_finset S (fun p hp => (hVo p hp).measurableSet)
    (fun p hp q hq hpq => hdisj p hp q hq hpq) (fun p hp => hI.mono_set (hVsub p hp))

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
  -- continuity of the integrand
  have hφ : ContDiff ℝ ∞ (bumpPhi χ) := by
    have : bumpPhi χ = fun z => (1 + z) * χ z / (4 * π) := rfl
    rw [this]
    exact ((contDiff_const.add contDiff_id).mul χ.contDiff).div_const _
  have hfc : Continuous fun x : ℝ × ℝ =>
      Family.triple G eu2 ev2 x * deriv (bumpPhi χ) ⟪G x, N⟫ :=
    (Family.contDiff_triple hG eu2 ev2).continuous.mul
      ((hφ.continuous_deriv (by simp)).comp (hG.continuous.inner continuous_const))
  have hbox := integral_box_eq_setIntegral (a := a) (a' := a + P) (b := b) (b' := b + P) hfc
    (le_add_of_nonneg_right hP.le) (le_add_of_nonneg_right hP.le)
  refine hbox.trans ?_
  -- the integrand vanishes off the neighbourhoods
  have hzero : ∀ x ∈ Icc a (a + P) ×ˢ Icc b (b + P), x ∉ ⋃ p ∈ S, sys.V p →
      Family.triple G eu2 ev2 x * deriv (bumpPhi χ) ⟪G x, N⟫ = 0 := by
    intro x hx hxU
    have hZ : ⟪G x, N⟫ < 1 - sys.δ := sys.small x hx hxU
    rw [deriv_bumpPhi_eq_zero_of_lt χ (by linarith), mul_zero]
  rw [setIntegral_box_eq_sum hfc S sys.V sys.V_isOpen
    (fun p hp => (sys.V_subset p hp).trans
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
    sys.disjoint_V hzero]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [integral_bump_on_nhd χ h₁ h₂ h₁₂ hN hG hn (hreg p hp) (sys.V_isOpen p hp)
    (sys.injOn_V p hp) (sys.pos_V p hp) (sys.sign_V p hp) (sys.ball_subset p hp)
    (fun w hw => chartDensity_mem_ball χ sys.r_pos hχr hw), integral_chartDensity χ hχ₁, mul_one]

/-- U-D helper: the shifted coordinate `u + P·[u < a]` of `u ∈ [0,P)`, `u ≠ a`, lies strictly inside
`(a, a + P)`. -/
theorem ud_shift_mem {P a u : ℝ} (ha0 : 0 < a) (haP : a < P) (h0 : 0 ≤ u) (huP : u < P)
    (hne : u ≠ a) :
    a < u + (if u < a then P else 0) ∧ u + (if u < a then P else 0) < a + P := by
  split_ifs with h
  · constructor <;> linarith
  · have : a < u := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)
    constructor <;> linarith

/-- U-D helper: the coordinate shift `u ↦ u + P·[u < a]` is injective on `[0, P)`. -/
theorem ud_shift_inj {P a u u' : ℝ} (h0 : 0 ≤ u) (huP : u < P) (h0' : 0 ≤ u') (hu'P : u' < P)
    (h : u + (if u < a then P else 0) = u' + (if u' < a then P else 0)) : u = u' := by
  split_ifs at h <;> linarith

/-- U-D helper: reduction of `u ∈ [a, a + P]` (with `0 < a < P`) into the fundamental domain
`[0, P)` by `u' = u − P·[P ≤ u]`, and the shift `u' + P·[u' < a]` recovers `u` when `u' ≠ a`. -/
theorem ud_shift_coord {P a u : ℝ} (ha0 : 0 < a) (haP : a < P) (hu : a ≤ u) (hu' : u ≤ a + P) :
    0 ≤ u - (if P ≤ u then P else 0) ∧ u - (if P ≤ u then P else 0) < P ∧
    (u - (if P ≤ u then P else 0) ≠ a →
      (u - (if P ≤ u then P else 0)) + (if u - (if P ≤ u then P else 0) < a then P else 0) = u) := by
  by_cases h : P ≤ u
  · simp only [ite_eq_left h]
    refine ⟨by linarith, by linarith, fun hne => ?_⟩
    have : u - P < a := lt_of_le_of_ne (by linarith) hne
    simp only [ite_eq_left this]; ring
  · simp only [ite_eq_right h, sub_zero]
    refine ⟨by linarith, by linarith, fun _ => ?_⟩
    simp only [ite_eq_right (not_lt.mpr hu), add_zero]

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
  classical
  set T := hfin.toFinset with hT_def
  have hmemT : ∀ p, p ∈ T ↔
      ((0 ≤ p.1 ∧ p.1 < P) ∧ (0 ≤ p.2 ∧ p.2 < P)) ∧ G p.1 p.2 = N := by
    intro p
    rw [hT_def, Finite.mem_toFinset]
    exact Iff.rfl
  -- choose `a, b ∈ (0, P)` avoiding the coordinates of the preimages
  obtain ⟨a, ⟨ha0, haP⟩, haA⟩ := (Ioo_infinite hP).exists_notMem_finset (T.image Prod.fst)
  obtain ⟨b, ⟨hb0, hbP⟩, hbB⟩ := (Ioo_infinite hP).exists_notMem_finset (T.image Prod.snd)
  have ha1 : ∀ p ∈ T, p.1 ≠ a := fun p hp h => haA (Finset.mem_image.mpr ⟨p, hp, h⟩)
  have hb1 : ∀ p ∈ T, p.2 ≠ b := fun p hp h => hbB (Finset.mem_image.mpr ⟨p, hp, h⟩)
  -- periodicity, unfolded
  have hGu : ∀ u v, G (u + P) v = G u v := fun u v => hpu v u
  have hGv : ∀ u v, G u (v + P) = G u v := fun u v => hpv u v
  have hGu' : ∀ u v, G (u - if P ≤ u then P else 0) v = G u v := by
    intro u v
    split_ifs
    · rw [← hGu (u - P) v, sub_add_cancel]
    · rw [sub_zero]
  have hGv' : ∀ u v, G u (v - if P ≤ v then P else 0) = G u v := by
    intro u v
    split_ifs
    · rw [← hGv u (v - P), sub_add_cancel]
    · rw [sub_zero]
  have hD1 : ∀ u v, gaussDensity G (u + P) v = gaussDensity G u v :=
    fun u v => (gaussDensity_periodic hpu hpv u v).1
  have hD2 : ∀ u v, gaussDensity G u (v + P) = gaussDensity G u v :=
    fun u v => (gaussDensity_periodic hpu hpv u v).2
  -- the shift map `τ p = p + (P·[p.1 < a], P·[p.2 < b])`
  set τ : ℝ × ℝ → ℝ × ℝ :=
    fun p => (p.1 + if p.1 < a then P else 0, p.2 + if p.2 < b then P else 0) with hτ_def
  have hτG : ∀ p, G (τ p).1 (τ p).2 = G p.1 p.2 := by
    intro p
    simp only [hτ_def]
    split_ifs <;> simp only [hGu, hGv, add_zero]
  have hτD : ∀ p, gaussDensity G (τ p).1 (τ p).2 = gaussDensity G p.1 p.2 := by
    intro p
    simp only [hτ_def]
    split_ifs <;> simp only [hD1, hD2, add_zero]
  have hτ_mem : ∀ p ∈ T, τ p ∈ Ioo a (a + P) ×ˢ Ioo b (b + P) := by
    intro p hp
    obtain ⟨⟨⟨h10, h1P⟩, ⟨h20, h2P⟩⟩, -⟩ := (hmemT p).mp hp
    simp only [hτ_def, mem_prod, mem_Ioo]
    exact ⟨ud_shift_mem ha0 haP h10 h1P (ha1 p hp), ud_shift_mem hb0 hbP h20 h2P (hb1 p hp)⟩
  have hτ_inj : InjOn τ (T : Set (ℝ × ℝ)) := by
    intro p hp q hq hpq
    obtain ⟨⟨⟨hp10, hp1P⟩, ⟨hp20, hp2P⟩⟩, -⟩ := (hmemT p).mp hp
    obtain ⟨⟨⟨hq10, hq1P⟩, ⟨hq20, hq2P⟩⟩, -⟩ := (hmemT q).mp hq
    simp only [hτ_def, Prod.ext_iff] at hpq
    exact Prod.ext (ud_shift_inj hp10 hp1P hq10 hq1P hpq.1) (ud_shift_inj hp20 hp2P hq20 hq2P hpq.2)
  refine ⟨a, b, T.image τ, ?_, ?_, ?_⟩
  · -- the preimages in the closed box are exactly the shifted ones
    intro x hx
    obtain ⟨⟨hx1a, hx1P⟩, ⟨hx2b, hx2P⟩⟩ := hx
    constructor
    · intro hGx
      have hGx' : G x.1 x.2 = N := hGx
      obtain ⟨hq10, hq1P, hq1τ⟩ := ud_shift_coord ha0 haP hx1a hx1P
      obtain ⟨hq20, hq2P, hq2τ⟩ := ud_shift_coord hb0 hbP hx2b hx2P
      -- `q`, the reduction of `x` into the fundamental domain, is a preimage
      have hqT : (x.1 - if P ≤ x.1 then P else 0, x.2 - if P ≤ x.2 then P else 0) ∈ T := by
        refine (hmemT _).mpr ⟨⟨⟨hq10, hq1P⟩, ⟨hq20, hq2P⟩⟩, ?_⟩
        show G (x.1 - if P ≤ x.1 then P else 0) (x.2 - if P ≤ x.2 then P else 0) = N
        rw [hGu', hGv']
        exact hGx'
      refine Finset.mem_image.mpr ⟨_, hqT, Prod.ext ?_ ?_⟩
      · exact hq1τ (ha1 _ hqT)
      · exact hq2τ (hb1 _ hqT)
    · intro hxS
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxS
      show G (τ p).1 (τ p).2 = N
      rw [hτG]
      exact ((hmemT p).mp hp).2
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact hτ_mem p hp
  · rw [Finset.sum_image hτ_inj]
    exact Finset.sum_congr rfl fun p _ => by rw [hτD]

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
