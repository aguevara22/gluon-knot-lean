import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import SM.ContactMotions

/-! # SM fd:transverse-neighborhood — PROOF SKELETON (row 84)

Written 2026-09-14 (work/drafts/fd/).  Source: reference/SM/sm-3-statesum.tex:2395-2409
(statement), 2410-2559 (proof).  Route: `FD_84_87_FEASIBILITY_v2.md` §1; leaf-by-leaf plan with
truth checks: `TN_PLAN.md`.

Layout.  §1–§6 (from `namespace SM` to `TransverseNeighborhoodData`) are **byte-identical** to
`TransverseNeighborhood.lean` lines 67-238 (the statement).  §7 adds the route: definitions,
lemmas PROVED here (the Moser rational identities of `MoserIdentityCheck.lean`, transported to the
concrete chart; small algebra), LEAF lemmas with `sorry` bodies grouped in units A–F, and the row
theorem `SM.fd_transverse_neighborhood : TransverseNeighborhoodData` PROVED from the leaves
(`#print axioms` shows `sorryAx` only through the leaves).

Units (dependencies): A chart `F` (none) · B forms and Moser field (none) · C the time-dependent
flow (B defs) · D the model neighbourhood `H` (A, B, C) · E Legendrian `L`, annulus, pushoff,
transverse isotopy (statement notions only) · F ambient isotopy `Ψ` (statement notions only).
Row theorem: D + E + F.

Check: `cd work/lean && lake env lean ../drafts/fd/TN_Skeleton.lean`. -/

namespace SM

open scoped ContDiff Topology
open Set Function Real

noncomputable section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace TransverseNeighborhood

/-! ## 1. Contact forms in coordinates -/

/-- `α = dz − y dx` at `p` on `v`: `α_p(v) = v_z − p_y v_x`. -/
def alpha (p v : ℝ³) : ℝ := v 2 - p 1 * v 0

/-- `α₀ = dθ + u dv − v du` at `(θ, w)`, `w = (u, v)`, on the tangent vector `(τ, η)`
(sm-3:2402). -/
def alpha0 (w : ℝ²) (τ : ℝ) (η : ℝ²) : ℝ := τ + w 0 * η 1 - w 1 * η 0

/-! ## 2. Circles -/

/-- A smooth embedded oriented circle `T : ℝ/(2πℤ) → ℝ³` (sm-3:2397-2398), as a `2π`-periodic
map on `ℝ`: smooth, periodic, injective modulo the period, immersed (FR-TN-1).  Its orientation is
the direction of the parameter. -/
structure IsEmbeddedCircle (T : ℝ → ℝ³) : Prop where
  /-- "smooth". -/
  smooth : ContDiff ℝ ∞ T
  /-- defined on `ℝ/(2πℤ)`. -/
  periodic : Periodic T (2 * π)
  /-- "embedded": injective on the circle. -/
  injective : ∀ θ θ', T θ = T θ' → ∃ k : ℤ, θ' = θ + 2 * π * k
  /-- "embedded": an immersion. -/
  immersion : ∀ θ, deriv T θ ≠ 0

/-- `α(T′) > 0` (sm-3:2398): a positive transverse circle. -/
def IsPositiveTransverse (T : ℝ → ℝ³) : Prop := ∀ θ, 0 < alpha (T θ) (deriv T θ)

/-- `α(L′) = 0`: a Legendrian circle. -/
def IsLegendrian (L : ℝ → ℝ³) : Prop := ∀ θ, alpha (L θ) (deriv L θ) = 0

/-- An orientation-preserving reparametrization of the circle: a smooth `ρ : ℝ → ℝ` with
`ρ′ > 0` lifting a degree-one map (`ρ(θ + 2π) = ρ(θ) + 2π`). -/
structure IsCircleReparam (ρ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ ρ
  deriv_pos : ∀ θ, 0 < deriv ρ θ
  lift : ∀ θ, ρ (θ + 2 * π) = ρ θ + 2 * π

/-! ## 3. The transverse model neighbourhood (sm-3:2399-2404) -/

/-- The open solid torus `S¹ × D_δ` in coordinates: all `θ`, `w` in the open disc. -/
def solidTorus (δ : ℝ) : Set (ℝ × ℝ²) := univ ×ˢ Metric.ball 0 δ

/-- "There are `δ > 0` and a smooth embedding `H : S¹ × D_δ → ℝ³` fixing the parametrized core `T`
such that `H^*α = hα₀`, `α₀ = dθ + u dv − v du`, `h > 0`" (sm-3:2399-2404), one field per clause
(FR-TN-2, FR-TN-3). -/
structure IsTransverseModel (T : ℝ → ℝ³) (δ : ℝ) (H : ℝ × ℝ² → ℝ³) (h : ℝ × ℝ² → ℝ) : Prop where
  /-- "`δ > 0`". -/
  delta_pos : 0 < δ
  /-- "smooth": `C^∞` on the open solid torus. -/
  smooth : ContDiffOn ℝ ∞ H (solidTorus δ)
  /-- defined on `S¹ × D_δ`: `2π`-periodic in `θ`. -/
  periodic : ∀ θ w, H (θ + 2 * π, w) = H (θ, w)
  /-- "embedding": injective on `S¹ × D_δ`. -/
  injective : ∀ θ w θ' w', w ∈ Metric.ball (0 : ℝ²) δ → w' ∈ Metric.ball (0 : ℝ²) δ →
    H (θ, w) = H (θ', w') → w = w' ∧ ∃ k : ℤ, θ' = θ + 2 * π * k
  /-- "embedding": an immersion. -/
  immersion : ∀ θ w, w ∈ Metric.ball (0 : ℝ²) δ → Injective (fderiv ℝ H (θ, w))
  /-- "embedding": a topological embedding of `S¹ × D_δ` — the image of every open set is
  relatively open in the image (FR-TN-2). -/
  open_map : ∀ U : Set (ℝ × ℝ²), IsOpen U →
    ∃ V : Set ℝ³, IsOpen V ∧ H '' (U ∩ solidTorus δ) = V ∩ H '' solidTorus δ
  /-- "fixing the parametrized core `T`": `H(θ, 0) = T(θ)`. -/
  core : ∀ θ, H (θ, 0) = T θ
  /-- "`h > 0`" on the solid torus. -/
  factor_pos : ∀ θ w, w ∈ Metric.ball (0 : ℝ²) δ → 0 < h (θ, w)
  /-- "`H^*α = hα₀`": for every point of the solid torus and every tangent vector `(τ, η)`,
  `α_{H(θ,w)}(DH(θ,w)(τ, η)) = h(θ, w) · α₀_{w}(τ, η)`. -/
  pullback : ∀ θ w, w ∈ Metric.ball (0 : ℝ²) δ → ∀ (τ : ℝ) (η : ℝ²),
    alpha (H (θ, w)) (fderiv ℝ H (θ, w) (τ, η)) = h (θ, w) * alpha0 w τ η

/-! ## 4. Pushoffs and transverse isotopies (sm-3:2405-2406, 2490-2504) -/

/-- A transverse pushoff annulus of the Legendrian circle `L` (sm-3:2490-2502): a smooth embedded
annulus `B(θ, s)`, `−ε < s < b`, `2π`-periodic in `θ`, with `B(·, 0) = L`, everywhere transverse
to the contact planes ("the annulus is transverse to the contact planes, even along `s = 0`"),
whose circles `B(·, s)` with `s > 0` are positive transverse. -/
structure IsPushoffAnnulus (L : ℝ → ℝ³) (ε b : ℝ) (B : ℝ × ℝ → ℝ³) : Prop where
  eps_pos : 0 < ε
  b_pos : 0 < b
  smooth : ContDiffOn ℝ ∞ B (univ ×ˢ Ioo (-ε) b)
  periodic : ∀ θ s, B (θ + 2 * π, s) = B (θ, s)
  core : ∀ θ, B (θ, 0) = L θ
  injective : ∀ θ s θ' s', s ∈ Ioo (-ε) b → s' ∈ Ioo (-ε) b → B (θ, s) = B (θ', s') →
    s = s' ∧ ∃ k : ℤ, θ' = θ + 2 * π * k
  immersion : ∀ θ s, s ∈ Ioo (-ε) b → Injective (fderiv ℝ B (θ, s))
  /-- the tangent plane of the annulus is nowhere contained in the contact plane. -/
  transverse : ∀ θ s, s ∈ Ioo (-ε) b →
    alpha (B (θ, s)) (fderiv ℝ B (θ, s) (1, 0)) ≠ 0 ∨ alpha (B (θ, s)) (fderiv ℝ B (θ, s) (0, 1)) ≠ 0
  /-- "positive transverse for `0 < s`". -/
  positive : ∀ s, 0 < s → s < b → IsPositiveTransverse fun θ => B (θ, s)

/-- `T'` is a positive transverse pushoff of the Legendrian circle `L` (FR-TN-4): a positive
circle `B(·, s₀)`, `0 < s₀ < b`, of a pushoff annulus `B` of `L` ("a sufficiently small positive
circle is therefore the positive pushoff in the source convention", sm-3:2501-2502). -/
def IsPositivePushoff (L T' : ℝ → ℝ³) : Prop :=
  ∃ (ε b : ℝ) (B : ℝ × ℝ → ℝ³), IsPushoffAnnulus L ε b B ∧
    ∃ s₀, 0 < s₀ ∧ s₀ < b ∧ T' = fun θ => B (θ, s₀)

/-- `T₀` is transversely isotopic to `T₁` (sm-3:2503-2504; FR-TN-5): a smooth family
`F s`, `s ∈ [0,1]`, of positive transverse embedded circles with `F 0 = T₀` and `F 1` an
orientation-preserving reparametrization of `T₁`. -/
def TransverselyIsotopic (T₀ T₁ : ℝ → ℝ³) : Prop :=
  ∃ F : ℝ → ℝ → ℝ³, ContDiffOn ℝ ∞ (uncurry F) (Icc 0 1 ×ˢ univ) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, IsEmbeddedCircle (F s) ∧ IsPositiveTransverse (F s)) ∧
    F 0 = T₀ ∧ ∃ ρ : ℝ → ℝ, IsCircleReparam ρ ∧ F 1 = T₁ ∘ ρ

/-! ## 5. Compactly supported ambient isotopies (sm-3:2406-2408) -/

/-- "An explicit compactly supported ordinary ambient isotopy" (sm-3:2406-2407): a family
`Ψ_t`, `t ∈ [0,1]`, smooth in `(t, p)`, with `Ψ_0 = id`, each `Ψ_t` a diffeomorphism of `ℝ³`,
all equal to the identity outside one compact set. -/
structure IsCompactlySupportedAmbientIsotopy (Ψ : ℝ → ℝ³ → ℝ³) : Prop where
  smooth : ContDiffOn ℝ ∞ (uncurry Ψ) (Icc 0 1 ×ˢ univ)
  zero : ∀ p, Ψ 0 p = p
  diffeo : ∀ t ∈ Icc (0 : ℝ) 1, ∃ Ψinv : ℝ³ → ℝ³, ContDiff ℝ ∞ Ψinv ∧
    LeftInverse Ψinv (Ψ t) ∧ RightInverse Ψinv (Ψ t)
  support : ∃ K : Set ℝ³, IsCompact K ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ p, p ∉ K → Ψ t p = p

end TransverseNeighborhood

open TransverseNeighborhood

/-! ## 6. The printed statement -/

/-- The hypotheses of fd:transverse-neighborhood (sm-3:2397-2398): "`T : ℝ/(2πℤ) → ℝ³` a smooth
embedded oriented circle with `α(T′) > 0`". -/
structure TransverseNeighborhoodHyp (T : ℝ → ℝ³) : Prop where
  /-- "a smooth embedded oriented circle". -/
  circle : IsEmbeddedCircle T
  /-- "with `α(T′) > 0`". -/
  transverse : IsPositiveTransverse T

/-- The conclusion of fd:transverse-neighborhood for the witnesses `δ, H, h, L, Ψ`
(sm-3:2399-2409), one field per printed clause. -/
structure TransverseNeighborhoodConclusion (T : ℝ → ℝ³) (δ : ℝ) (H : ℝ × ℝ² → ℝ³)
    (h : ℝ × ℝ² → ℝ) (L : ℝ → ℝ³) (Ψ : ℝ → ℝ³ → ℝ³) : Prop where
  /-- sm-3:2399-2404 "There are `δ > 0` and a smooth embedding `H : S¹ × D_δ → ℝ³` fixing the
  parametrized core `T` such that `H^*α = hα₀`, `α₀ = dθ + u dv − v du`, `h > 0`". -/
  model : IsTransverseModel T δ H h
  /-- sm-3:2405 "There is an oriented Legendrian knot `L`": a smooth embedded oriented circle. -/
  legendrian_circle : IsEmbeddedCircle L
  /-- sm-3:2405 "Legendrian": `α(L′) = 0`. -/
  legendrian : IsLegendrian L
  /-- sm-3:2405 "in this neighbourhood": `L` lies in `H(S¹ × D_δ)`. -/
  mem_neighbourhood : ∀ θ, L θ ∈ H '' solidTorus δ
  /-- sm-3:2405-2406 "whose positive transverse pushoff is transversely isotopic to `T`". -/
  pushoff_isotopic : ∃ T' : ℝ → ℝ³, IsPositivePushoff L T' ∧ TransverselyIsotopic T' T
  /-- sm-3:2406-2407 "An explicit compactly supported ordinary ambient isotopy". -/
  ambient : IsCompactlySupportedAmbientIsotopy Ψ
  /-- sm-3:2407-2408 "carries the parametrized `L` to the parametrized `T`, preserving their
  orientations": `Ψ_1 ∘ L = T` as parametrized circles. -/
  carries : ∀ θ, Ψ 1 (L θ) = T θ

/-- **fd:transverse-neighborhood** (sm-3:2395-2409), the statement: for every `T` satisfying the
hypotheses there are `δ, H, h, L, Ψ` with the printed conclusion.  Not proved here (see the
module docstring and `FD_84_86_FEASIBILITY.md` §2). -/
def TransverseNeighborhoodData : Prop :=
  ∀ T : ℝ → ℝ³, TransverseNeighborhoodHyp T →
    ∃ (δ : ℝ) (H : ℝ × ℝ² → ℝ³) (h : ℝ × ℝ² → ℝ) (L : ℝ → ℝ³) (Ψ : ℝ → ℝ³ → ℝ³),
      TransverseNeighborhoodConclusion T δ H h L Ψ

/-! ## 7. Proof skeleton -/

namespace TransverseNeighborhood

open ContactMotions (IsGlobalFlow)

/-! ### 7.0 Shared small tools -/

/-- Scalar cutoff `cut1 a b x = smoothTransition ((b − x)/(b − a))`: `1` for `x ≤ a`, `0` for
`x ≥ b`, smooth (the paper's `χ` of sm-3:2512-2519 in Mathlib's normalisation). -/
def cut1 (a b x : ℝ) : ℝ := Real.smoothTransition ((b - x) / (b - a))

lemma contDiff_cut1 (a b : ℝ) : ContDiff ℝ ∞ (cut1 a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

lemma cut1_of_le {a b x : ℝ} (hab : a < b) (hx : x ≤ a) : cut1 a b x = 1 := by
  unfold cut1
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by linarith)]; linarith

lemma cut1_of_ge {a b x : ℝ} (hab : a < b) (hx : b ≤ x) : cut1 a b x = 0 := by
  unfold cut1
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith

lemma cut1_nonneg (a b x : ℝ) : 0 ≤ cut1 a b x := Real.smoothTransition.nonneg _
lemma cut1_le_one (a b x : ℝ) : cut1 a b x ≤ 1 := Real.smoothTransition.le_one _

/-! ### Unit A — the chart `F` (sm-3:2411-2428) -/

section chart
variable (T : ℝ → ℝ³)

/-- `a(θ) = α(T′(θ)) > 0` (sm-3:2411). -/
def aT (θ : ℝ) : ℝ := alpha (T θ) (deriv T θ)
/-- `c(θ) = √(2a(θ))` (sm-3:2411). -/
def cT (θ : ℝ) : ℝ := Real.sqrt (2 * aT T θ)
/-- `E₁(p) = ∂_x + y∂_z = (1, 0, p_y)` (sm-3:2413). -/
def E1 (p : ℝ³) : ℝ³ := !₂[1, 0, p 1]
/-- `E₂ = ∂_y` (sm-3:2413). -/
def E2 : ℝ³ := !₂[0, 1, 0]
/-- The chart `F(θ,u,v) = T(θ) + c(θ)(u E₁(T θ) + v E₂)` (sm-3:2414-2416). -/
def chart (p : ℝ × ℝ²) : ℝ³ := T p.1 + cT T p.1 • (p.2 0 • E1 (T p.1) + p.2 1 • E2)
/-- The tube `{‖w‖ ≤ r}` (closed) in the torus coordinates. -/
def tube (r : ℝ) : Set (ℝ × ℝ²) := {p | ‖p.2‖ ≤ r}

variable {T}

theorem aT_pos (hT : TransverseNeighborhoodHyp T) (θ : ℝ) : 0 < aT T θ := hT.transverse θ

theorem cT_pos (hT : TransverseNeighborhoodHyp T) (θ : ℝ) : 0 < cT T θ :=
  Real.sqrt_pos.2 (by have := aT_pos hT θ; linarith)

theorem cT_sq (hT : TransverseNeighborhoodHyp T) (θ : ℝ) : cT T θ ^ 2 = 2 * aT T θ :=
  Real.sq_sqrt (by have := aT_pos hT θ; linarith)

/-- `F(θ, 0) = T(θ)`. -/
theorem chart_core (θ : ℝ) : chart T (θ, 0) = T θ := by simp [chart]

/-! helpers for A1 -/
lemma ta_contDiff_deriv (hT : TransverseNeighborhoodHyp T) : ContDiff ℝ ∞ (deriv T) :=
  (contDiff_infty_iff_deriv.1 hT.circle.smooth).2

lemma ta_contDiff_coord3 (i : Fin 3) : ContDiff ℝ ∞ (fun p : ℝ³ => p i) :=
  ContactMotions.contDiff_coord i

lemma ta_contDiff_coord2 (i : Fin 2) : ContDiff ℝ ∞ (fun p : ℝ × ℝ² => p.2 i) :=
  (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i : ℝ² →L[ℝ] ℝ).contDiff.comp contDiff_snd

lemma ta_contDiff_aT (hT : TransverseNeighborhoodHyp T) : ContDiff ℝ ∞ (aT T) := by
  have h1 : ContDiff ℝ ∞ (fun θ => deriv T θ 2) := (ta_contDiff_coord3 2).comp (ta_contDiff_deriv hT)
  have h2 : ContDiff ℝ ∞ (fun θ => T θ 1) := (ta_contDiff_coord3 1).comp hT.circle.smooth
  have h3 : ContDiff ℝ ∞ (fun θ => deriv T θ 0) := (ta_contDiff_coord3 0).comp (ta_contDiff_deriv hT)
  exact h1.sub (h2.mul h3)

lemma ta_contDiff_cT (hT : TransverseNeighborhoodHyp T) : ContDiff ℝ ∞ (cT T) :=
  (contDiff_const.mul (ta_contDiff_aT hT)).sqrt fun θ => by have := aT_pos hT θ; positivity

lemma ta_E1_eq (q : ℝ³) : E1 q = (!₂[1, 0, 0] : ℝ³) + q 1 • (!₂[0, 0, 1] : ℝ³) := by
  ext i; fin_cases i <;> simp [E1]

lemma ta_contDiff_E1 : ContDiff ℝ ∞ E1 := by
  have : E1 = fun q => (!₂[1, 0, 0] : ℝ³) + q 1 • (!₂[0, 0, 1] : ℝ³) := funext ta_E1_eq
  rw [this]
  exact contDiff_const.add ((ta_contDiff_coord3 1).smul contDiff_const)

/-- LEAF A1.  `F` is `C^∞` (T smooth, `a > 0` so `c = √(2a)` smooth). -/
theorem contDiff_chart (hT : TransverseNeighborhoodHyp T) : ContDiff ℝ ∞ (chart T) := by
  have hTf : ContDiff ℝ ∞ (fun p : ℝ × ℝ² => T p.1) := hT.circle.smooth.comp contDiff_fst
  have hc : ContDiff ℝ ∞ (fun p : ℝ × ℝ² => cT T p.1) := (ta_contDiff_cT hT).comp contDiff_fst
  have hE1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ² => E1 (T p.1)) := ta_contDiff_E1.comp hTf
  exact hTf.add (hc.smul (((ta_contDiff_coord2 0).smul hE1).add
    ((ta_contDiff_coord2 1).smul contDiff_const)))

/-- The derivative of a `2π`-periodic map is `2π`-periodic. -/
lemma ta_deriv_periodic (hT : TransverseNeighborhoodHyp T) (θ : ℝ) :
    deriv T (θ + 2 * π) = deriv T θ := by
  calc deriv T (θ + 2 * π) = deriv (fun x => T (x + 2 * π)) θ :=
        (deriv_comp_add_const T (2 * π) θ).symm
    _ = deriv T θ := by congr 1; funext x; exact hT.circle.periodic x

/-- LEAF A2.  `a`, `c` and `F` are `2π`-periodic in `θ` (the derivative of a periodic map is
periodic; `Function.Periodic` has no `deriv` lemma at this pin, use `deriv_comp_add_const`). -/
theorem chart_periodic (hT : TransverseNeighborhoodHyp T) (θ : ℝ) (w : ℝ²) :
    aT T (θ + 2 * π) = aT T θ ∧ cT T (θ + 2 * π) = cT T θ ∧
      deriv T (θ + 2 * π) = deriv T θ ∧ chart T (θ + 2 * π, w) = chart T (θ, w) := by
  have hd := ta_deriv_periodic hT θ
  have hTp : T (θ + 2 * π) = T θ := hT.circle.periodic θ
  have ha : aT T (θ + 2 * π) = aT T θ := by simp only [aT, hd, hTp]
  have hc : cT T (θ + 2 * π) = cT T θ := by simp only [cT, ha]
  exact ⟨ha, hc, hd, by simp only [chart, hc, hTp]⟩

/-- `HasFDerivAt` form of A3, with the derivative as an explicit continuous linear map. -/
lemma ta_hasFDerivAt_chart (hT : TransverseNeighborhoodHyp T) (θ : ℝ) (w : ℝ²) :
    HasFDerivAt (chart T)
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv T θ)).comp (ContinuousLinearMap.fst ℝ ℝ ℝ²)
        + ((ContinuousLinearMap.toSpanSingleton ℝ (deriv (cT T) θ)).comp
              (ContinuousLinearMap.fst ℝ ℝ ℝ²)).smulRight (w 0 • E1 (T θ) + w 1 • E2)
        + cT T θ • (w 0 • (ContinuousLinearMap.toSpanSingleton ℝ (deriv T θ 1 • (!₂[0, 0, 1] : ℝ³))).comp
              (ContinuousLinearMap.fst ℝ ℝ ℝ²)
            + ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ ℝ²)).smulRight (E1 (T θ))
            + ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : ℝ² →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ ℝ²)).smulRight E2))
      (θ, w) := by
  have hTd : HasDerivAt T (deriv T θ) θ :=
    ((hT.circle.smooth.differentiable (by simp)) θ).hasDerivAt
  have hcd : HasDerivAt (cT T) (deriv (cT T) θ) θ :=
    (((ta_contDiff_cT hT).differentiable (by simp)) θ).hasDerivAt
  have hT1 := hTd.hasFDerivAt.comp (θ, w) (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ²) (p := (θ, w)))
  have hc1 := hcd.hasFDerivAt.comp (θ, w) (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ²) (p := (θ, w)))
  have hu := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ).hasFDerivAt.comp (θ, w)
    (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ²) (p := (θ, w)))
  have hv := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : ℝ² →L[ℝ] ℝ).hasFDerivAt.comp (θ, w)
    (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ²) (p := (θ, w)))
  -- `p ↦ T p.1 1`
  have hy := (ContactMotions.coordCLM 1).hasFDerivAt.comp (θ, w) hT1
  have hE1 : HasFDerivAt (fun p : ℝ × ℝ² => E1 (T p.1))
      (((ContactMotions.coordCLM 1).comp
        ((ContinuousLinearMap.toSpanSingleton ℝ (deriv T θ)).comp
          (ContinuousLinearMap.fst ℝ ℝ ℝ²))).smulRight (!₂[0, 0, 1] : ℝ³)) (θ, w) := by
    have h2 := (hasFDerivAt_const (!₂[1, 0, 0] : ℝ³) (θ, w)).add (hy.smul_const (!₂[0, 0, 1] : ℝ³))
    refine (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)).congr_fderiv ?_
    · exact ta_E1_eq _
    · simp
  have h := hT1.add (hc1.smul ((hu.smul hE1).add (hv.smul_const E2)))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)).congr_fderiv ?_
  · rfl
  · refine ContinuousLinearMap.ext fun ξ => ?_
    obtain ⟨τ, η⟩ := ξ
    ext i
    fin_cases i <;> simp [E1, E2] <;> ring

/-- LEAF A3.  Derivative of `F` (sm-3:2419): `DF(θ,w)(τ,η) = τ(T′ + c′(u E₁ + v E₂) + c u (0,0,y′))
+ c(η₀ E₁(T θ) + η₁ E₂)`; on the core the columns are `T′, cE₁, cE₂`. -/
theorem fderiv_chart (hT : TransverseNeighborhoodHyp T) (θ : ℝ) (w : ℝ²) (τ : ℝ) (η : ℝ²) :
    fderiv ℝ (chart T) (θ, w) (τ, η) =
      τ • (deriv T θ + deriv (cT T) θ • (w 0 • E1 (T θ) + w 1 • E2)
            + cT T θ • (w 0 • !₂[0, 0, deriv T θ 1]))
        + cT T θ • (η 0 • E1 (T θ) + η 1 • E2) := by
  rw [(ta_hasFDerivAt_chart hT θ w).fderiv]
  ext i
  fin_cases i <;> simp [E1, E2] <;> ring


/-- A bijective continuous linear map between our finite-dimensional spaces is (the coercion of) a
continuous linear equivalence. -/
lemma ta_exists_cle_of_bijective (f : ℝ × ℝ² →L[ℝ] ℝ³) (hf : Bijective f) :
    ∃ e : (ℝ × ℝ²) ≃L[ℝ] ℝ³, (e : ℝ × ℝ² →L[ℝ] ℝ³) = f := by
  exact ⟨(LinearEquiv.ofBijective (f : ℝ × ℝ² →ₗ[ℝ] ℝ³) hf).toContinuousLinearEquiv,
    ContinuousLinearMap.ext fun x => rfl⟩

/-- The bijective continuous linear maps form an open set (Banach open mapping, finite dimension). -/
lemma ta_isOpen_bijective : IsOpen {L : ℝ × ℝ² →L[ℝ] ℝ³ | Bijective L} := by
  have : {L : ℝ × ℝ² →L[ℝ] ℝ³ | Bijective L} =
      range (ContinuousLinearEquiv.toContinuousLinearMap : ((ℝ × ℝ²) ≃L[ℝ] ℝ³) → _) := by
    ext L
    constructor
    · intro h
      obtain ⟨e, he⟩ := ta_exists_cle_of_bijective L h
      exact ⟨e, he⟩
    · rintro ⟨e, rfl⟩
      exact e.bijective
  rw [this]
  exact ContinuousLinearEquiv.isOpen

/-- On the core the columns `T′, cE₁, cE₂` of `DF` are independent ("applying `α` to a relation
first kills the `T′` coefficient", sm-3:2420-2421). -/
lemma ta_injective_fderiv_core (hT : TransverseNeighborhoodHyp T) (θ : ℝ) :
    Injective (fderiv ℝ (chart T) (θ, (0 : ℝ²))) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨τ, η⟩ h
  rw [fderiv_chart hT θ 0 τ η] at h
  have h0 := congrArg (fun v : ℝ³ => v 0) h
  have h1 := congrArg (fun v : ℝ³ => v 1) h
  have h2 := congrArg (fun v : ℝ³ => v 2) h
  simp [E1, E2] at h0 h1 h2
  have ha : aT T θ ≠ 0 := (aT_pos hT θ).ne'
  have hc : cT T θ ≠ 0 := (cT_pos hT θ).ne'
  have hτa : τ * aT T θ = 0 := by
    simp only [aT, alpha]
    linear_combination h2 - T θ 1 * h0
  have hτ : τ = 0 := (mul_eq_zero.1 hτa).resolve_right ha
  subst hτ
  have hη0 : η 0 = 0 := by
    have : cT T θ * η 0 = 0 := by linear_combination h0
    exact (mul_eq_zero.1 this).resolve_left hc
  have hη1 : η 1 = 0 := by
    have : cT T θ * η 1 = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_left hc
  refine Prod.ext rfl ?_
  ext i
  fin_cases i
  · simpa using hη0
  · simpa using hη1

/-- On the core `DF` is bijective (injective + equal dimensions). -/
lemma ta_bijective_fderiv_core (hT : TransverseNeighborhoodHyp T) (θ : ℝ) :
    Bijective (fderiv ℝ (chart T) (θ, (0 : ℝ²))) := by
  have hinj := ta_injective_fderiv_core hT θ
  refine ⟨hinj, ?_⟩
  have hrank : Module.finrank ℝ (ℝ × ℝ²) = Module.finrank ℝ ℝ³ := by simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
    (f := (fderiv ℝ (chart T) (θ, (0 : ℝ²)) : ℝ × ℝ² →ₗ[ℝ] ℝ³))).1 hinj

/-- `DF` is `2π`-periodic in `θ`. -/
lemma ta_fderiv_chart_periodic (hT : TransverseNeighborhoodHyp T) (θ : ℝ) (w : ℝ²) :
    fderiv ℝ (chart T) (θ + 2 * π, w) = fderiv ℝ (chart T) (θ, w) := by
  have hdiff := (contDiff_chart hT).differentiable (by simp)
  have hshift : HasFDerivAt (fun p : ℝ × ℝ² => p + ((2 * π : ℝ), (0 : ℝ²)))
      (ContinuousLinearMap.id ℝ (ℝ × ℝ²)) (θ, w) := (hasFDerivAt_id _).add_const _
  have h : HasFDerivAt (chart T ∘ fun p : ℝ × ℝ² => p + ((2 * π : ℝ), (0 : ℝ²)))
      ((fderiv ℝ (chart T) (θ + 2 * π, w)).comp (ContinuousLinearMap.id ℝ (ℝ × ℝ²))) (θ, w) := by
    refine HasFDerivAt.comp (θ, w) ?_ hshift
    simpa using (hdiff (θ + 2 * π, w)).hasFDerivAt
  have hfun : (chart T ∘ fun p : ℝ × ℝ² => p + ((2 * π : ℝ), (0 : ℝ²))) = chart T := by
    funext p
    obtain ⟨θ', w'⟩ := p
    simp [(chart_periodic hT θ' w').2.2.2]
  rw [hfun] at h
  rw [h.fderiv]
  simp

/-- LEAF A4.  "The inverse function theorem and compactness give a common radius on which every
derivative is invertible" (sm-3:2421-2422): on the core `DF` is bijective (columns `T′, cE₁, cE₂`,
"applying `α` to a relation first kills the `T′` coefficient"), invertibility is open, the core is
compact modulo the period. -/
theorem exists_chart_bij_radius (hT : TransverseNeighborhoodHyp T) :
    ∃ ρ > 0, ∀ θ (w : ℝ²), ‖w‖ ≤ ρ → Function.Bijective (fderiv ℝ (chart T) (θ, w)) := by
  set S : Set (ℝ × ℝ²) := (fderiv ℝ (chart T)) ⁻¹' {L | Bijective L} with hS
  have hSopen : IsOpen S :=
    ta_isOpen_bijective.preimage ((contDiff_chart hT).continuous_fderiv (by simp))
  have hcore : Icc (0 : ℝ) (2 * π) ×ˢ ({0} : Set ℝ²) ⊆ S := by
    rintro ⟨θ, w⟩ ⟨_, hw⟩
    simp only [mem_singleton_iff] at hw
    subst hw
    exact ta_bijective_fderiv_core hT θ
  obtain ⟨u, v, -, hv, hsu, htv, huv⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hSopen hcore
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hv 0 (htv rfl)
  refine ⟨ε / 2, by positivity, fun θ w hw => ?_⟩
  have hper : Periodic (fun θ => fderiv ℝ (chart T) (θ, w)) (2 * π) :=
    fun θ => ta_fderiv_chart_periodic hT θ w
  obtain ⟨θ₀, hθ₀, hθeq⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos θ
  rw [hθeq]
  have hwv : w ∈ v := hball (by rw [Metric.mem_ball, dist_zero_right]; linarith)
  exact huv ⟨hsu (Ico_subset_Icc_self hθ₀), hwv⟩

/-- Every real number reduces into `[0, 2π]` by an integer multiple of `2π`. -/
lemma ta_exists_reduce (θ : ℝ) : ∃ k : ℤ, θ - 2 * π * k ∈ Icc 0 (2 * π) := by
  refine ⟨⌊θ / (2 * π)⌋, ?_, ?_⟩
  · have := Int.floor_le (θ / (2 * π))
    have h2 := Real.two_pi_pos
    rw [le_div_iff₀ h2] at this
    linarith
  · have := Int.lt_floor_add_one (θ / (2 * π))
    have h2 := Real.two_pi_pos
    rw [div_lt_iff₀ h2] at this
    nlinarith

/-- `F` is invariant under integer multiples of the period. -/
lemma ta_chart_periodic_int (hT : TransverseNeighborhoodHyp T) (θ : ℝ) (w : ℝ²) (k : ℤ) :
    chart T (θ + 2 * π * k, w) = chart T (θ, w) := by
  have hper : Periodic (fun θ => chart T (θ, w)) (2 * π) :=
    fun θ => (chart_periodic hT θ w).2.2.2
  rw [show 2 * π * k = k * (2 * π) by ring]
  exact hper.int_mul k θ

/-- LEAF A5.  The injectivity radius by the limiting argument (sm-3:2422-2427). -/
theorem exists_chart_inj_radius (hT : TransverseNeighborhoodHyp T) :
    ∃ ρ > 0, ∀ θ (w : ℝ²) θ' (w' : ℝ²), ‖w‖ ≤ ρ → ‖w'‖ ≤ ρ →
      chart T (θ, w) = chart T (θ', w') → w = w' ∧ ∃ k : ℤ, θ' = θ + 2 * π * k := by
  by_contra hcon
  push Not at hcon
  -- bad pairs with parameters reduced to `[0, 2π]` and disc radii `≤ 1/(n+1)`
  have hbad : ∀ n : ℕ, ∃ q : (ℝ × ℝ²) × (ℝ × ℝ²), q.1.1 ∈ Icc 0 (2 * π) ∧ q.2.1 ∈ Icc 0 (2 * π) ∧
      ‖q.1.2‖ ≤ 1 / ((n : ℝ) + 1) ∧ ‖q.2.2‖ ≤ 1 / ((n : ℝ) + 1) ∧ chart T q.1 = chart T q.2 ∧
      ¬ (q.1.2 = q.2.2 ∧ ∃ k : ℤ, q.2.1 = q.1.1 + 2 * π * k) := by
    intro n
    obtain ⟨θ, w, θ', w', hw, hw', heq, hne⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨m, hm⟩ := ta_exists_reduce θ
    obtain ⟨m', hm'⟩ := ta_exists_reduce θ'
    refine ⟨((θ - 2 * π * m, w), (θ' - 2 * π * m', w')), hm, hm', hw, hw', ?_, ?_⟩
    · show chart T (θ - 2 * π * m, w) = chart T (θ' - 2 * π * m', w')
      have e1 : chart T (θ - 2 * π * m, w) = chart T (θ, w) := by
        rw [← ta_chart_periodic_int hT (θ - 2 * π * m) w m, sub_add_cancel]
      have e2 : chart T (θ' - 2 * π * m', w') = chart T (θ', w') := by
        rw [← ta_chart_periodic_int hT (θ' - 2 * π * m') w' m', sub_add_cancel]
      rw [e1, e2, heq]
    · rintro ⟨hww, k, hk⟩
      refine hne hww (k + m' - m) ?_
      simp only at hk
      push_cast
      linarith
  choose q hq using hbad
  -- convergent subsequences of the circle parameters
  obtain ⟨a, -, φ, hφ, hφa⟩ := isCompact_Icc.tendsto_subseq (x := fun n => (q n).1.1) fun n => (hq n).1
  obtain ⟨a', -, ψ, hψ, hψa'⟩ :=
    isCompact_Icc.tendsto_subseq (x := fun n => (q (φ n)).2.1) fun n => (hq (φ n)).2.1
  set σ : ℕ → ℕ := φ ∘ ψ with hσdef
  have hσ : StrictMono σ := hφ.comp hψ
  have hθ : Filter.Tendsto (fun n => (q (σ n)).1.1) Filter.atTop (𝓝 a) :=
    hφa.comp hψ.tendsto_atTop
  have hθ' : Filter.Tendsto (fun n => (q (σ n)).2.1) Filter.atTop (𝓝 a') := hψa'
  have hbound : ∀ n : ℕ, 1 / ((σ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := fun n => by
    apply one_div_le_one_div_of_le (by positivity)
    have := hσ.id_le n
    simp only [id] at this
    exact_mod_cast Nat.succ_le_succ this
  have hw : Filter.Tendsto (fun n => (q (σ n)).1.2) Filter.atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hq (σ n)).2.2.1.trans (hbound n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hw' : Filter.Tendsto (fun n => (q (σ n)).2.2) Filter.atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hq (σ n)).2.2.2.1.trans (hbound n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  -- the limiting circle parameters coincide modulo the period
  have hcont := (contDiff_chart hT).continuous
  have hlim1 : Filter.Tendsto (fun n => chart T (q (σ n)).1) Filter.atTop (𝓝 (chart T (a, 0))) :=
    (hcont.tendsto (a, 0)).comp (hθ.prodMk_nhds hw)
  have hlim2 : Filter.Tendsto (fun n => chart T (q (σ n)).2) Filter.atTop (𝓝 (chart T (a', 0))) :=
    (hcont.tendsto (a', 0)).comp (hθ'.prodMk_nhds hw')
  have hlim2' : Filter.Tendsto (fun n => chart T (q (σ n)).1) Filter.atTop (𝓝 (chart T (a', 0))) :=
    hlim2.congr fun n => ((hq (σ n)).2.2.2.2.1).symm
  have hTa : T a = T a' := by
    have := tendsto_nhds_unique hlim1 hlim2'
    rwa [chart_core, chart_core] at this
  obtain ⟨k, hk⟩ := hT.circle.injective a a' hTa
  -- local injectivity of `F` at `(a, 0)` (inverse function theorem)
  obtain ⟨e, he⟩ := ta_exists_cle_of_bijective _ (ta_bijective_fderiv_core hT a)
  have hs : HasStrictFDerivAt (chart T) (e : ℝ × ℝ² →L[ℝ] ℝ³) (a, (0 : ℝ²)) := by
    rw [he]
    exact (contDiff_chart hT).contDiffAt.hasStrictFDerivAt (by simp)
  set Ph := hs.toOpenPartialHomeomorph (chart T) with hPh
  have hsrc : (a, (0 : ℝ²)) ∈ Ph.source := hs.mem_toOpenPartialHomeomorph_source
  have hinj : InjOn (chart T) Ph.source := by
    have := Ph.injOn
    rwa [hs.toOpenPartialHomeomorph_coe] at this
  have hnhds : Ph.source ∈ 𝓝 (a, (0 : ℝ²)) := Ph.open_source.mem_nhds hsrc
  have hev1 : ∀ᶠ n in Filter.atTop, ((q (σ n)).1.1, (q (σ n)).1.2) ∈ Ph.source :=
    (hθ.prodMk_nhds hw).eventually_mem hnhds
  have hθ'' : Filter.Tendsto (fun n => (q (σ n)).2.1 - 2 * π * k) Filter.atTop (𝓝 a) := by
    have := hθ'.sub_const (2 * π * k)
    rwa [hk, add_sub_cancel_right] at this
  have hev2 : ∀ᶠ n in Filter.atTop, ((q (σ n)).2.1 - 2 * π * k, (q (σ n)).2.2) ∈ Ph.source :=
    (hθ''.prodMk_nhds hw').eventually_mem hnhds
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  have heqn : chart T ((q (σ n)).1.1, (q (σ n)).1.2) =
      chart T ((q (σ n)).2.1 - 2 * π * k, (q (σ n)).2.2) := by
    rw [← ta_chart_periodic_int hT ((q (σ n)).2.1 - 2 * π * k) _ k, sub_add_cancel]
    exact (hq (σ n)).2.2.2.2.1
  have hpair := hinj hn1 hn2 heqn
  rw [Prod.ext_iff] at hpair
  obtain ⟨hp1, hp2⟩ := hpair
  simp only at hp1 hp2
  exact (hq (σ n)).2.2.2.2.2 ⟨hp2, k, by linarith⟩

/-- LEAF A6.  On a tube where `DF` is bijective, `F` maps open sets to open sets (IFT:
`HasStrictFDerivAt.map_nhds_eq_of_equiv`). -/
theorem chart_isOpen_image (hT : TransverseNeighborhoodHyp T) {ρ : ℝ}
    (hρ : ∀ θ (w : ℝ²), ‖w‖ ≤ ρ → Function.Bijective (fderiv ℝ (chart T) (θ, w)))
    {U : Set (ℝ × ℝ²)} (hU : IsOpen U) (hUρ : U ⊆ tube ρ) : IsOpen (chart T '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨e, he⟩ := ta_exists_cle_of_bijective _ (hρ x.1 x.2 (hUρ hx))
  have hs : HasStrictFDerivAt (chart T) (e : ℝ × ℝ² →L[ℝ] ℝ³) x := by
    rw [he]
    exact (contDiff_chart hT).contDiffAt.hasStrictFDerivAt (by simp)
  rw [← hs.map_nhds_eq_of_equiv]
  exact Filter.image_mem_map (hU.mem_nhds hx)

end chart

/-! ### Unit B — the forms and the Moser field in coordinates (sm-3:2429-2453; memo §1.2) -/

section forms
variable (T : ℝ → ℝ³)

/-- `g(θ,u,v) = (c u y′ − c v x′ − c c′ u v)/a`, so that `F^*α = a((1+g)dθ − 2v du)` exactly
(memo §1.2). -/
def gfun (p : ℝ × ℝ²) : ℝ :=
  (cT T p.1 * p.2 0 * deriv T p.1 1 - cT T p.1 * p.2 1 * deriv T p.1 0
    - cT T p.1 * deriv (cT T) p.1 * p.2 0 * p.2 1) / aT T p.1
/-- `g_u = ∂_u g`. -/
def gu (p : ℝ × ℝ²) : ℝ := fderiv ℝ (gfun T) p (0, EuclideanSpace.single 0 1)
/-- `g_v = ∂_v g`. -/
def gv (p : ℝ × ℝ²) : ℝ := fderiv ℝ (gfun T) p (0, EuclideanSpace.single 1 1)
/-- `P = α_t(∂_θ) = 1 + t g`. -/
def Pf (t : ℝ) (p : ℝ × ℝ²) : ℝ := 1 + t * gfun T p
/-- `N = P · D_t = 2P − t g_u (1−t) u − t g_v (1+t) v` (`D_t = dα_t(X₁,X₂)` of sm-3:2445). -/
def Nf (t : ℝ) (p : ℝ × ℝ²) : ℝ :=
  2 * Pf T t p - t * gu T p * ((1 - t) * p.2 0) - t * gv T p * ((1 + t) * p.2 1)
/-- `α_t = (1−t)α₀ + tβ = P dθ − (1+t) v du + (1−t) u dv` at `p` on `w` (sm-3:2434). -/
def alphaT (t : ℝ) (p w : ℝ × ℝ²) : ℝ :=
  Pf T t p * w.1 - (1 + t) * p.2 1 * w.2 0 + (1 - t) * p.2 0 * w.2 1
/-- `ν = β − α₀ = g dθ − v du − u dv` (sm-3:2440). -/
def nuF (p w : ℝ × ℝ²) : ℝ := gfun T p * w.1 - p.2 1 * w.2 0 - p.2 0 * w.2 1
/-- `dα_t(x, y) = 2(x_u y_v − x_v y_u) + t g_u (x_u y_θ − x_θ y_u) + t g_v (x_v y_θ − x_θ y_v)`. -/
def dalphaT (t : ℝ) (p x y : ℝ × ℝ²) : ℝ :=
  2 * (x.2 0 * y.2 1 - x.2 1 * y.2 0) + t * gu T p * (x.2 0 * y.1 - x.1 * y.2 0)
    + t * gv T p * (x.2 1 * y.1 - x.1 * y.2 1)
/-- The Moser field `V_t = (ν(X₁)X₂ − ν(X₂)X₁)/D_t` (sm-3:2446) in closed form
`V_t = (2uv/N, u(1+g)/N, v(g−1)/N)` (memo §1.2, `MoserIdentityCheck.Vθ_eq/Vu_eq/Vv_eq`). -/
def Vf (t : ℝ) (p : ℝ × ℝ²) : ℝ × ℝ² :=
  (2 * p.2 0 * p.2 1 / Nf T t p,
    !₂[p.2 0 * (1 + gfun T p) / Nf T t p, p.2 1 * (gfun T p - 1) / Nf T t p])
/-- `μ_t = (ν + ι_{V_t}dα_t)(∂_θ)/α_t(∂_θ)` (sm-3:2464-2465) in closed form. -/
def muf (t : ℝ) (p : ℝ × ℝ²) : ℝ :=
  (gfun T p + t * (gu T p * p.2 0 * (1 + gfun T p) + gv T p * p.2 1 * (gfun T p - 1)) / Nf T t p)
    / Pf T t p

variable {T}

lemma vec2_zero (a b : ℝ) : (!₂[a, b] : ℝ²) 0 = a := by simp
lemma vec2_one (a b : ℝ) : (!₂[a, b] : ℝ²) 1 = b := by simp

/-- `α_0 = α₀` (sm-3:2402). -/
theorem alphaT_zero (p w : ℝ × ℝ²) : alphaT T 0 p w = alpha0 p.2 w.1 w.2 := by
  simp only [alphaT, alpha0, Pf]; ring

/-- `α_1 = β = (1+g)dθ − 2v du`. -/
theorem alphaT_one (p w : ℝ × ℝ²) :
    alphaT T 1 p w = (1 + gfun T p) * w.1 - 2 * p.2 1 * w.2 0 := by
  simp only [alphaT, Pf]; ring

/-- `g = 0` on the core. -/
theorem gfun_core (θ : ℝ) : gfun T (θ, 0) = 0 := by simp [gfun]

theorem Pf_core (t θ : ℝ) : Pf T t (θ, 0) = 1 := by simp [Pf, gfun_core]

theorem Nf_core (t θ : ℝ) : Nf T t (θ, 0) = 2 := by simp [Nf, Pf_core]

/-- "The vector field `V_t` vanishes on the core" (sm-3:2453). -/
theorem Vf_core (t θ : ℝ) : Vf T t (θ, 0) = 0 := by
  simp only [Vf, Prod.mk_eq_zero]
  refine ⟨by simp, ?_⟩
  ext i; fin_cases i <;> simp

/-- `α_t(V_t) = 0` (sm-3:2468 "since `α_t(V_t) = 0`"). -/
theorem alphaT_Vf (t : ℝ) (p : ℝ × ℝ²) (hP : Pf T t p ≠ 0) (hN : Nf T t p ≠ 0) :
    alphaT T t p (Vf T t p) = 0 := by
  have hPdef : Pf T t p = 1 + t * gfun T p := rfl
  have hNdef : Nf T t p = 2 * Pf T t p - t * gu T p * ((1 - t) * p.2 0)
      - t * gv T p * ((1 + t) * p.2 1) := rfl
  simp only [alphaT, Vf, vec2_zero, vec2_one]
  generalize Pf T t p = PP at *
  generalize Nf T t p = NN at *
  field_simp
  subst hPdef hNdef
  ring

/-- **The Moser identity** `ν(w) + dα_t(V_t, w) = μ_t α_t(w)` (sm-3:2464-2466), a rational identity
(`MoserIdentityCheck.moser_identity` transported to the concrete `g`). -/
theorem moser_identity (t : ℝ) (p w : ℝ × ℝ²) (hP : Pf T t p ≠ 0) (hN : Nf T t p ≠ 0) :
    nuF T p w + dalphaT T t p (Vf T t p) w = muf T t p * alphaT T t p w := by
  have hPdef : Pf T t p = 1 + t * gfun T p := rfl
  have hNdef : Nf T t p = 2 * Pf T t p - t * gu T p * ((1 - t) * p.2 0)
      - t * gv T p * ((1 + t) * p.2 1) := rfl
  simp only [nuF, dalphaT, Vf, muf, alphaT, vec2_zero, vec2_one]
  generalize Pf T t p = PP at *
  generalize Nf T t p = NN at *
  field_simp
  subst hPdef hNdef
  ring

/-- LEAF B1.  `g` is `C^∞` (quotient of smooth functions by `a > 0`). -/
theorem contDiff_gfun (hT : TransverseNeighborhoodHyp T) : ContDiff ℝ ∞ (gfun T) := by
  sorry

theorem contDiff_gu (hT : TransverseNeighborhoodHyp T) : ContDiff ℝ ∞ (gu T) :=
  ((contDiff_gfun hT).fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_gv (hT : TransverseNeighborhoodHyp T) : ContDiff ℝ ∞ (gv T) :=
  ((contDiff_gfun hT).fderiv_right (by simp)).clm_apply contDiff_const

/-- LEAF B2.  `g, g_u, g_v` are `2π`-periodic in `θ`. -/
theorem gfun_periodic (hT : TransverseNeighborhoodHyp T) (θ : ℝ) (w : ℝ²) :
    gfun T (θ + 2 * π, w) = gfun T (θ, w) ∧ gu T (θ + 2 * π, w) = gu T (θ, w) ∧
      gv T (θ + 2 * π, w) = gv T (θ, w) := by
  sorry

theorem Vf_periodic (hT : TransverseNeighborhoodHyp T) (t θ : ℝ) (w : ℝ²) :
    Vf T t (θ + 2 * π, w) = Vf T t (θ, w) := by
  obtain ⟨h1, h2, h3⟩ := gfun_periodic hT θ w
  simp only [Vf, Nf, Pf, h1, h2, h3]

theorem muf_periodic (hT : TransverseNeighborhoodHyp T) (t θ : ℝ) (w : ℝ²) :
    muf T t (θ + 2 * π, w) = muf T t (θ, w) := by
  obtain ⟨h1, h2, h3⟩ := gfun_periodic hT θ w
  simp only [muf, Nf, Pf, h1, h2, h3]

/-- LEAF B3.  `dα_t` is the antisymmetrised `p`-derivative of `α_t`
(`dα_t(x,y) = D_pα_t[x](y) − D_pα_t[y](x)`; the `g_θ` terms cancel). -/
theorem dalphaT_eq (hT : TransverseNeighborhoodHyp T) (t : ℝ) (p x y : ℝ × ℝ²) :
    dalphaT T t p x y =
      fderiv ℝ (fun q => alphaT T t q y) p x - fderiv ℝ (fun q => alphaT T t q x) p y := by
  sorry

/-- LEAF B4.  `P > 1/2` and `N > 1` on a uniform tube for `|t| ≤ 4` (`P = 1`, `N = 2` on the
core; continuity, periodicity, compactness of `[−4,4] × [0,2π]`) — sm-3:2437-2439. -/
theorem exists_PN_radius (hT : TransverseNeighborhoodHyp T) :
    ∃ ρ > 0, ∀ t ∈ Icc (-4 : ℝ) 4, ∀ θ (w : ℝ²), ‖w‖ ≤ ρ →
      1 / 2 < Pf T t (θ, w) ∧ 1 < Nf T t (θ, w) := by
  sorry

/-- A good radius: `ρ ≤ 1`, the chart is an injective local diffeomorphism on the `2ρ`-tube, and
`P > 1/2`, `N > 1` there for `|t| ≤ 4` (so `V_t`, `μ_t` are smooth on the `2ρ`-tube). -/
structure GoodRadius (T : ℝ → ℝ³) (ρ : ℝ) : Prop where
  pos : 0 < ρ
  le_one : ρ ≤ 1
  chart_bij : ∀ θ (w : ℝ²), ‖w‖ ≤ 2 * ρ → Function.Bijective (fderiv ℝ (chart T) (θ, w))
  chart_inj : ∀ θ (w : ℝ²) θ' (w' : ℝ²), ‖w‖ ≤ 2 * ρ → ‖w'‖ ≤ 2 * ρ →
    chart T (θ, w) = chart T (θ', w') → w = w' ∧ ∃ k : ℤ, θ' = θ + 2 * π * k
  P_pos : ∀ t ∈ Icc (-4 : ℝ) 4, ∀ θ (w : ℝ²), ‖w‖ ≤ 2 * ρ → 1 / 2 < Pf T t (θ, w)
  N_pos : ∀ t ∈ Icc (-4 : ℝ) 4, ∀ θ (w : ℝ²), ‖w‖ ≤ 2 * ρ → 1 < Nf T t (θ, w)

/-- A good radius exists (from A4, A5, B4). -/
theorem exists_goodRadius (hT : TransverseNeighborhoodHyp T) : ∃ ρ, GoodRadius T ρ := by
  obtain ⟨ρ₁, hρ₁, h₁⟩ := exists_chart_bij_radius hT
  obtain ⟨ρ₂, hρ₂, h₂⟩ := exists_chart_inj_radius hT
  obtain ⟨ρ₃, hρ₃, h₃⟩ := exists_PN_radius hT
  set ρ := min (min ρ₁ ρ₂) (min ρ₃ 1) / 2 with hρdef
  have m1 : min (min ρ₁ ρ₂) (min ρ₃ 1) ≤ min ρ₁ ρ₂ := min_le_left _ _
  have m2 : min (min ρ₁ ρ₂) (min ρ₃ 1) ≤ min ρ₃ 1 := min_le_right _ _
  have m3 : min ρ₁ ρ₂ ≤ ρ₁ := min_le_left _ _
  have m4 : min ρ₁ ρ₂ ≤ ρ₂ := min_le_right _ _
  have m5 : min ρ₃ 1 ≤ ρ₃ := min_le_left _ _
  have m6 : min ρ₃ 1 ≤ 1 := min_le_right _ _
  have hρpos : 0 < ρ := by positivity
  have e1 : 2 * ρ ≤ ρ₁ := by rw [hρdef]; linarith
  have e2 : 2 * ρ ≤ ρ₂ := by rw [hρdef]; linarith
  have e3 : 2 * ρ ≤ ρ₃ := by rw [hρdef]; linarith
  have e4 : ρ ≤ 1 := by rw [hρdef]; linarith
  refine ⟨ρ, hρpos, e4, fun θ w hw => h₁ θ w (hw.trans e1),
    fun θ w θ' w' hw hw' => h₂ θ w θ' w' (hw.trans e2) (hw'.trans e2),
    fun t ht θ w hw => (h₃ t ht θ w (hw.trans e3)).1,
    fun t ht θ w hw => (h₃ t ht θ w (hw.trans e3)).2⟩

/-- LEAF B5.  `V_t` is smooth in `(t, p)` on `|t| < 4`, `‖w‖ < 2ρ` (`N ≠ 0` there). -/
theorem contDiffOn_Vf (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) :
    ContDiffOn ℝ ∞ (uncurry (Vf T)) (Ioo (-4 : ℝ) 4 ×ˢ {p : ℝ × ℝ² | ‖p.2‖ < 2 * ρ}) := by
  sorry

/-- LEAF B6.  "Its norm is at most `C√(u²+v²)`" (sm-3:2458-2459): from the closed forms,
`N > 1` and boundedness of `g` on the tube. -/
theorem exists_Vf_bound (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc (-4 : ℝ) 4, ∀ θ (w : ℝ²), ‖w‖ ≤ 2 * ρ →
      ‖Vf T t (θ, w)‖ ≤ C * ‖w‖ := by
  sorry

end forms

/-! ### Unit C — the time-dependent Moser flow by suspension (sm-3:2454-2463; memo §1.3 S6) -/

section flow
variable (T : ℝ → ℝ³)

/-- `χ_τ(τ) = 1` for `|τ| ≤ 2`, `0` for `|τ| ≥ 3`. -/
def chiTau (τ : ℝ) : ℝ := cut1 4 9 (τ ^ 2)
/-- `χ_θ(θ) = 1` for `|θ| ≤ 20`, `0` for `|θ| ≥ 21`. -/
def chiTheta (θ : ℝ) : ℝ := cut1 400 441 (θ ^ 2)
/-- `χ_w(w) = 1` for `‖w‖ ≤ ρ/2`, `0` for `‖w‖ ≥ ρ`. -/
def chiW (ρ : ℝ) (w : ℝ²) : ℝ := cut1 (ρ ^ 2 / 4) (ρ ^ 2) (‖w‖ ^ 2)
/-- The spatial cutoff. -/
def cutoff (ρ : ℝ) (p : ℝ × ℝ²) : ℝ := chiTheta p.1 * chiW ρ p.2
/-- The suspended, cut-off Moser field on `ℝ × (ℝ × ℝ²)`:
`Y(τ, p) = (χ_τ(τ), χ_τ(τ) cutoff(p) V_τ(p))`; compactly supported and `C^∞`. -/
def Yfield (ρ : ℝ) (q : ℝ × (ℝ × ℝ²)) : ℝ × (ℝ × ℝ²) :=
  (chiTau q.1, (chiTau q.1 * cutoff ρ q.2) • Vf T q.1 q.2)
/-- Its global flow `Θ`. -/
def Theta (ρ : ℝ) : ℝ → ℝ × (ℝ × ℝ²) → ℝ × (ℝ × ℝ²) :=
  Classical.epsilon (IsGlobalFlow (Yfield T ρ))
/-- The Moser flow `Φ_t(p) = pr₂ Θ_t(0, p)` (sm-3:2463). -/
def Phi (ρ : ℝ) (t : ℝ) (p : ℝ × ℝ²) : ℝ × ℝ² := (Theta T ρ t (0, p)).2

variable {T}

lemma chiTau_eq_one {τ : ℝ} (h : |τ| ≤ 2) : chiTau τ = 1 := by
  unfold chiTau; apply cut1_of_le (by norm_num)
  nlinarith [abs_nonneg τ, sq_abs τ]

lemma chiTheta_eq_one {θ : ℝ} (h : |θ| ≤ 20) : chiTheta θ = 1 := by
  unfold chiTheta; apply cut1_of_le (by norm_num)
  nlinarith [abs_nonneg θ, sq_abs θ]

lemma chiW_eq_one {ρ : ℝ} (hρ : 0 < ρ) {w : ℝ²} (h : ‖w‖ ≤ ρ / 2) : chiW ρ w = 1 := by
  unfold chiW; apply cut1_of_le (by nlinarith)
  nlinarith [norm_nonneg w]

lemma cutoff_eq_one {ρ : ℝ} (hρ : 0 < ρ) {p : ℝ × ℝ²} (hθ : |p.1| ≤ 20) (hw : ‖p.2‖ ≤ ρ / 2) :
    cutoff ρ p = 1 := by
  simp [cutoff, chiTheta_eq_one hθ, chiW_eq_one hρ hw]

/-- LEAF C1.  `Y` is `C^∞` (B5: `V` smooth where the cutoff is nonzero; zero elsewhere). -/
theorem contDiff_Yfield (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) :
    ContDiff ℝ ∞ (Yfield T ρ) := by
  sorry

/-- LEAF C2.  `Y` has compact support (`|τ| ≤ 3`, `|θ| ≤ 21`, `‖w‖ ≤ ρ`). -/
theorem hasCompactSupport_Yfield {ρ : ℝ} (hρ : GoodRadius T ρ) :
    HasCompactSupport (Yfield T ρ) := by
  sorry

/-- `Θ` is a global flow of `Y` (row 86's existence theorem). -/
theorem isGlobalFlow_Theta (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) :
    IsGlobalFlow (Yfield T ρ) (Theta T ρ) :=
  Classical.epsilon_spec (ContactMotions.exists_isGlobalFlow_of_hasCompactSupport'
    (hasCompactSupport_Yfield hρ) ((contDiff_Yfield hT hρ).of_le (by simp)))

/-- `Θ` is jointly `C^∞` — **smooth dependence** (row 86, `ContactMotions.contDiff_uncurry`). -/
theorem contDiff_Theta (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) :
    ContDiff ℝ ∞ (uncurry (Theta T ρ)) :=
  ContactMotions.contDiff_uncurry (contDiff_Yfield hT hρ) (hasCompactSupport_Yfield hρ)
    (isGlobalFlow_Theta hT hρ)

theorem contDiff_Phi (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) (t : ℝ) :
    ContDiff ℝ ∞ (Phi T ρ t) :=
  contDiff_snd.comp ((contDiff_Theta hT hρ).comp
    (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)))

theorem contDiff_uncurry_Phi (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) :
    ContDiff ℝ ∞ (uncurry (Phi T ρ)) :=
  contDiff_snd.comp ((contDiff_Theta hT hρ).comp
    (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)))

theorem Phi_zero (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) (p : ℝ × ℝ²) :
    Phi T ρ 0 p = p := by
  simp [Phi, (isGlobalFlow_Theta hT hρ).zero]

/-- LEAF C3.  The suspended time coordinate is the time: `pr₁ Θ_t(0,p) = t` for `|t| ≤ 2`
(`τ′ = χ_τ(τ)`, `τ(0) = 0`, and `σ(t) = t` solves the same ODE while `|σ| ≤ 2`; uniqueness). -/
theorem Theta_fst (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) :
    ∀ t ∈ Icc (-2 : ℝ) 2, ∀ p, (Theta T ρ t (0, p)).1 = t := by
  sorry

/-- LEAF C4.  The ODE of `Φ` for `|t| < 2`: `∂_tΦ_t(p) = cutoff(Φ_t p) · V_t(Φ_t p)` (from the
flow ODE of `Θ`, C3 and `χ_τ = 1`). -/
theorem hasDerivAt_Phi (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ)
    (p : ℝ × ℝ²) : ∀ t ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun t => Phi T ρ t p) (cutoff ρ (Phi T ρ t p) • Vf T t (Phi T ρ t p)) t := by
  sorry

/-- LEAF C5.  `Φ_1` is a diffeomorphism of `ℝ × ℝ²` with inverse `p′ ↦ pr₂ Θ_{−1}(1, p′)`
(group law of `Θ` and C3). -/
theorem Phi_one_inverse (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) :
    ∃ Ψ : ℝ × ℝ² → ℝ × ℝ², ContDiff ℝ ∞ Ψ ∧ LeftInverse Ψ (Phi T ρ 1) ∧
      RightInverse Ψ (Phi T ρ 1) := by
  sorry

/-- The a-priori property of an initial radius `δ₁` (sm-3:2459-2463): trajectories from
`|θ₀| ≤ 4π`, `‖w₀‖ < δ₁` stay for `t ∈ [−1, 2]` in `‖w‖ ≤ ρ/4`, `|θ − θ₀| ≤ 1` — where the cutoff
is `1` with margin. -/
def AprioriRadius (T : ℝ → ℝ³) (ρ δ₁ : ℝ) : Prop :=
  0 < δ₁ ∧ ∀ θ₀ ∈ Icc (-(4 * π)) (4 * π), ∀ w₀ : ℝ², ‖w₀‖ < δ₁ → ∀ t ∈ Icc (-1 : ℝ) 2,
    ‖(Phi T ρ t (θ₀, w₀)).2‖ ≤ ρ / 4 ∧ |(Phi T ρ t (θ₀, w₀)).1 - θ₀| ≤ 1

/-- LEAF C6.  Grönwall a-priori bound (sm-3:2456-2463): `‖V^w‖ ≤ C‖w‖` gives
`‖w(t)‖ ≤ e^{3C}‖w₀‖`, `|θ′| = |2uv/N| ≤ 2‖w‖² ≤ ρ²/8 ≤ 1/8`; continuation keeps the trajectory
where `cutoff = 1`, so it solves the uncut ODE. -/
theorem exists_aprioriRadius (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) :
    ∃ δ₁, AprioriRadius T ρ δ₁ := by
  sorry

theorem cutoff_along (hρ : GoodRadius T ρ) {δ₁ : ℝ} (hδ : AprioriRadius T ρ δ₁)
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(4 * π)) (4 * π)) {w₀ : ℝ²} (hw₀ : ‖w₀‖ < δ₁)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 2) : cutoff ρ (Phi T ρ t (θ₀, w₀)) = 1 := by
  obtain ⟨h1, h2⟩ := hδ.2 θ₀ hθ₀ w₀ hw₀ t ht
  apply cutoff_eq_one hρ.pos
  · have hπ : π ≤ 4 := Real.pi_le_four
    have := abs_sub_abs_le_abs_sub (Phi T ρ t (θ₀, w₀)).1 θ₀
    have h4 : |θ₀| ≤ 4 * π := abs_le.2 ⟨by linarith [hθ₀.1], hθ₀.2⟩
    linarith
  · linarith [hρ.pos]

/-- LEAF C7.  Periodicity of the flow (sm-3:2420 "well defined on the circle"): for
`|θ₀| ≤ 2π`, `‖w₀‖ < δ₁`, `Φ_t(θ₀ + 2π, w₀) = Φ_t(θ₀, w₀) + (2π, 0)` on `[−1, 2]`
(both sides solve the uncut ODE by C6 and `Vf_periodic`; uniqueness). -/
theorem Phi_shift (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) {δ₁ : ℝ}
    (hδ : AprioriRadius T ρ δ₁) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(2 * π)) (2 * π)) {w₀ : ℝ²}
    (hw₀ : ‖w₀‖ < δ₁) : ∀ t ∈ Icc (-1 : ℝ) 2,
      Phi T ρ t (θ₀ + 2 * π, w₀) = ((Phi T ρ t (θ₀, w₀)).1 + 2 * π, (Phi T ρ t (θ₀, w₀)).2) := by
  sorry

/-- LEAF C8.  The core is fixed: `Φ_t(θ, 0) = (θ, 0)` for `|θ| ≤ 4π` (`V_t = 0` on the core,
`Vf_core`; uniqueness) — sm-3:2463 "fixing the core". -/
theorem Phi_core (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) {θ : ℝ}
    (hθ : θ ∈ Icc (-(4 * π)) (4 * π)) : ∀ t ∈ Icc (-1 : ℝ) 2, Phi T ρ t (θ, 0) = (θ, 0) := by
  sorry

/-- LEAF C9.  The variational equation along good trajectories (row 86's
`hasDerivAt_fderiv_flow` for the second component of the suspended flow; `cutoff = 1` near the
trajectory by C6): `∂_t DΦ_t(p) = DV_t(Φ_t p) ∘ DΦ_t(p)` for `t ∈ (−1, 2)`. -/
theorem hasDerivAt_fderiv_Phi (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ)
    {δ₁ : ℝ} (hδ : AprioriRadius T ρ δ₁) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(4 * π)) (4 * π)) {w₀ : ℝ²}
    (hw₀ : ‖w₀‖ < δ₁) : ∀ t ∈ Ioo (-1 : ℝ) 2,
      HasDerivAt (fun t => fderiv ℝ (Phi T ρ t) (θ₀, w₀))
        ((fderiv ℝ (Vf T t) (Phi T ρ t (θ₀, w₀))).comp (fderiv ℝ (Phi T ρ t) (θ₀, w₀))) t := by
  sorry

end flow

/-! ### Unit D — the model neighbourhood `H = F ∘ Φ_1` (sm-3:2464-2475) -/

section model
variable (T : ℝ → ℝ³)

/-- Reduction of `θ` to `[−π, π]`: `θ − 2π·round(θ/2π)`. -/
def redθ (θ : ℝ) : ℝ := θ - 2 * π * round (θ / (2 * π))
/-- The model map `H(θ, w) = F(Φ_1(red θ, w))` (sm-3:2472; the reduction makes `H` periodic, C7
makes it smooth). -/
def Hmap (ρ : ℝ) (p : ℝ × ℝ²) : ℝ³ := chart T (Phi T ρ 1 (redθ p.1, p.2))
/-- The conformal factor `h = a(θ(Φ_1 p)) · exp ∫₀¹ μ_t(Φ_t p) dt` (sm-3:2472-2474). -/
def hfun (ρ : ℝ) (p : ℝ × ℝ²) : ℝ :=
  aT T (Phi T ρ 1 (redθ p.1, p.2)).1 *
    Real.exp (∫ t in (0 : ℝ)..1, muf T t (Phi T ρ t (redθ p.1, p.2)))

variable {T}

lemma redθ_add (θ : ℝ) : redθ (θ + 2 * π) = redθ θ := by
  unfold redθ
  have : (θ + 2 * π) / (2 * π) = θ / (2 * π) + 1 := by field_simp
  rw [this, round_add_one]; push_cast; ring

lemma abs_redθ_le (θ : ℝ) : |redθ θ| ≤ π := by
  unfold redθ
  have h := abs_sub_round (θ / (2 * π))
  have hπ : 0 < 2 * π := by positivity
  have : θ - 2 * π * round (θ / (2 * π)) = 2 * π * (θ / (2 * π) - round (θ / (2 * π))) := by
    field_simp
  rw [this, abs_mul, abs_of_pos hπ]
  nlinarith

lemma redθ_spec (θ : ℝ) : ∃ k : ℤ, θ = redθ θ + 2 * π * k :=
  ⟨round (θ / (2 * π)), by unfold redθ; ring⟩

theorem hfun_pos (hT : TransverseNeighborhoodHyp T) (ρ : ℝ) (p : ℝ × ℝ²) : 0 < hfun T ρ p :=
  mul_pos (aT_pos hT _) (Real.exp_pos _)

theorem Hmap_periodic (ρ θ : ℝ) (w : ℝ²) : Hmap T ρ (θ + 2 * π, w) = Hmap T ρ (θ, w) := by
  simp [Hmap, redθ_add]

theorem Hmap_core (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) (θ : ℝ) :
    Hmap T ρ (θ, 0) = T θ := by
  have hred : redθ θ ∈ Icc (-(4 * π)) (4 * π) := by
    have h1 := abs_le.1 (abs_redθ_le θ); have h2 := Real.pi_pos
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  simp only [Hmap]
  rw [Phi_core hT hρ hred 1 (by norm_num), chart_core]
  obtain ⟨k, hk⟩ := redθ_spec θ
  conv_rhs => rw [hk]
  have := hT.circle.periodic.int_mul k (redθ θ)
  rw [show (k : ℝ) * (2 * π) = 2 * π * k by ring] at this
  exact this.symm

/-- LEAF D1.  The pullback ODE along good trajectories (sm-3:2468-2471, the "Cartan identity"
in coordinates): with `J_t = DΦ_t(p)`, `A(t) = α_t(Φ_t p)(J_t w)` satisfies `A′ = (μ_t∘Φ_t) A`.
Proof: product rule with C4 (`∂_tΦ = V`, cutoff `= 1`), C9 (`∂_t J = DV·J`), `∂_t α_t = ν`,
B3 (`dα_t` = antisymmetrised derivative), `α_t(V_t) ≡ 0` near the trajectory (`alphaT_Vf`, so its
`p`-derivative vanishes), and `moser_identity`. -/
theorem hasDerivAt_alphaT_flow (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ)
    {δ₁ : ℝ} (hδ : AprioriRadius T ρ δ₁) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(4 * π)) (4 * π)) {w₀ : ℝ²}
    (hw₀ : ‖w₀‖ < δ₁) (w : ℝ × ℝ²) : ∀ t ∈ Ioo (-1 : ℝ) 2,
      HasDerivAt (fun t => alphaT T t (Phi T ρ t (θ₀, w₀)) (fderiv ℝ (Phi T ρ t) (θ₀, w₀) w))
        (muf T t (Phi T ρ t (θ₀, w₀)) *
          alphaT T t (Phi T ρ t (θ₀, w₀)) (fderiv ℝ (Phi T ρ t) (θ₀, w₀) w)) t := by
  sorry

/-- LEAF D2.  Solving the scalar ODE (sm-3:2472): `β(Φ_1 p)(DΦ_1 w) = exp(∫₀¹ μ_t∘Φ_t) α₀(p)(w)`
(row 86's `alpha_flow_eq` pattern: `A e^{−∫μ}` is constant, `A(0) = α₀` by `Phi_zero`,
`alphaT_zero`, `fderiv_id`). -/
theorem alphaT_flow_one (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ)
    {δ₁ : ℝ} (hδ : AprioriRadius T ρ δ₁) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(4 * π)) (4 * π)) {w₀ : ℝ²}
    (hw₀ : ‖w₀‖ < δ₁) (w : ℝ × ℝ²) :
    alphaT T 1 (Phi T ρ 1 (θ₀, w₀)) (fderiv ℝ (Phi T ρ 1) (θ₀, w₀) w) =
      Real.exp (∫ t in (0 : ℝ)..1, muf T t (Phi T ρ t (θ₀, w₀))) * alpha0 w₀ w.1 w.2 := by
  sorry

/-- LEAF D3.  Local form of `H` (C7): near every point of the `δ₁`-tube, `H` agrees with
`p ↦ F(Φ_1(p.1 − 2πk, p.2))` for the `k` of the reduction (the two reductions at a seam differ by
one period and `Phi_shift` + `chart_periodic` identify them). -/
theorem Hmap_eventuallyEq (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ)
    {δ₁ : ℝ} (hδ : AprioriRadius T ρ δ₁) (θ : ℝ) {w : ℝ²} (hw : ‖w‖ < δ₁) :
    ∃ k : ℤ, Hmap T ρ =ᶠ[𝓝 (θ, w)] fun p => chart T (Phi T ρ 1 (p.1 - 2 * π * k, p.2)) := by
  sorry

theorem Hmap_smoothOn (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ)
    {δ₁ : ℝ} (hδ : AprioriRadius T ρ δ₁) : ContDiffOn ℝ ∞ (Hmap T ρ) (solidTorus δ₁) := by
  intro p hp
  obtain ⟨k, hk⟩ := Hmap_eventuallyEq hT hρ hδ p.1 (by simpa [solidTorus] using hp.2)
  apply ContDiffAt.contDiffWithinAt
  refine (ContDiffAt.congr_of_eventuallyEq ?_ hk)
  exact ((contDiff_chart hT).comp ((contDiff_Phi hT hρ 1).comp
    ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd))).contDiffAt

/-- LEAF D4.  `H^*α = h α₀` on the `δ₁`-tube (sm-3:2472-2474): chain rule through D3,
`pullback_chart` (A: `F^*α = a·β`), `alphaT_one` and D2. -/
theorem Hmap_pullback (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ)
    {δ₁ : ℝ} (hδ : AprioriRadius T ρ δ₁) (θ : ℝ) {w : ℝ²} (hw : ‖w‖ < δ₁) (τ : ℝ) (η : ℝ²) :
    alpha (Hmap T ρ (θ, w)) (fderiv ℝ (Hmap T ρ) (θ, w) (τ, η)) = hfun T ρ (θ, w) * alpha0 w τ η := by
  sorry

/-- LEAF A7 (used here).  `F^*α = a·((1+g)dθ − 2v du)` exactly (memo §1.2): from A3 and
`α_q(x) = x_z − q_y x_x`. -/
theorem pullback_chart (hT : TransverseNeighborhoodHyp T) (p ξ : ℝ × ℝ²) :
    alpha (chart T p) (fderiv ℝ (chart T) p ξ) =
      aT T p.1 * ((1 + gfun T p) * ξ.1 - 2 * p.2 1 * ξ.2 0) := by
  obtain ⟨θ, w⟩ := p
  obtain ⟨τ, η⟩ := ξ
  rw [fderiv_chart hT θ w τ η]
  have ha : aT T θ ≠ 0 := (aT_pos hT θ).ne'
  have hc2 := cT_sq hT θ
  have hg : aT T θ * gfun T (θ, w) = cT T θ * w 0 * deriv T θ 1 - cT T θ * w 1 * deriv T θ 0
      - cT T θ * deriv (cT T) θ * w 0 * w 1 := by
    unfold gfun
    field_simp
  simp only [alpha, chart, E1, E2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp
  simp only [aT, alpha] at hg hc2 ⊢
  linear_combination -τ * hg - (w 1 * η 0) * hc2

/-- LEAF D5.  `H` is injective modulo `2π` on the `δ₁`-tube (`chart_inj` on the `2ρ`-tube, the
a-priori bound, injectivity of `Φ_1`, the reduction bookkeeping) — sm-3:2472 "embedding". -/
theorem Hmap_injective (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ)
    {δ₁ : ℝ} (hδ : AprioriRadius T ρ δ₁) : ∀ θ (w : ℝ²) θ' (w' : ℝ²), w ∈ Metric.ball (0 : ℝ²) δ₁ →
      w' ∈ Metric.ball (0 : ℝ²) δ₁ → Hmap T ρ (θ, w) = Hmap T ρ (θ', w') →
      w = w' ∧ ∃ k : ℤ, θ' = θ + 2 * π * k := by
  sorry

/-- LEAF D6.  `H` is an immersion on the `δ₁`-tube (`DF` bijective on the `2ρ`-tube, `DΦ_1`
injective since `Φ_1` is a diffeomorphism, D3). -/
theorem Hmap_immersion (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ)
    {δ₁ : ℝ} (hδ : AprioriRadius T ρ δ₁) : ∀ θ (w : ℝ²), w ∈ Metric.ball (0 : ℝ²) δ₁ →
      Injective (fderiv ℝ (Hmap T ρ) (θ, w)) := by
  sorry

/-- LEAF D7.  `H` is a topological embedding of the open solid torus: images of open sets are
open (D6 + IFT `HasStrictFDerivAt.map_nhds_eq_of_equiv`, dimension `3 = 3`), so take `V = H(U ∩ tube)`. -/
theorem Hmap_open_map (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ)
    {δ₁ : ℝ} (hδ : AprioriRadius T ρ δ₁) : ∀ U : Set (ℝ × ℝ²), IsOpen U →
      ∃ V : Set ℝ³, IsOpen V ∧ Hmap T ρ '' (U ∩ solidTorus δ₁) = V ∩ Hmap T ρ '' solidTorus δ₁ := by
  sorry

/-- The model neighbourhood (sm-3:2399-2404), assembled from D1–D7. -/
theorem model (hT : TransverseNeighborhoodHyp T) {ρ : ℝ} (hρ : GoodRadius T ρ) {δ₁ : ℝ}
    (hδ : AprioriRadius T ρ δ₁) : IsTransverseModel T δ₁ (Hmap T ρ) (hfun T ρ) where
  delta_pos := hδ.1
  smooth := Hmap_smoothOn hT hρ hδ
  periodic := fun θ w => Hmap_periodic ρ θ w
  injective := Hmap_injective hT hρ hδ
  immersion := Hmap_immersion hT hρ hδ
  open_map := Hmap_open_map hT hρ hδ
  core := Hmap_core hT hρ
  factor_pos := fun θ w _ => hfun_pos hT ρ (θ, w)
  pullback := fun θ w hw τ η => Hmap_pullback hT hρ hδ θ (by simpa using hw) τ η

end model

/-! ### Unit E — the Legendrian `L`, the annulus, the pushoff (sm-3:2476-2506) -/

section legendrian

/-- `v(θ) = b(cos Nθ, −sin Nθ)` (sm-3:2478, 2507). -/
def helix (N : ℕ) (b θ : ℝ) : ℝ² := !₂[b * Real.cos (N * θ), -(b * Real.sin (N * θ))]
/-- The annulus `B(θ,s) = (θ + κs, (b − s)(cos Nθ, −sin Nθ))` in the torus coordinates
(sm-3:2484-2486). -/
def annulus0 (N : ℕ) (b κ : ℝ) (q : ℝ × ℝ) : ℝ × ℝ² := (q.1 + κ * q.2, helix N (b - q.2) q.1)

variable {T : ℝ → ℝ³} {δ : ℝ} {H : ℝ × ℝ² → ℝ³} {h : ℝ × ℝ² → ℝ}

/-- LEAF E1.  Choice of `N`, `b` (sm-3:2476-2477): `N ≥ 1`, `b = N^{−1/2} < δ`, `Nb² = 1`. -/
theorem exists_N_b {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (b : ℝ), 0 < N ∧ 0 < b ∧ b < δ ∧ (N : ℝ) * b ^ 2 = 1 := by
  sorry

/-- LEAF E2.  `‖v(θ)‖ = |b|`. -/
theorem norm_helix (N : ℕ) (b θ : ℝ) : ‖helix N b θ‖ = |b| := by
  sorry

/-- LEAF E3.  `α₀(L₀′) = 1 − Nb² = 0` (sm-3:2479): `L₀(θ) = (θ, v(θ))`. -/
theorem alpha0_helix (N : ℕ) (b θ : ℝ) (hb : (N : ℝ) * b ^ 2 = 1) :
    alpha0 (helix N b θ) 1 (deriv (helix N b) θ) = 0 := by
  sorry

/-- LEAF E4.  `L = H ∘ L₀` is Legendrian (sm-3:2480): `α(L′) = h · α₀(L₀′) = 0` by the model
pullback and E3. -/
theorem legendrian_L (hm : IsTransverseModel T δ H h) {N : ℕ} {b : ℝ} (hb : (N : ℝ) * b ^ 2 = 1)
    (hb0 : 0 < b) (hbδ : b < δ) : IsLegendrian fun θ => H (θ, helix N b θ) := by
  sorry

/-- LEAF E5.  `L` is a smooth embedded circle (sm-3:2479-2480 "its degree-one first coordinate
makes it an embedding"; `H` injective mod `2π`, immersion). -/
theorem embedded_L (hm : IsTransverseModel T δ H h) {N : ℕ} {b : ℝ} (hN : 0 < N)
    (hb0 : 0 < b) (hbδ : b < δ) : IsEmbeddedCircle fun θ => H (θ, helix N b θ) := by
  sorry

theorem mem_L (_hm : IsTransverseModel T δ H h) {N : ℕ} {b : ℝ} (hb0 : 0 < b) (hbδ : b < δ)
    (θ : ℝ) : H (θ, helix N b θ) ∈ H '' solidTorus δ :=
  ⟨(θ, helix N b θ), ⟨trivial, by
    simp only [Metric.mem_ball, dist_zero_right, norm_helix, abs_of_pos hb0]; exact hbδ⟩, rfl⟩

/-- LEAF E6.  The pushoff annulus (sm-3:2481-2502): `H ∘ B` on `−ε < s < b` is a smooth embedded
periodic annulus with `B(·,0) = L`, transverse to the contact planes (`B^*α₀ = (1 − N(b−s)²)dθ + κ ds`,
`κ ≠ 0`), whose circles are positive transverse for `0 < s < b`. -/
theorem pushoffAnnulus (hm : IsTransverseModel T δ H h) {N : ℕ} {b ε κ : ℝ} (hN : 0 < N)
    (hb : (N : ℝ) * b ^ 2 = 1) (hb0 : 0 < b) (hε : 0 < ε) (hbε : b + ε < δ) (hκ : κ ≠ 0) :
    IsPushoffAnnulus (fun θ => H (θ, helix N b θ)) ε b fun q => H (annulus0 N b κ q) := by
  sorry

/-- LEAF E7.  The transverse isotopy (sm-3:2503-2504): `s ↦ H ∘ B(·, s)` from `s₀` to `b` runs
through positive transverse embedded circles and ends at `T(θ + κb)` (`B(θ,b) = (θ+κb, 0)`,
`H(·,0) = T`). -/
theorem transverselyIsotopic_pushoff (hm : IsTransverseModel T δ H h) {N : ℕ} {b ε κ : ℝ}
    (hN : 0 < N) (hb : (N : ℝ) * b ^ 2 = 1) (hb0 : 0 < b) (hε : 0 < ε) (hbε : b + ε < δ)
    (hκ : κ ≠ 0) {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₀b : s₀ < b) :
    TransverselyIsotopic (fun θ => H (annulus0 N b κ (θ, s₀))) T := by
  sorry

/-- sm-3:2405-2406, assembled from E1–E7. -/
theorem exists_legendrian (hm : IsTransverseModel T δ H h) :
    ∃ (N : ℕ) (b : ℝ), 0 < N ∧ 0 < b ∧ b < δ ∧
      IsEmbeddedCircle (fun θ => H (θ, helix N b θ)) ∧
      IsLegendrian (fun θ => H (θ, helix N b θ)) ∧
      (∀ θ, H (θ, helix N b θ) ∈ H '' solidTorus δ) ∧
      ∃ T' : ℝ → ℝ³, IsPositivePushoff (fun θ => H (θ, helix N b θ)) T' ∧
        TransverselyIsotopic T' T := by
  obtain ⟨N, b, hN, hb0, hbδ, hb⟩ := exists_N_b hm.delta_pos
  have hε : 0 < (δ - b) / 2 := by linarith
  have hbε : b + (δ - b) / 2 < δ := by linarith
  refine ⟨N, b, hN, hb0, hbδ, embedded_L hm hN hb0 hbδ, legendrian_L hm hb hb0 hbδ,
    mem_L hm hb0 hbδ, fun θ => H (annulus0 N b 1 (θ, b / 2)), ?_, ?_⟩
  · exact ⟨(δ - b) / 2, b, fun q => H (annulus0 N b 1 q),
      pushoffAnnulus hm hN hb hb0 hε hbε one_ne_zero, b / 2, by linarith, by linarith, rfl⟩
  · exact transverselyIsotopic_pushoff hm hN hb hb0 hε hbε one_ne_zero (by linarith) (by linarith)

end legendrian

/-! ### Unit F — the explicit ambient isotopy `Ψ` (sm-3:2507-2559) -/

section ambient

/-- The paper's `χ` (sm-3:2512-2519) with `R₁ = b + (δ−b)/4`, `R₂ = b + (δ−b)/2`: `1` for
`s ≤ R₁²`, `0` for `s ≥ R₂²`. -/
def chiAmb (b δ s : ℝ) : ℝ := cut1 ((b + (δ - b) / 4) ^ 2) ((b + (δ - b) / 2) ^ 2) s
/-- `V(θ, w) = (0, −χ(|w|²) v(θ))` (sm-3:2521-2522). -/
def Vamb (N : ℕ) (b δ : ℝ) (p : ℝ × ℝ²) : ℝ × ℝ² :=
  (0, -(chiAmb b δ (‖p.2‖ ^ 2)) • helix N b p.1)
open scoped Classical in
/-- The pushforward `H_*V` extended by zero (sm-3:2524-2530): at `q = H(p)`, `p` in the solid
torus, the value `DH(p)(V(p))` (independent of the preimage by periodicity, F1). -/
def pushfwd (H : ℝ × ℝ² → ℝ³) (δ : ℝ) (V : ℝ × ℝ² → ℝ × ℝ²) (q : ℝ³) : ℝ³ :=
  if hq : ∃ p ∈ solidTorus δ, H p = q then fderiv ℝ H hq.choose (V hq.choose) else 0
/-- The ambient flow `Ψ` = the global flow of `X = H_*V` (sm-3:2531-2536). -/
def Psi (H : ℝ × ℝ² → ℝ³) (δ : ℝ) (N : ℕ) (b : ℝ) : ℝ → ℝ³ → ℝ³ :=
  ContactMotions.globalFlow (pushfwd H δ (Vamb N b δ))

variable {T : ℝ → ℝ³} {δ : ℝ} {H : ℝ × ℝ² → ℝ³} {h : ℝ × ℝ² → ℝ}

/-- LEAF F1.  Value of the pushforward on the image (well-definedness: two preimages differ by a
period, and `H`, `DH`, `V` are periodic). -/
theorem pushfwd_apply (hm : IsTransverseModel T δ H h) (N : ℕ) (b : ℝ) {p : ℝ × ℝ²}
    (hp : p ∈ solidTorus δ) :
    pushfwd H δ (Vamb N b δ) (H p) = fderiv ℝ H p (Vamb N b δ p) := by
  sorry

/-- LEAF F2.  `X = H_*V` is `C^∞` on `ℝ³` (sm-3:2522-2530): on the open image it is
`(DH·V) ∘ (local inverse of H)` (IFT, `ContDiffAt.localInverse`), and it vanishes on a
neighbourhood of every point outside the compact `K = H(S¹ × D̄_{R₂})`. -/
theorem contDiff_pushfwd (hm : IsTransverseModel T δ H h) {N : ℕ} {b : ℝ} (hN : 0 < N)
    (hb0 : 0 < b) (hbδ : b < δ) : ContDiff ℝ ∞ (pushfwd H δ (Vamb N b δ)) := by
  sorry

/-- LEAF F3.  `X` has compact support (`K = H([0,2π] × D̄_{R₂})`). -/
theorem hasCompactSupport_pushfwd (hm : IsTransverseModel T δ H h) {N : ℕ} {b : ℝ} (hN : 0 < N)
    (hb0 : 0 < b) (hbδ : b < δ) : HasCompactSupport (pushfwd H δ (Vamb N b δ)) := by
  sorry

/-- A compactly supported `C^1` field's global flow fixes every point outside the support
(sm-3:2538 "They fix every point outside `K`"; uniqueness against the constant curve). -/
theorem globalFlow_fixed_of_notMem {X : ℝ³ → ℝ³} (hc : HasCompactSupport X)
    (hX : ContDiff ℝ 1 X) {p : ℝ³} (hp : p ∉ tsupport X) (t : ℝ) :
    ContactMotions.globalFlow X t p = p := by
  obtain ⟨K, hK⟩ := ContactMotions.exists_lipschitzWith_of_hasCompactSupport' hc hX
  have hfl := ContactMotions.isGlobalFlow_globalFlow hc hX
  have h0 : X p = 0 := image_eq_zero_of_notMem_tsupport hp
  have := ContactMotions.ODE_unique_global hK (f := fun s => ContactMotions.globalFlow X s p)
    (g := fun _ => p) (fun s => hfl.hasDerivAt s p)
    (fun s => by simpa [h0] using hasDerivAt_const s p) (t₀ := 0) (by simp [hfl.zero])
  exact congrFun this t

/-- sm-3:2531-2541 assembled: `Ψ` is a compactly supported ambient isotopy (row 86's existence,
uniqueness, inverse `Ψ_{−t}` and smooth dependence). -/
theorem ambientIsotopy (hm : IsTransverseModel T δ H h) {N : ℕ} {b : ℝ} (hN : 0 < N)
    (hb0 : 0 < b) (hbδ : b < δ) : IsCompactlySupportedAmbientIsotopy (Psi H δ N b) := by
  have hX := contDiff_pushfwd hm hN hb0 hbδ
  have hc := hasCompactSupport_pushfwd hm hN hb0 hbδ
  have hfl := ContactMotions.isGlobalFlow_globalFlow hc (hX.of_le (by simp))
  have hs : ContDiff ℝ ∞ (uncurry (Psi H δ N b)) :=
    ContactMotions.contDiff_uncurry hX hc hfl
  obtain ⟨K, hK⟩ := ContactMotions.exists_lipschitzWith_of_hasCompactSupport' hc (hX.of_le (by simp))
  refine ⟨hs.contDiffOn, hfl.zero, fun t _ => ⟨Psi H δ N b (-t), ?_, hfl.leftInverse hK t,
    hfl.rightInverse hK t⟩, ⟨tsupport (pushfwd H δ (Vamb N b δ)), hc, fun t _ p hp =>
      globalFlow_fixed_of_notMem hc (hX.of_le (by simp)) hp t⟩⟩
  exact hs.comp (contDiff_const.prodMk contDiff_id)

/-- LEAF F4.  The tracked helix (sm-3:2542-2547): `Ψ_t(L θ) = H(θ, (1−t)v(θ))` for `t ∈ [0,1]`
— the curve has velocity `DH·(0, −v(θ)) = X` since `χ = 1` at radius `(1−t)b ≤ b < R₁` (F1);
uniqueness. -/
theorem psi_track (hm : IsTransverseModel T δ H h) {N : ℕ} {b : ℝ} (hN : 0 < N) (hb0 : 0 < b)
    (hbδ : b < δ) : ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ,
      Psi H δ N b t (H (θ, helix N b θ)) = H (θ, (1 - t) • helix N b θ) := by
  sorry

/-- sm-3:2547-2549: `Ψ_1 ∘ L = T` as parametrized circles. -/
theorem carries (hm : IsTransverseModel T δ H h) {N : ℕ} {b : ℝ} (hN : 0 < N) (hb0 : 0 < b)
    (hbδ : b < δ) (θ : ℝ) : Psi H δ N b 1 (H (θ, helix N b θ)) = T θ := by
  rw [psi_track hm hN hb0 hbδ 1 ⟨zero_le_one, le_rfl⟩ θ]
  simp [hm.core]

end ambient

end TransverseNeighborhood

open TransverseNeighborhood

/-- **fd:transverse-neighborhood** (sm-3:2395-2409), assembled from units D, E, F. -/
theorem fd_transverse_neighborhood : TransverseNeighborhoodData := by
  intro T hT
  obtain ⟨ρ, hρ⟩ := exists_goodRadius hT
  obtain ⟨δ₁, hδ⟩ := exists_aprioriRadius hT hρ
  have hm := model hT hρ hδ
  obtain ⟨N, b, hN, hb0, hbδ, hLc, hLl, hLmem, T', hpush, hiso⟩ := exists_legendrian hm
  exact ⟨δ₁, Hmap T ρ, hfun T ρ, fun θ => Hmap T ρ (θ, helix N b θ), Psi (Hmap T ρ) δ₁ N b,
    { model := hm
      legendrian_circle := hLc
      legendrian := hLl
      mem_neighbourhood := hLmem
      pushoff_isotopic := ⟨T', hpush, hiso⟩
      ambient := ambientIsotopy hm hN hb0 hbδ
      carries := carries hm hN hb0 hbδ }⟩

end

end SM
