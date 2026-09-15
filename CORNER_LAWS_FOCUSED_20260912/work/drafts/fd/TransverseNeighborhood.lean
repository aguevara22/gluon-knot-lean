import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # SM fd:transverse-neighborhood — a transverse neighbourhood and its Legendrian pushoff (row 84)

Source: reference/SM/sm-3-statesum.tex:2395-2409 (statement), 2410-2559 (proof).  Drafted
2026-09-14 in work/drafts/fd/ as part of the fd block 84-88.  **Statement only**: this file
defines the notions of the printed statement in coordinates and the Prop bundle
`SM.TransverseNeighborhoodData`; it contains no theorem about it.  The feasibility memo
`work/drafts/fd/FD_84_86_FEASIBILITY.md` §2 explains why: two printed steps (sm-3:2463, the
Moser flow `Φ_1` is a diffeomorphism; sm-3:2532-2541, the ambient flow `Ψ_t` consists of
diffeomorphisms) need the smooth dependence of an ODE flow on its initial point, which Mathlib
(this pin) does not have (see `SM.SmoothDependence` in `ContactMotions.lean`), and the rest of
the proof (uniform inverse-function radius, coordinate Gray–Moser computation, pushoff annulus)
is several thousand lines of new infrastructure.

Check: `cd work/lean && lake env lean ../drafts/fd/TransverseNeighborhood.lean`.

## The printed statement (sm-3:2395-2409, verbatim)

"Let α = dz − y dx and let T : ℝ/(2πℤ) → ℝ³ be a smooth embedded oriented circle with α(T′) > 0.
There are δ > 0 and a smooth embedding H : S¹ × D_δ → ℝ³ fixing the parametrized core T such
that H^*α = hα₀, α₀ = dθ + u dv − v du, h > 0.  There is an oriented Legendrian knot L in this
neighbourhood whose positive transverse pushoff is transversely isotopic to T.  An explicit
compactly supported ordinary ambient isotopy carries the parametrized L to the parametrized T,
preserving their orientations."

## Printed notion → Lean

| printed | Lean |
|---|---|
| `ℝ³`, coordinates `(x, y, z)` | `EuclideanSpace ℝ (Fin 3)`, `(p 0, p 1, p 2)` |
| `α = dz − y dx` | `alpha p v = v 2 − p 1 * v 0` (`α_p(v)`) |
| `S¹ = ℝ/(2πℤ)`, a circle `T : S¹ → ℝ³` | a `2π`-periodic map `T : ℝ → ℝ³` (FR-TN-1) |
| "smooth embedded oriented circle" | `IsEmbeddedCircle T`: `C^∞`, `2π`-periodic, injective modulo `2π`, `T' ≠ 0`; the orientation is the parametrization |
| `α(T′) > 0` | `IsPositiveTransverse T : ∀ θ, 0 < alpha (T θ) (deriv T θ)` |
| `S¹ × D_δ`, coordinates `(θ, u, v)` | `ℝ × EuclideanSpace ℝ (Fin 2)`, domain `univ ×ˢ Metric.ball 0 δ`, `u = w 0`, `v = w 1` |
| `α₀ = dθ + u dv − v du` | `alpha0 w τ η = τ + w 0 * η 1 − w 1 * η 0` on the tangent vector `(τ, η)` |
| "smooth embedding `H : S¹ × D_δ → ℝ³` fixing the parametrized core `T`", `H^*α = hα₀`, `h > 0` | `IsTransverseModel T δ H h` (FR-TN-2, FR-TN-3) |
| "oriented Legendrian knot `L` in this neighbourhood" | `IsEmbeddedCircle L`, `IsLegendrian L`, `∀ θ, L θ ∈ H '' (univ ×ˢ ball 0 δ)` |
| "positive transverse pushoff" of `L` | `IsPositivePushoff L T'`: a positive-transverse circle `B(·, s₀)`, `s₀ > 0` small, of a pushoff annulus `B` of `L` (`IsPushoffAnnulus`, sm-3:2490-2502; FR-TN-4) |
| "transversely isotopic to `T`" | `TransverselyIsotopic T' T` (a smooth family of positive transverse embedded circles ending at an orientation-preserving reparametrization of `T`, sm-3:2503-2504; FR-TN-5) |
| "compactly supported ordinary ambient isotopy" | `IsCompactlySupportedAmbientIsotopy Ψ` (`t ∈ [0,1]`, jointly smooth, `Ψ_0 = id`, each `Ψ_t` a diffeomorphism, identity outside a compact set) |
| "carries the parametrized `L` to the parametrized `T`, preserving their orientations" | `∀ θ, Ψ 1 (L θ) = T θ` (the parameter is carried, sm-3:2547-2549) |

## Fidelity readings

* **FR-TN-1 (periodic lifts).** `S¹ = ℝ/2πℤ` is read through `2π`-periodic maps on `ℝ`, as in the
  chart reading FR-PA-1 of row 85; "embedded" for a compact circle is "injective immersion"
  (injective modulo the period).
* **FR-TN-2 (smooth embedding of the open solid torus).** `H` is `C^∞` on the open domain,
  injective modulo the period, an immersion, and a topological embedding of the quotient: the
  image of every open set is relatively open in the image (`IsTransverseModel.open_map`), which
  for an injective continuous map on the quotient is the embedding condition.
* **FR-TN-3 (the conformal factor `h`).** `h` is quantified with `H`; it is in fact determined by
  `H` (`h = (H^*α)(∂_θ)`), so no smoothness of `h` is demanded beyond positivity (the printed
  clause is "`h > 0`").
* **FR-TN-4 (positive pushoff).** The paper fixes the pushoff by the transverse annulus
  `B` of sm-3:2490-2502 ("a sufficiently small positive circle is therefore the positive pushoff in
  the source convention"); `IsPositivePushoff L T'` says exactly that `T'` is a small positive
  circle of such an annulus of `L`.
* **FR-TN-5 (transverse isotopy up to reparametrization).** sm-3:2503-2504 ends the isotopy at
  `T(θ + κ b)`, "the same oriented transverse knot": the family may end at an
  orientation-preserving reparametrization `T ∘ ρ` (`IsCircleReparam ρ`). -/

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

/-! ## 7. Sanity checks on the model form (not printed clauses) -/

namespace TransverseNeighborhood

/-- `α₀(∂_θ) = 1`: the core `θ ↦ (θ, 0)` is positive transverse for `α₀`, so a model
neighbourhood carries the core orientation ("including coorientation and core orientation",
sm-3:2474). -/
lemma alpha0_zero_left (w : ℝ²) : alpha0 w 1 0 = 1 := by simp [alpha0]

/-- On the core `w = 0`, `α₀ = dθ`. -/
lemma alpha0_core (τ : ℝ) (η : ℝ²) : alpha0 0 τ η = τ := by simp [alpha0]

/-- A model neighbourhood is consistent with the hypothesis on the core: `h(θ, 0) · 1 =
α_{T θ}(DH(θ,0)(1,0))`. -/
lemma IsTransverseModel.alpha_core {T : ℝ → ℝ³} {δ : ℝ} {H : ℝ × ℝ² → ℝ³} {h : ℝ × ℝ² → ℝ}
    (hm : IsTransverseModel T δ H h) (θ : ℝ) :
    alpha (T θ) (fderiv ℝ H (θ, 0) (1, 0)) = h (θ, 0) := by
  have h0 : (0 : ℝ²) ∈ Metric.ball (0 : ℝ²) δ := Metric.mem_ball_self hm.delta_pos
  have := hm.pullback θ 0 h0 1 0
  rw [hm.core, alpha0_core] at this
  rw [this, mul_one]

end TransverseNeighborhood

end

end SM
