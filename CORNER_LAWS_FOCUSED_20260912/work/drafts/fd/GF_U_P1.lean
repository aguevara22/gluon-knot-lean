import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import SM.ContactMotions
import SM.ParameterAvoidance

/-! # SM fd:generic-front — PROOF SKELETON (row 87)

Written 2026-09-14 (work/drafts/fd/).  Source: reference/SM/sm-3-statesum.tex:2613-2630
(statement), 2631-2783 (proof).  Route: `FD_84_87_FEASIBILITY_v2.md` §2; leaf plan: `GF_PLAN.md`.

Layout.  §1–§4 (from `namespace SM` to `GenericFrontData`) are **byte-identical** to
`GenericFront_Statement.lean` lines 79-255.  §5 adds the route: definitions, PROVED glue, LEAF
lemmas (`sorry`) in units P0–P6, and the row theorem `SM.fd_generic_front : GenericFrontData`
PROVED from the leaves.  Independent of the row-84 skeleton: the row-84 notions it needs are the
copies already in `SM.GenericFront`.

Units: P0 contact isotopies from Hamiltonian flows (row 86) · P1 simultaneous zeros of `(x′,x″)`
(row 85, `(d,q) = (1,2)`) · P2 the uniform collar (local front injectivity) · P3 cusps on branches
and triple points (row 85, `(2,3)` and `(3,4)`) · P4 transverse, finite double points · P5 exact
cusp germs · P6 concatenation, pushoff annulus, knot type.

Check: `cd work/lean && lake env lean ../drafts/fd/GF_Skeleton.lean`. -/

namespace SM

open scoped ContDiff Topology
open Set Function Real

noncomputable section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace GenericFront

/-! ## 1. Notions shared with row 84 (verbatim copies of `SM.TransverseNeighborhood`, to be
deduplicated at porting time by importing that module) -/

/-- `α = dz − y dx` at `p` on `v`. -/
def alpha (p v : ℝ³) : ℝ := v 2 - p 1 * v 0

/-- A smooth embedded oriented circle as a `2π`-periodic map (FR-GF-1). -/
structure IsEmbeddedCircle (T : ℝ → ℝ³) : Prop where
  smooth : ContDiff ℝ ∞ T
  periodic : Periodic T (2 * π)
  injective : ∀ θ θ', T θ = T θ' → ∃ k : ℤ, θ' = θ + 2 * π * k
  immersion : ∀ θ, deriv T θ ≠ 0

/-- `α(T′) > 0`. -/
def IsPositiveTransverse (T : ℝ → ℝ³) : Prop := ∀ θ, 0 < alpha (T θ) (deriv T θ)

/-- `α(L′) = 0`. -/
def IsLegendrian (L : ℝ → ℝ³) : Prop := ∀ θ, alpha (L θ) (deriv L θ) = 0

/-- An orientation-preserving reparametrization of the circle. -/
structure IsCircleReparam (ρ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ ρ
  deriv_pos : ∀ θ, 0 < deriv ρ θ
  lift : ∀ θ, ρ (θ + 2 * π) = ρ θ + 2 * π

/-- A transverse pushoff annulus of the Legendrian circle `L` (sm-3:2490-2502). -/
structure IsPushoffAnnulus (L : ℝ → ℝ³) (ε b : ℝ) (B : ℝ × ℝ → ℝ³) : Prop where
  eps_pos : 0 < ε
  b_pos : 0 < b
  smooth : ContDiffOn ℝ ∞ B (univ ×ˢ Ioo (-ε) b)
  periodic : ∀ θ s, B (θ + 2 * π, s) = B (θ, s)
  core : ∀ θ, B (θ, 0) = L θ
  injective : ∀ θ s θ' s', s ∈ Ioo (-ε) b → s' ∈ Ioo (-ε) b → B (θ, s) = B (θ', s') →
    s = s' ∧ ∃ k : ℤ, θ' = θ + 2 * π * k
  immersion : ∀ θ s, s ∈ Ioo (-ε) b → Injective (fderiv ℝ B (θ, s))
  transverse : ∀ θ s, s ∈ Ioo (-ε) b →
    alpha (B (θ, s)) (fderiv ℝ B (θ, s) (1, 0)) ≠ 0 ∨ alpha (B (θ, s)) (fderiv ℝ B (θ, s) (0, 1)) ≠ 0
  positive : ∀ s, 0 < s → s < b → IsPositiveTransverse fun θ => B (θ, s)

/-- `T'` is a positive transverse pushoff of `L`: a small positive circle of a pushoff annulus. -/
def IsPositivePushoff (L T' : ℝ → ℝ³) : Prop :=
  ∃ (ε b : ℝ) (B : ℝ × ℝ → ℝ³), IsPushoffAnnulus L ε b B ∧
    ∃ s₀, 0 < s₀ ∧ s₀ < b ∧ T' = fun θ => B (θ, s₀)

/-- `T₀` is transversely isotopic to `T₁` (up to orientation-preserving reparametrization). -/
def TransverselyIsotopic (T₀ T₁ : ℝ → ℝ³) : Prop :=
  ∃ F : ℝ → ℝ → ℝ³, ContDiffOn ℝ ∞ (uncurry F) (Icc 0 1 ×ˢ univ) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, IsEmbeddedCircle (F s) ∧ IsPositiveTransverse (F s)) ∧
    F 0 = T₀ ∧ ∃ ρ : ℝ → ℝ, IsCircleReparam ρ ∧ F 1 = T₁ ∘ ρ

/-- A compactly supported ambient isotopy of `ℝ³`, `t ∈ [0,1]`. -/
structure IsCompactlySupportedAmbientIsotopy (Ψ : ℝ → ℝ³ → ℝ³) : Prop where
  smooth : ContDiffOn ℝ ∞ (uncurry Ψ) (Icc 0 1 ×ˢ univ)
  zero : ∀ p, Ψ 0 p = p
  diffeo : ∀ t ∈ Icc (0 : ℝ) 1, ∃ Ψinv : ℝ³ → ℝ³, ContDiff ℝ ∞ Ψinv ∧
    LeftInverse Ψinv (Ψ t) ∧ RightInverse Ψinv (Ψ t)
  support : ∃ K : Set ℝ³, IsCompact K ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ p, p ∉ K → Ψ t p = p

/-! ## 2. Contact isotopies (sm-3:2614-2615, 2767-2772) -/

/-- "A smooth ambient coorientation-preserving contact isotopy" `Φ_s`, `s ∈ [0,1]` (FR-GF-2):
a compactly supported ambient isotopy each of whose stages is a contactomorphism of
`α = dz − y dx` with a positive conformal factor (`Φ_s^*α = c_s α`, `c_s > 0`, sm-3:2771-2772). -/
structure IsContactIsotopy (Φ : ℝ → ℝ³ → ℝ³) : Prop where
  /-- "smooth ambient … isotopy": jointly smooth, `Φ_0 = id`, diffeomorphisms, compactly
  supported (the last is the printed proof's output and the consumer's input, not a printed
  clause of the statement — FR-GF-2). -/
  ambient : IsCompactlySupportedAmbientIsotopy Φ
  /-- "coorientation-preserving contact": `α_{Φ_s p}(DΦ_s(p) v) = c · α_p(v)` with `c > 0`. -/
  contact : ∀ s ∈ Icc (0 : ℝ) 1, ∀ p, ∃ c : ℝ, 0 < c ∧
    ∀ v, alpha (Φ s p) (fderiv ℝ (Φ s) p v) = c * alpha p v

/-! ## 3. Fronts, cusps, double points (sm-3:2615-2618) -/

/-- The `xz` front of a parametrized curve: `θ ↦ (x(θ), z(θ))`. -/
def front (L : ℝ → ℝ³) (θ : ℝ) : ℝ × ℝ := (L θ 0, L θ 2)

/-- The coordinate functions `x, y, z` of the curve. -/
def coordX (L : ℝ → ℝ³) (θ : ℝ) : ℝ := L θ 0
def coordY (L : ℝ → ℝ³) (θ : ℝ) : ℝ := L θ 1
def coordZ (L : ℝ → ℝ³) (θ : ℝ) : ℝ := L θ 2

/-- Two parameters name the same point of the circle. -/
def SameParam (θ η : ℝ) : Prop := ∃ k : ℤ, η = θ + 2 * π * k

/-- The cusp parameters of the front: `x′(θ) = 0` (FR-GF-3). -/
def cuspSet (L : ℝ → ℝ³) : Set ℝ := {θ | deriv (coordX L) θ = 0}

/-- The double points of the front: ordered pairs of distinct circle parameters with the same
front point (FR-GF-4). -/
def doublePoints (L : ℝ → ℝ³) : Set (ℝ × ℝ) :=
  {p | ¬ SameParam p.1 p.2 ∧ front L p.1 = front L p.2}

/-- A double point is transverse: the two front velocities `(x′, z′)` are independent. -/
def IsTransverseDouble (L : ℝ → ℝ³) (θ η : ℝ) : Prop :=
  deriv (coordX L) θ * deriv (coordZ L) η - deriv (coordZ L) θ * deriv (coordX L) η ≠ 0

/-- The exact semicubical cusp germ at the cusp parameter `θc` (sm-3:2621-2625, FR-GF-5): with
`u = y(θ) − y(θc)` a local coordinate (`y′(θc) ≠ 0`; `u` may increase or decrease with `θ`),
`x = x₀ + A u²` and `z = z₀ + A y₀ u² + ⅔ A u³` near `θc`, `A ≠ 0`. -/
def IsExactCuspGerm (L : ℝ → ℝ³) (θc : ℝ) : Prop :=
  ∃ A : ℝ, A ≠ 0 ∧ deriv (coordY L) θc ≠ 0 ∧ ∃ ε > 0, ∀ θ, |θ - θc| < ε →
    coordX L θ = coordX L θc + A * (coordY L θ - coordY L θc) ^ 2 ∧
    coordZ L θ = coordZ L θc + A * coordY L θc * (coordY L θ - coordY L θc) ^ 2
      + 2 / 3 * A * (coordY L θ - coordY L θc) ^ 3

/-- The front of `L` is generic in the sense of sm-3:2615-2618, one field per printed clause. -/
structure IsGenericFront (L : ℝ → ℝ³) : Prop where
  /-- "only finitely many … cusps" (counted on one period). -/
  finite_cusps : (cuspSet L ∩ Ico 0 (2 * π)).Finite
  /-- "semicubical cusps": every cusp has the exact germ of sm-3:2621-2625. -/
  exact_germ : ∀ θc ∈ cuspSet L, IsExactCuspGerm L θc
  /-- "finitely many … double points" (ordered pairs on one period square). -/
  finite_double : (doublePoints L ∩ Ico 0 (2 * π) ×ˢ Ico 0 (2 * π)).Finite
  /-- "transverse double points". -/
  transverse_double : ∀ p ∈ doublePoints L, IsTransverseDouble L p.1 p.2
  /-- "no triple point". -/
  no_triple : ∀ θ η τ, ¬ SameParam θ η → ¬ SameParam θ τ → ¬ SameParam η τ →
    ¬ (front L θ = front L η ∧ front L θ = front L τ)
  /-- "no cusp on another branch". -/
  no_cusp_on_branch : ∀ θ ∈ cuspSet L, ∀ η, ¬ SameParam θ η → front L η ≠ front L θ

end GenericFront

open GenericFront

/-! ## 4. The printed statement -/

/-- The hypotheses of fd:generic-front (sm-3:2614): "a smooth oriented Legendrian embedding
`L : S¹ → ℝ³`". -/
structure GenericFrontHyp (L : ℝ → ℝ³) : Prop where
  /-- "smooth oriented … embedding". -/
  circle : IsEmbeddedCircle L
  /-- "Legendrian". -/
  legendrian : IsLegendrian L

/-- The conclusion of fd:generic-front for the witness isotopy `Φ` (sm-3:2614-2630), one field
per printed clause; `L_g = Φ 1 ∘ L`. -/
structure GenericFrontConclusion (L : ℝ → ℝ³) (Φ : ℝ → ℝ³ → ℝ³) : Prop where
  /-- sm-3:2614-2615 "a smooth ambient coorientation-preserving contact isotopy". -/
  isotopy : IsContactIsotopy Φ
  /-- sm-3:2615 "to a Legendrian embedding `L_g`": an embedded circle … -/
  legendrian_circle : IsEmbeddedCircle (Φ 1 ∘ L)
  /-- … which is Legendrian. -/
  legendrian : IsLegendrian (Φ 1 ∘ L)
  /-- sm-3:2615-2625 "whose `xz` front has only finitely many semicubical cusps and transverse
  double points, with no triple point and no cusp on another branch", with the exact cusp germ. -/
  generic : IsGenericFront (Φ 1 ∘ L)
  /-- sm-3:2627-2629 "The isotopy carries a chosen thin positive-pushoff annulus and preserves its
  positive-pushoff transverse isotopy class" (FR-GF-6): for every pushoff annulus `B` of `L`,
  each `Φ_s ∘ B` is a pushoff annulus of `Φ_s ∘ L`, and each positive circle `B(·, s₀)` is
  transversely isotopic to `Φ_1 ∘ B(·, s₀)`, a positive pushoff of `L_g`. -/
  pushoff : ∀ (ε b : ℝ) (B : ℝ × ℝ → ℝ³), IsPushoffAnnulus L ε b B →
    (∀ s ∈ Icc (0 : ℝ) 1, IsPushoffAnnulus (Φ s ∘ L) ε b (fun q => Φ s (B q))) ∧
    ∀ s₀, 0 < s₀ → s₀ < b →
      TransverselyIsotopic (fun θ => B (θ, s₀)) (fun θ => Φ 1 (B (θ, s₀))) ∧
      IsPositivePushoff (Φ 1 ∘ L) (fun θ => Φ 1 (B (θ, s₀)))
  /-- sm-3:2629-2630 "as well as the oriented topological knot type" (FR-GF-7): `L_g` is carried
  to by a compactly supported ambient isotopy of the parametrized oriented circle `L`. -/
  knot_type : ∃ Ψ : ℝ → ℝ³ → ℝ³, IsCompactlySupportedAmbientIsotopy Ψ ∧ ∀ θ, Ψ 1 (L θ) = Φ 1 (L θ)

/-- **fd:generic-front** (sm-3:2613-2630), the statement: every smooth oriented Legendrian
embedding admits a contact isotopy with the printed conclusion.  Not proved here (see the module
docstring and `FD_84_87_FEASIBILITY_v2.md` §2). -/
def GenericFrontData : Prop :=
  ∀ L : ℝ → ℝ³, GenericFrontHyp L → ∃ Φ : ℝ → ℝ³ → ℝ³, GenericFrontConclusion L Φ

/-! ## 5. Proof skeleton -/

namespace GenericFront

open ContactMotions (hamFlow hamVF composeFlows ContactMotionsHyp)

local notation "ℝ^" n:max => EuclideanSpace ℝ (Fin n)

/-! ### Unit P0 — contact isotopies from Hamiltonian flows (sm-3:2632-2638; row 86) -/

/-- The path `s ↦ Φ_{sa}` of compositions of the time-`s·a_i` flows (sm-3:2636). -/
def hamIsotopy (n : ℕ) (Hs : Fin n → ℝ³ → ℝ) (a : Fin n → ℝ) (s : ℝ) (p : ℝ³) : ℝ³ :=
  composeFlows n Hs (s • a) p

theorem hamIsotopy_one (n : ℕ) (Hs : Fin n → ℝ³ → ℝ) (a : Fin n → ℝ) :
    hamIsotopy n Hs a 1 = composeFlows n Hs a := by
  funext p; simp [hamIsotopy]

/-- LEAF P0.1.  `s ↦ Φ_{sa}` is a compactly supported contact isotopy (row 86: `fd_contact_motions`
gives joint smoothness, the group law/inverses, `Φ^*α = c α` with `c > 0`; each flow fixes the
complement of `tsupport (hamVF Hᵢ)`). -/
theorem isContactIsotopy_hamIsotopy (n : ℕ) (Hs : Fin n → ℝ³ → ℝ) (a : Fin n → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) : IsContactIsotopy (hamIsotopy n Hs a) := by
  sorry

/-- LEAF P0.2.  A stage of a contact isotopy carries an embedded Legendrian circle to an embedded
Legendrian circle (sm-3:2637-2638 "its images are exactly Legendrian embeddings"). -/
theorem contact_preserves_legendrian {Φ : ℝ → ℝ³ → ℝ³} (hΦ : IsContactIsotopy Φ) {L : ℝ → ℝ³}
    (hL : IsEmbeddedCircle L) (hLeg : IsLegendrian L) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    IsEmbeddedCircle (Φ s ∘ L) ∧ IsLegendrian (Φ s ∘ L) := by
  sorry

/-- LEAF P0.3.  "At `a = 0`, the `aᵢ` derivative of `Φ_a ∘ L` is `X_{Hᵢ} ∘ L`" (sm-3:2635). -/
theorem fderiv_composeFlows_zero (n : ℕ) (Hs : Fin n → ℝ³ → ℝ) (hHs : ∀ i, ContactMotionsHyp (Hs i))
    (p : ℝ³) (i : Fin n) :
    fderiv ℝ (fun a : Fin n → ℝ => composeFlows n Hs a p) 0 (Pi.single i 1) = hamVF (Hs i) p := by
  sorry

/-! ### Intermediate genericity stages -/

/-- `(x′, x″)` never vanish together (sm-3:2656-2658 "every zero of `x₁′` is simple"). -/
def NoDoubleZero (L : ℝ → ℝ³) : Prop :=
  ∀ θ, deriv (coordX L) θ ≠ 0 ∨ deriv (deriv (coordX L)) θ ≠ 0
/-- Circular distance of two parameters. -/
def circDist (θ η : ℝ) : ℝ := |θ - η - 2 * π * round ((θ - η) / (2 * π))|
/-- Uniform local injectivity of the front below the collar width `δc` (sm-3:2677-2680). -/
def LocallyInjectiveFront (L : ℝ → ℝ³) (δc : ℝ) : Prop :=
  0 < δc ∧ ∀ θ η, circDist θ η < δc → ¬ SameParam θ η → front L θ ≠ front L η
/-- No cusp on another branch (sm-3:2713-2714). -/
def NoCuspOnBranch (L : ℝ → ℝ³) : Prop :=
  ∀ θ ∈ cuspSet L, ∀ η, ¬ SameParam θ η → front L η ≠ front L θ
/-- No triple point. -/
def NoTriple (L : ℝ → ℝ³) : Prop :=
  ∀ θ η τ, ¬ SameParam θ η → ¬ SameParam θ τ → ¬ SameParam η τ →
    ¬ (front L θ = front L η ∧ front L θ = front L τ)

/-- After step 1 (sm-3:2639-2658). -/
structure Stage1 (L : ℝ → ℝ³) : Prop where
  circle : IsEmbeddedCircle L
  legendrian : IsLegendrian L
  noDoubleZero : NoDoubleZero L

/-- After steps 2–3 (sm-3:2659-2714). -/
structure Stage2 (L : ℝ → ℝ³) : Prop extends Stage1 L where
  collar : ∃ δc, LocallyInjectiveFront L δc
  noCuspOnBranch : NoCuspOnBranch L
  noTriple : NoTriple L

/-- After step 4 (sm-3:2715-2730). -/
structure Stage3 (L : ℝ → ℝ³) : Prop extends Stage2 L where
  transverse_double : ∀ p ∈ doublePoints L, IsTransverseDouble L p.1 p.2
  finite_double : (doublePoints L ∩ Ico 0 (2 * π) ×ˢ Ico 0 (2 * π)).Finite

/-! ### Unit P1 — simultaneous zeros of `(x′, x″)` (sm-3:2639-2658; row 85 with `(d,q) = (1,2)`) -/

/-- The `x`-coordinate of `Φ_a ∘ L`. -/
def xParam (L : ℝ → ℝ³) (n : ℕ) (Hs : Fin n → ℝ³ → ℝ) (a : Fin n → ℝ) (θ : ℝ) : ℝ :=
  composeFlows n Hs a (L θ) 0
/-- The front `p_a = (x_a, z_a)` of `Φ_a ∘ L`. -/
def frontParam (L : ℝ → ℝ³) (n : ℕ) (Hs : Fin n → ℝ³ → ℝ) (a : Fin n → ℝ) (θ : ℝ) : ℝ × ℝ :=
  front (composeFlows n Hs a ∘ L) θ
/-- The parameter as a vector of `ℝ^n`, read as `Fin n → ℝ`. -/
def par {n : ℕ} (a : ℝ^n) : Fin n → ℝ := fun i => a i
/-- `(θ, a) ↦ (x_a′(θ), x_a″(θ))` on `ℝ^1 × ℝ^n` (sm-3:2639, 2653). -/
def cuspMap (L : ℝ → ℝ³) (n : ℕ) (Hs : Fin n → ℝ³ → ℝ) (z : ℝ^1 × ℝ^n) : ℝ^2 :=
  !₂[deriv (xParam L n Hs (par z.2)) (z.1 0), deriv (deriv (xParam L n Hs (par z.2))) (z.1 0)]
/-- One period of the circle in `ℝ^1`. -/
def Kper1 : Set (ℝ^1) := {z | z 0 ∈ Icc 0 (2 * π)}

/-- At a zero of `x′`, `y′ ≠ 0`: immersion and `z′ = y x′` (sm-3:2640).  Shared by P1.1 and P1.4. -/
theorem gp1_deriv_y_ne_zero {L : ℝ → ℝ³} (hc : IsEmbeddedCircle L) (hl : IsLegendrian L) {θ : ℝ}
    (hθ : deriv (coordX L) θ = 0) : deriv (coordY L) θ ≠ 0 := by
  have hd : HasDerivAt L (deriv L θ) θ := (hc.smooth.differentiable (by simp) θ).hasDerivAt
  have h0 : deriv (coordX L) θ = deriv L θ 0 := (ContactMotions.hasDerivAt_coord hd 0).deriv
  have h1 : deriv (coordY L) θ = deriv L θ 1 := (ContactMotions.hasDerivAt_coord hd 1).deriv
  have hleg : deriv L θ 2 - L θ 1 * deriv L θ 0 = 0 := hl θ
  intro hy
  apply hc.immersion θ
  rw [h0] at hθ
  rw [h1] at hy
  ext i
  fin_cases i
  · simpa using hθ
  · simpa using hy
  · rw [hθ, mul_zero, sub_zero] at hleg
    simpa using hleg

/-- The `θ`-partial derivative of a jointly differentiable `G : A × ℝ → ℝ` is the full derivative
in the direction `(0, 1)`. -/
theorem gp1_deriv_partial_eq {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] {G : A × ℝ → ℝ}
    {a : A} {θ : ℝ} (hG : DifferentiableAt ℝ G (a, θ)) :
    deriv (fun t => G (a, t)) θ = fderiv ℝ G (a, θ) (0, 1) := by
  have h1 : HasFDerivAt (fun t : ℝ => (a, t)) (ContinuousLinearMap.inr ℝ A ℝ) θ :=
    hasFDerivAt_prodMk_right a θ
  have h2 := hG.hasFDerivAt.comp θ h1
  have e : (fun t => G (a, t)) = G ∘ (fun t : ℝ => (a, t)) := rfl
  show fderiv ℝ (fun t => G (a, t)) θ 1 = _
  rw [e, h2.fderiv]
  rfl

/-- The `a`-partial derivative of a jointly differentiable `G : A × ℝ → ℝ`. -/
theorem gp1_fderiv_partial_eq {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] {G : A × ℝ → ℝ}
    {a : A} {θ : ℝ} (hG : DifferentiableAt ℝ G (a, θ)) (v : A) :
    fderiv ℝ (fun b => G (b, θ)) a v = fderiv ℝ G (a, θ) (v, 0) := by
  have h1 : HasFDerivAt (fun b : A => (b, θ)) (ContinuousLinearMap.inl ℝ A ℝ) a :=
    hasFDerivAt_prodMk_left a θ
  have h2 := hG.hasFDerivAt.comp a h1
  have e : (fun b => G (b, θ)) = G ∘ (fun b : A => (b, θ)) := rfl
  rw [e, h2.fderiv]
  rfl

/-- The `θ`-partial derivative of a jointly `C^∞` map is jointly `C^∞`. -/
theorem gp1_contDiff_partial_deriv {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {G : A × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun q : A × ℝ => deriv (fun t => G (q.1, t)) q.2) := by
  have h : (fun q : A × ℝ => deriv (fun t => G (q.1, t)) q.2) = fun q => fderiv ℝ G q (0, 1) := by
    funext q
    exact gp1_deriv_partial_eq (hG.differentiable (by simp) _)
  rw [h]
  exact (hG.fderiv_right (by simp)).clm_apply contDiff_const

/-- Derivative of `z ↦ fderiv G z w`. -/
theorem gp1_fderiv_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : E → ℝ}
    (hG : ContDiff ℝ ∞ G) (z v w : E) :
    fderiv ℝ (fun z => fderiv ℝ G z w) z v = fderiv ℝ (fderiv ℝ G) z v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ G) z :=
    (hG.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const w z)
  rw [h.fderiv]
  simp

/-- Mixed partials commute: `∂_a ∂_θ G = ∂_θ ∂_a G` for a jointly `C^∞` map. -/
theorem gp1_mixed {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] {G : A × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (a : A) (θ : ℝ) (v : A) :
    fderiv ℝ (fun b => deriv (fun t => G (b, t)) θ) a v =
      deriv (fun t => fderiv ℝ (fun b => G (b, t)) a v) θ := by
  have hd : ∀ z, DifferentiableAt ℝ G z := fun z => hG.differentiable (by simp) z
  have e1 : (fun b => deriv (fun t => G (b, t)) θ) = fun b => fderiv ℝ G (b, θ) (0, 1) := by
    funext b; exact gp1_deriv_partial_eq (hd _)
  have e2 : (fun t => fderiv ℝ (fun b => G (b, t)) a v) = fun t => fderiv ℝ G (a, t) (v, 0) := by
    funext t; exact gp1_fderiv_partial_eq (hd _) v
  rw [e1, e2]
  have hF : ContDiff ℝ ∞ (fun z => fderiv ℝ G z (0, 1)) :=
    (hG.fderiv_right (by simp)).clm_apply contDiff_const
  have hF' : ContDiff ℝ ∞ (fun z => fderiv ℝ G z (v, 0)) :=
    (hG.fderiv_right (by simp)).clm_apply contDiff_const
  rw [gp1_fderiv_partial_eq (G := fun z => fderiv ℝ G z (0, 1)) (hF.differentiable (by simp) _) v]
  rw [gp1_deriv_partial_eq (G := fun z => fderiv ℝ G z (v, 0)) (hF'.differentiable (by simp) _)]
  rw [gp1_fderiv_fderiv_apply hG, gp1_fderiv_fderiv_apply hG]
  exact (hG.contDiffAt.isSymmSndFDerivAt ContactMotions.minSmoothness_two_le) _ _

/-- The cut-off Hamiltonian `χ · h(y)` satisfies the row-86 hypotheses. -/
theorem gp1_contactMotionsHyp_bump (χ : ContDiffBump (0 : ℝ³)) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContactMotionsHyp (fun p : ℝ³ => χ p * h (p 1)) where
  smooth := χ.contDiff.mul (hh.comp (ContactMotions.contDiff_coord 1))
  compactSupport := χ.hasCompactSupport.mul_right

/-- The `x`-component of `X_H` for `H = χ · h(y)` at a point where `χ = 1` nearby is `−h′(y)`
(sm-3:2647 "their infinitesimal `x` changes"). -/
theorem gp1_hamVF_zero_bump (χ : ContDiffBump (0 : ℝ³)) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {p : ℝ³} (hp : p ∈ Metric.ball (0 : ℝ³) χ.rIn) :
    hamVF (fun p : ℝ³ => χ p * h (p 1)) p 0 = -deriv h (p 1) := by
  rw [ContactMotions.hamVF_apply_zero]
  congr 1
  have hev : (fun p : ℝ³ => χ p * h (p 1)) =ᶠ[𝓝 p] fun p => h (p 1) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hp] with q hq
    rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hq), one_mul]
  have hd : HasFDerivAt (fun p : ℝ³ => h (p 1)) (deriv h (p 1) • ContactMotions.coordCLM 1) p :=
    ((hh.differentiable (by simp) (p 1)).hasDerivAt).comp_hasFDerivAt p
      (ContactMotions.hasFDerivAt_coord 1 p)
  simp only [ContactMotions.pd, hev.fderiv_eq, hd.fderiv]
  simp [ContactMotions.e]

/-- A nonzero `2×2` minor of a linear map into `ℝ^2` makes it onto (FR-PA-2 "rank `q`"). -/
theorem gp1_range_eq_top_of_minor {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : X →L[ℝ] ℝ^2) (u v : X)
    (hm : T u 0 * T v 1 - T u 1 * T v 0 ≠ 0) : T.range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro w
  refine ⟨((w 0 * T v 1 - w 1 * T v 0) / (T u 0 * T v 1 - T u 1 * T v 0)) • u +
    ((T u 0 * w 1 - T u 1 * w 0) / (T u 0 * T v 1 - T u 1 * T v 0)) • v, ?_⟩
  have key : ∀ k : Fin 2, T (((w 0 * T v 1 - w 1 * T v 0) / (T u 0 * T v 1 - T u 1 * T v 0)) • u +
      ((T u 0 * w 1 - T u 1 * w 0) / (T u 0 * T v 1 - T u 1 * T v 0)) • v) k = w k := by
    intro k
    simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    fin_cases k
    · show _ * T u 0 + _ * T v 0 = w 0
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hm]
      ring
    · show _ * T u 1 + _ * T v 1 = w 1
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hm]
      ring
  ext k
  exact key k

theorem gp1_finrank_eq_two_of_minor {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : X →L[ℝ] ℝ^2) (u v : X)
    (hm : T u 0 * T v 1 - T u 1 * T v 0 ≠ 0) : Module.finrank ℝ T.range = 2 :=
  (rank_eq_iff_range_eq_top T).2 (gp1_range_eq_top_of_minor T u v hm)

/-- One period is compact in `ℝ^1`. -/
theorem gp1_isCompact_Kper1 : IsCompact Kper1 := by
  have h : Kper1 =
      (fun θ : ℝ => θ • (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : ℝ^1)) '' Icc 0 (2 * π) := by
    ext z
    constructor
    · intro hz
      refine ⟨z 0, hz, ?_⟩
      ext i
      fin_cases i
      simp
    · rintro ⟨θ, hθ, rfl⟩
      simpa [Kper1] using hθ
  rw [h]
  exact isCompact_Icc.image (continuous_id.smul continuous_const)

/-- Coordinates of a derivative into `ℝ^2`. -/
theorem gp1_fderiv_apply_coord2 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ^2} {p : X} (hf : DifferentiableAt ℝ f p) (v : X) (i : Fin 2) :
    fderiv ℝ f p v i = fderiv ℝ (fun q => f q i) p v := by
  have h := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i : ℝ^2 →L[ℝ] ℝ).hasFDerivAt.comp p hf.hasFDerivAt
  have e : (fun q => f q i) = ⇑(PiLp.proj 2 (fun _ : Fin 2 => ℝ) i : ℝ^2 →L[ℝ] ℝ) ∘ f := rfl
  rw [e, h.fderiv]
  rfl

/-- The joint map `(a, θ) ↦ x_a(θ)` on `ℝ^n × ℝ` is `C^∞` (row 86 `compositions_smooth`). -/
theorem gp1_contDiff_xJoint (L : ℝ → ℝ³) (hLs : ContDiff ℝ ∞ L) (n : ℕ) (Hs : Fin n → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) :
    ContDiff ℝ ∞ (fun q : ℝ^n × ℝ => composeFlows n Hs (par q.1) (L q.2) 0) := by
  have hcomp := fd_contact_motions.compositions_smooth n Hs hHs
  have hpar : ContDiff ℝ ∞ (fun a : ℝ^n => par a) := (EuclideanSpace.equiv (Fin n) ℝ).contDiff
  exact (ContactMotions.contDiff_coord 0).comp
    (hcomp.comp ((hpar.comp contDiff_fst).prodMk (hLs.comp contDiff_snd)))

/-- P0.3 transported to the parameter space `ℝ^n`: `∂_{aᵢ} x_a(s)|₀ = X_{Hᵢ}(L s)_x`. -/
theorem gp1_fderiv_xJoint_zero (L : ℝ → ℝ³) (n : ℕ) (Hs : Fin n → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) (s : ℝ) (i : Fin n) :
    fderiv ℝ (fun b : ℝ^n => composeFlows n Hs (par b) (L s) 0) 0 (EuclideanSpace.single i 1) =
      hamVF (Hs i) (L s) 0 := by
  have hcomp := fd_contact_motions.compositions_smooth n Hs hHs
  have hΨd : DifferentiableAt ℝ (fun c : Fin n → ℝ => composeFlows n Hs c (L s)) 0 :=
    (hcomp.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) 0
  have hcd : DifferentiableAt ℝ (fun p : ℝ³ => p 0)
      ((fun c : Fin n → ℝ => composeFlows n Hs c (L s)) 0) :=
    (ContactMotions.contDiff_coord 0).differentiable (by simp) _
  have e : (fun b : ℝ^n => composeFlows n Hs (par b) (L s) 0) =
      ((fun p : ℝ³ => p 0) ∘ (fun c : Fin n → ℝ => composeFlows n Hs c (L s))) ∘
        ⇑(EuclideanSpace.equiv (Fin n) ℝ) := rfl
  have hE0 : (EuclideanSpace.equiv (Fin n) ℝ) 0 = 0 := map_zero _
  have hE1 : (EuclideanSpace.equiv (Fin n) ℝ) (EuclideanSpace.single i 1) = Pi.single i 1 := by
    funext j; simp [Pi.single_apply]
  rw [e, (EuclideanSpace.equiv (Fin n) ℝ).comp_right_fderiv, hE0, fderiv_comp 0 hcd hΨd,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, hE1, ContactMotions.fderiv_coord,
    fderiv_composeFlows_zero n Hs hHs (L s) i]

/-- `cuspMap` is `C^∞`: two `θ`-derivatives of the jointly smooth `x_a(θ)`. -/
theorem gp1_contDiff_cuspMap (L : ℝ → ℝ³) (hLs : ContDiff ℝ ∞ L) (n : ℕ) (Hs : Fin n → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) : ContDiff ℝ ∞ (cuspMap L n Hs) := by
  have hG : ContDiff ℝ ∞ (fun q : ℝ^n × ℝ => composeFlows n Hs (par q.1) (L q.2) 0) :=
    gp1_contDiff_xJoint L hLs n Hs hHs
  have hG1 := gp1_contDiff_partial_deriv hG
  have hG2 := gp1_contDiff_partial_deriv hG1
  have hproj : ContDiff ℝ ∞ (fun z : ℝ^1 => z 0) := by
    have hp := (PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0 : ℝ^1 →L[ℝ] ℝ).contDiff (n := ∞)
    exact hp
  have hΛ : ContDiff ℝ ∞ (fun z : ℝ^1 × ℝ^n => (z.2, z.1 0)) :=
    contDiff_snd.prodMk (hproj.comp contDiff_fst)
  rw [contDiff_euclidean]
  intro k
  fin_cases k
  · exact hG1.comp hΛ
  · exact hG2.comp hΛ

/-- The parameter-`i` column of `D(cuspMap)` at `(θ, 0)`: `(gᵢ′(θ), gᵢ″(θ))` with
`gᵢ(s) = X_{Hᵢ}(L s)_x` (sm-3:2647-2651, via P0.3 and the symmetry of mixed partials). -/
theorem gp1_cuspMap_column (L : ℝ → ℝ³) (hLs : ContDiff ℝ ∞ L) (n : ℕ) (Hs : Fin n → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) (t : ℝ^1) (i : Fin n) :
    fderiv ℝ (cuspMap L n Hs) (t, 0) (0, EuclideanSpace.single i 1) 0 =
        deriv (fun s => hamVF (Hs i) (L s) 0) (t 0) ∧
      fderiv ℝ (cuspMap L n Hs) (t, 0) (0, EuclideanSpace.single i 1) 1 =
        deriv (deriv (fun s => hamVF (Hs i) (L s) 0)) (t 0) := by
  have hG : ContDiff ℝ ∞ (fun q : ℝ^n × ℝ => composeFlows n Hs (par q.1) (L q.2) 0) :=
    gp1_contDiff_xJoint L hLs n Hs hHs
  have hG1 : ContDiff ℝ ∞ (fun q : ℝ^n × ℝ =>
      deriv (fun s => composeFlows n Hs (par q.1) (L s) 0) q.2) :=
    gp1_contDiff_partial_deriv hG
  have hG2 : ContDiff ℝ ∞ (fun q : ℝ^n × ℝ =>
      deriv (fun s => deriv (fun r => composeFlows n Hs (par q.1) (L r) 0) s) q.2) :=
    gp1_contDiff_partial_deriv hG1
  let Λ : ℝ^1 × ℝ^n →L[ℝ] ℝ^n × ℝ := (ContinuousLinearMap.snd ℝ (ℝ^1) (ℝ^n)).prod
    ((EuclideanSpace.proj (0 : Fin 1)).comp (ContinuousLinearMap.fst ℝ (ℝ^1) (ℝ^n)))
  have hF0 : (fun z => cuspMap L n Hs z 0) =
      (fun q : ℝ^n × ℝ => deriv (fun s => composeFlows n Hs (par q.1) (L s) 0) q.2) ∘ Λ := rfl
  have hF1 : (fun z => cuspMap L n Hs z 1) =
      (fun q : ℝ^n × ℝ =>
        deriv (fun s => deriv (fun r => composeFlows n Hs (par q.1) (L r) 0) s) q.2) ∘ Λ := rfl
  have hF : ContDiff ℝ ∞ (cuspMap L n Hs) := gp1_contDiff_cuspMap L hLs n Hs hHs
  have key0 : ∀ s, fderiv ℝ (fun b : ℝ^n => composeFlows n Hs (par b) (L s) 0) 0
      (EuclideanSpace.single i 1) = hamVF (Hs i) (L s) 0 :=
    fun s => gp1_fderiv_xJoint_zero L n Hs hHs s i
  have key1 : ∀ s, fderiv ℝ (fun b : ℝ^n => deriv (fun r => composeFlows n Hs (par b) (L r) 0) s) 0
      (EuclideanSpace.single i 1) = deriv (fun s => hamVF (Hs i) (L s) 0) s := by
    intro s
    rw [gp1_mixed hG]
    congr 1
    funext r
    exact key0 r
  have key2 : fderiv ℝ (fun b : ℝ^n =>
      deriv (fun s => deriv (fun r => composeFlows n Hs (par b) (L r) 0) s) (t 0)) 0
      (EuclideanSpace.single i 1) = deriv (deriv (fun s => hamVF (Hs i) (L s) 0)) (t 0) := by
    rw [gp1_mixed hG1]
    congr 1
    funext r
    exact key1 r
  have hFd : DifferentiableAt ℝ (cuspMap L n Hs) (t, 0) := hF.differentiable (by simp) _
  have hΛz : Λ (t, 0) = (0, t 0) := rfl
  have hΛw : Λ (0, EuclideanSpace.single i 1) = (EuclideanSpace.single i 1, 0) := by
    refine Prod.ext rfl ?_
    show (0 : ℝ^1) 0 = 0
    simp
  constructor
  · rw [gp1_fderiv_apply_coord2 hFd, hF0]
    have h := (hG1.differentiable (by simp) (Λ (t, 0))).hasFDerivAt.comp (t, 0) Λ.hasFDerivAt
    rw [h.fderiv, ContinuousLinearMap.comp_apply, hΛw, hΛz,
      ← gp1_fderiv_partial_eq (hG1.differentiable (by simp) _)]
    exact key1 (t 0)
  · rw [gp1_fderiv_apply_coord2 hFd, hF1]
    have h := (hG2.differentiable (by simp) (Λ (t, 0))).hasFDerivAt.comp (t, 0) Λ.hasFDerivAt
    rw [h.fderiv, ContinuousLinearMap.comp_apply, hΛw, hΛz,
      ← gp1_fderiv_partial_eq (hG2.differentiable (by simp) _)]
    exact key2

/-- LEAF P1.1.  Bump Hamiltonians `H₂ = −½(y−y₀)²`, `H₃ = −⅙(y−y₀)³` at finitely many zeros of
`(x′,x″)` give a family with parameter rank `2` at every zero in `[0,2π] × B_r` (sm-3:2639-2652):
`ParameterAvoidanceHyp 1 n 2`. -/
theorem exists_cusp_avoidance (L : ℝ → ℝ³) (hL : GenericFrontHyp L) :
    ∃ (n : ℕ) (Hs : Fin n → ℝ³ → ℝ) (r : ℝ), (∀ i, ContactMotionsHyp (Hs i)) ∧ 0 < r ∧
      ParameterAvoidanceHyp 1 n 2 Kper1 0 r (cuspMap L n Hs) := by
  have hLs := hL.circle.smooth
  -- a ball containing the curve
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ θ, L θ ∈ Metric.ball (0 : ℝ³) R := by
    obtain ⟨R', hR'⟩ := (Metric.isBounded_iff_subset_closedBall 0).1
      (isCompact_Icc.image hLs.continuous).isBounded
    refine ⟨max R' 0 + 1, by positivity, fun θ => ?_⟩
    have hmem : L θ ∈ Metric.closedBall (0 : ℝ³) R' := by
      have hθ' := toIcoMod_mem_Ico Real.two_pi_pos 0 θ
      rw [zero_add] at hθ'
      have hLθ : L θ = L (toIcoMod Real.two_pi_pos 0 θ) := by
        conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 θ]
        exact hL.circle.periodic.zsmul _ _
      rw [hLθ]
      exact hR' ⟨_, Ico_subset_Icc_self hθ', rfl⟩
    rw [Metric.mem_closedBall] at hmem
    rw [Metric.mem_ball]
    calc dist (L θ) 0 ≤ R' := hmem
      _ ≤ max R' 0 := le_max_left _ _
      _ < max R' 0 + 1 := by linarith
  -- the cut-off `χ` (equal to `1` on the curve) and the two Hamiltonians `χ cos y`, `χ sin y`
  let χ : ContDiffBump (0 : ℝ³) := ⟨R, R + 1, hR0, by linarith⟩
  let h : Fin 2 → ℝ → ℝ := ![Real.cos, Real.sin]
  have hh : ∀ i, ContDiff ℝ ∞ (h i) := by
    intro i
    fin_cases i
    · exact Real.contDiff_cos
    · exact Real.contDiff_sin
  let Hs : Fin 2 → ℝ³ → ℝ := fun i p => χ p * h i (p 1)
  have hHs : ∀ i, ContactMotionsHyp (Hs i) := fun i => gp1_contactMotionsHyp_bump χ (hh i)
  -- `gᵢ(s) = X_{Hᵢ}(L s)_x = −hᵢ′(y(s))`
  have hg : ∀ i s, hamVF (Hs i) (L s) 0 = -deriv (h i) (coordY L s) := fun i s =>
    gp1_hamVF_zero_bump χ (hh i) (hR s)
  have hy : ContDiff ℝ ∞ (coordY L) := (ContactMotions.contDiff_coord 1).comp hLs
  have hy' : ContDiff ℝ ∞ (deriv (coordY L)) := (contDiff_infty_iff_deriv.1 hy).2
  have hyd : ∀ s, HasDerivAt (coordY L) (deriv (coordY L) s) s :=
    fun s => (hy.differentiable (by simp) s).hasDerivAt
  have hyd' : ∀ s, HasDerivAt (deriv (coordY L)) (deriv (deriv (coordY L)) s) s :=
    fun s => (hy'.differentiable (by simp) s).hasDerivAt
  have hg0 : (fun s => hamVF (Hs 0) (L s) 0) = fun s => Real.sin (coordY L s) := by
    funext s; rw [hg 0 s]; simp [h]
  have hg1 : (fun s => hamVF (Hs 1) (L s) 0) = fun s => -Real.cos (coordY L s) := by
    funext s; rw [hg 1 s]; simp [h]
  have d01 : deriv (fun s => Real.sin (coordY L s)) =
      fun s => Real.cos (coordY L s) * deriv (coordY L) s := by
    funext s; exact ((Real.hasDerivAt_sin _).comp s (hyd s)).deriv
  have d11 : deriv (fun s => -Real.cos (coordY L s)) =
      fun s => Real.sin (coordY L s) * deriv (coordY L) s := by
    funext s
    have hc : HasDerivAt (fun s => -Real.cos (coordY L s))
        (-(-Real.sin (coordY L s) * deriv (coordY L) s)) s :=
      ((Real.hasDerivAt_cos _).comp s (hyd s)).neg
    rw [hc.deriv]; ring
  have d02 : ∀ θ, deriv (deriv (fun s => Real.sin (coordY L s))) θ =
      -Real.sin (coordY L θ) * deriv (coordY L) θ ^ 2 +
        Real.cos (coordY L θ) * deriv (deriv (coordY L)) θ := by
    intro θ; rw [d01]
    have hc : HasDerivAt (fun s => Real.cos (coordY L s) * deriv (coordY L) s)
        (-Real.sin (coordY L θ) * deriv (coordY L) θ * deriv (coordY L) θ +
          Real.cos (coordY L θ) * deriv (deriv (coordY L)) θ) θ :=
      ((Real.hasDerivAt_cos _).comp θ (hyd θ)).mul (hyd' θ)
    rw [hc.deriv]; ring
  have d12 : ∀ θ, deriv (deriv (fun s => -Real.cos (coordY L s))) θ =
      Real.cos (coordY L θ) * deriv (coordY L) θ ^ 2 +
        Real.sin (coordY L θ) * deriv (deriv (coordY L)) θ := by
    intro θ; rw [d11]
    have hc : HasDerivAt (fun s => Real.sin (coordY L s) * deriv (coordY L) s)
        (Real.cos (coordY L θ) * deriv (coordY L) θ * deriv (coordY L) θ +
          Real.sin (coordY L θ) * deriv (deriv (coordY L)) θ) θ :=
      ((Real.hasDerivAt_sin _).comp θ (hyd θ)).mul (hyd' θ)
    rw [hc.deriv]; ring
  have d01' : ∀ θ, deriv (fun s => Real.sin (coordY L s)) θ =
      Real.cos (coordY L θ) * deriv (coordY L) θ := fun θ => by rw [d01]
  have d11' : ∀ θ, deriv (fun s => -Real.cos (coordY L s)) θ =
      Real.sin (coordY L θ) * deriv (coordY L) θ := fun θ => by rw [d11]
  -- the map, its smoothness, the `2×2` minor of the two parameter columns
  have hF : ContDiff ℝ ∞ (cuspMap L 2 Hs) := gp1_contDiff_cuspMap L hLs 2 Hs hHs
  let u : Fin 2 → ℝ^1 × ℝ^2 := fun i => (0, EuclideanSpace.single i 1)
  let m : ℝ^1 × ℝ^2 → ℝ := fun z =>
    fderiv ℝ (cuspMap L 2 Hs) z (u 0) 0 * fderiv ℝ (cuspMap L 2 Hs) z (u 1) 1 -
      fderiv ℝ (cuspMap L 2 Hs) z (u 0) 1 * fderiv ℝ (cuspMap L 2 Hs) z (u 1) 0
  have hmc : Continuous m := by
    have hc : ∀ (w : ℝ^1 × ℝ^2) (k : Fin 2),
        Continuous fun z => fderiv ℝ (cuspMap L 2 Hs) z w k := fun w k =>
      (EuclideanSpace.proj k).continuous.comp
        ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact ((hc _ _).mul (hc _ _)).sub ((hc _ _).mul (hc _ _))
  -- the minor at `(θ, 0)` is `y′(θ)³` (sm-3:2650-2651, "determinant `(y′)³`")
  have hm0 : ∀ t : ℝ^1, m (t, 0) = deriv (coordY L) (t 0) ^ 3 := by
    intro t
    obtain ⟨c00, c01⟩ := gp1_cuspMap_column L hLs 2 Hs hHs t 0
    obtain ⟨c10, c11⟩ := gp1_cuspMap_column L hLs 2 Hs hHs t 1
    show fderiv ℝ (cuspMap L 2 Hs) (t, 0) (0, EuclideanSpace.single 0 1) 0 *
        fderiv ℝ (cuspMap L 2 Hs) (t, 0) (0, EuclideanSpace.single 1 1) 1 -
      fderiv ℝ (cuspMap L 2 Hs) (t, 0) (0, EuclideanSpace.single 0 1) 1 *
        fderiv ℝ (cuspMap L 2 Hs) (t, 0) (0, EuclideanSpace.single 1 1) 0 = _
    rw [c00, c01, c10, c11, hg0, hg1, d02, d12, d01', d11']
    have hcs := Real.cos_sq_add_sin_sq (coordY L (t 0))
    linear_combination (deriv (coordY L) (t 0)) ^ 3 * hcs
  -- a zero of `cuspMap` at `a = 0` is a zero of `x′`
  have hFz : ∀ t : ℝ^1, cuspMap L 2 Hs (t, 0) = 0 → deriv (coordX L) (t 0) = 0 := by
    intro t ht
    have hpar0 : par (0 : ℝ^2) = 0 := by funext j; simp [par]
    have hx0 : xParam L 2 Hs (par 0) = coordX L := by
      funext s
      simp only [xParam, hpar0]
      rw [ContactMotions.composeFlows_zero 2 Hs (fun i p => (hHs i).hamFlow_zero p)]
      rfl
    have h0 := congrFun (congrArg WithLp.ofLp ht) 0
    simp only [cuspMap, hx0] at h0
    simpa using h0
  -- the open set `W` of good points contains `Kper1 × {0}`; the tube lemma gives the radius
  have hW : IsOpen ({z | m z ≠ 0} ∪ {z | cuspMap L 2 Hs z ≠ 0}) :=
    (isOpen_ne_fun hmc continuous_const).union (isOpen_ne_fun hF.continuous continuous_const)
  have hsub : Kper1 ×ˢ ({0} : Set (ℝ^2)) ⊆ {z | m z ≠ 0} ∪ {z | cuspMap L 2 Hs z ≠ 0} := by
    rintro ⟨t, a⟩ ⟨-, ha⟩
    rw [mem_singleton_iff] at ha
    subst ha
    by_cases hF0 : cuspMap L 2 Hs (t, 0) = 0
    · left
      show m (t, 0) ≠ 0
      rw [hm0]
      exact pow_ne_zero 3 (gp1_deriv_y_ne_zero hL.circle hL.legendrian (hFz t hF0))
    · right
      exact hF0
  obtain ⟨u', v, -, hv, hKu, h0v, huv⟩ :=
    generalized_tube_lemma gp1_isCompact_Kper1 isCompact_singleton hW hsub
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hv 0 (h0v (mem_singleton 0))
  refine ⟨2, Hs, ε / 2, hHs, by positivity, ?_⟩
  refine ⟨gp1_isCompact_Kper1, ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩, ?_, by norm_num⟩
  rintro ⟨t, a⟩ ⟨ht, ha⟩ hz
  have hzW : (t, a) ∈ {z | m z ≠ 0} ∪ {z | cuspMap L 2 Hs z ≠ 0} :=
    huv ⟨hKu ht, hball (Metric.closedBall_subset_ball (by linarith) ha)⟩
  have hmz : m (t, a) ≠ 0 := by
    rcases hzW with hm | hm
    · exact hm
    · exact absurd hz hm
  exact gp1_finrank_eq_two_of_minor (fderiv ℝ (cuspMap L 2 Hs) (t, a)) (u 0) (u 1) hmz

/-- The derivative of a periodic function is periodic. -/
theorem gp1_periodic_deriv {f : ℝ → ℝ} {c : ℝ} (hf : Periodic f c) : Periodic (deriv f) c := by
  intro x
  have h : (fun y => f (y + c)) = f := funext hf
  rw [← deriv_comp_add_const f c x, h]

/-- LEAF P1.2.  A parameter avoiding the bad set gives `NoDoubleZero` (periodicity reduces every
`θ` to `[0,2π]`). -/
theorem noDoubleZero_of_notMem (L : ℝ → ℝ³) (hL : GenericFrontHyp L) (n : ℕ)
    (Hs : Fin n → ℝ³ → ℝ) (hHs : ∀ i, ContactMotionsHyp (Hs i)) {r : ℝ} {a : ℝ^n}
    (ha : a ∉ ParameterAvoidance.zeroParams Kper1 (Metric.closedBall 0 r) (cuspMap L n Hs))
    (har : a ∈ Metric.closedBall (0 : ℝ^n) r) : NoDoubleZero (composeFlows n Hs (par a) ∘ L) := by
  intro θ
  by_contra hcon
  simp only [not_or, not_not] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hx : coordX (composeFlows n Hs (par a) ∘ L) = xParam L n Hs (par a) := rfl
  rw [hx] at h1 h2
  apply ha
  refine ⟨har, ?_⟩
  have hper : Periodic (xParam L n Hs (par a)) (2 * π) := fun t => by
    simp only [xParam]; rw [hL.circle.periodic t]
  have hper' : Periodic (deriv (xParam L n Hs (par a))) (2 * π) := gp1_periodic_deriv hper
  have hper'' : Periodic (deriv (deriv (xParam L n Hs (par a)))) (2 * π) := gp1_periodic_deriv hper'
  set θ' := toIcoMod Real.two_pi_pos 0 θ with hθ'
  have hmem : θ' ∈ Ico 0 (2 * π) := by simpa using toIcoMod_mem_Ico Real.two_pi_pos 0 θ
  have hθeq : θ' = θ - toIcoDiv Real.two_pi_pos 0 θ • (2 * π) := by
    rw [hθ', eq_sub_iff_add_eq]; exact toIcoMod_add_toIcoDiv_zsmul _ _ _
  have e1 : deriv (xParam L n Hs (par a)) θ' = 0 := by
    rw [hθeq, hper'.sub_zsmul_eq]; exact h1
  have e2 : deriv (deriv (xParam L n Hs (par a))) θ' = 0 := by
    rw [hθeq, hper''.sub_zsmul_eq]; exact h2
  refine ⟨θ' • (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)), ?_, ?_⟩
  · show (θ' • (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) : ℝ^1) 0 ∈ Icc 0 (2 * π)
    simpa using Ico_subset_Icc_self hmem
  · have hz : ((θ' • (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) : ℝ^1) 0) = θ' := by simp
    simp only [cuspMap, hz, e1, e2]
    ext i; fin_cases i <;> simp

/-- LEAF P1.3.  Simple zeros of `x′` on the circle are finitely many (sm-3:2657). -/
theorem finite_cusps_of_stage1 {L : ℝ → ℝ³} (h : Stage1 L) : (cuspSet L ∩ Ico 0 (2 * π)).Finite := by
  by_contra hinf
  have hx : ContDiff ℝ ∞ (coordX L) := (ContactMotions.contDiff_coord 0).comp h.circle.smooth
  have hx' : ContDiff ℝ ∞ (deriv (coordX L)) := (contDiff_infty_iff_deriv.1 hx).2
  obtain ⟨θ, -, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc
    (inter_subset_right.trans Ico_subset_Icc_self)
  have hcl : IsClosed (cuspSet L) := isClosed_eq hx'.continuous continuous_const
  have hθc : θ ∈ cuspSet L := by
    have h1 : θ ∈ closure (cuspSet L ∩ Ico 0 (2 * π)) :=
      mem_closure_iff_clusterPt.2 hacc.clusterPt
    exact hcl.closure_subset (closure_mono inter_subset_left h1)
  have h2 : deriv (deriv (coordX L)) θ ≠ 0 := (h.noDoubleZero θ).resolve_left (not_not.2 hθc)
  have hd : HasDerivAt (deriv (coordX L)) (deriv (deriv (coordX L)) θ) θ :=
    (hx'.differentiable (by simp) θ).hasDerivAt
  have hev : ∀ᶠ z in 𝓝[≠] θ, deriv (coordX L) z ≠ 0 := hd.eventually_ne h2
  rw [eventually_nhdsWithin_iff] at hev
  rw [accPt_iff_frequently] at hacc
  obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ := (hacc.and_eventually hev).exists
  exact hz3 hz1 hz2.1

/-- LEAF P1.4.  At a cusp `y′ ≠ 0` (immersion + `z′ = y x′`, sm-3:2640, 2658). -/
theorem deriv_y_ne_zero_at_cusp {L : ℝ → ℝ³} (h : Stage1 L) {θ : ℝ} (hθ : θ ∈ cuspSet L) :
    deriv (coordY L) θ ≠ 0 := by
  exact gp1_deriv_y_ne_zero h.circle h.legendrian hθ

/-- Step 1 assembled (sm-3:2639-2658): a contact isotopy to a `Stage1` curve. -/
theorem step1 (L : ℝ → ℝ³) (hL : GenericFrontHyp L) :
    ∃ Φ : ℝ → ℝ³ → ℝ³, IsContactIsotopy Φ ∧ Stage1 (Φ 1 ∘ L) := by
  obtain ⟨n, Hs, r, hHs, hr, hpa⟩ := exists_cusp_avoidance L hL
  obtain ⟨a, har, -, hav⟩ := exists_param_avoiding (ι := Unit) (d := fun _ => 1) (q := fun _ => 2)
    (K := fun _ => Kper1) (F := fun _ => cuspMap L n Hs) (fun _ => hpa) hr one_pos
  refine ⟨hamIsotopy n Hs (par a), isContactIsotopy_hamIsotopy n Hs (par a) hHs, ?_⟩
  have hΦ := isContactIsotopy_hamIsotopy n Hs (par a) hHs
  obtain ⟨hc, hl⟩ := contact_preserves_legendrian hΦ hL.circle hL.legendrian ⟨zero_le_one, le_rfl⟩
  rw [hamIsotopy_one] at hc hl ⊢
  exact ⟨hc, hl, noDoubleZero_of_notMem L hL n Hs hHs (hav ()) har⟩

/-! ### Unit P2 — the uniform collar (sm-3:2659-2685) -/

/-- LEAF P2.1.  A `Stage1` front is uniformly locally injective: regular intervals (`x′` of fixed
sign, `x` monotone) and critical intervals (one simple zero of `x′`, `y′` of fixed sign; for
`θ₁ < θ_c < θ₂` with `x(θ₁) = x(θ₂) = X`, `z(θ₂) − z(θ₁) = ∫ y′(θ)(X − x(θ)) dθ ≠ 0` by integration
by parts from `z′ = y x′`), Lebesgue number of the cover. -/
theorem exists_collar {L : ℝ → ℝ³} (h : Stage1 L) : ∃ δc, LocallyInjectiveFront L δc := by
  sorry

/-- LEAF P2.2.  `Stage1` and the collar persist for small parameters of any Hamiltonian family
(sm-3:2675-2677, 2709-2710): the sign margins are open conditions in `a` on compact `θ`-intervals
(joint smoothness of `(θ,a) ↦ Φ_a(L θ)`, `generalized_tube_lemma`). -/
theorem stage1_stable {L : ℝ → ℝ³} (h : Stage1 L) {δc : ℝ} (hδ : LocallyInjectiveFront L δc)
    (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (hHs : ∀ i, ContactMotionsHyp (Hs i)) :
    ∃ r > 0, ∀ a : ℝ^m, ‖a‖ < r →
      Stage1 (composeFlows m Hs (par a) ∘ L) ∧ LocallyInjectiveFront (composeFlows m Hs (par a) ∘ L) δc := by
  sorry

/-! ### Unit P3 — cusps on branches and triple points (sm-3:2686-2714; row 85 with `(2,3)`, `(3,4)`) -/

/-- `C(θ,η,a) = (x_a′(θ), p_a(θ) − p_a(η)) ∈ ℝ³` (sm-3:2687-2688). -/
def Cmap (L : ℝ → ℝ³) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (z : ℝ^2 × ℝ^m) : ℝ^3 :=
  !₂[deriv (xParam L m Hs (par z.2)) (z.1 0),
    (frontParam L m Hs (par z.2) (z.1 0)).1 - (frontParam L m Hs (par z.2) (z.1 1)).1,
    (frontParam L m Hs (par z.2) (z.1 0)).2 - (frontParam L m Hs (par z.2) (z.1 1)).2]
/-- `R(θ,η,τ,a) = (p_a(θ) − p_a(η), p_a(θ) − p_a(τ)) ∈ ℝ⁴` (sm-3:2689-2690). -/
def Rmap (L : ℝ → ℝ³) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (z : ℝ^3 × ℝ^m) : ℝ^4 :=
  !₂[(frontParam L m Hs (par z.2) (z.1 0)).1 - (frontParam L m Hs (par z.2) (z.1 1)).1,
    (frontParam L m Hs (par z.2) (z.1 0)).2 - (frontParam L m Hs (par z.2) (z.1 1)).2,
    (frontParam L m Hs (par z.2) (z.1 0)).1 - (frontParam L m Hs (par z.2) (z.1 2)).1,
    (frontParam L m Hs (par z.2) (z.1 0)).2 - (frontParam L m Hs (par z.2) (z.1 2)).2]
/-- `K₂`: ordered pairs in one period at circular distance `≥ δc` (sm-3:2685-2686). -/
def K2 (δc : ℝ) : Set (ℝ^2) :=
  {z | z 0 ∈ Icc 0 (2 * π) ∧ z 1 ∈ Icc 0 (2 * π) ∧ δc ≤ circDist (z 0) (z 1)}
/-- `K₃`: ordered triples in one period, pairwise at circular distance `≥ δc`. -/
def K3 (δc : ℝ) : Set (ℝ^3) :=
  {z | z 0 ∈ Icc 0 (2 * π) ∧ z 1 ∈ Icc 0 (2 * π) ∧ z 2 ∈ Icc 0 (2 * π) ∧
    δc ≤ circDist (z 0) (z 1) ∧ δc ≤ circDist (z 0) (z 2) ∧ δc ≤ circDist (z 1) (z 2)}

/-- LEAF P3.1 (local tool).  Hamiltonians equal near `q` to `H^x = −(y − y_q)` and `H^z = 1` have
`X_H = (1, 0, y_q)` and `(0, 0, 1)` at points where the bump is `1` (sm-3:2699-2701); `H₂ = −½(y−y₀)²`
has `x`-velocity `y − y₀` and vanishes where `y = y₀` (sm-3:2641-2646). -/
theorem hamVF_local_models (q : ℝ³) (χ : ℝ³ → ℝ) (hχ : χ =ᶠ[𝓝 q] 1) :
    hamVF (fun p => χ p * (-(p 1 - q 1))) q = !₂[1, 0, q 1] ∧
    hamVF (fun p => χ p * 1) q = !₂[0, 0, 1] ∧
    hamVF (fun p => χ p * (-(1 / 2) * (p 1 - q 1) ^ 2)) q = 0 := by
  sorry

/-- LEAF P3.2.  One Hamiltonian family serving both `C` and `R` with a common parameter ball of
radius `≤ r₀` (sm-3:2695-2710): disjoint bumps at the distinct spatial points of each zero,
block-triangular minors of ranks `3` and `4`, finitely many zeros covered, uniform ball. -/
theorem exists_CR_avoidance {L : ℝ → ℝ³} (h : Stage1 L) {δc : ℝ} (hδ : LocallyInjectiveFront L δc)
    (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (r : ℝ), (∀ i, ContactMotionsHyp (Hs i)) ∧ 0 < r ∧ r ≤ r₀ ∧
      ParameterAvoidanceHyp 2 m 3 (K2 δc) 0 r (Cmap L m Hs) ∧
      ParameterAvoidanceHyp 3 m 4 (K3 δc) 0 r (Rmap L m Hs) := by
  sorry

/-- LEAF P3.3.  `C ≠ 0` on `K₂ × {a}` plus the collar give `NoCuspOnBranch` (pairs closer than
`δc` are handled by local injectivity; others are reduced to one period). -/
theorem noCuspOnBranch_of_C {L : ℝ → ℝ³} (h : Stage1 L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) {δc r : ℝ} {a : ℝ^m}
    (hδa : LocallyInjectiveFront (composeFlows m Hs (par a) ∘ L) δc)
    (ha : a ∉ ParameterAvoidance.zeroParams (K2 δc) (Metric.closedBall 0 r) (Cmap L m Hs))
    (har : a ∈ Metric.closedBall (0 : ℝ^m) r) : NoCuspOnBranch (composeFlows m Hs (par a) ∘ L) := by
  sorry

/-- LEAF P3.4.  `R ≠ 0` on `K₃ × {a}` plus the collar give `NoTriple`. -/
theorem noTriple_of_R {L : ℝ → ℝ³} (h : Stage1 L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) {δc r : ℝ} {a : ℝ^m}
    (hδa : LocallyInjectiveFront (composeFlows m Hs (par a) ∘ L) δc)
    (ha : a ∉ ParameterAvoidance.zeroParams (K3 δc) (Metric.closedBall 0 r) (Rmap L m Hs))
    (har : a ∈ Metric.closedBall (0 : ℝ^m) r) : NoTriple (composeFlows m Hs (par a) ∘ L) := by
  sorry

/-- Steps 2–3 assembled (sm-3:2659-2714). -/
theorem step2 {L : ℝ → ℝ³} (h : Stage1 L) :
    ∃ Φ : ℝ → ℝ³ → ℝ³, IsContactIsotopy Φ ∧ Stage2 (Φ 1 ∘ L) := by
  obtain ⟨δc, hδ⟩ := exists_collar h
  -- the stability radius depends on the family, the family on nothing but `L, δc`: obtain the
  -- family with a provisional radius `1`, then shrink.
  obtain ⟨m, Hs, r, hHs, hr, -, hC, hR⟩ := exists_CR_avoidance h hδ 1 one_pos
  obtain ⟨rs, hrs, hstab⟩ := stage1_stable h hδ m Hs hHs
  -- shrink the avoidance radius to `r' = min r (rs/2)` (monotonicity of `ParameterAvoidanceHyp`)
  have hmono : ∀ {d q : ℕ} {K : Set (ℝ^d)} {F : ℝ^d × ℝ^m → ℝ^q} {r' : ℝ}, 0 < r' → r' ≤ r →
      ParameterAvoidanceHyp d m q K 0 r F → ParameterAvoidanceHyp d m q K 0 r' F := by
    intro d q K F r' hr' hr'r hp
    refine ⟨hp.compact, ?_, ?_, hp.dim_lt⟩
    · obtain ⟨U, hU, hKU, hF⟩ := hp.smooth
      exact ⟨U, hU, (Set.prod_mono le_rfl (Metric.closedBall_subset_closedBall hr'r)).trans hKU, hF⟩
    · intro z hz hFz
      exact hp.rank z ⟨hz.1, Metric.closedBall_subset_closedBall hr'r hz.2⟩ hFz
  set r' := min r (rs / 2) with hr'def
  have hr'pos : 0 < r' := lt_min hr (by linarith)
  have hr'r : r' ≤ r := min_le_left _ _
  have hr'rs : r' < rs := (min_le_right _ _).trans_lt (by linarith)
  have hA := hmono hr'pos hr'r hC
  have hB := hmono hr'pos hr'r hR
  have hU : interior (ParameterAvoidance.zeroParams (K2 δc) (Metric.closedBall 0 r') (Cmap L m Hs) ∪
      ParameterAvoidance.zeroParams (K3 δc) (Metric.closedBall 0 r') (Rmap L m Hs)) = ∅ := by
    rw [interior_union_isClosed_of_interior_empty hA.isClosed_zeroParams
      hB.interior_zeroParams_eq_empty]
    exact hA.interior_zeroParams_eq_empty
  obtain ⟨a, hab, ha⟩ := (interior_eq_empty_iff_dense_compl.1 hU).exists_mem_open
    Metric.isOpen_ball (Metric.nonempty_ball.2 hr'pos)
  have hav : a ∉ ParameterAvoidance.zeroParams (K2 δc) (Metric.closedBall 0 r') (Cmap L m Hs) ∧
      a ∉ ParameterAvoidance.zeroParams (K3 δc) (Metric.closedBall 0 r') (Rmap L m Hs) := by
    simpa [Set.mem_union, not_or] using hab
  have har : a ∈ Metric.closedBall (0 : ℝ^m) r' := Metric.ball_subset_closedBall ha
  have hnorm : ‖a‖ < rs := by
    have := Metric.mem_closedBall.1 har; rw [dist_zero_right] at this; linarith
  obtain ⟨hs1, hδa⟩ := hstab a hnorm
  refine ⟨hamIsotopy m Hs (par a), isContactIsotopy_hamIsotopy m Hs (par a) hHs, ?_⟩
  rw [hamIsotopy_one]
  exact { hs1 with
    collar := ⟨δc, hδa⟩
    noCuspOnBranch := noCuspOnBranch_of_C h m Hs hHs hδa hav.1 har
    noTriple := noTriple_of_R h m Hs hHs hδa hav.2 har }

/-! ### Unit P4 — transverse, finite double points (sm-3:2715-2730) -/

/-- LEAF P4.1.  Every double point of a `Stage2` front is transverse: both parameters regular
(`NoCuspOnBranch`), `y(θ) ≠ y(η)` (embeddedness), determinant `x′(θ)x′(η)(y(η) − y(θ)) ≠ 0`
from `z′ = y x′`. -/
theorem transverse_double_of_stage2 {L : ℝ → ℝ³} (h : Stage2 L) :
    ∀ p ∈ doublePoints L, IsTransverseDouble L p.1 p.2 := by
  sorry

/-- LEAF P4.2.  Transverse double points are isolated (IFT on `(θ,η) ↦ p(θ) − p(η)`), the pairs at
circular distance `≥ δc` form a compact set, so there are finitely many in one period square. -/
theorem finite_double_of_stage2 {L : ℝ → ℝ³} (h : Stage2 L)
    (ht : ∀ p ∈ doublePoints L, IsTransverseDouble L p.1 p.2) :
    (doublePoints L ∩ Ico 0 (2 * π) ×ˢ Ico 0 (2 * π)).Finite := by
  sorry

theorem step3 {L : ℝ → ℝ³} (h : Stage2 L) : Stage3 L :=
  { h with
    transverse_double := transverse_double_of_stage2 h
    finite_double := finite_double_of_stage2 h (transverse_double_of_stage2 h) }

/-! ### Unit P5 — exact semicubical cusp germs (sm-3:2731-2768) -/

/-- `ψ(y) = ∫_{y₀}^{y} (f(v) − q(v)) dv`, `q(v) = f(y₀) + A(v − y₀)²` (sm-3:2734-2736). -/
def cuspHam (f : ℝ → ℝ) (y₀ A y : ℝ) : ℝ := ∫ v in y₀..y, (f v - (f y₀ + A * (v - y₀) ^ 2))
/-- The explicit contact flow of `H = ψ(y)`: `(x, y, z) ↦ (x − sψ′(y), y, z + s(ψ(y) − yψ′(y)))`
(sm-3:2738-2740). -/
def cuspFlowMap (ψ : ℝ → ℝ) (s : ℝ) (p : ℝ³) : ℝ³ :=
  !₂[p 0 - s * deriv ψ (p 1), p 1, p 2 + s * (ψ (p 1) - p 1 * deriv ψ (p 1))]

/-- LEAF P5.1.  For `H(x,y,z) = ψ(y)` smooth compactly supported, `hamFlow H = cuspFlowMap ψ`
(`X_H = (−ψ′, 0, ψ − yψ′)`; the explicit map is a global flow; `hamFlow_unique`). -/
theorem hamFlow_of_y_only (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    hamFlow (fun p => ψ (p 1)) = cuspFlowMap ψ := by
  sorry

/-- LEAF P5.2.  Near a cusp `y` is a local parameter and `x = f(y)` with `f′(y₀) = 0`,
`f″(y₀) = x″(θ_c)/y′(θ_c)² ≠ 0` (1-D inverse function theorem; sm-3:2732-2734). -/
theorem exists_local_graph {L : ℝ → ℝ³} (h : Stage3 L) {θc : ℝ} (hθc : θc ∈ cuspSet L) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ deriv f (coordY L θc) = 0 ∧ deriv (deriv f) (coordY L θc) ≠ 0 ∧
      ∀ᶠ θ in 𝓝 θc, coordX L θ = f (coordY L θ) := by
  sorry

/-- LEAF P5.3.  The exact germ after the time-one map (sm-3:2741-2747): if near `θc` the new curve
is `cuspFlowMap ψ 1 ∘ L` with `ψ = cuspHam f y₀ A`, `A = f″(y₀)/2`, then `x = x₀ + Au²`,
`z = z₀ + Ay₀u² + ⅔Au³` (`z` by Legendrianity: `dz/dy = y·2Au`). -/
theorem exactGerm_of_cuspFlow {L L' : ℝ → ℝ³} (h : Stage3 L) {θc : ℝ} (hθc : θc ∈ cuspSet L)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hf' : deriv f (coordY L θc) = 0)
    (hf'' : deriv (deriv f) (coordY L θc) ≠ 0) (hgraph : ∀ᶠ θ in 𝓝 θc, coordX L θ = f (coordY L θ))
    (hL' : ∀ᶠ θ in 𝓝 θc,
      L' θ = cuspFlowMap (cuspHam f (coordY L θc) (deriv (deriv f) (coordY L θc) / 2)) 1 (L θ)) :
    IsExactCuspGerm L' θc := by
  sorry

/-- LEAF P5.4.  Cut-off cusp Hamiltonians are `C²`-small (sm-3:2753-2758): with `f′(y₀) = 0`,
`f″(y₀) = 2A` one has `ψ = O(u⁴)` (`ψ′, ψ″, ψ‴ = O(u³), O(u²), O(u)`); a bump of radius `ε` has
derivatives `O(ε^{−k})`, so `‖D^k X_H‖ ≤ η` for `k ≤ 2` once `ε` is small; the Hamiltonian equals
`ψ(y)` on the inner ball.  (Without the two derivative hypotheses the statement is FALSE.) -/
theorem exists_small_cusp_hamiltonian (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (y₀ A : ℝ)
    (hf' : deriv f y₀ = 0) (hf'' : deriv (deriv f) y₀ = 2 * A) (pc : ℝ³)
    (hpc : pc 1 = y₀) {η : ℝ} (hη : 0 < η) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ (ε : ℝ) (H : ℝ³ → ℝ), 0 < ε ∧ ε ≤ ε₀ ∧ ContactMotionsHyp H ∧
      (∀ p ∈ Metric.ball pc (ε / 2), H p = cuspHam f y₀ A (p 1)) ∧
      tsupport H ⊆ Metric.closedBall pc ε ∧
      ∀ k ≤ 2, ∀ p, ‖iteratedFDeriv ℝ k (hamVF H) p‖ ≤ η := by
  sorry

/-- LEAF P5.5 (general).  The time-one map of a `C²`-small compactly supported field is `C²`-close
to the identity (sm-3:2758-2761: `J′ = DX·J`, `M′ = DX·M + D²X[J,J]`, Grönwall). -/
theorem flow_C2_close : ∃ C₀ > 0, ∀ (X : ℝ³ → ℝ³), ContDiff ℝ ∞ X → HasCompactSupport X →
    ∀ η, 0 < η → η ≤ 1 → (∀ k ≤ 2, ∀ p, ‖iteratedFDeriv ℝ k X p‖ ≤ η) →
      ∀ k ≤ 2, ∀ p, ‖iteratedFDeriv ℝ k (fun p => ContactMotions.globalFlow X 1 p - p) p‖ ≤ C₀ * η := by
  sorry

/-- LEAF P5.6.  Stability of `Stage3` under `C²`-small contactomorphisms supported near the cusps
that keep the cusp parameters (sm-3:2762-2766 "retain all previous genericity margins"): the
cusp set is unchanged and all `Stage3` properties persist (the contact hypothesis is what keeps
`legendrian`; the intended `Ψ = Φ 1` of P5.7 is contact by P0.1). -/
theorem stage3_stable {L : ℝ → ℝ³} (h : Stage3 L) :
    ∃ η > 0, ∃ rc > 0, ∀ Ψ : ℝ³ → ℝ³, ContDiff ℝ ∞ Ψ → Function.Bijective Ψ →
      (∀ p, ∃ c : ℝ, 0 < c ∧ ∀ v, alpha (Ψ p) (fderiv ℝ Ψ p v) = c * alpha p v) →
      (∀ k ≤ 2, ∀ p, ‖iteratedFDeriv ℝ k (fun p => Ψ p - p) p‖ ≤ η) →
      (∀ p, (∀ θc ∈ cuspSet L, rc ≤ dist p (L θc)) → Ψ p = p) →
      (∀ θc ∈ cuspSet L, deriv (coordX (Ψ ∘ L)) θc = 0) →
      cuspSet (Ψ ∘ L) = cuspSet L ∧ Stage3 (Ψ ∘ L) := by
  sorry

/-- LEAF P5.7 (assembly of P5.1–P5.6 over the finitely many cusps).  A contact isotopy, product of
the cut-off cusp flows in disjoint balls (P1.3, P1.4, P5.2, P5.4), whose time-one map is `C²`-close
to the identity (P5.5, compositions), fixes the cusp parameters and gives the exact germ at each
cusp (P5.1, P5.3: the inner subarc has displacement `O(ε³)` and never leaves the inner ball), so
`Stage3` persists (P5.6). -/
theorem exists_germ_isotopy {L : ℝ → ℝ³} (h : Stage3 L) :
    ∃ Φ : ℝ → ℝ³ → ℝ³, IsContactIsotopy Φ ∧ Stage3 (Φ 1 ∘ L) ∧
      ∀ θc ∈ cuspSet (Φ 1 ∘ L), IsExactCuspGerm (Φ 1 ∘ L) θc := by
  sorry

/-- The generic front (sm-3:2615-2625) from a `Stage3` curve with exact germs. -/
theorem isGenericFront_of_stage3 {L : ℝ → ℝ³} (h : Stage3 L)
    (hg : ∀ θc ∈ cuspSet L, IsExactCuspGerm L θc) : IsGenericFront L where
  finite_cusps := finite_cusps_of_stage1 h.toStage1
  exact_germ := hg
  finite_double := h.finite_double
  transverse_double := h.transverse_double
  no_triple := h.noTriple
  no_cusp_on_branch := h.noCuspOnBranch

/-! ### Unit P6 — concatenation, the chosen pushoff, the knot type (sm-3:2769-2783) -/

/-- Concatenation of two isotopies with the flat reparametrization `Real.smoothTransition`
(sm-3:2769-2770): `Φ` on `[0, ½]`, then `Ψ ∘ Φ_1` on `[½, 1]`. -/
def concat (Φ Ψ : ℝ → ℝ³ → ℝ³) (s : ℝ) (p : ℝ³) : ℝ³ :=
  if s ≤ 1 / 2 then Φ (Real.smoothTransition (2 * s)) p
  else Ψ (Real.smoothTransition (2 * s - 1)) (Φ 1 p)

theorem concat_one (Φ Ψ : ℝ → ℝ³ → ℝ³) (p : ℝ³) : concat Φ Ψ 1 p = Ψ 1 (Φ 1 p) := by
  have h : ¬ ((1 : ℝ) ≤ 1 / 2) := by norm_num
  simp only [concat, h, ite_false]
  norm_num [Real.smoothTransition.one_of_one_le]

/-- LEAF P6.1.  The concatenation of two contact isotopies is a contact isotopy (flatness of
`smoothTransition` at `0` and `1` gives joint smoothness across the join). -/
theorem isContactIsotopy_concat {Φ Ψ : ℝ → ℝ³ → ℝ³} (hΦ : IsContactIsotopy Φ)
    (hΨ : IsContactIsotopy Ψ) : IsContactIsotopy (concat Φ Ψ) := by
  sorry

/-- LEAF P6.2.  A stage of a contact isotopy carries a pushoff annulus of `L` to a pushoff annulus
of `Φ_s ∘ L` (sm-3:2773-2778: diffeomorphism + `Φ_s^*α = c_s α`, `c_s > 0`). -/
theorem pushoffAnnulus_map {Φ : ℝ → ℝ³ → ℝ³} (hΦ : IsContactIsotopy Φ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) {L : ℝ → ℝ³} {ε b : ℝ} {B : ℝ × ℝ → ℝ³} (hB : IsPushoffAnnulus L ε b B) :
    IsPushoffAnnulus (Φ s ∘ L) ε b fun q => Φ s (B q) := by
  sorry

/-- LEAF P6.3.  A positive transverse embedded circle moves through positive transverse embedded
circles under a contact isotopy (sm-3:2776-2779: `α((Φ_s∘K)′) = (c_s∘K) α(K′) > 0`). -/
theorem transverselyIsotopic_contact {Φ : ℝ → ℝ³ → ℝ³} (hΦ : IsContactIsotopy Φ) {K : ℝ → ℝ³}
    (hK : IsEmbeddedCircle K) (hKt : IsPositiveTransverse K) :
    TransverselyIsotopic K fun θ => Φ 1 (K θ) := by
  sorry

/-- LEAF P6.4.  The circles `B(·, s₀)` of a pushoff annulus are embedded circles. -/
theorem IsPushoffAnnulus.circle {L : ℝ → ℝ³} {ε b : ℝ} {B : ℝ × ℝ → ℝ³} (hB : IsPushoffAnnulus L ε b B)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (-ε) b) : IsEmbeddedCircle fun θ => B (θ, s₀) := by
  sorry

end GenericFront

open GenericFront

/-- **fd:generic-front** (sm-3:2613-2630), assembled from units P0–P6. -/
theorem fd_generic_front : GenericFrontData := by
  intro L hL
  obtain ⟨Φ₁, hΦ₁, hS1⟩ := step1 L hL
  obtain ⟨Φ₂, hΦ₂, hS2⟩ := step2 hS1
  have hS3 := step3 hS2
  obtain ⟨Φ₃, hΦ₃, hS3', hgerm⟩ := exists_germ_isotopy hS3
  have hΦ : IsContactIsotopy (concat (concat Φ₁ Φ₂) Φ₃) :=
    isContactIsotopy_concat (isContactIsotopy_concat hΦ₁ hΦ₂) hΦ₃
  have hfin : concat (concat Φ₁ Φ₂) Φ₃ 1 ∘ L = Φ₃ 1 ∘ (Φ₂ 1 ∘ (Φ₁ 1 ∘ L)) := by
    funext θ; simp [concat_one]
  have h1 : IsEmbeddedCircle (concat (concat Φ₁ Φ₂) Φ₃ 1 ∘ L) := by rw [hfin]; exact hS3'.circle
  have h2 : IsLegendrian (concat (concat Φ₁ Φ₂) Φ₃ 1 ∘ L) := by rw [hfin]; exact hS3'.legendrian
  have h3 : IsGenericFront (concat (concat Φ₁ Φ₂) Φ₃ 1 ∘ L) := by
    rw [hfin]; exact isGenericFront_of_stage3 hS3' hgerm
  refine ⟨concat (concat Φ₁ Φ₂) Φ₃, ⟨hΦ, h1, h2, h3, ?_, ?_⟩⟩
  · intro ε b B hB
    refine ⟨fun s hs => pushoffAnnulus_map hΦ hs hB, fun s₀ hs₀ hs₀b => ?_⟩
    have hK := hB.circle ⟨by linarith [hB.eps_pos], hs₀b⟩
    have hKt := hB.positive s₀ hs₀ hs₀b
    refine ⟨transverselyIsotopic_contact hΦ hK hKt, ?_⟩
    exact ⟨ε, b, fun q => concat (concat Φ₁ Φ₂) Φ₃ 1 (B q),
      pushoffAnnulus_map hΦ ⟨zero_le_one, le_rfl⟩ hB, s₀, hs₀, hs₀b, rfl⟩
  · exact ⟨concat (concat Φ₁ Φ₂) Φ₃, hΦ.ambient, fun θ => rfl⟩

end

end SM
