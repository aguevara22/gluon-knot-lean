import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Bounds
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

/-- LEAF P1.1.  Bump Hamiltonians `H₂ = −½(y−y₀)²`, `H₃ = −⅙(y−y₀)³` at finitely many zeros of
`(x′,x″)` give a family with parameter rank `2` at every zero in `[0,2π] × B_r` (sm-3:2639-2652):
`ParameterAvoidanceHyp 1 n 2`. -/
theorem exists_cusp_avoidance (L : ℝ → ℝ³) (hL : GenericFrontHyp L) :
    ∃ (n : ℕ) (Hs : Fin n → ℝ³ → ℝ) (r : ℝ), (∀ i, ContactMotionsHyp (Hs i)) ∧ 0 < r ∧
      ParameterAvoidanceHyp 1 n 2 Kper1 0 r (cuspMap L n Hs) := by
  sorry

/-- LEAF P1.2.  A parameter avoiding the bad set gives `NoDoubleZero` (periodicity reduces every
`θ` to `[0,2π]`). -/
theorem noDoubleZero_of_notMem (L : ℝ → ℝ³) (hL : GenericFrontHyp L) (n : ℕ)
    (Hs : Fin n → ℝ³ → ℝ) (hHs : ∀ i, ContactMotionsHyp (Hs i)) {r : ℝ} {a : ℝ^n}
    (ha : a ∉ ParameterAvoidance.zeroParams Kper1 (Metric.closedBall 0 r) (cuspMap L n Hs))
    (har : a ∈ Metric.closedBall (0 : ℝ^n) r) : NoDoubleZero (composeFlows n Hs (par a) ∘ L) := by
  sorry

/-- LEAF P1.3.  Simple zeros of `x′` on the circle are finitely many (sm-3:2657). -/
theorem finite_cusps_of_stage1 {L : ℝ → ℝ³} (h : Stage1 L) : (cuspSet L ∩ Ico 0 (2 * π)).Finite := by
  sorry

/-- LEAF P1.4.  At a cusp `y′ ≠ 0` (immersion + `z′ = y x′`, sm-3:2640, 2658). -/
theorem deriv_y_ne_zero_at_cusp {L : ℝ → ℝ³} (h : Stage1 L) {θ : ℝ} (hθ : θ ∈ cuspSet L) :
    deriv (coordY L) θ ≠ 0 := by
  sorry

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

/-- Derivative of a curve into `ℝ³` from its coordinates. -/
lemma gp5_hasDerivAt_toLp {g : ℝ → Fin 3 → ℝ} {g' : Fin 3 → ℝ} {s : ℝ}
    (h : ∀ i, HasDerivAt (fun s => g s i) (g' i) s) :
    HasDerivAt (fun s => (WithLp.toLp 2 (g s) : ℝ³)) (WithLp.toLp 2 g') s := by
  have h1 : HasDerivAt g g' s := hasDerivAt_pi.2 h
  have h2 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt
    s h1
  exact h2

open ContactMotions in
/-- The partial derivatives of `H = ψ ∘ y`. -/
lemma gp5_hasFDerivAt_y_only (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (p : ℝ³) :
    HasFDerivAt (fun p : ℝ³ => ψ (p 1)) (deriv ψ (p 1) • coordCLM 1) p := by
  have h := ((hψ.differentiable (by simp)) (p 1)).hasDerivAt.comp_hasFDerivAt p
    (hasFDerivAt_coord 1 p)
  exact h

open ContactMotions in
lemma gp5_pd_y_only (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (p : ℝ³) (i : Fin 3) :
    pd (fun p : ℝ³ => ψ (p 1)) i p = deriv ψ (p 1) * (e i 1) := by
  simp only [pd, (gp5_hasFDerivAt_y_only ψ hψ p).fderiv]
  simp

open ContactMotions in
/-- `X_{ψ(y)} = (−ψ′(y), 0, ψ(y) − yψ′(y))`. -/
lemma gp5_hamVF_y_only (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (q : ℝ³) :
    hamVF (fun p : ℝ³ => ψ (p 1)) q = !₂[-(deriv ψ (q 1)), 0, ψ (q 1) - q 1 * deriv ψ (q 1)] := by
  ext i
  fin_cases i <;> simp [hamVF, gp5_pd_y_only ψ hψ]

open ContactMotions in
/-- The explicit map is a global flow of `X_{ψ(y)}`. -/
lemma gp5_isGlobalFlow_cuspFlowMap (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    IsGlobalFlow (hamVF (fun p : ℝ³ => ψ (p 1))) (cuspFlowMap ψ) where
  zero p := by
    ext i; fin_cases i <;> simp [cuspFlowMap]
  hasDerivAt s p := by
    rw [gp5_hamVF_y_only ψ hψ]
    have hy : cuspFlowMap ψ s p 1 = p 1 := by simp [cuspFlowMap]
    rw [hy]
    unfold cuspFlowMap
    apply gp5_hasDerivAt_toLp
    intro i
    fin_cases i
    · simpa using ((hasDerivAt_id s).mul_const (deriv ψ (p 1))).const_sub (p 0)
    · simpa using hasDerivAt_const s (p 1)
    · simpa using ((hasDerivAt_id s).mul_const (ψ (p 1) - p 1 * deriv ψ (p 1))).const_add (p 2)

open ContactMotions in
/-- `X_{ψ(y)}` is globally Lipschitz (it depends on `y` only, through a compactly supported `C¹`
function of one variable). -/
lemma gp5_exists_lipschitz_hamVF_y_only (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) : ∃ K : NNReal, LipschitzWith K (hamVF (fun p : ℝ³ => ψ (p 1))) := by
  set F : ℝ → ℝ³ := fun y => !₂[-(deriv ψ y), 0, ψ y - y * deriv ψ y] with hF
  have hψ' : ContDiff ℝ ∞ (deriv ψ) := hψ.iterate_deriv 1
  have hFs : ContDiff ℝ 1 F := by
    have : ContDiff ℝ ∞ F := by
      rw [hF, contDiff_euclidean]
      intro i
      fin_cases i
      · simpa using hψ'.neg
      · simpa using contDiff_const
      · simpa using hψ.sub (contDiff_id.mul hψ')
    exact this.of_le (by simp)
  have hFc : HasCompactSupport F := by
    have hc' : HasCompactSupport (deriv ψ) := hc.deriv
    refine HasCompactSupport.intro (hc.union hc') fun y hy => ?_
    rw [Set.mem_union, not_or] at hy
    have h0 : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy.1
    have h1 : deriv ψ y = 0 := image_eq_zero_of_notMem_tsupport hy.2
    ext i; fin_cases i <;> simp [hF, h0, h1]
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_hasCompactSupport' hFc hFs
  refine ⟨K * ‖coordCLM 1‖₊, ?_⟩
  have heq : hamVF (fun p : ℝ³ => ψ (p 1)) = F ∘ (coordCLM 1) := by
    funext q; simp [hF, gp5_hamVF_y_only ψ hψ]
  rw [heq]
  exact hK.comp (coordCLM 1).lipschitzWith

/-- LEAF P5.1.  For `H(x,y,z) = ψ(y)` smooth compactly supported, `hamFlow H = cuspFlowMap ψ`
(`X_H = (−ψ′, 0, ψ − yψ′)`; the explicit map is a global flow; `hamFlow_unique`). -/
theorem hamFlow_of_y_only (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    hamFlow (fun p => ψ (p 1)) = cuspFlowMap ψ := by
  obtain ⟨K, hK⟩ := gp5_exists_lipschitz_hamVF_y_only ψ hψ hc
  have hflow := gp5_isGlobalFlow_cuspFlowMap ψ hψ
  have hgf : ContactMotions.IsGlobalFlow (hamVF (fun p : ℝ³ => ψ (p 1)))
      (ContactMotions.globalFlow (hamVF (fun p : ℝ³ => ψ (p 1)))) :=
    Classical.epsilon_spec (p := ContactMotions.IsGlobalFlow (hamVF (fun p : ℝ³ => ψ (p 1))))
      ⟨cuspFlowMap ψ, hflow⟩
  exact (hgf.unique hK hflow).symm

/-- LEAF P5.2.  Near a cusp `y` is a local parameter and `x = f(y)` with `f′(y₀) = 0`,
`f″(y₀) = x″(θ_c)/y′(θ_c)² ≠ 0` (1-D inverse function theorem; sm-3:2732-2734). -/
theorem exists_local_graph {L : ℝ → ℝ³} (h : Stage3 L) {θc : ℝ} (hθc : θc ∈ cuspSet L) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ deriv f (coordY L θc) = 0 ∧ deriv (deriv f) (coordY L θc) ≠ 0 ∧
      ∀ᶠ θ in 𝓝 θc, coordX L θ = f (coordY L θ) := by
  -- notation
  have hL : ContDiff ℝ ∞ L := h.circle.smooth
  have hy : ContDiff ℝ ∞ (coordY L) := (ContactMotions.contDiff_coord 1).comp hL
  have hx : ContDiff ℝ ∞ (coordX L) := (ContactMotions.contDiff_coord 0).comp hL
  have hy' : deriv (coordY L) θc ≠ 0 := deriv_y_ne_zero_at_cusp h.toStage1 hθc
  have hyd : ∀ θ, HasDerivAt (coordY L) (deriv (coordY L) θ) θ := fun θ =>
    (hy.differentiable (by simp) θ).hasDerivAt
  -- the 1-D inverse function theorem: `y` is a local diffeomorphism near `θc`
  have hys : HasStrictDerivAt (coordY L) (deriv (coordY L) θc) θc :=
    hy.contDiffAt.hasStrictDerivAt (by simp)
  set P : OpenPartialHomeomorph ℝ ℝ :=
    (hys.hasStrictFDerivAt_equiv hy').toOpenPartialHomeomorph (coordY L) with hP
  have hPcoe : (P : ℝ → ℝ) = coordY L := rfl
  have hθcP : θc ∈ P.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  have hopen : IsOpen {θ | deriv (coordY L) θ ≠ 0} :=
    isOpen_ne_fun (hy.continuous_deriv (by simp)) continuous_const
  set Q := P.restrOpen {θ | deriv (coordY L) θ ≠ 0} hopen with hQ
  have hQcoe : (Q : ℝ → ℝ) = coordY L := rfl
  have hθcQ : θc ∈ Q.source := by
    rw [hQ, OpenPartialHomeomorph.restrOpen_source]; exact ⟨hθcP, hy'⟩
  have hy₀Q : coordY L θc ∈ Q.target := Q.map_source hθcQ
  -- the inverse is smooth on the (open) target, since `y′ ≠ 0` on the source
  have hsymm : ContDiffOn ℝ ∞ Q.symm Q.target := by
    intro a ha
    have hsrc : Q.symm a ∈ Q.source := Q.map_target ha
    rw [hQ, OpenPartialHomeomorph.restrOpen_source] at hsrc
    have hne : deriv (coordY L) (Q.symm a) ≠ 0 := hsrc.2
    exact (Q.contDiffAt_symm_deriv hne ha (hyd _) hy.contDiffAt).contDiffWithinAt
  -- extend `x ∘ Q.symm` from the target to a global smooth function by a bump
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 Q.open_target _ hy₀Q
  set b : ContDiffBump (coordY L θc) := ⟨r / 4, r / 2, by linarith, by linarith⟩ with hb
  set f : ℝ → ℝ := fun v => b v * coordX L (Q.symm v) with hfdef
  have hf : ContDiff ℝ ∞ f := by
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : v ∈ Q.target
    · have h1 : ContDiffAt ℝ ∞ (fun v => coordX L (Q.symm v)) v :=
        hx.contDiffAt.comp v (hsymm.contDiffAt (Q.open_target.mem_nhds hv))
      exact b.contDiffAt.mul h1
    · have hv' : v ∉ Metric.closedBall (coordY L θc) (r / 2) := fun hv' =>
        hv (hball (Metric.closedBall_subset_ball (by linarith) hv'))
      have hnhds : (Metric.closedBall (coordY L θc) (r / 2))ᶜ ∈ 𝓝 v :=
        Metric.isClosed_closedBall.isOpen_compl.mem_nhds hv'
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with w hw
      have hw' : b.rOut ≤ dist w (coordY L θc) := by
        simp only [Metric.mem_closedBall, mem_compl_iff, not_le] at hw
        exact hw.le
      simp only [hfdef, b.zero_of_le_dist hw', zero_mul]
  -- the graph property near `θc`
  have hgraph : ∀ᶠ θ in 𝓝 θc, coordX L θ = f (coordY L θ) := by
    have h1 : ∀ᶠ θ in 𝓝 θc, θ ∈ Q.source := Q.open_source.mem_nhds hθcQ
    have h2 : ∀ᶠ θ in 𝓝 θc, coordY L θ ∈ Metric.ball (coordY L θc) (r / 4) :=
      hy.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by linarith))
    filter_upwards [h1, h2] with θ hθ hθ'
    have hone : b (coordY L θ) = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hθ')
    have hinv : Q.symm (coordY L θ) = θ := Q.left_inv hθ
    simp only [hfdef, hone, one_mul, hinv]
  -- derivatives of `f` at `y₀` from the chain rule `x′ = f′(y) y′`
  have hf1 : ∀ v, HasDerivAt f (deriv f v) v := fun v => (hf.differentiable (by simp) v).hasDerivAt
  have hf' : ContDiff ℝ ∞ (deriv f) := hf.iterate_deriv 1
  have hf2 : ∀ v, HasDerivAt (deriv f) (deriv (deriv f) v) v := fun v =>
    (hf'.differentiable (by simp) v).hasDerivAt
  have hy'' : ContDiff ℝ ∞ (deriv (coordY L)) := hy.iterate_deriv 1
  have hyd2 : HasDerivAt (deriv (coordY L)) (deriv (deriv (coordY L)) θc) θc :=
    (hy''.differentiable (by simp) θc).hasDerivAt
  obtain ⟨U, hU, hUo, hθcU⟩ := eventually_nhds_iff.1 hgraph
  have hxd : ∀ θ ∈ U, HasDerivAt (coordX L) (deriv f (coordY L θ) * deriv (coordY L) θ) θ :=
    fun θ hθ => ((hf1 (coordY L θ)).comp θ (hyd θ)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hUo.mem_nhds hθ) fun θ' hθ' => hU θ' hθ')
  have hx'eq : deriv (coordX L) =ᶠ[𝓝 θc] fun θ => deriv f (coordY L θ) * deriv (coordY L) θ :=
    Filter.eventually_of_mem (hUo.mem_nhds hθcU) fun θ hθ => (hxd θ hθ).deriv
  have hx'c : deriv (coordX L) θc = deriv f (coordY L θc) * deriv (coordY L) θc := (hxd θc hθcU).deriv
  have hx'0 : deriv (coordX L) θc = 0 := hθc
  have hfy0 : deriv f (coordY L θc) = 0 := by
    rw [hx'0] at hx'c
    rcases mul_eq_zero.1 hx'c.symm with h1 | h1
    · exact h1
    · exact absurd h1 hy'
  have hx''c : deriv (deriv (coordX L)) θc =
      deriv (deriv f) (coordY L θc) * deriv (coordY L) θc * deriv (coordY L) θc := by
    rw [hx'eq.deriv_eq]
    have hd : HasDerivAt (fun θ => deriv f (coordY L θ) * deriv (coordY L) θ)
        (deriv (deriv f) (coordY L θc) * deriv (coordY L) θc * deriv (coordY L) θc +
          deriv f (coordY L θc) * deriv (deriv (coordY L)) θc) θc :=
      ((hf2 (coordY L θc)).comp θc (hyd θc)).mul hyd2
    rw [hd.deriv, hfy0]; ring
  have hx''ne : deriv (deriv (coordX L)) θc ≠ 0 := by
    rcases h.noDoubleZero θc with h1 | h1
    · exact absurd hx'0 h1
    · exact h1
  refine ⟨f, hf, hfy0, fun hcontra => hx''ne ?_, hgraph⟩
  rw [hx''c, hcontra, zero_mul, zero_mul]

/-- LEAF P5.3.  The exact germ after the time-one map (sm-3:2741-2747): if near `θc` the new curve
is `cuspFlowMap ψ 1 ∘ L` with `ψ = cuspHam f y₀ A`, `A = f″(y₀)/2`, then `x = x₀ + Au²`,
`z = z₀ + Ay₀u² + ⅔Au³` (`z` by Legendrianity: `dz/dy = y·2Au`). -/
theorem exactGerm_of_cuspFlow {L L' : ℝ → ℝ³} (h : Stage3 L) {θc : ℝ} (hθc : θc ∈ cuspSet L)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hf' : deriv f (coordY L θc) = 0)
    (hf'' : deriv (deriv f) (coordY L θc) ≠ 0) (hgraph : ∀ᶠ θ in 𝓝 θc, coordX L θ = f (coordY L θ))
    (hL' : ∀ᶠ θ in 𝓝 θc,
      L' θ = cuspFlowMap (cuspHam f (coordY L θc) (deriv (deriv f) (coordY L θc) / 2)) 1 (L θ)) :
    IsExactCuspGerm L' θc := by
  clear hf'
  -- notation and basic facts
  set y₀ := coordY L θc with hy₀
  set A := deriv (deriv f) (coordY L θc) / 2 with hA
  set ψ := cuspHam f y₀ A with hψ
  have hA0 : A ≠ 0 := div_ne_zero hf'' two_ne_zero
  have hL : ContDiff ℝ ∞ L := h.circle.smooth
  have hLd : ∀ θ, HasDerivAt L (deriv L θ) θ := fun θ => (hL.differentiable (by simp) θ).hasDerivAt
  have hy : ContDiff ℝ ∞ (coordY L) := (ContactMotions.contDiff_coord 1).comp hL
  have hyd : ∀ θ, HasDerivAt (coordY L) (deriv (coordY L) θ) θ := fun θ =>
    (hy.differentiable (by simp) θ).hasDerivAt
  have hyd' : ∀ θ, HasDerivAt (coordY L) (deriv L θ 1) θ := fun θ =>
    ContactMotions.hasDerivAt_coord (hLd θ) 1
  have hzd : ∀ θ, HasDerivAt (coordZ L) (deriv L θ 2) θ := fun θ =>
    ContactMotions.hasDerivAt_coord (hLd θ) 2
  have hxd0 : ∀ θ, HasDerivAt (coordX L) (deriv L θ 0) θ := fun θ =>
    ContactMotions.hasDerivAt_coord (hLd θ) 0
  have hy' : deriv (coordY L) θc ≠ 0 := deriv_y_ne_zero_at_cusp h.toStage1 hθc
  have hf1 : ∀ v, HasDerivAt f (deriv f v) v := fun v => (hf.differentiable (by simp) v).hasDerivAt
  -- `ψ′ = g := f − q` (FTC) and `ψ″ = f′ − 2A(v − y₀)`
  set g : ℝ → ℝ := fun v => f v - (f y₀ + A * (v - y₀) ^ 2) with hg
  have hgc : Continuous g := by
    rw [hg]
    exact hf.continuous.sub (continuous_const.add (continuous_const.mul
      ((continuous_id.sub continuous_const).pow 2)))
  have hψd : ∀ v, HasDerivAt ψ (g v) v := fun v =>
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt
  have hψ' : deriv ψ = g := funext fun v => (hψd v).deriv
  have hgd : ∀ v, HasDerivAt g (deriv f v - 2 * A * (v - y₀)) v := by
    intro v
    have h1 : HasDerivAt (fun v => f y₀ + A * (v - y₀) ^ 2) (A * (2 * (v - y₀))) v := by
      have := (((hasDerivAt_id v).sub_const y₀).pow 2).const_mul A
      refine (this.const_add (f y₀)).congr_deriv ?_
      simp
    refine ((hf1 v).sub h1).congr_deriv ?_
    ring
  have hψ0 : ψ y₀ = 0 := by simp [hψ, cuspHam]
  have hg0 : g y₀ = 0 := by simp [hg]
  -- the neighbourhood where both hypotheses hold
  obtain ⟨U, hU, hUo, hθcU⟩ := eventually_nhds_iff.1 (hgraph.and hL')
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo θc hθcU
  have hmem : ∀ θ, |θ - θc| < ε → θ ∈ U := fun θ hθ => hball (by
    rw [Metric.mem_ball, Real.dist_eq]; exact hθ)
  have hθcε : |θc - θc| < ε := by simp [hε]
  -- coordinates of `L'` on the ball
  have hL'x : ∀ θ ∈ U, coordX L' θ = f y₀ + A * (coordY L θ - y₀) ^ 2 := by
    intro θ hθ
    have h1 := (hU θ hθ).1
    have h2 := (hU θ hθ).2
    simp only [coordX, h2, cuspFlowMap, hψ']
    change L θ 0 - 1 * g (L θ 1) = f y₀ + A * (L θ 1 - y₀) ^ 2
    change L θ 0 = f (L θ 1) at h1
    simp only [hg, h1]; ring
  have hL'y : ∀ θ ∈ U, coordY L' θ = coordY L θ := by
    intro θ hθ
    simp only [coordY, (hU θ hθ).2, cuspFlowMap]
    rfl
  have hL'z : ∀ θ ∈ U, coordZ L' θ = coordZ L θ + (ψ (coordY L θ) - coordY L θ * g (coordY L θ)) := by
    intro θ hθ
    simp only [coordZ, (hU θ hθ).2, cuspFlowMap, hψ']
    change L θ 2 + 1 * (ψ (L θ 1) - L θ 1 * g (L θ 1)) = L θ 2 + (ψ (L θ 1) - L θ 1 * g (L θ 1))
    ring
  -- `x′ = f′(y) y′` on the ball
  have hxd : ∀ θ ∈ U, HasDerivAt (coordX L) (deriv f (coordY L θ) * deriv (coordY L) θ) θ :=
    fun θ hθ => ((hf1 (coordY L θ)).comp θ (hyd θ)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hUo.mem_nhds hθ) fun θ' hθ' => (hU θ' hθ').1)
  -- the `z`-identity by constancy of `G` on the ball
  set G : ℝ → ℝ := fun θ => coordZ L θ + (ψ (coordY L θ) - coordY L θ * g (coordY L θ)) -
    (A * y₀ * (coordY L θ - y₀) ^ 2 + 2 / 3 * A * (coordY L θ - y₀) ^ 3) with hG
  have hGd : ∀ θ ∈ Metric.ball θc ε, HasDerivAt G 0 θ := by
    intro θ hθ
    have hθU : θ ∈ U := hball hθ
    have h1 : HasDerivAt (fun θ => ψ (coordY L θ)) (g (coordY L θ) * deriv (coordY L) θ) θ :=
      (hψd (coordY L θ)).comp θ (hyd θ)
    have h2 : HasDerivAt (fun θ => coordY L θ * g (coordY L θ))
        (deriv (coordY L) θ * g (coordY L θ) +
          coordY L θ * ((deriv f (coordY L θ) - 2 * A * (coordY L θ - y₀)) * deriv (coordY L) θ)) θ :=
      (hyd θ).mul ((hgd (coordY L θ)).comp θ (hyd θ))
    have h3 : HasDerivAt (fun θ => A * y₀ * (coordY L θ - y₀) ^ 2 + 2 / 3 * A * (coordY L θ - y₀) ^ 3)
        (A * y₀ * (↑2 * (coordY L θ - y₀) ^ (2 - 1) * deriv (coordY L) θ) +
          2 / 3 * A * (↑3 * (coordY L θ - y₀) ^ (3 - 1) * deriv (coordY L) θ)) θ :=
      ((((hyd θ).sub_const y₀).pow 2).const_mul (A * y₀)).add
        ((((hyd θ).sub_const y₀).pow 3).const_mul (2 / 3 * A))
    have hd := ((hzd θ).add (h1.sub h2)).sub h3
    refine hd.congr_deriv ?_
    -- Legendrian: `z′ = y x′`, and `x′ = f′(y) y′`
    have hleg : deriv L θ 2 = L θ 1 * deriv L θ 0 := by
      have := h.legendrian θ
      simp only [alpha] at this
      linarith
    have hx1 : deriv L θ 0 = deriv f (coordY L θ) * deriv (coordY L) θ := by
      rw [← (hxd0 θ).deriv]; exact (hxd θ hθU).deriv
    have hyL : coordY L θ = L θ 1 := rfl
    rw [hleg, hx1]
    simp only [hyL]
    ring
  have hGconst : ∀ θ ∈ Metric.ball θc ε, G θ = G θc :=
    fun θ hθ => Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball θc ε).isPreconnected
      (fun θ hθ => (hGd θ hθ).differentiableAt.differentiableWithinAt)
      (fun θ hθ => (hGd θ hθ).deriv) hθ (Metric.mem_ball_self hε)
  -- assemble
  refine ⟨A, hA0, ?_, ε, hε, fun θ hθ => ?_⟩
  · have heq : coordY L' =ᶠ[𝓝 θc] coordY L :=
      Filter.eventually_of_mem (hUo.mem_nhds hθcU) fun θ hθ => hL'y θ hθ
    rw [heq.deriv_eq]; exact hy'
  · have hθU : θ ∈ U := hmem θ hθ
    have hθball : θ ∈ Metric.ball θc ε := by rw [Metric.mem_ball, Real.dist_eq]; exact hθ
    have hcU : θc ∈ U := hθcU
    rw [hL'y θ hθU, hL'y θc hcU, hL'x θ hθU, hL'x θc hcU, hL'z θ hθU, hL'z θc hcU]
    refine ⟨by simp [y₀], ?_⟩
    have hGθ := hGconst θ hθball
    simp only [hG] at hGθ
    rw [← hy₀] at hGθ ⊢
    linarith

/-- The unit bump on `ℝ³`: `1` on the closed unit ball, supported in the ball of radius `2`. -/
def gp5_bump1 : ContDiffBump (0 : ℝ³) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The bump of radius `ε` about `pc`: `b₁((2/ε)(p − pc))`, equal to `1` on `closedBall pc (ε/2)`
and to `0` off `ball pc ε`. -/
def gp5_bump (pc : ℝ³) (ε : ℝ) (p : ℝ³) : ℝ := gp5_bump1 ((2 / ε) • (p - pc))

lemma gp5_bump_contDiff (pc : ℝ³) (ε : ℝ) : ContDiff ℝ ∞ (gp5_bump pc ε) := by
  have h : ContDiff ℝ ∞ (fun p : ℝ³ => (2 / ε) • (p - pc)) :=
    (contDiff_id.sub contDiff_const).const_smul (2 / ε)
  exact (gp5_bump1.contDiff (n := ⊤)).comp h

lemma gp5_bump_one {pc : ℝ³} {ε : ℝ} (hε : 0 < ε) {p : ℝ³} (hp : dist p pc ≤ ε / 2) :
    gp5_bump pc ε p = 1 := by
  apply gp5_bump1.one_of_mem_closedBall
  rw [show gp5_bump1.rIn = 1 from rfl, mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 / ε), ← dist_eq_norm, div_mul_eq_mul_div,
    div_le_one hε]
  linarith

lemma gp5_bump_zero {pc : ℝ³} {ε : ℝ} (hε : 0 < ε) {p : ℝ³} (hp : ε ≤ dist p pc) :
    gp5_bump pc ε p = 0 := by
  apply gp5_bump1.zero_of_le_dist
  rw [show gp5_bump1.rOut = 2 from rfl, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 / ε), ← dist_eq_norm, div_mul_eq_mul_div,
    le_div_iff₀ hε]
  linarith

lemma gp5_bump_support {pc : ℝ³} {ε : ℝ} (hε : 0 < ε) :
    support (gp5_bump pc ε) ⊆ Metric.closedBall pc ε := by
  intro p hp
  rw [Function.mem_support] at hp
  rw [Metric.mem_closedBall]
  by_contra h
  exact hp (gp5_bump_zero hε (not_le.1 h).le)

lemma gp5_bump_tsupport {pc : ℝ³} {ε : ℝ} (hε : 0 < ε) :
    tsupport (gp5_bump pc ε) ⊆ Metric.closedBall pc ε :=
  closure_minimal (gp5_bump_support hε) Metric.isClosed_closedBall

lemma gp5_bump_hasCompactSupport {pc : ℝ³} {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (gp5_bump pc ε) :=
  HasCompactSupport.intro (isCompact_closedBall pc ε) fun p hp =>
    gp5_bump_zero hε (by rw [Metric.mem_closedBall] at hp; exact (not_le.1 hp).le)

/-- Derivative bounds for the scaled bump: `‖D^n b_ε‖ ≤ C_n (2/ε)^n`. -/
lemma gp5_bump_bound (pc : ℝ³) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ p,
      ‖iteratedFDeriv ℝ n (gp5_bump pc ε) p‖ ≤ C * (2 / ε) ^ n := by
  obtain ⟨C, hC⟩ := ContactMotions.exists_bound_of_hasCompactSupport'
    (gp5_bump1.hasCompactSupport.iteratedFDeriv n)
    ((gp5_bump1.contDiff (n := ⊤)).continuous_iteratedFDeriv (by simp))
  refine ⟨C, C.coe_nonneg, fun ε hε p => ?_⟩
  set L : ℝ³ →L[ℝ] ℝ³ := (2 / ε) • ContinuousLinearMap.id ℝ ℝ³ with hL
  have hLn : ‖L‖ ≤ 2 / ε := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    rw [hL, smul_apply, ContinuousLinearMap.id_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have heq : gp5_bump pc ε = fun z => (gp5_bump1 ∘ L) (-pc + z) := by
    funext z; simp [gp5_bump, hL, neg_add_eq_sub]
  rw [heq, iteratedFDeriv_comp_add_left,
    L.iteratedFDeriv_comp_right (gp5_bump1.contDiff (n := ⊤)) _ (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul (hC _) (pow_le_pow_left₀ (norm_nonneg _) hLn n) (by positivity) C.coe_nonneg

/-- One step of the mean value theorem: if `φ′ = φ₁`, `φ y₀ = 0` and `|φ₁| ≤ M |· − y₀|^m` on
`Icc (y₀ − 1) (y₀ + 1)`, then `|φ| ≤ M |· − y₀|^(m+1)` there. -/
lemma gp5_mvt_step {φ φ₁ : ℝ → ℝ} {y₀ M : ℝ} {m : ℕ} (hM : 0 ≤ M)
    (hd : ∀ x, HasDerivAt φ (φ₁ x) x) (h0 : φ y₀ = 0)
    (hb : ∀ x ∈ Icc (y₀ - 1) (y₀ + 1), |φ₁ x| ≤ M * |x - y₀| ^ m) :
    ∀ y ∈ Icc (y₀ - 1) (y₀ + 1), |φ y| ≤ M * |y - y₀| ^ (m + 1) := by
  intro y hy
  have hseg : uIcc y₀ y ⊆ Icc (y₀ - 1) (y₀ + 1) :=
    uIcc_subset_Icc ⟨by linarith, by linarith⟩ hy
  have hbound : ∀ x ∈ uIcc y₀ y, ‖deriv φ x‖ ≤ M * |y - y₀| ^ m := by
    intro x hx
    rw [(hd x).deriv, Real.norm_eq_abs]
    refine (hb x (hseg hx)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (Set.abs_sub_left_of_mem_uIcc hx) m) hM
  have := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => (hd x).differentiableAt) hbound
    (convex_uIcc y₀ y) left_mem_uIcc right_mem_uIcc
  rw [h0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at this
  rw [pow_succ, ← mul_assoc]
  exact this

/-- The cutoff bound: for `χ` smooth vanishing to order `3` at `y₀`, all derivatives of order
`≤ 3` of `χ(y)·b_ε(p)` are `O(ε)` uniformly. -/
lemma gp5_cutoff_bound (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (y₀ : ℝ) (h0 : χ y₀ = 0)
    (h1 : deriv χ y₀ = 0) (h2 : deriv^[2] χ y₀ = 0) (h3 : deriv^[3] χ y₀ = 0) (pc : ℝ³)
    (hpc : pc 1 = y₀) :
    ∃ K, 0 ≤ K ∧ ∀ ε, 0 < ε → ε ≤ 1 → ∀ n ≤ 3, ∀ p,
      ‖iteratedFDeriv ℝ n (fun p => χ (p 1) * gp5_bump pc ε p) p‖ ≤ K * ε := by
  -- Taylor bounds on `Icc (y₀ − 1) (y₀ + 1)`
  have hχj : ∀ j, ContDiff ℝ ∞ (deriv^[j] χ) := fun j => hχ.iterate_deriv j
  have hdj : ∀ j x, HasDerivAt (deriv^[j] χ) (deriv^[j + 1] χ x) x := fun j x => by
    have h := ((hχj j).differentiable (by simp) x).hasDerivAt
    rw [Function.iterate_succ_apply']; exact h
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := y₀ - 1) (b := y₀ + 1)).exists_bound_of_continuousOn
    (hχj 4).continuous.continuousOn
  set M := max M₀ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hT4 : ∀ x ∈ Icc (y₀ - 1) (y₀ + 1), |deriv^[4] χ x| ≤ M * |x - y₀| ^ 0 := fun x hx => by
    rw [pow_zero, mul_one]
    exact ((hM₀ x hx).trans (le_max_left _ _))
  have hT3 := gp5_mvt_step hM (hdj 3) h3 hT4
  have hT2 := gp5_mvt_step hM (hdj 2) h2 hT3
  have hT1 := gp5_mvt_step hM (hdj 1) h1 hT2
  have hT0 := gp5_mvt_step hM (hdj 0) h0 hT1
  have hT : ∀ j ≤ 3, ∀ y ∈ Icc (y₀ - 1) (y₀ + 1), |deriv^[j] χ y| ≤ M * |y - y₀| ^ (4 - j) := by
    intro j hj y hy
    interval_cases j
    · exact hT0 y hy
    · exact hT1 y hy
    · exact hT2 y hy
    · exact hT3 y hy
  -- bump constants
  choose C hC using gp5_bump_bound pc
  set Cb := C 0 + C 1 + C 2 + C 3 with hCb
  have hCb0 : 0 ≤ Cb := by
    have := (hC 0).1; have := (hC 1).1; have := (hC 2).1; have := (hC 3).1; linarith
  have hCle : ∀ j ≤ 3, C j ≤ Cb := by
    intro j hj
    have := (hC 0).1; have := (hC 1).1; have := (hC 2).1; have := (hC 3).1
    interval_cases j <;> linarith
  refine ⟨64 * M * Cb, by positivity, fun ε hε hε1 n hn p => ?_⟩
  set bε := gp5_bump pc ε with hbε
  have hf : ContDiff ℝ ∞ (fun p : ℝ³ => χ (p 1)) := hχ.comp (ContactMotions.contDiff_coord 1)
  have hg : ContDiff ℝ ∞ bε := gp5_bump_contDiff pc ε
  by_cases hp : dist p pc ≤ ε
  · -- on the support: Leibniz
    have hyp : |p 1 - y₀| ≤ ε := by
      have h := PiLp.norm_apply_le (p - pc) 1
      rw [PiLp.sub_apply, Real.norm_eq_abs, ← dist_eq_norm, hpc] at h
      exact h.trans hp
    have hpI : p 1 ∈ Icc (y₀ - 1) (y₀ + 1) := by
      rw [abs_le] at hyp; constructor <;> linarith
    -- derivatives of `χ ∘ π₁`
    have hfi : ∀ i ≤ 3, ‖iteratedFDeriv ℝ i (fun p : ℝ³ => χ (p 1)) p‖ ≤ M * ε ^ (4 - i) := by
      intro i hi
      have hcomp : (fun p : ℝ³ => χ (p 1)) = χ ∘ ContactMotions.coordCLM 1 := rfl
      rw [hcomp, (ContactMotions.coordCLM 1).iteratedFDeriv_comp_right hχ p (by simp)]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      have hπ : ‖ContactMotions.coordCLM 1‖ ≤ 1 :=
        ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by
          rw [one_mul]; exact PiLp.norm_apply_le q 1
      have hprod : ∏ _x : Fin i, ‖ContactMotions.coordCLM 1‖ ≤ 1 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) hπ
      have hval : ‖iteratedFDeriv ℝ i χ (ContactMotions.coordCLM 1 p)‖ ≤ M * ε ^ (4 - i) := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.norm_eq_abs,
          ContactMotions.coordCLM_apply]
        refine (hT i hi (p 1) hpI).trans ?_
        gcongr
      calc ‖iteratedFDeriv ℝ i χ (ContactMotions.coordCLM 1 p)‖ * ∏ _x : Fin i, ‖ContactMotions.coordCLM 1‖
          ≤ (M * ε ^ (4 - i)) * 1 := mul_le_mul hval hprod (by positivity) (by positivity)
        _ = M * ε ^ (4 - i) := mul_one _
    have hgi : ∀ i ≤ 3, ‖iteratedFDeriv ℝ i bε p‖ ≤ Cb * (2 / ε) ^ i := fun i hi =>
      ((hC i).2 ε hε p).trans (mul_le_mul_of_nonneg_right (hCle i hi) (by positivity))
    -- the term bound
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun p : ℝ³ => χ (p 1)) p‖ *
          ‖iteratedFDeriv ℝ (n - i) bε p‖ ≤ (n.choose i : ℝ) * (8 * M * Cb * ε) := by
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ‖iteratedFDeriv ℝ i (fun p : ℝ³ => χ (p 1)) p‖ * ‖iteratedFDeriv ℝ (n - i) bε p‖
          ≤ (M * ε ^ (4 - i)) * (Cb * (2 / ε) ^ (n - i)) :=
            mul_le_mul (hfi i (by omega)) (hgi (n - i) (by omega)) (norm_nonneg _) (by positivity)
        _ ≤ 8 * M * Cb * ε := by
            have h4 : 4 - i = (4 - n) + (n - i) := by omega
            have h2 : ε ^ (n - i) * (2 / ε) ^ (n - i) = 2 ^ (n - i) := by
              rw [← mul_pow]; congr 1; field_simp
            have h8 : (2 : ℝ) ^ (n - i) ≤ 8 := by
              calc (2 : ℝ) ^ (n - i) ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
                _ = 8 := by norm_num
            have hεn : ε ^ (4 - n) ≤ ε := pow_le_of_le_one hε.le hε1 (by omega)
            calc M * ε ^ (4 - i) * (Cb * (2 / ε) ^ (n - i))
                = M * Cb * ε ^ (4 - n) * (ε ^ (n - i) * (2 / ε) ^ (n - i)) := by
                  rw [h4, pow_add]; ring
              _ = M * Cb * ε ^ (4 - n) * 2 ^ (n - i) := by rw [h2]
              _ ≤ M * Cb * ε * 8 := by gcongr
              _ = 8 * M * Cb * ε := by ring
    calc ‖iteratedFDeriv ℝ n (fun p => χ (p 1) * bε p) p‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun p : ℝ³ => χ (p 1)) p‖ * ‖iteratedFDeriv ℝ (n - i) bε p‖ :=
          norm_iteratedFDeriv_mul_le hf hg p (by simp)
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (8 * M * Cb * ε) := Finset.sum_le_sum hterm
      _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * (8 * M * Cb * ε) := by
          rw [Finset.sum_mul]
      _ = (2 : ℝ) ^ n * (8 * M * Cb * ε) := by
          rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
      _ ≤ 8 * (8 * M * Cb * ε) := by
          gcongr
          calc (2 : ℝ) ^ n ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hn
            _ = 8 := by norm_num
      _ = 64 * M * Cb * ε := by ring
  · -- off the support: the derivative vanishes
    have hsupp : tsupport (fun p => χ (p 1) * bε p) ⊆ Metric.closedBall pc ε :=
      tsupport_mul_subset_right.trans (gp5_bump_tsupport hε)
    have hnot : p ∉ tsupport (fun p => χ (p 1) * bε p) := fun h => hp (hsupp h)
    have hzero : iteratedFDeriv ℝ n (fun p => χ (p 1) * bε p) p = 0 :=
      Function.notMem_support.1 fun h => hnot (support_iteratedFDeriv_subset n h)
    rw [hzero, norm_zero]
    positivity

open ContactMotions in
/-- `X_H` through `H` and `yH := y·H`:
`X_H = (−∂₁H) e₀ + (∂₀H + ∂₂(yH)) e₁ + (2H − ∂₁(yH)) e₂`. -/
lemma gp5_hamVF_eq (H : ℝ³ → ℝ) (hH : ContDiff ℝ ∞ H) :
    hamVF H = (fun p => (-(pd H 1 p)) • e 0) + (fun p => (pd H 0 p + pd (fun q => q 1 * H q) 2 p) • e 1) +
      (fun p => (2 * H p - pd (fun q => q 1 * H q) 1 p) • e 2) := by
  funext p
  have hd := (hasFDerivAt_coord 1 p).mul (hH.differentiable (by simp) p).hasFDerivAt
  have h2 : pd (fun q => q 1 * H q) 2 p = p 1 * pd H 2 p := by
    simp only [pd]
    rw [show (fun q : ℝ³ => q 1 * H q) = (fun q : ℝ³ => q 1) * H from rfl, hd.fderiv]
    simp
  have h1 : pd (fun q => q 1 * H q) 1 p = H p + p 1 * pd H 1 p := by
    simp only [pd]
    rw [show (fun q : ℝ³ => q 1 * H q) = (fun q : ℝ³ => q 1) * H from rfl, hd.fderiv]
    simp; ring
  show hamVF H p = (-(pd H 1 p)) • e 0 + (pd H 0 p + pd (fun q => q 1 * H q) 2 p) • e 1 +
    (2 * H p - pd (fun q => q 1 * H q) 1 p) • e 2
  rw [h1, h2]
  ext i; fin_cases i <;> (simp [hamVF]; try ring)

open ContactMotions in
/-- Norm bound for the derivatives of `X_H` through those of `H` and `yH`. -/
lemma gp5_norm_iteratedFDeriv_hamVF_le (H : ℝ³ → ℝ) (hH : ContDiff ℝ ∞ H) (k : ℕ) (p : ℝ³) :
    ‖iteratedFDeriv ℝ k (hamVF H) p‖ ≤
      2 * ‖iteratedFDeriv ℝ (k + 1) H p‖ + 2 * ‖iteratedFDeriv ℝ (k + 1) (fun q => q 1 * H q) p‖ +
        2 * ‖iteratedFDeriv ℝ k H p‖ := by
  set yH : ℝ³ → ℝ := fun q => q 1 * H q with hyH
  have hyHs : ContDiff ℝ ∞ yH := (contDiff_coord 1).mul hH
  -- `‖D^k (∂ᵢ G)‖ ≤ ‖D^{k+1} G‖`
  have hpd : ∀ (G : ℝ³ → ℝ), ContDiff ℝ ∞ G → ∀ i,
      ‖iteratedFDeriv ℝ k (pd G i) p‖ ≤ ‖iteratedFDeriv ℝ (k + 1) G p‖ := by
    intro G hG i
    have h := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ G) (c := e i) (x := p) (N := ∞)
      (n := k) (hG.fderiv_right (m := ∞) (by simp)).contDiffAt (by simp)
    rw [norm_iteratedFDeriv_fderiv] at h
    have he : ‖e i‖ = 1 := by
      rw [e, PiLp.norm_single, norm_one]
    rw [he, one_mul] at h
    exact h
  -- `‖D^k (c • v)‖ ≤ ‖D^k c‖` for a unit vector `v`
  have hsmul : ∀ (c : ℝ³ → ℝ), ContDiff ℝ ∞ c → ∀ v : ℝ³, ‖v‖ = 1 →
      ‖iteratedFDeriv ℝ k (fun q => c q • v) p‖ ≤ ‖iteratedFDeriv ℝ k c p‖ := by
    intro c hc v hv
    have hcomp : (fun q => c q • v) = (ContinuousLinearMap.toSpanSingleton ℝ v) ∘ c := by
      funext q; simp [ContinuousLinearMap.toSpanSingleton_apply]
    rw [hcomp]
    refine ((ContinuousLinearMap.toSpanSingleton ℝ v).norm_iteratedFDeriv_comp_left (N := ∞)
      hc.contDiffAt (by simp)).trans ?_
    rw [ContinuousLinearMap.norm_toSpanSingleton, hv, one_mul]
  have he0 : ‖e 0‖ = 1 := by rw [e, PiLp.norm_single, norm_one]
  have he1 : ‖e 1‖ = 1 := by rw [e, PiLp.norm_single, norm_one]
  have he2 : ‖e 2‖ = 1 := by rw [e, PiLp.norm_single, norm_one]
  -- smoothness of the pieces
  have hpd1 : ContDiff ℝ ∞ (pd H 1) := contDiff_pd hH 1
  have hpd0 : ContDiff ℝ ∞ (pd H 0) := contDiff_pd hH 0
  have hpdy2 : ContDiff ℝ ∞ (pd yH 2) := contDiff_pd hyHs 2
  have hpdy1 : ContDiff ℝ ∞ (pd yH 1) := contDiff_pd hyHs 1
  set a : ℝ³ → ℝ³ := fun p => (-(pd H 1 p)) • e 0 with ha
  set b : ℝ³ → ℝ³ := fun p => (pd H 0 p + pd yH 2 p) • e 1 with hb
  set c : ℝ³ → ℝ³ := fun p => (2 * H p - pd yH 1 p) • e 2 with hc
  have has : ContDiff ℝ ∞ a := hpd1.neg.smul contDiff_const
  have hbs : ContDiff ℝ ∞ b := (hpd0.add hpdy2).smul contDiff_const
  have hcs : ContDiff ℝ ∞ c := ((contDiff_const.mul hH).sub hpdy1).smul contDiff_const
  have heq : hamVF H = a + b + c := gp5_hamVF_eq H hH
  have hab : ContDiff ℝ ∞ (a + b) := has.add hbs
  rw [heq, iteratedFDeriv_add_apply (hab.contDiffAt.of_le (by simp)) (hcs.contDiffAt.of_le (by simp)),
    iteratedFDeriv_add_apply (has.contDiffAt.of_le (by simp)) (hbs.contDiffAt.of_le (by simp))]
  -- bounds for the three pieces
  have hA : ‖iteratedFDeriv ℝ k a p‖ ≤ ‖iteratedFDeriv ℝ (k + 1) H p‖ := by
    refine (hsmul _ hpd1.neg (e 0) he0).trans ?_
    have : (fun p => -(pd H 1 p)) = -(pd H 1) := rfl
    rw [this, iteratedFDeriv_neg_apply, norm_neg]
    exact hpd H hH 1
  have hB : ‖iteratedFDeriv ℝ k b p‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) H p‖ + ‖iteratedFDeriv ℝ (k + 1) yH p‖ := by
    refine (hsmul _ (hpd0.add hpdy2) (e 1) he1).trans ?_
    have : (fun p => pd H 0 p + pd yH 2 p) = pd H 0 + pd yH 2 := rfl
    rw [this, iteratedFDeriv_add_apply (hpd0.contDiffAt.of_le (by simp)) (hpdy2.contDiffAt.of_le (by simp))]
    exact (norm_add_le _ _).trans (add_le_add (hpd H hH 0) (hpd yH hyHs 2))
  have hC : ‖iteratedFDeriv ℝ k c p‖ ≤
      2 * ‖iteratedFDeriv ℝ k H p‖ + ‖iteratedFDeriv ℝ (k + 1) yH p‖ := by
    refine (hsmul _ ((contDiff_const.mul hH).sub hpdy1) (e 2) he2).trans ?_
    have : (fun p => 2 * H p - pd yH 1 p) = (2 : ℝ) • H - pd yH 1 := by
      funext q; simp [smul_eq_mul]
    have h2H : ContDiff ℝ ∞ ((2 : ℝ) • H) := hH.const_smul (2 : ℝ)
    rw [this, iteratedFDeriv_sub_apply (h2H.contDiffAt.of_le (by simp))
      (hpdy1.contDiffAt.of_le (by simp)), iteratedFDeriv_const_smul_apply (hH.contDiffAt.of_le (by simp))]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (hpd yH hyHs 1))
    rw [norm_smul, Real.norm_eq_abs, abs_two]
  calc ‖iteratedFDeriv ℝ k a p + iteratedFDeriv ℝ k b p + iteratedFDeriv ℝ k c p‖
      ≤ ‖iteratedFDeriv ℝ k a p‖ + ‖iteratedFDeriv ℝ k b p‖ + ‖iteratedFDeriv ℝ k c p‖ :=
        norm_add₃_le
    _ ≤ ‖iteratedFDeriv ℝ (k + 1) H p‖ +
        (‖iteratedFDeriv ℝ (k + 1) H p‖ + ‖iteratedFDeriv ℝ (k + 1) yH p‖) +
        (2 * ‖iteratedFDeriv ℝ k H p‖ + ‖iteratedFDeriv ℝ (k + 1) yH p‖) :=
          add_le_add (add_le_add hA hB) hC
    _ = _ := by ring

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
  set ψ := cuspHam f y₀ A with hψ
  -- `ψ′ = g`, `ψ″ = g₂`, `ψ‴ = g₃`
  set g : ℝ → ℝ := fun v => f v - (f y₀ + A * (v - y₀) ^ 2) with hg
  set g₂ : ℝ → ℝ := fun v => deriv f v - 2 * A * (v - y₀) with hg₂
  have hf1 : ∀ v, HasDerivAt f (deriv f v) v := fun v => (hf.differentiable (by simp) v).hasDerivAt
  have hfd2s : ContDiff ℝ ∞ (deriv f) := hf.iterate_deriv 1
  have hf2 : ∀ v, HasDerivAt (deriv f) (deriv (deriv f) v) v := fun v =>
    (hfd2s.differentiable (by simp) v).hasDerivAt
  have hgs : ContDiff ℝ ∞ g :=
    hf.sub (contDiff_const.add (contDiff_const.mul ((contDiff_id.sub contDiff_const).pow 2)))
  have hg₂s : ContDiff ℝ ∞ g₂ := hfd2s.sub (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have hψd : ∀ v, HasDerivAt ψ (g v) v := fun v =>
    intervalIntegral.integral_hasDerivAt_right (hgs.continuous.intervalIntegrable _ _)
      (hgs.continuous.stronglyMeasurableAtFilter _ _) hgs.continuous.continuousAt
  have hψ' : deriv ψ = g := funext fun v => (hψd v).deriv
  have hgd : ∀ v, HasDerivAt g (g₂ v) v := by
    intro v
    have h1 : HasDerivAt (fun v => f y₀ + A * (v - y₀) ^ 2) (A * (2 * (v - y₀))) v := by
      have := (((hasDerivAt_id v).sub_const y₀).pow 2).const_mul A
      refine (this.const_add (f y₀)).congr_deriv ?_
      simp
    refine ((hf1 v).sub h1).congr_deriv ?_
    simp only [hg₂]; ring
  have hg' : deriv g = g₂ := funext fun v => (hgd v).deriv
  have hg₂d : ∀ v, HasDerivAt g₂ (deriv (deriv f) v - 2 * A) v := by
    intro v
    have h1 : HasDerivAt (fun v => 2 * A * (v - y₀)) (2 * A) v := by
      simpa using ((hasDerivAt_id v).sub_const y₀).const_mul (2 * A)
    exact (hf2 v).sub h1
  have hψs : ContDiff ℝ ∞ ψ :=
    contDiff_infty_iff_deriv.2 ⟨fun v => (hψd v).differentiableAt, hψ' ▸ hgs⟩
  have hψ1s : ContDiff ℝ ∞ (deriv ψ) := hψ' ▸ hgs
  have hψ2s : ContDiff ℝ ∞ (deriv (deriv ψ)) := by rw [hψ', hg']; exact hg₂s
  have hψ1d : ∀ v, HasDerivAt ψ (deriv ψ v) v := fun v => (hψs.differentiable (by simp) v).hasDerivAt
  have hψ2d : ∀ v, HasDerivAt (deriv ψ) (deriv (deriv ψ) v) v := fun v =>
    (hψ1s.differentiable (by simp) v).hasDerivAt
  have hψ3d : ∀ v, HasDerivAt (deriv (deriv ψ)) (deriv (deriv (deriv ψ)) v) v := fun v =>
    (hψ2s.differentiable (by simp) v).hasDerivAt
  -- vanishing at `y₀` to order `3`
  have hψ0 : ψ y₀ = 0 := by simp [hψ, cuspHam]
  have hψ1 : deriv ψ y₀ = 0 := by rw [hψ']; simp [hg]
  have hψ2 : deriv (deriv ψ) y₀ = 0 := by rw [hψ', hg']; simp [hg₂, hf']
  have hψ3 : deriv (deriv (deriv ψ)) y₀ = 0 := by
    rw [hψ', hg', (hg₂d y₀).deriv, hf'']; ring
  -- `χ₂ = y ψ(y)` also vanishes to order `3`
  set χ₂ : ℝ → ℝ := fun v => v * ψ v with hχ₂
  have hχ₂s : ContDiff ℝ ∞ χ₂ := contDiff_id.mul hψs
  have hχ₂d : ∀ v, HasDerivAt χ₂ (ψ v + v * deriv ψ v) v := fun v => by
    rw [hχ₂]
    exact ((hasDerivAt_id v).mul (hψ1d v)).congr_deriv (by simp only [id_eq, one_mul])
  have hχ₂1 : deriv χ₂ = fun v => ψ v + v * deriv ψ v := funext fun v => (hχ₂d v).deriv
  have hχ₂2d : ∀ v, HasDerivAt (fun v => ψ v + v * deriv ψ v)
      (deriv ψ v + (deriv ψ v + v * deriv (deriv ψ) v)) v := fun v =>
    ((hψ1d v).add ((hasDerivAt_id v).mul (hψ2d v))).congr_deriv (by simp only [id_eq, one_mul])
  have hχ₂2 : deriv (deriv χ₂) = fun v => deriv ψ v + (deriv ψ v + v * deriv (deriv ψ) v) := by
    rw [hχ₂1]; exact funext fun v => (hχ₂2d v).deriv
  have hχ₂3 : deriv (deriv (deriv χ₂)) y₀ = 0 := by
    rw [hχ₂2]
    have h : HasDerivAt (fun v => deriv ψ v + (deriv ψ v + v * deriv (deriv ψ) v))
        (deriv (deriv ψ) y₀ + (deriv (deriv ψ) y₀ +
          (1 * deriv (deriv ψ) y₀ + y₀ * deriv (deriv (deriv ψ)) y₀))) y₀ :=
      (hψ2d y₀).add ((hψ2d y₀).add ((hasDerivAt_id y₀).mul (hψ3d y₀)))
    rw [h.deriv]
    simp [hψ2, hψ3]
  have hχ₂0 : χ₂ y₀ = 0 := by simp [hχ₂, hψ0]
  have hχ₂1' : deriv χ₂ y₀ = 0 := by rw [hχ₂1]; simp [hψ0, hψ1]
  have hχ₂2' : deriv (deriv χ₂) y₀ = 0 := by rw [hχ₂2]; simp [hψ1, hψ2]
  -- the constants
  obtain ⟨K₁, hK₁0, hK₁⟩ := gp5_cutoff_bound ψ hψs y₀ hψ0 hψ1 hψ2 hψ3 pc hpc
  obtain ⟨K₂, hK₂0, hK₂⟩ := gp5_cutoff_bound χ₂ hχ₂s y₀ hχ₂0 hχ₂1' hχ₂2' hχ₂3 pc hpc
  set Kt : ℝ := 4 * K₁ + 2 * K₂ + 1 with hKt
  have hKt0 : 0 < Kt := by positivity
  set ε : ℝ := min (min ε₀ 1) (η / Kt) with hεdef
  have hε : 0 < ε := lt_min (lt_min hε₀ one_pos) (div_pos hη hKt0)
  have hεε₀ : ε ≤ ε₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hεη : Kt * ε ≤ η := by
    have : ε ≤ η / Kt := min_le_right _ _
    rwa [le_div_iff₀ hKt0, mul_comm] at this
  set H : ℝ³ → ℝ := fun p => ψ (p 1) * gp5_bump pc ε p with hH
  have hHs : ContDiff ℝ ∞ H := (hψs.comp (ContactMotions.contDiff_coord 1)).mul (gp5_bump_contDiff pc ε)
  have hHc : HasCompactSupport H := (gp5_bump_hasCompactSupport hε).mul_left
  refine ⟨ε, H, hε, hεε₀, ⟨hHs, hHc⟩, ?_, ?_, ?_⟩
  · intro p hp
    simp only [hH]
    rw [gp5_bump_one hε (Metric.mem_ball.1 hp).le, mul_one]
  · exact tsupport_mul_subset_right.trans (gp5_bump_tsupport hε)
  · intro k hk p
    have hyH : (fun q : ℝ³ => q 1 * H q) = fun q => χ₂ (q 1) * gp5_bump pc ε q := by
      funext q; simp only [hH, hχ₂]; ring
    calc ‖iteratedFDeriv ℝ k (hamVF H) p‖
        ≤ 2 * ‖iteratedFDeriv ℝ (k + 1) H p‖ +
            2 * ‖iteratedFDeriv ℝ (k + 1) (fun q => q 1 * H q) p‖ +
            2 * ‖iteratedFDeriv ℝ k H p‖ := gp5_norm_iteratedFDeriv_hamVF_le H hHs k p
      _ ≤ 2 * (K₁ * ε) + 2 * (K₂ * ε) + 2 * (K₁ * ε) := by
          rw [hyH]
          gcongr
          · exact hK₁ ε hε hε1 (k + 1) (by omega) p
          · exact hK₂ ε hε hε1 (k + 1) (by omega) p
          · exact hK₁ ε hε hε1 k (by omega) p
      _ = (4 * K₁ + 2 * K₂) * ε := by ring
      _ ≤ Kt * ε := by
          gcongr
          simp only [hKt]; linarith
      _ ≤ η := hεη

/-- `e^η ≤ 4` for `0 ≤ η ≤ 1` (elementary: `e^{η/2} ≤ 1/(1 − η/2) ≤ 2`). -/
lemma gp5_exp_le_four {η : ℝ} (h1 : η ≤ 1) : Real.exp η ≤ 4 := by
  have hpos := Real.exp_pos (η / 2)
  have h2 : Real.exp (η / 2) ≤ 2 := by
    have h := Real.add_one_le_exp (-(η / 2))
    rw [Real.exp_neg] at h
    have h3 : (1 - η / 2) * Real.exp (η / 2) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h hpos.le
      rwa [inv_mul_cancel₀ hpos.ne', show -(η / 2) + 1 = 1 - η / 2 by ring] at this
    nlinarith
  have : Real.exp η = Real.exp (η / 2) * Real.exp (η / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]
  nlinarith

/-- `e^η − 1 ≤ 4η` for `0 ≤ η ≤ 1`. -/
lemma gp5_exp_sub_one_le {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) : Real.exp η - 1 ≤ 4 * η := by
  have h := Real.add_one_le_exp (-η)
  rw [Real.exp_neg] at h
  have hpos := Real.exp_pos η
  have h3 : (1 - η) * Real.exp η ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h hpos.le
    rwa [inv_mul_cancel₀ hpos.ne', show -η + 1 = 1 - η by ring] at this
  have h4 := gp5_exp_le_four h1
  nlinarith

/-- The Grönwall bound with `δ = 0`, `K = η ≤ 1` on `[0,1]` is at most `4ε`. -/
lemma gp5_gronwallBound_le {η ε x : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 ≤ ε)
    (hx1 : x ≤ 1) : gronwallBound 0 η ε x ≤ 4 * ε := by
  rw [gronwallBound_of_K_ne_0 hη.ne']
  simp only [zero_mul, zero_add]
  have h1 : Real.exp (η * x) - 1 ≤ 4 * η := by
    have : Real.exp (η * x) ≤ Real.exp η := Real.exp_le_exp.2 (by nlinarith)
    linarith [gp5_exp_sub_one_le hη.le hη1]
  calc ε / η * (Real.exp (η * x) - 1) ≤ ε / η * (4 * η) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hε hη.le)
    _ = 4 * ε := by field_simp

open ContactMotions in
/-- If `Ψ` is jointly smooth and `∂_s Ψ s p = G s p`, then `∂_s (D_p Ψ_s (p)) = D_p (G s) (p)`
(symmetry of the second derivative of `uncurry Ψ`). -/
lemma gp5_hasDerivAt_fderiv_of_time_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ψ G : ℝ → ℝ³ → F} (hΨ : ContDiff ℝ ∞ (uncurry Ψ))
    (hder : ∀ s p, HasDerivAt (fun s => Ψ s p) (G s p) s) (s : ℝ) (p : ℝ³) :
    HasDerivAt (fun s => fderiv ℝ (Ψ s) p) (fderiv ℝ (G s) p) s := by
  have hd : ∀ q : ℝ × ℝ³, HasFDerivAt (uncurry Ψ) (fderiv ℝ (uncurry Ψ) q) q := fun q =>
    (hΨ.differentiable (by simp) q).hasFDerivAt
  have htime : ∀ s p, fderiv ℝ (uncurry Ψ) (s, p) (1, 0) = G s p := by
    intro s p
    have hc : HasDerivAt (fun s : ℝ => (s, p)) ((1 : ℝ), (0 : ℝ³)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s p)
    have hdsp : HasFDerivAt (uncurry Ψ) (fderiv ℝ (uncurry Ψ) (s, p)) (s, p) := hd (s, p)
    have h1 := hdsp.comp_hasDerivAt s hc
    exact h1.unique (hder s p)
  have hspace : ∀ s p, fderiv ℝ (Ψ s) p =
      (fderiv ℝ (uncurry Ψ) (s, p)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ³) := fun s p =>
    ((hd (s, p)).comp p (hasFDerivAt_prodMk_right s p)).fderiv
  have hGeq : uncurry G = fun q : ℝ × ℝ³ => fderiv ℝ (uncurry Ψ) q (1, 0) := by
    funext ⟨s, p⟩; exact (htime s p).symm
  have hD1 : ContDiff ℝ ∞ (fderiv ℝ (uncurry Ψ)) := hΨ.fderiv_right (m := ∞) (by simp)
  have hGs : ContDiff ℝ ∞ (uncurry G) := by
    rw [hGeq]; exact hD1.clm_apply contDiff_const
  have hGd : HasFDerivAt (uncurry G) (fderiv ℝ (uncurry G) (s, p)) (s, p) :=
    (hGs.differentiable (by simp) _).hasFDerivAt
  have hGspace : fderiv ℝ (G s) p =
      (fderiv ℝ (uncurry G) (s, p)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ³) :=
    (hGd.comp p (hasFDerivAt_prodMk_right s p)).fderiv
  have hDd : HasFDerivAt (fderiv ℝ (uncurry Ψ)) (fderiv ℝ (fderiv ℝ (uncurry Ψ)) (s, p)) (s, p) :=
    (hD1.differentiable (by simp) _).hasFDerivAt
  have hc : HasDerivAt (fun s : ℝ => (s, p)) ((1 : ℝ), (0 : ℝ³)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s p)
  have hDs : HasDerivAt (fun s => fderiv ℝ (uncurry Ψ) (s, p))
      (fderiv ℝ (fderiv ℝ (uncurry Ψ)) (s, p) (1, 0)) s := hDd.comp_hasDerivAt s hc
  have h1 : HasDerivAt
      (fun s => (fderiv ℝ (uncurry Ψ) (s, p)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ³))
      ((fderiv ℝ (fderiv ℝ (uncurry Ψ)) (s, p) (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ³)) s := by
    have := hDs.clm_comp (hasDerivAt_const s (ContinuousLinearMap.inr ℝ ℝ ℝ³))
    simpa using this
  have hsymm : ∀ v : ℝ³, fderiv ℝ (fderiv ℝ (uncurry Ψ)) (s, p) (1, 0) (0, v) =
      fderiv ℝ (fderiv ℝ (uncurry Ψ)) (s, p) (0, v) (1, 0) := fun v =>
    (hΨ.contDiffAt.isSymmSndFDerivAt minSmoothness_two_le) _ _
  have hA : HasFDerivAt (fun q : ℝ × ℝ³ => fderiv ℝ (uncurry Ψ) q (1, 0))
      ((fderiv ℝ (fderiv ℝ (uncurry Ψ)) (s, p)).flip (1, 0)) (s, p) := by
    have h := hDd.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : ℝ³)) (s, p))
    refine h.congr_fderiv ?_
    simp
  have hA' : HasFDerivAt (uncurry G) ((fderiv ℝ (fderiv ℝ (uncurry Ψ)) (s, p)).flip (1, 0)) (s, p) := by
    rw [hGeq]; exact hA
  have hAB : fderiv ℝ (uncurry G) (s, p) = (fderiv ℝ (fderiv ℝ (uncurry Ψ)) (s, p)).flip (1, 0) :=
    hA'.fderiv
  have hfun : (fun s => fderiv ℝ (Ψ s) p) =
      fun s => (fderiv ℝ (uncurry Ψ) (s, p)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ³) :=
    funext fun s => hspace s p
  rw [hfun, hGspace, hAB]
  refine h1.congr_deriv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.flip_apply]
  exact hsymm v

section flowC2

variable {X : ℝ³ → ℝ³} {φ : ℝ → ℝ³ → ℝ³}

open ContactMotions in
/-- The first variational equation `∂_s Dφ_s(p) = DX(φ_s p) ∘ Dφ_s(p)` as an operator identity. -/
lemma gp5_hasDerivAt_fderiv_flow (hX : ContDiff ℝ ∞ X) (hφ : IsGlobalFlow X φ)
    (hs : ContDiff ℝ ∞ (uncurry φ)) (s : ℝ) (p : ℝ³) :
    HasDerivAt (fun s => fderiv ℝ (φ s) p) ((fderiv ℝ X (φ s p)).comp (fderiv ℝ (φ s) p)) s := by
  have h := gp5_hasDerivAt_fderiv_of_time_deriv (Ψ := φ) (G := fun s p => X (φ s p)) hs
    (fun s p => hφ.hasDerivAt s p) s p
  refine h.congr_deriv ?_
  have h1 : DifferentiableAt ℝ X (φ s p) := hX.differentiable (by simp) _
  have h2 : DifferentiableAt ℝ (φ s) p := (contDiff_flow_space hs s).differentiable (by simp) p
  exact fderiv_comp p h1 h2

open ContactMotions in
/-- The second variational equation: `∂_s D²φ_s(p) = D_p [DX(φ_s ·) ∘ Dφ_s(·)] (p)`. -/
lemma gp5_hasDerivAt_fderiv2_flow (hX : ContDiff ℝ ∞ X) (hφ : IsGlobalFlow X φ)
    (hs : ContDiff ℝ ∞ (uncurry φ)) (s : ℝ) (p : ℝ³) :
    HasDerivAt (fun s => fderiv ℝ (fderiv ℝ (φ s)) p)
      (fderiv ℝ (fun p => (fderiv ℝ X (φ s p)).comp (fderiv ℝ (φ s) p)) p) s := by
  have hD1 : ContDiff ℝ ∞ (fderiv ℝ (uncurry φ)) := hs.fderiv_right (m := ∞) (by simp)
  have hΨ : ContDiff ℝ ∞ (uncurry fun s p => fderiv ℝ (φ s) p) := by
    have : (uncurry fun s p => fderiv ℝ (φ s) p) =
        fun q : ℝ × ℝ³ => (fderiv ℝ (uncurry φ) q).comp (ContinuousLinearMap.inr ℝ ℝ ℝ³) := by
      funext ⟨s, p⟩
      show fderiv ℝ (φ s) p = _
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
      exact fderiv_flow_space hs s p v
    rw [this]
    exact hD1.clm_comp contDiff_const
  exact gp5_hasDerivAt_fderiv_of_time_deriv (Ψ := fun s p => fderiv ℝ (φ s) p)
    (G := fun s p => (fderiv ℝ X (φ s p)).comp (fderiv ℝ (φ s) p)) hΨ
    (fun s p => gp5_hasDerivAt_fderiv_flow hX hφ hs s p) s p

end flowC2

/-- LEAF P5.5 (general).  The time-one map of a `C²`-small compactly supported field is `C²`-close
to the identity (sm-3:2758-2761: `J′ = DX·J`, `M′ = DX·M + D²X[J,J]`, Grönwall). -/
theorem flow_C2_close : ∃ C₀ > 0, ∀ (X : ℝ³ → ℝ³), ContDiff ℝ ∞ X → HasCompactSupport X →
    ∀ η, 0 < η → η ≤ 1 → (∀ k ≤ 2, ∀ p, ‖iteratedFDeriv ℝ k X p‖ ≤ η) →
      ∀ k ≤ 2, ∀ p, ‖iteratedFDeriv ℝ k (fun p => ContactMotions.globalFlow X 1 p - p) p‖ ≤ C₀ * η := by
  refine ⟨100, by norm_num, ?_⟩
  intro X hX hc η hη hη1 hb k hk p
  set φ := ContactMotions.globalFlow X with hφdef
  have hφ : ContactMotions.IsGlobalFlow X φ :=
    ContactMotions.isGlobalFlow_globalFlow hc (hX.of_le (by simp))
  have hs : ContDiff ℝ ∞ (uncurry φ) := ContactMotions.contDiff_uncurry hX hc hφ
  have hb0 : ∀ q, ‖X q‖ ≤ η := fun q => by
    have := hb 0 (by norm_num) q
    rwa [norm_iteratedFDeriv_zero] at this
  have hb1 : ∀ q, ‖fderiv ℝ X q‖ ≤ η := fun q => by
    have := hb 1 (by norm_num) q
    rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at this
  have hb2 : ∀ q, ‖fderiv ℝ (fderiv ℝ X) q‖ ≤ η := fun q => by
    have := hb 2 (by norm_num) q
    rwa [← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at this
  have hφ0 : φ 0 = id := funext hφ.zero
  -- `J_s = Dφ_s(p)`: Grönwall
  set J : ℝ → ℝ³ →L[ℝ] ℝ³ := fun s => fderiv ℝ (φ s) p with hJ
  have hJd : ∀ s, HasDerivAt J ((fderiv ℝ X (φ s p)).comp (J s)) s := fun s =>
    gp5_hasDerivAt_fderiv_flow hX hφ hs s p
  have hJ0 : J 0 = 1 := by
    simp only [hJ, hφ0, fderiv_id]; rfl
  have hJbound : ∀ s ∈ Icc (0 : ℝ) 1, ‖J s - 1‖ ≤ 4 * η := by
    intro s hs'
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s => J s - 1)
      (f' := fun s => (fderiv ℝ X (φ s p)).comp (J s)) (δ := 0) (K := η) (ε := η) (a := 0) (b := 1)
      (fun t _ => ((hJd t).sub_const 1).continuousAt.continuousWithinAt)
      (fun t _ => ((hJd t).sub_const 1).hasDerivWithinAt)
      (by simp [hJ0])
      (fun t _ => by
        have heq : (fderiv ℝ X (φ t p)).comp (J t) =
            (fderiv ℝ X (φ t p)).comp (J t - 1) + fderiv ℝ X (φ t p) := by
          rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.one_def,
            ContinuousLinearMap.comp_id, sub_add_cancel]
        rw [heq]
        calc ‖(fderiv ℝ X (φ t p)).comp (J t - 1) + fderiv ℝ X (φ t p)‖
            ≤ ‖(fderiv ℝ X (φ t p)).comp (J t - 1)‖ + ‖fderiv ℝ X (φ t p)‖ := norm_add_le _ _
          _ ≤ ‖fderiv ℝ X (φ t p)‖ * ‖J t - 1‖ + ‖fderiv ℝ X (φ t p)‖ :=
              add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) le_rfl
          _ ≤ η * ‖J t - 1‖ + η := by gcongr <;> exact hb1 _)
      s hs'
    rw [sub_zero] at h
    exact h.trans (gp5_gronwallBound_le hη hη1 hη.le hs'.2)
  have hJnorm : ∀ s ∈ Icc (0 : ℝ) 1, ‖J s‖ ≤ 5 := by
    intro s hs'
    calc ‖J s‖ = ‖(J s - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖J s - 1‖ + ‖(1 : ℝ³ →L[ℝ] ℝ³)‖ := norm_add_le _ _
      _ ≤ 4 * η + 1 := by
          gcongr
          · exact hJbound s hs'
          · rw [ContinuousLinearMap.one_def]; exact ContinuousLinearMap.norm_id_le
      _ ≤ 5 := by linarith
  -- `M_s = D²φ_s(p)`: Grönwall
  set M : ℝ → ℝ³ →L[ℝ] ℝ³ →L[ℝ] ℝ³ := fun s => fderiv ℝ (fderiv ℝ (φ s)) p with hM
  have hMd : ∀ s, HasDerivAt M
      (fderiv ℝ (fun p => (fderiv ℝ X (φ s p)).comp (fderiv ℝ (φ s) p)) p) s := fun s =>
    gp5_hasDerivAt_fderiv2_flow hX hφ hs s p
  have hM0 : M 0 = 0 := by
    have : fderiv ℝ (φ 0) = fun _ => (1 : ℝ³ →L[ℝ] ℝ³) := by
      funext q; rw [hφ0, fderiv_id, ContinuousLinearMap.one_def]
    simp only [hM, this, fderiv_const_apply]
  have hMbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖fderiv ℝ (fun p => (fderiv ℝ X (φ t p)).comp (fderiv ℝ (φ t) p)) p‖ ≤
        η * ‖M t‖ + 25 * η := by
    intro t ht
    have hJt : ‖J t‖ ≤ 5 := hJnorm t (Ico_subset_Icc_self ht)
    have hφt : ContDiff ℝ ∞ (φ t) := ContactMotions.contDiff_flow_space hs t
    have hcd : HasFDerivAt (fun p => fderiv ℝ X (φ t p))
        ((fderiv ℝ (fderiv ℝ X) (φ t p)).comp (J t)) p :=
      ((hX.fderiv_right (m := ∞) (by simp)).differentiable (by simp) _).hasFDerivAt.comp p
        (hφt.differentiable (by simp) p).hasFDerivAt
    have hdd : HasFDerivAt (fun p => fderiv ℝ (φ t) p) (M t) p :=
      ((hφt.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p).hasFDerivAt
    have hprod := hcd.clm_comp hdd
    rw [hprod.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
    calc ‖(fderiv ℝ X (φ t p)).comp (M t w) + (fderiv ℝ (fderiv ℝ X) (φ t p) (J t w)).comp (J t)‖
        ≤ ‖(fderiv ℝ X (φ t p)).comp (M t w)‖ +
            ‖(fderiv ℝ (fderiv ℝ X) (φ t p) (J t w)).comp (J t)‖ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ X (φ t p)‖ * ‖M t w‖ + ‖fderiv ℝ (fderiv ℝ X) (φ t p) (J t w)‖ * ‖J t‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ η * (‖M t‖ * ‖w‖) + (‖fderiv ℝ (fderiv ℝ X) (φ t p)‖ * ‖J t w‖) * 5 := by
          gcongr
          · exact hb1 _
          · exact ContinuousLinearMap.le_opNorm _ _
          · exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ η * (‖M t‖ * ‖w‖) + (η * (‖J t‖ * ‖w‖)) * 5 := by
          gcongr
          · exact hb2 _
          · exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ η * (‖M t‖ * ‖w‖) + (η * (5 * ‖w‖)) * 5 := by gcongr
      _ = (η * ‖M t‖ + 25 * η) * ‖w‖ := by ring
  have hM1 : ‖M 1‖ ≤ 100 * η := by
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := M)
      (f' := fun t => fderiv ℝ (fun p => (fderiv ℝ X (φ t p)).comp (fderiv ℝ (φ t) p)) p)
      (δ := 0) (K := η) (ε := 25 * η) (a := 0) (b := 1)
      (fun t _ => (hMd t).continuousAt.continuousWithinAt)
      (fun t _ => (hMd t).hasDerivWithinAt)
      (by rw [hM0]; exact (norm_zero (E := ℝ³ →L[ℝ] ℝ³ →L[ℝ] ℝ³)).le)
      (fun t ht => hMbound t ht) 1 ⟨zero_le_one, le_rfl⟩
    rw [sub_zero] at h
    refine h.trans ((gp5_gronwallBound_le hη hη1 (by positivity) le_rfl).trans ?_)
    linarith
  -- the three orders
  have hφ1 : ContDiff ℝ ∞ (φ 1) := ContactMotions.contDiff_flow_space hs 1
  have hg1 : fderiv ℝ (fun p => φ 1 p - p) = fun p => fderiv ℝ (φ 1) p - 1 := by
    funext q
    have h := (hφ1.differentiable (by simp) q).hasFDerivAt.sub (hasFDerivAt_id q)
    exact h.fderiv
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · rw [norm_iteratedFDeriv_zero]
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => φ s p)
      (f' := fun s => X (φ s p)) (a := 0) (b := 1) (C := η)
      (fun s _ => (hφ.hasDerivAt s p).hasDerivWithinAt) (fun s _ => hb0 _) 1 ⟨zero_le_one, le_rfl⟩
    simp only [hφ.zero, sub_zero, mul_one] at hmvt
    linarith
  · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero, hg1]
    have := hJbound 1 ⟨zero_le_one, le_rfl⟩
    simp only [hJ] at this
    linarith
  · rw [← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero, hg1,
      fderiv_sub_const]
    exact hM1

/-- Reduction of a parameter into the period `[a, a + 2π)`. -/
lemma gp5_reduce (a θ : ℝ) : ∃ k : ℤ, θ - 2 * π * k ∈ Ico a (a + 2 * π) := by
  refine ⟨⌊(θ - a) / (2 * π)⌋, ?_⟩
  have h2π : 0 < 2 * π := by positivity
  have h1 := Int.floor_le ((θ - a) / (2 * π))
  have h2 := Int.lt_floor_add_one ((θ - a) / (2 * π))
  rw [le_div_iff₀ h2π] at h1
  rw [div_lt_iff₀ h2π] at h2
  constructor <;> linarith

/-- The derivative of a `2π`-periodic function is `2π`-periodic. -/
lemma gp5_periodic_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : Periodic f (2 * π)) : Periodic (deriv f) (2 * π) := by
  intro θ
  have : (fun x => f (x + 2 * π)) = f := funext fun x => hf x
  rw [← deriv_comp_add_const, this]

/-- A periodic function is invariant under shifts by `2πk`. -/
lemma gp5_periodic_int {E : Type*} {f : ℝ → E} (hf : Periodic f (2 * π)) (θ : ℝ) (k : ℤ) :
    f (θ + 2 * π * k) = f θ := by
  have := hf.int_mul k θ
  rwa [show θ + 2 * π * k = θ + k * (2 * π) by ring]

/-- A continuous periodic function is bounded. -/
lemma gp5_bounded_of_periodic {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f)
    (hp : Periodic f (2 * π)) : ∃ B, 0 ≤ B ∧ ∀ θ, ‖f θ‖ ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun θ => ?_⟩
  obtain ⟨k, hk⟩ := gp5_reduce 0 θ
  have hk' : θ - 2 * π * k ∈ Icc 0 (2 * π) := by
    rw [zero_add] at hk; exact Ico_subset_Icc_self hk
  have : f θ = f (θ - 2 * π * k) := by
    rw [show θ - 2 * π * k = θ - k * (2 * π) by ring]
    exact (hp.sub_int_mul_eq k).symm
  rw [this]
  exact (hC _ hk').trans (le_max_left _ _)

/-- A positive lower bound for finitely many positive numbers. -/
lemma gp5_finset_min {ι : Type*} (S : Finset ι) (r : ι → ℝ) (hr : ∀ j ∈ S, 0 < r j) :
    ∃ ρ > 0, ∀ j ∈ S, ρ ≤ r j := by
  rcases S.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨j₀, hj₀, hmin⟩ := S.exists_min_image r h
    exact ⟨r j₀, hr j₀ hj₀, hmin⟩

lemma gp5_sameParam_shift {θ η : ℝ} (k : ℤ) : SameParam θ (η + 2 * π * k) ↔ SameParam θ η := by
  constructor
  · rintro ⟨k', hk'⟩
    refine ⟨k' - k, ?_⟩
    push_cast; linarith
  · rintro ⟨k', hk'⟩
    refine ⟨k' + k, ?_⟩
    push_cast; linarith

/-- Shifting the second argument by `2πk` does not change `circDist`. -/
lemma gp5_circDist_shift (θ η : ℝ) (k : ℤ) : circDist θ (η + 2 * π * k) = circDist θ η := by
  simp only [circDist]
  have h2π : (2 * π) ≠ 0 := by positivity
  have : (θ - (η + 2 * π * k)) / (2 * π) = (θ - η) / (2 * π) - k := by field_simp; ring
  rw [this, round_sub_intCast]
  congr 1; push_cast; ring

/-- The representative `η + 2π·round((θ − η)/2π)` realizes the circular distance. -/
lemma gp5_circDist_eq_abs (θ η : ℝ) :
    circDist θ η = |θ - (η + 2 * π * round ((θ - η) / (2 * π)))| := by
  simp only [circDist]; congr 1; ring

/-- For representatives in one period, `circDist ≥ δ` (`δ ≤ π`) gives `δ ≤ |θ − η| ≤ 2π − δ`. -/
lemma gp5_circDist_bounds {θ η δ : ℝ} (hθ : θ ∈ Ico 0 (2 * π)) (hη : η ∈ Ico 0 (2 * π))
    (hδ : δ ≤ π) (h : δ ≤ circDist θ η) : δ ≤ |θ - η| ∧ |θ - η| ≤ 2 * π - δ := by
  have hπ : 0 < π := Real.pi_pos
  have h2π : 0 < 2 * π := by positivity
  have hd1 : -(2 * π) < θ - η := by linarith [hθ.1, hη.2]
  have hd2 : θ - η < 2 * π := by linarith [hθ.2, hη.1]
  set x := (θ - η) / (2 * π) with hx
  have hdx : θ - η = 2 * π * x := by rw [hx]; field_simp
  have hx1 : -1 < x := by rw [hx, lt_div_iff₀ h2π]; linarith
  have hx2 : x < 1 := by rw [hx, div_lt_iff₀ h2π]; linarith
  have hcd : circDist θ η = 2 * π * |x - round x| := by
    simp only [circDist]
    rw [← hx, ← abs_of_pos h2π, ← abs_mul, abs_of_pos h2π]
    congr 1; rw [hdx]; ring
  rw [hcd] at h
  have hr := abs_sub_round x
  have hxabs : |x| < 1 := abs_lt.2 ⟨hx1, hx2⟩
  have hr1 : |(round x : ℝ)| < 3 / 2 := by
    have : (round x : ℝ) = x - (x - round x) := by ring
    rw [this]
    linarith [abs_sub (x) (x - round x)]
  have hr2 : |round x| ≤ 1 := by
    by_contra hc
    have hc' : 2 ≤ |round x| := not_le.1 hc
    have : (2 : ℝ) ≤ |(round x : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hc'
    linarith
  rcases Int.abs_le_one_iff.1 hr2 with h0 | h0 | h0
  · -- round x = 0
    rw [h0] at h hr
    simp only [Int.cast_zero, sub_zero] at h hr
    rw [hdx, abs_mul, abs_of_pos h2π]
    constructor
    · exact h
    · nlinarith
  · -- round x = 1: x ∈ [1/2, 3/2)
    have hx3 := round_eq_iff.1 h0
    rw [h0] at h
    simp only [Int.cast_one] at hx3 h
    have hxpos : 0 < x := by linarith [hx3.1]
    rw [abs_of_neg (by linarith : x - 1 < 0)] at h
    rw [hdx, abs_mul, abs_of_pos h2π, abs_of_pos hxpos]
    constructor
    · nlinarith [hx3.1]
    · nlinarith
  · -- round x = -1: x ∈ [-3/2, -1/2)
    have hx3 := round_eq_iff.1 h0
    rw [h0] at h
    simp only [Int.cast_neg, Int.cast_one] at hx3 h
    have hxneg : x < 0 := by linarith [hx3.2]
    rw [sub_neg_eq_add, abs_of_pos (by linarith : 0 < x + 1)] at h
    rw [hdx, abs_mul, abs_of_pos h2π, abs_of_neg hxneg]
    constructor
    · nlinarith [hx3.2]
    · nlinarith

/-- Curve-level `C²`-closeness: if `Ψ − id` is `C²`-small then `Ψ ∘ L` is `C²`-close to `L`. -/
lemma gp5_curve_close {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) {Ψ : ℝ³ → ℝ³} (hΨ : ContDiff ℝ ∞ Ψ)
    {η : ℝ} (hb : ∀ k ≤ 2, ∀ p, ‖iteratedFDeriv ℝ k (fun p => Ψ p - p) p‖ ≤ η) (θ : ℝ) :
    ‖deriv (Ψ ∘ L) θ - deriv L θ‖ ≤ η * ‖deriv L θ‖ ∧
    ‖deriv (deriv (Ψ ∘ L)) θ - deriv (deriv L) θ‖ ≤ η * (‖deriv L θ‖ ^ 2 + ‖deriv (deriv L) θ‖) := by
  set Φ : ℝ³ → ℝ³ := fun p => Ψ p - p with hΦ
  have hΦs : ContDiff ℝ ∞ Φ := hΨ.sub contDiff_id
  have hb1 : ∀ q, ‖fderiv ℝ Φ q‖ ≤ η := fun q => by
    have := hb 1 (by norm_num) q
    rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at this
  have hb2 : ∀ q, ‖fderiv ℝ (fderiv ℝ Φ) q‖ ≤ η := fun q => by
    have := hb 2 (by norm_num) q
    rwa [← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at this
  have hLd : ∀ θ, HasDerivAt L (deriv L θ) θ := fun θ => (hL.differentiable (by simp) θ).hasDerivAt
  have hL' : ContDiff ℝ ∞ (deriv L) := hL.iterate_deriv 1
  have hLd2 : ∀ θ, HasDerivAt (deriv L) (deriv (deriv L) θ) θ := fun θ =>
    (hL'.differentiable (by simp) θ).hasDerivAt
  have heq : Ψ ∘ L = fun θ => L θ + Φ (L θ) := by funext θ; simp [hΦ]
  have hΦd : ∀ θ, HasDerivAt (fun θ => Φ (L θ)) (fderiv ℝ Φ (L θ) (deriv L θ)) θ := fun θ =>
    (hΦs.differentiable (by simp) (L θ)).hasFDerivAt.comp_hasDerivAt θ (hLd θ)
  have hΨLd : ∀ θ, HasDerivAt (Ψ ∘ L) (deriv L θ + fderiv ℝ Φ (L θ) (deriv L θ)) θ := fun θ => by
    rw [heq]; exact (hLd θ).add (hΦd θ)
  have hd1 : deriv (Ψ ∘ L) = fun θ => deriv L θ + fderiv ℝ Φ (L θ) (deriv L θ) :=
    funext fun θ => (hΨLd θ).deriv
  have hAd : ∀ θ, HasDerivAt (fun θ => fderiv ℝ Φ (L θ))
      (fderiv ℝ (fderiv ℝ Φ) (L θ) (deriv L θ)) θ := fun θ =>
    ((hΦs.fderiv_right (m := ∞) (by simp)).differentiable (by simp) (L θ)).hasFDerivAt.comp_hasDerivAt
      θ (hLd θ)
  have hd2 : HasDerivAt (fun θ => deriv L θ + fderiv ℝ Φ (L θ) (deriv L θ))
      (deriv (deriv L) θ + (fderiv ℝ (fderiv ℝ Φ) (L θ) (deriv L θ) (deriv L θ) +
        fderiv ℝ Φ (L θ) (deriv (deriv L) θ))) θ :=
    (hLd2 θ).add ((hAd θ).clm_apply (hLd2 θ))
  constructor
  · rw [hd1]
    simp only [add_sub_cancel_left]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hb1 _) (norm_nonneg _))
  · rw [hd1, hd2.deriv]
    simp only [add_sub_cancel_left]
    calc ‖fderiv ℝ (fderiv ℝ Φ) (L θ) (deriv L θ) (deriv L θ) + fderiv ℝ Φ (L θ) (deriv (deriv L) θ)‖
        ≤ ‖fderiv ℝ (fderiv ℝ Φ) (L θ) (deriv L θ) (deriv L θ)‖ +
            ‖fderiv ℝ Φ (L θ) (deriv (deriv L) θ)‖ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ Φ) (L θ)‖ * ‖deriv L θ‖ * ‖deriv L θ‖ +
            ‖fderiv ℝ Φ (L θ)‖ * ‖deriv (deriv L) θ‖ :=
          add_le_add (ContinuousLinearMap.le_opNorm₂ _ _ _) (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ η * ‖deriv L θ‖ * ‖deriv L θ‖ + η * ‖deriv (deriv L) θ‖ := by
          gcongr
          · exact hb2 _
          · exact hb1 _
      _ = η * (‖deriv L θ‖ ^ 2 + ‖deriv (deriv L) θ‖) := by ring

/-- `C⁰`-closeness of `Ψ` to the identity from the `k = 0` bound. -/
lemma gp5_C0_close {Ψ : ℝ³ → ℝ³} {η : ℝ}
    (hb : ∀ k ≤ 2, ∀ p, ‖iteratedFDeriv ℝ k (fun p => Ψ p - p) p‖ ≤ η) (p : ℝ³) :
    ‖Ψ p - p‖ ≤ η := by
  have := hb 0 (by norm_num) p
  rwa [norm_iteratedFDeriv_zero] at this

/-- `DΨ` is injective when `‖DΨ − 1‖ ≤ η < 1`. -/
lemma gp5_fderiv_injective {Ψ : ℝ³ → ℝ³} (hΨ : ContDiff ℝ ∞ Ψ) {η : ℝ} (hη1 : η < 1)
    (hb : ∀ k ≤ 2, ∀ p, ‖iteratedFDeriv ℝ k (fun p => Ψ p - p) p‖ ≤ η) (p : ℝ³) :
    Function.Injective (fderiv ℝ Ψ p) := by
  have hb1 : ‖fderiv ℝ (fun p => Ψ p - p) p‖ ≤ η := by
    have := hb 1 (by norm_num) p
    rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at this
  have hd : fderiv ℝ (fun p => Ψ p - p) p = fderiv ℝ Ψ p - ContinuousLinearMap.id ℝ ℝ³ :=
    ((hΨ.differentiable (by simp) p).hasFDerivAt.sub (hasFDerivAt_id p)).fderiv
  rw [hd] at hb1
  intro v w hvw
  have h0 : fderiv ℝ Ψ p (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have : ‖v - w‖ ≤ η * ‖v - w‖ := by
    have h1 : (fderiv ℝ Ψ p - ContinuousLinearMap.id ℝ ℝ³) (v - w) = -(v - w) := by
      simp [h0]
    calc ‖v - w‖ = ‖(fderiv ℝ Ψ p - ContinuousLinearMap.id ℝ ℝ³) (v - w)‖ := by
          rw [h1, norm_neg]
      _ ≤ ‖fderiv ℝ Ψ p - ContinuousLinearMap.id ℝ ℝ³‖ * ‖v - w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ η * ‖v - w‖ := mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
  have hvw0 : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.1 (norm_eq_zero.1 hvw0)

/-- Coordinate derivatives of a curve. -/
lemma gp5_coord_deriv {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (i : Fin 3) (θ : ℝ) :
    deriv (fun θ => L θ i) θ = deriv L θ i ∧
    deriv (deriv (fun θ => L θ i)) θ = deriv (deriv L) θ i := by
  have hLd : ∀ θ, HasDerivAt L (deriv L θ) θ := fun θ => (hL.differentiable (by simp) θ).hasDerivAt
  have hL' : ContDiff ℝ ∞ (deriv L) := hL.iterate_deriv 1
  have hLd2 : ∀ θ, HasDerivAt (deriv L) (deriv (deriv L) θ) θ := fun θ =>
    (hL'.differentiable (by simp) θ).hasDerivAt
  have h1 : deriv (fun θ => L θ i) = fun θ => deriv L θ i :=
    funext fun θ => (ContactMotions.hasDerivAt_coord (hLd θ) i).deriv
  refine ⟨by rw [h1], ?_⟩
  rw [h1]
  exact (ContactMotions.hasDerivAt_coord (hLd2 θ) i).deriv

/-- Local injectivity of the front of a Legendrian arc through a simple cusp (positive case):
on `Icc a b ∋ θc` with `x′(θc) = 0`, `x″ > 0` and `y′ > 0`, equal `x`-values at `θ₁ < θ₂` force
different `z`-values (`z(θ₂) − z(θ₁) = ∫ y′ (X − x) > 0`). -/
lemma gp5_cusp_arc_injective_pos {x y z : ℝ → ℝ} {a b θc : ℝ} (haθ : a ≤ θc) (hθb : θc ≤ b)
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) (hz : ContDiff ℝ ∞ z)
    (hleg : ∀ θ, deriv z θ = y θ * deriv x θ) (hx'c : deriv x θc = 0)
    (hx'' : ∀ θ ∈ Icc a b, 0 < deriv (deriv x) θ) (hy' : ∀ θ ∈ Icc a b, 0 < deriv y θ) :
    ∀ θ₁ ∈ Icc a b, ∀ θ₂ ∈ Icc a b, θ₁ < θ₂ → x θ₁ = x θ₂ → z θ₁ ≠ z θ₂ := by
  intro θ₁ h₁ θ₂ h₂ hlt hxeq
  have hxc : Continuous (deriv x) := hx.continuous_deriv (by simp)
  have hyc : Continuous (deriv y) := hy.continuous_deriv (by simp)
  have hx'mono : StrictMonoOn (deriv x) (Icc a b) :=
    strictMonoOn_of_deriv_pos (convex_Icc a b) hxc.continuousOn
      (fun θ hθ => hx'' θ (interior_subset hθ))
  have hx'neg : ∀ θ ∈ Icc a b, θ < θc → deriv x θ < 0 := fun θ hθ h => by
    have := hx'mono hθ ⟨haθ, hθb⟩ h; rwa [hx'c] at this
  have hx'pos : ∀ θ ∈ Icc a b, θc < θ → 0 < deriv x θ := fun θ hθ h => by
    have := hx'mono ⟨haθ, hθb⟩ hθ h; rwa [hx'c] at this
  have hxanti : StrictAntiOn x (Icc a θc) :=
    strictAntiOn_of_deriv_neg (convex_Icc a θc) hx.continuous.continuousOn fun θ hθ => by
      rw [interior_Icc] at hθ; exact hx'neg θ ⟨hθ.1.le, hθ.2.le.trans hθb⟩ hθ.2
  have hxmono : StrictMonoOn x (Icc θc b) :=
    strictMonoOn_of_deriv_pos (convex_Icc θc b) hx.continuous.continuousOn fun θ hθ => by
      rw [interior_Icc] at hθ; exact hx'pos θ ⟨haθ.trans hθ.1.le, hθ.2.le⟩ hθ.1
  have hθ₁ : θ₁ < θc := by
    by_contra hcon
    have hcon' : θc ≤ θ₁ := not_lt.1 hcon
    exact (hxmono ⟨hcon', h₁.2⟩ ⟨hcon'.trans hlt.le, h₂.2⟩ hlt).ne hxeq
  have hθ₂ : θc < θ₂ := by
    by_contra hcon
    have hcon' : θ₂ ≤ θc := not_lt.1 hcon
    exact (hxanti ⟨h₁.1, hlt.le.trans hcon'⟩ ⟨h₂.1, hcon'⟩ hlt).ne' hxeq
  have hbelow : ∀ θ ∈ Ioo θ₁ θ₂, x θ < x θ₁ := by
    intro θ hθ
    rcases le_or_gt θ θc with h | h
    · exact hxanti ⟨h₁.1, hθ₁.le⟩ ⟨h₁.1.trans hθ.1.le, h⟩ hθ.1
    · have := hxmono ⟨h.le, hθ.2.le.trans h₂.2⟩ ⟨hθ₂.le, h₂.2⟩ hθ.2
      rwa [← hxeq] at this
  have hzd : ∀ θ, HasDerivAt z (y θ * deriv x θ) θ := fun θ => by
    rw [← hleg]; exact (hz.differentiable (by simp) θ).hasDerivAt
  have hxd : ∀ θ, HasDerivAt x (deriv x θ) θ := fun θ => (hx.differentiable (by simp) θ).hasDerivAt
  have hyd : ∀ θ, HasDerivAt y (deriv y θ) θ := fun θ => (hy.differentiable (by simp) θ).hasDerivAt
  have hint1 : z θ₂ - z θ₁ = ∫ θ in θ₁..θ₂, y θ * deriv x θ :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hzd θ)
      ((hy.continuous.mul hxc).intervalIntegrable _ _)).symm
  have hibp : ∫ θ in θ₁..θ₂, y θ * deriv x θ =
      y θ₂ * x θ₂ - y θ₁ * x θ₁ - ∫ θ in θ₁..θ₂, deriv y θ * x θ :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun θ _ => hyd θ) (fun θ _ => hxd θ)
      (hyc.intervalIntegrable _ _) (hxc.intervalIntegrable _ _)
  have hint2 : ∫ θ in θ₁..θ₂, deriv y θ * x θ₁ = (y θ₂ - y θ₁) * x θ₁ := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hyd θ) (hyc.intervalIntegrable _ _)]
  have hsub : ∫ θ in θ₁..θ₂, deriv y θ * (x θ₁ - x θ) =
      (∫ θ in θ₁..θ₂, deriv y θ * x θ₁) - ∫ θ in θ₁..θ₂, deriv y θ * x θ := by
    rw [← intervalIntegral.integral_sub]
    · congr 1; funext θ; ring
    · exact (hyc.mul continuous_const).intervalIntegrable _ _
    · exact (hyc.mul hx.continuous).intervalIntegrable _ _
  have hkey : z θ₂ - z θ₁ = ∫ θ in θ₁..θ₂, deriv y θ * (x θ₁ - x θ) := by
    rw [hsub, hint2, hint1, hibp, ← hxeq]; ring
  have hpos : 0 < ∫ θ in θ₁..θ₂, deriv y θ * (x θ₁ - x θ) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((hyc.mul (continuous_const.sub hx.continuous)).intervalIntegrable _ _)
      (fun θ hθ => mul_pos (hy' θ ⟨h₁.1.trans hθ.1.le, hθ.2.le.trans h₂.2⟩)
        (sub_pos.2 (hbelow θ hθ))) hlt
  intro hzeq
  rw [hzeq, sub_self] at hkey
  linarith

/-- Local injectivity of the front of a Legendrian arc through a simple cusp, all sign cases. -/
lemma gp5_cusp_arc_injective {x y z : ℝ → ℝ} {a b θc : ℝ} (haθ : a ≤ θc) (hθb : θc ≤ b)
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) (hz : ContDiff ℝ ∞ z)
    (hleg : ∀ θ, deriv z θ = y θ * deriv x θ) (hx'c : deriv x θc = 0)
    (hx'' : (∀ θ ∈ Icc a b, 0 < deriv (deriv x) θ) ∨ (∀ θ ∈ Icc a b, deriv (deriv x) θ < 0))
    (hy' : (∀ θ ∈ Icc a b, 0 < deriv y θ) ∨ (∀ θ ∈ Icc a b, deriv y θ < 0)) :
    ∀ θ₁ ∈ Icc a b, ∀ θ₂ ∈ Icc a b, θ₁ ≠ θ₂ → (x θ₁, z θ₁) ≠ (x θ₂, z θ₂) := by
  have key : ∀ (s t : ℝ), s ≠ 0 → t ≠ 0 →
      (∀ θ ∈ Icc a b, 0 < s * deriv (deriv x) θ) → (∀ θ ∈ Icc a b, 0 < t * deriv y θ) →
      ∀ θ₁ ∈ Icc a b, ∀ θ₂ ∈ Icc a b, θ₁ ≠ θ₂ → (x θ₁, z θ₁) ≠ (x θ₂, z θ₂) := by
    intro s t hs0 ht0 hsx hty θ₁ h₁ θ₂ h₂ hne
    have hx1 : ContDiff ℝ ∞ (fun θ => s * x θ) := contDiff_const.mul hx
    have hy1 : ContDiff ℝ ∞ (fun θ => t * y θ) := contDiff_const.mul hy
    have hz1 : ContDiff ℝ ∞ (fun θ => (s * t) * z θ) := contDiff_const.mul hz
    have hdx : deriv (fun θ => s * x θ) = fun θ => s * deriv x θ :=
      funext fun θ => deriv_const_mul_field s
    have hdy : deriv (fun θ => t * y θ) = fun θ => t * deriv y θ :=
      funext fun θ => deriv_const_mul_field t
    have hdz : deriv (fun θ => (s * t) * z θ) = fun θ => (s * t) * deriv z θ :=
      funext fun θ => deriv_const_mul_field _
    have hleg1 : ∀ θ, deriv (fun θ => (s * t) * z θ) θ = (t * y θ) * deriv (fun θ => s * x θ) θ := by
      intro θ; rw [hdz, hdx]
      show s * t * deriv z θ = t * y θ * (s * deriv x θ)
      rw [hleg θ]; ring
    have hx'c1 : deriv (fun θ => s * x θ) θc = 0 := by
      rw [hdx]; show s * deriv x θc = 0; rw [hx'c, mul_zero]
    have hx''1 : ∀ θ ∈ Icc a b, 0 < deriv (deriv (fun θ => s * x θ)) θ := by
      intro θ hθ; rw [hdx, deriv_const_mul_field]; exact hsx θ hθ
    have hy'1 : ∀ θ ∈ Icc a b, 0 < deriv (fun θ => t * y θ) θ := by
      intro θ hθ; rw [hdy]; exact hty θ hθ
    intro heq
    have hxeq := (Prod.mk.inj heq).1
    have hzeq := (Prod.mk.inj heq).2
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact gp5_cusp_arc_injective_pos haθ hθb hx1 hy1 hz1 hleg1 hx'c1 hx''1 hy'1 θ₁ h₁ θ₂ h₂ hlt
        (by rw [hxeq]) (by rw [hzeq])
    · exact gp5_cusp_arc_injective_pos haθ hθb hx1 hy1 hz1 hleg1 hx'c1 hx''1 hy'1 θ₂ h₂ θ₁ h₁ hlt
        (by rw [hxeq]) (by rw [hzeq])
  rcases hx'' with hx'' | hx'' <;> rcases hy' with hy' | hy'
  · exact key 1 1 one_ne_zero one_ne_zero (fun θ hθ => by linarith [hx'' θ hθ])
      (fun θ hθ => by linarith [hy' θ hθ])
  · exact key 1 (-1) one_ne_zero (by norm_num) (fun θ hθ => by linarith [hx'' θ hθ])
      (fun θ hθ => by linarith [hy' θ hθ])
  · exact key (-1) 1 (by norm_num) one_ne_zero (fun θ hθ => by linarith [hx'' θ hθ])
      (fun θ hθ => by linarith [hy' θ hθ])
  · exact key (-1) (-1) (by norm_num) (by norm_num) (fun θ hθ => by linarith [hx'' θ hθ])
      (fun θ hθ => by linarith [hy' θ hθ])


/-- `circDist` is at most the plain distance. -/
lemma gp5_circDist_le_abs (θ η : ℝ) : circDist θ η ≤ |θ - η| := by
  simp only [circDist]
  have h2π : 0 < 2 * π := by positivity
  have key : θ - η - 2 * π * round ((θ - η) / (2 * π)) =
      2 * π * ((θ - η) / (2 * π) - round ((θ - η) / (2 * π))) := by
    rw [mul_sub, mul_div_cancel₀ _ h2π.ne']
  rw [key, abs_mul, abs_of_pos h2π]
  have hround : ∀ x : ℝ, |x - round x| ≤ |x| := by
    intro x
    rcases lt_or_ge |x| (1 / 2) with h | h
    · have h' := abs_lt.1 h
      have : round x = 0 := round_eq_zero_iff.2 ⟨h'.1.le, h'.2⟩
      rw [this]; simp
    · exact (abs_sub_round x).trans h
  calc 2 * π * |(θ - η) / (2 * π) - round ((θ - η) / (2 * π))|
      ≤ 2 * π * |(θ - η) / (2 * π)| := mul_le_mul_of_nonneg_left (hround _) h2π.le
    _ = |θ - η| := by rw [abs_div, abs_of_pos h2π, mul_div_cancel₀ _ h2π.ne']

/-- Shifting the first argument by `2πk` does not change `circDist`. -/
lemma gp5_circDist_shift_left (θ η : ℝ) (k : ℤ) : circDist (θ + 2 * π * k) η = circDist θ η := by
  simp only [circDist]
  have h2π : (2 * π) ≠ 0 := by positivity
  have : (θ + 2 * π * k - η) / (2 * π) = (θ - η) / (2 * π) + k := by field_simp; ring
  rw [this, round_add_intCast]
  congr 1; push_cast; ring

/-- Parameters whose difference lies in `[δ, 2π − δ]` (`0 < δ`) are not the same circle point. -/
lemma gp5_not_sameParam_of_bounds {a b δ : ℝ} (hδ : 0 < δ) (h1 : δ ≤ |a - b|)
    (h2 : |a - b| ≤ 2 * π - δ) : ¬ SameParam a b := by
  rintro ⟨k, hk⟩
  rw [hk, show a - (a + 2 * π * k) = -(2 * π * k) by ring, abs_neg, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at h1 h2
  rcases eq_or_ne k 0 with hk0 | hk0
  · rw [hk0] at h1; simp at h1; linarith
  · have h3 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith

/-- The front difference is bounded by the point difference. -/
lemma gp5_front_sub_norm_le (L L' : ℝ → ℝ³) (θ η : ℝ) :
    ‖front L θ - front L' η‖ ≤ ‖L θ - L' η‖ := by
  simp only [front, Prod.mk_sub_mk, Prod.norm_def]
  apply max_le
  · have := PiLp.norm_apply_le (L θ - L' η) 0; rwa [PiLp.sub_apply] at this
  · have := PiLp.norm_apply_le (L θ - L' η) 2; rwa [PiLp.sub_apply] at this

lemma gp5_front_comp_close {L : ℝ → ℝ³} {Ψ : ℝ³ → ℝ³} {η : ℝ} (hC0 : ∀ p, ‖Ψ p - p‖ ≤ η) (θ : ℝ) :
    ‖front (Ψ ∘ L) θ - front L θ‖ ≤ η :=
  (gp5_front_sub_norm_le (Ψ ∘ L) L θ θ).trans (hC0 (L θ))

lemma gp5_front_periodic {L : ℝ → ℝ³} (hL : Periodic L (2 * π)) : Periodic (front L) (2 * π) :=
  fun θ => by simp [front, hL θ]

lemma gp5_continuous_front {L : ℝ → ℝ³} (hL : Continuous L) : Continuous (front L) :=
  ((ContactMotions.contDiff_coord 0).continuous.comp hL).prodMk
    ((ContactMotions.contDiff_coord 2).continuous.comp hL)

/-- Embeddedness margin: a point of the curve within `rc` of the cusp point `L θc` comes from a
parameter within `ρ` of `θc` modulo `2π`. -/
lemma gp5_exists_rc {L : ℝ → ℝ³} (hL : IsEmbeddedCircle L) (S : Finset ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hρπ : ρ ≤ π) :
    ∃ rc > 0, ∀ θc ∈ S, ∀ θ, dist (L θ) (L θc) ≤ rc → ∃ k : ℤ, |θ - 2 * π * k - θc| < ρ := by
  have hmin : ∀ θc ∈ S, ∃ r > 0, ∀ θ ∈ Icc (θc + ρ) (θc + 2 * π - ρ), r ≤ dist (L θ) (L θc) := by
    intro θc _
    rcases (Icc (θc + ρ) (θc + 2 * π - ρ)).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun θ hθ => by rw [he] at hθ; exact absurd hθ (Set.notMem_empty θ)⟩
    · obtain ⟨θ₀, hθ₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne
        (hL.smooth.continuous.dist continuous_const).continuousOn
      refine ⟨dist (L θ₀) (L θc), ?_, fun θ hθ => hmin hθ⟩
      show 0 < dist (L θ₀) (L θc)
      rw [dist_pos]
      intro heq
      have hsp : SameParam θ₀ θc := hL.injective θ₀ θc heq
      refine gp5_not_sameParam_of_bounds hρ ?_ ?_ hsp
      · rw [abs_of_nonneg (by linarith [hθ₀.1])]; linarith [hθ₀.1]
      · rw [abs_of_nonneg (by linarith [hθ₀.1])]; linarith [hθ₀.2]
  choose! r hr using hmin
  obtain ⟨rc, hrc, hrcle⟩ := gp5_finset_min S r (fun j hj => (hr j hj).1)
  refine ⟨rc / 2, by linarith, fun θc hθc θ hθ => ?_⟩
  obtain ⟨k, hk⟩ := gp5_reduce (θc - ρ) θ
  refine ⟨k, ?_⟩
  by_contra hcon
  have hcon' : ρ ≤ |θ - 2 * π * k - θc| := not_lt.1 hcon
  have hLper : ∀ j : ℤ, L (θ - 2 * π * j) = L θ := fun j => by
    rw [show θ - 2 * π * j = θ - j * (2 * π) by ring]; exact hL.periodic.sub_int_mul_eq j
  -- a far representative: either `θ − 2πk` itself or, at the left endpoint, `θ − 2π(k − 1)`
  have hfar : ∃ θ', θ' ∈ Icc (θc + ρ) (θc + 2 * π - ρ) ∧ L θ' = L θ := by
    rcases le_or_gt 0 (θ - 2 * π * k - θc) with h | h
    · rw [abs_of_nonneg h] at hcon'
      exact ⟨θ - 2 * π * k, ⟨by linarith, by linarith [hk.2]⟩, hLper k⟩
    · rw [abs_of_neg h] at hcon'
      have heq : θ - 2 * π * k = θc - ρ := by linarith [hk.1]
      refine ⟨θ - 2 * π * (k - 1 : ℤ), ⟨?_, ?_⟩, hLper (k - 1)⟩
      · push_cast; linarith [Real.pi_pos]
      · push_cast; linarith
  obtain ⟨θ', hθ', hLθ'⟩ := hfar
  have := (hr θc hθc).2 _ hθ'
  rw [hLθ'] at this
  linarith [hrcle θc hθc]

/-- The margin of `NoCuspOnBranch` on the far interval `[θc + δ, θc + 2π − δ]`. -/
lemma gp5_cusp_margin {L : ℝ → ℝ³} (hL : IsEmbeddedCircle L) (hno : NoCuspOnBranch L) {θc : ℝ}
    (hθc : θc ∈ cuspSet L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m > 0, ∀ η ∈ Icc (θc + δ) (θc + 2 * π - δ), m ≤ ‖front L η - front L θc‖ := by
  rcases (Icc (θc + δ) (θc + 2 * π - δ)).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun η hη => by rw [he] at hη; exact absurd hη (Set.notMem_empty η)⟩
  · have hcont : Continuous fun η => ‖front L η - front L θc‖ :=
      ((gp5_continuous_front hL.smooth.continuous).sub continuous_const).norm
    obtain ⟨η₀, hη₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont.continuousOn
    refine ⟨_, ?_, fun η hη => hmin hη⟩
    show 0 < ‖front L η₀ - front L θc‖
    rw [norm_pos_iff, sub_ne_zero]
    apply hno θc hθc η₀
    refine gp5_not_sameParam_of_bounds hδ ?_ ?_
    · rw [abs_of_nonpos (by linarith [hη₀.1])]; linarith [hη₀.1]
    · rw [abs_of_nonpos (by linarith [hη₀.1])]; linarith [hη₀.2]

/-- The margin of `NoTriple` on the compact set of triples in one period with pairwise
differences in `[δ, 2π − δ]`. -/
lemma gp5_triple_margin {L : ℝ → ℝ³} (hL : IsEmbeddedCircle L) (hno : NoTriple L) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ m > 0, ∀ θ η τ : ℝ, θ ∈ Icc 0 (2 * π) → η ∈ Icc 0 (2 * π) → τ ∈ Icc 0 (2 * π) →
      δ ≤ |θ - η| → |θ - η| ≤ 2 * π - δ → δ ≤ |θ - τ| → |θ - τ| ≤ 2 * π - δ →
      δ ≤ |η - τ| → |η - τ| ≤ 2 * π - δ →
      m ≤ ‖front L θ - front L η‖ + ‖front L θ - front L τ‖ := by
  set T : Set (ℝ × ℝ × ℝ) := {v | v.1 ∈ Icc 0 (2 * π) ∧ v.2.1 ∈ Icc 0 (2 * π) ∧
    v.2.2 ∈ Icc 0 (2 * π) ∧ δ ≤ |v.1 - v.2.1| ∧ |v.1 - v.2.1| ≤ 2 * π - δ ∧ δ ≤ |v.1 - v.2.2| ∧
    |v.1 - v.2.2| ≤ 2 * π - δ ∧ δ ≤ |v.2.1 - v.2.2| ∧ |v.2.1 - v.2.2| ≤ 2 * π - δ} with hT
  have c1 : Continuous fun v : ℝ × ℝ × ℝ => v.1 := continuous_fst
  have c2 : Continuous fun v : ℝ × ℝ × ℝ => v.2.1 := continuous_snd.fst
  have c3 : Continuous fun v : ℝ × ℝ × ℝ => v.2.2 := continuous_snd.snd
  have hTc : IsCompact T := by
    have hK : IsCompact (Icc (0 : ℝ) (2 * π) ×ˢ (Icc (0 : ℝ) (2 * π) ×ˢ Icc (0 : ℝ) (2 * π))) :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    refine hK.of_isClosed_subset ?_ ?_
    · simp only [hT, Set.ofPred_and]
      refine IsClosed.inter (isClosed_Icc.preimage c1) (IsClosed.inter (isClosed_Icc.preimage c2)
        (IsClosed.inter (isClosed_Icc.preimage c3) (IsClosed.inter (isClosed_le continuous_const
        (c1.sub c2).abs) (IsClosed.inter (isClosed_le (c1.sub c2).abs continuous_const)
        (IsClosed.inter (isClosed_le continuous_const (c1.sub c3).abs) (IsClosed.inter (isClosed_le
        (c1.sub c3).abs continuous_const) (IsClosed.inter (isClosed_le continuous_const
        (c2.sub c3).abs) (isClosed_le (c2.sub c3).abs continuous_const))))))))
    · intro v hv; exact ⟨hv.1, hv.2.1, hv.2.2.1⟩
  have hmemT : ∀ θ η τ : ℝ, θ ∈ Icc 0 (2 * π) → η ∈ Icc 0 (2 * π) → τ ∈ Icc 0 (2 * π) →
      δ ≤ |θ - η| → |θ - η| ≤ 2 * π - δ → δ ≤ |θ - τ| → |θ - τ| ≤ 2 * π - δ →
      δ ≤ |η - τ| → |η - τ| ≤ 2 * π - δ → (θ, η, τ) ∈ T :=
    fun θ η τ h1 h2 h3 h4 h5 h6 h7 h8 h9 => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  rcases T.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun θ η τ h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_⟩
    have := hmemT θ η τ h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [he] at this; exact absurd this (Set.notMem_empty _)
  · have hF : Continuous (front L) := gp5_continuous_front hL.smooth.continuous
    have hcont : Continuous fun v : ℝ × ℝ × ℝ =>
        ‖front L v.1 - front L v.2.1‖ + ‖front L v.1 - front L v.2.2‖ :=
      (((hF.comp c1).sub (hF.comp c2)).norm).add (((hF.comp c1).sub (hF.comp c3)).norm)
    obtain ⟨v₀, hv₀, hmin⟩ := hTc.exists_isMinOn hne hcont.continuousOn
    refine ⟨_, ?_, fun θ η τ h1 h2 h3 h4 h5 h6 h7 h8 h9 => hmin (hmemT θ η τ h1 h2 h3 h4 h5 h6 h7 h8 h9)⟩
    by_contra hle
    have hle' : ‖front L v₀.1 - front L v₀.2.1‖ + ‖front L v₀.1 - front L v₀.2.2‖ ≤ 0 := not_lt.1 hle
    have hn1 := norm_nonneg (front L v₀.1 - front L v₀.2.1)
    have hn2 := norm_nonneg (front L v₀.1 - front L v₀.2.2)
    have h1 : front L v₀.1 = front L v₀.2.1 := by
      rw [← sub_eq_zero]; exact norm_eq_zero.1 (by linarith)
    have h2 : front L v₀.1 = front L v₀.2.2 := by
      rw [← sub_eq_zero]; exact norm_eq_zero.1 (by linarith)
    obtain ⟨-, -, -, hb1, hb2, hb3, hb4, hb5, hb6⟩ := hv₀
    exact hno v₀.1 v₀.2.1 v₀.2.2 (gp5_not_sameParam_of_bounds hδ hb1 hb2)
      (gp5_not_sameParam_of_bounds hδ hb3 hb4) (gp5_not_sameParam_of_bounds hδ hb5 hb6) ⟨h1, h2⟩

/-- Every cusp of a periodic curve is a cusp in `[0, 2π)` shifted by a period. -/
lemma gp5_cusp_reduce {L : ℝ → ℝ³} (hper : Periodic L (2 * π)) {θ : ℝ} (hθ : θ ∈ cuspSet L) :
    ∃ θc ∈ cuspSet L ∩ Ico 0 (2 * π), ∃ k : ℤ, θ = θc + 2 * π * k := by
  obtain ⟨k, hk⟩ := gp5_reduce 0 θ
  rw [zero_add] at hk
  refine ⟨θ - 2 * π * k, ⟨?_, hk⟩, k, by ring⟩
  have hx : Periodic (deriv (coordX L)) (2 * π) :=
    gp5_periodic_deriv (fun t => by simp [coordX, hper t])
  show deriv (coordX L) (θ - 2 * π * k) = 0
  rw [show θ - 2 * π * k = θ + 2 * π * (-k : ℤ) by push_cast; ring, gp5_periodic_int hx]
  exact hθ

/-- Where the curve stays away from all cusp points, `Ψ ∘ L` agrees with `L` near `θ`. -/
lemma gp5_eventuallyEq_of_far {L : ℝ → ℝ³} (hL : Continuous L) {Ψ : ℝ³ → ℝ³} (S : Finset ℝ)
    {rc : ℝ} (hfix : ∀ p, (∀ θc ∈ S, rc ≤ dist p (L θc)) → Ψ p = p) {θ : ℝ}
    (hfar : ∀ θc ∈ S, rc < dist (L θ) (L θc)) : (Ψ ∘ L) =ᶠ[𝓝 θ] L := by
  have hU : IsOpen (⋂ θc ∈ S, {p : ℝ³ | rc < dist p (L θc)}) :=
    isOpen_biInter_finset fun θc _ =>
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have hmem : L θ ∈ ⋂ θc ∈ S, {p : ℝ³ | rc < dist p (L θc)} := by
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]; exact fun θc hθc => hfar θc hθc
  have hnhds : L ⁻¹' (⋂ θc ∈ S, {p : ℝ³ | rc < dist p (L θc)}) ∈ 𝓝 θ :=
    hL.continuousAt.preimage_mem_nhds (hU.mem_nhds hmem)
  filter_upwards [hnhds] with t ht
  simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq] at ht
  exact hfix (L t) fun θc hθc => (ht θc hθc).le

lemma gp5_deriv_eq_of_eventuallyEq {f g : ℝ → ℝ³} {θ : ℝ} (h : f =ᶠ[𝓝 θ] g) :
    deriv (coordX f) θ = deriv (coordX g) θ ∧
    deriv (deriv (coordX f)) θ = deriv (deriv (coordX g)) θ := by
  have h1 : coordX f =ᶠ[𝓝 θ] coordX g := h.fun_comp (fun p : ℝ³ => p 0)
  exact ⟨h1.deriv_eq, h1.deriv.deriv_eq⟩

/-- Sign transfer: if `|g − g θc| ≤ |g θc|/2` and `|g' − g| ≤ |g θc|/4` on `A`, then `g'` has the
sign of `g θc` on `A`. -/
lemma gp5_sign_transfer {g g' : ℝ → ℝ} {A : Set ℝ} {θc : ℝ} (hc : g θc ≠ 0)
    (h1 : ∀ θ ∈ A, |g θ - g θc| ≤ |g θc| / 2) (h2 : ∀ θ ∈ A, |g' θ - g θ| ≤ |g θc| / 4) :
    (∀ θ ∈ A, 0 < g' θ) ∨ (∀ θ ∈ A, g' θ < 0) := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · right; intro θ hθ
    have ha := abs_le.1 (h1 θ hθ); have hb := abs_le.1 (h2 θ hθ)
    rw [abs_of_neg hneg] at ha hb
    linarith [ha.2, hb.2]
  · left; intro θ hθ
    have ha := abs_le.1 (h1 θ hθ); have hb := abs_le.1 (h2 θ hθ)
    rw [abs_of_pos hpos] at ha hb
    linarith [ha.1, hb.1]

/-- A continuous `g` with `g θc ≠ 0` stays within `|g θc|/2` of `g θc` on a small closed
interval about `θc`. -/
lemma gp5_exists_arc {g : ℝ → ℝ} (hg : Continuous g) (θc : ℝ) (hc : g θc ≠ 0) :
    ∃ ρ > 0, ∀ θ ∈ Icc (θc - ρ) (θc + ρ), |g θ - g θc| ≤ |g θc| / 2 := by
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hg.continuousAt (|g θc| / 2) (by positivity)
  refine ⟨δ / 2, by linarith, fun θ hθ => ?_⟩
  have hd : dist θ θc < δ := by
    rw [Real.dist_eq]
    have : |θ - θc| ≤ δ / 2 := abs_sub_le_iff.2 ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    linarith
  have := hδ' hd
  rw [Real.dist_eq] at this
  exact this.le

/-- The collar of the perturbed curve, of width `min δc ρ`. -/
lemma gp5_new_collar {L L' : ℝ → ℝ³} (hper : Periodic L' (2 * π)) (S : Finset ℝ) {ρ δc rc : ℝ}
    (hρ : 0 < ρ) (hcol : LocallyInjectiveFront L δc)
    (hfix : ∀ θ, (∀ θc ∈ S, rc < dist (L θ) (L θc)) → L' θ = L θ)
    (hrc : ∀ θc ∈ S, ∀ θ, dist (L θ) (L θc) ≤ rc → ∃ k : ℤ, |θ - 2 * π * k - θc| < ρ)
    (harc : ∀ θc ∈ S, ∀ θ₁ ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ), ∀ θ₂ ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ),
      θ₁ ≠ θ₂ → front L' θ₁ ≠ front L' θ₂) :
    LocallyInjectiveFront L' (min δc ρ) := by
  refine ⟨lt_min hcol.1 hρ, fun θ η hd hns => ?_⟩
  have hfper := gp5_front_periodic hper
  have hfrontper : ∀ t (k : ℤ), front L' (t - 2 * π * k) = front L' t := fun t k => by
    rw [show t - 2 * π * k = t + 2 * π * (-k : ℤ) by push_cast; ring]
    exact gp5_periodic_int hfper t (-k)
  set r := round ((θ - η) / (2 * π)) with hr
  set η' := η + 2 * π * r with hη'
  have hd' : |θ - η'| < min δc ρ := by rw [hη', ← gp5_circDist_eq_abs]; exact hd
  have hns' : ¬ SameParam θ η' := by rwa [hη', gp5_sameParam_shift]
  have hfront : front L' η' = front L' η := by rw [hη']; exact gp5_periodic_int hfper η r
  have hne : θ ≠ η' := fun h => hns' ⟨0, by rw [h]; simp⟩
  have hdρ := abs_lt.1 (hd'.trans_le (min_le_right _ _))
  rw [← hfront]
  by_cases hA : ∃ θc ∈ S, dist (L θ) (L θc) ≤ rc
  · obtain ⟨θc, hθc, hdist⟩ := hA
    obtain ⟨k, hk⟩ := hrc θc hθc θ hdist
    have hk' := abs_lt.1 hk
    have h1 : θ - 2 * π * k ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ) := ⟨by linarith, by linarith⟩
    have h2 : η' - 2 * π * k ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ) := ⟨by linarith, by linarith⟩
    have hne' : θ - 2 * π * k ≠ η' - 2 * π * k := fun h => hne (by linarith)
    have := harc θc hθc _ h1 _ h2 hne'
    rwa [hfrontper, hfrontper] at this
  · by_cases hB : ∃ θc ∈ S, dist (L η') (L θc) ≤ rc
    · obtain ⟨θc, hθc, hdist⟩ := hB
      obtain ⟨k, hk⟩ := hrc θc hθc η' hdist
      have hk' := abs_lt.1 hk
      have h2 : η' - 2 * π * k ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ) := ⟨by linarith, by linarith⟩
      have h1 : θ - 2 * π * k ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ) := ⟨by linarith, by linarith⟩
      have hne' : θ - 2 * π * k ≠ η' - 2 * π * k := fun h => hne (by linarith)
      have := harc θc hθc _ h1 _ h2 hne'
      rwa [hfrontper, hfrontper] at this
    · push Not at hA hB
      have e1 : front L' θ = front L θ := by simp [front, hfix θ hA]
      have e2 : front L' η' = front L η' := by simp [front, hfix η' hB]
      rw [e1, e2]
      refine hcol.2 θ η' ?_ hns'
      rw [hη', gp5_circDist_shift]
      exact hd.trans_le (min_le_left _ _)

/-- `NoCuspOnBranch` for the perturbed curve. -/
lemma gp5_new_noCuspOnBranch {L L' : ℝ → ℝ³} (hper : Periodic L' (2 * π)) (S : Finset ℝ)
    {δ' m η₀ : ℝ} (hcuspS : ∀ θ ∈ cuspSet L', ∃ θc ∈ S, ∃ k : ℤ, θ = θc + 2 * π * k)
    (hcol' : LocallyInjectiveFront L' δ')
    (hmargin : ∀ θc ∈ S, ∀ η ∈ Icc (θc + δ') (θc + 2 * π - δ'), m ≤ ‖front L η - front L θc‖)
    (hC0 : ∀ θ, ‖front L' θ - front L θ‖ ≤ η₀) (h2 : 2 * η₀ < m) : NoCuspOnBranch L' := by
  intro θ hθ η hns heq
  have hfper := gp5_front_periodic hper
  obtain ⟨θc, hθc, k, hk⟩ := hcuspS θ hθ
  have hfrontθ : front L' θ = front L' θc := by rw [hk]; exact gp5_periodic_int hfper θc k
  have hns' : ¬ SameParam θc η := by
    rintro ⟨k', hk'⟩
    exact hns ⟨k' - k, by rw [hk', hk]; push_cast; ring⟩
  rw [hfrontθ] at heq
  by_cases hd : circDist θc η < δ'
  · exact hcol'.2 θc η hd hns' heq.symm
  · obtain ⟨j, hj⟩ := gp5_reduce (θc + δ') η
    have hfrontη : front L' (η - 2 * π * j) = front L' η := by
      rw [show η - 2 * π * j = η + 2 * π * (-j : ℤ) by push_cast; ring]
      exact gp5_periodic_int hfper η (-j)
    by_cases hfar : η - 2 * π * j ≤ θc + 2 * π - δ'
    · have hm := hmargin θc hθc (η - 2 * π * j) ⟨hj.1, hfar⟩
      have : ‖front L (η - 2 * π * j) - front L θc‖ ≤ 2 * η₀ := by
        calc ‖front L (η - 2 * π * j) - front L θc‖
            = ‖(front L (η - 2 * π * j) - front L' (η - 2 * π * j)) +
                (front L' θc - front L θc)‖ := by
              rw [hfrontη, heq]; congr 1; abel
          _ ≤ ‖front L (η - 2 * π * j) - front L' (η - 2 * π * j)‖ +
                ‖front L' θc - front L θc‖ := norm_add_le _ _
          _ ≤ η₀ + η₀ := by
              gcongr
              · rw [norm_sub_rev]; exact hC0 _
              · exact hC0 _
          _ = 2 * η₀ := by ring
      linarith
    · push Not at hfar
      apply hd
      have : circDist θc η = circDist θc (η - 2 * π * j - 2 * π) := by
        rw [show η - 2 * π * j - 2 * π = η + 2 * π * ((-j - 1 : ℤ) : ℝ) by push_cast; ring,
          gp5_circDist_shift]
      rw [this]
      refine (gp5_circDist_le_abs _ _).trans_lt ?_
      rw [abs_lt]; constructor <;> linarith [hj.2]

/-- `NoTriple` for the perturbed curve. -/
lemma gp5_new_noTriple {L L' : ℝ → ℝ³} (hper : Periodic L' (2 * π)) {δ' m₃ η₀ : ℝ}
    (hδπ : δ' ≤ π) (hcol' : LocallyInjectiveFront L' δ')
    (hmargin : ∀ θ η τ : ℝ, θ ∈ Icc 0 (2 * π) → η ∈ Icc 0 (2 * π) → τ ∈ Icc 0 (2 * π) →
      δ' ≤ |θ - η| → |θ - η| ≤ 2 * π - δ' → δ' ≤ |θ - τ| → |θ - τ| ≤ 2 * π - δ' →
      δ' ≤ |η - τ| → |η - τ| ≤ 2 * π - δ' →
      m₃ ≤ ‖front L θ - front L η‖ + ‖front L θ - front L τ‖)
    (hC0 : ∀ θ, ‖front L' θ - front L θ‖ ≤ η₀) (h4 : 4 * η₀ < m₃) : NoTriple L' := by
  intro θ η τ hθη hθτ hητ ⟨h1, h2⟩
  by_cases d1 : circDist θ η < δ'
  · exact hcol'.2 θ η d1 hθη h1
  by_cases d2 : circDist θ τ < δ'
  · exact hcol'.2 θ τ d2 hθτ h2
  by_cases d3 : circDist η τ < δ'
  · exact hcol'.2 η τ d3 hητ (h1.symm.trans h2)
  push Not at d1 d2 d3
  have hfper := gp5_front_periodic hper
  obtain ⟨a, ha⟩ := gp5_reduce 0 θ
  obtain ⟨b, hb⟩ := gp5_reduce 0 η
  obtain ⟨c, hc⟩ := gp5_reduce 0 τ
  rw [zero_add] at ha hb hc
  have hsh : ∀ (t : ℝ) (k : ℤ), t - 2 * π * k = t + 2 * π * ((-k : ℤ) : ℝ) := fun t k => by
    push_cast; ring
  have e1 : circDist (θ - 2 * π * a) (η - 2 * π * b) = circDist θ η := by
    rw [hsh, hsh, gp5_circDist_shift_left, gp5_circDist_shift]
  have e2 : circDist (θ - 2 * π * a) (τ - 2 * π * c) = circDist θ τ := by
    rw [hsh, hsh, gp5_circDist_shift_left, gp5_circDist_shift]
  have e3 : circDist (η - 2 * π * b) (τ - 2 * π * c) = circDist η τ := by
    rw [hsh, hsh, gp5_circDist_shift_left, gp5_circDist_shift]
  have b1 := gp5_circDist_bounds ha hb hδπ (by rw [e1]; exact d1)
  have b2 := gp5_circDist_bounds ha hc hδπ (by rw [e2]; exact d2)
  have b3 := gp5_circDist_bounds hb hc hδπ (by rw [e3]; exact d3)
  have hm := hmargin _ _ _ (Ico_subset_Icc_self ha) (Ico_subset_Icc_self hb)
    (Ico_subset_Icc_self hc) b1.1 b1.2 b2.1 b2.2 b3.1 b3.2
  have fper : ∀ (t : ℝ) (k : ℤ), front L' (t - 2 * π * k) = front L' t := fun t k => by
    rw [hsh]; exact gp5_periodic_int hfper t (-k)
  have hpair : ∀ t s : ℝ, front L' t = front L' s → ‖front L t - front L s‖ ≤ 2 * η₀ := by
    intro t s hts
    calc ‖front L t - front L s‖ = ‖(front L t - front L' t) + (front L' s - front L s)‖ := by
          rw [hts]; congr 1; abel
      _ ≤ ‖front L t - front L' t‖ + ‖front L' s - front L s‖ := norm_add_le _ _
      _ ≤ η₀ + η₀ := by
          gcongr
          · rw [norm_sub_rev]; exact hC0 _
          · exact hC0 _
      _ = 2 * η₀ := by ring
  have p1 := hpair (θ - 2 * π * a) (η - 2 * π * b) (by rw [fper, fper]; exact h1)
  have p2 := hpair (θ - 2 * π * a) (τ - 2 * π * c) (by rw [fper, fper]; exact h2)
  linarith

/-- `NoDoubleZero` and the cusp set of the perturbed curve. -/
lemma gp5_new_noDoubleZero_cuspSet {L L' : ℝ → ℝ³} (hL' : ContDiff ℝ ∞ L')
    (hper : Periodic L' (2 * π)) (hperL : Periodic L (2 * π)) (hndz : NoDoubleZero L)
    (S : Finset ℝ) {ρ rc : ℝ} (hSdef : ∀ θ ∈ cuspSet L ∩ Ico 0 (2 * π), θ ∈ S)
    (hS : ∀ θc ∈ S, θc ∈ cuspSet L) (hScusp : ∀ θc ∈ S, deriv (coordX L') θc = 0)
    (hfar : ∀ θ, (∀ θc ∈ S, rc < dist (L θ) (L θc)) → L' =ᶠ[𝓝 θ] L)
    (hrc : ∀ θc ∈ S, ∀ θ, dist (L θ) (L θc) ≤ rc → ∃ k : ℤ, |θ - 2 * π * k - θc| < ρ)
    (harc : ∀ θc ∈ S, (∀ θ ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ), 0 < deriv (deriv (coordX L')) θ) ∨
      (∀ θ ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ), deriv (deriv (coordX L')) θ < 0)) :
    NoDoubleZero L' ∧ cuspSet L' = cuspSet L := by
  have hx' : Periodic (deriv (coordX L')) (2 * π) :=
    gp5_periodic_deriv (fun t => by simp [coordX, hper t])
  have hx'' : Periodic (deriv (deriv (coordX L'))) (2 * π) := gp5_periodic_deriv hx'
  have hxL : Periodic (deriv (coordX L)) (2 * π) :=
    gp5_periodic_deriv (fun t => by simp [coordX, hperL t])
  have hshift : ∀ (f : ℝ → ℝ), Periodic f (2 * π) → ∀ (t : ℝ) (k : ℤ), f (t - 2 * π * k) = f t :=
    fun f hf t k => by
      rw [show t - 2 * π * k = t + 2 * π * ((-k : ℤ) : ℝ) by push_cast; ring]
      exact gp5_periodic_int hf t (-k)
  have hx'c : Continuous (deriv (coordX L')) :=
    ((ContactMotions.contDiff_coord 0).comp hL').continuous_deriv (by simp)
  -- on each arc, `x̃′` is strictly monotone and `x̃″ ≠ 0`
  have harc' : ∀ θc ∈ S, ∀ θ ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ),
      deriv (deriv (coordX L')) θ ≠ 0 ∧ (deriv (coordX L') θ = 0 → θ = θc) := by
    intro θc hθc θ hθ
    have hρ' : θc ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ) := by
      have : 0 ≤ ρ := by linarith [hθ.1, hθ.2]
      constructor <;> linarith
    rcases harc θc hθc with hpos | hneg
    · have hmono : StrictMonoOn (deriv (coordX L')) (Icc (θc - 2 * ρ) (θc + 2 * ρ)) :=
        strictMonoOn_of_deriv_pos (convex_Icc _ _) hx'c.continuousOn
          fun t ht => hpos t (interior_subset ht)
      exact ⟨(hpos θ hθ).ne', fun h0 => hmono.injOn hθ hρ' (by rw [h0, hScusp θc hθc])⟩
    · have hmono : StrictAntiOn (deriv (coordX L')) (Icc (θc - 2 * ρ) (θc + 2 * ρ)) :=
        strictAntiOn_of_deriv_neg (convex_Icc _ _) hx'c.continuousOn
          fun t ht => hneg t (interior_subset ht)
      exact ⟨(hneg θ hθ).ne, fun h0 => hmono.injOn hθ hρ' (by rw [h0, hScusp θc hθc])⟩
  -- the two regimes for a parameter `θ`
  have hcase : ∀ θ, (∃ θc ∈ S, ∃ k : ℤ, θ - 2 * π * k ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ)) ∨
      L' =ᶠ[𝓝 θ] L := by
    intro θ
    by_cases hA : ∃ θc ∈ S, dist (L θ) (L θc) ≤ rc
    · obtain ⟨θc, hθc, hdist⟩ := hA
      obtain ⟨k, hk⟩ := hrc θc hθc θ hdist
      have hk' := abs_lt.1 hk
      have hρ0 : 0 < ρ := by linarith [abs_nonneg (θ - 2 * π * k - θc)]
      exact Or.inl ⟨θc, hθc, k, ⟨by linarith, by linarith⟩⟩
    · push Not at hA
      exact Or.inr (hfar θ hA)
  constructor
  · intro θ
    rcases hcase θ with ⟨θc, hθc, k, hk⟩ | hev
    · right
      rw [← hshift _ hx'' θ k]
      exact (harc' θc hθc _ hk).1
    · obtain ⟨e1, e2⟩ := gp5_deriv_eq_of_eventuallyEq hev
      rw [e1, e2]
      exact hndz θ
  · ext θ
    constructor
    · intro hθ
      rcases hcase θ with ⟨θc, hθc, k, hk⟩ | hev
      · have h0 : deriv (coordX L') (θ - 2 * π * k) = 0 := by rw [hshift _ hx' θ k]; exact hθ
        have := (harc' θc hθc _ hk).2 h0
        have hθc' := hS θc hθc
        show deriv (coordX L) θ = 0
        rw [show θ = θc + 2 * π * k by linarith, gp5_periodic_int hxL]
        exact hθc'
      · obtain ⟨e1, -⟩ := gp5_deriv_eq_of_eventuallyEq hev
        show deriv (coordX L) θ = 0
        rw [← e1]; exact hθ
    · intro hθ
      obtain ⟨θc, hθc, k, hk⟩ := gp5_cusp_reduce hperL hθ
      show deriv (coordX L') θ = 0
      rw [hk, gp5_periodic_int hx']
      exact hScusp θc (hSdef θc hθc)

/-- The perturbed curve is an embedded Legendrian circle. -/
lemma gp5_new_embedded {L : ℝ → ℝ³} (hL : IsEmbeddedCircle L) (hLeg : IsLegendrian L)
    {Ψ : ℝ³ → ℝ³} (hΨ : ContDiff ℝ ∞ Ψ) (hbij : Function.Bijective Ψ)
    (hcontact : ∀ p, ∃ c : ℝ, 0 < c ∧ ∀ v, alpha (Ψ p) (fderiv ℝ Ψ p v) = c * alpha p v)
    (hinj : ∀ p, Function.Injective (fderiv ℝ Ψ p)) :
    IsEmbeddedCircle (Ψ ∘ L) ∧ IsLegendrian (Ψ ∘ L) := by
  have hLd : ∀ θ, HasDerivAt L (deriv L θ) θ := fun θ =>
    (hL.smooth.differentiable (by simp) θ).hasDerivAt
  have hd : ∀ θ, deriv (Ψ ∘ L) θ = fderiv ℝ Ψ (L θ) (deriv L θ) := fun θ =>
    ((hΨ.differentiable (by simp) (L θ)).hasFDerivAt.comp_hasDerivAt θ (hLd θ)).deriv
  refine ⟨⟨hΨ.comp hL.smooth, fun θ => by simp [Function.comp, hL.periodic θ], ?_, ?_⟩, ?_⟩
  · intro θ θ' h
    exact hL.injective θ θ' (hbij.1 h)
  · intro θ h0
    rw [hd] at h0
    have := hinj (L θ) (by rw [h0, map_zero] : fderiv ℝ Ψ (L θ) (deriv L θ) = fderiv ℝ Ψ (L θ) 0)
    exact hL.immersion θ this
  · intro θ
    obtain ⟨c, -, hc⟩ := hcontact (L θ)
    rw [hd, Function.comp_apply, hc, hLeg θ, mul_zero]

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
  -- finite cusp data
  have hfin : (cuspSet L ∩ Ico 0 (2 * π)).Finite := finite_cusps_of_stage1 h.toStage1
  set S : Finset ℝ := hfin.toFinset with hSdef
  have hSmem : ∀ θc, θc ∈ S ↔ θc ∈ cuspSet L ∩ Ico 0 (2 * π) := fun θc => hfin.mem_toFinset
  have hS : ∀ θc ∈ S, θc ∈ cuspSet L := fun θc hθc => ((hSmem θc).1 hθc).1
  have hSdef' : ∀ θ ∈ cuspSet L ∩ Ico 0 (2 * π), θ ∈ S := fun θ hθ => (hSmem θ).2 hθ
  have hL : ContDiff ℝ ∞ L := h.circle.smooth
  have hperL : Periodic L (2 * π) := h.circle.periodic
  have hx : ContDiff ℝ ∞ (coordX L) := (ContactMotions.contDiff_coord 0).comp hL
  have hy : ContDiff ℝ ∞ (coordY L) := (ContactMotions.contDiff_coord 1).comp hL
  have hx''c : Continuous (deriv (deriv (coordX L))) :=
    (hx.iterate_deriv 1).continuous_deriv (by simp)
  have hy'c : Continuous (deriv (coordY L)) := hy.continuous_deriv (by simp)
  have hx''ne : ∀ θc ∈ S, deriv (deriv (coordX L)) θc ≠ 0 := by
    intro θc hθc
    rcases h.noDoubleZero θc with h1 | h1
    · exact absurd (hS θc hθc) h1
    · exact h1
  have hy'ne : ∀ θc ∈ S, deriv (coordY L) θc ≠ 0 := fun θc hθc =>
    deriv_y_ne_zero_at_cusp h.toStage1 (hS θc hθc)
  -- arcs about the cusps on which `x″` and `y′` keep their sign with a margin
  have harcx : ∀ θc ∈ S, ∃ ρ > 0, ∀ θ ∈ Icc (θc - ρ) (θc + ρ),
      |deriv (deriv (coordX L)) θ - deriv (deriv (coordX L)) θc| ≤
        |deriv (deriv (coordX L)) θc| / 2 :=
    fun θc hθc => gp5_exists_arc hx''c θc (hx''ne θc hθc)
  have harcy : ∀ θc ∈ S, ∃ ρ > 0, ∀ θ ∈ Icc (θc - ρ) (θc + ρ),
      |deriv (coordY L) θ - deriv (coordY L) θc| ≤ |deriv (coordY L) θc| / 2 :=
    fun θc hθc => gp5_exists_arc hy'c θc (hy'ne θc hθc)
  choose! ρx hρx using harcx
  choose! ρy hρy using harcy
  obtain ⟨ρ₀, hρ₀, hρ₀le⟩ := gp5_finset_min S (fun j => min (ρx j) (ρy j))
    (fun j hj => lt_min (hρx j hj).1 (hρy j hj).1)
  set ρ : ℝ := min (ρ₀ / 2) (π / 2) with hρdef
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith [Real.pi_pos])
  have hρπ : ρ ≤ π := (min_le_right _ _).trans (by linarith [Real.pi_pos])
  have h2ρ : ∀ j ∈ S, Icc (j - 2 * ρ) (j + 2 * ρ) ⊆ Icc (j - ρx j) (j + ρx j) ∧
      Icc (j - 2 * ρ) (j + 2 * ρ) ⊆ Icc (j - ρy j) (j + ρy j) := by
    intro j hj
    have h0 : ρ₀ ≤ min (ρx j) (ρy j) := hρ₀le j hj
    have hm1 := min_le_left (ρ₀ / 2) (π / 2)
    have hm2 := min_le_left (ρx j) (ρy j)
    have hm3 := min_le_right (ρx j) (ρy j)
    exact ⟨Icc_subset_Icc (by linarith) (by linarith), Icc_subset_Icc (by linarith) (by linarith)⟩
  -- margins of `x″` and `y′` at the cusps
  obtain ⟨mx, hmx, hmxle⟩ := gp5_finset_min S (fun j => |deriv (deriv (coordX L)) j| / 4)
    (fun j hj => by have := hx''ne j hj; positivity)
  obtain ⟨my, hmy, hmyle⟩ := gp5_finset_min S (fun j => |deriv (coordY L) j| / 4)
    (fun j hj => by have := hy'ne j hj; positivity)
  -- bounds on `L′`, `L″`
  have hL'c : Continuous (deriv L) := hL.continuous_deriv (by simp)
  have hL''c : Continuous (deriv (deriv L)) := (hL.iterate_deriv 1).continuous_deriv (by simp)
  obtain ⟨B₁, hB₁0, hB₁⟩ := gp5_bounded_of_periodic hL'c (gp5_periodic_deriv hperL)
  obtain ⟨B₂, hB₂0, hB₂⟩ :=
    gp5_bounded_of_periodic hL''c (gp5_periodic_deriv (gp5_periodic_deriv hperL))
  -- the spatial radius `rc`
  obtain ⟨rc, hrc, hrcP⟩ := gp5_exists_rc h.circle S hρ hρπ
  -- the old collar and the new collar width
  obtain ⟨δc, hδc⟩ := h.collar
  set δ' : ℝ := min δc ρ with hδ'def
  have hδ' : 0 < δ' := lt_min hδc.1 hρ
  have hδ'π : δ' ≤ π := (min_le_right _ _).trans hρπ
  -- front margins
  have hcm : ∀ θc ∈ S, ∃ m > 0, ∀ η ∈ Icc (θc + δ') (θc + 2 * π - δ'),
      m ≤ ‖front L η - front L θc‖ :=
    fun θc hθc => gp5_cusp_margin h.circle h.noCuspOnBranch (hS θc hθc) hδ'
  choose! mc hmc using hcm
  obtain ⟨m₂, hm₂, hm₂le⟩ := gp5_finset_min S mc (fun j hj => (hmc j hj).1)
  obtain ⟨m₃, hm₃, hm₃P⟩ := gp5_triple_margin h.circle h.noTriple hδ'
  -- the `C²`-smallness
  set K : ℝ := B₁ ^ 2 + B₂ + B₁ + 1 with hKdef
  have hK : 0 < K := by positivity
  set η : ℝ := min (min (mx / K) (my / K)) (min (min (m₂ / 4) (m₃ / 8)) (1 / 2)) with hηdef
  have hη : 0 < η := lt_min (lt_min (by positivity) (by positivity))
    (lt_min (lt_min (by positivity) (by positivity)) (by norm_num))
  have hηK1 : η * K ≤ mx := by
    have : η ≤ mx / K := (min_le_left _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ hK] at this
  have hηK2 : η * K ≤ my := by
    have : η ≤ my / K := (min_le_left _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ hK] at this
  have hηm₂ : η ≤ m₂ / 4 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hηm₃ : η ≤ m₃ / 8 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hη1 : η ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η, hη, rc, hrc, ?_⟩
  intro Ψ hΨ hbij hcontact hb hfix hcusp'
  set L' := Ψ ∘ L with hL'def
  have hL' : ContDiff ℝ ∞ L' := hΨ.comp hL
  have hper' : Periodic L' (2 * π) := fun θ => by simp [hL'def, hperL θ]
  have hC0 : ∀ p, ‖Ψ p - p‖ ≤ η := gp5_C0_close hb
  have hfrontC0 : ∀ θ, ‖front L' θ - front L θ‖ ≤ η := gp5_front_comp_close hC0
  -- the fixing hypothesis in terms of `S`
  have hfixS : ∀ p, (∀ θc ∈ S, rc ≤ dist p (L θc)) → Ψ p = p := by
    intro p hp
    apply hfix p
    intro θc hθc
    obtain ⟨θc', hθc', k, hk⟩ := gp5_cusp_reduce hperL hθc
    rw [hk, gp5_periodic_int hperL]
    exact hp θc' (hSdef' θc' hθc')
  have hfixθ : ∀ θ, (∀ θc ∈ S, rc < dist (L θ) (L θc)) → L' θ = L θ := fun θ hθ =>
    hfixS (L θ) fun θc hθc => (hθ θc hθc).le
  have hfar : ∀ θ, (∀ θc ∈ S, rc < dist (L θ) (L θc)) → L' =ᶠ[𝓝 θ] L := fun θ hθ =>
    gp5_eventuallyEq_of_far hL.continuous S hfixS hθ
  -- embedded Legendrian
  have hinj : ∀ p, Function.Injective (fderiv ℝ Ψ p) :=
    gp5_fderiv_injective hΨ (by linarith) hb
  obtain ⟨hcirc', hleg'⟩ := gp5_new_embedded h.circle h.legendrian hΨ hbij hcontact hinj
  -- closeness of the coordinate derivatives
  have hclose : ∀ θ, |deriv (deriv (coordX L')) θ - deriv (deriv (coordX L)) θ| ≤ η * K ∧
      |deriv (coordY L') θ - deriv (coordY L) θ| ≤ η * K := by
    intro θ
    obtain ⟨c1, c2⟩ := gp5_curve_close hL hΨ hb θ
    have e1 := gp5_coord_deriv hL' 0 θ
    have e2 := gp5_coord_deriv hL 0 θ
    have e3 := gp5_coord_deriv hL' 1 θ
    have e4 := gp5_coord_deriv hL 1 θ
    have hsq : ‖deriv L θ‖ ^ 2 ≤ B₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hB₁ θ) 2
    constructor
    · show |deriv (deriv (fun θ => L' θ 0)) θ - deriv (deriv (fun θ => L θ 0)) θ| ≤ η * K
      rw [e1.2, e2.2]
      calc |deriv (deriv L') θ 0 - deriv (deriv L) θ 0|
          = ‖(deriv (deriv L') θ - deriv (deriv L) θ) 0‖ := by
            rw [PiLp.sub_apply, Real.norm_eq_abs]
        _ ≤ ‖deriv (deriv L') θ - deriv (deriv L) θ‖ := PiLp.norm_apply_le _ 0
        _ ≤ η * (‖deriv L θ‖ ^ 2 + ‖deriv (deriv L) θ‖) := c2
        _ ≤ η * K := by
            gcongr
            simp only [hKdef]
            linarith [hB₂ θ]
    · show |deriv (fun θ => L' θ 1) θ - deriv (fun θ => L θ 1) θ| ≤ η * K
      rw [e3.1, e4.1]
      calc |deriv L' θ 1 - deriv L θ 1| = ‖(deriv L' θ - deriv L θ) 1‖ := by
            rw [PiLp.sub_apply, Real.norm_eq_abs]
        _ ≤ ‖deriv L' θ - deriv L θ‖ := PiLp.norm_apply_le _ 1
        _ ≤ η * ‖deriv L θ‖ := c1
        _ ≤ η * K := by
            gcongr
            simp only [hKdef]
            nlinarith [hB₁ θ, sq_nonneg B₁]
  -- arc sign conditions for the new curve
  have harcx' : ∀ θc ∈ S, (∀ θ ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ), 0 < deriv (deriv (coordX L')) θ) ∨
      (∀ θ ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ), deriv (deriv (coordX L')) θ < 0) := by
    intro θc hθc
    refine gp5_sign_transfer (hx''ne θc hθc)
      (fun θ hθ => (hρx θc hθc).2 θ ((h2ρ θc hθc).1 hθ)) (fun θ hθ => ?_)
    refine (hclose θ).1.trans ?_
    have : mx ≤ |deriv (deriv (coordX L)) θc| / 4 := hmxle θc hθc
    linarith
  have harcy' : ∀ θc ∈ S, (∀ θ ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ), 0 < deriv (coordY L') θ) ∨
      (∀ θ ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ), deriv (coordY L') θ < 0) := by
    intro θc hθc
    refine gp5_sign_transfer (hy'ne θc hθc)
      (fun θ hθ => (hρy θc hθc).2 θ ((h2ρ θc hθc).2 hθ)) (fun θ hθ => ?_)
    refine (hclose θ).2.trans ?_
    have : my ≤ |deriv (coordY L) θc| / 4 := hmyle θc hθc
    linarith
  -- `x̃′` vanishes at the cusps
  have hScusp : ∀ θc ∈ S, deriv (coordX L') θc = 0 := fun θc hθc => hcusp' θc (hS θc hθc)
  -- the Legendrian relation in coordinates
  have hlegc : ∀ θ, deriv (coordZ L') θ = coordY L' θ * deriv (coordX L') θ := by
    intro θ
    have hLd : HasDerivAt L' (deriv L' θ) θ := (hL'.differentiable (by simp) θ).hasDerivAt
    have h2 := (ContactMotions.hasDerivAt_coord hLd 2).deriv
    have h0 := (ContactMotions.hasDerivAt_coord hLd 0).deriv
    have hα := hleg' θ
    simp only [alpha] at hα
    show deriv (fun θ => L' θ 2) θ = L' θ 1 * deriv (fun θ => L' θ 0) θ
    rw [h2, h0]; linarith
  -- the front is injective on each arc
  have harcF : ∀ θc ∈ S, ∀ θ₁ ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ),
      ∀ θ₂ ∈ Icc (θc - 2 * ρ) (θc + 2 * ρ), θ₁ ≠ θ₂ → front L' θ₁ ≠ front L' θ₂ := by
    intro θc hθc θ₁ h₁ θ₂ h₂ hne
    exact gp5_cusp_arc_injective (x := coordX L') (y := coordY L') (z := coordZ L')
      (by linarith [hρ] : θc - 2 * ρ ≤ θc) (by linarith [hρ])
      ((ContactMotions.contDiff_coord 0).comp hL') ((ContactMotions.contDiff_coord 1).comp hL')
      ((ContactMotions.contDiff_coord 2).comp hL') hlegc (hScusp θc hθc) (harcx' θc hθc)
      (harcy' θc hθc) θ₁ h₁ θ₂ h₂ hne
  -- the collar of the new curve
  have hcol' : LocallyInjectiveFront L' δ' := gp5_new_collar hper' S hρ hδc hfixθ hrcP harcF
  -- `NoDoubleZero` and the cusp set
  obtain ⟨hndz', hcusp⟩ := gp5_new_noDoubleZero_cuspSet hL' hper' hperL h.noDoubleZero S hSdef' hS
    hScusp hfar hrcP harcx'
  -- `NoCuspOnBranch` and `NoTriple`
  have hcuspS : ∀ θ ∈ cuspSet L', ∃ θc ∈ S, ∃ k : ℤ, θ = θc + 2 * π * k := by
    intro θ hθ
    rw [hcusp] at hθ
    obtain ⟨θc, hθc, k, hk⟩ := gp5_cusp_reduce hperL hθ
    exact ⟨θc, hSdef' θc hθc, k, hk⟩
  have hnc' : NoCuspOnBranch L' := gp5_new_noCuspOnBranch hper' S hcuspS hcol'
    (fun θc hθc η' hη' => (hm₂le θc hθc).trans ((hmc θc hθc).2 η' hη')) hfrontC0 (by linarith)
  have hnt' : NoTriple L' := gp5_new_noTriple hper' hδ'π hcol' hm₃P hfrontC0 (by linarith)
  refine ⟨hcusp, step3 ?_⟩
  exact
    { circle := hcirc'
      legendrian := hleg'
      noDoubleZero := hndz'
      collar := ⟨δ', hcol'⟩
      noCuspOnBranch := hnc'
      noTriple := hnt' }

/-- Fourth-order Taylor bounds for a smooth function vanishing to order `3` at `y₀`. -/
lemma gp5_taylor4 (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (y₀ : ℝ) (h0 : χ y₀ = 0)
    (h1 : deriv χ y₀ = 0) (h2 : deriv^[2] χ y₀ = 0) (h3 : deriv^[3] χ y₀ = 0) :
    ∃ M, 0 ≤ M ∧ ∀ y ∈ Icc (y₀ - 1) (y₀ + 1),
      |χ y| ≤ M * |y - y₀| ^ 4 ∧ |deriv χ y| ≤ M * |y - y₀| ^ 3 := by
  have hχj : ∀ j, ContDiff ℝ ∞ (deriv^[j] χ) := fun j => hχ.iterate_deriv j
  have hdj : ∀ j x, HasDerivAt (deriv^[j] χ) (deriv^[j + 1] χ x) x := fun j x => by
    have h := ((hχj j).differentiable (by simp) x).hasDerivAt
    rw [Function.iterate_succ_apply']; exact h
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := y₀ - 1) (b := y₀ + 1)).exists_bound_of_continuousOn
    (hχj 4).continuous.continuousOn
  set M := max M₀ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hT4 : ∀ x ∈ Icc (y₀ - 1) (y₀ + 1), |deriv^[4] χ x| ≤ M * |x - y₀| ^ 0 := fun x hx => by
    rw [pow_zero, mul_one]
    exact (hM₀ x hx).trans (le_max_left _ _)
  have hT3 := gp5_mvt_step hM (hdj 3) h3 hT4
  have hT2 := gp5_mvt_step hM (hdj 2) h2 hT3
  have hT1 := gp5_mvt_step hM (hdj 1) h1 hT2
  have hT0 := gp5_mvt_step hM (hdj 0) h0 hT1
  exact ⟨M, hM, fun y hy => ⟨hT0 y hy, hT1 y hy⟩⟩

/-- `ψ = cuspHam f y₀ A` is smooth and vanishes to order `3` at `y₀` when `f′(y₀) = 0` and
`f″(y₀) = 2A`. -/
lemma gp5_cuspHam_props (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (y₀ A : ℝ) (hf' : deriv f y₀ = 0)
    (hf'' : deriv (deriv f) y₀ = 2 * A) :
    ContDiff ℝ ∞ (cuspHam f y₀ A) ∧ cuspHam f y₀ A y₀ = 0 ∧ deriv (cuspHam f y₀ A) y₀ = 0 ∧
      deriv (deriv (cuspHam f y₀ A)) y₀ = 0 ∧ deriv (deriv (deriv (cuspHam f y₀ A))) y₀ = 0 := by
  set ψ := cuspHam f y₀ A with hψ
  set g : ℝ → ℝ := fun v => f v - (f y₀ + A * (v - y₀) ^ 2) with hg
  set g₂ : ℝ → ℝ := fun v => deriv f v - 2 * A * (v - y₀) with hg₂
  have hf1 : ∀ v, HasDerivAt f (deriv f v) v := fun v => (hf.differentiable (by simp) v).hasDerivAt
  have hfd2s : ContDiff ℝ ∞ (deriv f) := hf.iterate_deriv 1
  have hf2 : ∀ v, HasDerivAt (deriv f) (deriv (deriv f) v) v := fun v =>
    (hfd2s.differentiable (by simp) v).hasDerivAt
  have hgs : ContDiff ℝ ∞ g :=
    hf.sub (contDiff_const.add (contDiff_const.mul ((contDiff_id.sub contDiff_const).pow 2)))
  have hg₂s : ContDiff ℝ ∞ g₂ := hfd2s.sub (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have hψd : ∀ v, HasDerivAt ψ (g v) v := fun v =>
    intervalIntegral.integral_hasDerivAt_right (hgs.continuous.intervalIntegrable _ _)
      (hgs.continuous.stronglyMeasurableAtFilter _ _) hgs.continuous.continuousAt
  have hψ' : deriv ψ = g := funext fun v => (hψd v).deriv
  have hgd : ∀ v, HasDerivAt g (g₂ v) v := by
    intro v
    have h1 : HasDerivAt (fun v => f y₀ + A * (v - y₀) ^ 2) (A * (2 * (v - y₀))) v := by
      have := (((hasDerivAt_id v).sub_const y₀).pow 2).const_mul A
      refine (this.const_add (f y₀)).congr_deriv ?_
      simp
    refine ((hf1 v).sub h1).congr_deriv ?_
    simp only [hg₂]; ring
  have hg' : deriv g = g₂ := funext fun v => (hgd v).deriv
  have hg₂d : ∀ v, HasDerivAt g₂ (deriv (deriv f) v - 2 * A) v := by
    intro v
    have h1 : HasDerivAt (fun v => 2 * A * (v - y₀)) (2 * A) v := by
      simpa using ((hasDerivAt_id v).sub_const y₀).const_mul (2 * A)
    exact (hf2 v).sub h1
  have hψs : ContDiff ℝ ∞ ψ :=
    contDiff_infty_iff_deriv.2 ⟨fun v => (hψd v).differentiableAt, hψ' ▸ hgs⟩
  refine ⟨hψs, by simp [hψ, cuspHam], by rw [hψ']; simp [hg], by rw [hψ', hg']; simp [hg₂, hf'], ?_⟩
  rw [hψ', hg', (hg₂d y₀).deriv, hf'']; ring

lemma gp5_norm_le_sum_abs (v : ℝ³) : ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  have hv : v = v 0 • ContactMotions.e 0 + v 1 • ContactMotions.e 1 + v 2 • ContactMotions.e 2 := by
    ext i; fin_cases i <;> simp
  have he : ∀ i, ‖ContactMotions.e i‖ = 1 := fun i => by
    rw [ContactMotions.e, PiLp.norm_single, norm_one]
  calc ‖v‖ = ‖v 0 • ContactMotions.e 0 + v 1 • ContactMotions.e 1 + v 2 • ContactMotions.e 2‖ :=
        congrArg norm hv
    _ ≤ ‖v 0 • ContactMotions.e 0 + v 1 • ContactMotions.e 1‖ + ‖v 2 • ContactMotions.e 2‖ :=
        norm_add_le _ _
    _ ≤ ‖v 0 • ContactMotions.e 0‖ + ‖v 1 • ContactMotions.e 1‖ + ‖v 2 • ContactMotions.e 2‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ = |v 0| + |v 1| + |v 2| := by simp only [norm_smul, he, mul_one, Real.norm_eq_abs]

/-- Displacement of the explicit cusp flow on the inner ball: `O(ε³) < ε/8`. -/
lemma gp5_cuspFlow_small {ψ : ℝ → ℝ} {pc : ℝ³} {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hT : ∀ y ∈ Icc (pc 1 - 1) (pc 1 + 1),
      |ψ y| ≤ M * |y - pc 1| ^ 4 ∧ |deriv ψ y| ≤ M * |y - pc 1| ^ 3)
    (hC : (3 + |pc 1|) * M * ε ^ 2 < 8) {q : ℝ³} (hq : q ∈ Metric.ball pc (ε / 4)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : dist (cuspFlowMap ψ s q) q < ε / 8 := by
  have hq1 : |q 1 - pc 1| < ε / 4 := by
    have h := PiLp.norm_apply_le (q - pc) 1
    rw [PiLp.sub_apply, Real.norm_eq_abs, ← dist_eq_norm] at h
    exact h.trans_lt (Metric.mem_ball.1 hq)
  have hqI : q 1 ∈ Icc (pc 1 - 1) (pc 1 + 1) := by
    have := abs_lt.1 hq1; constructor <;> linarith
  obtain ⟨hψ0, hψ1⟩ := hT (q 1) hqI
  have hu : |q 1 - pc 1| ^ 3 ≤ (ε / 4) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hq1.le 3
  have hu4 : |q 1 - pc 1| ^ 4 ≤ (ε / 4) ^ 3 := by
    calc |q 1 - pc 1| ^ 4 = |q 1 - pc 1| ^ 3 * |q 1 - pc 1| := by ring
      _ ≤ (ε / 4) ^ 3 * 1 :=
          mul_le_mul hu (by linarith) (abs_nonneg _) (by positivity)
      _ = (ε / 4) ^ 3 := mul_one _
  have hq1abs : |q 1| ≤ |pc 1| + 1 := by
    calc |q 1| = |(q 1 - pc 1) + pc 1| := by ring_nf
      _ ≤ |q 1 - pc 1| + |pc 1| := abs_add_le _ _
      _ ≤ |pc 1| + 1 := by linarith
  have h0 : (cuspFlowMap ψ s q - q) 0 = -(s * deriv ψ (q 1)) := by
    rw [PiLp.sub_apply]; simp [cuspFlowMap]
  have h1 : (cuspFlowMap ψ s q - q) 1 = 0 := by
    rw [PiLp.sub_apply]; simp [cuspFlowMap]
  have h2 : (cuspFlowMap ψ s q - q) 2 = s * (ψ (q 1) - q 1 * deriv ψ (q 1)) := by
    rw [PiLp.sub_apply]; simp [cuspFlowMap]
  rw [dist_eq_norm]
  refine (gp5_norm_le_sum_abs _).trans_lt ?_
  rw [h0, h1, h2, abs_neg, abs_zero, add_zero, abs_mul, abs_mul, abs_of_nonneg hs.1]
  have hA : |ψ (q 1) - q 1 * deriv ψ (q 1)| ≤ |ψ (q 1)| + |q 1| * |deriv ψ (q 1)| := by
    calc _ ≤ |ψ (q 1)| + |q 1 * deriv ψ (q 1)| := abs_sub _ _
      _ = _ := by rw [abs_mul]
  have e1 : |deriv ψ (q 1)| ≤ M * (ε / 4) ^ 3 := hψ1.trans (mul_le_mul_of_nonneg_left hu hM)
  have e2 : |ψ (q 1)| ≤ M * (ε / 4) ^ 3 := hψ0.trans (mul_le_mul_of_nonneg_left hu4 hM)
  have e3 : |q 1| * |deriv ψ (q 1)| ≤ (|pc 1| + 1) * (M * (ε / 4) ^ 3) :=
    mul_le_mul hq1abs e1 (abs_nonneg _) (by positivity)
  have key : |deriv ψ (q 1)| + (|ψ (q 1)| + |q 1| * |deriv ψ (q 1)|) ≤
      (3 + |pc 1|) * M * (ε / 4) ^ 3 := by linarith
  have hfin : (3 + |pc 1|) * M * (ε / 4) ^ 3 < ε / 8 := by
    have : (3 + |pc 1|) * M * (ε / 4) ^ 3 = ((3 + |pc 1|) * M * ε ^ 2) * (ε / 64) := by ring
    rw [this]
    calc ((3 + |pc 1|) * M * ε ^ 2) * (ε / 64) < 8 * (ε / 64) :=
          mul_lt_mul_of_pos_right hC (by positivity)
      _ = ε / 8 := by ring
  calc s * |deriv ψ (q 1)| + s * |ψ (q 1) - q 1 * deriv ψ (q 1)|
      ≤ 1 * |deriv ψ (q 1)| + 1 * (|ψ (q 1)| + |q 1| * |deriv ψ (q 1)|) :=
        add_le_add (mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _))
          (mul_le_mul hs.2 hA (abs_nonneg _) zero_le_one)
    _ = |deriv ψ (q 1)| + (|ψ (q 1)| + |q 1| * |deriv ψ (q 1)|) := by ring
    _ ≤ (3 + |pc 1|) * M * (ε / 4) ^ 3 := key
    _ < ε / 8 := hfin

lemma gp5_hamVF_congr {H H' : ℝ³ → ℝ} {q : ℝ³} (h : H =ᶠ[𝓝 q] H') : hamVF H q = hamVF H' q := by
  simp only [ContactMotions.hamVF, ContactMotions.pd, h.fderiv_eq, h.eq_of_nhds]

/-- On the inner ball of a cusp cutoff, the flow of `H` is the explicit cusp flow (uniqueness of
solutions of the `X_H`-ODE along the explicit trajectory, which stays where `H = ψ(y)`). -/
lemma gp5_flow_eq_cuspFlow {H : ℝ³ → ℝ} (hH : ContactMotionsHyp H) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {pc : ℝ³} {ε : ℝ} (hHψ : ∀ p ∈ Metric.ball pc (ε / 2), H p = ψ (p 1))
    (hsmall : ∀ q ∈ Metric.ball pc (ε / 4), ∀ s ∈ Icc (0 : ℝ) 1,
      dist (cuspFlowMap ψ s q) q < ε / 8)
    {q : ℝ³} (hq : q ∈ Metric.ball pc (ε / 4)) : hamFlow H 1 q = cuspFlowMap ψ 1 q := by
  obtain ⟨K, hK⟩ := hH.exists_lipschitzWith
  have hflow := hH.isGlobalFlow
  have hγ := gp5_isGlobalFlow_cuspFlowMap ψ hψ
  have hε : 0 < ε := by
    have := Metric.mem_ball.1 hq
    have := dist_nonneg (x := q) (y := pc)
    linarith
  have hin : ∀ s ∈ Icc (0 : ℝ) 1, cuspFlowMap ψ s q ∈ Metric.ball pc (ε / 2) := by
    intro s hs
    have h1 := hsmall q hq s hs
    have h2 := Metric.mem_ball.1 hq
    rw [Metric.mem_ball]
    calc dist (cuspFlowMap ψ s q) pc ≤ dist (cuspFlowMap ψ s q) q + dist q pc := dist_triangle _ _ _
      _ < ε / 8 + ε / 4 := add_lt_add h1 h2
      _ ≤ ε / 2 := by linarith
  have hHeq : ∀ s ∈ Icc (0 : ℝ) 1, H =ᶠ[𝓝 (cuspFlowMap ψ s q)] fun p => ψ (p 1) := fun s hs =>
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (hin s hs)) fun p hp => hHψ p hp
  have hγ' : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s => cuspFlowMap ψ s q) (hamVF H (cuspFlowMap ψ s q)) s := by
    intro s hs
    rw [gp5_hamVF_congr (hHeq s hs)]
    exact hγ.hasDerivAt s q
  have h := dist_le_of_trajectories_ODE (v := fun _ => hamVF H) (fun _ => hK)
    (f := fun s => hamFlow H s q) (g := fun s => cuspFlowMap ψ s q) (a := 0) (b := 1) (δ := 0)
    (hflow.continuous_time q).continuousOn
    (fun t _ => (hflow.hasDerivAt t q).hasDerivWithinAt)
    (fun t ht => (hγ' t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hγ' t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [hflow.zero, hγ.zero]) 1 ⟨zero_le_one, le_rfl⟩
  rw [zero_mul] at h
  exact dist_le_zero.1 h

/-- `X_H` is linear in `H`: the field of a finite sum is the sum of the fields. -/
lemma gp5_hamVF_sum {ι : Type*} [DecidableEq ι] (S : Finset ι) (Hs : ι → ℝ³ → ℝ)
    (hHs : ∀ i ∈ S, ContDiff ℝ ∞ (Hs i)) (p : ℝ³) :
    hamVF (fun q => ∑ i ∈ S, Hs i q) p = ∑ i ∈ S, hamVF (Hs i) p := by
  have hpd : ∀ j, ContactMotions.pd (fun q => ∑ i ∈ S, Hs i q) j p =
      ∑ i ∈ S, ContactMotions.pd (Hs i) j p := by
    intro j
    simp only [ContactMotions.pd]
    have : (fun q => ∑ i ∈ S, Hs i q) = ∑ i ∈ S, Hs i := by funext q; simp
    rw [this, fderiv_sum (fun i hi => ((hHs i hi).differentiable (by simp) p))]
    simp
  have hsum : ∀ (T : Finset ι) (a b c : ι → ℝ),
      ∑ i ∈ T, (!₂[a i, b i, c i] : ℝ³) = !₂[∑ i ∈ T, a i, ∑ i ∈ T, b i, ∑ i ∈ T, c i] := by
    intro T a b c
    induction T using Finset.induction_on with
    | empty => ext k; fin_cases k <;> simp
    | @insert j T hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj, ih]
      ext k; fin_cases k <;> simp
  simp only [ContactMotions.hamVF, hpd]
  rw [hsum]
  congr 1
  ext k
  fin_cases k <;> simp [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_sub_distrib]

/-- `C²`-smallness of a sum of fields with pairwise disjoint supports. -/
lemma gp5_sum_bound {ι : Type*} [DecidableEq ι] (S : Finset ι) (Xs : ι → ℝ³ → ℝ³) (K : ι → Set ℝ³)
    (hXs : ∀ i ∈ S, ContDiff ℝ ∞ (Xs i)) (hsupp : ∀ i ∈ S, tsupport (Xs i) ⊆ K i)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (K i) (K j)) {η : ℝ} (hη : 0 ≤ η)
    (hb : ∀ i ∈ S, ∀ k ≤ 2, ∀ p, ‖iteratedFDeriv ℝ k (Xs i) p‖ ≤ η) (k : ℕ) (hk : k ≤ 2)
    (p : ℝ³) : ‖iteratedFDeriv ℝ k (fun q => ∑ i ∈ S, Xs i q) p‖ ≤ η := by
  rw [iteratedFDeriv_sum (fun j hj => (hXs j hj).of_le (by simp)), Finset.sum_apply]
  by_cases hex : ∃ i₀ ∈ S, p ∈ K i₀
  · obtain ⟨i₀, hi₀, hp⟩ := hex
    rw [Finset.sum_eq_single i₀]
    · exact hb i₀ hi₀ k hk p
    · intro j hj hji
      have : p ∉ tsupport (Xs j) := fun h =>
        Set.disjoint_left.1 (hdisj j hj i₀ hi₀ hji) (hsupp j hj h) hp
      exact Function.notMem_support.1 fun h => this (support_iteratedFDeriv_subset k h)
    · intro h; exact absurd hi₀ h
  · push Not at hex
    rw [Finset.sum_eq_zero, norm_zero]
    · exact hη
    · intro j hj
      have : p ∉ tsupport (Xs j) := fun h => hex j hj (hsupp j hj h)
      exact Function.notMem_support.1 fun h => this (support_iteratedFDeriv_subset k h)

/-- The (topological) support of a finite sum lies in the union of closed supersets of the
supports. -/
lemma gp5_tsupport_sum_subset {ι : Type*} (S : Finset ι) (Hs : ι → ℝ³ → ℝ) (K : ι → Set ℝ³)
    (hK : ∀ i ∈ S, IsClosed (K i)) (hsupp : ∀ i ∈ S, tsupport (Hs i) ⊆ K i) :
    tsupport (fun q => ∑ i ∈ S, Hs i q) ⊆ ⋃ i ∈ S, K i := by
  apply closure_minimal
  · intro q hq
    rw [Function.mem_support] at hq
    by_contra hnot
    apply hq
    apply Finset.sum_eq_zero
    intro i hi
    have : q ∉ K i := fun h => hnot (Set.mem_biUnion hi h)
    exact image_eq_zero_of_notMem_tsupport fun h => this (hsupp i hi h)
  · exact S.finite_toSet.isClosed_biUnion hK

lemma gp5_hamVF_eq_zero_of_notMem {H : ℝ³ → ℝ} {p : ℝ³} (hp : p ∉ tsupport H) : hamVF H p = 0 := by
  have h0 : H p = 0 := image_eq_zero_of_notMem_tsupport hp
  ext i
  fin_cases i <;> simp [ContactMotions.hamVF, ContactMotions.pd_eq_zero_of_notMem hp, h0]

/-- A zero of `X_H` is fixed by the flow. -/
lemma gp5_hamFlow_fixed {H : ℝ³ → ℝ} (hH : ContactMotionsHyp H) {p : ℝ³} (h0 : hamVF H p = 0)
    (s : ℝ) : hamFlow H s p = p := by
  obtain ⟨K, hK⟩ := hH.exists_lipschitzWith
  have := ContactMotions.ODE_unique_global hK (f := fun s => hamFlow H s p) (g := fun _ => p)
    (fun s => hH.isGlobalFlow.hasDerivAt s p)
    (fun s => by
      show HasDerivAt (fun _ => p) (hamVF H p) s
      rw [h0]; exact hasDerivAt_const s p)
    (t₀ := 0) (by simp [hH.hamFlow_zero])
  exact congrFun this s

/-- The exact germ is invariant under shifting the cusp parameter by a period. -/
lemma gp5_germ_shift {L : ℝ → ℝ³} (hper : Periodic L (2 * π)) {θc : ℝ} (k : ℤ)
    (h : IsExactCuspGerm L θc) : IsExactCuspGerm L (θc + 2 * π * k) := by
  obtain ⟨A, hA, hy', ε, hε, hg⟩ := h
  have hX : Periodic (coordX L) (2 * π) := fun t => by simp [coordX, hper t]
  have hY : Periodic (coordY L) (2 * π) := fun t => by simp [coordY, hper t]
  have hZ : Periodic (coordZ L) (2 * π) := fun t => by simp [coordZ, hper t]
  have hY' : Periodic (deriv (coordY L)) (2 * π) := gp5_periodic_deriv hY
  refine ⟨A, hA, by rw [gp5_periodic_int hY']; exact hy', ε, hε, fun θ hθ => ?_⟩
  have hθ' : |θ - 2 * π * k - θc| < ε := by
    rw [show θ - 2 * π * k - θc = θ - (θc + 2 * π * k) by ring]; exact hθ
  obtain ⟨h1, h2⟩ := hg (θ - 2 * π * k) hθ'
  have e : ∀ f : ℝ → ℝ, Periodic f (2 * π) → f (θ - 2 * π * k) = f θ := fun f hf => by
    rw [show θ - 2 * π * k = θ + 2 * π * ((-k : ℤ) : ℝ) by push_cast; ring]
    exact gp5_periodic_int hf θ (-k)
  rw [e _ hX, e _ hY] at h1
  rw [e _ hZ, e _ hY] at h2
  rw [gp5_periodic_int hX, gp5_periodic_int hY, gp5_periodic_int hZ]
  exact ⟨h1, h2⟩

/-- At an exact cusp germ, `x′ = 0`. -/
lemma gp5_deriv_x_zero_of_germ {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) {θc : ℝ}
    (h : IsExactCuspGerm L θc) : deriv (coordX L) θc = 0 := by
  obtain ⟨A, -, -, ε, hε, hg⟩ := h
  have hy : ContDiff ℝ ∞ (coordY L) := (ContactMotions.contDiff_coord 1).comp hL
  have hev : coordX L =ᶠ[𝓝 θc] fun θ => coordX L θc + A * (coordY L θ - coordY L θc) ^ 2 := by
    filter_upwards [Metric.ball_mem_nhds θc hε] with θ hθ
    exact (hg θ (by rwa [Metric.mem_ball, Real.dist_eq] at hθ)).1
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun θ => coordX L θc + A * (coordY L θ - coordY L θc) ^ 2)
      (A * (2 * (coordY L θc - coordY L θc) ^ 1 * deriv (coordY L) θc)) θc := by
    have := ((((hy.differentiable (by simp) θc).hasDerivAt).sub_const (coordY L θc)).pow 2).const_mul A
    exact (this.const_add _).congr_deriv (by simp)
  rw [hd.deriv]; simp

/-- Distinct cusp parameters in one period have distinct cusp points, with a uniform margin. -/
lemma gp5_pairwise_dist {L : ℝ → ℝ³} (hL : IsEmbeddedCircle L) (S : Finset ℝ)
    (hS : ∀ θ ∈ S, θ ∈ Ico 0 (2 * π)) :
    ∃ d > 0, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → d ≤ dist (L a) (L b) := by
  classical
  have hpos : ∀ q ∈ (S ×ˢ S).filter (fun q : ℝ × ℝ => q.1 ≠ q.2), 0 < dist (L q.1) (L q.2) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    rw [dist_pos]
    intro heq
    obtain ⟨k, hk⟩ := hL.injective q.1 q.2 heq
    have h1 := hS q.1 hq.1.1
    have h2 := hS q.2 hq.1.2
    rcases eq_or_ne k 0 with hk0 | hk0
    · rw [hk0] at hk
      simp only [Int.cast_zero, mul_zero, add_zero] at hk
      exact hq.2 hk.symm
    · have h3 : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
      have h4 : |q.2 - q.1| < 2 * π := by
        rw [abs_lt]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      rw [hk, show q.1 + 2 * π * k - q.1 = 2 * π * k by ring, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at h4
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * π)
      linarith
  obtain ⟨d, hd, hdle⟩ := gp5_finset_min ((S ×ˢ S).filter fun q : ℝ × ℝ => q.1 ≠ q.2)
    (fun q => dist (L q.1) (L q.2)) hpos
  refine ⟨d, hd, fun a ha b hb hab => hdle (a, b) ?_⟩
  simp only [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨ha, hb⟩, hab⟩

/-- LEAF P5.7 (assembly of P5.1–P5.6 over the finitely many cusps).  A contact isotopy, product of
the cut-off cusp flows in disjoint balls (P1.3, P1.4, P5.2, P5.4), whose time-one map is `C²`-close
to the identity (P5.5, compositions), fixes the cusp parameters and gives the exact germ at each
cusp (P5.1, P5.3: the inner subarc has displacement `O(ε³)` and never leaves the inner ball), so
`Stage3` persists (P5.6). -/
theorem exists_germ_isotopy {L : ℝ → ℝ³} (h : Stage3 L) :
    ∃ Φ : ℝ → ℝ³ → ℝ³, IsContactIsotopy Φ ∧ Stage3 (Φ 1 ∘ L) ∧
      ∀ θc ∈ cuspSet (Φ 1 ∘ L), IsExactCuspGerm (Φ 1 ∘ L) θc := by
  classical
  -- stability data (P5.6) and the finite cusp set
  obtain ⟨η, hη, rc, hrc, hstab⟩ := stage3_stable h
  have hfin : (cuspSet L ∩ Ico 0 (2 * π)).Finite := finite_cusps_of_stage1 h.toStage1
  set S : Finset ℝ := hfin.toFinset with hSdef
  have hSmem : ∀ θc, θc ∈ S ↔ θc ∈ cuspSet L ∩ Ico 0 (2 * π) := fun θc => hfin.mem_toFinset
  have hS : ∀ θc ∈ S, θc ∈ cuspSet L := fun θc hθc => ((hSmem θc).1 hθc).1
  have hSI : ∀ θc ∈ S, θc ∈ Ico 0 (2 * π) := fun θc hθc => ((hSmem θc).1 hθc).2
  have hL : ContDiff ℝ ∞ L := h.circle.smooth
  have hperL : Periodic L (2 * π) := h.circle.periodic
  -- local graphs at the cusps (P5.2)
  have hgraph : ∀ θc ∈ S, ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ deriv f (coordY L θc) = 0 ∧
      deriv (deriv f) (coordY L θc) ≠ 0 ∧ ∀ᶠ θ in 𝓝 θc, coordX L θ = f (coordY L θ) :=
    fun θc hθc => exists_local_graph h (hS θc hθc)
  choose! f hf using hgraph
  -- the cusp Hamiltonians `ψ_c = cuspHam f_c y_c A_c` and their Taylor constants
  have hA : ∀ θc ∈ S, deriv (deriv (f θc)) (coordY L θc) =
      2 * (deriv (deriv (f θc)) (coordY L θc) / 2) := fun _ _ => by ring
  have hψprops : ∀ θc ∈ S,
      ContDiff ℝ ∞ (cuspHam (f θc) (coordY L θc) (deriv (deriv (f θc)) (coordY L θc) / 2)) ∧
      cuspHam (f θc) (coordY L θc) (deriv (deriv (f θc)) (coordY L θc) / 2) (coordY L θc) = 0 ∧
      deriv (cuspHam (f θc) (coordY L θc) (deriv (deriv (f θc)) (coordY L θc) / 2)) (coordY L θc) = 0 ∧
      deriv (deriv (cuspHam (f θc) (coordY L θc) (deriv (deriv (f θc)) (coordY L θc) / 2)))
        (coordY L θc) = 0 ∧
      deriv (deriv (deriv (cuspHam (f θc) (coordY L θc) (deriv (deriv (f θc)) (coordY L θc) / 2))))
        (coordY L θc) = 0 :=
    fun θc hθc => gp5_cuspHam_props (f θc) (hf θc hθc).1 (coordY L θc) _ (hf θc hθc).2.1 (hA θc hθc)
  have hT : ∀ θc ∈ S, ∃ M, 0 ≤ M ∧ ∀ y ∈ Icc (coordY L θc - 1) (coordY L θc + 1),
      |cuspHam (f θc) (coordY L θc) (deriv (deriv (f θc)) (coordY L θc) / 2) y| ≤
          M * |y - coordY L θc| ^ 4 ∧
      |deriv (cuspHam (f θc) (coordY L θc) (deriv (deriv (f θc)) (coordY L θc) / 2)) y| ≤
          M * |y - coordY L θc| ^ 3 := by
    intro θc hθc
    obtain ⟨hs, h0, h1, h2, h3⟩ := hψprops θc hθc
    exact gp5_taylor4 _ hs _ h0 h1 h2 h3
  choose! M hM using hT
  -- pairwise distance of the cusp points
  obtain ⟨d, hd, hdP⟩ := gp5_pairwise_dist h.circle S hSI
  -- the `C²`-smallness `η'` of the fields and the radii `ε₀ θc`
  obtain ⟨C₀, hC₀, hC2⟩ := flow_C2_close
  set η' : ℝ := min (η / C₀) 1 with hη'def
  have hη' : 0 < η' := lt_min (div_pos hη hC₀) one_pos
  have hη'1 : η' ≤ 1 := min_le_right _ _
  have hη'C : C₀ * η' ≤ η := by
    have : η' ≤ η / C₀ := min_le_left _ _
    rwa [le_div_iff₀ hC₀, mul_comm] at this
  have hε₀ : ∀ θc ∈ S, 0 < min (rc / 2) (min (d / 3) (min 1
      (1 / ((3 + |coordY L θc|) * M θc + 1)))) := fun θc hθc => by
    have := (hM θc hθc).1
    exact lt_min (by linarith) (lt_min (by linarith) (lt_min one_pos (by positivity)))
  -- the cutoff Hamiltonians (P5.4)
  have hHam : ∀ θc ∈ S, ∃ (ε : ℝ) (H : ℝ³ → ℝ), 0 < ε ∧
      ε ≤ min (rc / 2) (min (d / 3) (min 1 (1 / ((3 + |coordY L θc|) * M θc + 1)))) ∧
      ContactMotionsHyp H ∧
      (∀ p ∈ Metric.ball (L θc) (ε / 2),
        H p = cuspHam (f θc) (coordY L θc) (deriv (deriv (f θc)) (coordY L θc) / 2) (p 1)) ∧
      tsupport H ⊆ Metric.closedBall (L θc) ε ∧
      ∀ k ≤ 2, ∀ p, ‖iteratedFDeriv ℝ k (hamVF H) p‖ ≤ η' :=
    fun θc hθc => exists_small_cusp_hamiltonian (f θc) (hf θc hθc).1 (coordY L θc) _
      (hf θc hθc).2.1 (hA θc hθc) (L θc) rfl hη' (hε₀ θc hθc)
  choose! ε Hc hHc using hHam
  have hεd : ∀ θc ∈ S, ε θc ≤ d / 3 := fun θc hθc =>
    ((hHc θc hθc).2.1).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεrc : ∀ θc ∈ S, ε θc ≤ rc / 2 := fun θc hθc => ((hHc θc hθc).2.1).trans (min_le_left _ _)
  have hε1 : ∀ θc ∈ S, ε θc ≤ 1 := fun θc hθc =>
    ((hHc θc hθc).2.1).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεC : ∀ θc ∈ S, ε θc ≤ 1 / ((3 + |coordY L θc|) * M θc + 1) := fun θc hθc =>
    ((hHc θc hθc).2.1).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  -- disjoint supports
  have hdisj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      Disjoint (Metric.closedBall (L a) (ε a)) (Metric.closedBall (L b) (ε b)) := by
    intro a ha b hb hab
    rw [Set.disjoint_left]
    intro p hpa hpb
    rw [Metric.mem_closedBall] at hpa hpb
    have := hdP a ha b hb hab
    have htri := dist_triangle (L a) p (L b)
    rw [dist_comm] at hpa
    linarith [hεd a ha, hεd b hb]
  -- the summed Hamiltonian
  set H : ℝ³ → ℝ := fun q => ∑ θc ∈ S, Hc θc q with hHdef
  have hHs : ∀ θc ∈ S, ContDiff ℝ ∞ (Hc θc) := fun θc hθc => (hHc θc hθc).2.2.1.smooth
  have hHsmooth : ContDiff ℝ ∞ H := ContDiff.sum fun θc hθc => hHs θc hθc
  have hsuppH : tsupport H ⊆ ⋃ θc ∈ S, Metric.closedBall (L θc) (ε θc) :=
    gp5_tsupport_sum_subset S Hc _ (fun _ _ => Metric.isClosed_closedBall)
      fun θc hθc => (hHc θc hθc).2.2.2.2.1
  have hHcs : HasCompactSupport H := by
    refine HasCompactSupport.intro (K := ⋃ θc ∈ S, Metric.closedBall (L θc) (ε θc))
      (S.isCompact_biUnion fun θc _ => isCompact_closedBall (L θc) (ε θc)) fun q hq => ?_
    exact image_eq_zero_of_notMem_tsupport fun h => hq (hsuppH h)
  have hH : ContactMotionsHyp H := ⟨hHsmooth, hHcs⟩
  -- the `C²` bound on `X_H`
  have hXb : ∀ k ≤ 2, ∀ p, ‖iteratedFDeriv ℝ k (hamVF H) p‖ ≤ η' := by
    intro k hk p
    have heq : hamVF H = fun q => ∑ θc ∈ S, hamVF (Hc θc) q := by
      funext q; exact gp5_hamVF_sum S Hc hHs q
    rw [heq]
    refine gp5_sum_bound S (fun θc => hamVF (Hc θc)) (fun θc => Metric.closedBall (L θc) (ε θc))
      (fun θc hθc => ContactMotions.contDiff_hamVF (hHs θc hθc)) ?_ hdisj hη'.le
      (fun θc hθc => (hHc θc hθc).2.2.2.2.2) k hk p
    intro θc hθc
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro q hq
    by_contra hnot
    exact hq (gp5_hamVF_eq_zero_of_notMem fun h => hnot ((hHc θc hθc).2.2.2.2.1 h))
  -- the isotopy: the flow of `H` (P0.1)
  set Φ := hamIsotopy 1 (fun _ => H) (fun _ => 1) with hΦdef
  have hΦ : IsContactIsotopy Φ := isContactIsotopy_hamIsotopy 1 (fun _ => H) (fun _ => 1) fun _ => hH
  have hΦ1 : Φ 1 = hamFlow H 1 := by
    funext p
    show composeFlows 1 (fun _ => H) ((1 : ℝ) • fun _ => (1 : ℝ)) p = hamFlow H 1 p
    simp [composeFlows]
  have hΦ1s : ContDiff ℝ ∞ (Φ 1) := by rw [hΦ1]; exact ((fd_contact_motions.diffeo H hH).2 1).1
  have hΦ1bij : Function.Bijective (Φ 1) := by rw [hΦ1]; exact hH.hamFlow_bijective 1
  have hΦ1contact : ∀ p, ∃ c : ℝ, 0 < c ∧ ∀ v, alpha (Φ 1 p) (fderiv ℝ (Φ 1) p v) = c * alpha p v :=
    fun p => hΦ.contact 1 ⟨zero_le_one, le_rfl⟩ p
  have hΦ1C2 : ∀ k ≤ 2, ∀ p, ‖iteratedFDeriv ℝ k (fun p => Φ 1 p - p) p‖ ≤ η := by
    intro k hk p
    rw [hΦ1]
    have := hC2 (hamVF H) hH.contDiff_hamVF hH.hasCompactSupport_hamVF η' hη' hη'1 hXb k hk p
    exact this.trans hη'C
  have hΦ1fix : ∀ p, (∀ θc ∈ cuspSet L, rc ≤ dist p (L θc)) → Φ 1 p = p := by
    intro p hp
    rw [hΦ1]
    apply gp5_hamFlow_fixed hH
    apply gp5_hamVF_eq_zero_of_notMem
    intro hmem
    have hmem' := hsuppH hmem
    rw [Set.mem_iUnion₂] at hmem'
    obtain ⟨θc, hθc, hball'⟩ := hmem'
    rw [Metric.mem_closedBall] at hball'
    have := hp θc (hS θc hθc)
    linarith [hεrc θc hθc]
  -- the exact germ at each cusp of `S` (P5.1, P5.3, uniqueness on the inner ball)
  have hgerm : ∀ θc ∈ S, IsExactCuspGerm (Φ 1 ∘ L) θc := by
    intro θc hθc
    obtain ⟨hεpos, -, -, hHcψ, -, -⟩ := hHc θc hθc
    have hHψ : ∀ p ∈ Metric.ball (L θc) (ε θc / 2),
        H p = cuspHam (f θc) (coordY L θc) (deriv (deriv (f θc)) (coordY L θc) / 2) (p 1) := by
      intro p hp
      simp only [hHdef]
      rw [Finset.sum_eq_single θc]
      · exact hHcψ p hp
      · intro b hb hbθ
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have h1 := (hHc b hb).2.2.2.2.1 hmem
        exact Set.disjoint_left.1 (hdisj b hb θc hθc hbθ) h1
          (Metric.mem_closedBall.2 ((Metric.mem_ball.1 hp).le.trans (by linarith)))
      · intro hn; exact absurd hθc hn
    have hsmall : ∀ q ∈ Metric.ball (L θc) (ε θc / 4), ∀ s ∈ Icc (0 : ℝ) 1,
        dist (cuspFlowMap (cuspHam (f θc) (coordY L θc) (deriv (deriv (f θc)) (coordY L θc) / 2)) s q)
          q < ε θc / 8 := by
      intro q hq s hs
      refine gp5_cuspFlow_small (hM θc hθc).1 hεpos (hε1 θc hθc) (fun y hy => (hM θc hθc).2 y hy)
        ?_ hq hs
      have hC := hεC θc hθc
      have hM0 := (hM θc hθc).1
      have hεle1 := hε1 θc hθc
      set P : ℝ := (3 + |coordY L θc|) * M θc with hPdef
      have hP0 : 0 ≤ P := by positivity
      have hε' : ε θc * (P + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hC
      have h1 : P * ε θc ≤ 1 := by nlinarith
      show P * ε θc ^ 2 < 8
      calc P * ε θc ^ 2 = (P * ε θc) * ε θc := by ring
        _ ≤ 1 * 1 := mul_le_mul h1 hεle1 hεpos.le zero_le_one
        _ < 8 := by norm_num
    have hL' : ∀ᶠ θ in 𝓝 θc, (Φ 1 ∘ L) θ =
        cuspFlowMap (cuspHam (f θc) (coordY L θc) (deriv (deriv (f θc)) (coordY L θc) / 2)) 1
          (L θ) := by
      have hnhds : L ⁻¹' Metric.ball (L θc) (ε θc / 4) ∈ 𝓝 θc :=
        hL.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity))
      filter_upwards [hnhds] with θ hθ
      rw [Function.comp_apply, hΦ1]
      exact gp5_flow_eq_cuspFlow hH (hψprops θc hθc).1 hHψ hsmall hθ
    exact exactGerm_of_cuspFlow h (hS θc hθc) (hf θc hθc).1 (hf θc hθc).2.1 (hf θc hθc).2.2.1
      (hf θc hθc).2.2.2 hL'
  -- `x′` of the new curve vanishes at all cusps
  have hΦ1L : ContDiff ℝ ∞ (Φ 1 ∘ L) := hΦ1s.comp hL
  have hper' : Periodic (Φ 1 ∘ L) (2 * π) := fun θ => by simp [hperL θ]
  have hx'0 : ∀ θc ∈ cuspSet L, deriv (coordX (Φ 1 ∘ L)) θc = 0 := by
    intro θc hθc
    obtain ⟨θc', hθc', k, hk⟩ := gp5_cusp_reduce hperL hθc
    have hper'' : Periodic (deriv (coordX (Φ 1 ∘ L))) (2 * π) :=
      gp5_periodic_deriv fun t => by simp [coordX, hperL t]
    rw [hk, gp5_periodic_int hper'']
    exact gp5_deriv_x_zero_of_germ hΦ1L (hgerm θc' ((hSmem θc').2 hθc'))
  -- stability (P5.6)
  obtain ⟨hcusp, hS3⟩ := hstab (Φ 1) hΦ1s hΦ1bij hΦ1contact hΦ1C2 hΦ1fix hx'0
  refine ⟨Φ, hΦ, hS3, fun θc hθc => ?_⟩
  rw [hcusp] at hθc
  obtain ⟨θc', hθc', k, hk⟩ := gp5_cusp_reduce hperL hθc
  rw [hk]
  exact gp5_germ_shift hper' k (hgerm θc' ((hSmem θc').2 hθc'))

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
