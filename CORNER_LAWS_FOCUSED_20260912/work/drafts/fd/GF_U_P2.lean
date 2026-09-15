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

/-! Helpers for unit P2 (prefix `gp2_`).  The front is shown injective on an interval from a
*certificate*: either `x′ ≠ 0` on it (regular interval), or `x″ ≠ 0` and `y′ ≠ 0` on it (critical
interval).  Both cases are Rolle's theorem; the critical case is the mean-value form of the
integration by parts `z(θ₂) − z(θ₁) = ∫ y′ (X − x)` (sm-3:2666-2675): the function
`k = z − y (x − X)` has `k′ = y′ (X − x)`. -/

/-- Rolle: a function whose derivative never vanishes on the interior of an interval is injective
on the closed interval. -/
lemma gp2_injOn_of_deriv_ne_zero {f : ℝ → ℝ} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    (h : ∀ θ ∈ Ioo α β, deriv f θ ≠ 0) : InjOn f (Icc α β) := by
  intro θ₁ h₁ θ₂ h₂ heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hlt (hf.mono (Icc_subset_Icc h₁.1 h₂.2)) heq
    exact h c ⟨h₁.1.trans_lt hc.1, hc.2.trans_le h₂.2⟩ hc0
  · obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hlt (hf.mono (Icc_subset_Icc h₂.1 h₁.2)) heq.symm
    exact h c ⟨h₂.1.trans_lt hc.1, hc.2.trans_le h₁.2⟩ hc0

/-- Regular interval: `x′ ≠ 0` makes `(x, z)` injective. -/
lemma gp2_injOn_front_regular {x z : ℝ → ℝ} {α β : ℝ} (hx : ContinuousOn x (Icc α β))
    (h : ∀ θ ∈ Ioo α β, deriv x θ ≠ 0) : InjOn (fun θ => (x θ, z θ)) (Icc α β) := by
  intro θ₁ h₁ θ₂ h₂ heq
  simp only [Prod.mk.injEq] at heq
  exact gp2_injOn_of_deriv_ne_zero hx h h₁ h₂ heq.1

/-- Critical interval (sm-3:2666-2675): `x″ ≠ 0` (so `x′` is injective), `y′ ≠ 0` and `z′ = y x′`
on `[α, β]` make `(x, z)` injective there.  With `X = x θ₁ = x θ₂` and `k = z − y (x − X)`,
`k θ₁ = k θ₂` gives `c` with `0 = k′ c = y′ c (X − x c)`, so `x c = X`, and then `x′` vanishes
once in `(θ₁, c)` and once in `(c, θ₂)`, contradicting its injectivity. -/
lemma gp2_injOn_front_critical {x y z : ℝ → ℝ} {α β : ℝ}
    (hx : Differentiable ℝ x) (hy : Differentiable ℝ y) (hz : Differentiable ℝ z)
    (hx' : ContinuousOn (deriv x) (Icc α β)) (hleg : ∀ θ, deriv z θ = y θ * deriv x θ)
    (hx'' : ∀ θ ∈ Ioo α β, deriv (deriv x) θ ≠ 0) (hy' : ∀ θ ∈ Ioo α β, deriv y θ ≠ 0) :
    InjOn (fun θ => (x θ, z θ)) (Icc α β) := by
  have hinj : InjOn (deriv x) (Icc α β) := gp2_injOn_of_deriv_ne_zero hx' hx''
  have key : ∀ θ₁ ∈ Icc α β, ∀ θ₂ ∈ Icc α β, θ₁ < θ₂ → x θ₁ = x θ₂ → z θ₁ = z θ₂ → False := by
    intro θ₁ h₁ θ₂ h₂ hlt hxe hze
    have hkc : ContinuousOn (fun θ => z θ - y θ * (x θ - x θ₁)) (Icc θ₁ θ₂) :=
      (hz.continuous.sub (hy.continuous.mul (hx.continuous.sub continuous_const))).continuousOn
    have hk12 : (fun θ => z θ - y θ * (x θ - x θ₁)) θ₁ = (fun θ => z θ - y θ * (x θ - x θ₁)) θ₂ := by
      simp only [hxe, sub_self, mul_zero, sub_zero, hze]
    obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hlt hkc hk12
    have hkd : HasDerivAt (fun θ => z θ - y θ * (x θ - x θ₁))
        (deriv z c - (deriv y c * (x c - x θ₁) + y c * deriv x c)) c :=
      (hz c).hasDerivAt.sub ((hy c).hasDerivAt.mul ((hx c).hasDerivAt.sub_const (x θ₁)))
    rw [hkd.deriv, hleg c] at hc0
    have hcI : c ∈ Ioo α β := ⟨h₁.1.trans_lt hc.1, hc.2.trans_le h₂.2⟩
    have hc0' : deriv y c * (x θ₁ - x c) = 0 := by linear_combination hc0
    have hxc : x c = x θ₁ := by
      rcases mul_eq_zero.1 hc0' with h0 | h0
      · exact absurd h0 (hy' c hcI)
      · linarith
    obtain ⟨c₁, hc₁, hc₁0⟩ := exists_deriv_eq_zero hc.1 hx.continuous.continuousOn hxc.symm
    obtain ⟨c₂, hc₂, hc₂0⟩ := exists_deriv_eq_zero hc.2 hx.continuous.continuousOn (hxc.trans hxe)
    have hc₁I : c₁ ∈ Icc α β := ⟨h₁.1.trans hc₁.1.le, (hc₁.2.trans hc.2).le.trans h₂.2⟩
    have hc₂I : c₂ ∈ Icc α β := ⟨h₁.1.trans (hc.1.trans hc₂.1).le, hc₂.2.le.trans h₂.2⟩
    have := hinj hc₁I hc₂I (hc₁0.trans hc₂0.symm)
    linarith [hc₁.2, hc₂.1]
  intro θ₁ h₁ θ₂ h₂ heq
  simp only [Prod.mk.injEq] at heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key θ₁ h₁ θ₂ h₂ hlt heq.1 heq.2
  · exact key θ₂ h₂ θ₁ h₁ hlt heq.1.symm heq.2.symm

/-- Legendrian curves satisfy `z′ = y x′`. -/
lemma gp2_deriv_coordZ {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (hleg : IsLegendrian L) (θ : ℝ) :
    deriv (coordZ L) θ = coordY L θ * deriv (coordX L) θ := by
  have hd : HasDerivAt L (deriv L θ) θ := (hL.differentiable (by simp) θ).hasDerivAt
  have h0 := (ContactMotions.hasDerivAt_coord hd 0).deriv
  have h2 := (ContactMotions.hasDerivAt_coord hd 2).deriv
  have h := hleg θ
  simp only [alpha] at h
  show deriv (fun t => L t 2) θ = L θ 1 * deriv (fun t => L t 0) θ
  rw [h0, h2]; linarith

/-- A certificate on `[α, β]` makes the front injective there. -/
lemma gp2_injOn_front_of_cert {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (hleg : IsLegendrian L) {α β : ℝ}
    (hc : (∀ θ ∈ Icc α β, deriv (coordX L) θ ≠ 0) ∨
      ((∀ θ ∈ Icc α β, deriv (deriv (coordX L)) θ ≠ 0) ∧ ∀ θ ∈ Icc α β, deriv (coordY L) θ ≠ 0)) :
    InjOn (front L) (Icc α β) := by
  have hx : ContDiff ℝ ∞ (coordX L) := (ContactMotions.contDiff_coord 0).comp hL
  have hy : ContDiff ℝ ∞ (coordY L) := (ContactMotions.contDiff_coord 1).comp hL
  have hz : ContDiff ℝ ∞ (coordZ L) := (ContactMotions.contDiff_coord 2).comp hL
  have hfront : front L = fun θ => (coordX L θ, coordZ L θ) := rfl
  rw [hfront]
  rcases hc with h | ⟨h1, h2⟩
  · exact gp2_injOn_front_regular hx.continuous.continuousOn
      fun θ hθ => h θ (Ioo_subset_Icc_self hθ)
  · exact gp2_injOn_front_critical (hx.differentiable (by simp)) (hy.differentiable (by simp))
      (hz.differentiable (by simp)) (hx.continuous_deriv (by simp)).continuousOn
      (gp2_deriv_coordZ hL hleg) (fun θ hθ => h1 θ (Ioo_subset_Icc_self hθ))
      (fun θ hθ => h2 θ (Ioo_subset_Icc_self hθ))

/-- Every point of a `Stage1` curve has a certificate interval (`NoDoubleZero`; at a cusp `y′ ≠ 0`
by P1.4). -/
lemma gp2_exists_cert {L : ℝ → ℝ³} (h : Stage1 L) (θ₀ : ℝ) :
    ∃ ρ > 0, (∀ θ ∈ Icc (θ₀ - ρ) (θ₀ + ρ), deriv (coordX L) θ ≠ 0) ∨
      ((∀ θ ∈ Icc (θ₀ - ρ) (θ₀ + ρ), deriv (deriv (coordX L)) θ ≠ 0) ∧
        ∀ θ ∈ Icc (θ₀ - ρ) (θ₀ + ρ), deriv (coordY L) θ ≠ 0) := by
  have hx : ContDiff ℝ ∞ (coordX L) := (ContactMotions.contDiff_coord 0).comp h.circle.smooth
  have hy : ContDiff ℝ ∞ (coordY L) := (ContactMotions.contDiff_coord 1).comp h.circle.smooth
  have hx' : Continuous (deriv (coordX L)) := hx.continuous_deriv (by simp)
  have hx'' : Continuous (deriv (deriv (coordX L))) :=
    (contDiff_infty_iff_deriv.1 hx).2.continuous_deriv (by simp)
  have hy' : Continuous (deriv (coordY L)) := hy.continuous_deriv (by simp)
  have step : ∀ {P : ℝ → Prop}, (∀ᶠ θ in 𝓝 θ₀, P θ) →
      ∃ ρ > 0, ∀ θ ∈ Icc (θ₀ - ρ) (θ₀ + ρ), P θ := by
    intro P hP
    obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hP
    refine ⟨ε / 2, half_pos hε, fun θ hθ => hεP ?_⟩
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [hθ.1, hθ.2]
  by_cases hx0 : deriv (coordX L) θ₀ = 0
  · have hx2 : deriv (deriv (coordX L)) θ₀ ≠ 0 := (h.noDoubleZero θ₀).resolve_left (not_not.2 hx0)
    have hy0 : deriv (coordY L) θ₀ ≠ 0 := deriv_y_ne_zero_at_cusp h hx0
    obtain ⟨ρ, hρ, hP⟩ := step ((hx''.continuousAt.eventually_ne hx2).and
      (hy'.continuousAt.eventually_ne hy0))
    exact ⟨ρ, hρ, Or.inr ⟨fun θ hθ => (hP θ hθ).1, fun θ hθ => (hP θ hθ).2⟩⟩
  · obtain ⟨ρ, hρ, hP⟩ := step (hx'.continuousAt.eventually_ne hx0)
    exact ⟨ρ, hρ, Or.inl hP⟩

/-- The front of a `2π`-periodic curve is `2π`-periodic. -/
lemma gp2_periodic_front {L : ℝ → ℝ³} (hL : Periodic L (2 * π)) : Periodic (front L) (2 * π) :=
  fun θ => by show (L (θ + 2 * π) 0, L (θ + 2 * π) 2) = (L θ 0, L θ 2); rw [hL θ]

/-- The circular distance is at most `π`. -/
lemma gp2_circDist_le_pi (θ η : ℝ) : circDist θ η ≤ π := by
  have h1 := abs_sub_round ((θ - η) / (2 * π))
  have h2 : θ - η - 2 * π * round ((θ - η) / (2 * π)) =
      2 * π * ((θ - η) / (2 * π) - round ((θ - η) / (2 * π))) := by
    field_simp
  rw [circDist, h2, abs_mul, abs_of_pos two_pi_pos]
  nlinarith [pi_pos]

/-- Reduction of the collar property to pairs `(θ, η)` with `θ ∈ [0, 2π)`, `|θ − η| < δ` and
`|θ − η| ≤ π` (the circular distance is realised after shifting both parameters by multiples of
`2π`; `¬ SameParam` becomes `θ ≠ η`). -/
lemma gp2_collar_of_reduced {L : ℝ → ℝ³} (hL : Periodic L (2 * π)) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ θ ∈ Ico 0 (2 * π), ∀ η, |θ - η| < δ → |θ - η| ≤ π → θ ≠ η → front L θ ≠ front L η) :
    LocallyInjectiveFront L δ := by
  refine ⟨hδ, fun θ η hd hns heq => ?_⟩
  have hF : Periodic (front L) (2 * π) := gp2_periodic_front hL
  have hpi := gp2_circDist_le_pi θ η
  rw [circDist] at hd hpi
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (k : ℝ) = round ((θ - η) / (2 * π)) := ⟨_, rfl⟩
  rw [← hk] at hd hpi
  have hθ'mem : toIcoMod two_pi_pos 0 θ ∈ Ico 0 (2 * π) := toIcoMod_mem_Ico' two_pi_pos θ
  have hθθ' : θ - toIcoMod two_pi_pos 0 θ = (toIcoDiv two_pi_pos 0 θ : ℝ) * (2 * π) := by
    rw [self_sub_toIcoMod, zsmul_eq_mul]
  have hdiff : toIcoMod two_pi_pos 0 θ - (η + k * (2 * π) - toIcoDiv two_pi_pos 0 θ * (2 * π)) =
      θ - η - 2 * π * k := by linarith
  have hFθ : front L (toIcoMod two_pi_pos 0 θ) = front L θ := by
    have := hF.sub_int_mul_eq (x := θ) (toIcoDiv two_pi_pos 0 θ)
    rwa [show θ - toIcoDiv two_pi_pos 0 θ * (2 * π) = toIcoMod two_pi_pos 0 θ by linarith] at this
  have hFη : front L (η + k * (2 * π) - toIcoDiv two_pi_pos 0 θ * (2 * π)) = front L η := by
    rw [show η + k * (2 * π) - toIcoDiv two_pi_pos 0 θ * (2 * π) =
        η + ((k - toIcoDiv two_pi_pos 0 θ : ℤ) : ℝ) * (2 * π) by push_cast; ring]
    exact hF.int_mul _ η
  refine h _ hθ'mem _ (by rw [hdiff]; exact hd) (by rw [hdiff]; exact hpi) ?_
    (hFθ.trans (heq.trans hFη.symm))
  intro heq'
  apply hns
  refine ⟨-k, ?_⟩
  push_cast
  linarith

/-- The collar from a cover of `[0, 2π]` by sets on which the front is injective, with a Lebesgue
number `δ` (sm-3:2680-2685). -/
lemma gp2_collar_of_cover {L : ℝ → ℝ³} (hL : Periodic L (2 * π)) {ι : Sort*} {c : ι → Set ℝ}
    (hinj : ∀ i, InjOn (front L) (c i)) {δ : ℝ} (hδ : 0 < δ)
    (hleb : ∀ θ ∈ Icc 0 (2 * π), ∃ i, Metric.ball θ δ ⊆ c i) : LocallyInjectiveFront L δ := by
  refine gp2_collar_of_reduced hL hδ fun θ hθ η hd _ hne heq => ?_
  obtain ⟨i, hi⟩ := hleb θ (Ico_subset_Icc_self hθ)
  have hθi : θ ∈ c i := hi (Metric.mem_ball_self hδ)
  have hηi : η ∈ c i := hi (by rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]; exact hd)
  exact hne (hinj i hθi hηi heq)

/-- LEAF P2.1.  A `Stage1` front is uniformly locally injective: regular intervals (`x′` of fixed
sign, `x` monotone) and critical intervals (one simple zero of `x′`, `y′` of fixed sign; for
`θ₁ < θ_c < θ₂` with `x(θ₁) = x(θ₂) = X`, `z(θ₂) − z(θ₁) = ∫ y′(θ)(X − x(θ)) dθ ≠ 0` by integration
by parts from `z′ = y x′`), Lebesgue number of the cover. -/
theorem exists_collar {L : ℝ → ℝ³} (h : Stage1 L) : ∃ δc, LocallyInjectiveFront L δc := by
  choose ρ hρ hc using gp2_exists_cert h
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (ι := ℝ)
    (c := fun θ₀ => Ioo (θ₀ - ρ θ₀) (θ₀ + ρ θ₀)) isCompact_Icc (fun _ => isOpen_Ioo)
    (fun θ _ => mem_iUnion.2 ⟨θ, ⟨by linarith [hρ θ], by linarith [hρ θ]⟩⟩)
  refine ⟨δ, gp2_collar_of_cover h.circle.periodic (fun θ₀ => ?_) hδ hleb⟩
  exact (gp2_injOn_front_of_cert h.circle.smooth h.legendrian (hc θ₀)).mono Ioo_subset_Icc_self

/-! Helpers for P2.2 (prefix `gp2_`).  The leaf `stage1_stable` is FALSE as stated (see
`GF_U_P2_REPORT.md`: a front double point at circular distance exactly `δc` moves inside the collar
under a Hamiltonian perturbation); what is true, and proved here as `gp2_stage1_stable_of_lt`, is
that `Stage1` persists and the collar persists with every smaller width `δ' < δc`. -/

/-- Tube lemma: an open condition on a compact set at parameter `0` holds for all small
parameters. -/
lemma gp2_eventually_of_compact {X : Type*} [TopologicalSpace X] {m : ℕ} {I : Set X}
    (hI : IsCompact I) {V : Set (X × ℝ^m)} (hV : IsOpen V) (h0 : ∀ θ ∈ I, (θ, (0 : ℝ^m)) ∈ V) :
    ∀ᶠ a in 𝓝 (0 : ℝ^m), ∀ θ ∈ I, (θ, a) ∈ V := by
  obtain ⟨u, v, -, hv, hIu, h0v, huv⟩ := generalized_tube_lemma hI isCompact_singleton hV
    (by rintro ⟨θ, a⟩ ⟨hθ, ha⟩; rw [mem_singleton_iff] at ha; subst ha; exact h0 θ hθ)
  exact Filter.eventually_of_mem (hv.mem_nhds (h0v rfl)) fun a ha θ hθ => huv ⟨hIu hθ, ha⟩

/-- `(θ, a) ↦ Φ_a (L θ)` is jointly smooth (row 86, `compositions_smooth`). -/
lemma gp2_contDiff_G {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ^m => composeFlows m Hs (par q.2) (L q.1)) := by
  have h1 := fd_contact_motions.compositions_smooth m Hs hHs
  have hpar : ContDiff ℝ ∞ (fun a : ℝ^m => par a) := by
    refine contDiff_pi.2 fun i => ?_
    show ContDiff ℝ ∞ (fun a : ℝ^m => a i)
    exact (PiLp.proj 2 (fun _ : Fin m => ℝ) i : ℝ^m →L[ℝ] ℝ).contDiff
  exact h1.comp ((hpar.comp contDiff_snd).prodMk (hL.comp contDiff_fst))

/-- At parameter `0` the composition is the identity. -/
lemma gp2_composeFlows_par_zero (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (hHs : ∀ i, ContactMotionsHyp (Hs i))
    (p : ℝ³) : composeFlows m Hs (par (0 : ℝ^m)) p = p := by
  have : par (0 : ℝ^m) = 0 := funext fun i => by simp [par]
  rw [this]
  exact ContactMotions.composeFlows_zero m Hs (fun i p => (hHs i).hamFlow_zero p) p

/-- The partial `θ`-derivative `DG (1, 0)` of a jointly smooth map is jointly smooth. -/
lemma gp2_contDiff_D1 {m : ℕ} {G : ℝ × ℝ^m → ℝ³} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun q => fderiv ℝ G q (1, 0)) :=
  (hG.contDiff_fderiv_apply (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)

/-- The `θ`-derivative of a coordinate of the slice `θ ↦ G (θ, a)` is the partial derivative. -/
lemma gp2_deriv_slice {m : ℕ} {G : ℝ × ℝ^m → ℝ³} (hG : ContDiff ℝ ∞ G) (a : ℝ^m) (i : Fin 3)
    (θ : ℝ) : deriv (fun θ => G (θ, a) i) θ = fderiv ℝ G (θ, a) (1, 0) i := by
  have h1 : HasDerivAt (fun θ : ℝ => (θ, a)) ((1 : ℝ), (0 : ℝ^m)) θ :=
    (hasDerivAt_id θ).prodMk (hasDerivAt_const θ a)
  have h2 : HasDerivAt (fun θ => G (θ, a)) (fderiv ℝ G (θ, a) (1, 0)) θ :=
    (hG.differentiable (by simp) (θ, a)).hasFDerivAt.comp_hasDerivAt θ h1
  exact (ContactMotions.hasDerivAt_coord h2 i).deriv

/-- The second `θ`-derivative of a coordinate of the slice. -/
lemma gp2_deriv2_slice {m : ℕ} {G : ℝ × ℝ^m → ℝ³} (hG : ContDiff ℝ ∞ G) (a : ℝ^m) (i : Fin 3)
    (θ : ℝ) : deriv (deriv (fun θ => G (θ, a) i)) θ =
      fderiv ℝ (fun q => fderiv ℝ G q (1, 0)) (θ, a) (1, 0) i := by
  have : deriv (fun θ => G (θ, a) i) = fun θ => (fun q => fderiv ℝ G q (1, 0)) (θ, a) i :=
    funext fun θ => gp2_deriv_slice hG a i θ
  rw [this, gp2_deriv_slice (gp2_contDiff_D1 hG) a i θ]

/-- The derivative of a `2π`-periodic function is `2π`-periodic. -/
lemma gp2_periodic_deriv {f : ℝ → ℝ} (hf : Periodic f (2 * π)) : Periodic (deriv f) (2 * π) := by
  intro θ
  have : (fun t => f (t + 2 * π)) = f := funext hf
  rw [← deriv_comp_add_const, this]

/-- Every parameter is `θ' + n·2π` with `θ' ∈ [0, 2π)`. -/
lemma gp2_exists_shift (θ : ℝ) : ∃ θ' ∈ Ico 0 (2 * π), ∃ n : ℤ, θ = θ' + n * (2 * π) :=
  ⟨toIcoMod two_pi_pos 0 θ, toIcoMod_mem_Ico' two_pi_pos θ, toIcoDiv two_pi_pos 0 θ, by
    have := self_sub_toIcoMod two_pi_pos 0 θ
    rw [zsmul_eq_mul] at this
    linarith⟩

/-- `circDist θ η ≤ |θ − η|`. -/
lemma gp2_circDist_le_abs (θ η : ℝ) : circDist θ η ≤ |θ - η| := by
  have h1 := round_le ((θ - η) / (2 * π)) 0
  have h2 : θ - η - 2 * π * round ((θ - η) / (2 * π)) =
      2 * π * ((θ - η) / (2 * π) - round ((θ - η) / (2 * π))) := by
    field_simp
  have h3 : θ - η = 2 * π * ((θ - η) / (2 * π)) := by field_simp
  rw [circDist, h2, abs_mul, abs_of_pos two_pi_pos]
  conv_rhs => rw [h3, abs_mul, abs_of_pos two_pi_pos]
  simp only [Int.cast_zero, sub_zero] at h1
  exact mul_le_mul_of_nonneg_left h1 two_pi_pos.le

/-- Parameters at distance in `(0, π]` are distinct on the circle. -/
lemma gp2_not_sameParam {θ η : ℝ} (h1 : 0 < |θ - η|) (h2 : |θ - η| ≤ π) : ¬ SameParam θ η := by
  rintro ⟨k, hk⟩
  have e : θ - η = -(2 * π) * k := by rw [hk]; ring
  rw [e, abs_mul, abs_neg, abs_of_pos two_pi_pos] at h1 h2
  have hk0 : (k : ℝ) ≠ 0 := by
    intro h0; rw [h0, abs_zero, mul_zero] at h1; exact lt_irrefl _ h1
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have := Int.one_le_abs (Int.cast_ne_zero.1 hk0)
    exact_mod_cast this
  nlinarith [pi_pos]

/-- Monotonicity of the collar in its width. -/
lemma gp2_locallyInjectiveFront_mono {L : ℝ → ℝ³} {δ δ' : ℝ} (h : LocallyInjectiveFront L δ)
    (hδ' : 0 < δ') (hle : δ' ≤ δ) : LocallyInjectiveFront L δ' :=
  ⟨hδ', fun θ η hd => h.2 θ η (hd.trans_le hle)⟩

/-- Certificates persist for small parameters: the three functions `(θ, a) ↦ x_a′(θ), x_a″(θ),
y_a′(θ)` are jointly continuous (partial `θ`-derivatives of the jointly smooth `(θ, a) ↦ Φ_a(L θ)`),
and a nonvanishing condition on a compact interval is open (tube lemma). -/
lemma gp2_cert_stable {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) {α β : ℝ}
    (hc : (∀ θ ∈ Icc α β, deriv (coordX L) θ ≠ 0) ∨
      ((∀ θ ∈ Icc α β, deriv (deriv (coordX L)) θ ≠ 0) ∧ ∀ θ ∈ Icc α β, deriv (coordY L) θ ≠ 0)) :
    ∀ᶠ a in 𝓝 (0 : ℝ^m),
      (∀ θ ∈ Icc α β, deriv (coordX (composeFlows m Hs (par a) ∘ L)) θ ≠ 0) ∨
      ((∀ θ ∈ Icc α β, deriv (deriv (coordX (composeFlows m Hs (par a) ∘ L))) θ ≠ 0) ∧
        ∀ θ ∈ Icc α β, deriv (coordY (composeFlows m Hs (par a) ∘ L)) θ ≠ 0) := by
  have hG : ContDiff ℝ ∞ (fun q : ℝ × ℝ^m => composeFlows m Hs (par q.2) (L q.1)) :=
    gp2_contDiff_G hL m Hs hHs
  have hG1 := gp2_contDiff_D1 hG
  have hG2 := gp2_contDiff_D1 hG1
  have e1 : ∀ (a : ℝ^m) (θ : ℝ), deriv (coordX (composeFlows m Hs (par a) ∘ L)) θ =
      fderiv ℝ (fun q : ℝ × ℝ^m => composeFlows m Hs (par q.2) (L q.1)) (θ, a) (1, 0) 0 :=
    fun a θ => gp2_deriv_slice hG a 0 θ
  have e2 : ∀ (a : ℝ^m) (θ : ℝ), deriv (deriv (coordX (composeFlows m Hs (par a) ∘ L))) θ =
      fderiv ℝ (fun q => fderiv ℝ (fun q : ℝ × ℝ^m => composeFlows m Hs (par q.2) (L q.1)) q (1, 0))
        (θ, a) (1, 0) 0 :=
    fun a θ => gp2_deriv2_slice hG a 0 θ
  have e3 : ∀ (a : ℝ^m) (θ : ℝ), deriv (coordY (composeFlows m Hs (par a) ∘ L)) θ =
      fderiv ℝ (fun q : ℝ × ℝ^m => composeFlows m Hs (par q.2) (L q.1)) (θ, a) (1, 0) 1 :=
    fun a θ => gp2_deriv_slice hG a 1 θ
  have h0 : composeFlows m Hs (par (0 : ℝ^m)) ∘ L = L :=
    funext fun θ => gp2_composeFlows_par_zero m Hs hHs (L θ)
  have c1 : Continuous fun q : ℝ × ℝ^m =>
      fderiv ℝ (fun q : ℝ × ℝ^m => composeFlows m Hs (par q.2) (L q.1)) q (1, 0) 0 :=
    (ContactMotions.contDiff_coord 0).continuous.comp hG1.continuous
  have c2 : Continuous fun q : ℝ × ℝ^m =>
      fderiv ℝ (fun q => fderiv ℝ (fun q : ℝ × ℝ^m => composeFlows m Hs (par q.2) (L q.1)) q (1, 0))
        q (1, 0) 0 :=
    (ContactMotions.contDiff_coord 0).continuous.comp hG2.continuous
  have c3 : Continuous fun q : ℝ × ℝ^m =>
      fderiv ℝ (fun q : ℝ × ℝ^m => composeFlows m Hs (par q.2) (L q.1)) q (1, 0) 1 :=
    (ContactMotions.contDiff_coord 1).continuous.comp hG1.continuous
  rcases hc with h | ⟨h1, h2⟩
  · have := gp2_eventually_of_compact isCompact_Icc (isOpen_ne.preimage c1) (fun θ hθ => by
      simp only [mem_preimage, mem_ofPred_eq]
      rw [← e1 0 θ, h0]; exact h θ hθ)
    exact this.mono fun a ha => Or.inl fun θ hθ => by rw [e1]; exact ha θ hθ
  · have hA := gp2_eventually_of_compact isCompact_Icc (isOpen_ne.preimage c2) (fun θ hθ => by
      simp only [mem_preimage, mem_ofPred_eq]
      rw [← e2 0 θ, h0]; exact h1 θ hθ)
    have hB := gp2_eventually_of_compact isCompact_Icc (isOpen_ne.preimage c3) (fun θ hθ => by
      simp only [mem_preimage, mem_ofPred_eq]
      rw [← e3 0 θ, h0]; exact h2 θ hθ)
    exact (hA.and hB).mono fun a ⟨ha, hb⟩ => Or.inr
      ⟨fun θ hθ => by rw [e2]; exact ha θ hθ, fun θ hθ => by rw [e3]; exact hb θ hθ⟩

/-- Pairs in one period at distance in `[δ, δ']`, `δ' < δc`, have distinct fronts, stably: they
form a compact set, "fronts differ" is an open condition, and `(θ, η, a) ↦ (p_a(θ), p_a(η))` is
continuous. -/
lemma gp2_far_stable {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) {δc : ℝ} (hδ : LocallyInjectiveFront L δc)
    {δ δ' : ℝ} (hδpos : 0 < δ) (hδ' : δ' < δc) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) :
    ∀ᶠ a in 𝓝 (0 : ℝ^m), ∀ θ ∈ Icc 0 (2 * π), ∀ η, δ ≤ |θ - η| → |θ - η| ≤ δ' → |θ - η| ≤ π →
      front (composeFlows m Hs (par a) ∘ L) θ ≠ front (composeFlows m Hs (par a) ∘ L) η := by
  have hG : ContDiff ℝ ∞ (fun q : ℝ × ℝ^m => composeFlows m Hs (par q.2) (L q.1)) :=
    gp2_contDiff_G hL m Hs hHs
  have h0 : ∀ θ, composeFlows m Hs (par (0 : ℝ^m)) (L θ) = L θ :=
    fun θ => gp2_composeFlows_par_zero m Hs hHs (L θ)
  have hd : Continuous fun q : ℝ × ℝ => |q.1 - q.2| := (continuous_fst.sub continuous_snd).abs
  have hSc : IsClosed ((Prod.fst ⁻¹' Icc 0 (2 * π)) ∩ {q : ℝ × ℝ | δ ≤ |q.1 - q.2|} ∩
      {q | |q.1 - q.2| ≤ δ'} ∩ {q | |q.1 - q.2| ≤ π}) :=
    (((isClosed_Icc.preimage continuous_fst).inter (isClosed_le continuous_const hd)).inter
      (isClosed_le hd continuous_const)).inter (isClosed_le hd continuous_const)
  have hSb : (Prod.fst ⁻¹' Icc 0 (2 * π)) ∩ {q : ℝ × ℝ | δ ≤ |q.1 - q.2|} ∩
      {q | |q.1 - q.2| ≤ δ'} ∩ {q | |q.1 - q.2| ≤ π} ⊆ Icc 0 (2 * π) ×ˢ Icc (-π) (3 * π) := by
    rintro ⟨θ, η⟩ ⟨⟨⟨h1, -⟩, -⟩, h4⟩
    simp only [mem_preimage, mem_ofPred_eq] at h1 h4
    obtain ⟨h4a, h4b⟩ := abs_le.1 h4
    exact ⟨h1, by constructor <;> linarith [h1.1, h1.2]⟩
  have hScomp := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hSc hSb
  have hSfront : ∀ q ∈ (Prod.fst ⁻¹' Icc 0 (2 * π)) ∩ {q : ℝ × ℝ | δ ≤ |q.1 - q.2|} ∩
      {q | |q.1 - q.2| ≤ δ'} ∩ {q | |q.1 - q.2| ≤ π}, front L q.1 ≠ front L q.2 := by
    rintro ⟨θ, η⟩ ⟨⟨⟨-, h2⟩, h3⟩, h4⟩
    simp only [mem_ofPred_eq] at h2 h3 h4
    exact hδ.2 θ η ((gp2_circDist_le_abs θ η).trans_lt (h3.trans_lt hδ'))
      (gp2_not_sameParam (hδpos.trans_le h2) h4)
  have hV : IsOpen {p : (ℝ × ℝ) × ℝ^m |
      (composeFlows m Hs (par p.2) (L p.1.1) 0, composeFlows m Hs (par p.2) (L p.1.1) 2) ≠
        (composeFlows m Hs (par p.2) (L p.1.2) 0, composeFlows m Hs (par p.2) (L p.1.2) 2)} := by
    have hc1 : Continuous fun p : (ℝ × ℝ) × ℝ^m => composeFlows m Hs (par p.2) (L p.1.1) :=
      hG.continuous.comp (continuous_fst.fst.prodMk continuous_snd)
    have hc2 : Continuous fun p : (ℝ × ℝ) × ℝ^m => composeFlows m Hs (par p.2) (L p.1.2) :=
      hG.continuous.comp (continuous_fst.snd.prodMk continuous_snd)
    exact isOpen_ne_fun
      (((ContactMotions.contDiff_coord 0).continuous.comp hc1).prodMk
        ((ContactMotions.contDiff_coord 2).continuous.comp hc1))
      (((ContactMotions.contDiff_coord 0).continuous.comp hc2).prodMk
        ((ContactMotions.contDiff_coord 2).continuous.comp hc2))
  have := gp2_eventually_of_compact hScomp hV (fun q hq => by
    simp only [mem_ofPred_eq]
    rw [h0, h0]; exact hSfront q hq)
  refine this.mono fun a ha θ hθ η h1 h2 h3 => ?_
  exact ha (θ, η) ⟨⟨⟨hθ, h1⟩, h2⟩, h3⟩

/-- **The true form of P2.2.**  `Stage1` persists under small parameters of any Hamiltonian
family, and so does the collar with every *smaller* width `δ' < δc`: near the diagonal by the
stability of the certificates on a finite subcover (same Lebesgue number), away from it by the
compactness of the pairs at distance in `[δ, δ']`.  (With the width `δc` itself the statement is
false in general — see `GF_U_P2_REPORT.md`.) -/
theorem gp2_stage1_stable_of_lt {L : ℝ → ℝ³} (h : Stage1 L) {δc : ℝ}
    (hδ : LocallyInjectiveFront L δc) {δ' : ℝ} (hδ'pos : 0 < δ') (hδ' : δ' < δc)
    (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (hHs : ∀ i, ContactMotionsHyp (Hs i)) :
    ∃ r > 0, ∀ a : ℝ^m, ‖a‖ < r →
      Stage1 (composeFlows m Hs (par a) ∘ L) ∧
        LocallyInjectiveFront (composeFlows m Hs (par a) ∘ L) δ' := by
  -- 1. certificate intervals, a finite subcover of `[0, 2π]`, its Lebesgue number
  choose ρ hρ hc using gp2_exists_cert h
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover (fun θ₀ => Ioo (θ₀ - ρ θ₀) (θ₀ + ρ θ₀))
    (fun _ => isOpen_Ioo) (fun θ _ => mem_iUnion.2 ⟨θ, ⟨by linarith [hρ θ], by linarith [hρ θ]⟩⟩)
  obtain ⟨δ, hδpos, hleb⟩ := lebesgue_number_lemma_of_metric (ι := t)
    (c := fun i => Ioo (i.1 - ρ i.1) (i.1 + ρ i.1)) isCompact_Icc (fun _ => isOpen_Ioo)
    (fun θ hθ => by
      obtain ⟨i, hi, hθi⟩ := mem_iUnion₂.1 (ht hθ)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hθi⟩)
  -- 2. the certificates persist on the finitely many intervals; far pairs stay apart
  have hcert : ∀ᶠ a in 𝓝 (0 : ℝ^m), ∀ i ∈ t,
      (∀ θ ∈ Icc (i - ρ i) (i + ρ i), deriv (coordX (composeFlows m Hs (par a) ∘ L)) θ ≠ 0) ∨
      ((∀ θ ∈ Icc (i - ρ i) (i + ρ i),
          deriv (deriv (coordX (composeFlows m Hs (par a) ∘ L))) θ ≠ 0) ∧
        ∀ θ ∈ Icc (i - ρ i) (i + ρ i), deriv (coordY (composeFlows m Hs (par a) ∘ L)) θ ≠ 0) := by
    rw [Filter.eventually_all_finset]
    intro i _
    exact gp2_cert_stable h.circle.smooth m Hs hHs (hc i)
  have hfar := gp2_far_stable h.circle.smooth hδ hδpos hδ' m Hs hHs
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff.1 (hcert.and hfar)
  refine ⟨r, hr, fun a ha => ?_⟩
  have ha' : dist a 0 < r := by rw [dist_zero_right]; exact ha
  obtain ⟨hcerta, hfara⟩ := hall ha'
  -- 3. `Stage1`: circle and Legendrian from P0, `NoDoubleZero` from the certificates
  have hΦ := isContactIsotopy_hamIsotopy m Hs (par a) hHs
  obtain ⟨hcirc, hleg⟩ :=
    contact_preserves_legendrian hΦ h.circle h.legendrian ⟨zero_le_one, le_rfl⟩
  rw [hamIsotopy_one] at hcirc hleg
  have hxper : Periodic (deriv (coordX (composeFlows m Hs (par a) ∘ L))) (2 * π) :=
    gp2_periodic_deriv fun θ => by
      show (composeFlows m Hs (par a) ∘ L) (θ + 2 * π) 0 = (composeFlows m Hs (par a) ∘ L) θ 0
      rw [hcirc.periodic θ]
  have hnd : NoDoubleZero (composeFlows m Hs (par a) ∘ L) := by
    intro θ
    obtain ⟨θ', hθ', n, rfl⟩ := gp2_exists_shift θ
    rw [hxper.int_mul n θ', (gp2_periodic_deriv hxper).int_mul n θ']
    obtain ⟨i, hi, hθi⟩ := mem_iUnion₂.1 (ht (Ico_subset_Icc_self hθ'))
    rcases hcerta i hi with hreg | ⟨hcrit, -⟩
    · exact Or.inl (hreg θ' (Ioo_subset_Icc_self hθi))
    · exact Or.inr (hcrit θ' (Ioo_subset_Icc_self hθi))
  refine ⟨⟨hcirc, hleg, hnd⟩, ?_⟩
  -- 4. the collar of width `δ'`
  refine gp2_collar_of_reduced hcirc.periodic hδ'pos fun θ hθ η hd hpi hne heq => ?_
  by_cases hclose : |θ - η| < δ
  · obtain ⟨i, hi⟩ := hleb θ (Ico_subset_Icc_self hθ)
    have hinj := gp2_injOn_front_of_cert hcirc.smooth hleg (hcerta i.1 i.2)
    exact hne (hinj (Ioo_subset_Icc_self (hi (Metric.mem_ball_self hδpos)))
      (Ioo_subset_Icc_self (hi (by rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]; exact hclose)))
      heq)
  · exact hfara θ (Ico_subset_Icc_self hθ) η (not_lt.1 hclose) hd.le hpi heq

/-- LEAF P2.2.  `Stage1` and the collar persist for small parameters of any Hamiltonian family
(sm-3:2675-2677, 2709-2710): the sign margins are open conditions in `a` on compact `θ`-intervals
(joint smoothness of `(θ,a) ↦ Φ_a(L θ)`, `generalized_tube_lemma`). -/
theorem stage1_stable {L : ℝ → ℝ³} (h : Stage1 L) {δc : ℝ} (hδ : LocallyInjectiveFront L δc)
    (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (hHs : ∀ i, ContactMotionsHyp (Hs i)) :
    ∃ r > 0, ∀ a : ℝ^m, ‖a‖ < r →
      Stage1 (composeFlows m Hs (par a) ∘ L) ∧ LocallyInjectiveFront (composeFlows m Hs (par a) ∘ L) δc := by
  -- FALSE as stated (GF_U_P2_REPORT.md §2: a double point at circular distance exactly `δc`).
  -- Use `gp2_stage1_stable_of_lt` (collar with any `δ' < δc`) together with
  -- `gp2_locallyInjectiveFront_mono` in the assembly instead.
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
