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


/-! ### Unit P3 helpers: local models of `X_H` -/

theorem gp3_hamVF_congr {H₁ H₂ : ℝ³ → ℝ} {p : ℝ³} (h : H₁ =ᶠ[𝓝 p] H₂) :
    hamVF H₁ p = hamVF H₂ p := by
  simp only [hamVF, ContactMotions.pd, h.fderiv_eq, h.eq_of_nhds]

theorem gp3_hamVF_eq_zero_of_notMem {H : ℝ³ → ℝ} {p : ℝ³} (hp : p ∉ tsupport H) :
    hamVF H p = 0 := by
  have h0 : H p = 0 := image_eq_zero_of_notMem_tsupport hp
  ext i
  fin_cases i <;> simp [ContactMotions.pd_eq_zero_of_notMem hp, h0]

theorem gp3_hamVF_Hx (c : ℝ) (p : ℝ³) : hamVF (fun p : ℝ³ => -(p 1 - c)) p = !₂[1, 0, c] := by
  have hd : HasFDerivAt (fun p : ℝ³ => -(p 1 - c)) (-(ContactMotions.coordCLM 1)) p :=
    ((ContactMotions.hasFDerivAt_coord 1 p).sub_const c).neg
  simp only [hamVF, ContactMotions.pd, hd.fderiv]
  ext i
  fin_cases i <;> simp [ContactMotions.e_apply]

theorem gp3_hamVF_Hz (p : ℝ³) : hamVF (fun _ : ℝ³ => (1 : ℝ)) p = !₂[0, 0, 1] := by
  ext i
  fin_cases i <;> simp [ContactMotions.pd]

theorem gp3_pd_H2 (c : ℝ) (p : ℝ³) (i : Fin 3) :
    ContactMotions.pd (fun p : ℝ³ => -(1 / 2) * (p 1 - c) ^ 2) i p =
      -(p 1 - c) * ContactMotions.e i 1 := by
  have hd : HasFDerivAt (fun p : ℝ³ => -(1 / 2) * (p 1 - c) ^ 2)
      ((-(1 / 2 : ℝ)) • ((2 : ℕ) • (p 1 - c) ^ (2 - 1)) • ContactMotions.coordCLM 1) p :=
    (((ContactMotions.hasFDerivAt_coord 1 p).sub_const c).pow 2).const_mul (-(1 / 2 : ℝ))
  simp only [ContactMotions.pd, hd.fderiv]
  simp

theorem gp3_hamVF_H2 (c : ℝ) (p : ℝ³) :
    hamVF (fun p : ℝ³ => -(1 / 2) * (p 1 - c) ^ 2) p =
      !₂[p 1 - c, 0, -(1 / 2) * (p 1 - c) ^ 2 + p 1 * (p 1 - c)] := by
  simp only [hamVF, gp3_pd_H2]
  ext i
  fin_cases i
  · simp
  · simp
  · simp [ContactMotions.e_apply]; ring

theorem gp3_hamVF_H2_zero (c : ℝ) (p : ℝ³) :
    hamVF (fun p : ℝ³ => -(1 / 2) * (p 1 - c) ^ 2) p 0 = p 1 - c := by
  rw [gp3_hamVF_H2]; simp

theorem gp3_hamVF_H2_at (c : ℝ) (p : ℝ³) (hp : p 1 = c) :
    hamVF (fun p : ℝ³ => -(1 / 2) * (p 1 - c) ^ 2) p = 0 := by
  rw [gp3_hamVF_H2, hp]
  ext i
  fin_cases i <;> simp

/-- LEAF P3.1 (local tool).  Hamiltonians equal near `q` to `H^x = −(y − y_q)` and `H^z = 1` have
`X_H = (1, 0, y_q)` and `(0, 0, 1)` at points where the bump is `1` (sm-3:2699-2701); `H₂ = −½(y−y₀)²`
has `x`-velocity `y − y₀` and vanishes where `y = y₀` (sm-3:2641-2646). -/
theorem hamVF_local_models (q : ℝ³) (χ : ℝ³ → ℝ) (hχ : χ =ᶠ[𝓝 q] 1) :
    hamVF (fun p => χ p * (-(p 1 - q 1))) q = !₂[1, 0, q 1] ∧
    hamVF (fun p => χ p * 1) q = !₂[0, 0, 1] ∧
    hamVF (fun p => χ p * (-(1 / 2) * (p 1 - q 1) ^ 2)) q = 0 := by
  have hc : ∀ f : ℝ³ → ℝ, (fun p => χ p * f p) =ᶠ[𝓝 q] f := fun f =>
    hχ.mono fun p hp => by simp [hp]
  refine ⟨?_, ?_, ?_⟩
  · rw [gp3_hamVF_congr (hc _), gp3_hamVF_Hx]
  · rw [gp3_hamVF_congr (hc fun _ => 1), gp3_hamVF_Hz]
  · rw [gp3_hamVF_congr (hc _), gp3_hamVF_H2_at _ _ rfl]


/-! ### Unit P3 helpers: circular distance -/

theorem gp3_circDist_eq (θ η : ℝ) :
    circDist θ η = 2 * π * min (Int.fract ((θ - η) / (2 * π))) (1 - Int.fract ((θ - η) / (2 * π))) := by
  unfold circDist
  set u := (θ - η) / (2 * π) with hu
  have h2 : θ - η = 2 * π * u := by rw [hu]; field_simp
  rw [← abs_sub_round_eq_min, h2, ← mul_sub, abs_mul, abs_of_pos two_pi_pos]

theorem gp3_continuous_circDist : Continuous fun z : ℝ × ℝ => circDist z.1 z.2 := by
  have hf : Continuous ((fun u : ℝ => min u (1 - u)) ∘ Int.fract) :=
    ContinuousOn.comp_fract'' (continuous_id.min (continuous_const.sub continuous_id)).continuousOn
      (by norm_num)
  have : (fun z : ℝ × ℝ => circDist z.1 z.2) =
      fun z => 2 * π * ((fun u : ℝ => min u (1 - u)) ∘ Int.fract) ((z.1 - z.2) / (2 * π)) := by
    funext z; rw [gp3_circDist_eq]; rfl
  rw [this]
  exact continuous_const.mul (hf.comp ((continuous_fst.sub continuous_snd).div_const _))

theorem gp3_circDist_eq_zero_of_sameParam {θ η : ℝ} (h : SameParam θ η) : circDist θ η = 0 := by
  obtain ⟨k, hk⟩ := h
  have : (θ - η) / (2 * π) = ((-k : ℤ) : ℝ) := by
    rw [hk]; push_cast; field_simp; ring
  unfold circDist
  rw [this, round_intCast, hk]; push_cast; ring_nf; simp

theorem gp3_not_sameParam_of_le_circDist {δ θ η : ℝ} (hδ : 0 < δ) (h : δ ≤ circDist θ η) :
    ¬ SameParam θ η := fun hs => by
  rw [gp3_circDist_eq_zero_of_sameParam hs] at h; linarith

/-- The coordinate functional `z ↦ z i` on `ℝ^d`. -/
def gp3_proj (d : ℕ) (i : Fin d) : ℝ^d →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin d => ℝ) i

@[simp] theorem gp3_proj_apply (d : ℕ) (i : Fin d) (z : ℝ^d) : gp3_proj d i z = z i := rfl

theorem gp3_continuous_apply (d : ℕ) (i : Fin d) : Continuous fun z : ℝ^d => z i :=
  (gp3_proj d i).continuous

theorem gp3_contDiff_apply (d : ℕ) (i : Fin d) : ContDiff ℝ ∞ fun z : ℝ^d => z i :=
  (gp3_proj d i).contDiff

theorem gp3_isCompact_box (d : ℕ) : IsCompact {z : ℝ^d | ∀ i, z i ∈ Icc 0 (2 * π)} := by
  have h : IsCompact (Set.pi univ fun _ : Fin d => Icc (0 : ℝ) (2 * π)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have h2 := h.image (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.continuous
  refine h2.of_isClosed_subset ?_ ?_
  · have : {z : ℝ^d | ∀ i, z i ∈ Icc 0 (2 * π)} = ⋂ i, (fun z : ℝ^d => z i) ⁻¹' Icc 0 (2 * π) := by
      ext z; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_Icc.preimage (gp3_continuous_apply d i)
  · intro z hz
    exact ⟨WithLp.ofLp z, fun i _ => hz i, rfl⟩

theorem gp3_isCompact_K2 (δc : ℝ) : IsCompact (K2 δc) := by
  refine (gp3_isCompact_box 2).of_isClosed_subset ?_ ?_
  · unfold K2
    refine IsClosed.inter (isClosed_Icc.preimage (gp3_continuous_apply 2 0))
      (IsClosed.inter (isClosed_Icc.preimage (gp3_continuous_apply 2 1)) ?_)
    exact isClosed_le continuous_const (gp3_continuous_circDist.comp
      ((gp3_continuous_apply 2 0).prodMk (gp3_continuous_apply 2 1)))
  · rintro z ⟨h0, h1, -⟩ i
    fin_cases i <;> assumption

theorem gp3_isCompact_K3 (δc : ℝ) : IsCompact (K3 δc) := by
  refine (gp3_isCompact_box 3).of_isClosed_subset ?_ ?_
  · unfold K3
    have hc : ∀ i j : Fin 3, IsClosed {z : ℝ^3 | δc ≤ circDist (z i) (z j)} := fun i j =>
      isClosed_le continuous_const (gp3_continuous_circDist.comp
        ((gp3_continuous_apply 3 i).prodMk (gp3_continuous_apply 3 j)))
    have hI : ∀ i : Fin 3, IsClosed {z : ℝ^3 | z i ∈ Icc 0 (2 * π)} := fun i =>
      isClosed_Icc.preimage (gp3_continuous_apply 3 i)
    exact (hI 0).inter ((hI 1).inter ((hI 2).inter ((hc 0 1).inter ((hc 0 2).inter (hc 1 2)))))
  · rintro z ⟨h0, h1, h2, -, -, -⟩ i
    fin_cases i <;> assumption


theorem gp3_xParam_eq (L : ℝ → ℝ³) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (a : Fin m → ℝ) :
    xParam L m Hs a = coordX (composeFlows m Hs a ∘ L) := rfl

theorem gp3_frontParam_eq (L : ℝ → ℝ³) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (a : Fin m → ℝ) :
    frontParam L m Hs a = front (composeFlows m Hs a ∘ L) := rfl


/-! ### Unit P3 helpers: partial derivatives of jointly smooth maps -/

section gp3_partial

variable {A B E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
  [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem gp3_fderiv_slice_left {f : A × B → F} {a : A} {b : B} (hf : DifferentiableAt ℝ f (a, b))
    (v : A) : fderiv ℝ (fun a => f (a, b)) a v = fderiv ℝ f (a, b) (v, 0) := by
  have h : HasFDerivAt (fun a => f (a, b))
      ((fderiv ℝ f (a, b)).comp (ContinuousLinearMap.inl ℝ A B)) a :=
    hf.hasFDerivAt.comp a (hasFDerivAt_prodMk_left a b)
  rw [h.fderiv]; rfl

theorem gp3_deriv_slice_right {f : A × ℝ → F} {a : A} {t : ℝ} (hf : DifferentiableAt ℝ f (a, t)) :
    deriv (fun t => f (a, t)) t = fderiv ℝ f (a, t) (0, 1) := by
  have h : HasDerivAt (fun t => f (a, t)) (fderiv ℝ f (a, t) (0, 1)) t :=
    hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t a).prodMk (hasDerivAt_id t))
  exact h.deriv

theorem gp3_fderiv_comp_clm {g : E → F} (σ : A →L[ℝ] E) {z : A} (hg : DifferentiableAt ℝ g (σ z))
    (v : A) : fderiv ℝ (fun z => g (σ z)) z v = fderiv ℝ g (σ z) (σ v) := by
  have h : HasFDerivAt (fun z => g (σ z)) ((fderiv ℝ g (σ z)).comp σ) z :=
    hg.hasFDerivAt.comp z σ.hasFDerivAt
  rw [h.fderiv]; rfl

/-- Symmetry of the second derivative of a `C^∞` map, in the "partial derivative" form. -/
theorem gp3_fderiv_fderiv_comm {f : E → F} (hf : ContDiff ℝ ∞ f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fun y => fderiv ℝ f y v) x w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have h1 : ∀ u : E, fderiv ℝ (fun y => fderiv ℝ f y u) x = (fderiv ℝ (fderiv ℝ f) x).flip u := by
    intro u
    rw [fderiv_clm_apply hd (differentiableAt_const u)]
    simp
  rw [h1, h1]
  simp only [ContinuousLinearMap.flip_apply]
  exact hf.contDiffAt.isSymmSndFDerivAt ContactMotions.minSmoothness_two_le v w

theorem gp3_contDiff_fderiv_apply {f : E → F} (hf : ContDiff ℝ ∞ f) (w : E) :
    ContDiff ℝ ∞ fun y => fderiv ℝ f y w :=
  (hf.contDiff_fderiv_apply (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)

theorem gp3_fderiv_apply_coord {n : ℕ} {f : A → ℝ^n} {p : A} (hf : DifferentiableAt ℝ f p) (v : A)
    (i : Fin n) : fderiv ℝ f p v i = fderiv ℝ (fun q => f q i) p v := by
  have h : HasFDerivAt (fun q => f q i) ((gp3_proj n i).comp (fderiv ℝ f p)) p :=
    (gp3_proj n i).hasFDerivAt.comp p hf.hasFDerivAt
  rw [h.fderiv]; rfl

end gp3_partial

/-! ### Unit P3 helpers: the joint map `(a, θ) ↦ Φ_a(L θ)` and the derivatives of `C`, `R` -/

/-- The joint map `(a, θ) ↦ Φ_a(L θ)`. -/
def gp3_G (L : ℝ → ℝ³) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (q : (Fin m → ℝ) × ℝ) : ℝ³ :=
  composeFlows m Hs q.1 (L q.2)

/-- Its `k`-th coordinate. -/
def gp3_Gk (L : ℝ → ℝ³) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (k : Fin 3) (q : (Fin m → ℝ) × ℝ) : ℝ :=
  gp3_G L m Hs q k

theorem gp3_contDiff_G {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) : ContDiff ℝ ∞ (gp3_G L m Hs) :=
  (fd_contact_motions.compositions_smooth m Hs hHs).comp (contDiff_fst.prodMk (hL.comp contDiff_snd))

theorem gp3_contDiff_Gk {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) (k : Fin 3) : ContDiff ℝ ∞ (gp3_Gk L m Hs k) :=
  (ContactMotions.contDiff_coord k).comp (gp3_contDiff_G hL m Hs hHs)

/-- The linear slice map `z ↦ (a, θ_j)` from `ℝ^d × ℝ^m` to `(Fin m → ℝ) × ℝ`. -/
def gp3_σ (d m : ℕ) (j : Fin d) : ℝ^d × ℝ^m →L[ℝ] (Fin m → ℝ) × ℝ :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ) : ℝ^m →L[ℝ] (Fin m → ℝ)).comp
    (ContinuousLinearMap.snd ℝ (ℝ^d) (ℝ^m))).prod
    ((gp3_proj d j).comp (ContinuousLinearMap.fst ℝ (ℝ^d) (ℝ^m)))

theorem gp3_σ_apply (d m : ℕ) (j : Fin d) (z : ℝ^d × ℝ^m) :
    gp3_σ d m j z = (par z.2, z.1 j) := rfl

theorem gp3_par_zero (m : ℕ) : par (0 : ℝ^m) = 0 := by ext; simp [par]

theorem gp3_par_single (m : ℕ) (i : Fin m) : par (EuclideanSpace.single i (1 : ℝ)) = Pi.single i 1 := by
  ext j; simp [par, Pi.single_apply]

theorem gp3_σ_zero (d m : ℕ) (j : Fin d) (t : ℝ^d) : gp3_σ d m j (t, 0) = (0, t j) := by
  simp [gp3_σ_apply, gp3_par_zero]

theorem gp3_σ_single (d m : ℕ) (j : Fin d) (i : Fin m) :
    gp3_σ d m j (0, EuclideanSpace.single i 1) = (Pi.single i 1, 0) := by
  simp [gp3_σ_apply, gp3_par_single]

theorem gp3_xParam_deriv {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) (a : Fin m → ℝ) (θ : ℝ) :
    deriv (xParam L m Hs a) θ = fderiv ℝ (gp3_Gk L m Hs 0) (a, θ) (0, 1) :=
  gp3_deriv_slice_right (((gp3_contDiff_Gk hL m Hs hHs 0).differentiable (by simp)).differentiableAt)

/-- `∂_{a_i} Φ_a(L θ)_k |_{a=0} = X_{H_i}(L θ)_k` (P0.3 in the joint-map form). -/
theorem gp3_fderiv_Gk_zero {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) (k : Fin 3) (θ : ℝ) (i : Fin m) :
    fderiv ℝ (gp3_Gk L m Hs k) (0, θ) (Pi.single i 1, 0) = hamVF (Hs i) (L θ) k := by
  rw [← gp3_fderiv_slice_left (((gp3_contDiff_Gk hL m Hs hHs k).differentiable (by simp)).differentiableAt)]
  have hdiff : DifferentiableAt ℝ (fun a : Fin m → ℝ => composeFlows m Hs a (L θ)) 0 :=
    (((fd_contact_motions.compositions_smooth m Hs hHs).comp
      (contDiff_id.prodMk contDiff_const)).differentiable (by simp)).differentiableAt
  have := ContactMotions.fderiv_apply_coord hdiff (Pi.single i 1) k
  rw [fderiv_composeFlows_zero m Hs hHs (L θ) i] at this
  exact this.symm

/-- `Cmap` in terms of the joint map. -/
theorem gp3_Cmap_eq {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) :
    Cmap L m Hs = fun z => !₂[fderiv ℝ (gp3_Gk L m Hs 0) (gp3_σ 2 m 0 z) (0, 1),
      gp3_Gk L m Hs 0 (gp3_σ 2 m 0 z) - gp3_Gk L m Hs 0 (gp3_σ 2 m 1 z),
      gp3_Gk L m Hs 2 (gp3_σ 2 m 0 z) - gp3_Gk L m Hs 2 (gp3_σ 2 m 1 z)] := by
  funext z
  simp only [Cmap, gp3_xParam_deriv hL m Hs hHs, gp3_σ_apply]
  rfl

/-- `Rmap` in terms of the joint map. -/
theorem gp3_Rmap_eq (L : ℝ → ℝ³) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) :
    Rmap L m Hs = fun z => !₂[gp3_Gk L m Hs 0 (gp3_σ 3 m 0 z) - gp3_Gk L m Hs 0 (gp3_σ 3 m 1 z),
      gp3_Gk L m Hs 2 (gp3_σ 3 m 0 z) - gp3_Gk L m Hs 2 (gp3_σ 3 m 1 z),
      gp3_Gk L m Hs 0 (gp3_σ 3 m 0 z) - gp3_Gk L m Hs 0 (gp3_σ 3 m 2 z),
      gp3_Gk L m Hs 2 (gp3_σ 3 m 0 z) - gp3_Gk L m Hs 2 (gp3_σ 3 m 2 z)] := by
  funext z; rfl

theorem gp3_contDiff_Cmap {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) : ContDiff ℝ ∞ (Cmap L m Hs) := by
  rw [gp3_Cmap_eq hL m Hs hHs]
  have hG0 := gp3_contDiff_Gk hL m Hs hHs 0
  have hG2 := gp3_contDiff_Gk hL m Hs hHs 2
  have hd := gp3_contDiff_fderiv_apply hG0 (0, 1)
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · exact hd.comp (gp3_σ 2 m 0).contDiff
  · exact (hG0.comp (gp3_σ 2 m 0).contDiff).sub (hG0.comp (gp3_σ 2 m 1).contDiff)
  · exact (hG2.comp (gp3_σ 2 m 0).contDiff).sub (hG2.comp (gp3_σ 2 m 1).contDiff)

theorem gp3_contDiff_Rmap {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) : ContDiff ℝ ∞ (Rmap L m Hs) := by
  rw [gp3_Rmap_eq L m Hs]
  have hG0 := gp3_contDiff_Gk hL m Hs hHs 0
  have hG2 := gp3_contDiff_Gk hL m Hs hHs 2
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · exact (hG0.comp (gp3_σ 3 m 0).contDiff).sub (hG0.comp (gp3_σ 3 m 1).contDiff)
  · exact (hG2.comp (gp3_σ 3 m 0).contDiff).sub (hG2.comp (gp3_σ 3 m 1).contDiff)
  · exact (hG0.comp (gp3_σ 3 m 0).contDiff).sub (hG0.comp (gp3_σ 3 m 2).contDiff)
  · exact (hG2.comp (gp3_σ 3 m 0).contDiff).sub (hG2.comp (gp3_σ 3 m 2).contDiff)

/-- The column of `∂_a C` at `a = 0` contributed by one Hamiltonian `H`:
`(∂_θ (X_H(L θ))_x, X_H(L θ)_x − X_H(L η)_x, X_H(L θ)_z − X_H(L η)_z)`. -/
def gp3_colC (L : ℝ → ℝ³) (H : ℝ³ → ℝ) (θ η : ℝ) : ℝ^3 :=
  !₂[deriv (fun θ => hamVF H (L θ) 0) θ, hamVF H (L θ) 0 - hamVF H (L η) 0,
    hamVF H (L θ) 2 - hamVF H (L η) 2]

/-- The column of `∂_a R` at `a = 0` contributed by one Hamiltonian `H`. -/
def gp3_colR (L : ℝ → ℝ³) (H : ℝ³ → ℝ) (θ η τ : ℝ) : ℝ^4 :=
  !₂[hamVF H (L θ) 0 - hamVF H (L η) 0, hamVF H (L θ) 2 - hamVF H (L η) 2,
    hamVF H (L θ) 0 - hamVF H (L τ) 0, hamVF H (L θ) 2 - hamVF H (L τ) 2]

/-- The difference-of-coordinates component of `∂_a C`, `∂_a R` at `a = 0`. -/
theorem gp3_fderiv_diff_zero {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) (k : Fin 3) {d : ℕ} (j j' : Fin d) (t : ℝ^d) (i : Fin m) :
    fderiv ℝ (fun z : ℝ^d × ℝ^m => gp3_Gk L m Hs k (gp3_σ d m j z) - gp3_Gk L m Hs k (gp3_σ d m j' z))
      (t, 0) (0, EuclideanSpace.single i 1) = hamVF (Hs i) (L (t j)) k - hamVF (Hs i) (L (t j')) k := by
  have hG := gp3_contDiff_Gk hL m Hs hHs k
  have hd : ∀ j : Fin d, DifferentiableAt ℝ (fun z : ℝ^d × ℝ^m => gp3_Gk L m Hs k (gp3_σ d m j z)) (t, 0) :=
    fun j => ((hG.comp (gp3_σ d m j).contDiff).differentiable (by simp)).differentiableAt
  rw [fderiv_fun_sub (hd j) (hd j'), sub_apply,
    gp3_fderiv_comp_clm (g := gp3_Gk L m Hs k) (gp3_σ d m j) (hG.differentiable (by simp)).differentiableAt,
    gp3_fderiv_comp_clm (g := gp3_Gk L m Hs k) (gp3_σ d m j') (hG.differentiable (by simp)).differentiableAt,
    gp3_σ_zero, gp3_σ_zero, gp3_σ_single, gp3_σ_single, gp3_fderiv_Gk_zero hL m Hs hHs,
    gp3_fderiv_Gk_zero hL m Hs hHs]

/-- The `x_a′(θ)` component of `∂_a C` at `a = 0`: `∂_θ (X_{H_i}(L θ))_x` (mixed partials commute). -/
theorem gp3_fderiv_xderiv_zero {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) {d : ℕ} (j : Fin d) (t : ℝ^d) (i : Fin m) :
    fderiv ℝ (fun z : ℝ^d × ℝ^m => fderiv ℝ (gp3_Gk L m Hs 0) (gp3_σ d m j z) (0, 1))
      (t, 0) (0, EuclideanSpace.single i 1) = deriv (fun θ => hamVF (Hs i) (L θ) 0) (t j) := by
  have hG := gp3_contDiff_Gk hL m Hs hHs 0
  have hg := gp3_contDiff_fderiv_apply hG (0, 1)
  rw [gp3_fderiv_comp_clm (g := fun y => fderiv ℝ (gp3_Gk L m Hs 0) y (0, 1)) (gp3_σ d m j)
    (hg.differentiable (by simp)).differentiableAt, gp3_σ_zero, gp3_σ_single,
    gp3_fderiv_fderiv_comm hG]
  have hg' := gp3_contDiff_fderiv_apply hG (Pi.single i 1, 0)
  rw [← gp3_deriv_slice_right (hg'.differentiable (by simp)).differentiableAt]
  congr 1
  funext θ
  exact gp3_fderiv_Gk_zero hL m Hs hHs 0 θ i

theorem gp3_fderiv_Cmap_zero {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) (t : ℝ^2) (i : Fin m) :
    fderiv ℝ (Cmap L m Hs) (t, 0) (0, EuclideanSpace.single i 1) = gp3_colC L (Hs i) (t 0) (t 1) := by
  have hdC : DifferentiableAt ℝ (Cmap L m Hs) (t, 0) :=
    ((gp3_contDiff_Cmap hL m Hs hHs).differentiable (by simp)).differentiableAt
  ext k
  rw [gp3_fderiv_apply_coord hdC]
  simp only [gp3_Cmap_eq hL m Hs hHs]
  fin_cases k
  · simpa [gp3_colC] using gp3_fderiv_xderiv_zero hL m Hs hHs (0 : Fin 2) t i
  · simpa [gp3_colC] using gp3_fderiv_diff_zero hL m Hs hHs 0 (0 : Fin 2) 1 t i
  · simpa [gp3_colC] using gp3_fderiv_diff_zero hL m Hs hHs 2 (0 : Fin 2) 1 t i

theorem gp3_fderiv_Rmap_zero {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) (t : ℝ^3) (i : Fin m) :
    fderiv ℝ (Rmap L m Hs) (t, 0) (0, EuclideanSpace.single i 1) =
      gp3_colR L (Hs i) (t 0) (t 1) (t 2) := by
  have hdR : DifferentiableAt ℝ (Rmap L m Hs) (t, 0) :=
    ((gp3_contDiff_Rmap hL m Hs hHs).differentiable (by simp)).differentiableAt
  ext k
  rw [gp3_fderiv_apply_coord hdR]
  simp only [gp3_Rmap_eq L m Hs]
  fin_cases k
  · simpa [gp3_colR] using gp3_fderiv_diff_zero hL m Hs hHs 0 (0 : Fin 3) 1 t i
  · simpa [gp3_colR] using gp3_fderiv_diff_zero hL m Hs hHs 2 (0 : Fin 3) 1 t i
  · simpa [gp3_colR] using gp3_fderiv_diff_zero hL m Hs hHs 0 (0 : Fin 3) 2 t i
  · simpa [gp3_colR] using gp3_fderiv_diff_zero hL m Hs hHs 2 (0 : Fin 3) 2 t i


/-! ### Unit P3 helpers: from independent columns at `a = 0` to `ParameterAvoidanceHyp` -/

theorem gp3_finrank_of_indep {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {q : ℕ}
    (f : X →L[ℝ] ℝ^q) {v : Fin q → X} (h : LinearIndependent ℝ (fun j => f (v j))) :
    Module.finrank ℝ f.range = q := by
  have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range fun j => f (v j))) = q := by
    rw [finrank_span_eq_card h, Fintype.card_fin]
  have h2 : Submodule.span ℝ (Set.range fun j => f (v j)) ≤ f.range := by
    rw [Submodule.span_le]; rintro _ ⟨j, rfl⟩; exact LinearMap.mem_range_self (f : X →ₗ[ℝ] ℝ^q) (v j)
  have h3 := Submodule.finrank_mono h2
  have h4 : Module.finrank ℝ f.range ≤ q := by
    have := Submodule.finrank_le f.range; rwa [finrank_euclideanSpace_fin] at this
  omega

theorem gp3_isOpen_indep {d m q : ℕ} {F : ℝ^d × ℝ^m → ℝ^q} (hF : ContDiff ℝ ∞ F) (ι : Fin q → Fin m) :
    IsOpen {z | LinearIndependent ℝ (fun j => fderiv ℝ F z (0, EuclideanSpace.single (ι j) 1))} := by
  have hc : Continuous fun z => (fun j => fderiv ℝ F z (0, EuclideanSpace.single (ι j) 1)) :=
    continuous_pi fun j => (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  exact isOpen_setOfPred_linearIndependent.preimage hc

/-- The compactness/shrinking step: if at every zero over `a = 0` some `q` parameter columns are
independent, then for a small parameter ball every zero has parameter rank `q`, and the
`ParameterAvoidanceHyp` holds for every smaller radius. -/
theorem gp3_exists_paHyp {d m q : ℕ} {K : Set (ℝ^d)} (hK : IsCompact K) {F : ℝ^d × ℝ^m → ℝ^q}
    (hF : ContDiff ℝ ∞ F) (hdq : d < q) {κ : Type*} (ι : κ → Fin q → Fin m)
    (h0 : ∀ t ∈ K, F (t, 0) = 0 → ∃ k, LinearIndependent ℝ
      (fun j => fderiv ℝ F (t, 0) (0, EuclideanSpace.single (ι k j) 1))) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r → ParameterAvoidanceHyp d m q K 0 r' F := by
  set W : Set (ℝ^d × ℝ^m) := ⋃ k, {z | LinearIndependent ℝ
    (fun j => fderiv ℝ F z (0, EuclideanSpace.single (ι k j) 1))} with hW
  have hWo : IsOpen W := isOpen_iUnion fun k => gp3_isOpen_indep hF (ι k)
  have hWrank : ∀ z ∈ W, Module.finrank ℝ (fderiv ℝ F z).range = q := by
    intro z hz
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hz
    exact gp3_finrank_of_indep _ hk
  have h0W : ∀ t ∈ K, F (t, 0) = 0 → (t, 0) ∈ W := fun t ht hF0 => by
    obtain ⟨k, hk⟩ := h0 t ht hF0
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  set S := (K ×ˢ Metric.closedBall (0 : ℝ^m) 1) ∩ F ⁻¹' {0} ∩ Wᶜ with hS
  have hSc : IsCompact S :=
    ((hK.prod (isCompact_closedBall 0 1)).inter_right
      (isClosed_singleton.preimage hF.continuous)).inter_right hWo.isClosed_compl
  have key : ∃ r > 0, r ≤ 1 ∧ ∀ z ∈ K ×ˢ Metric.closedBall (0 : ℝ^m) r, F z = 0 → z ∈ W := by
    rcases S.eq_empty_or_nonempty with hS0 | hSne
    · refine ⟨1, one_pos, le_rfl, fun z hz hz0 => ?_⟩
      by_contra hzW
      have : z ∈ S := ⟨⟨hz, hz0⟩, hzW⟩
      rw [hS0] at this
      exact this
    · obtain ⟨z₀, hz₀S, hmin⟩ := hSc.exists_isMinOn hSne continuous_snd.norm.continuousOn
      have hz₀ : 0 < ‖z₀.2‖ := by
        rw [norm_pos_iff]
        intro h2
        apply hz₀S.2
        have hz₀' : z₀ = (z₀.1, 0) := by ext <;> simp [h2]
        rw [hz₀']
        exact h0W z₀.1 hz₀S.1.1.1 (by rw [← hz₀']; exact hz₀S.1.2)
      refine ⟨min 1 (‖z₀.2‖ / 2), by positivity, min_le_left _ _, fun z hz hz0 => ?_⟩
      by_contra hzW
      have hzS : z ∈ S :=
        ⟨⟨⟨hz.1, Metric.closedBall_subset_closedBall (min_le_left _ _) hz.2⟩, hz0⟩, hzW⟩
      have h1 : ‖z₀.2‖ ≤ ‖z.2‖ := hmin hzS
      have h2 : ‖z.2‖ ≤ min 1 (‖z₀.2‖ / 2) := by simpa using hz.2
      have h3 := min_le_right 1 (‖z₀.2‖ / 2)
      linarith
  obtain ⟨r, hr, -, hW'⟩ := key
  refine ⟨r, hr, fun r' hr' hr'r => ?_⟩
  exact { compact := hK
          smooth := ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
          rank := fun z hz hz0 =>
            hWrank z (hW' z ⟨hz.1, Metric.closedBall_subset_closedBall hr'r hz.2⟩ hz0)
          dim_lt := hdq }

/-! ### Unit P3 helpers: bumps and the local Hamiltonians at a zero -/

theorem gp3_exists_bump (c : ℝ³) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ χ : ℝ³ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ χ =ᶠ[𝓝 c] 1 ∧
      tsupport χ ⊆ Metric.closedBall c ρ := by
  let b : ContDiffBump c := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  exact ⟨b, b.contDiff, b.hasCompactSupport, b.eventuallyEq_one, b.tsupport_eq.le⟩

/-- `χ · f` is an admissible Hamiltonian. -/
theorem gp3_hyp_of_bump {χ : ℝ³ → ℝ} (hχs : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    {f : ℝ³ → ℝ} (hf : ContDiff ℝ ∞ f) : ContactMotionsHyp (fun p => χ p * f p) :=
  ⟨hχs.mul hf, hχc.mul_right⟩

/-- Far from the bump's centre, `X_{χ f} = 0`. -/
theorem gp3_hamVF_bump_far {χ : ℝ³ → ℝ} {c : ℝ³} {ρ : ℝ} (hχ : tsupport χ ⊆ Metric.closedBall c ρ)
    {f : ℝ³ → ℝ} {p : ℝ³} (hp : ρ < dist p c) : hamVF (fun p => χ p * f p) p = 0 := by
  apply gp3_hamVF_eq_zero_of_notMem
  intro hmem
  have := hχ (tsupport_mul_subset_left hmem)
  rw [Metric.mem_closedBall] at this
  linarith

/-- Where the bump is `1` near `p`, `X_{χ f}(p) = X_f(p)`. -/
theorem gp3_hamVF_bump_near {χ : ℝ³ → ℝ} {f : ℝ³ → ℝ} {p : ℝ³} (hp : χ =ᶠ[𝓝 p] 1) :
    hamVF (fun p => χ p * f p) p = hamVF f p :=
  gp3_hamVF_congr (hp.mono fun q hq => by simp [hq])

theorem gp3_eventually_near {L : ℝ → ℝ³} (hL : Continuous L) {χ : ℝ³ → ℝ} {θ₀ : ℝ}
    (hχ : χ =ᶠ[𝓝 (L θ₀)] 1) : ∀ᶠ θ in 𝓝 θ₀, χ =ᶠ[𝓝 (L θ)] 1 :=
  hL.continuousAt.eventually hχ.eventually_nhds

theorem gp3_eventually_far {L : ℝ → ℝ³} (hL : Continuous L) {c : ℝ³} {ρ : ℝ} {θ₀ : ℝ}
    (h : ρ < dist (L θ₀) c) : ∀ᶠ θ in 𝓝 θ₀, ρ < dist (L θ) c :=
  continuousAt_const.eventually_lt (hL.continuousAt.dist continuousAt_const) h

/-- The chart at a zero of `C`: three Hamiltonians with independent columns (sm-3:2695-2703). -/
theorem gp3_exists_C_chart {L : ℝ → ℝ³} (h : Stage1 L) {θ₀ η₀ : ℝ} (hx : deriv (coordX L) θ₀ = 0)
    (hne : L θ₀ ≠ L η₀) :
    ∃ H : Fin 3 → ℝ³ → ℝ, (∀ j, ContactMotionsHyp (H j)) ∧
      LinearIndependent ℝ (fun j => gp3_colC L (H j) θ₀ η₀) := by
  have hLc : Continuous L := h.circle.smooth.continuous
  have hy : deriv (coordY L) θ₀ ≠ 0 := deriv_y_ne_zero_at_cusp h hx
  have hdist : 0 < dist (L θ₀) (L η₀) := dist_pos.2 hne
  obtain ⟨χ₁, hχ₁s, hχ₁c, hχ₁e, hχ₁t⟩ := gp3_exists_bump (L θ₀) (half_pos hdist)
  obtain ⟨χ₂, hχ₂s, hχ₂c, hχ₂e, hχ₂t⟩ := gp3_exists_bump (L η₀) (half_pos hdist)
  have hfar1 : dist (L θ₀) (L η₀) / 2 < dist (L η₀) (L θ₀) := by rw [dist_comm (L η₀)]; linarith
  have hfar2 : dist (L θ₀) (L η₀) / 2 < dist (L θ₀) (L η₀) := by linarith
  have hfAs : ContDiff ℝ ∞ fun p : ℝ³ => -(1 / 2) * (p 1 - L θ₀ 1) ^ 2 :=
    contDiff_const.mul (((ContactMotions.contDiff_coord 1).sub contDiff_const).pow 2)
  have hfBs : ContDiff ℝ ∞ fun p : ℝ³ => -(p 1 - L η₀ 1) :=
    ((ContactMotions.contDiff_coord 1).sub contDiff_const).neg
  have cA : gp3_colC L (fun p => χ₁ p * (-(1 / 2) * (p 1 - L θ₀ 1) ^ 2)) θ₀ η₀ =
      !₂[deriv (coordY L) θ₀, 0, 0] := by
    have h1 : (fun θ => hamVF (fun p => χ₁ p * (-(1 / 2) * (p 1 - L θ₀ 1) ^ 2)) (L θ) 0) =ᶠ[𝓝 θ₀]
        fun θ => L θ 1 - L θ₀ 1 := by
      filter_upwards [gp3_eventually_near hLc hχ₁e] with θ hθ
      rw [gp3_hamVF_bump_near hθ, gp3_hamVF_H2_zero]
    have h2 : hamVF (fun p => χ₁ p * (-(1 / 2) * (p 1 - L θ₀ 1) ^ 2)) (L θ₀) = 0 := by
      rw [gp3_hamVF_bump_near hχ₁e, gp3_hamVF_H2_at _ _ rfl]
    have h3 : hamVF (fun p => χ₁ p * (-(1 / 2) * (p 1 - L θ₀ 1) ^ 2)) (L η₀) = 0 :=
      gp3_hamVF_bump_far hχ₁t hfar1
    have h4 : deriv (coordY L) θ₀ = deriv (fun θ => L θ 1 - L θ₀ 1) θ₀ := by
      rw [deriv_sub_const]; rfl
    simp only [gp3_colC, h1.deriv_eq, h2, h3, h4]
    ext i; fin_cases i <;> simp
  have cB : gp3_colC L (fun p => χ₂ p * (-(p 1 - L η₀ 1))) θ₀ η₀ = !₂[0, -1, -(L η₀ 1)] := by
    have h1 : (fun θ => hamVF (fun p => χ₂ p * (-(p 1 - L η₀ 1))) (L θ) 0) =ᶠ[𝓝 θ₀]
        fun _ => (0 : ℝ) := by
      filter_upwards [gp3_eventually_far hLc hfar2] with θ hθ
      rw [gp3_hamVF_bump_far hχ₂t hθ]; rfl
    have h2 : hamVF (fun p => χ₂ p * (-(p 1 - L η₀ 1))) (L θ₀) = 0 := gp3_hamVF_bump_far hχ₂t hfar2
    have h3 : hamVF (fun p => χ₂ p * (-(p 1 - L η₀ 1))) (L η₀) = !₂[1, 0, L η₀ 1] := by
      rw [gp3_hamVF_bump_near hχ₂e, gp3_hamVF_Hx]
    simp only [gp3_colC, h1.deriv_eq, h2, h3, deriv_const]
    ext i; fin_cases i <;> simp
  have cC : gp3_colC L (fun p => χ₂ p * 1) θ₀ η₀ = !₂[0, 0, -1] := by
    have h1 : (fun θ => hamVF (fun p => χ₂ p * 1) (L θ) 0) =ᶠ[𝓝 θ₀] fun _ => (0 : ℝ) := by
      filter_upwards [gp3_eventually_far hLc hfar2] with θ hθ
      rw [gp3_hamVF_bump_far hχ₂t hθ]; rfl
    have h2 : hamVF (fun p => χ₂ p * 1) (L θ₀) = 0 := gp3_hamVF_bump_far hχ₂t hfar2
    have h3 : hamVF (fun p => χ₂ p * 1) (L η₀) = !₂[0, 0, 1] := by
      rw [gp3_hamVF_bump_near hχ₂e, gp3_hamVF_Hz]
    simp only [gp3_colC, h1.deriv_eq, h2, h3, deriv_const]
    ext i; fin_cases i <;> simp
  refine ⟨![fun p => χ₁ p * (-(1 / 2) * (p 1 - L θ₀ 1) ^ 2), fun p => χ₂ p * (-(p 1 - L η₀ 1)),
    fun p => χ₂ p * 1], ?_, ?_⟩
  · intro j
    fin_cases j
    · exact gp3_hyp_of_bump hχ₁s hχ₁c hfAs
    · exact gp3_hyp_of_bump hχ₂s hχ₂c hfBs
    · exact gp3_hyp_of_bump hχ₂s hχ₂c contDiff_const
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • gp3_colC L (fun p => χ₁ p * (-(1 / 2) * (p 1 - L θ₀ 1) ^ 2)) θ₀ η₀ +
        g 1 • gp3_colC L (fun p => χ₂ p * (-(p 1 - L η₀ 1))) θ₀ η₀ +
        g 2 • gp3_colC L (fun p => χ₂ p * 1) θ₀ η₀ = 0 := by
      simp only [Fin.sum_univ_three] at hg
      exact hg
    rw [cA, cB, cC] at hg'
    have e0 := congrArg (fun v : ℝ^3 => v 0) hg'
    have e1 := congrArg (fun v : ℝ^3 => v 1) hg'
    have e2 := congrArg (fun v : ℝ^3 => v 2) hg'
    simp at e0 e1 e2
    have g0 : g 0 = 0 := e0.resolve_right hy
    have g1 : g 1 = 0 := e1
    have g2 : g 2 = 0 := by rw [g1] at e2; simpa using e2
    intro i
    fin_cases i <;> assumption

/-- The chart at a zero of `R`: four Hamiltonians with independent columns (sm-3:2703-2706). -/
theorem gp3_exists_R_chart (L : ℝ → ℝ³) {θ₀ η₀ τ₀ : ℝ}
    (h1 : L θ₀ ≠ L η₀) (h2 : L θ₀ ≠ L τ₀) (h3 : L η₀ ≠ L τ₀) :
    ∃ H : Fin 4 → ℝ³ → ℝ, (∀ j, ContactMotionsHyp (H j)) ∧
      LinearIndependent ℝ (fun j => gp3_colR L (H j) θ₀ η₀ τ₀) := by
  set ρ := min (min (dist (L θ₀) (L η₀)) (dist (L θ₀) (L τ₀))) (dist (L η₀) (L τ₀)) / 2 with hρ
  have hρpos : 0 < ρ := by
    have := dist_pos.2 h1; have := dist_pos.2 h2; have := dist_pos.2 h3
    positivity
  have hρ1 : ρ < dist (L θ₀) (L η₀) := by
    have := min_le_left (min (dist (L θ₀) (L η₀)) (dist (L θ₀) (L τ₀))) (dist (L η₀) (L τ₀))
    have := min_le_left (dist (L θ₀) (L η₀)) (dist (L θ₀) (L τ₀))
    linarith
  have hρ2 : ρ < dist (L θ₀) (L τ₀) := by
    have := min_le_left (min (dist (L θ₀) (L η₀)) (dist (L θ₀) (L τ₀))) (dist (L η₀) (L τ₀))
    have := min_le_right (dist (L θ₀) (L η₀)) (dist (L θ₀) (L τ₀))
    linarith
  have hρ3 : ρ < dist (L η₀) (L τ₀) := by
    have := min_le_right (min (dist (L θ₀) (L η₀)) (dist (L θ₀) (L τ₀))) (dist (L η₀) (L τ₀))
    linarith
  have hρ1' : ρ < dist (L η₀) (L θ₀) := by rwa [dist_comm]
  have hρ2' : ρ < dist (L τ₀) (L θ₀) := by rwa [dist_comm]
  have hρ3' : ρ < dist (L τ₀) (L η₀) := by rwa [dist_comm]
  obtain ⟨χ₂, hχ₂s, hχ₂c, hχ₂e, hχ₂t⟩ := gp3_exists_bump (L η₀) hρpos
  obtain ⟨χ₃, hχ₃s, hχ₃c, hχ₃e, hχ₃t⟩ := gp3_exists_bump (L τ₀) hρpos
  have hfBs : ∀ c : ℝ, ContDiff ℝ ∞ fun p : ℝ³ => -(p 1 - c) := fun c =>
    ((ContactMotions.contDiff_coord 1).sub contDiff_const).neg
  -- values of the four fields at the three points
  have vB2 : hamVF (fun p => χ₂ p * (-(p 1 - L η₀ 1))) (L η₀) = !₂[1, 0, L η₀ 1] := by
    rw [gp3_hamVF_bump_near hχ₂e, gp3_hamVF_Hx]
  have vC2 : hamVF (fun p => χ₂ p * 1) (L η₀) = !₂[0, 0, 1] := by
    rw [gp3_hamVF_bump_near hχ₂e, gp3_hamVF_Hz]
  have vB3 : hamVF (fun p => χ₃ p * (-(p 1 - L τ₀ 1))) (L τ₀) = !₂[1, 0, L τ₀ 1] := by
    rw [gp3_hamVF_bump_near hχ₃e, gp3_hamVF_Hx]
  have vC3 : hamVF (fun p => χ₃ p * 1) (L τ₀) = !₂[0, 0, 1] := by
    rw [gp3_hamVF_bump_near hχ₃e, gp3_hamVF_Hz]
  have c0 : gp3_colR L (fun p => χ₂ p * (-(p 1 - L η₀ 1))) θ₀ η₀ τ₀ = !₂[-1, -(L η₀ 1), 0, 0] := by
    simp only [gp3_colR, vB2, gp3_hamVF_bump_far hχ₂t hρ1, gp3_hamVF_bump_far hχ₂t hρ3']
    ext i; fin_cases i <;> simp
  have c1 : gp3_colR L (fun p => χ₂ p * 1) θ₀ η₀ τ₀ = !₂[0, -1, 0, 0] := by
    simp only [gp3_colR, vC2, gp3_hamVF_bump_far hχ₂t hρ1, gp3_hamVF_bump_far hχ₂t hρ3']
    ext i; fin_cases i <;> simp
  have c2 : gp3_colR L (fun p => χ₃ p * (-(p 1 - L τ₀ 1))) θ₀ η₀ τ₀ = !₂[0, 0, -1, -(L τ₀ 1)] := by
    simp only [gp3_colR, vB3, gp3_hamVF_bump_far hχ₃t hρ2, gp3_hamVF_bump_far hχ₃t hρ3]
    ext i; fin_cases i <;> simp
  have c3 : gp3_colR L (fun p => χ₃ p * 1) θ₀ η₀ τ₀ = !₂[0, 0, 0, -1] := by
    simp only [gp3_colR, vC3, gp3_hamVF_bump_far hχ₃t hρ2, gp3_hamVF_bump_far hχ₃t hρ3]
    ext i; fin_cases i <;> simp
  refine ⟨![fun p => χ₂ p * (-(p 1 - L η₀ 1)), fun p => χ₂ p * 1,
    fun p => χ₃ p * (-(p 1 - L τ₀ 1)), fun p => χ₃ p * 1], ?_, ?_⟩
  · intro j
    fin_cases j
    · exact gp3_hyp_of_bump hχ₂s hχ₂c (hfBs _)
    · exact gp3_hyp_of_bump hχ₂s hχ₂c contDiff_const
    · exact gp3_hyp_of_bump hχ₃s hχ₃c (hfBs _)
    · exact gp3_hyp_of_bump hχ₃s hχ₃c contDiff_const
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • gp3_colR L (fun p => χ₂ p * (-(p 1 - L η₀ 1))) θ₀ η₀ τ₀ +
        g 1 • gp3_colR L (fun p => χ₂ p * 1) θ₀ η₀ τ₀ +
        g 2 • gp3_colR L (fun p => χ₃ p * (-(p 1 - L τ₀ 1))) θ₀ η₀ τ₀ +
        g 3 • gp3_colR L (fun p => χ₃ p * 1) θ₀ η₀ τ₀ = 0 := by
      simp only [Fin.sum_univ_four] at hg
      exact hg
    rw [c0, c1, c2, c3] at hg'
    have e0 := congrArg (fun v : ℝ^4 => v 0) hg'
    have e1 := congrArg (fun v : ℝ^4 => v 1) hg'
    have e2 := congrArg (fun v : ℝ^4 => v 2) hg'
    have e3 := congrArg (fun v : ℝ^4 => v 3) hg'
    simp at e0 e1 e2 e3
    have g0 : g 0 = 0 := e0
    have g2 : g 2 = 0 := e2
    have g1 : g 1 = 0 := by rw [g0] at e1; simpa using e1
    have g3 : g 3 = 0 := by rw [g2] at e3; simpa using e3
    intro i
    fin_cases i <;> assumption

/-- The set of pairs where the three columns are independent is open (continuity in `(θ, η)`). -/
theorem gp3_contDiff_colC {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) {H : ℝ³ → ℝ}
    (hH : ContactMotionsHyp H) : ContDiff ℝ ∞ fun t : ℝ^2 => gp3_colC L H (t 0) (t 1) := by
  have hX : ContDiff ℝ ∞ fun θ => hamVF H (L θ) := hH.contDiff_hamVF.comp hL
  have hXk : ∀ k : Fin 3, ContDiff ℝ ∞ fun θ => hamVF H (L θ) k := fun k =>
    (ContactMotions.contDiff_coord k).comp hX
  have hD : ContDiff ℝ ∞ (deriv fun θ => hamVF H (L θ) 0) := ((hXk 0).of_le (by simp)).deriv'
  have h0 := gp3_contDiff_apply 2 0
  have h1 := gp3_contDiff_apply 2 1
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · exact hD.comp h0
  · exact ((hXk 0).comp h0).sub ((hXk 0).comp h1)
  · exact ((hXk 2).comp h0).sub ((hXk 2).comp h1)

theorem gp3_contDiff_colR {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) {H : ℝ³ → ℝ}
    (hH : ContactMotionsHyp H) : ContDiff ℝ ∞ fun t : ℝ^3 => gp3_colR L H (t 0) (t 1) (t 2) := by
  have hX : ContDiff ℝ ∞ fun θ => hamVF H (L θ) := hH.contDiff_hamVF.comp hL
  have hXk : ∀ k : Fin 3, ContDiff ℝ ∞ fun θ => hamVF H (L θ) k := fun k =>
    (ContactMotions.contDiff_coord k).comp hX
  have h0 := gp3_contDiff_apply 3 0
  have h1 := gp3_contDiff_apply 3 1
  have h2 := gp3_contDiff_apply 3 2
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · exact ((hXk 0).comp h0).sub ((hXk 0).comp h1)
  · exact ((hXk 2).comp h0).sub ((hXk 2).comp h1)
  · exact ((hXk 0).comp h0).sub ((hXk 0).comp h2)
  · exact ((hXk 2).comp h0).sub ((hXk 2).comp h2)

theorem gp3_isOpen_colC {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) {H : Fin 3 → ℝ³ → ℝ}
    (hH : ∀ j, ContactMotionsHyp (H j)) :
    IsOpen {t : ℝ^2 | LinearIndependent ℝ fun j => gp3_colC L (H j) (t 0) (t 1)} := by
  have hc : Continuous fun t : ℝ^2 => fun j => gp3_colC L (H j) (t 0) (t 1) :=
    continuous_pi fun j => (gp3_contDiff_colC hL (hH j)).continuous
  exact isOpen_setOfPred_linearIndependent.preimage hc

theorem gp3_isOpen_colR {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) {H : Fin 4 → ℝ³ → ℝ}
    (hH : ∀ j, ContactMotionsHyp (H j)) :
    IsOpen {t : ℝ^3 | LinearIndependent ℝ fun j => gp3_colR L (H j) (t 0) (t 1) (t 2)} := by
  have hc : Continuous fun t : ℝ^3 => fun j => gp3_colR L (H j) (t 0) (t 1) (t 2) :=
    continuous_pi fun j => (gp3_contDiff_colR hL (hH j)).continuous
  exact isOpen_setOfPred_linearIndependent.preimage hc

/-- LEAF P3.2.  One Hamiltonian family serving both `C` and `R` with a common parameter ball of
radius `≤ r₀` (sm-3:2695-2710): disjoint bumps at the distinct spatial points of each zero,
block-triangular minors of ranks `3` and `4`, finitely many zeros covered, uniform ball. -/
theorem exists_CR_avoidance {L : ℝ → ℝ³} (h : Stage1 L) {δc : ℝ} (hδ : LocallyInjectiveFront L δc)
    (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (r : ℝ), (∀ i, ContactMotionsHyp (Hs i)) ∧ 0 < r ∧ r ≤ r₀ ∧
      ParameterAvoidanceHyp 2 m 3 (K2 δc) 0 r (Cmap L m Hs) ∧
      ParameterAvoidanceHyp 3 m 4 (K3 δc) 0 r (Rmap L m Hs) := by
  have hLs : ContDiff ℝ ∞ L := h.circle.smooth
  have hδpos : 0 < δc := hδ.1
  -- circular distance `≥ δc` forces distinct spatial points (embeddedness)
  have hne : ∀ {θ η : ℝ}, δc ≤ circDist θ η → L θ ≠ L η := fun {θ η} hd heq =>
    gp3_not_sameParam_of_le_circDist hδpos hd (h.circle.injective θ η heq)
  -- continuity of the ingredients of the `a = 0` slices
  have hxs : ContDiff ℝ ∞ (coordX L) := (ContactMotions.contDiff_coord 0).comp hLs
  have hxc : Continuous (deriv (coordX L)) := hxs.continuous_deriv (by simp)
  have hfc : Continuous (front L) :=
    ((ContactMotions.contDiff_coord 0).comp hLs).continuous.prodMk
      ((ContactMotions.contDiff_coord 2).comp hLs).continuous
  -- the zero sets of `C(·, 0)` and `R(·, 0)`
  set ZC : Set (ℝ^2) :=
    {t | t ∈ K2 δc ∧ deriv (coordX L) (t 0) = 0 ∧ front L (t 0) = front L (t 1)} with hZC
  set ZR : Set (ℝ^3) :=
    {t | t ∈ K3 δc ∧ front L (t 0) = front L (t 1) ∧ front L (t 0) = front L (t 2)} with hZR
  have hZCc : IsCompact ZC := by
    have : ZC = K2 δc ∩ ({t | deriv (coordX L) (t 0) = 0} ∩ {t | front L (t 0) = front L (t 1)}) := by
      ext t; simp only [hZC, Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [this]
    exact (gp3_isCompact_K2 δc).inter_right
      ((isClosed_eq (hxc.comp (gp3_continuous_apply 2 0)) continuous_const).inter
        (isClosed_eq (hfc.comp (gp3_continuous_apply 2 0)) (hfc.comp (gp3_continuous_apply 2 1))))
  have hZRc : IsCompact ZR := by
    have : ZR = K3 δc ∩ ({t | front L (t 0) = front L (t 1)} ∩ {t | front L (t 0) = front L (t 2)}) := by
      ext t; simp only [hZR, Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [this]
    exact (gp3_isCompact_K3 δc).inter_right
      ((isClosed_eq (hfc.comp (gp3_continuous_apply 3 0)) (hfc.comp (gp3_continuous_apply 3 1))).inter
        (isClosed_eq (hfc.comp (gp3_continuous_apply 3 0)) (hfc.comp (gp3_continuous_apply 3 2))))
  -- charts: three (four) Hamiltonians at each zero, with independent columns there
  have hchartC : ∀ t : ZC, ∃ H : Fin 3 → ℝ³ → ℝ, (∀ j, ContactMotionsHyp (H j)) ∧
      LinearIndependent ℝ (fun j => gp3_colC L (H j) (t.1 0) (t.1 1)) := fun t =>
    gp3_exists_C_chart h t.2.2.1 (hne t.2.1.2.2)
  have hchartR : ∀ t : ZR, ∃ H : Fin 4 → ℝ³ → ℝ, (∀ j, ContactMotionsHyp (H j)) ∧
      LinearIndependent ℝ (fun j => gp3_colR L (H j) (t.1 0) (t.1 1) (t.1 2)) := fun t =>
    gp3_exists_R_chart L (hne t.2.1.2.2.2.1) (hne t.2.1.2.2.2.2.1) (hne t.2.1.2.2.2.2.2)
  choose HC hHC hindC using hchartC
  choose HR hHR hindR using hchartR
  -- the open sets where the columns stay independent, and finite subcovers
  obtain ⟨bC, hcovC⟩ := hZCc.elim_nhds_subcover'
    (fun t ht => {s : ℝ^2 | LinearIndependent ℝ fun j => gp3_colC L (HC ⟨t, ht⟩ j) (s 0) (s 1)})
    (fun t ht => (gp3_isOpen_colC hLs (hHC ⟨t, ht⟩)).mem_nhds (hindC ⟨t, ht⟩))
  obtain ⟨bR, hcovR⟩ := hZRc.elim_nhds_subcover'
    (fun t ht => {s : ℝ^3 | LinearIndependent ℝ fun j => gp3_colR L (HR ⟨t, ht⟩ j) (s 0) (s 1) (s 2)})
    (fun t ht => (gp3_isOpen_colR hLs (hHR ⟨t, ht⟩)).mem_nhds (hindR ⟨t, ht⟩))
  -- the family: all chart Hamiltonians, indexed by `Fin m`
  let κ := (↥bC × Fin 3) ⊕ (↥bR × Fin 4)
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let HH : κ → ℝ³ → ℝ := Sum.elim (fun p => HC p.1.1 p.2) (fun p => HR p.1.1 p.2)
  have hHH : ∀ k, ContactMotionsHyp (HH k) := by
    rintro (⟨t, j⟩ | ⟨t, j⟩)
    · exact hHC _ _
    · exact hHR _ _
  set m := Fintype.card κ with hm
  let Hs : Fin m → ℝ³ → ℝ := fun i => HH (e.symm i)
  have hHs : ∀ i, ContactMotionsHyp (Hs i) := fun i => hHH _
  let ιC : ↥bC → Fin 3 → Fin m := fun t j => e (Sum.inl (t, j))
  let ιR : ↥bR → Fin 4 → Fin m := fun t j => e (Sum.inr (t, j))
  have hHsC : ∀ (t : ↥bC) (j : Fin 3), Hs (ιC t j) = HC t.1 j := fun t j => by
    simp [Hs, ιC, HH]
  have hHsR : ∀ (t : ↥bR) (j : Fin 4), Hs (ιR t j) = HR t.1 j := fun t j => by
    simp [Hs, ιR, HH]
  -- at `a = 0` the composition is the identity
  have hid : composeFlows m Hs (par (0 : ℝ^m)) = id := by
    funext p
    rw [gp3_par_zero]
    exact ContactMotions.composeFlows_zero m Hs (fun i p => (hHs i).hamFlow_zero p) p
  have hC0 : ∀ t : ℝ^2, Cmap L m Hs (t, 0) = !₂[deriv (coordX L) (t 0),
      (front L (t 0)).1 - (front L (t 1)).1, (front L (t 0)).2 - (front L (t 1)).2] := by
    intro t
    simp only [Cmap, gp3_xParam_eq, gp3_frontParam_eq, hid, Function.id_comp]
  have hR0 : ∀ t : ℝ^3, Rmap L m Hs (t, 0) = !₂[(front L (t 0)).1 - (front L (t 1)).1,
      (front L (t 0)).2 - (front L (t 1)).2, (front L (t 0)).1 - (front L (t 2)).1,
      (front L (t 0)).2 - (front L (t 2)).2] := by
    intro t
    simp only [Rmap, gp3_frontParam_eq, hid, Function.id_comp]
  -- the rank hypotheses at `a = 0`
  have h0C : ∀ t ∈ K2 δc, Cmap L m Hs (t, 0) = 0 → ∃ k : ↥bC, LinearIndependent ℝ
      (fun j => fderiv ℝ (Cmap L m Hs) (t, 0) (0, EuclideanSpace.single (ιC k j) 1)) := by
    intro t ht hC
    rw [hC0] at hC
    have e0 := congrArg (fun v : ℝ^3 => v 0) hC
    have e1 := congrArg (fun v : ℝ^3 => v 1) hC
    have e2 := congrArg (fun v : ℝ^3 => v 2) hC
    simp at e0 e1 e2
    have htZ : t ∈ ZC := ⟨ht, e0, Prod.ext (sub_eq_zero.1 e1) (sub_eq_zero.1 e2)⟩
    obtain ⟨k, hk, hkV⟩ := Set.mem_iUnion₂.1 (hcovC htZ)
    refine ⟨⟨k, hk⟩, ?_⟩
    have : (fun j => fderiv ℝ (Cmap L m Hs) (t, 0) (0, EuclideanSpace.single (ιC ⟨k, hk⟩ j) 1)) =
        fun j => gp3_colC L (HC k j) (t 0) (t 1) := by
      funext j; rw [gp3_fderiv_Cmap_zero hLs m Hs hHs, hHsC]
    rw [this]
    exact hkV
  have h0R : ∀ t ∈ K3 δc, Rmap L m Hs (t, 0) = 0 → ∃ k : ↥bR, LinearIndependent ℝ
      (fun j => fderiv ℝ (Rmap L m Hs) (t, 0) (0, EuclideanSpace.single (ιR k j) 1)) := by
    intro t ht hR
    rw [hR0] at hR
    have e0 := congrArg (fun v : ℝ^4 => v 0) hR
    have e1 := congrArg (fun v : ℝ^4 => v 1) hR
    have e2 := congrArg (fun v : ℝ^4 => v 2) hR
    have e3 := congrArg (fun v : ℝ^4 => v 3) hR
    simp at e0 e1 e2 e3
    have htZ : t ∈ ZR := ⟨ht, Prod.ext (sub_eq_zero.1 e0) (sub_eq_zero.1 e1),
      Prod.ext (sub_eq_zero.1 e2) (sub_eq_zero.1 e3)⟩
    obtain ⟨k, hk, hkV⟩ := Set.mem_iUnion₂.1 (hcovR htZ)
    refine ⟨⟨k, hk⟩, ?_⟩
    have : (fun j => fderiv ℝ (Rmap L m Hs) (t, 0) (0, EuclideanSpace.single (ιR ⟨k, hk⟩ j) 1)) =
        fun j => gp3_colR L (HR k j) (t 0) (t 1) (t 2) := by
      funext j; rw [gp3_fderiv_Rmap_zero hLs m Hs hHs, hHsR]
    rw [this]
    exact hkV
  obtain ⟨rC, hrC, hCpa⟩ := gp3_exists_paHyp (gp3_isCompact_K2 δc)
    (gp3_contDiff_Cmap hLs m Hs hHs) (by norm_num) ιC h0C
  obtain ⟨rR, hrR, hRpa⟩ := gp3_exists_paHyp (gp3_isCompact_K3 δc)
    (gp3_contDiff_Rmap hLs m Hs hHs) (by norm_num) ιR h0R
  refine ⟨m, Hs, min (min rC rR) r₀, hHs, by positivity, min_le_right _ _, ?_, ?_⟩
  · exact hCpa _ (by positivity) ((min_le_left _ _).trans (min_le_left _ _))
  · exact hRpa _ (by positivity) ((min_le_left _ _).trans (min_le_right _ _))

/-! ### Unit P3 helpers: reduction of parameters to one period -/

theorem gp3_sameParam_symm {θ η : ℝ} (h : SameParam θ η) : SameParam η θ := by
  obtain ⟨k, hk⟩ := h; exact ⟨-k, by rw [hk]; push_cast; ring⟩

theorem gp3_sameParam_trans {θ η τ : ℝ} (h1 : SameParam θ η) (h2 : SameParam η τ) : SameParam θ τ := by
  obtain ⟨k, hk⟩ := h1; obtain ⟨l, hl⟩ := h2; exact ⟨k + l, by rw [hl, hk]; push_cast; ring⟩

/-- The representative of `θ` in `[0, 2π)`, with `SameParam θ θ̄`. -/
theorem gp3_exists_reduce (θ : ℝ) : ∃ θ', θ' ∈ Ico 0 (2 * π) ∧ SameParam θ θ' := by
  refine ⟨toIcoMod two_pi_pos 0 θ, by simpa using toIcoMod_mem_Ico two_pi_pos 0 θ,
    -(toIcoDiv two_pi_pos 0 θ), ?_⟩
  have := toIcoMod_add_toIcoDiv_zsmul two_pi_pos 0 θ
  rw [zsmul_eq_mul] at this
  push_cast; linear_combination this

theorem gp3_periodic_comp {L : ℝ → ℝ³} (hL : Periodic L (2 * π)) (Φ : ℝ³ → ℝ³) :
    Periodic (Φ ∘ L) (2 * π) := fun θ => by simp [hL θ]

theorem gp3_front_eq_of_sameParam {L : ℝ → ℝ³} (hL : Periodic L (2 * π)) {θ η : ℝ}
    (h : SameParam θ η) : front L η = front L θ := by
  obtain ⟨k, hk⟩ := h
  have := hL.int_mul k θ
  rw [hk]; unfold front; rw [show θ + 2 * π * k = θ + k * (2 * π) by ring, this]

theorem gp3_deriv_coordX_eq_of_sameParam {L : ℝ → ℝ³} (hL : Periodic L (2 * π)) {θ η : ℝ}
    (h : SameParam θ η) : deriv (coordX L) η = deriv (coordX L) θ := by
  obtain ⟨k, hk⟩ := h
  have hp : Periodic (coordX L) (k * (2 * π)) := fun x => by
    unfold coordX; rw [hL.int_mul k x]
  have : coordX L = fun x => coordX L (x + k * (2 * π)) := funext fun x => (hp x).symm
  rw [hk, show θ + 2 * π * k = θ + k * (2 * π) by ring]
  conv_rhs => rw [this]
  rw [deriv_comp_add_const]

/-- LEAF P3.3.  `C ≠ 0` on `K₂ × {a}` plus the collar give `NoCuspOnBranch` (pairs closer than
`δc` are handled by local injectivity; others are reduced to one period). -/
theorem noCuspOnBranch_of_C {L : ℝ → ℝ³} (h : Stage1 L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) {δc r : ℝ} {a : ℝ^m}
    (hδa : LocallyInjectiveFront (composeFlows m Hs (par a) ∘ L) δc)
    (ha : a ∉ ParameterAvoidance.zeroParams (K2 δc) (Metric.closedBall 0 r) (Cmap L m Hs))
    (har : a ∈ Metric.closedBall (0 : ℝ^m) r) : NoCuspOnBranch (composeFlows m Hs (par a) ∘ L) := by
  -- `hHs` is not needed for this leaf
  have _ := hHs
  set L' := composeFlows m Hs (par a) ∘ L with hL'
  have hper : Periodic L' (2 * π) := gp3_periodic_comp h.circle.periodic _
  intro θ hθ η hne hfront
  obtain ⟨θ', hθ'I, hθθ'⟩ := gp3_exists_reduce θ
  obtain ⟨η', hη'I, hηη'⟩ := gp3_exists_reduce η
  have hne' : ¬ SameParam θ' η' := fun hs =>
    hne (gp3_sameParam_trans hθθ' (gp3_sameParam_trans hs (gp3_sameParam_symm hηη')))
  have hfθ : front L' θ' = front L' θ := gp3_front_eq_of_sameParam hper hθθ'
  have hfη : front L' η' = front L' η := gp3_front_eq_of_sameParam hper hηη'
  have hf' : front L' θ' = front L' η' := by rw [hfθ, hfη, hfront]
  have hx' : deriv (coordX L') θ' = 0 := by
    rw [gp3_deriv_coordX_eq_of_sameParam hper hθθ']; exact hθ
  by_cases hd : circDist θ' η' < δc
  · exact hδa.2 θ' η' hd hne' hf'
  · push Not at hd
    apply ha
    refine ⟨har, !₂[θ', η'], ⟨?_, ?_, ?_⟩, ?_⟩
    · simpa using Ico_subset_Icc_self hθ'I
    · simpa using Ico_subset_Icc_self hη'I
    · simpa using hd
    · ext k
      fin_cases k
      · simpa [Cmap, gp3_xParam_eq] using hx'
      · simp [Cmap, gp3_frontParam_eq]; exact sub_eq_zero.2 (congrArg Prod.fst hf')
      · simp [Cmap, gp3_frontParam_eq]; exact sub_eq_zero.2 (congrArg Prod.snd hf')

/-- LEAF P3.4.  `R ≠ 0` on `K₃ × {a}` plus the collar give `NoTriple`. -/
theorem noTriple_of_R {L : ℝ → ℝ³} (h : Stage1 L) (m : ℕ) (Hs : Fin m → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) {δc r : ℝ} {a : ℝ^m}
    (hδa : LocallyInjectiveFront (composeFlows m Hs (par a) ∘ L) δc)
    (ha : a ∉ ParameterAvoidance.zeroParams (K3 δc) (Metric.closedBall 0 r) (Rmap L m Hs))
    (har : a ∈ Metric.closedBall (0 : ℝ^m) r) : NoTriple (composeFlows m Hs (par a) ∘ L) := by
  -- `hHs` is not needed for this leaf
  have _ := hHs
  set L' := composeFlows m Hs (par a) ∘ L with hL'
  have hper : Periodic L' (2 * π) := gp3_periodic_comp h.circle.periodic _
  rintro θ η τ hθη hθτ hητ ⟨hfη, hfτ⟩
  obtain ⟨θ', hθ'I, hθθ'⟩ := gp3_exists_reduce θ
  obtain ⟨η', hη'I, hηη'⟩ := gp3_exists_reduce η
  obtain ⟨τ', hτ'I, hττ'⟩ := gp3_exists_reduce τ
  have hne : ∀ {x x' y y' : ℝ}, ¬ SameParam x y → SameParam x x' → SameParam y y' →
      ¬ SameParam x' y' := fun hxy hx hy hs =>
    hxy (gp3_sameParam_trans hx (gp3_sameParam_trans hs (gp3_sameParam_symm hy)))
  have hθη' := hne hθη hθθ' hηη'
  have hθτ' := hne hθτ hθθ' hττ'
  have hητ' := hne hητ hηη' hττ'
  have hfθ := gp3_front_eq_of_sameParam hper hθθ'
  have hfη' := gp3_front_eq_of_sameParam hper hηη'
  have hfτ' := gp3_front_eq_of_sameParam hper hττ'
  have h1 : front L' θ' = front L' η' := by rw [hfθ, hfη', hfη]
  have h2 : front L' θ' = front L' τ' := by rw [hfθ, hfτ', hfτ]
  have h3 : front L' η' = front L' τ' := by rw [← h1, h2]
  by_cases d1 : circDist θ' η' < δc
  · exact hδa.2 θ' η' d1 hθη' h1
  by_cases d2 : circDist θ' τ' < δc
  · exact hδa.2 θ' τ' d2 hθτ' h2
  by_cases d3 : circDist η' τ' < δc
  · exact hδa.2 η' τ' d3 hητ' h3
  push Not at d1 d2 d3
  apply ha
  refine ⟨har, !₂[θ', η', τ'], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa using Ico_subset_Icc_self hθ'I
  · simpa using Ico_subset_Icc_self hη'I
  · simpa using Ico_subset_Icc_self hτ'I
  · simpa using d1
  · simpa using d2
  · simpa using d3
  · ext k
    fin_cases k
    · simp [Rmap, gp3_frontParam_eq]; exact sub_eq_zero.2 (congrArg Prod.fst h1)
    · simp [Rmap, gp3_frontParam_eq]; exact sub_eq_zero.2 (congrArg Prod.snd h1)
    · simp [Rmap, gp3_frontParam_eq]; exact sub_eq_zero.2 (congrArg Prod.fst h2)
    · simp [Rmap, gp3_frontParam_eq]; exact sub_eq_zero.2 (congrArg Prod.snd h2)

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
