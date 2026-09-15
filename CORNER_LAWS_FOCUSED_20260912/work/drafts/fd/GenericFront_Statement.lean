import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # SM fd:generic-front — a generic front preserving the chosen positive pushoff (row 87)

Source: reference/SM/sm-3-statesum.tex:2613-2634 (statement), 2635-2783 (proof).  Drafted
2026-09-14 in work/drafts/fd/ as part of the fd block 84-88 (feasibility memo
`work/drafts/fd/FD_84_87_FEASIBILITY_v2.md` §2).  **Statement only**: this file defines the
notions of the printed statement in coordinates and the Prop bundle `SM.GenericFrontData`; it
contains no theorem about it.  The typecheck of the bundle with a `sorry` row theorem is done
on a /tmp copy only (`theorem fd_generic_front : GenericFrontData := sorry`), never here.

Check: `cd work/lean && lake env lean ../drafts/fd/GenericFront_Statement.lean`.

## The printed statement (sm-3:2613-2630, verbatim)

"Every smooth oriented Legendrian embedding L : S¹ → ℝ³ admits a smooth ambient
coorientation-preserving contact isotopy to a Legendrian embedding L_g whose xz front has only
finitely many semicubical cusps and transverse double points, with no triple point and no cusp on
another branch.  At each cusp there is a smooth local coordinate u = y − y₀ in which
x = x₀ + Au², y = y₀ + u, z = z₀ + Ay₀u² + ⅔Au³, A ≠ 0; the coordinate u may increase or decrease
along the prescribed orientation.  The isotopy carries a chosen thin positive-pushoff annulus and
preserves its positive-pushoff transverse isotopy class, as well as the oriented topological knot
type."

## Printed notion → Lean

| printed | Lean |
|---|---|
| `ℝ³`, `(x, y, z)`, `α = dz − y dx` | `EuclideanSpace ℝ (Fin 3)`, `(p 0, p 1, p 2)`, `alpha p v = v 2 − p 1 * v 0` (as rows 84, 86) |
| "smooth oriented Legendrian embedding `L : S¹ → ℝ³`" | `IsEmbeddedCircle L ∧ IsLegendrian L` (`2π`-periodic lift, FR-GF-1) |
| "smooth ambient coorientation-preserving contact isotopy" `Φ_s`, `s ∈ [0,1]` | `IsContactIsotopy Φ` (jointly `C^∞` on `[0,1] × ℝ³`, `Φ_0 = id`, each `Φ_s` a `C^∞` diffeomorphism, `Φ_s^*α = c α` with `c > 0` pointwise, identity outside one compact set — FR-GF-2) |
| "to a Legendrian embedding `L_g`" | `L_g = Φ 1 ∘ L`; fields `legendrian_circle`, `legendrian` |
| "its `xz` front" | `front L θ = (L θ 0, L θ 2) : ℝ × ℝ` |
| "semicubical cusps" (points with `x′ = 0`, sm-3:3470-3474) | `cuspSet L = {θ | x′(θ) = 0}`; `finite_cusps : (cuspSet L_g ∩ Ico 0 (2π)).Finite` (FR-GF-3) |
| "transverse double points", "finitely many" | `doublePoints L = {(θ, η) | θ ≢ η mod 2π ∧ front θ = front η}`; `finite_double`, `transverse_double : ∀ (θ, η) ∈ doublePoints, x′(θ) z′(η) − z′(θ) x′(η) ≠ 0` (FR-GF-4) |
| "no triple point" | `no_triple` |
| "no cusp on another branch" | `no_cusp_on_branch : ∀ θ ∈ cuspSet, ∀ η, θ ≢ η → front η ≠ front θ` |
| the exact cusp germ (sm-3:2621-2625) | `IsExactCuspGerm L θc`: `∃ A ≠ 0`, `y′(θc) ≠ 0`, and on a neighbourhood of `θc`, with `u = y(θ) − y(θc)`, `x = x₀ + A u²` and `z = z₀ + A y₀ u² + ⅔ A u³` (FR-GF-5) |
| "carries a chosen thin positive-pushoff annulus and preserves its positive-pushoff transverse isotopy class" | `pushoff`: for every pushoff annulus `B` of `L` (row 84's `IsPushoffAnnulus`), every `Φ_s ∘ B` is a pushoff annulus of `Φ_s ∘ L`, and every positive circle `K = B(·, s₀)` is transversely isotopic (through `Φ_s ∘ K`) to `Φ_1 ∘ K`, a positive pushoff of `L_g` (FR-GF-6) |
| "as well as the oriented topological knot type" | `knot_type : ∃ Ψ, IsCompactlySupportedAmbientIsotopy Ψ ∧ ∀ θ, Ψ 1 (L θ) = L_g θ` (FR-GF-7) |

## Fidelity readings

* **FR-GF-1 (circles as periodic lifts).** As FR-TN-1 of row 84: `S¹ = ℝ/2πℤ` is read through
  `2π`-periodic maps on `ℝ`; "embedded" = injective modulo `2π` + immersion.
* **FR-GF-2 (contact isotopy, compact support).** "Smooth ambient coorientation-preserving contact
  isotopy" = jointly smooth family of diffeomorphisms of `ℝ³` starting at the identity with
  `Φ_s^*α = c_s α`, `c_s > 0` (pointwise conformal factor; FR-CM-1/2 of row 86).  The field
  `support` (identity outside one compact set) is **not in the printed statement**; the printed
  proof produces it (compositions of compactly supported Hamiltonian flows, sm-3:2636-2640,
  2767-2771) and the consumer sm-3:3480-3481 uses it ("the two smooth compactly supported ambient
  flows").  Recorded as a deliberate strengthening.
* **FR-GF-3 (cusps).** A cusp of the front is a parameter with `x′ = 0` (the consumer sm-3:3470-3474:
  "Legendrianity `z′ = yx′` makes the front tangent vanish wherever `x′ = 0`, so every such point is
  one of these cusps"); "semicubical" is the germ clause `exact_germ`, which contains `x″ = 2A y′² ≠ 0`.
  Finiteness is counted on one period.
* **FR-GF-4 (double points).** Ordered pairs of parameters distinct modulo `2π` with equal front
  points; transversality = nonzero determinant of the two front velocities `(x′, z′)`; finiteness on
  one period square.  (The printed proof's formula `x′(θ)x′(η)(y(η) − y(θ))` is this determinant for
  a Legendrian curve, sm-3:2727-2731.)
* **FR-GF-5 (exact germ).** "A smooth local coordinate `u = y − y₀`" = `y′(θc) ≠ 0` (so `u` is a
  local coordinate, increasing or decreasing with the orientation — "may increase or decrease" is
  the absence of a sign condition) together with the two displayed identities on a neighbourhood of
  the cusp parameter; `y = y₀ + u` is the definition of `u`.
* **FR-GF-6 (the chosen annulus).** "A chosen thin positive-pushoff annulus" is any pushoff
  annulus of `L` in the sense of row 84 (`IsPushoffAnnulus`, sm-3:2490-2502); the conclusion is
  quantified over all of them.  "Preserves its positive-pushoff transverse isotopy class": the
  positive parallel circle moves through positive transverse embeddings (sm-3:2773-2779) to a
  positive pushoff of `L_g`; rendered with row 84's `TransverselyIsotopic` and `IsPositivePushoff`.
* **FR-GF-7 (oriented topological knot type).** Rendered as the ambient isotopy class of the
  parametrized oriented embedding: a compactly supported ambient isotopy `Ψ` (row 84's notion)
  with `Ψ_1 ∘ L = L_g` as parametrized circles, which carries the orientation.  The witness in the
  printed proof is `Φ` itself (sm-3:2780-2781), so the field is implied by `isotopy`; it is kept as
  a separate field because it is a separate printed clause and is what the consumer
  sm-3:3476-3490 uses. -/

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

/-! ## 5. Sanity checks (not printed clauses) -/

namespace GenericFront

/-- The cusp germ has `x″(θc) = 2A y′(θc)² ≠ 0` in spirit; here only the trivial consistency that
the germ identities hold at the cusp parameter itself. -/
lemma IsExactCuspGerm.self {L : ℝ → ℝ³} {θc : ℝ} (h : IsExactCuspGerm L θc) :
    ∃ A : ℝ, A ≠ 0 ∧ coordX L θc = coordX L θc + A * (coordY L θc - coordY L θc) ^ 2 := by
  obtain ⟨A, hA, -, ε, hε, hθ⟩ := h
  exact ⟨A, hA, (hθ θc (by simpa using hε)).1⟩

/-- A double point is symmetric. -/
lemma doublePoints_swap {L : ℝ → ℝ³} {θ η : ℝ} (h : (θ, η) ∈ doublePoints L) :
    (η, θ) ∈ doublePoints L := by
  obtain ⟨hne, heq⟩ := h
  refine ⟨fun ⟨k, hk⟩ => hne ⟨-k, ?_⟩, heq.symm⟩
  simp only [Int.cast_neg] at *
  linarith

end GenericFront

end

end SM
