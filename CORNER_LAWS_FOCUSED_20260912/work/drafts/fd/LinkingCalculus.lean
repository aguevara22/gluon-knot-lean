import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Real.Sign
import Mathlib.Topology.DiscreteSubset
import Mathlib.Algebra.BigOperators.Finprod

/-! # SM fd:linking-calculus — Linking calculus and uniform transverse framing (row 88)

Source: reference/SM/sm-3-statesum.tex:2785-2826 (statement), 2827-3010 (proof).  Drafted 2026-09-14
in work/drafts/fd/ (the fd block 84-88; sibling row 85 fd:parameter-avoidance in
`ParameterAvoidance.lean`).  Pure analysis: no dependency on the project's diagram layer, Mathlib
only.  Intended home: `work/lean/SM/LinkingCalculus.lean`.
Main declaration: `SM.fd_linking_calculus : LinkingCalculusData`.
Check: `cd work/lean && lake env lean ../drafts/fd/LinkingCalculus.lean`.

## The printed statement (sm-3:2787-2824, verbatim)

"For two disjoint smooth oriented parametrized circles `C₁, C₂` in oriented `ℝ³`, use the normalized
linking pairing
  `ℓ(C₁,C₂) = (1/4π) ∫_{S¹×S¹} G·(G_u × G_v) du dv,  G(u,v) = (C₂(v) − C₁(u))/|C₂(v) − C₁(u)|.`   (fd:gauss-linking)
It is symmetric and is constant under smooth families of disjoint oriented pairs. Call a direction
`ν ∈ S²` generic for the pair if at every parameter pair `(u,v)` at which `C₂(v) − C₁(u)` is parallel
to `ν` the tangents of the two circles projected along `ν` are linearly independent; the projection
along such a `ν` displays the pair with finitely many transverse mixed crossings. Let `ν` point toward
the observer and orient the projection plane so that its positive basis followed by `ν` is positive in
`ℝ³`; at a mixed crossing the strand nearer the observer is over. Then `ℓ(C₁,C₂)` equals one half the
sum over the mixed crossings of the overpass-first sign `sgn det(u_o,u_u)` of the projected over and
under tangents. Thus it has exactly the linking normalization used in the source's front calculations.

More generally, let `C_s`, `0 ≤ s ≤ 1`, be a smooth family of embedded oriented circles and let `v_s`
be a smooth vector field along them, everywhere linearly independent of `∂_u C_s`. One common
sufficiently small positive `ε` gives disjoint framed pairs `(C_s, C_s + εv_s)` throughout the family.
Their pairing is independent of that radius and of `s`. This includes a homotopy of normal framings on
a fixed curve.

If `T_s : S¹ → ℝ³`, `0 ≤ s ≤ 1`, is a smooth family of embeddings with `(dz − y dx)(∂_u T_s) > 0`,
there is one `ε₀ > 0` such that `T_s` and `T_s + ε∂_y` are disjoint positive transverse embeddings
for every `s` and `0 < ε ≤ ε₀`. The number `sl(T_s) = ℓ(T_s, T_s + ε∂_y)` (fd:framed-linking) is
independent of such `ε` and of `s`."

## Printed notion → Lean

| printed | Lean |
|---|---|
| oriented `ℝ³` (2788) | `E3 = EuclideanSpace ℝ (Fin 3)`, coordinates `p 0, p 1, p 2 = x, y, z`, standard orientation; `cross`, triple product `⟪a, cross b c⟫ = det ![a, b, c]` (`inner_cross_eq_det`) |
| "smooth oriented parametrized circle" (2787) | `IsSmoothCircle P C`: `ContDiff ℝ ∞ C`, `Periodic C P`; `S¹ = ℝ/Pℤ`, `P > 0` a parameter (FR-LC-1); orientation = parameter direction |
| "two disjoint … circles" (2787) | `DisjointPair P C₁ C₂` (`disjoint : ∀ u v, C₂ v ≠ C₁ u`) |
| `G(u,v)` (2792) | `gaussMap C₁ C₂ u v = ‖C₂ v − C₁ u‖⁻¹ • (C₂ v − C₁ u)` |
| `G_u`, `G_v` (2791) | `pderivU G u v = deriv (fun u' => G u' v) u`, `pderivV` (FR-LC-2) |
| `G·(G_u × G_v)` (2791) | `gaussDensity G u v = ⟪G u v, cross (pderivU G u v) (pderivV G u v)⟫` |
| `ℓ(C₁,C₂)` (2790-2791) | `linking P C₁ C₂ = (1/(4π)) * ∫ u in 0..P, ∫ v in 0..P, gaussDensity (gaussMap C₁ C₂) u v` |
| "smooth families of disjoint oriented pairs" (2794-2795) | `DisjointPairFamily P C₁ C₂`: jointly `C^∞` maps `ℝ × ℝ → E3` (FR-LC-3), `P`-periodic in `u`, disjoint for `s ∈ [0,1]` |
| "parallel to `ν`" (2796) | `Parallel w ν = ∃ t : ℝ, w = t • ν` (both signs) |
| "projected along `ν`" (2797) | `projAlong ν w = w − ⟪w, ν⟫ • ν` |
| "generic for the pair" (2795-2798) | `GenericDirection C₁ C₂ ν`: `‖ν‖ = 1` and `LinearIndependent ℝ ![projAlong ν (deriv C₁ u), projAlong ν (deriv C₂ v)]` at every parallel pair |
| "the mixed crossings" (2799, 2803) | `mixedCrossings P C₁ C₂ ν = {p ∈ [0,P)² | Parallel (C₂ p.2 − C₁ p.1) ν}` (one fundamental domain) |
| plane orientation, over strand, `sgn det(u_o,u_u)` (2799-2804) | `planeDet ν x y = ⟪ν, cross x y⟫ = det(x, y, ν)`; `lcCrossingSign`: over strand = larger `⟪·, ν⟫` (`ν` toward the observer) (FR-LC-4) |
| fd:regular-pole-count (2894-2897), used by the crossing clause | `RegularPoleCount` (the isolated hypothesis, FR-LC-6) |
| "smooth family of embedded oriented circles … `v_s` … linearly independent of `∂_u C_s`" (2808-2810) | `FramedFamily P C v` (embedded = injective on `ℝ/Pℤ`, FR-LC-7) |
| `C_s + εv_s` (2812) | `pushoff (C s) (v s) ε = fun u => C s u + ε • v s u` |
| `dz − y dx` (2817), `∂_y` (2818) | `lcContactForm p w = w 2 − p 1 * w 0`, `ey = EuclideanSpace.single 1 1` |
| "positive transverse embedding" (2819) | `IsPositiveTransverseEmbedding P T` |
| "smooth family of embeddings with `(dz − y dx)(∂_u T_s) > 0`" (2816-2817) | `TransverseFamily P T` |
| `sl(T_s)` (2822) | `selfLinking P T ε = linking P T (pushoff T (fun _ => ey) ε)` |

## Clause → field of `LinkingCalculusData`

| tex | clause | field | status |
|---|---|---|---|
| 2794 | "It is symmetric" | `symm` | proved |
| 2794-2795 | "constant under smooth families of disjoint oriented pairs" | `family_const` | proved |
| 2798-2799 | "finitely many transverse mixed crossings" | `finite_crossings` | proved |
| 2802-2804 | `ℓ` = one half the sum of the overpass-first crossing signs | `crossing_formula` | proved from `RegularPoleCount` |
| 2810-2812 | one common `ε` gives disjoint framed pairs | `framing_uniform` | proved |
| 2812-2813 | pairing independent of the radius and of `s` | `framing_invariant` | proved |
| 2813-2814 | homotopy of normal framings on a fixed curve | `framing_homotopy` | proved |
| 2817-2820 | one `ε₀` with `T_s`, `T_s + ε∂_y` disjoint positive transverse embeddings | `transverse_uniform` | proved |
| 2820-2824 | `sl(T_s)` independent of such `ε` and of `s` | `self_linking_invariant` | proved |

The sentence 2805-2806 ("Thus it has exactly the linking normalization used in the source's front
calculations") is commentary on the crossing formula and has no field.

## Route

* Symmetry (2838-2841): `gaussDensity_swap` (`G̃ = −G` with the variables exchanged; `deriv.neg`,
  antisymmetry of the cross product), then Fubini on the compact square
  (`integral_integral_swap_of_continuous`).
* Constancy (2843-2867): the printed calculation.  For `G(u,v,s)` into the unit sphere and
  `A = G·(G_u × G_v)`, `B = G·(G_s × G_v)`, `C = G·(G_u × G_s)`: the identity
  `∂_s A = ∂_u B + ∂_v C` (fd:gauss-divergence) from the product rule, the vanishing of triple
  products of vectors orthogonal to `G` (`inner_cross_eq_zero_of_orth`), and the symmetry of second
  derivatives (`ContDiffAt.isSymmSndFDerivAt`); then the fundamental theorem of calculus in `s` and
  in the periodic variables, with Fubini for the continuous integrands.  The `[0,1]`-family is
  reparametrised through `Real.smoothTransition` so that the pairs are disjoint for every real
  parameter.
* Finiteness (2881-2883): the zeros of `p ↦ projAlong ν (C₂ p.2 − C₁ p.1)` have injective derivative
  (the genericity), so are isolated (`HasFDerivAt.eventually_ne`, `LinearMap.exists_antilipschitzWith`),
  and form a closed subset of the compact square (`IsCompact.finite`).
* Crossing formula (2917-2941): `RegularPoleCount` at `N = ν` and `N = −ν`; the derivatives of `G` at
  a crossing are the projected tangents over `|C₂(v) − C₁(u)|`, the local orientation sign is the
  overpass-first sign at both poles, and the two signed counts add to `2ℓ`.
* Framing radius (2942-2985): a direct Taylor estimate replaces the four-dimensional normal chart
  (fd:family-normal-chart); see `LinkingCalculus.Framing`.  Radius and `s` independence
  (2968-2970): the parameters are joined by a smooth path (`LinkingCalculus.Interp.interp`) along
  which the pairs stay disjoint, and the constancy clause applies.
* Transverse family (2986-3009): `dz − y dx` on a linear relation gives the independence
  (`TransverseFamily.framedFamily`); `a₀ = min (z' − yx') > 0`, `M ≥ |x'|`, `ε₀ M < a₀/2` gives the
  positivity of the pushoff (`TransverseFamily.exists_uniform_positive`).

## Fidelity readings recorded (details in LINKING_CALCULUS_REPORT.md)

* FR-LC-1 period convention `S¹ = ℝ/Pℤ`, `P > 0` a parameter (the consumer sm-3:2398 uses `2π`).
* FR-LC-2 `G_u, G_v` are the derivatives of the slices (`deriv`), equal to the Fréchet partials.
* FR-LC-3 a smooth family on `[0,1]` is the restriction of a jointly `C^∞` map on `ℝ × ℝ`; the
  hypotheses are imposed only for `s ∈ [0,1]`.
* FR-LC-4 orientation conventions: `planeDet ν x y = det(x, y, ν)`; "nearer the observer" = larger
  `⟪·, ν⟫`.
* FR-LC-5 "parallel" includes both signs; crossings are counted in one fundamental domain `[0,P)²`;
  "transverse" is the defining independence.
* FR-LC-6 the crossing formula is proved from the isolated hypothesis `RegularPoleCount`
  (fd:regular-pole-count), the only unformalised ingredient (Stokes on the punctured torus).
* FR-LC-7 "embedded" = injective on `ℝ/Pℤ`; the immersion condition follows from the independence
  (resp. positivity) hypothesis.
* FR-LC-8 "independent of that radius" is proved for every common radius `ε₀` with the disjointness
  property, and the proof of the radius clause does not construct the normal chart. -/

namespace SM

open scoped RealInnerProductSpace ContDiff
open Set Function Filter Topology Real

noncomputable section

/-- Oriented `ℝ³`: `EuclideanSpace ℝ (Fin 3)`; coordinates `p 0 = x`, `p 1 = y`, `p 2 = z`; the
standard orientation is the one in which `det ![e₀, e₁, e₂] = 1`. -/
local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace LinkingCalculus

/-! ## 0. Algebra of oriented `ℝ³`: cross product, triple product, projections -/

/-- The cross product `a × b` of oriented `ℝ³`, transported from Mathlib's `crossProduct` on
`Fin 3 → ℝ`. -/
def cross (a b : E3) : E3 := WithLp.toLp 2 (crossProduct a.ofLp b.ofLp)

theorem inner_eq_sum (a b : E3) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem cross_apply0 (a b : E3) : cross a b 0 = a 1 * b 2 - a 2 * b 1 := by
  simp [cross, cross_apply]

theorem cross_apply1 (a b : E3) : cross a b 1 = a 2 * b 0 - a 0 * b 2 := by
  simp [cross, cross_apply]

theorem cross_apply2 (a b : E3) : cross a b 2 = a 0 * b 1 - a 1 * b 0 := by
  simp [cross, cross_apply]

theorem cross_comm_neg (a b : E3) : cross a b = -cross b a := by
  ext i
  fin_cases i <;> simp [cross_apply0, cross_apply1, cross_apply2] <;> ring

theorem cross_self (a : E3) : cross a a = 0 := by
  ext i
  fin_cases i <;> simp [cross_apply0, cross_apply1, cross_apply2] <;> ring

theorem cross_add_left (a a' b : E3) : cross (a + a') b = cross a b + cross a' b := by
  ext i
  fin_cases i <;> simp [cross_apply0, cross_apply1, cross_apply2] <;> ring

theorem cross_add_right (a b b' : E3) : cross a (b + b') = cross a b + cross a b' := by
  ext i
  fin_cases i <;> simp [cross_apply0, cross_apply1, cross_apply2] <;> ring

theorem cross_smul_left (t : ℝ) (a b : E3) : cross (t • a) b = t • cross a b := by
  ext i
  fin_cases i <;> simp [cross_apply0, cross_apply1, cross_apply2] <;> ring

theorem cross_smul_right (t : ℝ) (a b : E3) : cross a (t • b) = t • cross a b := by
  ext i
  fin_cases i <;> simp [cross_apply0, cross_apply1, cross_apply2] <;> ring

theorem cross_neg_left (a b : E3) : cross (-a) b = -cross a b := by
  ext i
  fin_cases i <;> simp [cross_apply0, cross_apply1, cross_apply2] <;> ring

theorem cross_neg_right (a b : E3) : cross a (-b) = -cross a b := by
  ext i
  fin_cases i <;> simp [cross_apply0, cross_apply1, cross_apply2] <;> ring

theorem cross_sub_left (a a' b : E3) : cross (a - a') b = cross a b - cross a' b := by
  ext i
  fin_cases i <;> simp [cross_apply0, cross_apply1, cross_apply2] <;> ring

theorem cross_sub_right (a b b' : E3) : cross a (b - b') = cross a b - cross a b' := by
  ext i
  fin_cases i <;> simp [cross_apply0, cross_apply1, cross_apply2] <;> ring

theorem cross_zero_left (b : E3) : cross 0 b = 0 := by
  ext i
  fin_cases i <;> simp [cross_apply0, cross_apply1, cross_apply2]

theorem cross_zero_right (a : E3) : cross a 0 = 0 := by
  ext i
  fin_cases i <;> simp [cross_apply0, cross_apply1, cross_apply2]

/-- The scalar triple product `a·(b × c)` is the determinant with rows `a, b, c`. -/
theorem inner_cross_eq_det (a b c : E3) :
    ⟪a, cross b c⟫ = Matrix.det ![a.ofLp, b.ofLp, c.ofLp] := by
  rw [← triple_product_eq_det]
  simp [PiLp.inner_apply, dotProduct, cross, mul_comm]

theorem inner_cross_expand (a b c : E3) :
    ⟪a, cross b c⟫ = a 0 * (b 1 * c 2 - b 2 * c 1) + a 1 * (b 2 * c 0 - b 0 * c 2)
      + a 2 * (b 0 * c 1 - b 1 * c 0) := by
  rw [inner_eq_sum, cross_apply0, cross_apply1, cross_apply2]

/-- Cyclic symmetry of the triple product. -/
theorem inner_cross_cyclic (a b c : E3) : ⟪a, cross b c⟫ = ⟪b, cross c a⟫ := by
  rw [inner_cross_expand, inner_cross_expand]; ring

theorem inner_cross_cyclic' (a b c : E3) : ⟪a, cross b c⟫ = ⟪c, cross a b⟫ := by
  rw [inner_cross_cyclic, inner_cross_cyclic]

theorem inner_cross_self_left (a b : E3) : ⟪a, cross a b⟫ = 0 := by
  rw [inner_cross_expand]; ring

theorem inner_cross_self_right (a b : E3) : ⟪b, cross a b⟫ = 0 := by
  rw [inner_cross_expand]; ring

theorem inner_cross_swap (a b c : E3) : ⟪a, cross c b⟫ = -⟪a, cross b c⟫ := by
  rw [cross_comm_neg c b, inner_neg_right]

/-- BAC-CAB: `a × (b × c) = ⟪a, c⟫ b − ⟪a, b⟫ c`. -/
theorem cross_cross_eq (a b c : E3) : cross a (cross b c) = ⟪a, c⟫ • b - ⟪a, b⟫ • c := by
  ext i
  fin_cases i <;> simp [cross_apply0, cross_apply1, cross_apply2, inner_eq_sum] <;> ring

/-- Lagrange's identity: `|a × b|² = |a|²|b|² − ⟪a, b⟫²`. -/
theorem norm_cross_sq (a b : E3) : ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_eq_sum, inner_eq_sum, inner_eq_sum, inner_eq_sum, cross_apply0, cross_apply1,
    cross_apply2]
  ring

theorem norm_cross_le (a b : E3) : ‖cross a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h : ‖cross a b‖ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
    rw [norm_cross_sq, mul_pow]
    nlinarith [sq_nonneg ⟪a, b⟫]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- Three vectors orthogonal to a nonzero vector are linearly dependent: their triple product
vanishes (the paper's "every scalar triple product of these three vectors vanishes",
sm-3:2849-2851). -/
theorem inner_cross_eq_zero_of_orth {g a b c : E3} (hg : g ≠ 0) (ha : ⟪g, a⟫ = 0)
    (hb : ⟪g, b⟫ = 0) (hc : ⟪g, c⟫ = 0) : ⟪a, cross b c⟫ = 0 := by
  rw [inner_cross_eq_det]
  have key : (Matrix.of ![a.ofLp, b.ofLp, c.ofLp]).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨g.ofLp, fun h => hg (by ext i; simpa using congrFun h i), ?_⟩
    rw [inner_eq_sum] at ha hb hc
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> linarith
  exact key

/-- Linearly independent vectors have a nonzero cross product. -/
theorem cross_ne_zero_of_linearIndependent {a b : E3} (h : LinearIndependent ℝ ![a, b]) :
    cross a b ≠ 0 := by
  intro h0
  have ha : a ≠ 0 := h.ne_zero 0
  have hrel := cross_cross_eq a a b
  rw [h0, cross_zero_right] at hrel
  have hpair := LinearIndependent.pair_iff.1 h (-⟪a, b⟫) ⟪a, a⟫ (by
    rw [neg_smul]; rw [eq_comm, sub_eq_zero] at hrel; rw [hrel]; simp)
  have : ⟪a, a⟫ = 0 := hpair.2
  exact ha (inner_self_eq_zero.1 this)

/-- The cross product as a continuous bilinear map. -/
def crossₗ : E3 →ₗ[ℝ] E3 →ₗ[ℝ] E3 :=
  LinearMap.mk₂ ℝ cross cross_add_left cross_smul_left cross_add_right cross_smul_right

def crossL : E3 →L[ℝ] E3 →L[ℝ] E3 :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E3 →ₗ[ℝ] E3) ≃ₗ[ℝ] (E3 →L[ℝ] E3)).toLinearMap ∘ₗ crossₗ)

@[simp] theorem crossL_apply (a b : E3) : crossL a b = cross a b := rfl

theorem contDiff_cross {n : WithTop ℕ∞} : ContDiff ℝ n (fun p : E3 × E3 => cross p.1 p.2) :=
  (crossL.isBoundedBilinearMap).contDiff

theorem ContDiff.cross {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞}
    {f g : X → E3} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun x => cross (f x) (g x)) :=
  contDiff_cross.comp (hf.prodMk hg)

theorem HasFDerivAt.cross {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f g : X → E3}
    {f' g' : X →L[ℝ] E3} {x : X} (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun y => cross (f y) (g y))
      ((crossL (f x)).comp g' + (crossL.comp f').flip (g x)) x :=
  (crossL.hasFDerivAt.comp x hf).clm_apply hg

/-- Projection along a unit vector `ν` ("projected along ν"): `w − ⟪w, ν⟫ ν`. -/
def projAlong (ν w : E3) : E3 := w - ⟪w, ν⟫ • ν

/-- "`w` is parallel to `ν`": `w = t ν` for a real `t`. -/
def Parallel (w ν : E3) : Prop := ∃ t : ℝ, w = t • ν

theorem inner_projAlong (ν w : E3) (hν : ‖ν‖ = 1) : ⟪projAlong ν w, ν⟫ = 0 := by
  simp [projAlong, inner_sub_left, inner_smul_left, hν]

theorem inner_projAlong' (ν w : E3) (hν : ‖ν‖ = 1) : ⟪ν, projAlong ν w⟫ = 0 := by
  rw [real_inner_comm]; exact inner_projAlong ν w hν

theorem parallel_iff_projAlong_eq_zero (ν w : E3) (hν : ‖ν‖ = 1) :
    Parallel w ν ↔ projAlong ν w = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    simp [projAlong, inner_smul_left, hν]
  · intro h
    exact ⟨⟪w, ν⟫, by rw [projAlong, sub_eq_zero] at h; exact h⟩

theorem projAlong_add (ν w w' : E3) : projAlong ν (w + w') = projAlong ν w + projAlong ν w' := by
  simp [projAlong, inner_add_left, add_smul]; abel

theorem projAlong_smul (ν : E3) (t : ℝ) (w : E3) : projAlong ν (t • w) = t • projAlong ν w := by
  simp [projAlong, inner_smul_left, smul_sub, smul_smul]

theorem projAlong_neg (ν w : E3) : projAlong ν (-w) = -projAlong ν w := by
  simp [projAlong, inner_neg_left]; abel

/-- `det(P a, P b, ν) = det(a, b, ν)`: the triple product with `ν` sees only the projections. -/
theorem inner_cross_projAlong (ν a b : E3) :
    ⟪ν, cross (projAlong ν a) (projAlong ν b)⟫ = ⟪ν, cross a b⟫ := by
  simp only [projAlong, cross_sub_left, cross_sub_right, cross_smul_left, cross_smul_right,
    inner_sub_right, inner_smul_right, inner_cross_self_left, inner_cross_self_right]
  ring

end LinkingCalculus

open LinkingCalculus

/-! ## 1. The linking pairing (sm-3:2787-2790) -/

/-- sm-3:2792: the Gauss map of the pair, `G(u,v) = (C₂(v) − C₁(u))/|C₂(v) − C₁(u)|`. -/
def gaussMap (C₁ C₂ : ℝ → E3) (u v : ℝ) : E3 := ‖C₂ v - C₁ u‖⁻¹ • (C₂ v - C₁ u)

/-- `G_u = ∂G/∂u`, the derivative of the `u`-slice. -/
def pderivU (G : ℝ → ℝ → E3) (u v : ℝ) : E3 := deriv (fun u' => G u' v) u

/-- `G_v = ∂G/∂v`, the derivative of the `v`-slice. -/
def pderivV (G : ℝ → ℝ → E3) (u v : ℝ) : E3 := deriv (fun v' => G u v') v

/-- The integrand `G·(G_u × G_v)` of sm-3:2791 (the pullback of the area form of `S²`). -/
def gaussDensity (G : ℝ → ℝ → E3) (u v : ℝ) : ℝ :=
  ⟪G u v, cross (pderivU G u v) (pderivV G u v)⟫

/-- `(1/4π) ∫_{S¹×S¹} G·(G_u × G_v) du dv` with `S¹ = ℝ/Pℤ` (FR-LC-1: the period `P > 0` is a
parameter; the paper's `S¹` is `ℝ/2πℤ` in the consumer sm-3:2398 and `ℝ/ℤ` elsewhere). -/
def gaussIntegral (P : ℝ) (G : ℝ → ℝ → E3) : ℝ :=
  (1 / (4 * π)) * ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, gaussDensity G u v

/-- sm-3:2788-2792, the normalized linking pairing
`ℓ(C₁,C₂) = (1/4π) ∫_{S¹×S¹} G·(G_u × G_v) du dv`, `G = (C₂(v) − C₁(u))/|C₂(v) − C₁(u)|`. -/
def linking (P : ℝ) (C₁ C₂ : ℝ → E3) : ℝ := gaussIntegral P (gaussMap C₁ C₂)

/-! ### Basic facts on the Gauss map and the density -/

theorem gaussMap_swap (C₁ C₂ : ℝ → E3) (u v : ℝ) : gaussMap C₂ C₁ v u = -gaussMap C₁ C₂ u v := by
  simp only [gaussMap, ← smul_neg, neg_sub, norm_sub_rev]

theorem norm_gaussMap {C₁ C₂ : ℝ → E3} {u v : ℝ} (h : C₂ v ≠ C₁ u) :
    ‖gaussMap C₁ C₂ u v‖ = 1 := by
  have hne : ‖C₂ v - C₁ u‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 h)
  simp [gaussMap, norm_smul, hne]

theorem gaussMap_ne_zero {C₁ C₂ : ℝ → E3} {u v : ℝ} (h : C₂ v ≠ C₁ u) :
    gaussMap C₁ C₂ u v ≠ 0 := by
  intro h0
  have := norm_gaussMap h
  rw [h0, norm_zero] at this
  exact zero_ne_one this

/-- The Gauss map of a smooth disjoint pair is smooth (the denominator "is bounded away from zero
on the compact parameter torus", sm-3:2828-2829). -/
theorem contDiff_gaussMap {n : WithTop ℕ∞} {C₁ C₂ : ℝ → E3} (h₁ : ContDiff ℝ n C₁)
    (h₂ : ContDiff ℝ n C₂) (hd : ∀ u v, C₂ v ≠ C₁ u) :
    ContDiff ℝ n (fun p : ℝ × ℝ => gaussMap C₁ C₂ p.1 p.2) := by
  have hD : ContDiff ℝ n (fun p : ℝ × ℝ => C₂ p.2 - C₁ p.1) :=
    (h₂.comp contDiff_snd).sub (h₁.comp contDiff_fst)
  have hne : ∀ p : ℝ × ℝ, C₂ p.2 - C₁ p.1 ≠ 0 := fun p => sub_ne_zero.2 (hd p.1 p.2)
  exact ((hD.norm ℝ hne).inv (fun p => norm_ne_zero_iff.2 (hne p))).smul hD

theorem hasDerivAt_sliceU {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : ℝ × ℝ → Y}
    {u v : ℝ} (h : DifferentiableAt ℝ F (u, v)) :
    HasDerivAt (fun u' => F (u', v)) (fderiv ℝ F (u, v) (1, 0)) u := by
  have h1 : HasDerivAt (fun u' : ℝ => (u', v)) ((1 : ℝ), (0 : ℝ)) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u v)
  exact h.hasFDerivAt.comp_hasDerivAt u h1

theorem hasDerivAt_sliceV {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : ℝ × ℝ → Y}
    {u v : ℝ} (h : DifferentiableAt ℝ F (u, v)) :
    HasDerivAt (fun v' => F (u, v')) (fderiv ℝ F (u, v) (0, 1)) v := by
  have h1 : HasDerivAt (fun v' : ℝ => (u, v')) ((0 : ℝ), (1 : ℝ)) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id v)
  exact h.hasFDerivAt.comp_hasDerivAt v h1

theorem pderivU_eq_fderiv {G : ℝ → ℝ → E3} {u v : ℝ} (h : DifferentiableAt ℝ (uncurry G) (u, v)) :
    pderivU G u v = fderiv ℝ (uncurry G) (u, v) (1, 0) :=
  (hasDerivAt_sliceU (F := uncurry G) h).deriv

theorem pderivV_eq_fderiv {G : ℝ → ℝ → E3} {u v : ℝ} (h : DifferentiableAt ℝ (uncurry G) (u, v)) :
    pderivV G u v = fderiv ℝ (uncurry G) (u, v) (0, 1) :=
  (hasDerivAt_sliceV (F := uncurry G) h).deriv

/-- For a `C¹` map `G`, the density `G·(G_u × G_v)` is the smooth expression in `G` and its
derivative (`m + 1 ≤ n` derivatives remain). -/
theorem gaussDensity_eq_of_contDiff {n : WithTop ℕ∞} {G : ℝ → ℝ → E3} (hG : ContDiff ℝ n (uncurry G))
    (hn : n ≠ 0) :
    uncurry (gaussDensity G) = fun p : ℝ × ℝ =>
      ⟪uncurry G p, cross (fderiv ℝ (uncurry G) p (1, 0)) (fderiv ℝ (uncurry G) p (0, 1))⟫ := by
  funext p
  have hd : DifferentiableAt ℝ (uncurry G) (p.1, p.2) :=
    (hG.differentiable hn) (p.1, p.2)
  simp only [uncurry, gaussDensity, pderivU_eq_fderiv hd, pderivV_eq_fderiv hd]

theorem contDiff_gaussDensity {m n : WithTop ℕ∞} {G : ℝ → ℝ → E3} (hG : ContDiff ℝ n (uncurry G))
    (hmn : m + 1 ≤ n) : ContDiff ℝ m (uncurry (gaussDensity G)) := by
  have hn : n ≠ 0 := by rintro rfl; simp at hmn
  rw [gaussDensity_eq_of_contDiff hG hn]
  have hG' : ContDiff ℝ m (fderiv ℝ (uncurry G)) := hG.fderiv_right hmn
  have hGm : ContDiff ℝ m (uncurry G) := hG.of_le (le_trans (by simp) hmn)
  exact hGm.inner ℝ ((hG'.clm_apply contDiff_const).cross (hG'.clm_apply contDiff_const))

theorem continuous_gaussDensity {G : ℝ → ℝ → E3} (hG : ContDiff ℝ ∞ (uncurry G)) :
    Continuous (uncurry (gaussDensity G)) :=
  (contDiff_gaussDensity (m := 0) hG (by simp)).continuous

/-- Fubini for a continuous integrand on a rectangle (the paper's "ordinary smooth calculus on a
compact domain", sm-3:2830-2832). -/
theorem integral_integral_swap_of_continuous {f : ℝ → ℝ → ℝ} (hf : Continuous (uncurry f))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  apply MeasureTheory.integral_integral_swap
  rw [MeasureTheory.Measure.prod_restrict]
  have hK : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  exact (hf.continuousOn.integrableOn_compact hK).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem continuous_parametric_integral {f : ℝ → ℝ → ℝ} (hf : Continuous (uncurry f)) (c d : ℝ) :
    Continuous fun x => ∫ y in c..d, f x y :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf c d

/-- "a smooth oriented parametrized circle in `ℝ³`": a `C^∞` map `ℝ → ℝ³` of period `P`
(`S¹ = ℝ/Pℤ`); the orientation is that of the parameter. -/
structure IsSmoothCircle (P : ℝ) (C : ℝ → E3) : Prop where
  smooth : ContDiff ℝ ∞ C
  periodic : Periodic C P

/-- sm-3:2787-2788 "two disjoint smooth oriented parametrized circles `C₁, C₂` in oriented `ℝ³`". -/
structure DisjointPair (P : ℝ) (C₁ C₂ : ℝ → E3) : Prop where
  pos : 0 < P
  circle₁ : IsSmoothCircle P C₁
  circle₂ : IsSmoothCircle P C₂
  disjoint : ∀ u v, C₂ v ≠ C₁ u

/-- sm-3:2794-2795 "smooth families of disjoint oriented pairs", parameter `s ∈ [0,1]`: the maps
`(s,u) ↦ Cᵢ(s,u)` are jointly `C^∞` on `ℝ × ℝ` (FR-LC-3: a smooth family on `[0,1]` is read as the
restriction of a smooth map on `ℝ × ℝ`), each `Cᵢ(s,·)` is `P`-periodic, and the pair is disjoint at
every `s ∈ [0,1]`. -/
structure DisjointPairFamily (P : ℝ) (C₁ C₂ : ℝ → ℝ → E3) : Prop where
  pos : 0 < P
  smooth₁ : ContDiff ℝ ∞ (uncurry C₁)
  smooth₂ : ContDiff ℝ ∞ (uncurry C₂)
  periodic₁ : ∀ s, Periodic (C₁ s) P
  periodic₂ : ∀ s, Periodic (C₂ s) P
  disjoint : ∀ s ∈ Icc (0:ℝ) 1, ∀ u v, C₂ s v ≠ C₁ s u

/-- sm-3:2795-2798 "Call a direction `ν ∈ S²` generic for the pair if at every parameter pair
`(u,v)` at which `C₂(v) − C₁(u)` is parallel to `ν` the tangents of the two circles projected along
`ν` are linearly independent". -/
structure GenericDirection (C₁ C₂ : ℝ → E3) (ν : E3) : Prop where
  unit : ‖ν‖ = 1
  indep : ∀ u v, Parallel (C₂ v - C₁ u) ν →
    LinearIndependent ℝ ![projAlong ν (deriv C₁ u), projAlong ν (deriv C₂ v)]

/-- The mixed crossings of the projection along `ν`, one fundamental domain `[0,P)²` of the
parameter torus: the parameter pairs `(u,v)` at which `C₂(v) − C₁(u)` is parallel to `ν`. -/
def mixedCrossings (P : ℝ) (C₁ C₂ : ℝ → E3) (ν : E3) : Set (ℝ × ℝ) :=
  {p | p ∈ Ico (0:ℝ) P ×ˢ Ico (0:ℝ) P ∧ Parallel (C₂ p.2 - C₁ p.1) ν}

/-- sm-3:2800-2801 "orient the projection plane so that its positive basis followed by `ν` is
positive in `ℝ³`": for `x, y` in the plane `ν^⊥`, `det_plane(x, y) = det(x, y, ν) = ⟪ν, x × y⟫`. -/
def planeDet (ν x y : E3) : ℝ := ⟪ν, cross x y⟫

/-- sm-3:2799-2804: at a mixed crossing `(u,v)`, "let `ν` point toward the observer …; at a mixed
crossing the strand nearer the observer is over"; the overpass-first sign `sgn det(u_o, u_u)` of the
projected over and under tangents.  `C₂(v)` is nearer the observer iff `⟪C₂(v) − C₁(u), ν⟫ > 0`. -/
def lcCrossingSign (C₁ C₂ : ℝ → E3) (ν : E3) (p : ℝ × ℝ) : ℝ :=
  if 0 < ⟪C₂ p.2 - C₁ p.1, ν⟫ then
    Real.sign (planeDet ν (projAlong ν (deriv C₂ p.2)) (projAlong ν (deriv C₁ p.1)))
  else Real.sign (planeDet ν (projAlong ν (deriv C₁ p.1)) (projAlong ν (deriv C₂ p.2)))

/-- **The isolated hypothesis** fd:regular-pole-count (sm-3:2894-2897), the degree formula for a
regular value: for a smooth doubly periodic `G : S¹×S¹ → S²` and a regular value `N` of `G`
(every preimage of `N` has `G·(G_u × G_v) ≠ 0`, i.e. `G_u, G_v` span the tangent plane at `N`),
`∫_{S¹×S¹} G^*ω = ∑_{p ∈ G⁻¹(N)} σ(p)` with `ω` the outward area form of `S²` divided by `4π` and
`σ(p) = sgn (G·(G_u × G_v))(p)` the local orientation sign.  Its printed proof (sm-3:2869-2916)
uses the primitive `λ_N` of `ω` on `S² ∖ {N}` and Green's formula on the torus minus small discs;
this Stokes-type argument is not formalised here (no Mathlib support for Stokes on a punctured
torus or for degree theory), and the row's mixed-crossing clause is proved from this statement. -/
def RegularPoleCount : Prop :=
  ∀ (P : ℝ) (G : ℝ → ℝ → E3) (N : E3), 0 < P → ContDiff ℝ ∞ (uncurry G) →
    (∀ v, Periodic (fun u => G u v) P) → (∀ u, Periodic (G u) P) → (∀ u v, ‖G u v‖ = 1) →
    ‖N‖ = 1 → (∀ u v, G u v = N → gaussDensity G u v ≠ 0) →
    ∀ hfin : {p : ℝ × ℝ | p ∈ Ico (0:ℝ) P ×ˢ Ico (0:ℝ) P ∧ G p.1 p.2 = N}.Finite,
      gaussIntegral P G = ∑ p ∈ hfin.toFinset, Real.sign (gaussDensity G p.1 p.2)

/-- sm-3:2808-2810 "let `C_s`, `0 ≤ s ≤ 1`, be a smooth family of embedded oriented circles and let
`v_s` be a smooth vector field along them, everywhere linearly independent of `∂_u C_s`":
`(s,u) ↦ C s u` and `(s,u) ↦ v s u` jointly `C^∞` (FR-LC-3), `P`-periodic in `u`; for `s ∈ [0,1]`
the circle `C s` is embedded (injective on `ℝ/Pℤ`) and `v s u ∉ ℝ ∂_u C s u`. -/
structure FramedFamily (P : ℝ) (C v : ℝ → ℝ → E3) : Prop where
  pos : 0 < P
  smooth : ContDiff ℝ ∞ (uncurry C)
  smooth_v : ContDiff ℝ ∞ (uncurry v)
  periodic : ∀ s, Periodic (C s) P
  periodic_v : ∀ s, Periodic (v s) P
  embedded : ∀ s ∈ Icc (0:ℝ) 1, ∀ u u', C s u = C s u' → ∃ k : ℤ, u' = u + k * P
  indep : ∀ s ∈ Icc (0:ℝ) 1, ∀ u, LinearIndependent ℝ ![deriv (C s) u, v s u]

/-- The pushoff `C_s + ε v_s` (sm-3:2812). -/
def pushoff (C v : ℝ → E3) (ε : ℝ) : ℝ → E3 := fun u => C u + ε • v u

/-- The standard contact form `α = dz − y dx` of sm-3:2817, evaluated at the point `p` on the
vector `w`. -/
def lcContactForm (p w : E3) : ℝ := w 2 - p 1 * w 0

/-- The coordinate field `∂_y`. -/
def ey : E3 := EuclideanSpace.single 1 1

/-- "positive transverse embedding": a smooth embedded circle `T` with `(dz − y dx)(∂_u T) > 0`. -/
structure IsPositiveTransverseEmbedding (P : ℝ) (T : ℝ → E3) : Prop where
  circle : IsSmoothCircle P T
  embedded : ∀ u u', T u = T u' → ∃ k : ℤ, u' = u + k * P
  positive : ∀ u, 0 < lcContactForm (T u) (deriv T u)

/-- sm-3:2816-2817 "`T_s : S¹ → ℝ³`, `0 ≤ s ≤ 1`, a smooth family of embeddings with
`(dz − y dx)(∂_u T_s) > 0`". -/
structure TransverseFamily (P : ℝ) (T : ℝ → ℝ → E3) : Prop where
  pos : 0 < P
  smooth : ContDiff ℝ ∞ (uncurry T)
  periodic : ∀ s, Periodic (T s) P
  embedded : ∀ s ∈ Icc (0:ℝ) 1, ∀ u u', T s u = T s u' → ∃ k : ℤ, u' = u + k * P
  positive : ∀ s ∈ Icc (0:ℝ) 1, ∀ u, 0 < lcContactForm (T s u) (deriv (T s) u)

/-- sm-3:2820-2824, fd:framed-linking: `sl(T) = ℓ(T, T + ε ∂_y)`. -/
def selfLinking (P : ℝ) (T : ℝ → E3) (ε : ℝ) : ℝ := linking P T (pushoff T (fun _ => ey) ε)

/-- fd:linking-calculus (sm-3:2785-2830), one field per printed clause. -/
structure LinkingCalculusDataOf : Prop where
  /-- sm-3:2794 "It is symmetric". -/
  symm : ∀ (P : ℝ) (C₁ C₂ : ℝ → E3), DisjointPair P C₁ C₂ → linking P C₁ C₂ = linking P C₂ C₁
  /-- sm-3:2794-2795 "and is constant under smooth families of disjoint oriented pairs". -/
  family_const : ∀ (P : ℝ) (C₁ C₂ : ℝ → ℝ → E3), DisjointPairFamily P C₁ C₂ →
    ∀ s ∈ Icc (0:ℝ) 1, ∀ s' ∈ Icc (0:ℝ) 1, linking P (C₁ s) (C₂ s) = linking P (C₁ s') (C₂ s')
  /-- sm-3:2798-2799 "the projection along such a `ν` displays the pair with finitely many
  transverse mixed crossings" (transversality is the defining independence of `GenericDirection`). -/
  finite_crossings : ∀ (P : ℝ) (C₁ C₂ : ℝ → E3) (ν : E3), DisjointPair P C₁ C₂ →
    GenericDirection C₁ C₂ ν → (mixedCrossings P C₁ C₂ ν).Finite
  /-- sm-3:2802-2804 "Then `ℓ(C₁,C₂)` equals one half the sum over the mixed crossings of the
  overpass-first sign `sgn det(u_o,u_u)` of the projected over and under tangents", proved from the
  isolated hypothesis `RegularPoleCount` (fd:regular-pole-count, sm-3:2894-2897). -/
  crossing_formula : RegularPoleCount → ∀ (P : ℝ) (C₁ C₂ : ℝ → E3) (ν : E3),
    DisjointPair P C₁ C₂ → GenericDirection C₁ C₂ ν →
    linking P C₁ C₂ = (1 / 2) * ∑ᶠ p ∈ mixedCrossings P C₁ C₂ ν, lcCrossingSign C₁ C₂ ν p
  /-- sm-3:2810-2812 "One common sufficiently small positive `ε` gives disjoint framed pairs
  `(C_s, C_s + εv_s)` throughout the family." -/
  framing_uniform : ∀ (P : ℝ) (C v : ℝ → ℝ → E3), FramedFamily P C v →
    ∃ ε₀ > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ → DisjointPair P (C s) (pushoff (C s) (v s) ε)
  /-- sm-3:2812-2813 "Their pairing is independent of that radius and of `s`": for any common radius
  `ε₀` as in the previous clause, `ℓ(C_s, C_s + εv_s)` does not depend on `s ∈ [0,1]` or
  `ε ∈ (0, ε₀]`. -/
  framing_invariant : ∀ (P : ℝ) (C v : ℝ → ℝ → E3), FramedFamily P C v → ∀ ε₀ > 0,
    (∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ u u', pushoff (C s) (v s) ε u ≠ C s u') →
    ∀ s ∈ Icc (0:ℝ) 1, ∀ s' ∈ Icc (0:ℝ) 1, ∀ ε ε', 0 < ε → ε ≤ ε₀ → 0 < ε' → ε' ≤ ε₀ →
      linking P (C s) (pushoff (C s) (v s) ε) = linking P (C s') (pushoff (C s') (v s') ε')
  /-- sm-3:2813-2814 "This includes a homotopy of normal framings on a fixed curve": the previous
  clause with `C_s = C` constant. -/
  framing_homotopy : ∀ (P : ℝ) (C : ℝ → E3) (v : ℝ → ℝ → E3), FramedFamily P (fun _ => C) v →
    ∀ ε₀ > 0, (∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ u u', pushoff C (v s) ε u ≠ C u') →
    ∀ s ∈ Icc (0:ℝ) 1, ∀ s' ∈ Icc (0:ℝ) 1, ∀ ε ε', 0 < ε → ε ≤ ε₀ → 0 < ε' → ε' ≤ ε₀ →
      linking P C (pushoff C (v s) ε) = linking P C (pushoff C (v s') ε')
  /-- sm-3:2817-2820 "there is one `ε₀ > 0` such that `T_s` and `T_s + ε∂_y` are disjoint positive
  transverse embeddings for every `s` and `0 < ε ≤ ε₀`". -/
  transverse_uniform : ∀ (P : ℝ) (T : ℝ → ℝ → E3), TransverseFamily P T →
    ∃ ε₀ > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ →
      IsPositiveTransverseEmbedding P (T s) ∧
      IsPositiveTransverseEmbedding P (pushoff (T s) (fun _ => ey) ε) ∧
      DisjointPair P (T s) (pushoff (T s) (fun _ => ey) ε)
  /-- sm-3:2820-2824 "The number `sl(T_s) = ℓ(T_s, T_s + ε∂_y)` is independent of such `ε` and of
  `s`": for any `ε₀` making the pairs disjoint as in the previous clause. -/
  self_linking_invariant : ∀ (P : ℝ) (T : ℝ → ℝ → E3), TransverseFamily P T → ∀ ε₀ > 0,
    (∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ u u', pushoff (T s) (fun _ => ey) ε u ≠ T s u') →
    ∀ s ∈ Icc (0:ℝ) 1, ∀ s' ∈ Icc (0:ℝ) 1, ∀ ε ε', 0 < ε → ε ≤ ε₀ → 0 < ε' → ε' ≤ ε₀ →
      selfLinking P (T s) ε = selfLinking P (T s') ε'



/-! ## 2. Symmetry (sm-3:2794, proof sm-3:2838-2841) -/

/-- Exchanging the two curves negates `G` and both partial derivatives (with the variables
exchanged), and the triple product is unchanged: `G̃·(G̃_u × G̃_v)(v,u) = G·(G_u × G_v)(u,v)`. -/
theorem gaussDensity_swap (C₁ C₂ : ℝ → E3) (u v : ℝ) :
    gaussDensity (gaussMap C₂ C₁) v u = gaussDensity (gaussMap C₁ C₂) u v := by
  have h1 : (fun x => gaussMap C₂ C₁ x u) = -(fun x => gaussMap C₁ C₂ u x) :=
    funext fun x => gaussMap_swap C₁ C₂ u x
  have h2 : (fun x => gaussMap C₂ C₁ v x) = -(fun x => gaussMap C₁ C₂ x v) :=
    funext fun x => gaussMap_swap C₁ C₂ x v
  have h0 : gaussMap C₂ C₁ v u = -gaussMap C₁ C₂ u v := gaussMap_swap C₁ C₂ u v
  unfold gaussDensity pderivU pderivV
  rw [h1, h2, h0, deriv.neg, deriv.neg, cross_neg_left, cross_neg_right, neg_neg, inner_neg_left,
    inner_cross_swap, neg_neg]

/-- sm-3:2794 "It is symmetric": `ℓ(C₁,C₂) = ℓ(C₂,C₁)` (exchange of the curves and of the
integration variables, then Fubini on the compact parameter torus). -/
theorem DisjointPair.linking_comm {P : ℝ} {C₁ C₂ : ℝ → E3} (h : DisjointPair P C₁ C₂) :
    linking P C₁ C₂ = linking P C₂ C₁ := by
  unfold linking gaussIntegral
  congr 1
  have hcont : Continuous (uncurry (gaussDensity (gaussMap C₁ C₂))) :=
    continuous_gaussDensity (contDiff_gaussMap h.circle₁.smooth h.circle₂.smooth h.disjoint)
  have hsw : ∀ u v, gaussDensity (gaussMap C₂ C₁) u v = gaussDensity (gaussMap C₁ C₂) v u :=
    fun u v => gaussDensity_swap C₁ C₂ v u
  simp_rw [hsw]
  exact integral_integral_swap_of_continuous hcont h.pos.le h.pos.le

/-! ## 3. Packaging of circles, pushoffs and families -/

theorem periodic_deriv {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : ℝ → Y} {c : ℝ}
    (h : Periodic f c) : Periodic (deriv f) c := by
  intro x
  have hf : (fun y => f (y + c)) = f := funext fun y => h y
  rw [← deriv_comp_add_const, hf]

/-- A slice `C s` of a jointly smooth family is smooth. -/
theorem contDiff_slice {C : ℝ → ℝ → E3} (h : ContDiff ℝ ∞ (uncurry C)) (s : ℝ) :
    ContDiff ℝ ∞ (C s) :=
  h.comp (contDiff_const.prodMk contDiff_id)

theorem contDiff_pushoff {C v : ℝ → E3} (hC : ContDiff ℝ ∞ C) (hv : ContDiff ℝ ∞ v) (ε : ℝ) :
    ContDiff ℝ ∞ (pushoff C v ε) := by
  show ContDiff ℝ ∞ (fun u => C u + ε • v u)
  exact hC.add (hv.const_smul ε)

theorem periodic_pushoff {C v : ℝ → E3} {P : ℝ} (hC : Periodic C P) (hv : Periodic v P) (ε : ℝ) :
    Periodic (pushoff C v ε) P := fun u => by simp [pushoff, hC u, hv u]

theorem FramedFamily.isSmoothCircle {P : ℝ} {C v : ℝ → ℝ → E3} (h : FramedFamily P C v) (s : ℝ) :
    IsSmoothCircle P (C s) :=
  ⟨contDiff_slice h.smooth s, h.periodic s⟩

theorem FramedFamily.isSmoothCircle_pushoff {P : ℝ} {C v : ℝ → ℝ → E3} (h : FramedFamily P C v)
    (s ε : ℝ) : IsSmoothCircle P (pushoff (C s) (v s) ε) :=
  ⟨contDiff_pushoff (contDiff_slice h.smooth s) (contDiff_slice h.smooth_v s) ε,
    periodic_pushoff (h.periodic s) (h.periodic_v s) ε⟩

/-- A disjoint pushoff is a disjoint pair of smooth circles ("disjoint framed pairs"). -/
theorem FramedFamily.disjointPair_pushoff {P : ℝ} {C v : ℝ → ℝ → E3} (h : FramedFamily P C v)
    (s ε : ℝ) (hd : ∀ u u', pushoff (C s) (v s) ε u ≠ C s u') :
    DisjointPair P (C s) (pushoff (C s) (v s) ε) :=
  ⟨h.pos, h.isSmoothCircle s, h.isSmoothCircle_pushoff s ε, fun u u' => hd u' u⟩

/-- The paper's first sentence of the framing paragraph, reduced to the disjointness statement
proved in the framing section. -/
theorem FramedFamily.exists_uniform_disjointPair_of
    (hB : ∀ {P : ℝ} {C v : ℝ → ℝ → E3}, FramedFamily P C v →
      ∃ ε₀ > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ u u', pushoff (C s) (v s) ε u ≠ C s u')
    {P : ℝ} {C v : ℝ → ℝ → E3} (h : FramedFamily P C v) :
    ∃ ε₀ > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ → DisjointPair P (C s) (pushoff (C s) (v s) ε) := by
  obtain ⟨ε₀, hε₀, hd⟩ := hB h
  exact ⟨ε₀, hε₀, fun s hs ε hε hεε₀ => h.disjointPair_pushoff s ε (hd s hs ε hε hεε₀)⟩

/-! ## 4. Interpolation of parameters: the paper's "interpolating between two positive radii
stays in the same disc" (sm-3:2968-2970), realised with `Real.smoothTransition`. -/

namespace LinkingCalculus.Interp

/-- `σ t = a + (b − a) τ(t)` with `τ` the smooth transition: `σ 0 = a`, `σ 1 = b`, values between
`a` and `b`. -/
def interp (a b t : ℝ) : ℝ := a + (b - a) * Real.smoothTransition t

theorem contDiff_interp (a b : ℝ) : ContDiff ℝ ∞ (interp a b) :=
  contDiff_const.add (contDiff_const.mul Real.smoothTransition.contDiff)

theorem interp_zero (a b : ℝ) : interp a b 0 = a := by
  simp [interp, Real.smoothTransition.zero_of_nonpos le_rfl]

theorem interp_one (a b : ℝ) : interp a b 1 = b := by
  simp [interp, Real.smoothTransition.one_of_one_le le_rfl]

theorem interp_mem_Icc {a b lo hi : ℝ} (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi) (t : ℝ) :
    interp a b t ∈ Icc lo hi := by
  have h0 := Real.smoothTransition.nonneg t
  have h1 := Real.smoothTransition.le_one t
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  constructor <;> unfold interp <;> nlinarith

theorem interp_mem_Ioc {a b lo hi : ℝ} (ha : a ∈ Ioc lo hi) (hb : b ∈ Ioc lo hi) (t : ℝ) :
    interp a b t ∈ Ioc lo hi := by
  have h0 := Real.smoothTransition.nonneg t
  have h1 := Real.smoothTransition.le_one t
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  refine ⟨?_, ?_⟩
  · unfold interp
    rcases h0.lt_or_eq with hpos | hzero
    · nlinarith [mul_pos hpos (sub_pos.2 hb0), mul_nonneg (sub_nonneg.2 h1) (sub_pos.2 ha0).le]
    · rw [← hzero]; simpa using ha0
  · unfold interp; nlinarith

end LinkingCalculus.Interp

open LinkingCalculus.Interp in
/-- sm-3:2812-2813 "Their pairing is independent of that radius and of `s`", from the constancy of
`ℓ` along global smooth families (`hglob`, proved in the family section): the parameters `(s, ε)`
and `(s', ε')` are joined by the smooth path `t ↦ (interp s s' t, interp ε ε' t)`, along which the
pairs stay disjoint. -/
theorem FramedFamily.linking_pushoff_eq_of_global
    (hglob : ∀ {P : ℝ}, 0 < P → ∀ {C₁ C₂ : ℝ → ℝ → E3}, ContDiff ℝ ∞ (uncurry C₁) →
      ContDiff ℝ ∞ (uncurry C₂) → (∀ s, Periodic (C₁ s) P) → (∀ s, Periodic (C₂ s) P) →
      (∀ s u v, C₂ s v ≠ C₁ s u) → ∀ s s', linking P (C₁ s) (C₂ s) = linking P (C₁ s') (C₂ s'))
    {P : ℝ} {C v : ℝ → ℝ → E3} (h : FramedFamily P C v) {ε₀ : ℝ}
    (hd : ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ u u', pushoff (C s) (v s) ε u ≠ C s u')
    {s s' : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (hs' : s' ∈ Icc (0:ℝ) 1) {ε ε' : ℝ} (hε : 0 < ε)
    (hεε₀ : ε ≤ ε₀) (hε' : 0 < ε') (hε'ε₀ : ε' ≤ ε₀) :
    linking P (C s) (pushoff (C s) (v s) ε) = linking P (C s') (pushoff (C s') (v s') ε') := by
  set σ : ℝ → ℝ := interp s s' with hσ
  set e : ℝ → ℝ := interp ε ε' with he
  have hσc : ContDiff ℝ ∞ σ := contDiff_interp s s'
  have hec : ContDiff ℝ ∞ e := contDiff_interp ε ε'
  have hσmem : ∀ t, σ t ∈ Icc (0:ℝ) 1 := fun t => interp_mem_Icc hs hs' t
  have hemem : ∀ t, e t ∈ Ioc 0 ε₀ := fun t => interp_mem_Ioc ⟨hε, hεε₀⟩ ⟨hε', hε'ε₀⟩ t
  -- the two families
  let D₁ : ℝ → ℝ → E3 := fun t u => C (σ t) u
  let D₂ : ℝ → ℝ → E3 := fun t u => pushoff (C (σ t)) (v (σ t)) (e t) u
  have hD₁ : ContDiff ℝ ∞ (uncurry D₁) :=
    h.smooth.comp ((hσc.comp contDiff_fst).prodMk contDiff_snd)
  have hD₂ : ContDiff ℝ ∞ (uncurry D₂) := by
    have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => v (σ p.1) p.2) :=
      h.smooth_v.comp ((hσc.comp contDiff_fst).prodMk contDiff_snd)
    exact hD₁.add ((hec.comp contDiff_fst).smul h1)
  have hp₁ : ∀ t, Periodic (D₁ t) P := fun t => h.periodic (σ t)
  have hp₂ : ∀ t, Periodic (D₂ t) P := fun t =>
    periodic_pushoff (h.periodic (σ t)) (h.periodic_v (σ t)) (e t)
  have hdis : ∀ t u u', D₂ t u' ≠ D₁ t u := fun t u u' =>
    hd (σ t) (hσmem t) (e t) (hemem t).1 (hemem t).2 u' u
  have key := hglob h.pos hD₁ hD₂ hp₁ hp₂ hdis 0 1
  have e0 : D₁ 0 = C s := by
    funext u; simp only [D₁, hσ, interp_zero]
  have e1 : D₁ 1 = C s' := by
    funext u; simp only [D₁, hσ, interp_one]
  have f0 : D₂ 0 = pushoff (C s) (v s) ε := by
    funext u; simp only [D₂, hσ, he, interp_zero]
  have f1 : D₂ 1 = pushoff (C s') (v s') ε' := by
    funext u; simp only [D₂, hσ, he, interp_one]
  rw [e0, e1, f0, f1] at key
  exact key

/-! ## 5. The transverse family (sm-3:2816-2824) -/

theorem ey_apply0 : ey 0 = 0 := by simp [ey]
theorem ey_apply1 : ey 1 = 1 := by simp [ey]
theorem ey_apply2 : ey 2 = 0 := by simp [ey]

theorem ey_ne_zero : ey ≠ 0 := by
  intro h
  have := congrArg (fun w : E3 => w 1) h
  simp [ey_apply1] at this

theorem contactForm_add_smul (p w : E3) (a b : ℝ) (w' : E3) :
    lcContactForm p (a • w + b • w') = a * lcContactForm p w + b * lcContactForm p w' := by
  simp only [lcContactForm, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem contactForm_ey (p : E3) : lcContactForm p ey = 0 := by
  simp [lcContactForm, ey_apply0, ey_apply2]

/-- `(dz − y dx)` at the pushed-off point: `α_{T+ε∂_y}(w) = α_T(w) − ε w_x` (sm-3:2994-2998). -/
theorem contactForm_pushoff (p w : E3) (ε : ℝ) :
    lcContactForm (p + ε • ey) w = lcContactForm p w - ε * w 0 := by
  simp only [lcContactForm, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, ey_apply1]; ring

/-- sm-3:2986-2988 "independence of the two columns follows by applying `dz − y dx` to a linear
relation: it is positive on `∂_u T_s` and zero on `∂_y`". -/
theorem TransverseFamily.framedFamily {P : ℝ} {T : ℝ → ℝ → E3} (h : TransverseFamily P T) :
    FramedFamily P T (fun _ _ => ey) where
  pos := h.pos
  smooth := h.smooth
  smooth_v := contDiff_const
  periodic := h.periodic
  periodic_v := fun _ _ => rfl
  embedded := h.embedded
  indep := fun s hs u => by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hα := h.positive s hs u
    have h1 := contactForm_add_smul (T s u) (deriv (T s) u) a b ey
    rw [hab, contactForm_ey] at h1
    simp only [lcContactForm, PiLp.zero_apply, mul_zero, sub_zero, add_zero] at h1
    have ha : a = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact h
      · exact absurd h (ne_of_gt hα)
    subst ha
    simp only [zero_smul, zero_add] at hab
    exact ⟨rfl, (smul_eq_zero.1 hab).resolve_right ey_ne_zero⟩

theorem TransverseFamily.isPositiveTransverseEmbedding {P : ℝ} {T : ℝ → ℝ → E3}
    (h : TransverseFamily P T) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    IsPositiveTransverseEmbedding P (T s) :=
  ⟨⟨contDiff_slice h.smooth s, h.periodic s⟩, h.embedded s hs, h.positive s hs⟩

theorem deriv_pushoff_const {T : ℝ → E3} (ε : ℝ) (u : ℝ) :
    deriv (pushoff T (fun _ => ey) ε) u = deriv T u := by
  show deriv (fun x => T x + ε • ey) u = deriv T u
  exact deriv_add_const (ε • ey)

/-- The tangent of a smooth family is jointly continuous: `∂_u T_s(u) = D(uncurry T)(s,u)(0,1)`. -/
theorem deriv_slice_eq {T : ℝ → ℝ → E3} (h : ContDiff ℝ ∞ (uncurry T)) (s u : ℝ) :
    deriv (T s) u = fderiv ℝ (uncurry T) (s, u) (0, 1) :=
  (hasDerivAt_sliceV (F := uncurry T) ((h.differentiable (by simp)) (s, u))).deriv

theorem continuous_fderiv_slice {T : ℝ → ℝ → E3} (h : ContDiff ℝ ∞ (uncurry T)) :
    Continuous fun p : ℝ × ℝ => fderiv ℝ (uncurry T) p (0, 1) :=
  (h.fderiv_right (m := 0) (by simp)).continuous.clm_apply continuous_const

/-- sm-3:2989-2998: `a₀ = min (z' − y x') > 0`, `M ≥ |x'|`, `ε₀ M < a₀/2` gives
`(dz − y dx)_{T_s + ε ∂_y}(∂_u T_s) > a₀/2 > 0`. -/
theorem TransverseFamily.exists_uniform_positive {P : ℝ} {T : ℝ → ℝ → E3}
    (h : TransverseFamily P T) :
    ∃ ε₀ > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ u,
      0 < lcContactForm (pushoff (T s) (fun _ => ey) ε u) (deriv (pushoff (T s) (fun _ => ey) ε) u) := by
  set K₀ : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) P with hK₀
  have hK₀c : IsCompact K₀ := isCompact_Icc.prod isCompact_Icc
  have hK₀ne : K₀.Nonempty := ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, h.pos.le⟩⟩⟩
  -- the contact form along the family, as a continuous function of `(s, u)`
  have hWc : Continuous (fun p : ℝ × ℝ => fderiv ℝ (uncurry T) p (0, 1)) :=
    continuous_fderiv_slice h.smooth
  have hTc : Continuous (uncurry T) := h.smooth.continuous
  have hαc : Continuous (fun p : ℝ × ℝ =>
      lcContactForm (uncurry T p) (fderiv ℝ (uncurry T) p (0, 1))) := by
    unfold lcContactForm
    fun_prop
  have hα_eq : ∀ s u, lcContactForm (uncurry T (s, u)) (fderiv ℝ (uncurry T) (s, u) (0, 1)) =
      lcContactForm (T s u) (deriv (T s) u) := by
    intro s u
    rw [deriv_slice_eq h.smooth]
    rfl
  obtain ⟨p₀, hp₀K, hp₀min⟩ := hK₀c.exists_isMinOn hK₀ne hαc.continuousOn
  set a₀ := lcContactForm (uncurry T p₀) (fderiv ℝ (uncurry T) p₀ (0, 1)) with ha₀
  have ha₀pos : 0 < a₀ := by
    rw [ha₀, show p₀ = (p₀.1, p₀.2) from rfl, hα_eq]
    exact h.positive p₀.1 hp₀K.1 p₀.2
  have hlow : ∀ p ∈ K₀, a₀ ≤ lcContactForm (uncurry T p) (fderiv ℝ (uncurry T) p (0, 1)) :=
    fun p hp => (isMinOn_iff.1 hp₀min) p hp
  -- a bound for the `x`-component of the tangent
  obtain ⟨M, hM⟩ := hK₀c.exists_bound_of_continuousOn
    (f := fun p : ℝ × ℝ => fderiv ℝ (uncurry T) p (0, 1) 0)
    (by fun_prop : Continuous fun p : ℝ × ℝ => fderiv ℝ (uncurry T) p (0, 1) 0).continuousOn
  have hM0 : 0 ≤ M :=
    le_trans (norm_nonneg _) (hM (0, 0) ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, h.pos.le⟩⟩)
  refine ⟨a₀ / (2 * (M + 1)), by positivity, ?_⟩
  intro s hs ε hε hεε₀ u
  -- reduce `u` to the fundamental domain
  set y : ℝ := u - ⌊u / P⌋ * P with hy
  have hy0 : 0 ≤ y := Int.sub_floor_div_mul_nonneg u h.pos
  have hyP : y < P := Int.sub_floor_div_mul_lt u h.pos
  have hTy : T s y = T s u := (h.periodic s).sub_int_mul_eq _
  have hT'y : deriv (T s) y = deriv (T s) u := (periodic_deriv (h.periodic s)).sub_int_mul_eq _
  have hyK : (s, y) ∈ K₀ := ⟨hs, ⟨hy0, hyP.le⟩⟩
  have h1 : a₀ ≤ lcContactForm (T s u) (deriv (T s) u) := by
    rw [← hTy, ← hT'y, ← hα_eq]
    exact hlow _ hyK
  have h2 : |deriv (T s) u 0| ≤ M := by
    have := hM (s, y) hyK
    rw [Real.norm_eq_abs] at this
    rw [← hT'y, deriv_slice_eq h.smooth]
    exact this
  rw [deriv_pushoff_const, pushoff, contactForm_pushoff]
  have h3 : ε * deriv (T s) u 0 ≤ ε * M := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    exact le_trans (le_abs_self _) h2
  have h4 : ε * M ≤ a₀ / (2 * (M + 1)) * M :=
    mul_le_mul_of_nonneg_right hεε₀ hM0
  have h5 : a₀ / (2 * (M + 1)) * M < a₀ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

theorem TransverseFamily.isPositiveTransverseEmbedding_pushoff {P : ℝ} {T : ℝ → ℝ → E3}
    (h : TransverseFamily P T) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) {ε : ℝ}
    (hpos : ∀ u, 0 < lcContactForm (pushoff (T s) (fun _ => ey) ε u)
      (deriv (pushoff (T s) (fun _ => ey) ε) u)) :
    IsPositiveTransverseEmbedding P (pushoff (T s) (fun _ => ey) ε) where
  circle := h.framedFamily.isSmoothCircle_pushoff s ε
  embedded := fun u u' huu' => h.embedded s hs u u' (by
    simpa [pushoff] using huu')
  positive := hpos

/-- sm-3:2817-2820: the uniform `ε₀` for the transverse family, from the framing radius (`hB`) and
the positivity radius. -/
theorem TransverseFamily.exists_uniform_of
    (hB : ∀ {P : ℝ} {C v : ℝ → ℝ → E3}, FramedFamily P C v →
      ∃ ε₀ > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ u u', pushoff (C s) (v s) ε u ≠ C s u')
    {P : ℝ} {T : ℝ → ℝ → E3} (h : TransverseFamily P T) :
    ∃ ε₀ > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ →
      IsPositiveTransverseEmbedding P (T s) ∧
      IsPositiveTransverseEmbedding P (pushoff (T s) (fun _ => ey) ε) ∧
      DisjointPair P (T s) (pushoff (T s) (fun _ => ey) ε) := by
  obtain ⟨ε₁, hε₁, hd⟩ := hB h.framedFamily
  obtain ⟨ε₂, hε₂, hp⟩ := h.exists_uniform_positive
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun s hs ε hε hεε₀ => ?_⟩
  have hε1 : ε ≤ ε₁ := le_trans hεε₀ (min_le_left _ _)
  have hε2 : ε ≤ ε₂ := le_trans hεε₀ (min_le_right _ _)
  exact ⟨h.isPositiveTransverseEmbedding hs,
    h.isPositiveTransverseEmbedding_pushoff hs (hp s hs ε hε hε2),
    h.framedFamily.disjointPair_pushoff s ε (hd s hs ε hε hε1)⟩


/-! ## 6. Constancy under smooth families (sm-3:2794-2795; proof sm-3:2843-2867)

The paper's argument: put `G(u,v,s) = gaussMap (C₁ s) (C₂ s) u v` and
`A = G·(G_u×G_v)`, `B = G·(G_s×G_v)`, `C = G·(G_u×G_s)`.  Since `|G| = 1`, all first derivatives
of `G` are orthogonal to `G`, so every triple product of `G_u, G_v, G_s` vanishes, and the product
rule plus symmetry of second derivatives gives the divergence identity `∂_s A = ∂_u B + ∂_v C`.
Integrating over the torus, the right side vanishes by periodicity, so `∫∫ A` does not depend
on `s`. -/

namespace LinkingCalculus.Family

section Abstract

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The triple product `⟪G, (∂_a G) × (∂_b G)⟫` of a map `G : X → ℝ³` along the directions
`a, b`, as a function of the point (sm-3:2846: `A = G·(G_u×G_v)`, `B = G·(G_s×G_v)`,
`C = G·(G_u×G_s)`). -/
def triple (G : X → E3) (a b : X) (x : X) : ℝ :=
  ⟪G x, cross (fderiv ℝ G x a) (fderiv ℝ G x b)⟫

theorem contDiff_fderiv_apply {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F : X → Y} (hF : ContDiff ℝ ∞ F) (c : X) : ContDiff ℝ ∞ (fun x => fderiv ℝ F x c) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_triple {G : X → E3} (hG : ContDiff ℝ ∞ G) (a b : X) :
    ContDiff ℝ ∞ (triple G a b) := by
  have hG' : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by simp)
  exact hG.inner ℝ ((hG'.clm_apply contDiff_const).cross (hG'.clm_apply contDiff_const))

/-- Derivative of `y ↦ fderiv ℝ G y a`. -/
theorem hasFDerivAt_fderiv_apply {G : X → E3} (hG : ContDiff ℝ ∞ G) (x a : X) :
    HasFDerivAt (fun y => fderiv ℝ G y a)
      (fderiv ℝ G x ∘SL (0 : X →L[ℝ] X) + (fderiv ℝ (fderiv ℝ G) x).flip a) x := by
  have hG' : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by simp)
  have hG2 : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x :=
    (hG'.differentiable (by simp) x).hasFDerivAt
  exact hG2.clm_apply (hasFDerivAt_const a x)

/-- The product rule for the triple product (sm-3:2853-2854): with `G' = fderiv G x` and
`G'' = fderiv (fderiv G) x`,
`∂_c ⟪G, G'a × G'b⟫ = ⟪G'c, G'a × G'b⟫ + ⟪G, G''ca × G'b⟫ + ⟪G, G'a × G''cb⟫`. -/
theorem fderiv_triple_apply {G : X → E3} (hG : ContDiff ℝ ∞ G) (a b c x : X) :
    fderiv ℝ (triple G a b) x c
      = ⟪fderiv ℝ G x c, cross (fderiv ℝ G x a) (fderiv ℝ G x b)⟫
        + ⟪G x, cross (fderiv ℝ (fderiv ℝ G) x c a) (fderiv ℝ G x b)⟫
        + ⟪G x, cross (fderiv ℝ G x a) (fderiv ℝ (fderiv ℝ G) x c b)⟫ := by
  have hG1 : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by simp) x).hasFDerivAt
  have ha := hasFDerivAt_fderiv_apply hG x a
  have hb := hasFDerivAt_fderiv_apply hG x b
  have h := hG1.inner ℝ (ha.cross hb)
  have h' : HasFDerivAt (triple G a b) _ x := h
  rw [h'.fderiv]
  simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply,
    add_apply, ContinuousLinearMap.flip_apply, crossL_apply,
    zero_apply, map_zero, zero_add, inner_add_right]
  ring

/-- sm-3:2849-2850: `|G| = 1` forces every derivative of `G` to be orthogonal to `G`. -/
theorem inner_fderiv_eq_zero {G : X → E3} (hG : ContDiff ℝ ∞ G) (hn : ∀ y, ‖G y‖ = 1) (x a : X) :
    ⟪G x, fderiv ℝ G x a⟫ = 0 := by
  have hG1 : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by simp) x).hasFDerivAt
  have h1 := hG1.inner ℝ hG1
  have hc : (fun y => ⟪G y, G y⟫) = fun _ => (1 : ℝ) := by
    funext y; rw [real_inner_self_eq_norm_sq, hn y, one_pow]
  have h2 : HasFDerivAt (fun y => ⟪G y, G y⟫) (0 : X →L[ℝ] ℝ) x := by
    rw [hc]; exact hasFDerivAt_const 1 x
  have h3 := congrArg (fun L : X →L[ℝ] ℝ => L a) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply,
    zero_apply] at h3
  have h4 := real_inner_comm (G x) (fderiv ℝ G x a)
  linarith

/-- Symmetry of the second derivative of a smooth map. -/
theorem fderiv_fderiv_symm {G : X → E3} (hG : ContDiff ℝ ∞ G) (x a b : X) :
    fderiv ℝ (fderiv ℝ G) x a b = fderiv ℝ (fderiv ℝ G) x b a :=
  (hG.contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)) a b

/-- The divergence identity (sm-3:2853-2862), in abstract form: for a unit-vector-valued smooth
`G` and any directions `a b c`,  `∂_c ⟪G, G_a × G_b⟫ = ∂_a ⟪G, G_c × G_b⟫ + ∂_b ⟪G, G_a × G_c⟫`.
With `(a, b, c) = (∂_u, ∂_v, ∂_s)` this is `∂_s A = ∂_u B + ∂_v C`. -/
theorem fderiv_triple_div {G : X → E3} (hG : ContDiff ℝ ∞ G) (hn : ∀ y, ‖G y‖ = 1) (a b c x : X) :
    fderiv ℝ (triple G a b) x c
      = fderiv ℝ (triple G c b) x a + fderiv ℝ (triple G a c) x b := by
  have hg : G x ≠ 0 := by
    intro h0; have := hn x; rw [h0, norm_zero] at this; exact zero_ne_one this
  have ho : ∀ d, ⟪G x, fderiv ℝ G x d⟫ = 0 := inner_fderiv_eq_zero hG hn x
  have hsym := fderiv_fderiv_symm hG x
  rw [fderiv_triple_apply hG a b c x, fderiv_triple_apply hG c b a x,
    fderiv_triple_apply hG a c b x,
    inner_cross_eq_zero_of_orth hg (ho c) (ho a) (ho b),
    inner_cross_eq_zero_of_orth hg (ho a) (ho c) (ho b),
    inner_cross_eq_zero_of_orth hg (ho b) (ho a) (ho c),
    hsym a c, hsym b a, hsym b c,
    cross_comm_neg (fderiv ℝ G x c) (fderiv ℝ (fderiv ℝ G) x a b), inner_neg_right]
  ring

/-- A periodic map has a periodic derivative. -/
theorem fderiv_periodic {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : X → Y} {w : X}
    (h : Periodic F w) : Periodic (fderiv ℝ F) w := by
  intro p
  have hF : (fun x => F (x + w)) = F := funext h
  rw [← fderiv_comp_add_right w, hF]

theorem periodic_fderiv_apply {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : X → Y}
    {w : X} (h : Periodic F w) (c : X) : Periodic (fun x => fderiv ℝ F x c) w := by
  intro p
  simp only [fderiv_periodic h p]

theorem periodic_triple {G : X → E3} {w : X} (h : Periodic G w) (a b : X) :
    Periodic (triple G a b) w := by
  intro p
  simp only [triple, h p, fderiv_periodic h p]

end Abstract

/-! ### The parameter space `ℝ × ℝ × ℝ`, points `(u, v, s)` -/

/-- The coordinate direction `∂_u`. -/
def eu : ℝ × ℝ × ℝ := (1, 0, 0)
/-- The coordinate direction `∂_v`. -/
def ev : ℝ × ℝ × ℝ := (0, 1, 0)
/-- The coordinate direction `∂_s`. -/
def es : ℝ × ℝ × ℝ := (0, 0, 1)

section Slices

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem hasDerivAt_slice1 {F : ℝ × ℝ × ℝ → Y} {u v s : ℝ} (h : DifferentiableAt ℝ F (u, v, s)) :
    HasDerivAt (fun t => F (t, v, s)) (fderiv ℝ F (u, v, s) eu) u := by
  have h1 : HasDerivAt (fun t : ℝ => (t, v, s)) eu u :=
    (hasDerivAt_id u).prodMk ((hasDerivAt_const u v).prodMk (hasDerivAt_const u s))
  exact h.hasFDerivAt.comp_hasDerivAt u h1

theorem hasDerivAt_slice2 {F : ℝ × ℝ × ℝ → Y} {u v s : ℝ} (h : DifferentiableAt ℝ F (u, v, s)) :
    HasDerivAt (fun t => F (u, t, s)) (fderiv ℝ F (u, v, s) ev) v := by
  have h1 : HasDerivAt (fun t : ℝ => (u, t, s)) ev v :=
    (hasDerivAt_const v u).prodMk ((hasDerivAt_id v).prodMk (hasDerivAt_const v s))
  exact h.hasFDerivAt.comp_hasDerivAt v h1

theorem hasDerivAt_slice3 {F : ℝ × ℝ × ℝ → Y} {u v s : ℝ} (h : DifferentiableAt ℝ F (u, v, s)) :
    HasDerivAt (fun t => F (u, v, t)) (fderiv ℝ F (u, v, s) es) s := by
  have h1 : HasDerivAt (fun t : ℝ => (u, v, t)) es s :=
    (hasDerivAt_const s u).prodMk ((hasDerivAt_const s v).prodMk (hasDerivAt_id s))
  exact h.hasFDerivAt.comp_hasDerivAt s h1

end Slices

theorem continuous_slice1 {Y : Type*} [TopologicalSpace Y] {H : ℝ × ℝ × ℝ → Y} (hH : Continuous H) (v s : ℝ) :
    Continuous fun t => H (t, v, s) :=
  hH.comp (continuous_id.prodMk (continuous_const.prodMk continuous_const))

theorem continuous_slice2 {Y : Type*} [TopologicalSpace Y] {H : ℝ × ℝ × ℝ → Y} (hH : Continuous H) (u s : ℝ) :
    Continuous fun t => H (u, t, s) :=
  hH.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))

theorem continuous_slice3 {Y : Type*} [TopologicalSpace Y] {H : ℝ × ℝ × ℝ → Y} (hH : Continuous H) (u v : ℝ) :
    Continuous fun t => H (u, v, t) :=
  hH.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))

/-- Joint continuity of `(u, v) ↦ ∫_s^{s'} H(u, v, t) dt`. -/
theorem continuous_intS {H : ℝ × ℝ × ℝ → ℝ} (hH : Continuous H) (s s' : ℝ) :
    Continuous fun p : ℝ × ℝ => ∫ t in s..s', H (p.1, p.2, t) := by
  have hc : Continuous fun q : (ℝ × ℝ) × ℝ => H (q.1.1, q.1.2, q.2) := hH.comp (by fun_prop)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : ℝ × ℝ) (t : ℝ) => H (p.1, p.2, t)) hc s s'

theorem continuous_intS_slice2 {H : ℝ × ℝ × ℝ → ℝ} (hH : Continuous H) (u s s' : ℝ) :
    Continuous fun v => ∫ t in s..s', H (u, v, t) := by
  have hc : Continuous fun q : ℝ × ℝ => H (u, q.1, q.2) := hH.comp (by fun_prop)
  exact continuous_parametric_integral (f := fun v t => H (u, v, t)) hc s s'

theorem continuous_intVS {H : ℝ × ℝ × ℝ → ℝ} (hH : Continuous H) (P s s' : ℝ) :
    Continuous fun u => ∫ v in (0:ℝ)..P, ∫ t in s..s', H (u, v, t) :=
  continuous_parametric_integral (f := fun u v => ∫ t in s..s', H (u, v, t))
    (continuous_intS hH s s') 0 P

/-! ### Fundamental theorem of calculus along the three coordinate lines -/

theorem ftc_slice1 {F : ℝ × ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (a b v s : ℝ) :
    ∫ t in a..b, fderiv ℝ F (t, v, s) eu = F (b, v, s) - F (a, v, s) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _; exact hasDerivAt_slice1 (hF.differentiable (by simp) _)
  · exact (continuous_slice1 (contDiff_fderiv_apply hF eu).continuous v s).intervalIntegrable _ _

theorem ftc_slice2 {F : ℝ × ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (u a b s : ℝ) :
    ∫ t in a..b, fderiv ℝ F (u, t, s) ev = F (u, b, s) - F (u, a, s) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _; exact hasDerivAt_slice2 (hF.differentiable (by simp) _)
  · exact (continuous_slice2 (contDiff_fderiv_apply hF ev).continuous u s).intervalIntegrable _ _

theorem ftc_slice3 {F : ℝ × ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (u v a b : ℝ) :
    ∫ t in a..b, fderiv ℝ F (u, v, t) es = F (u, v, b) - F (u, v, a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _; exact hasDerivAt_slice3 (hF.differentiable (by simp) _)
  · exact (continuous_slice3 (contDiff_fderiv_apply hF es).continuous u v).intervalIntegrable _ _

/-! ### The two boundary terms vanish by periodicity (sm-3:2863-2865) -/

/-- `∫∫∫ ∂_u B = 0` for `B` periodic in `u`. -/
theorem integral_fderiv1_eq_zero {F : ℝ × ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {P : ℝ} (hP : 0 ≤ P)
    (hper : Periodic F (P, 0, 0)) {s s' : ℝ} (hss' : s ≤ s') :
    ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, ∫ t in s..s', fderiv ℝ F (u, v, t) eu = 0 := by
  have hc : Continuous fun x => fderiv ℝ F x eu := (contDiff_fderiv_apply hF eu).continuous
  have h3 : ∀ v t, ∫ u in (0:ℝ)..P, fderiv ℝ F (u, v, t) eu = 0 := by
    intro v t
    rw [ftc_slice1 hF 0 P v t]
    have := hper (0, v, t)
    simp only [Prod.mk_add_mk, zero_add, add_zero] at this
    rw [this, sub_self]
  calc ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, ∫ t in s..s', fderiv ℝ F (u, v, t) eu
      = ∫ v in (0:ℝ)..P, ∫ u in (0:ℝ)..P, ∫ t in s..s', fderiv ℝ F (u, v, t) eu :=
        integral_integral_swap_of_continuous
          (f := fun u v => ∫ t in s..s', fderiv ℝ F (u, v, t) eu) (continuous_intS hc s s') hP hP
    _ = ∫ v in (0:ℝ)..P, ∫ t in s..s', ∫ u in (0:ℝ)..P, fderiv ℝ F (u, v, t) eu := by
        refine intervalIntegral.integral_congr fun v _ => ?_
        have hc' : Continuous fun q : ℝ × ℝ => fderiv ℝ F (q.1, v, q.2) eu := hc.comp (by fun_prop)
        exact integral_integral_swap_of_continuous (f := fun u t => fderiv ℝ F (u, v, t) eu)
          hc' hP hss'
    _ = ∫ v in (0:ℝ)..P, ∫ t in s..s', (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun v _ => ?_
        refine intervalIntegral.integral_congr fun t _ => ?_
        exact h3 v t
    _ = 0 := by simp

/-- `∫∫∫ ∂_v C = 0` for `C` periodic in `v`. -/
theorem integral_fderiv2_eq_zero {F : ℝ × ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {P : ℝ} (hP : 0 ≤ P)
    (hper : Periodic F (0, P, 0)) {s s' : ℝ} (hss' : s ≤ s') :
    ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, ∫ t in s..s', fderiv ℝ F (u, v, t) ev = 0 := by
  have hc : Continuous fun x => fderiv ℝ F x ev := (contDiff_fderiv_apply hF ev).continuous
  have h3 : ∀ u t, ∫ v in (0:ℝ)..P, fderiv ℝ F (u, v, t) ev = 0 := by
    intro u t
    rw [ftc_slice2 hF u 0 P t]
    have := hper (u, 0, t)
    simp only [Prod.mk_add_mk, zero_add, add_zero] at this
    rw [this, sub_self]
  calc ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, ∫ t in s..s', fderiv ℝ F (u, v, t) ev
      = ∫ u in (0:ℝ)..P, ∫ t in s..s', ∫ v in (0:ℝ)..P, fderiv ℝ F (u, v, t) ev := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        have hc' : Continuous fun q : ℝ × ℝ => fderiv ℝ F (u, q.1, q.2) ev := hc.comp (by fun_prop)
        exact integral_integral_swap_of_continuous (f := fun v t => fderiv ℝ F (u, v, t) ev)
          hc' hP hss'
    _ = ∫ u in (0:ℝ)..P, ∫ t in s..s', (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        refine intervalIntegral.integral_congr fun t _ => ?_
        exact h3 u t
    _ = 0 := by simp

/-! ### The main computation (sm-3:2853-2867) -/

/-- For a smooth unit-vector-valued `G` on `ℝ × ℝ × ℝ`, `P`-periodic in `u` and in `v`, the
torus integral of `A = ⟪G, G_u × G_v⟫` does not depend on `s`. -/
theorem integral_triple_eq {G : ℝ × ℝ × ℝ → E3} (hG : ContDiff ℝ ∞ G) (hn : ∀ y, ‖G y‖ = 1)
    {P : ℝ} (hP : 0 ≤ P) (hpu : Periodic G (P, 0, 0)) (hpv : Periodic G (0, P, 0))
    {s s' : ℝ} (hss' : s ≤ s') :
    ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, triple G eu ev (u, v, s')
      = ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, triple G eu ev (u, v, s) := by
  have hA : ContDiff ℝ ∞ (triple G eu ev) := contDiff_triple hG eu ev
  have hB : ContDiff ℝ ∞ (triple G es ev) := contDiff_triple hG es ev
  have hC : ContDiff ℝ ∞ (triple G eu es) := contDiff_triple hG eu es
  have hAc : Continuous (triple G eu ev) := hA.continuous
  have hA2 : ∀ σ, Continuous fun p : ℝ × ℝ => triple G eu ev (p.1, p.2, σ) :=
    fun σ => hAc.comp (by fun_prop)
  have hBu : Continuous fun x => fderiv ℝ (triple G es ev) x eu :=
    (contDiff_fderiv_apply hB eu).continuous
  have hCv : Continuous fun x => fderiv ℝ (triple G eu es) x ev :=
    (contDiff_fderiv_apply hC ev).continuous
  have hdiv : ∀ x, fderiv ℝ (triple G eu ev) x es
      = fderiv ℝ (triple G es ev) x eu + fderiv ℝ (triple G eu es) x ev :=
    fun x => fderiv_triple_div hG hn eu ev es x
  have hBz := integral_fderiv1_eq_zero hB hP (periodic_triple hpu es ev) hss'
  have hCz := integral_fderiv2_eq_zero hC hP (periodic_triple hpv eu es) hss'
  rw [← sub_eq_zero]
  calc (∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, triple G eu ev (u, v, s'))
        - ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, triple G eu ev (u, v, s)
      = ∫ u in (0:ℝ)..P, ((∫ v in (0:ℝ)..P, triple G eu ev (u, v, s'))
          - ∫ v in (0:ℝ)..P, triple G eu ev (u, v, s)) :=
        (intervalIntegral.integral_sub
          ((continuous_parametric_integral (f := fun u v => triple G eu ev (u, v, s'))
            (hA2 s') 0 P).intervalIntegrable 0 P)
          ((continuous_parametric_integral (f := fun u v => triple G eu ev (u, v, s))
            (hA2 s) 0 P).intervalIntegrable 0 P)).symm
    _ = ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P,
          (triple G eu ev (u, v, s') - triple G eu ev (u, v, s)) := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        exact (intervalIntegral.integral_sub ((continuous_slice2 hAc u s').intervalIntegrable 0 P)
          ((continuous_slice2 hAc u s).intervalIntegrable 0 P)).symm
    _ = ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, ∫ t in s..s', fderiv ℝ (triple G eu ev) (u, v, t) es := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        refine intervalIntegral.integral_congr fun v _ => ?_
        exact (ftc_slice3 hA u v s s').symm
    _ = ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, ∫ t in s..s',
          (fderiv ℝ (triple G es ev) (u, v, t) eu + fderiv ℝ (triple G eu es) (u, v, t) ev) := by
        simp only [hdiv]
    _ = ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P,
          ((∫ t in s..s', fderiv ℝ (triple G es ev) (u, v, t) eu)
            + ∫ t in s..s', fderiv ℝ (triple G eu es) (u, v, t) ev) := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        refine intervalIntegral.integral_congr fun v _ => ?_
        exact intervalIntegral.integral_add ((continuous_slice3 hBu u v).intervalIntegrable s s')
          ((continuous_slice3 hCv u v).intervalIntegrable s s')
    _ = ∫ u in (0:ℝ)..P,
          ((∫ v in (0:ℝ)..P, ∫ t in s..s', fderiv ℝ (triple G es ev) (u, v, t) eu)
            + ∫ v in (0:ℝ)..P, ∫ t in s..s', fderiv ℝ (triple G eu es) (u, v, t) ev) := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        exact intervalIntegral.integral_add
          ((continuous_intS_slice2 hBu u s s').intervalIntegrable 0 P)
          ((continuous_intS_slice2 hCv u s s').intervalIntegrable 0 P)
    _ = (∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, ∫ t in s..s', fderiv ℝ (triple G es ev) (u, v, t) eu)
          + ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, ∫ t in s..s', fderiv ℝ (triple G eu es) (u, v, t) ev :=
        intervalIntegral.integral_add ((continuous_intVS hBu P s s').intervalIntegrable 0 P)
          ((continuous_intVS hCv P s s').intervalIntegrable 0 P)
    _ = 0 := by rw [hBz, hCz, add_zero]

/-! ### The Gauss map of the family -/

/-- The Gauss map of the family as one map on `ℝ × ℝ × ℝ`:
`G (u, v, s) = gaussMap (C₁ s) (C₂ s) u v` (sm-3:2843). -/
def gaussFam (C₁ C₂ : ℝ → ℝ → E3) (p : ℝ × ℝ × ℝ) : E3 :=
  gaussMap (C₁ p.2.2) (C₂ p.2.2) p.1 p.2.1

theorem contDiff_gaussFam {C₁ C₂ : ℝ → ℝ → E3} (h₁ : ContDiff ℝ ∞ (uncurry C₁))
    (h₂ : ContDiff ℝ ∞ (uncurry C₂)) (hd : ∀ s u v, C₂ s v ≠ C₁ s u) :
    ContDiff ℝ ∞ (gaussFam C₁ C₂) := by
  have hD : ContDiff ℝ ∞ (fun p : ℝ × ℝ × ℝ => C₂ p.2.2 p.2.1 - C₁ p.2.2 p.1) := by
    have e2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ × ℝ => uncurry C₂ (p.2.2, p.2.1)) :=
      h₂.comp ((contDiff_snd.comp contDiff_snd).prodMk (contDiff_fst.comp contDiff_snd))
    have e1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ × ℝ => uncurry C₁ (p.2.2, p.1)) :=
      h₁.comp ((contDiff_snd.comp contDiff_snd).prodMk contDiff_fst)
    exact e2.sub e1
  have hne : ∀ p : ℝ × ℝ × ℝ, C₂ p.2.2 p.2.1 - C₁ p.2.2 p.1 ≠ 0 :=
    fun p => sub_ne_zero.2 (hd _ _ _)
  exact ((hD.norm ℝ hne).inv (fun p => norm_ne_zero_iff.2 (hne p))).smul hD

theorem norm_gaussFam {C₁ C₂ : ℝ → ℝ → E3} (hd : ∀ s u v, C₂ s v ≠ C₁ s u) (p : ℝ × ℝ × ℝ) :
    ‖gaussFam C₁ C₂ p‖ = 1 :=
  norm_gaussMap (hd _ _ _)

theorem gaussFam_periodic_u {C₁ C₂ : ℝ → ℝ → E3} {P : ℝ} (hp₁ : ∀ s, Periodic (C₁ s) P) :
    Periodic (gaussFam C₁ C₂) (P, 0, 0) := by
  rintro ⟨u, v, s⟩
  simp only [Prod.mk_add_mk, add_zero]
  show gaussMap (C₁ s) (C₂ s) (u + P) v = gaussMap (C₁ s) (C₂ s) u v
  unfold gaussMap
  rw [hp₁ s u]

theorem gaussFam_periodic_v {C₁ C₂ : ℝ → ℝ → E3} {P : ℝ} (hp₂ : ∀ s, Periodic (C₂ s) P) :
    Periodic (gaussFam C₁ C₂) (0, P, 0) := by
  rintro ⟨u, v, s⟩
  simp only [Prod.mk_add_mk, add_zero]
  show gaussMap (C₁ s) (C₂ s) u (v + P) = gaussMap (C₁ s) (C₂ s) u v
  unfold gaussMap
  rw [hp₂ s v]

/-- The integrand of the linking pairing at `s` is the slice of `A = ⟪G, G_u × G_v⟫`. -/
theorem gaussDensity_eq_triple {C₁ C₂ : ℝ → ℝ → E3} (hG : ContDiff ℝ ∞ (gaussFam C₁ C₂))
    (u v s : ℝ) :
    gaussDensity (gaussMap (C₁ s) (C₂ s)) u v = triple (gaussFam C₁ C₂) eu ev (u, v, s) := by
  have hd : DifferentiableAt ℝ (gaussFam C₁ C₂) (u, v, s) := hG.differentiable (by simp) _
  have hu : HasDerivAt (fun u' => gaussMap (C₁ s) (C₂ s) u' v)
      (fderiv ℝ (gaussFam C₁ C₂) (u, v, s) eu) u :=
    hasDerivAt_slice1 (F := gaussFam C₁ C₂) hd
  have hv : HasDerivAt (fun v' => gaussMap (C₁ s) (C₂ s) u v')
      (fderiv ℝ (gaussFam C₁ C₂) (u, v, s) ev) v :=
    hasDerivAt_slice2 (F := gaussFam C₁ C₂) hd
  show ⟪gaussMap (C₁ s) (C₂ s) u v, cross (deriv (fun u' => gaussMap (C₁ s) (C₂ s) u' v) u)
      (deriv (fun v' => gaussMap (C₁ s) (C₂ s) u v') v)⟫ = _
  rw [hu.deriv, hv.deriv]
  rfl

end LinkingCalculus.Family

open LinkingCalculus.Family in
/-- sm-3:2794-2795, global form: the linking pairing is constant along a smooth family of
disjoint pairs parametrized by all of `ℝ`. -/
theorem linking_const_of_family_global {P : ℝ} (hP : 0 < P) {C₁ C₂ : ℝ → ℝ → E3}
    (h₁ : ContDiff ℝ ∞ (uncurry C₁)) (h₂ : ContDiff ℝ ∞ (uncurry C₂))
    (hp₁ : ∀ s, Periodic (C₁ s) P) (hp₂ : ∀ s, Periodic (C₂ s) P)
    (hd : ∀ s u v, C₂ s v ≠ C₁ s u) (s s' : ℝ) :
    linking P (C₁ s) (C₂ s) = linking P (C₁ s') (C₂ s') := by
  have hG : ContDiff ℝ ∞ (gaussFam C₁ C₂) := contDiff_gaussFam h₁ h₂ hd
  have hn : ∀ p, ‖gaussFam C₁ C₂ p‖ = 1 := norm_gaussFam hd
  have hpu : Periodic (gaussFam C₁ C₂) (P, 0, 0) := gaussFam_periodic_u hp₁
  have hpv : Periodic (gaussFam C₁ C₂) (0, P, 0) := gaussFam_periodic_v hp₂
  have e : ∀ σ, (∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, gaussDensity (gaussMap (C₁ σ) (C₂ σ)) u v)
      = ∫ u in (0:ℝ)..P, ∫ v in (0:ℝ)..P, triple (gaussFam C₁ C₂) eu ev (u, v, σ) := by
    intro σ; simp only [gaussDensity_eq_triple hG]
  unfold linking gaussIntegral
  rw [e s, e s']
  rcases le_total s s' with h | h
  · rw [integral_triple_eq hG hn hP.le hpu hpv h]
  · rw [integral_triple_eq hG hn hP.le hpu hpv h]

open LinkingCalculus.Family in
/-- sm-3:2794-2795 "constant under smooth families of disjoint oriented pairs": the `[0,1]`
version, obtained from the global one by reparametrizing with `Real.smoothTransition`. -/
theorem DisjointPairFamily.linking_eq {P : ℝ} {C₁ C₂ : ℝ → ℝ → E3}
    (h : DisjointPairFamily P C₁ C₂) {s s' : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (hs' : s' ∈ Icc (0:ℝ) 1) :
    linking P (C₁ s) (C₂ s) = linking P (C₁ s') (C₂ s') := by
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ → ℝ, σ = fun t => s + (s' - s) * Real.smoothTransition t := ⟨_, rfl⟩
  have hσ0 : σ 0 = s := by
    rw [hσ]; simp only [Real.smoothTransition.zero_of_nonpos le_rfl, mul_zero, add_zero]
  have hσ1 : σ 1 = s' := by
    rw [hσ]; simp only [Real.smoothTransition.one_of_one_le le_rfl, mul_one]; ring
  have hσmem : ∀ t, σ t ∈ Icc (0:ℝ) 1 := by
    intro t
    rw [hσ]
    obtain ⟨hs0, hs1⟩ := hs
    obtain ⟨hs'0, hs'1⟩ := hs'
    have h0 := Real.smoothTransition.nonneg t
    have h1 := Real.smoothTransition.le_one t
    constructor
    · nlinarith
    · nlinarith
  have hσs : ContDiff ℝ ∞ σ := by
    rw [hσ]
    exact contDiff_const.add (contDiff_const.mul Real.smoothTransition.contDiff)
  have h₁' : ContDiff ℝ ∞ (uncurry fun t u => C₁ (σ t) u) := by
    have e : (uncurry fun t u => C₁ (σ t) u) = uncurry C₁ ∘ (fun p : ℝ × ℝ => (σ p.1, p.2)) := by
      funext p; rfl
    rw [e]; exact h.smooth₁.comp ((hσs.comp contDiff_fst).prodMk contDiff_snd)
  have h₂' : ContDiff ℝ ∞ (uncurry fun t u => C₂ (σ t) u) := by
    have e : (uncurry fun t u => C₂ (σ t) u) = uncurry C₂ ∘ (fun p : ℝ × ℝ => (σ p.1, p.2)) := by
      funext p; rfl
    rw [e]; exact h.smooth₂.comp ((hσs.comp contDiff_fst).prodMk contDiff_snd)
  have key := linking_const_of_family_global h.pos h₁' h₂' (fun t => h.periodic₁ (σ t))
    (fun t => h.periodic₂ (σ t)) (fun t u v => h.disjoint (σ t) (hσmem t) u v) 0 1
  change linking P (C₁ (σ 0)) (C₂ (σ 0)) = linking P (C₁ (σ 1)) (C₂ (σ 1)) at key
  rwa [hσ0, hσ1] at key


/-! ## 7. Uniform framed pushoff (sm-3:2810-2812; replaces the normal-chart argument of
sm-3:2942-2985 by a direct Taylor estimate) -/

namespace LinkingCalculus.Framing

/-! ### (a) Slice derivatives of a jointly smooth map `ℝ × ℝ → ℝ³` -/

/-- The `u`-slice derivative of a jointly `C^∞` map is the partial `fderiv` in the direction `(0,1)`. -/
theorem deriv_sliceV_eq {F : ℝ × ℝ → E3} (hF : ContDiff ℝ ∞ F) (s u : ℝ) :
    deriv (fun u' => F (s, u')) u = fderiv ℝ F (s, u) (0, 1) :=
  (hasDerivAt_sliceV (F := F) ((hF.differentiable (by simp)) (s, u))).deriv

theorem differentiable_sliceV {F : ℝ × ℝ → E3} (hF : ContDiff ℝ ∞ F) (s : ℝ) :
    Differentiable ℝ (fun u' => F (s, u')) := fun u =>
  (hasDerivAt_sliceV (F := F) ((hF.differentiable (by simp)) (s, u))).differentiableAt

/-- The slice derivative, as a function of `(s,u)`, is again jointly `C^∞`. -/
theorem contDiff_deriv_sliceV {F : ℝ × ℝ → E3} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun u' => F (p.1, u')) p.2) := by
  have heq : (fun p : ℝ × ℝ => deriv (fun u' => F (p.1, u')) p.2) =
      fun p => fderiv ℝ F p (0, 1) := by
    funext p; exact deriv_sliceV_eq hF p.1 p.2
  rw [heq]
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem continuous_deriv_sliceV {F : ℝ × ℝ → E3} (hF : ContDiff ℝ ∞ F) :
    Continuous (fun p : ℝ × ℝ => deriv (fun u' => F (p.1, u')) p.2) :=
  (contDiff_deriv_sliceV hF).continuous

/-- The derivative of a periodic function is periodic. -/
theorem periodic_deriv {f : ℝ → E3} {P : ℝ} (hf : Periodic f P) : Periodic (deriv f) P := by
  intro u
  calc deriv f (u + P) = deriv (fun t => f (t + P)) u := (deriv_comp_add_const f P u).symm
    _ = deriv f u := by
      congr 1
      funext t
      exact hf t

/-- Reduction of a real number to the fundamental domain `[0, P)` by an integer multiple of `P`. -/
theorem exists_int_sub_mem_Ico {P : ℝ} (hP : 0 < P) (u : ℝ) : ∃ k : ℤ, u - k * P ∈ Ico 0 P :=
  ⟨⌊u / P⌋, Int.sub_floor_div_mul_nonneg u hP, Int.sub_floor_div_mul_lt u hP⟩

/-! ### (b) Taylor remainder from a second-derivative bound -/

/-- Second-order Taylor estimate: if `‖f''‖ ≤ K` everywhere then
`‖f u' − f u − (u' − u) f'(u)‖ ≤ K |u' − u|²`. -/
theorem taylor_bound {f : ℝ → E3} (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    {K : ℝ} (hK : ∀ t, ‖deriv (deriv f) t‖ ≤ K) (u u' : ℝ) :
    ‖f u' - f u - (u' - u) • deriv f u‖ ≤ K * |u' - u| ^ 2 := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK u)
  have hlip : ∀ t, ‖deriv f t - deriv f u‖ ≤ K * ‖t - u‖ := fun t =>
    Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hf' x) (fun x _ => hK x) convex_univ
      (mem_univ u) (mem_univ t)
  let g : ℝ → E3 := fun t => f t - t • deriv f u
  have hgd : ∀ t, HasDerivAt g (deriv f t - deriv f u) t := fun t => by
    have h1 : HasDerivAt f (deriv f t) t := (hf t).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => y • deriv f u) ((1:ℝ) • deriv f u) t :=
      (hasDerivAt_id t).smul_const (deriv f u)
    rw [one_smul] at h2
    exact h1.sub h2
  have hball : ∀ t ∈ Metric.closedBall u |u' - u|, ‖deriv g t‖ ≤ K * |u' - u| := by
    intro t ht
    rw [Metric.mem_closedBall, Real.dist_eq] at ht
    rw [(hgd t).deriv]
    calc ‖deriv f t - deriv f u‖ ≤ K * ‖t - u‖ := hlip t
      _ = K * |t - u| := by rw [Real.norm_eq_abs]
      _ ≤ K * |u' - u| := mul_le_mul_of_nonneg_left ht hK0
  have hu : u ∈ Metric.closedBall u |u' - u| := Metric.mem_closedBall_self (abs_nonneg _)
  have hu' : u' ∈ Metric.closedBall u |u' - u| := by
    rw [Metric.mem_closedBall, Real.dist_eq]
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => (hgd x).differentiableAt)
    hball (convex_closedBall u _) hu hu'
  have heq : g u' - g u = f u' - f u - (u' - u) • deriv f u := by
    simp only [g, sub_smul]; abel
  rw [heq] at hmain
  calc ‖f u' - f u - (u' - u) • deriv f u‖ ≤ K * |u' - u| * ‖u' - u‖ := hmain
    _ = K * |u' - u| ^ 2 := by rw [Real.norm_eq_abs]; ring

/-! ### (c) The local step, in algebraic form -/

/-- If `ε w = δ T + R` with `‖R‖ ≤ K δ²`, `‖w‖ ≤ V`, `‖T × w‖ ≥ c > 0`, `|δ| ≤ η` and
`η K V < c`, then we have a contradiction: crossing with `w` kills the `εw` term and leaves
`|δ| ‖T × w‖ ≤ V K δ²`. -/
theorem local_contra {T w R : E3} {ε δ c V K η : ℝ} (hε : 0 < ε) (hc0 : 0 < c)
    (hc : c ≤ ‖cross T w‖) (hw : ‖w‖ ≤ V) (hR : ‖R‖ ≤ K * |δ| ^ 2) (hδ : |δ| ≤ η)
    (hη : η * K * V < c) (hK : 0 ≤ K) (hV : 0 ≤ V) (heq : ε • w = δ • T + R) : False := by
  have h1 : cross w (ε • w) = 0 := by rw [cross_smul_right, cross_self, smul_zero]
  have h2 : cross w (δ • T + R) = δ • cross w T + cross w R := by
    rw [cross_add_right, cross_smul_right]
  have h3 : δ • cross w T = -cross w R := by
    rw [← heq, h1] at h2
    exact eq_neg_of_add_eq_zero_left h2.symm
  have h4 : |δ| * ‖cross w T‖ = ‖cross w R‖ := by
    rw [← norm_neg (cross w R), ← h3, norm_smul, Real.norm_eq_abs]
  have h5 : ‖cross w T‖ = ‖cross T w‖ := by rw [cross_comm_neg w T, norm_neg]
  have h6 : ‖cross w R‖ ≤ ‖w‖ * ‖R‖ := norm_cross_le w R
  have h7 : |δ| * ‖cross T w‖ ≤ V * (K * |δ| ^ 2) := by
    rw [← h5, h4]
    exact h6.trans (mul_le_mul hw hR (norm_nonneg _) hV)
  by_cases hδ0 : δ = 0
  · subst hδ0
    rw [abs_zero, zero_pow two_ne_zero, mul_zero] at hR
    have hR0 : R = 0 := norm_le_zero_iff.1 hR
    rw [hR0, zero_smul, zero_add] at heq
    have hw0 : w = 0 := (smul_eq_zero.1 heq).resolve_left hε.ne'
    rw [hw0, cross_zero_right, norm_zero] at hc
    linarith
  · have hδpos : 0 < |δ| := abs_pos.2 hδ0
    have h8 : c * |δ| ≤ V * (K * |δ| ^ 2) := by
      calc c * |δ| ≤ ‖cross T w‖ * |δ| := mul_le_mul_of_nonneg_right hc hδpos.le
        _ = |δ| * ‖cross T w‖ := mul_comm _ _
        _ ≤ V * (K * |δ| ^ 2) := h7
    have h9 : V * (K * |δ| ^ 2) ≤ V * K * η * |δ| := by
      have hVK : 0 ≤ V * K := mul_nonneg hV hK
      have : |δ| ^ 2 ≤ η * |δ| := by nlinarith
      nlinarith
    nlinarith [mul_pos (sub_pos.2 hη) hδpos]

/-! ### (b) Uniform constants over `s ∈ [0,1]`, `u ∈ ℝ` by compactness and periodicity -/

section Constants

variable {P : ℝ} {C v : ℝ → ℝ → E3}

/-- The tangent `∂ᵤC`, written as the slice derivative of `uncurry C`. -/
theorem tangent_eq (C : ℝ → ℝ → E3) (s : ℝ) :
    deriv (C s) = fun u => (fun p : ℝ × ℝ => deriv (fun u' => uncurry C (p.1, u')) p.2) (s, u) := by
  funext u; rfl

theorem differentiable_slice (h : FramedFamily P C v) (s : ℝ) : Differentiable ℝ (C s) :=
  differentiable_sliceV h.smooth s

theorem differentiable_deriv_slice (h : FramedFamily P C v) (s : ℝ) :
    Differentiable ℝ (deriv (C s)) := by
  rw [tangent_eq C s]
  exact differentiable_sliceV (contDiff_deriv_sliceV h.smooth) s

theorem continuous_tangent (h : FramedFamily P C v) :
    Continuous (fun p : ℝ × ℝ => deriv (C p.1) p.2) :=
  continuous_deriv_sliceV h.smooth

theorem continuous_deriv2 (h : FramedFamily P C v) :
    Continuous (fun p : ℝ × ℝ => deriv (deriv (C p.1)) p.2) := by
  have heq : (fun p : ℝ × ℝ => deriv (deriv (C p.1)) p.2) = fun p : ℝ × ℝ =>
      deriv (fun u' => (fun q : ℝ × ℝ => deriv (fun u'' => uncurry C (q.1, u'')) q.2) (p.1, u'))
        p.2 := by
    funext p
    rw [tangent_eq C p.1]
  rw [heq]
  exact continuous_deriv_sliceV (contDiff_deriv_sliceV h.smooth)

/-- A uniform positive lower bound on `‖∂ᵤC × v‖`. -/
theorem exists_cross_lower_bound (h : FramedFamily P C v) :
    ∃ c > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ u, c ≤ ‖cross (deriv (C s) u) (v s u)‖ := by
  have hP := h.pos
  have hK₀ : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) P) := isCompact_Icc.prod isCompact_Icc
  have hne : (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) P).Nonempty :=
    ⟨(0, 0), ⟨le_refl _, zero_le_one⟩, ⟨le_refl _, hP.le⟩⟩
  have hv : Continuous (fun p : ℝ × ℝ => v p.1 p.2) := h.smooth_v.continuous
  have hg : Continuous (fun p : ℝ × ℝ => ‖cross (deriv (C p.1) p.2) (v p.1 p.2)‖) :=
    ((contDiff_cross (n := 0)).continuous.comp ((continuous_tangent h).prodMk hv)).norm
  obtain ⟨p₀, hp₀, hmin⟩ := hK₀.exists_isMinOn hne hg.continuousOn
  refine ⟨‖cross (deriv (C p₀.1) p₀.2) (v p₀.1 p₀.2)‖, ?_, ?_⟩
  · exact norm_pos_iff.2 (cross_ne_zero_of_linearIndependent (h.indep p₀.1 hp₀.1 p₀.2))
  · intro s hs u
    obtain ⟨k, hk⟩ := exists_int_sub_mem_Ico hP u
    have h1 : deriv (C s) (u - k * P) = deriv (C s) u :=
      (periodic_deriv (h.periodic s)).sub_int_mul_eq k
    have h2 : v s (u - k * P) = v s u := (h.periodic_v s).sub_int_mul_eq k
    have hmem : (s, u - k * P) ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) P := ⟨hs, Ico_subset_Icc_self hk⟩
    have := isMinOn_iff.1 hmin _ hmem
    change ‖cross (deriv (C p₀.1) p₀.2) (v p₀.1 p₀.2)‖ ≤
      ‖cross (deriv (C s) (u - k * P)) (v s (u - k * P))‖ at this
    rwa [h1, h2] at this

/-- A uniform bound on `‖v‖`. -/
theorem exists_v_bound (h : FramedFamily P C v) :
    ∃ V > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ u, ‖v s u‖ ≤ V := by
  have hP := h.pos
  have hK₀ : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) P) := isCompact_Icc.prod isCompact_Icc
  have hv : Continuous (fun p : ℝ × ℝ => v p.1 p.2) := h.smooth_v.continuous
  obtain ⟨B, hB⟩ := hK₀.exists_bound_of_continuousOn hv.continuousOn
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro s hs u
  obtain ⟨k, hk⟩ := exists_int_sub_mem_Ico hP u
  have h2 : v s (u - k * P) = v s u := (h.periodic_v s).sub_int_mul_eq k
  have := hB (s, u - k * P) ⟨hs, Ico_subset_Icc_self hk⟩
  change ‖v s (u - k * P)‖ ≤ B at this
  rw [h2] at this
  linarith [le_abs_self B]

/-- A uniform bound on the second `u`-derivative `‖∂ᵤ²C‖`. -/
theorem exists_deriv2_bound (h : FramedFamily P C v) :
    ∃ K > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ u, ‖deriv (deriv (C s)) u‖ ≤ K := by
  have hP := h.pos
  have hK₀ : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) P) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hK₀.exists_bound_of_continuousOn (continuous_deriv2 h).continuousOn
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro s hs u
  obtain ⟨k, hk⟩ := exists_int_sub_mem_Ico hP u
  have h2 : deriv (deriv (C s)) (u - k * P) = deriv (deriv (C s)) u :=
    (periodic_deriv (periodic_deriv (h.periodic s))).sub_int_mul_eq k
  have := hB (s, u - k * P) ⟨hs, Ico_subset_Icc_self hk⟩
  change ‖deriv (deriv (C s)) (u - k * P)‖ ≤ B at this
  rw [h2] at this
  linarith [le_abs_self B]

/-! ### (d) The global step: points at parameter distance in `[η, P − η]` stay apart -/

/-- No integer multiple of `P` lies strictly between `0` and `P`. -/
theorem not_int_mul_of_mem_Ioo {P d : ℝ} (hP : 0 < P) (hd : d ∈ Ioo 0 P) (k : ℤ)
    (hk : d = k * P) : False := by
  rcases le_or_gt k 0 with hk0 | hk0
  · have : (k:ℝ) ≤ 0 := by exact_mod_cast hk0
    nlinarith [hd.1]
  · have : (1:ℝ) ≤ k := by exact_mod_cast hk0
    nlinarith [hd.2]

/-- The minimum of `‖C s (u + d) − C s u‖` over `s ∈ [0,1]`, `u ∈ ℝ`, `d ∈ [η, P − η]` is positive. -/
theorem exists_global_min (h : FramedFamily P C v) {η : ℝ} (hη0 : 0 < η) (hηP : η ≤ P / 4) :
    ∃ m > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ u, ∀ d ∈ Icc η (P - η), m ≤ ‖C s (u + d) - C s u‖ := by
  have hP := h.pos
  have hK₁ : IsCompact (Icc (0:ℝ) 1 ×ˢ (Icc (0:ℝ) P ×ˢ Icc η (P - η))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hne : (Icc (0:ℝ) 1 ×ˢ (Icc (0:ℝ) P ×ˢ Icc η (P - η))).Nonempty :=
    ⟨(0, 0, η), ⟨le_refl _, zero_le_one⟩, ⟨le_refl _, hP.le⟩, ⟨le_refl _, by linarith⟩⟩
  have hC : Continuous (uncurry C) := h.smooth.continuous
  have hf : Continuous (fun p : ℝ × ℝ × ℝ =>
      ‖uncurry C (p.1, p.2.1 + p.2.2) - uncurry C (p.1, p.2.1)‖) :=
    ((hC.comp (continuous_fst.prodMk (continuous_snd.fst.add continuous_snd.snd))).sub
      (hC.comp (continuous_fst.prodMk continuous_snd.fst))).norm
  obtain ⟨p₀, hp₀, hmin⟩ := hK₁.exists_isMinOn hne hf.continuousOn
  obtain ⟨hs₀, hu₀, hd₀⟩ := hp₀
  refine ⟨‖C p₀.1 (p₀.2.1 + p₀.2.2) - C p₀.1 p₀.2.1‖, ?_, ?_⟩
  · apply norm_pos_iff.2
    intro heq
    rw [sub_eq_zero] at heq
    obtain ⟨k, hk⟩ := h.embedded p₀.1 hs₀ _ _ heq.symm
    have hd₁ : 0 < p₀.2.2 := by linarith [hd₀.1]
    have hd₂ : p₀.2.2 < P := by linarith [hd₀.2]
    have hdk : p₀.2.2 = k * P := by linarith
    exact not_int_mul_of_mem_Ioo hP ⟨hd₁, hd₂⟩ k hdk
  · intro s hs u d hd
    obtain ⟨k, hk⟩ := exists_int_sub_mem_Ico hP u
    have h1 : C s (u - k * P + d) = C s (u + d) := by
      rw [show u - k * P + d = (u + d) - k * P by ring]
      exact (h.periodic s).sub_int_mul_eq k
    have h2 : C s (u - k * P) = C s u := (h.periodic s).sub_int_mul_eq k
    have hmem : (s, u - k * P, d) ∈ Icc (0:ℝ) 1 ×ˢ (Icc (0:ℝ) P ×ˢ Icc η (P - η)) :=
      ⟨hs, Ico_subset_Icc_self hk, hd⟩
    have := isMinOn_iff.1 hmin _ hmem
    change ‖C p₀.1 (p₀.2.1 + p₀.2.2) - C p₀.1 p₀.2.1‖ ≤
      ‖C s (u - k * P + d) - C s (u - k * P)‖ at this
    rwa [h1, h2] at this

/-! ### (e) Assembly -/

/-- Reduce a pair of parameters `(u, u')` to `(ū, ū + d)` with `d ∈ [0, P)` without changing the
values of `C s`, `v s`. -/
theorem exists_reduce_pair (h : FramedFamily P C v) (s u u' : ℝ) :
    ∃ ū d : ℝ, d ∈ Ico 0 P ∧ C s ū = C s u ∧ v s ū = v s u ∧ C s (ū + d) = C s u' := by
  have hP := h.pos
  obtain ⟨k₁, hk₁⟩ := exists_int_sub_mem_Ico hP u
  obtain ⟨k₂, hk₂⟩ := exists_int_sub_mem_Ico hP (u' - (u - k₁ * P))
  refine ⟨u - k₁ * P, u' - (u - k₁ * P) - k₂ * P, hk₂, (h.periodic s).sub_int_mul_eq k₁,
    (h.periodic_v s).sub_int_mul_eq k₁, ?_⟩
  rw [show u - k₁ * P + (u' - (u - k₁ * P) - k₂ * P) = u' - k₂ * P by ring]
  exact (h.periodic s).sub_int_mul_eq k₂

/-- The uniform pushoff statement, with the pushoff written out. -/
theorem exists_uniform_pushoff_aux (h : FramedFamily P C v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ s ∈ Icc (0:ℝ) 1, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ u u',
      C s u + ε • v s u ≠ C s u' := by
  obtain ⟨c, hc0, hc⟩ := exists_cross_lower_bound h
  obtain ⟨V, hV0, hV⟩ := exists_v_bound h
  obtain ⟨K, hK0, hK⟩ := exists_deriv2_bound h
  have hP := h.pos
  obtain ⟨η, hη0, hηP, hηc⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ P / 4 ∧ η * K * V < c := by
    refine ⟨min (P / 4) (c / (2 * K * V)), lt_min (by positivity) (by positivity),
      min_le_left _ _, ?_⟩
    have h1 : min (P / 4) (c / (2 * K * V)) ≤ c / (2 * K * V) := min_le_right _ _
    have hKV : 0 < K * V := mul_pos hK0 hV0
    have h2 : min (P / 4) (c / (2 * K * V)) * (K * V) ≤ c / (2 * K * V) * (K * V) :=
      mul_le_mul_of_nonneg_right h1 hKV.le
    have h3 : c / (2 * K * V) * (K * V) = c / 2 := by
      field_simp
    nlinarith
  -- the local step
  have hlocal : ∀ s ∈ Icc (0:ℝ) 1, ∀ ε : ℝ, 0 < ε → ∀ u u', |u' - u| ≤ η →
      C s u + ε • v s u ≠ C s u' := by
    intro s hs ε hε u u' hclose heq
    have hT := taylor_bound (differentiable_slice h s) (differentiable_deriv_slice h s)
      (hK s hs) u u'
    refine local_contra hε hc0 (hc s hs u) (hV s hs u) hT hclose hηc hK0.le hV0.le ?_
    rw [← heq]
    abel
  -- the global step
  obtain ⟨m, hm0, hm⟩ := exists_global_min h hη0 hηP
  refine ⟨m / (2 * V), by positivity, ?_⟩
  intro s hs ε hε hεm u u' heq
  obtain ⟨ū, d, hd, hCū, hvū, hCd⟩ := exists_reduce_pair h s u u'
  have heq' : C s ū + ε • v s ū = C s (ū + d) := by rw [hCū, hvū, hCd]; exact heq
  rcases le_or_gt d η with hdη | hdη
  · exact hlocal s hs ε hε ū (ū + d)
      (by rw [add_sub_cancel_left, abs_of_nonneg hd.1]; exact hdη) heq'
  rcases le_or_gt (P - η) d with hdP | hdP
  · have heq'' : C s ū + ε • v s ū = C s (ū + d - P) := by
      rw [(h.periodic s).sub_eq]; exact heq'
    refine hlocal s hs ε hε ū (ū + d - P) ?_ heq''
    rw [show ū + d - P - ū = -(P - d) by ring, abs_neg, abs_of_nonneg (by linarith [hd.2])]
    linarith
  · have h1 := hm s hs ū d ⟨hdη.le, hdP.le⟩
    have h2 : C s (ū + d) - C s ū = ε • v s ū := by rw [← heq']; abel
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos hε] at h1
    have h3 : ε * ‖v s ū‖ ≤ ε * V := mul_le_mul_of_nonneg_left (hV s hs ū) hε.le
    have h4 : ε * V ≤ m / (2 * V) * V := mul_le_mul_of_nonneg_right hεm hV0.le
    have h5 : m / (2 * V) * V = m / 2 := by field_simp
    linarith

end Constants

end LinkingCalculus.Framing

/-- sm-3:2810-2812 "One common sufficiently small positive `ε` gives disjoint framed pairs
`(C_s, C_s + εv_s)` throughout the family": a uniform `ε₀ > 0` such that the pushoff
`C_s + ε v_s` misses `C_s` for every `s ∈ [0,1]` and `0 < ε ≤ ε₀`. -/
theorem FramedFamily.exists_uniform_pushoff {P : ℝ} {C v : ℝ → ℝ → E3} (h : FramedFamily P C v) :
    ∃ ε₀ > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ u u', pushoff (C s) (v s) ε u ≠ C s u' :=
  LinkingCalculus.Framing.exists_uniform_pushoff_aux h


/-! ## 8. Mixed crossings of a generic projection (sm-3:2798-2804): finiteness and the crossing
formula -/

namespace LinkingCalculus.Crossing

/-! ### Part (i): the mixed crossings are finite

The set of parameter pairs `(u,v)` with `C₂ v − C₁ u ∥ ν` is the zero set of the smooth "parallel
defect" `Φ(u,v) = P_ν(C₂ v − C₁ u)`.  At a zero, genericity makes `dΦ` injective, so the zero is
isolated (inverse function theorem, in the form `HasFDerivAt.eventually_ne`); the zero set is
closed, hence its intersection with the compact box `[0,P]²` is compact and discrete, hence finite
(sm-3:2881-2883). -/

/-- `projAlong ν` as a continuous linear map `w ↦ w − ⟪ν, w⟫ ν`. -/
def projAlongL (ν : E3) : E3 →L[ℝ] E3 :=
  ContinuousLinearMap.id ℝ E3 - (innerSL ℝ ν).smulRight ν

theorem projAlongL_apply (ν w : E3) : projAlongL ν w = projAlong ν w := by
  simp [projAlongL, projAlong, real_inner_comm]

/-- The parallel defect `Φ(u,v) = P_ν (C₂ v − C₁ u)`. -/
def defect (C₁ C₂ : ℝ → E3) (ν : E3) (p : ℝ × ℝ) : E3 := projAlong ν (C₂ p.2 - C₁ p.1)

/-- The derivative of the defect at `p = (u,v)`: `(a,b) ↦ P_ν (b C₂'(v) − a C₁'(u))`. -/
def defectDeriv (C₁ C₂ : ℝ → E3) (ν : E3) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] E3 :=
  (projAlongL ν).comp
    (ContinuousLinearMap.toSpanSingleton ℝ (deriv C₂ p.2) ∘L ContinuousLinearMap.snd ℝ ℝ ℝ -
      ContinuousLinearMap.toSpanSingleton ℝ (deriv C₁ p.1) ∘L ContinuousLinearMap.fst ℝ ℝ ℝ)

theorem defectDeriv_apply (C₁ C₂ : ℝ → E3) (ν : E3) (p : ℝ × ℝ) (a b : ℝ) :
    defectDeriv C₁ C₂ ν p (a, b) =
      b • projAlong ν (deriv C₂ p.2) - a • projAlong ν (deriv C₁ p.1) := by
  simp only [defectDeriv, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_fst', map_sub, map_smul]
  rw [projAlongL_apply, projAlongL_apply]

theorem hasFDerivAt_defect {C₁ C₂ : ℝ → E3} (h₁ : Differentiable ℝ C₁) (h₂ : Differentiable ℝ C₂)
    (ν : E3) (p : ℝ × ℝ) : HasFDerivAt (defect C₁ C₂ ν) (defectDeriv C₁ C₂ ν p) p := by
  have hD : HasFDerivAt (fun q : ℝ × ℝ => C₂ q.2 - C₁ q.1)
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv C₂ p.2) ∘L ContinuousLinearMap.snd ℝ ℝ ℝ -
        ContinuousLinearMap.toSpanSingleton ℝ (deriv C₁ p.1) ∘L ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    ((h₂ p.2).hasDerivAt.hasFDerivAt.comp p hasFDerivAt_snd).sub
      ((h₁ p.1).hasDerivAt.hasFDerivAt.comp p hasFDerivAt_fst)
  have := (projAlongL ν).hasFDerivAt.comp p hD
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  show projAlong ν (C₂ q.2 - C₁ q.1) = projAlongL ν (C₂ q.2 - C₁ q.1)
  rw [projAlongL_apply]

/-- Genericity: at a zero of the defect, its derivative is injective. -/
theorem defectDeriv_ker_eq_bot {C₁ C₂ : ℝ → E3} {ν : E3} (hν : GenericDirection C₁ C₂ ν)
    {p : ℝ × ℝ} (hp : defect C₁ C₂ ν p = 0) :
    LinearMap.ker (defectDeriv C₁ C₂ ν p : ℝ × ℝ →ₗ[ℝ] E3) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  rintro ⟨a, b⟩ hab
  have hpar : Parallel (C₂ p.2 - C₁ p.1) ν := (parallel_iff_projAlong_eq_zero ν _ hν.unit).2 hp
  rw [ContinuousLinearMap.coe_coe, defectDeriv_apply] at hab
  obtain ⟨ha, hb⟩ := LinearIndependent.pair_iff.1 (hν.indep p.1 p.2 hpar) (-a) b
    (by rw [neg_smul, neg_add_eq_sub]; exact hab)
  rw [neg_eq_zero] at ha
  exact Prod.ext ha hb

/-- Every zero of the defect is isolated (the inverse function theorem). -/
theorem eventually_defect_ne {P : ℝ} {C₁ C₂ : ℝ → E3} {ν : E3} (h : DisjointPair P C₁ C₂)
    (hν : GenericDirection C₁ C₂ ν) {p : ℝ × ℝ} (hp : defect C₁ C₂ ν p = 0) :
    ∀ᶠ q in 𝓝[≠] p, defect C₁ C₂ ν q ≠ 0 := by
  obtain ⟨K, -, hK⟩ := LinearMap.exists_antilipschitzWith _ (defectDeriv_ker_eq_bot hν hp)
  exact (hasFDerivAt_defect (h.circle₁.smooth.differentiable (by simp))
    (h.circle₂.smooth.differentiable (by simp)) ν p).eventually_ne ⟨K, hK⟩

/-- The zeros of the defect in the closed box `[0,P]²` form a finite set: closed in a compact set
and discrete. -/
theorem finite_defect_zeros {P : ℝ} {C₁ C₂ : ℝ → E3} {ν : E3} (h : DisjointPair P C₁ C₂)
    (hν : GenericDirection C₁ C₂ ν) :
    ({p : ℝ × ℝ | defect C₁ C₂ ν p = 0} ∩ Icc (0:ℝ) P ×ˢ Icc (0:ℝ) P).Finite := by
  have hd₁ := h.circle₁.smooth.differentiable (by simp)
  have hd₂ := h.circle₂.smooth.differentiable (by simp)
  have hcont : Continuous (defect C₁ C₂ ν) :=
    continuous_iff_continuousAt.2 fun p => (hasFDerivAt_defect hd₁ hd₂ ν p).continuousAt
  have hZ : IsClosed {p : ℝ × ℝ | defect C₁ C₂ ν p = 0} := isClosed_singleton.preimage hcont
  have hK : IsCompact ({p : ℝ × ℝ | defect C₁ C₂ ν p = 0} ∩ Icc (0:ℝ) P ×ˢ Icc (0:ℝ) P) :=
    (isCompact_Icc.prod isCompact_Icc).inter_left hZ
  refine hK.finite (isDiscrete_iff_nhdsNE.2 fun p hp => ?_)
  rw [Filter.inf_principal_eq_bot]
  exact (eventually_defect_ne h hν hp.1).mono fun q hq hqS => hq hqS.1

/-! ### Part (ii): the crossing formula, from `RegularPoleCount` -/

theorem sign_mul_of_pos {c x : ℝ} (hc : 0 < c) : Real.sign (c * x) = Real.sign x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx, Real.sign_of_neg (mul_neg_of_pos_of_neg hc hx)]
  · rw [mul_zero]
  · rw [Real.sign_of_pos hx, Real.sign_of_pos (mul_pos hc hx)]

/-- A vector with `ν × w = 0` is a multiple of the unit vector `ν`. -/
theorem eq_smul_of_cross_eq_zero {ν w : E3} (hν : ‖ν‖ = 1) (hw : cross ν w = 0) :
    w = ⟪ν, w⟫ • ν := by
  have h := cross_cross_eq ν ν w
  rw [hw, cross_zero_right, real_inner_self_eq_norm_sq, hν, one_pow, one_smul] at h
  exact (sub_eq_zero.1 h.symm).symm

/-- The cross product of two vectors of the plane `ν^⊥` is `det(x, y, ν) ν`. -/
theorem cross_eq_smul_of_orth {ν x y : E3} (hν : ‖ν‖ = 1) (hx : ⟪ν, x⟫ = 0) (hy : ⟪ν, y⟫ = 0) :
    cross x y = ⟪ν, cross x y⟫ • ν := by
  apply eq_smul_of_cross_eq_zero hν
  rw [cross_cross_eq, hx, hy, zero_smul, zero_smul, sub_zero]

/-- Independent projected tangents have a nonzero triple product with `ν`. -/
theorem inner_cross_ne_zero_of_linearIndependent {ν a b : E3} (hν : ‖ν‖ = 1)
    (hli : LinearIndependent ℝ ![projAlong ν a, projAlong ν b]) : ⟪ν, cross a b⟫ ≠ 0 := by
  intro h0
  apply cross_ne_zero_of_linearIndependent hli
  rw [cross_eq_smul_of_orth hν (inner_projAlong' ν a hν) (inner_projAlong' ν b hν),
    inner_cross_projAlong, h0, zero_smul]

/-- Derivative of the normalisation `f/|f|`: `(f/|f|)' = |f|⁻¹ P_{f/|f|} f'`. -/
theorem hasDerivAt_normalize {f : ℝ → E3} {f' : E3} {x : ℝ} (hf : HasDerivAt f f' x)
    (hx : f x ≠ 0) :
    HasDerivAt (fun y => ‖f y‖⁻¹ • f y) (‖f x‖⁻¹ • projAlong (‖f x‖⁻¹ • f x) f') x := by
  have hr : ‖f x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hsq : HasDerivAt (fun y => ‖f y‖ ^ 2) (2 * ⟪f x, f'⟫) x := hf.norm_sq
  have hsqrt := hsq.sqrt (pow_ne_zero 2 hr)
  have hn : HasDerivAt (fun y => ‖f y‖) (2 * ⟪f x, f'⟫ / (2 * √(‖f x‖ ^ 2))) x :=
    hsqrt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => (Real.sqrt_sq (norm_nonneg (f y))).symm)
  have key : HasDerivAt (fun y => ‖f y‖⁻¹ • f y)
      (‖f x‖⁻¹ • f' + (-(2 * ⟪f x, f'⟫ / (2 * √(‖f x‖ ^ 2))) / ‖f x‖ ^ 2) • f x) x :=
    (hn.inv hr).smul hf
  refine key.congr_deriv ?_
  rw [Real.sqrt_sq (norm_nonneg _)]
  simp only [projAlong, smul_sub, smul_smul, inner_smul_right, real_inner_comm (f x) f']
  match_scalars <;> field_simp

theorem hasDerivAt_chord_left {P : ℝ} {C₁ C₂ : ℝ → E3} (h : DisjointPair P C₁ C₂) (u v : ℝ) :
    HasDerivAt (fun u' => C₂ v - C₁ u') (-deriv C₁ u) u :=
  ((h.circle₁.smooth.differentiable (by simp)) u).hasDerivAt.const_sub (C₂ v)

theorem hasDerivAt_chord_right {P : ℝ} {C₁ C₂ : ℝ → E3} (h : DisjointPair P C₁ C₂) (u v : ℝ) :
    HasDerivAt (fun v' => C₂ v' - C₁ u) (deriv C₂ v) v :=
  ((h.circle₂.smooth.differentiable (by simp)) v).hasDerivAt.sub_const (C₁ u)

/-- `G_u = |D|⁻¹ P_G(−C₁'(u))`, `D = C₂ v − C₁ u`. -/
theorem pderivU_gaussMap {P : ℝ} {C₁ C₂ : ℝ → E3} (h : DisjointPair P C₁ C₂) (u v : ℝ) :
    pderivU (gaussMap C₁ C₂) u v =
      ‖C₂ v - C₁ u‖⁻¹ • projAlong (gaussMap C₁ C₂ u v) (-deriv C₁ u) :=
  (hasDerivAt_normalize (hasDerivAt_chord_left h u v) (sub_ne_zero.2 (h.disjoint u v))).deriv

/-- `G_v = |D|⁻¹ P_G(C₂'(v))`. -/
theorem pderivV_gaussMap {P : ℝ} {C₁ C₂ : ℝ → E3} (h : DisjointPair P C₁ C₂) (u v : ℝ) :
    pderivV (gaussMap C₁ C₂) u v =
      ‖C₂ v - C₁ u‖⁻¹ • projAlong (gaussMap C₁ C₂ u v) (deriv C₂ v) :=
  (hasDerivAt_normalize (hasDerivAt_chord_right h u v) (sub_ne_zero.2 (h.disjoint u v))).deriv

/-- The Gauss density of a disjoint pair: `G·(G_u × G_v) = |D|⁻² G·((−C₁') × C₂')`. -/
theorem gaussDensity_gaussMap {P : ℝ} {C₁ C₂ : ℝ → E3} (h : DisjointPair P C₁ C₂) (u v : ℝ) :
    gaussDensity (gaussMap C₁ C₂) u v =
      ‖C₂ v - C₁ u‖⁻¹ ^ 2 * ⟪gaussMap C₁ C₂ u v, cross (-deriv C₁ u) (deriv C₂ v)⟫ := by
  unfold gaussDensity
  rw [pderivU_gaussMap h, pderivV_gaussMap h, cross_smul_left, cross_smul_right,
    inner_smul_right, inner_smul_right, inner_cross_projAlong]
  ring

theorem norm_smul_gaussMap {C₁ C₂ : ℝ → E3} {u v : ℝ} (hne : C₂ v ≠ C₁ u) :
    ‖C₂ v - C₁ u‖ • gaussMap C₁ C₂ u v = C₂ v - C₁ u := by
  unfold gaussMap
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 (sub_ne_zero.2 hne)), one_smul]

/-- At a preimage of `±ν` the chord is parallel to `ν`. -/
theorem parallel_of_gaussMap_eq {C₁ C₂ : ℝ → E3} {ν : E3} {u v : ℝ} (hne : C₂ v ≠ C₁ u)
    (hN : gaussMap C₁ C₂ u v = ν ∨ gaussMap C₁ C₂ u v = -ν) : Parallel (C₂ v - C₁ u) ν := by
  rcases hN with hN | hN
  · exact ⟨‖C₂ v - C₁ u‖, (norm_smul_gaussMap hne).symm.trans (by rw [hN])⟩
  · exact ⟨-‖C₂ v - C₁ u‖, (norm_smul_gaussMap hne).symm.trans (by rw [hN, smul_neg, neg_smul])⟩

/-- Conversely, a chord parallel to the unit vector `ν` has Gauss image `ν` or `−ν`. -/
theorem gaussMap_eq_or_eq_neg {C₁ C₂ : ℝ → E3} {ν : E3} {u v : ℝ} (hne : C₂ v ≠ C₁ u)
    (hν : ‖ν‖ = 1) (hpar : Parallel (C₂ v - C₁ u) ν) :
    gaussMap C₁ C₂ u v = ν ∨ gaussMap C₁ C₂ u v = -ν := by
  obtain ⟨t, ht⟩ := hpar
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact sub_ne_zero.2 hne (by rw [ht, zero_smul])
  unfold gaussMap
  rw [ht, norm_smul, Real.norm_eq_abs, hν, mul_one, smul_smul]
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · right
    rw [abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ ht0, neg_one_smul]
  · left
    rw [abs_of_pos hpos, inv_mul_cancel₀ ht0, one_smul]

/-- At a crossing the local sign of the Gauss map is the overpass-first crossing sign. -/
theorem sign_gaussDensity_eq_crossingSign {P : ℝ} {C₁ C₂ : ℝ → E3} {ν : E3}
    (h : DisjointPair P C₁ C₂) (hν : GenericDirection C₁ C₂ ν) (p : ℝ × ℝ)
    (hN : gaussMap C₁ C₂ p.1 p.2 = ν ∨ gaussMap C₁ C₂ p.1 p.2 = -ν) :
    Real.sign (gaussDensity (gaussMap C₁ C₂) p.1 p.2) = lcCrossingSign C₁ C₂ ν p := by
  have hne := h.disjoint p.1 p.2
  have hr : 0 < ‖C₂ p.2 - C₁ p.1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hD := (norm_smul_gaussMap hne).symm
  rw [gaussDensity_gaussMap h, sign_mul_of_pos (pow_pos (inv_pos.2 hr) 2)]
  unfold lcCrossingSign planeDet
  rcases hN with hN | hN
  · have hpos : 0 < ⟪C₂ p.2 - C₁ p.1, ν⟫ := by
      rw [hD, hN, real_inner_smul_left, real_inner_self_eq_norm_sq, hν.unit, one_pow, mul_one]
      exact hr
    rw [ite_eq_left hpos, hN, inner_cross_projAlong,
      inner_cross_swap ν (deriv C₁ p.1) (deriv C₂ p.2), cross_neg_left, inner_neg_right]
  · have hneg : ¬ 0 < ⟪C₂ p.2 - C₁ p.1, ν⟫ := by
      rw [hD, hN, real_inner_smul_left, inner_neg_left, real_inner_self_eq_norm_sq, hν.unit,
        one_pow, mul_neg, mul_one]
      exact not_lt.2 (by linarith)
    rw [ite_eq_right hneg, hN, inner_cross_projAlong, cross_neg_left, inner_neg_left,
      inner_neg_right, neg_neg]

/-- `±ν` are regular values of the Gauss map of a pair for which `ν` is generic. -/
theorem gaussDensity_gaussMap_ne_zero {P : ℝ} {C₁ C₂ : ℝ → E3} {ν : E3}
    (h : DisjointPair P C₁ C₂) (hν : GenericDirection C₁ C₂ ν) (u v : ℝ)
    (hN : gaussMap C₁ C₂ u v = ν ∨ gaussMap C₁ C₂ u v = -ν) :
    gaussDensity (gaussMap C₁ C₂) u v ≠ 0 := by
  have hne := h.disjoint u v
  have hr : ‖C₂ v - C₁ u‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hne)
  have hkey : ⟪ν, cross (deriv C₁ u) (deriv C₂ v)⟫ ≠ 0 :=
    inner_cross_ne_zero_of_linearIndependent hν.unit
      (hν.indep u v (parallel_of_gaussMap_eq hne hN))
  rw [gaussDensity_gaussMap h]
  refine mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hr)) ?_
  rcases hN with hN | hN
  · rw [hN, cross_neg_left, inner_neg_right]
    exact neg_ne_zero.2 hkey
  · rw [hN, cross_neg_left, inner_neg_left, inner_neg_right, neg_neg]
    exact hkey

end LinkingCalculus.Crossing

/-- sm-3:2798-2799: for a generic direction the mixed crossings are finite ("the inverse function
theorem makes it discrete, and it is closed in a compact torus", sm-3:2881-2883). -/
theorem DisjointPair.finite_mixedCrossings {P : ℝ} {C₁ C₂ : ℝ → E3} {ν : E3}
    (h : DisjointPair P C₁ C₂) (hν : GenericDirection C₁ C₂ ν) :
    (mixedCrossings P C₁ C₂ ν).Finite := by
  refine (Crossing.finite_defect_zeros h hν).subset ?_
  rintro ⟨u, v⟩ ⟨hbox, hpar⟩
  exact ⟨(parallel_iff_projAlong_eq_zero ν _ hν.unit).1 hpar,
    Ico_subset_Icc_self hbox.1, Ico_subset_Icc_self hbox.2⟩

/-- sm-3:2802-2804, from the isolated hypothesis fd:regular-pole-count applied to the regular values
`ν` and `−ν` of the Gauss map: `ℓ(C₁,C₂)` is one half of the sum of the crossing signs over the
mixed crossings of the projection along `ν` (sm-3:2917-2941). -/
theorem crossing_formula_of_regularPoleCount (hreg : RegularPoleCount) {P : ℝ} {C₁ C₂ : ℝ → E3}
    {ν : E3} (h : DisjointPair P C₁ C₂) (hν : GenericDirection C₁ C₂ ν) :
    linking P C₁ C₂ = (1 / 2) * ∑ᶠ p ∈ mixedCrossings P C₁ C₂ ν, lcCrossingSign C₁ C₂ ν p := by
  have hfinMC := h.finite_mixedCrossings hν
  have hsmooth : ContDiff ℝ ∞ (uncurry (gaussMap C₁ C₂)) :=
    contDiff_gaussMap h.circle₁.smooth h.circle₂.smooth h.disjoint
  have hperU : ∀ v, Periodic (fun u => gaussMap C₁ C₂ u v) P := by
    intro v u
    simp only [gaussMap, h.circle₁.periodic u]
  have hperV : ∀ u, Periodic (gaussMap C₁ C₂ u) P := by
    intro u v
    simp only [gaussMap, h.circle₂.periodic v]
  have hunit : ∀ u v, ‖gaussMap C₁ C₂ u v‖ = 1 := fun u v => norm_gaussMap (h.disjoint u v)
  -- the preimages of `ν` and `−ν` are contained in the mixed crossings
  have hsub : ∀ N : E3, N = ν ∨ N = -ν →
      {p : ℝ × ℝ | p ∈ Ico (0:ℝ) P ×ˢ Ico (0:ℝ) P ∧ gaussMap C₁ C₂ p.1 p.2 = N} ⊆
        mixedCrossings P C₁ C₂ ν := by
    intro N hNν p hp
    refine ⟨hp.1, Crossing.parallel_of_gaussMap_eq (h.disjoint p.1 p.2) ?_⟩
    rcases hNν with rfl | rfl
    · exact Or.inl hp.2
    · exact Or.inr hp.2
  have hfinP : {p : ℝ × ℝ | p ∈ Ico (0:ℝ) P ×ˢ Ico (0:ℝ) P ∧ gaussMap C₁ C₂ p.1 p.2 = ν}.Finite :=
    hfinMC.subset (hsub ν (Or.inl rfl))
  have hfinM : {p : ℝ × ℝ | p ∈ Ico (0:ℝ) P ×ˢ Ico (0:ℝ) P ∧ gaussMap C₁ C₂ p.1 p.2 = -ν}.Finite :=
    hfinMC.subset (hsub (-ν) (Or.inr rfl))
  -- the pole count at `ν` and at `−ν`
  have eP := hreg P (gaussMap C₁ C₂) ν h.pos hsmooth hperU hperV hunit hν.unit
    (fun u v huv => Crossing.gaussDensity_gaussMap_ne_zero h hν u v (Or.inl huv)) hfinP
  have eM := hreg P (gaussMap C₁ C₂) (-ν) h.pos hsmooth hperU hperV hunit
    (by rw [norm_neg, hν.unit])
    (fun u v huv => Crossing.gaussDensity_gaussMap_ne_zero h hν u v (Or.inr huv)) hfinM
  have sP : ∑ p ∈ hfinP.toFinset, Real.sign (gaussDensity (gaussMap C₁ C₂) p.1 p.2) =
      ∑ p ∈ hfinP.toFinset, lcCrossingSign C₁ C₂ ν p :=
    Finset.sum_congr rfl fun p hp =>
      Crossing.sign_gaussDensity_eq_crossingSign h hν p (Or.inl (hfinP.mem_toFinset.1 hp).2)
  have sM : ∑ p ∈ hfinM.toFinset, Real.sign (gaussDensity (gaussMap C₁ C₂) p.1 p.2) =
      ∑ p ∈ hfinM.toFinset, lcCrossingSign C₁ C₂ ν p :=
    Finset.sum_congr rfl fun p hp =>
      Crossing.sign_gaussDensity_eq_crossingSign h hν p (Or.inr (hfinM.mem_toFinset.1 hp).2)
  -- the mixed crossings are the disjoint union of the two preimages
  have hunion : hfinMC.toFinset = hfinP.toFinset ∪ hfinM.toFinset := by
    ext p
    simp only [Finset.mem_union, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hbox, hpar⟩
      rcases Crossing.gaussMap_eq_or_eq_neg (h.disjoint p.1 p.2) hν.unit hpar with hp | hp
      · exact Or.inl ⟨hbox, hp⟩
      · exact Or.inr ⟨hbox, hp⟩
    · rintro (hp | hp)
      · exact hsub ν (Or.inl rfl) hp
      · exact hsub (-ν) (Or.inr rfl) hp
  have hdisj : Disjoint hfinP.toFinset hfinM.toFinset := by
    rw [Finset.disjoint_left]
    intro p hpP hpM
    have h1 := (hfinP.mem_toFinset.1 hpP).2
    have h2 := (hfinM.mem_toFinset.1 hpM).2
    have h3 := congrArg (fun w => ⟪ν, w⟫) (h1.symm.trans h2)
    simp only [inner_neg_right, real_inner_self_eq_norm_sq, hν.unit] at h3
    norm_num at h3
  rw [finsum_mem_eq_finite_toFinset_sum _ hfinMC, hunion, Finset.sum_union hdisj]
  show gaussIntegral P (gaussMap C₁ C₂) = _
  linarith [eP, eM, sP, sM]


/-! ## 9. Assembly: the row -/

/-- sm-3:2810-2812: the common radius, packaged as disjoint pairs of smooth circles. -/
theorem FramedFamily.exists_uniform_disjointPair {P : ℝ} {C v : ℝ → ℝ → E3}
    (h : FramedFamily P C v) :
    ∃ ε₀ > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ → DisjointPair P (C s) (pushoff (C s) (v s) ε) :=
  h.exists_uniform_disjointPair_of (fun h' => h'.exists_uniform_pushoff)

/-- sm-3:2812-2813: radius and family independence of the framed pairing. -/
theorem FramedFamily.linking_pushoff_eq {P : ℝ} {C v : ℝ → ℝ → E3} (h : FramedFamily P C v)
    {ε₀ : ℝ}
    (hd : ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ u u', pushoff (C s) (v s) ε u ≠ C s u')
    {s s' : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (hs' : s' ∈ Icc (0:ℝ) 1) {ε ε' : ℝ} (hε : 0 < ε)
    (hεε₀ : ε ≤ ε₀) (hε' : 0 < ε') (hε'ε₀ : ε' ≤ ε₀) :
    linking P (C s) (pushoff (C s) (v s) ε) = linking P (C s') (pushoff (C s') (v s') ε') :=
  h.linking_pushoff_eq_of_global
    (by
      intro P hP C₁ C₂ h₁ h₂ hp₁ hp₂ hdis t t'
      exact linking_const_of_family_global hP h₁ h₂ hp₁ hp₂ hdis t t')
    hd hs hs' hε hεε₀ hε' hε'ε₀

/-- sm-3:2817-2820: the common `ε₀` of the transverse family. -/
theorem TransverseFamily.exists_uniform {P : ℝ} {T : ℝ → ℝ → E3} (h : TransverseFamily P T) :
    ∃ ε₀ > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ →
      IsPositiveTransverseEmbedding P (T s) ∧
      IsPositiveTransverseEmbedding P (pushoff (T s) (fun _ => ey) ε) ∧
      DisjointPair P (T s) (pushoff (T s) (fun _ => ey) ε) :=
  h.exists_uniform_of (fun h' => h'.exists_uniform_pushoff)

/-- sm-3:2820-2824: `sl(T_s) = ℓ(T_s, T_s + ε∂_y)` is independent of such `ε` and of `s`. -/
theorem TransverseFamily.selfLinking_eq {P : ℝ} {T : ℝ → ℝ → E3} (h : TransverseFamily P T)
    {ε₀ : ℝ}
    (hd : ∀ s ∈ Icc (0:ℝ) 1, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ u u', pushoff (T s) (fun _ => ey) ε u ≠ T s u')
    {s s' : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (hs' : s' ∈ Icc (0:ℝ) 1) {ε ε' : ℝ} (hε : 0 < ε)
    (hεε₀ : ε ≤ ε₀) (hε' : 0 < ε') (hε'ε₀ : ε' ≤ ε₀) :
    selfLinking P (T s) ε = selfLinking P (T s') ε' :=
  h.framedFamily.linking_pushoff_eq hd hs hs' hε hεε₀ hε' hε'ε₀

/-- **fd:linking-calculus** (sm-3:2785-2830): the row.  Every field is proved; the mixed-crossing
formula is proved from the isolated hypothesis `RegularPoleCount` (fd:regular-pole-count,
sm-3:2894-2897), which is the only unformalised ingredient. -/
theorem fd_linking_calculus_of : LinkingCalculusDataOf where
  symm _ _ _ h := h.linking_comm
  family_const _ _ _ h _ hs _ hs' := h.linking_eq hs hs'
  finite_crossings _ _ _ _ h hν := h.finite_mixedCrossings hν
  crossing_formula hreg _ _ _ _ h hν := crossing_formula_of_regularPoleCount hreg h hν
  framing_uniform _ _ _ h := h.exists_uniform_disjointPair
  framing_invariant _ _ _ h _ _ hd _ hs _ hs' _ _ hε hεε₀ hε' hε'ε₀ :=
    h.linking_pushoff_eq hd hs hs' hε hεε₀ hε' hε'ε₀
  framing_homotopy _ _ _ h _ _ hd _ hs _ hs' _ _ hε hεε₀ hε' hε'ε₀ :=
    h.linking_pushoff_eq hd hs hs' hε hεε₀ hε' hε'ε₀
  transverse_uniform _ _ h := h.exists_uniform
  self_linking_invariant _ _ h _ _ hd _ hs _ hs' _ _ hε hεε₀ hε' hε'ε₀ :=
    h.selfLinking_eq hd hs hs' hε hεε₀ hε' hε'ε₀

end

end SM
