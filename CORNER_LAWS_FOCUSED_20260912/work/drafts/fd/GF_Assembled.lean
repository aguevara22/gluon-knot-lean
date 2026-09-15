import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import SM.ContactMotions
import SM.ParameterAvoidance

/-! # SM fd:generic-front — generic fronts of Legendrian knots (row 87), assembled

Assembled 2026-09-14 (work/drafts/fd/, `GF_assemble.py`) from `GF_Skeleton.lean` and the unit files
`GF_U_P{0,…,6}.lean`.  Source: reference/SM/sm-3-statesum.tex:2613-2630 (statement), 2631-2783
(proof).  Route: `FD_84_87_FEASIBILITY_v2.md` §2; leaf plan: `GF_PLAN.md`; assembly record:
`GF_ASSEMBLY_REPORT.md`.

Layout.  §1–§4 (from `namespace SM` to `GenericFrontData`) are **byte-identical** to
`GenericFront_Statement.lean` lines 79-255 (the statement).  §5 is the proof: definitions, glue,
the former leaf lemmas (all proved) grouped in units P0–P6 with their helpers (prefixes `gp0_` …
`gp6_`), and the row theorem `SM.fd_generic_front : GenericFrontData`.
`#print axioms SM.fd_generic_front` gives `[propext, Classical.choice, Quot.sound]`.  Independent of
the row-84 file: the row-84 notions it needs are the copies in `SM.GenericFront` (§1).

Units: P0 contact isotopies from Hamiltonian flows (row 86) · P1 simultaneous zeros of `(x′,x″)`
(row 85, `(d,q) = (1,2)`) · P2 the uniform collar (local front injectivity) · P3 cusps on branches
and triple points (row 85, `(2,3)` and `(3,4)`) · P4 transverse, finite double points · P5 exact
cusp germs · P6 concatenation, pushoff annulus, knot type.

One deviation from the skeleton: its leaf P2.2 (`stage1_stable`, persistence of the collar with the
same width) was false as stated and is replaced by persistence with any smaller width
(`gp2_stage1_stable_of_lt`; see the note in Unit P2 and `GF_U_P2_REPORT.md` §2-3); `step2` uses the
half width.  The header carries one import beyond the skeleton's
(`Mathlib.Analysis.Calculus.ContDiff.Bounds`, the Leibniz rule for P5.4).

Check: `cd work/lean && lake env lean ../drafts/fd/GF_Assembled.lean`. -/

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

lemma gp0_alpha_eq (p v : ℝ³) : alpha p v = ContactMotions.alpha p v := rfl

/-- A point outside the support of `X_H` is fixed by the flow (uniqueness against the constant
curve). -/
lemma gp0_hamFlow_fixed {H : ℝ³ → ℝ} (h : ContactMotionsHyp H) {p : ℝ³}
    (hp : p ∉ tsupport (hamVF H)) (s : ℝ) : hamFlow H s p = p := by
  obtain ⟨K, hK⟩ := h.exists_lipschitzWith
  have hfl := h.isGlobalFlow
  have h0 : hamVF H p = 0 := image_eq_zero_of_notMem_tsupport hp
  have := ContactMotions.ODE_unique_global hK (f := fun s => hamFlow H s p)
    (g := fun _ => p) (fun s => hfl.hasDerivAt s p)
    (fun s => by simpa [h0] using hasDerivAt_const s p) (t₀ := 0) (by simp [hfl.zero])
  exact congrFun this s

/-- A point fixed by every flow is fixed by every composition. -/
lemma gp0_composeFlows_fixed (n : ℕ) (Hs : Fin n → ℝ³ → ℝ) (b : Fin n → ℝ) {p : ℝ³}
    (hp : ∀ i s, hamFlow (Hs i) s p = p) : composeFlows n Hs b p = p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show hamFlow (Hs 0) (b 0) (composeFlows n (Fin.tail Hs) (Fin.tail b) p) = p
    rw [ih (Fin.tail Hs) (Fin.tail b) (fun i s => hp i.succ s), hp 0]

/-- Each composition of flows is smooth in the point. -/
lemma gp0_contDiff_composeFlows (n : ℕ) (Hs : Fin n → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) (b : Fin n → ℝ) :
    ContDiff ℝ ∞ (composeFlows n Hs b) :=
  (fd_contact_motions.compositions_smooth n Hs hHs).comp (contDiff_const.prodMk contDiff_id)

/-- Each composition of flows has a smooth two-sided inverse (the reversed composition of the
inverse flows). -/
lemma gp0_composeFlows_inv (n : ℕ) (Hs : Fin n → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) (b : Fin n → ℝ) :
    ∃ Ψ : ℝ³ → ℝ³, ContDiff ℝ ∞ Ψ ∧ LeftInverse Ψ (composeFlows n Hs b) ∧
      RightInverse Ψ (composeFlows n Hs b) := by
  induction n with
  | zero => exact ⟨id, contDiff_id, fun p => rfl, fun p => rfl⟩
  | succ n ih =>
    obtain ⟨Ψ, hΨ, hl, hr⟩ := ih (Fin.tail Hs) (fun i => hHs i.succ) (Fin.tail b)
    obtain ⟨_, hd⟩ := fd_contact_motions.diffeo (Hs 0) (hHs 0)
    obtain ⟨_, hsm, hl0, hr0⟩ := hd (b 0)
    refine ⟨Ψ ∘ hamFlow (Hs 0) (-(b 0)), hΨ.comp hsm, fun p => ?_, fun q => ?_⟩
    · show Ψ (hamFlow (Hs 0) (-(b 0)) (hamFlow (Hs 0) (b 0)
        (composeFlows n (Fin.tail Hs) (Fin.tail b) p))) = p
      rw [hl0, hl]
    · show hamFlow (Hs 0) (b 0) (composeFlows n (Fin.tail Hs) (Fin.tail b)
        (Ψ (hamFlow (Hs 0) (-(b 0)) q))) = q
      rw [hr, hr0]

/-- Each composition of flows is a contactomorphism with a positive conformal factor. -/
lemma gp0_composeFlows_contact (n : ℕ) (Hs : Fin n → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) (b : Fin n → ℝ) (p : ℝ³) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, alpha (composeFlows n Hs b p) (fderiv ℝ (composeFlows n Hs b) p v)
      = c * alpha p v := by
  induction n generalizing p with
  | zero =>
    refine ⟨1, one_pos, fun v => ?_⟩
    have : composeFlows 0 Hs b = id := funext fun _ => rfl
    rw [this, fderiv_id]
    simp
  | succ n ih =>
    obtain ⟨c, hc, hcv⟩ := ih (Fin.tail Hs) (fun i => hHs i.succ) (Fin.tail b) p
    set g := composeFlows n (Fin.tail Hs) (Fin.tail b) with hg
    have hcomp : composeFlows (n + 1) Hs b = hamFlow (Hs 0) (b 0) ∘ g := funext fun _ => rfl
    have hgd : DifferentiableAt ℝ g p :=
      (gp0_contDiff_composeFlows n (Fin.tail Hs) (fun i => hHs i.succ) (Fin.tail b)).differentiable
        (by simp) p
    have hfd : DifferentiableAt ℝ (hamFlow (Hs 0) (b 0)) (g p) :=
      ((fd_contact_motions.diffeo (Hs 0) (hHs 0)).2 (b 0)).1.differentiable (by simp) (g p)
    refine ⟨ContactMotions.confFactor (Hs 0) (b 0) (g p) * c,
      mul_pos (fd_contact_motions.confFactor_pos (Hs 0) (hHs 0) (b 0) (g p)) hc, fun v => ?_⟩
    rw [hcomp, fderiv_comp p hfd hgd, ContinuousLinearMap.comp_apply, comp_apply, gp0_alpha_eq,
      fd_contact_motions.contact (Hs 0) (hHs 0) (b 0) (g p), ← gp0_alpha_eq, hcv v, mul_assoc]

/-- LEAF P0.1.  `s ↦ Φ_{sa}` is a compactly supported contact isotopy (row 86: `fd_contact_motions`
gives joint smoothness, the group law/inverses, `Φ^*α = c α` with `c > 0`; each flow fixes the
complement of `tsupport (hamVF Hᵢ)`). -/
theorem isContactIsotopy_hamIsotopy (n : ℕ) (Hs : Fin n → ℝ³ → ℝ) (a : Fin n → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) : IsContactIsotopy (hamIsotopy n Hs a) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- joint smoothness
    have h1 := fd_contact_motions.compositions_smooth n Hs hHs
    have h2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ³ => (q.1 • a, q.2)) :=
      (contDiff_fst.smul contDiff_const).prodMk contDiff_snd
    exact (h1.comp h2).contDiffOn
  · intro p
    show composeFlows n Hs ((0 : ℝ) • a) p = p
    rw [zero_smul]
    exact ContactMotions.composeFlows_zero n Hs (fun i p => (hHs i).hamFlow_zero p) p
  · intro t _
    exact gp0_composeFlows_inv n Hs hHs (t • a)
  · refine ⟨⋃ i, tsupport (hamVF (Hs i)), isCompact_iUnion fun i => (hHs i).hasCompactSupport_hamVF,
      fun t _ p hp => ?_⟩
    rw [mem_iUnion, not_exists] at hp
    exact gp0_composeFlows_fixed n Hs (t • a) fun i s => gp0_hamFlow_fixed (hHs i) (hp i) s
  · intro s _ p
    exact gp0_composeFlows_contact n Hs hHs (s • a) p

/-- LEAF P0.2.  A stage of a contact isotopy carries an embedded Legendrian circle to an embedded
Legendrian circle (sm-3:2637-2638 "its images are exactly Legendrian embeddings"). -/
theorem contact_preserves_legendrian {Φ : ℝ → ℝ³ → ℝ³} (hΦ : IsContactIsotopy Φ) {L : ℝ → ℝ³}
    (hL : IsEmbeddedCircle L) (hLeg : IsLegendrian L) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    IsEmbeddedCircle (Φ s ∘ L) ∧ IsLegendrian (Φ s ∘ L) := by
  -- smoothness of the stage `Φ s`
  have hΦs : ContDiff ℝ ∞ (Φ s) := by
    have h1 : ContDiffOn ℝ ∞ (uncurry Φ ∘ fun p : ℝ³ => (s, p)) univ :=
      hΦ.ambient.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun p _ => ⟨hs, mem_univ _⟩)
    exact contDiffOn_univ.1 h1
  obtain ⟨Ψ, hΨ, hl, hr⟩ := hΦ.ambient.diffeo s hs
  -- `DΦ_s(p)` is injective: `DΨ(Φ_s p) ∘ DΦ_s(p) = id`
  have hinj : ∀ p v, fderiv ℝ (Φ s) p v = 0 → v = 0 := by
    intro p v hv
    have hid : Ψ ∘ Φ s = id := funext hl
    have h1 := fderiv_comp p (hΨ.differentiable (by simp) (Φ s p))
      (hΦs.differentiable (by simp) p)
    rw [hid, fderiv_id] at h1
    have := congrArg (fun T : ℝ³ →L[ℝ] ℝ³ => T v) h1
    simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, hv, map_zero] at this
    exact this
  -- the derivative of the image curve
  have hder : ∀ θ, HasDerivAt (Φ s ∘ L) (fderiv ℝ (Φ s) (L θ) (deriv L θ)) θ := fun θ =>
    (hΦs.differentiable (by simp) (L θ)).hasFDerivAt.comp_hasDerivAt θ
      (hL.smooth.differentiable (by simp) θ).hasDerivAt
  refine ⟨⟨hΦs.comp hL.smooth, fun θ => ?_, fun θ θ' h => ?_, fun θ => ?_⟩, fun θ => ?_⟩
  · show Φ s (L (θ + 2 * π)) = Φ s (L θ)
    rw [hL.periodic θ]
  · exact hL.injective θ θ' (hl.injective h)
  · rw [(hder θ).deriv]
    intro h0
    exact hL.immersion θ (hinj _ _ h0)
  · rw [(hder θ).deriv]
    obtain ⟨c, _, hc⟩ := hΦ.contact s hs (L θ)
    show alpha (Φ s (L θ)) (fderiv ℝ (Φ s) (L θ) (deriv L θ)) = 0
    rw [hc, hLeg θ, mul_zero]

/-- `Φ_{t eᵢ} = φ_{Hᵢ}^t`: with all other times zero the composition is the single flow. -/
lemma gp0_composeFlows_single (n : ℕ) (Hs : Fin n → ℝ³ → ℝ)
    (hHs : ∀ i, ContactMotionsHyp (Hs i)) (i : Fin n) (t : ℝ) (p : ℝ³) :
    composeFlows n Hs (Pi.single i t) p = hamFlow (Hs i) t p := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    show hamFlow (Hs 0) ((Pi.single i t : Fin (n + 1) → ℝ) 0) (composeFlows n (Fin.tail Hs)
      (Fin.tail (Pi.single i t : Fin (n + 1) → ℝ)) p) = hamFlow (Hs i) t p
    refine Fin.cases ?_ (fun j => ?_) i
    · have h1 : Fin.tail (Pi.single (0 : Fin (n + 1)) t : Fin (n + 1) → ℝ) = 0 := by
        funext k; simp [Fin.tail, Fin.succ_ne_zero]
      rw [h1, ContactMotions.composeFlows_zero n (Fin.tail Hs) (fun k q => (hHs k.succ).hamFlow_zero q)]
      simp
    · have h1 : Fin.tail (Pi.single (j.succ : Fin (n + 1)) t : Fin (n + 1) → ℝ) = Pi.single j t := by
        funext k; simp [Fin.tail, Pi.single_apply, Fin.succ_inj]
      rw [h1, ih (Fin.tail Hs) (fun k => hHs k.succ) j]
      simp [Fin.tail, (hHs 0).hamFlow_zero]

/-- LEAF P0.3.  "At `a = 0`, the `aᵢ` derivative of `Φ_a ∘ L` is `X_{Hᵢ} ∘ L`" (sm-3:2635). -/
theorem fderiv_composeFlows_zero (n : ℕ) (Hs : Fin n → ℝ³ → ℝ) (hHs : ∀ i, ContactMotionsHyp (Hs i))
    (p : ℝ³) (i : Fin n) :
    fderiv ℝ (fun a : Fin n → ℝ => composeFlows n Hs a p) 0 (Pi.single i 1) = hamVF (Hs i) p := by
  set f := fun a : Fin n → ℝ => composeFlows n Hs a p with hf
  have hfs : ContDiff ℝ ∞ f :=
    (fd_contact_motions.compositions_smooth n Hs hHs).comp (contDiff_id.prodMk contDiff_const)
  have hd : HasFDerivAt f (fderiv ℝ f 0) 0 := (hfs.differentiable (by simp) 0).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => t • (Pi.single i 1 : Fin n → ℝ)) (Pi.single i 1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : Fin n → ℝ)
  have hd' : HasFDerivAt f (fderiv ℝ f 0) ((0 : ℝ) • (Pi.single i 1 : Fin n → ℝ)) := by
    simpa using hd
  have h1 : HasDerivAt (fun t : ℝ => f (t • (Pi.single i 1 : Fin n → ℝ)))
      (fderiv ℝ f 0 (Pi.single i 1)) 0 := by
    have := hd'.comp_hasDerivAt (0 : ℝ) hline
    exact this
  have heq : (fun t : ℝ => f (t • (Pi.single i 1 : Fin n → ℝ))) = fun t => hamFlow (Hs i) t p := by
    funext t
    have : t • (Pi.single i 1 : Fin n → ℝ) = Pi.single i t := by
      funext k; simp [Pi.single_apply]
    simp only [hf, this]
    exact gp0_composeFlows_single n Hs hHs i t p
  rw [heq] at h1
  have h2 : HasDerivAt (fun t => hamFlow (Hs i) t p) (hamVF (Hs i) p) 0 := by
    have := (hHs i).isGlobalFlow.hasDerivAt 0 p
    rwa [(hHs i).hamFlow_zero] at this
  exact h1.unique h2

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

/-! The skeleton's LEAF P2.2 (`stage1_stable`: for every collar width `δc` of `L` and every
Hamiltonian family, `Stage1` and the collar of the SAME width `δc` persist for all small parameters)
is FALSE as stated (`GF_U_P2_REPORT.md` §2, numerically checked in `GF_U_P2_probe.py`): for
`L(θ) = (sin 2θ, sin θ, cos θ − ⅓cos 3θ)` the front has one double point at circular distance
exactly `π = δc`, and the `H^x`-bump perturbation at one of its two points moves the double point
to distance `π − |a|/2 < δc` for every `a ≠ 0`.  The true statement is persistence of the collar
with any SMALLER width, `gp2_stage1_stable_of_lt` above (`δ' < δc`); `step2` below uses it with
the half width `δc / 2` (`gp2_locallyInjectiveFront_mono`).  Nothing else referenced the leaf. -/

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
  -- P2.2 is false with the width `δc` itself; work with the half width `δc / 2`, which persists
  -- (`gp2_stage1_stable_of_lt`).  The family is obtained with a provisional radius `1`, then shrunk.
  have hδ' : LocallyInjectiveFront L (δc / 2) :=
    gp2_locallyInjectiveFront_mono hδ (half_pos hδ.1) (half_le_self hδ.1.le)
  obtain ⟨m, Hs, r, hHs, hr, -, hC, hR⟩ := exists_CR_avoidance h hδ' 1 one_pos
  obtain ⟨rs, hrs, hstab⟩ :=
    gp2_stage1_stable_of_lt h hδ (half_pos hδ.1) (half_lt_self hδ.1) m Hs hHs
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
  have hU : interior (ParameterAvoidance.zeroParams (K2 (δc / 2)) (Metric.closedBall 0 r') (Cmap L m Hs) ∪
      ParameterAvoidance.zeroParams (K3 (δc / 2)) (Metric.closedBall 0 r') (Rmap L m Hs)) = ∅ := by
    rw [interior_union_isClosed_of_interior_empty hA.isClosed_zeroParams
      hB.interior_zeroParams_eq_empty]
    exact hA.interior_zeroParams_eq_empty
  obtain ⟨a, hab, ha⟩ := (interior_eq_empty_iff_dense_compl.1 hU).exists_mem_open
    Metric.isOpen_ball (Metric.nonempty_ball.2 hr'pos)
  have hav : a ∉ ParameterAvoidance.zeroParams (K2 (δc / 2)) (Metric.closedBall 0 r') (Cmap L m Hs) ∧
      a ∉ ParameterAvoidance.zeroParams (K3 (δc / 2)) (Metric.closedBall 0 r') (Rmap L m Hs) := by
    simpa [Set.mem_union, not_or] using hab
  have har : a ∈ Metric.closedBall (0 : ℝ^m) r' := Metric.ball_subset_closedBall ha
  have hnorm : ‖a‖ < rs := by
    have := Metric.mem_closedBall.1 har; rw [dist_zero_right] at this; linarith
  obtain ⟨hs1, hδa⟩ := hstab a hnorm
  refine ⟨hamIsotopy m Hs (par a), isContactIsotopy_hamIsotopy m Hs (par a) hHs, ?_⟩
  rw [hamIsotopy_one]
  exact { hs1 with
    collar := ⟨δc / 2, hδa⟩
    noCuspOnBranch := noCuspOnBranch_of_C h m Hs hHs hδa hav.1 har
    noTriple := noTriple_of_R h m Hs hHs hδa hav.2 har }

/-! ### Unit P4 — transverse, finite double points (sm-3:2715-2730) -/

/-- P4 helper: the derivatives of the coordinate functions of a smooth curve are the coordinates
of its derivative. -/
lemma gp4_deriv_coord {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (θ : ℝ) :
    deriv (coordX L) θ = deriv L θ 0 ∧ deriv (coordY L) θ = deriv L θ 1 ∧
      deriv (coordZ L) θ = deriv L θ 2 := by
  have hd : HasDerivAt L (deriv L θ) θ := (hL.differentiable (by simp) θ).hasDerivAt
  exact ⟨(ContactMotions.hasDerivAt_coord hd 0).deriv, (ContactMotions.hasDerivAt_coord hd 1).deriv,
    (ContactMotions.hasDerivAt_coord hd 2).deriv⟩

/-- P4 helper: `z′ = y x′` along a smooth Legendrian curve. -/
lemma gp4_deriv_z {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) (hLeg : IsLegendrian L) (θ : ℝ) :
    deriv (coordZ L) θ = coordY L θ * deriv (coordX L) θ := by
  obtain ⟨hx, -, hz⟩ := gp4_deriv_coord hL θ
  have h := hLeg θ
  unfold alpha at h
  rw [hx, hz]; unfold coordY; linarith

/-- LEAF P4.1.  Every double point of a `Stage2` front is transverse: both parameters regular
(`NoCuspOnBranch`), `y(θ) ≠ y(η)` (embeddedness), determinant `x′(θ)x′(η)(y(η) − y(θ)) ≠ 0`
from `z′ = y x′`. -/
theorem transverse_double_of_stage2 {L : ℝ → ℝ³} (h : Stage2 L) :
    ∀ p ∈ doublePoints L, IsTransverseDouble L p.1 p.2 := by
  rintro ⟨θ, η⟩ ⟨hne, hfr⟩
  simp only at hne hfr ⊢
  have hsm := h.circle.smooth
  have hxθ : deriv (coordX L) θ ≠ 0 := fun h0 => h.noCuspOnBranch θ h0 η hne hfr.symm
  have hxη : deriv (coordX L) η ≠ 0 := fun h0 =>
    h.noCuspOnBranch η h0 θ (fun hs => hne (gp3_sameParam_symm hs)) hfr
  have hy : coordY L η - coordY L θ ≠ 0 := by
    intro h0
    apply hne
    have hLeq : L θ = L η := by
      ext i
      fin_cases i
      · show L θ 0 = L η 0
        exact congrArg Prod.fst hfr
      · show L θ 1 = L η 1
        unfold coordY at h0; linarith
      · show L θ 2 = L η 2
        exact congrArg Prod.snd hfr
    exact h.circle.injective θ η hLeq
  unfold IsTransverseDouble
  rw [gp4_deriv_z hsm h.legendrian θ, gp4_deriv_z hsm h.legendrian η]
  have e : deriv (coordX L) θ * (coordY L η * deriv (coordX L) η) -
      coordY L θ * deriv (coordX L) θ * deriv (coordX L) η =
      deriv (coordX L) θ * deriv (coordX L) η * (coordY L η - coordY L θ) := by ring
  rw [e]
  exact mul_ne_zero (mul_ne_zero hxθ hxη) hy

/-- P4 helper: the circular distance is at most `|θ − η − 2πk|` for every integer `k`. -/
lemma gp4_circDist_le (θ η : ℝ) (k : ℤ) : circDist θ η ≤ |θ - η - 2 * π * k| := by
  unfold circDist
  have hpi : (0:ℝ) < 2 * π := by positivity
  have h := round_le ((θ - η) / (2 * π)) k
  have e1 : θ - η - 2 * π * round ((θ - η) / (2 * π)) =
      2 * π * ((θ - η) / (2 * π) - round ((θ - η) / (2 * π))) := by
    field_simp
  have e2 : θ - η - 2 * π * k = 2 * π * ((θ - η) / (2 * π) - k) := by field_simp
  rw [e1, e2, abs_mul (2 * π), abs_mul (2 * π), abs_of_pos hpi]
  exact mul_le_mul_of_nonneg_left h hpi.le

/-- P4 helper: the front-difference map `G(θ,η) = (x(θ) − x(η), z(θ) − z(η))`. -/
def gp4_G (L : ℝ → ℝ³) (p : ℝ × ℝ) : ℝ × ℝ :=
  (coordX L p.1 - coordX L p.2, coordZ L p.1 - coordZ L p.2)

lemma gp4_front_eq_iff (L : ℝ → ℝ³) (θ η : ℝ) : front L θ = front L η ↔ gp4_G L (θ, η) = 0 := by
  simp only [gp4_G, front, coordX, coordZ, Prod.mk_eq_zero, sub_eq_zero, Prod.mk.injEq]

/-- P4 helper: the derivative of `gp4_G` at a transverse double point is injective, so `G` is
injective near the point (inverse function theorem). -/
lemma gp4_G_injOn_nhds {L : ℝ → ℝ³} (hL : ContDiff ℝ ∞ L) {θ₀ η₀ : ℝ}
    (htr : IsTransverseDouble L θ₀ η₀) :
    ∃ U ∈ 𝓝 (θ₀, η₀), InjOn (gp4_G L) U := by
  have hcx : ContDiff ℝ ∞ (coordX L) := (ContactMotions.contDiff_coord 0).comp hL
  have hcz : ContDiff ℝ ∞ (coordZ L) := (ContactMotions.contDiff_coord 2).comp hL
  have hxθ : HasStrictDerivAt (coordX L) (deriv (coordX L) θ₀) θ₀ := hcx.hasStrictDerivAt (by simp)
  have hxη : HasStrictDerivAt (coordX L) (deriv (coordX L) η₀) η₀ := hcx.hasStrictDerivAt (by simp)
  have hzθ : HasStrictDerivAt (coordZ L) (deriv (coordZ L) θ₀) θ₀ := hcz.hasStrictDerivAt (by simp)
  have hzη : HasStrictDerivAt (coordZ L) (deriv (coordZ L) η₀) η₀ := hcz.hasStrictDerivAt (by simp)
  set xθ := deriv (coordX L) θ₀
  set xη := deriv (coordX L) η₀
  set zθ := deriv (coordZ L) θ₀
  set zη := deriv (coordZ L) η₀
  let A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (xθ • ContinuousLinearMap.fst ℝ ℝ ℝ - xη • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (zθ • ContinuousLinearMap.fst ℝ ℝ ℝ - zη • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hGA : HasStrictFDerivAt (gp4_G L) A (θ₀, η₀) := by
    have hf : HasStrictFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) (θ₀, η₀) :=
      hasStrictFDerivAt_fst
    have hs : HasStrictFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) (θ₀, η₀) :=
      hasStrictFDerivAt_snd
    have h1 : HasStrictFDerivAt (coordX L ∘ (Prod.fst : ℝ × ℝ → ℝ))
        (xθ • ContinuousLinearMap.fst ℝ ℝ ℝ) (θ₀, η₀) := hxθ.comp_hasStrictFDerivAt (θ₀, η₀) hf
    have h2 : HasStrictFDerivAt (coordX L ∘ (Prod.snd : ℝ × ℝ → ℝ))
        (xη • ContinuousLinearMap.snd ℝ ℝ ℝ) (θ₀, η₀) := hxη.comp_hasStrictFDerivAt (θ₀, η₀) hs
    have h3 : HasStrictFDerivAt (coordZ L ∘ (Prod.fst : ℝ × ℝ → ℝ))
        (zθ • ContinuousLinearMap.fst ℝ ℝ ℝ) (θ₀, η₀) := hzθ.comp_hasStrictFDerivAt (θ₀, η₀) hf
    have h4 : HasStrictFDerivAt (coordZ L ∘ (Prod.snd : ℝ × ℝ → ℝ))
        (zη • ContinuousLinearMap.snd ℝ ℝ ℝ) (θ₀, η₀) := hzη.comp_hasStrictFDerivAt (θ₀, η₀) hs
    exact (h1.sub h2).prodMk (h3.sub h4)
  have hA : ∀ w : ℝ × ℝ, A w = (xθ * w.1 - xη * w.2, zθ * w.1 - zη * w.2) := by
    intro w
    simp [A]
  have hAinj : Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun w hw => ?_
    rw [hA, Prod.mk_eq_zero] at hw
    obtain ⟨h1, h2⟩ := hw
    have hdet : xθ * zη - zθ * xη ≠ 0 := htr
    have hu : (xθ * zη - zθ * xη) * w.1 = 0 := by linear_combination zη * h1 - xη * h2
    have hv : (xθ * zη - zθ * xη) * w.2 = 0 := by linear_combination zθ * h1 - xθ * h2
    exact Prod.ext ((mul_eq_zero.1 hu).resolve_left hdet) ((mul_eq_zero.1 hv).resolve_left hdet)
  have hAbij : Bijective A :=
    ⟨hAinj, LinearMap.injective_iff_surjective (f := (A : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))).1 hAinj⟩
  let E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    (LinearEquiv.ofBijective (A : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) hAbij).toContinuousLinearEquiv
  have hEA : (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = A := by
    refine ContinuousLinearMap.ext fun w => ?_
    simp [E]
  have hGE : HasStrictFDerivAt (gp4_G L) (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (θ₀, η₀) := by
    rw [hEA]; exact hGA
  refine ⟨(hGE.toOpenPartialHomeomorph (gp4_G L)).source,
    (hGE.toOpenPartialHomeomorph (gp4_G L)).open_source.mem_nhds
      hGE.mem_toOpenPartialHomeomorph_source, ?_⟩
  have := (hGE.toOpenPartialHomeomorph (gp4_G L)).injOn
  rwa [hGE.toOpenPartialHomeomorph_coe] at this

/-- LEAF P4.2.  Transverse double points are isolated (IFT on `(θ,η) ↦ p(θ) − p(η)`), the pairs at
circular distance `≥ δc` form a compact set, so there are finitely many in one period square. -/
theorem finite_double_of_stage2 {L : ℝ → ℝ³} (h : Stage2 L)
    (ht : ∀ p ∈ doublePoints L, IsTransverseDouble L p.1 p.2) :
    (doublePoints L ∩ Ico 0 (2 * π) ×ˢ Ico 0 (2 * π)).Finite := by
  obtain ⟨δc, hδpos, hδ⟩ := h.collar
  by_contra hinf
  set S := doublePoints L ∩ Ico 0 (2 * π) ×ˢ Ico 0 (2 * π) with hS
  have hK : IsCompact (Icc (0:ℝ) (2 * π) ×ˢ Icc (0:ℝ) (2 * π)) := isCompact_Icc.prod isCompact_Icc
  have hsub : S ⊆ Icc (0:ℝ) (2 * π) ×ˢ Icc (0:ℝ) (2 * π) := fun p hp =>
    ⟨Ico_subset_Icc_self hp.2.1, Ico_subset_Icc_self hp.2.2⟩
  obtain ⟨⟨θ₀, η₀⟩, -, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hK hsub
  have hcx : ContDiff ℝ ∞ (coordX L) := (ContactMotions.contDiff_coord 0).comp h.circle.smooth
  have hcz : ContDiff ℝ ∞ (coordZ L) := (ContactMotions.contDiff_coord 2).comp h.circle.smooth
  have hGcont : Continuous (gp4_G L) := by
    have h1 := hcx.continuous
    have h2 := hcz.continuous
    unfold gp4_G
    fun_prop
  have hGS : ∀ p ∈ S, gp4_G L p = 0 := fun p hp => (gp4_front_eq_iff L p.1 p.2).1 hp.1.2
  have hG0 : gp4_G L (θ₀, η₀) = 0 := by
    have hcl : (θ₀, η₀) ∈ closure S := mem_closure_iff_clusterPt.2 hacc.clusterPt
    exact ((isClosed_eq hGcont continuous_const).closure_subset_iff.2 hGS) hcl
  have hfr : front L θ₀ = front L η₀ := (gp4_front_eq_iff L θ₀ η₀).2 hG0
  by_cases hsp : SameParam θ₀ η₀
  · -- the limit pair is a diagonal pair: nearby pairs are within the collar, so none is a double
    -- point
    obtain ⟨k, hk⟩ := hsp
    obtain ⟨⟨θ, η⟩, ⟨hU, hpS⟩, -⟩ := accPt_iff_nhds.1 hacc (Metric.ball (θ₀, η₀) (δc / 2))
      (Metric.ball_mem_nhds _ (by linarith))
    have hd := Metric.mem_ball.1 hU
    rw [Prod.dist_eq] at hd
    have hθ : |θ - θ₀| < δc / 2 := by
      have := (le_max_left _ _).trans_lt hd
      rwa [Real.dist_eq] at this
    have hη : |η - η₀| < δc / 2 := by
      have := (le_max_right _ _).trans_lt hd
      rwa [Real.dist_eq] at this
    have hcd : circDist θ η < δc := by
      calc circDist θ η ≤ |θ - η - 2 * π * ((-k : ℤ) : ℝ)| := gp4_circDist_le θ η (-k)
        _ = |(θ - θ₀) - (η - η₀)| := by congr 1; push_cast; linarith
        _ ≤ |θ - θ₀| + |η - η₀| := abs_sub _ _
        _ < δc := by linarith
    exact hδ θ η hcd hpS.1.1 hpS.1.2
  · -- the limit pair is a transverse double point: `G` is injective near it, so it is isolated
    have htr : IsTransverseDouble L θ₀ η₀ := ht (θ₀, η₀) ⟨hsp, hfr⟩
    obtain ⟨U, hU, hinj⟩ := gp4_G_injOn_nhds h.circle.smooth htr
    obtain ⟨p, ⟨hpU, hpS⟩, hpne⟩ := accPt_iff_nhds.1 hacc U hU
    exact hpne (hinj hpU (mem_of_mem_nhds hU) (by rw [hGS p hpS, hG0]))

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
  have hfper := gp2_periodic_front hper
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
  have hfper := gp2_periodic_front hper
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
      refine (gp2_circDist_le_abs _ _).trans_lt ?_
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
  have hfper := gp2_periodic_front hper
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
    exact hq (gp3_hamVF_eq_zero_of_notMem fun h => hnot ((hHc θc hθc).2.2.2.2.1 h))
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
    apply gp3_hamVF_eq_zero_of_notMem
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

/-- A stage `Φ s`, `s ∈ [0,1]`, of a compactly supported ambient isotopy is smooth. -/
lemma gp6_contDiff_stage {Φ : ℝ → ℝ³ → ℝ³} (hΦ : IsCompactlySupportedAmbientIsotopy Φ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : ContDiff ℝ ∞ (Φ s) := by
  have h1 : ContDiffOn ℝ ∞ (uncurry Φ ∘ fun p : ℝ³ => (s, p)) univ :=
    hΦ.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun p _ => ⟨hs, mem_univ _⟩)
  exact contDiffOn_univ.1 h1

/-- The left branch `(s, p) ↦ Φ (τ(2s)) p` of the concatenation is smooth on all of `ℝ × ℝ³`. -/
lemma gp6_contDiff_concat_left {Φ : ℝ → ℝ³ → ℝ³} (hΦ : IsCompactlySupportedAmbientIsotopy Φ) :
    ContDiff ℝ ∞ fun q : ℝ × ℝ³ => Φ (Real.smoothTransition (2 * q.1)) q.2 := by
  have hg : ContDiff ℝ ∞ fun q : ℝ × ℝ³ => (Real.smoothTransition (2 * q.1), q.2) :=
    (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have h1 : ContDiffOn ℝ ∞
      (uncurry Φ ∘ fun q : ℝ × ℝ³ => (Real.smoothTransition (2 * q.1), q.2)) univ :=
    hΦ.smooth.comp hg.contDiffOn
      (fun q _ => ⟨⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, mem_univ _⟩)
  exact contDiffOn_univ.1 h1

/-- The right branch `(s, p) ↦ Ψ (τ(2s − 1)) (Φ 1 p)` is smooth on all of `ℝ × ℝ³`. -/
lemma gp6_contDiff_concat_right {Φ Ψ : ℝ → ℝ³ → ℝ³} (hΦ : IsCompactlySupportedAmbientIsotopy Φ)
    (hΨ : IsCompactlySupportedAmbientIsotopy Ψ) :
    ContDiff ℝ ∞ fun q : ℝ × ℝ³ => Ψ (Real.smoothTransition (2 * q.1 - 1)) (Φ 1 q.2) := by
  have hΦ1 : ContDiff ℝ ∞ (Φ 1) := gp6_contDiff_stage hΦ ⟨zero_le_one, le_rfl⟩
  have hg : ContDiff ℝ ∞ fun q : ℝ × ℝ³ => (Real.smoothTransition (2 * q.1 - 1), Φ 1 q.2) :=
    (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_fst).sub contDiff_const)).prodMk (hΦ1.comp contDiff_snd)
  have h1 : ContDiffOn ℝ ∞
      (uncurry Ψ ∘ fun q : ℝ × ℝ³ => (Real.smoothTransition (2 * q.1 - 1), Φ 1 q.2)) univ :=
    hΨ.smooth.comp hg.contDiffOn
      (fun q _ => ⟨⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, mem_univ _⟩)
  exact contDiffOn_univ.1 h1

/-- The concatenation is the globally smooth function `A + C − Φ₁`: the left branch `A` is
constantly `Φ 1` for `s ≥ ½` (`τ(2s) = 1`) and the right branch `C` is constantly `Φ 1` for
`s ≤ ½` (`τ(2s − 1) = 0`, `Ψ 0 = id`).  No gluing lemma is needed. -/
lemma gp6_uncurry_concat_eq {Φ Ψ : ℝ → ℝ³ → ℝ³} (hΨ : IsCompactlySupportedAmbientIsotopy Ψ) :
    uncurry (concat Φ Ψ) = fun q : ℝ × ℝ³ =>
      Φ (Real.smoothTransition (2 * q.1)) q.2 + Ψ (Real.smoothTransition (2 * q.1 - 1)) (Φ 1 q.2)
        - Φ 1 q.2 := by
  funext ⟨s, p⟩
  show concat Φ Ψ s p = _
  unfold concat
  split_ifs with h
  · have : Real.smoothTransition (2 * s - 1) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [this, hΨ.zero, add_sub_cancel_right]
  · have : Real.smoothTransition (2 * s) = 1 := Real.smoothTransition.one_of_one_le (by linarith)
    rw [this, add_sub_cancel_left]

/-- On `s ≤ ½` the concatenation is the left branch. -/
lemma gp6_concat_of_le (Φ Ψ : ℝ → ℝ³ → ℝ³) {s : ℝ} (hs : s ≤ 1 / 2) :
    concat Φ Ψ s = Φ (Real.smoothTransition (2 * s)) :=
  funext fun p => by simp only [concat, ite_eq_left hs]

/-- On `s > ½` the concatenation is the right branch. -/
lemma gp6_concat_of_not_le (Φ Ψ : ℝ → ℝ³ → ℝ³) {s : ℝ} (hs : ¬ s ≤ 1 / 2) :
    concat Φ Ψ s = Ψ (Real.smoothTransition (2 * s - 1)) ∘ Φ 1 :=
  funext fun p => by simp only [concat, ite_eq_right hs, comp_apply]

/-- LEAF P6.1.  The concatenation of two contact isotopies is a contact isotopy (flatness of
`smoothTransition` at `0` and `1` gives joint smoothness across the join). -/
theorem isContactIsotopy_concat {Φ Ψ : ℝ → ℝ³ → ℝ³} (hΦ : IsContactIsotopy Φ)
    (hΨ : IsContactIsotopy Ψ) : IsContactIsotopy (concat Φ Ψ) := by
  have hτ : ∀ x : ℝ, Real.smoothTransition x ∈ Icc (0 : ℝ) 1 := fun x =>
    ⟨Real.smoothTransition.nonneg x, Real.smoothTransition.le_one x⟩
  have h01 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hΦ1 : ContDiff ℝ ∞ (Φ 1) := gp6_contDiff_stage hΦ.ambient h01
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- joint smoothness
    rw [gp6_uncurry_concat_eq hΨ.ambient]
    exact (((gp6_contDiff_concat_left hΦ.ambient).add
      (gp6_contDiff_concat_right hΦ.ambient hΨ.ambient)).sub (hΦ1.comp contDiff_snd)).contDiffOn
  · -- `concat Φ Ψ 0 = id`
    intro p
    rw [gp6_concat_of_le Φ Ψ (by norm_num), mul_zero, Real.smoothTransition.zero, hΦ.ambient.zero]
  · -- diffeomorphisms
    intro t _
    by_cases h : t ≤ 1 / 2
    · rw [gp6_concat_of_le Φ Ψ h]
      exact hΦ.ambient.diffeo _ (hτ _)
    · rw [gp6_concat_of_not_le Φ Ψ h]
      obtain ⟨Φinv, hΦinv, hl1, hr1⟩ := hΦ.ambient.diffeo 1 h01
      obtain ⟨Ψinv, hΨinv, hl2, hr2⟩ := hΨ.ambient.diffeo _ (hτ (2 * t - 1))
      exact ⟨Φinv ∘ Ψinv, hΦinv.comp hΨinv, hl2.comp hl1, hr2.comp hr1⟩
  · -- compact support
    obtain ⟨K₁, hK₁, hfix₁⟩ := hΦ.ambient.support
    obtain ⟨K₂, hK₂, hfix₂⟩ := hΨ.ambient.support
    refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun t _ p hp => ?_⟩
    have hp₁ : p ∉ K₁ := fun h => hp (Or.inl h)
    have hp₂ : p ∉ K₂ := fun h => hp (Or.inr h)
    by_cases h : t ≤ 1 / 2
    · rw [gp6_concat_of_le Φ Ψ h]
      exact hfix₁ _ (hτ _) p hp₁
    · rw [gp6_concat_of_not_le Φ Ψ h, comp_apply, hfix₁ 1 h01 p hp₁]
      exact hfix₂ _ (hτ _) p hp₂
  · -- contact, with the product of the conformal factors
    intro s _ p
    by_cases h : s ≤ 1 / 2
    · rw [gp6_concat_of_le Φ Ψ h]
      exact hΦ.contact _ (hτ _) p
    · rw [gp6_concat_of_not_le Φ Ψ h]
      have hΨt : ContDiff ℝ ∞ (Ψ (Real.smoothTransition (2 * s - 1))) :=
        gp6_contDiff_stage hΨ.ambient (hτ _)
      obtain ⟨c₁, hc₁, hc₁v⟩ := hΦ.contact 1 h01 p
      obtain ⟨c₂, hc₂, hc₂v⟩ := hΨ.contact _ (hτ (2 * s - 1)) (Φ 1 p)
      refine ⟨c₂ * c₁, mul_pos hc₂ hc₁, fun v => ?_⟩
      rw [fderiv_comp p (hΨt.differentiable (by simp) _) (hΦ1.differentiable (by simp) p),
        ContinuousLinearMap.comp_apply, comp_apply, hc₂v, hc₁v]
      ring

/-- A stage is injective (it has a left inverse). -/
lemma gp6_injective_stage {Φ : ℝ → ℝ³ → ℝ³} (hΦ : IsCompactlySupportedAmbientIsotopy Φ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : Injective (Φ s) := by
  obtain ⟨Ψ, -, hl, -⟩ := hΦ.diffeo s hs
  exact hl.injective

/-- `DΦ_s(p)` is injective: `DΨ(Φ_s p) ∘ DΦ_s(p) = id` for the smooth inverse `Ψ`. -/
lemma gp6_fderiv_stage_injective {Φ : ℝ → ℝ³ → ℝ³} (hΦ : IsCompactlySupportedAmbientIsotopy Φ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (p : ℝ³) : Injective (fderiv ℝ (Φ s) p) := by
  obtain ⟨Ψ, hΨ, hl, -⟩ := hΦ.diffeo s hs
  have hΦs := gp6_contDiff_stage hΦ hs
  have hid : Ψ ∘ Φ s = id := funext hl
  have h1 := fderiv_comp p (hΨ.differentiable (by simp) (Φ s p)) (hΦs.differentiable (by simp) p)
  rw [hid, fderiv_id] at h1
  have hli : LeftInverse (fderiv ℝ Ψ (Φ s p)) (fderiv ℝ (Φ s) p) := fun v => by
    have := congrArg (fun T : ℝ³ →L[ℝ] ℝ³ => T v) h1
    simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at this
    exact this.symm
  exact hli.injective

/-- The derivative of the image curve `Φ_s ∘ γ`. -/
lemma gp6_hasDerivAt_stage_comp {Φ : ℝ → ℝ³ → ℝ³} (hΦ : IsCompactlySupportedAmbientIsotopy Φ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {γ : ℝ → ℝ³} {γ' : ℝ³} {θ : ℝ} (hγ : HasDerivAt γ γ' θ) :
    HasDerivAt (fun θ => Φ s (γ θ)) (fderiv ℝ (Φ s) (γ θ) γ') θ :=
  ((gp6_contDiff_stage hΦ hs).differentiable (by simp) (γ θ)).hasFDerivAt.comp_hasDerivAt θ hγ

/-- A stage of a contact isotopy carries positive transverse curves to positive transverse curves:
`α((Φ_s∘K)′) = (c_s∘K) α(K′) > 0` (sm-3:2776-2779). -/
lemma gp6_isPositiveTransverse_stage {Φ : ℝ → ℝ³ → ℝ³} (hΦ : IsContactIsotopy Φ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) {K : ℝ → ℝ³} (hK : ContDiff ℝ ∞ K) (hKt : IsPositiveTransverse K) :
    IsPositiveTransverse fun θ => Φ s (K θ) := by
  intro θ
  show 0 < alpha (Φ s (K θ)) (deriv (fun θ => Φ s (K θ)) θ)
  rw [(gp6_hasDerivAt_stage_comp hΦ.ambient hs (hK.differentiable (by simp) θ).hasDerivAt).deriv]
  obtain ⟨c, hc, hcv⟩ := hΦ.contact s hs (K θ)
  rw [hcv]
  exact mul_pos hc (hKt θ)

/-- The circle `θ ↦ B (θ, s₀)` of an annulus is smooth. -/
lemma gp6_contDiff_annulus_circle {L : ℝ → ℝ³} {ε b : ℝ} {B : ℝ × ℝ → ℝ³}
    (hB : IsPushoffAnnulus L ε b B) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (-ε) b) :
    ContDiff ℝ ∞ fun θ => B (θ, s₀) := by
  have h1 : ContDiffOn ℝ ∞ (B ∘ fun θ : ℝ => (θ, s₀)) univ :=
    hB.smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun θ _ => ⟨mem_univ _, hs₀⟩)
  exact contDiffOn_univ.1 h1

/-- `B` is differentiable at every point of its open domain. -/
lemma gp6_differentiableAt_annulus {L : ℝ → ℝ³} {ε b : ℝ} {B : ℝ × ℝ → ℝ³}
    (hB : IsPushoffAnnulus L ε b B) {θ s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (-ε) b) :
    DifferentiableAt ℝ B (θ, s₀) :=
  (hB.smooth.differentiableOn (by simp)).differentiableAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hs₀⟩)

/-- LEAF P6.2.  A stage of a contact isotopy carries a pushoff annulus of `L` to a pushoff annulus
of `Φ_s ∘ L` (sm-3:2773-2778: diffeomorphism + `Φ_s^*α = c_s α`, `c_s > 0`). -/
theorem pushoffAnnulus_map {Φ : ℝ → ℝ³ → ℝ³} (hΦ : IsContactIsotopy Φ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) {L : ℝ → ℝ³} {ε b : ℝ} {B : ℝ × ℝ → ℝ³} (hB : IsPushoffAnnulus L ε b B) :
    IsPushoffAnnulus (Φ s ∘ L) ε b fun q => Φ s (B q) := by
  have hΦs := gp6_contDiff_stage hΦ.ambient hs
  have hfd : ∀ θ s', s' ∈ Ioo (-ε) b → fderiv ℝ (fun q => Φ s (B q)) (θ, s') =
      (fderiv ℝ (Φ s) (B (θ, s'))).comp (fderiv ℝ B (θ, s')) := fun θ s' hs' =>
    fderiv_comp (θ, s') (hΦs.differentiable (by simp) _) (gp6_differentiableAt_annulus hB hs')
  refine ⟨hB.eps_pos, hB.b_pos, hΦs.comp_contDiffOn hB.smooth, fun θ s' => ?_, fun θ => ?_,
    fun θ s' θ' s'' hs' hs'' h => ?_, fun θ s' hs' => ?_, fun θ s' hs' => ?_,
    fun s' hs'0 hs'b => ?_⟩
  · show Φ s (B (θ + 2 * π, s')) = Φ s (B (θ, s'))
    rw [hB.periodic]
  · show Φ s (B (θ, 0)) = Φ s (L θ)
    rw [hB.core]
  · exact hB.injective θ s' θ' s'' hs' hs'' (gp6_injective_stage hΦ.ambient hs h)
  · rw [hfd θ s' hs']
    intro v w hvw
    exact hB.immersion θ s' hs' (gp6_fderiv_stage_injective hΦ.ambient hs _ hvw)
  · rw [hfd θ s' hs']
    obtain ⟨c, hc, hcv⟩ := hΦ.contact s hs (B (θ, s'))
    simp only [ContinuousLinearMap.comp_apply, hcv]
    rcases hB.transverse θ s' hs' with h | h
    · exact Or.inl (mul_ne_zero hc.ne' h)
    · exact Or.inr (mul_ne_zero hc.ne' h)
  · have hs' : s' ∈ Ioo (-ε) b := ⟨by linarith [hB.eps_pos], hs'b⟩
    exact gp6_isPositiveTransverse_stage hΦ hs (gp6_contDiff_annulus_circle hB hs')
      (hB.positive s' hs'0 hs'b)

/-- A stage of an ambient isotopy carries embedded circles to embedded circles. -/
lemma gp6_isEmbeddedCircle_stage {Φ : ℝ → ℝ³ → ℝ³} (hΦ : IsCompactlySupportedAmbientIsotopy Φ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {K : ℝ → ℝ³} (hK : IsEmbeddedCircle K) :
    IsEmbeddedCircle fun θ => Φ s (K θ) where
  smooth := (gp6_contDiff_stage hΦ hs).comp hK.smooth
  periodic := fun θ => by
    show Φ s (K (θ + 2 * π)) = Φ s (K θ)
    rw [hK.periodic θ]
  injective := fun θ θ' h => hK.injective θ θ' (gp6_injective_stage hΦ hs h)
  immersion := fun θ => by
    rw [(gp6_hasDerivAt_stage_comp hΦ hs (hK.smooth.differentiable (by simp) θ).hasDerivAt).deriv]
    intro h0
    exact hK.immersion θ (gp6_fderiv_stage_injective hΦ hs (K θ) (by rw [h0, map_zero]))

/-- LEAF P6.3.  A positive transverse embedded circle moves through positive transverse embedded
circles under a contact isotopy (sm-3:2776-2779: `α((Φ_s∘K)′) = (c_s∘K) α(K′) > 0`). -/
theorem transverselyIsotopic_contact {Φ : ℝ → ℝ³ → ℝ³} (hΦ : IsContactIsotopy Φ) {K : ℝ → ℝ³}
    (hK : IsEmbeddedCircle K) (hKt : IsPositiveTransverse K) :
    TransverselyIsotopic K fun θ => Φ 1 (K θ) := by
  refine ⟨fun s θ => Φ s (K θ), ?_, fun s hs => ⟨gp6_isEmbeddedCircle_stage hΦ.ambient hs hK,
    gp6_isPositiveTransverse_stage hΦ hs hK.smooth hKt⟩, ?_, id,
    ⟨contDiff_id, fun θ => ?_, fun θ => rfl⟩, ?_⟩
  · -- joint smoothness of `(s, θ) ↦ Φ s (K θ)`
    have h1 : ContDiffOn ℝ ∞ (uncurry Φ ∘ fun q : ℝ × ℝ => (q.1, K q.2)) (Icc 0 1 ×ˢ univ) :=
      hΦ.ambient.smooth.comp (contDiff_fst.prodMk (hK.smooth.comp contDiff_snd)).contDiffOn
        (fun q hq => ⟨hq.1, mem_univ _⟩)
    exact h1
  · funext θ
    exact hΦ.ambient.zero (K θ)
  · rw [deriv_id]
    exact one_pos
  · rfl

/-- The velocity of the circle `θ ↦ B (θ, s₀)` is `DB(θ,s₀)(1,0)`. -/
lemma gp6_hasDerivAt_annulus_circle {L : ℝ → ℝ³} {ε b : ℝ} {B : ℝ × ℝ → ℝ³}
    (hB : IsPushoffAnnulus L ε b B) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (-ε) b) (θ : ℝ) :
    HasDerivAt (fun θ => B (θ, s₀)) (fderiv ℝ B (θ, s₀) (1, 0)) θ :=
  (gp6_differentiableAt_annulus hB hs₀).hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_id θ).prodMk (hasDerivAt_const θ s₀))

/-- LEAF P6.4.  The circles `B(·, s₀)` of a pushoff annulus are embedded circles. -/
theorem IsPushoffAnnulus.circle {L : ℝ → ℝ³} {ε b : ℝ} {B : ℝ × ℝ → ℝ³} (hB : IsPushoffAnnulus L ε b B)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (-ε) b) : IsEmbeddedCircle fun θ => B (θ, s₀) := by
  refine ⟨gp6_contDiff_annulus_circle hB hs₀, fun θ => hB.periodic θ s₀,
    fun θ θ' h => (hB.injective θ s₀ θ' s₀ hs₀ hs₀ h).2, fun θ => ?_⟩
  rw [(gp6_hasDerivAt_annulus_circle hB hs₀ θ).deriv]
  intro h0
  have h1 : fderiv ℝ B (θ, s₀) (1, 0) = fderiv ℝ B (θ, s₀) 0 := by rw [h0, map_zero]
  have h2 := hB.immersion θ s₀ hs₀ h1
  exact one_ne_zero (congrArg Prod.fst h2)

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
