import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Smooth dependence of an ODE flow on the initial point (`SM.SmoothDependence`)

Drafted 2026-09-14 in work/drafts/fd/.  Proves the one hypothesis left open by
`ContactMotions.lean` (row 86 fd:contact-motions): for a `C^∞` compactly supported vector field
`X` on a finite-dimensional real normed space, every global flow `φ` of `X` is `C^∞` jointly in
`(s, p)`.  Mathlib (this pin) has existence, uniqueness, Grönwall and regularity in time only.
Check: `cd work/lean && lake env lean ../drafts/fd/SmoothDependence.lean`.

Nothing is imported from `work/drafts`; the definition `IsGlobalFlow` and the general flow lemmas
of `ContactMotions.lean` §2–3 are copied verbatim under the namespace `SM.SmoothDep` (same
statements, same proofs), so the executor can merge by replacing `SmoothDep.IsGlobalFlow` with
`ContactMotions.IsGlobalFlow`.  The final theorems are also stated structure-free
(`SM.smoothDependence_of_flow`), so `SM.SmoothDependence` follows in one line.

## Route

1. **Time reversal** `IsGlobalFlow.neg`: `(s, p) ↦ φ (-s) p` is a global flow of `-X`; every
   estimate is proved forward in time and reflected.
2. **Lipschitz dependence** `IsGlobalFlow.dist_le`: `dist (φ s p) (φ s q) ≤ dist p q · e^{K|s|}`
   (Grönwall, `dist_le_of_trajectories_ODE`).
3. **The variational estimate** `hasFDerivAt_flow_of_variational`: if `X` is differentiable with
   `‖DX‖ ≤ K` and `DX` uniformly continuous, and `D : ℝ → E →L E` solves the variational equation
   `D' = DX(φ t p) ∘ D`, `D 0 = 1` on `[0, T]`, then `φ T` has derivative `D T` at `p`.  Proof: the
   error `f t = φ t (p+h) − φ t p − D t h` satisfies `‖f'‖ ≤ K‖f‖ + η e^{KT}‖h‖` (mean value
   inequality `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` + uniform continuity of `DX`),
   `f 0 = 0`, so Grönwall (`norm_le_gronwallBound_of_norm_deriv_right_le`) gives
   `‖f T‖ ≤ η e^{KT} e^{(K+1)T} ‖h‖`, i.e. `o(‖h‖)`.
4. **The augmented system** on `F = E × (E →L E)`: `Y (x, A) = (X x, DX(x) ∘ A)`, cut off by a
   bump `b` in the `A`-variable (`augFieldCut`), is `C^∞` and compactly supported.  For its flow
   `Ψ`, the curve `t ↦ Ψ t (p, 1)` has second component bounded by `e^{Kt}` (Grönwall), so it
   stays where the cut-off is `1`; its first component is `φ t p` (forward uniqueness) and its
   second component solves the variational equation.  With (3), `fderiv (φ s) p = (Ψ s (p, 1)).2`.
5. **Induction on `k`** (`spaceSmooth`): `S k := ` "for every finite-dimensional `E`, every `C^∞`
   compactly supported `X`, every global flow `φ`, every `s`: `φ s ∈ C^k`".  `S 0` is (2);
   `S k → S (k+1)` applies `S k` to the augmented flow `Ψ` on `F` and uses
   `contDiff_succ_iff_fderiv`.  Hence `φ s ∈ C^∞` in space, for every `s`.
6. **Joint smoothness by suspension** (`contDiff_uncurry`): for the field
   `X̂ (τ, x) = (0, χ(τ) • X x)` on `ℝ × E`, `χ = b • id` a cut-off equal to `τ` on `[-R, R]`,
   `(s, (τ, x)) ↦ (τ, φ (χ τ · s) x)` is a global flow; its **time-one map** is `C^∞` in the
   space variable `(τ, x)` by (5), and equals `(τ, φ τ x)` for `|τ| < R`.  So `uncurry φ` is
   `C^∞` near every point.  No "continuous partials ⇒ jointly differentiable" lemma is needed.

Main results: `SM.SmoothDep.contDiff_uncurry` (any finite-dimensional `E : Type`),
`SM.smoothDependence_of_flow` / `SM.smoothDependence_of_isGlobalFlow` (for `ℝ³`, structure-free and
structured), which unfold `SM.SmoothDependence`. -/

namespace SM

namespace SmoothDep

open scoped ContDiff Topology NNReal
open Set Filter Function

noncomputable section

/-! ## 1. Global flows (copied from `ContactMotions.lean` §2) -/

section flows

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A global flow of the (autonomous) vector field `X`: `φ 0 = id` and
`∂_s φ s p = X (φ s p)` for all `s ∈ ℝ`, `p`.  (Verbatim `ContactMotions.IsGlobalFlow`.) -/
structure IsGlobalFlow (X : E → E) (φ : ℝ → E → E) : Prop where
  zero : ∀ p, φ 0 p = p
  hasDerivAt : ∀ s p, HasDerivAt (fun s => φ s p) (X (φ s p)) s

/-- Uniqueness of global solutions (backwards and forwards) for a globally Lipschitz field. -/
lemma ODE_unique_global {X : E → E} {K : ℝ≥0} (hK : LipschitzWith K X) {f g : ℝ → E}
    (hf : ∀ t, HasDerivAt f (X (f t)) t) (hg : ∀ t, HasDerivAt g (X (g t)) t) {t₀ : ℝ}
    (h : f t₀ = g t₀) : f = g :=
  ODE_solution_unique_univ (v := fun _ => X) (s := fun _ => univ) (K := K)
    (fun _ => hK.lipschitzOnWith) (fun t => ⟨hf t, trivial⟩) (fun t => ⟨hg t, trivial⟩) h

/-- Uniqueness on an open interval. -/
lemma ODE_unique_Ioo {X : E → E} {K : ℝ≥0} (hK : LipschitzWith K X) {f g : ℝ → E} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (hf : ∀ t ∈ Ioo a b, HasDerivAt f (X (f t)) t)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (X (g t)) t) (h : f t₀ = g t₀) : EqOn f g (Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo (v := fun _ => X) (s := fun _ => univ) (K := K)
    (fun _ _ => hK.lipschitzOnWith) ht₀ (fun t ht => ⟨hf t ht, trivial⟩)
    (fun t ht => ⟨hg t ht, trivial⟩) h

variable [CompleteSpace E]

/-- Existence on the symmetric interval `(−(n+1), n+1)` for every initial point. -/
lemma exists_solution_Ioo {X : E → E} {K L : ℝ≥0} (hK : LipschitzWith K X)
    (hL : ∀ p, ‖X p‖ ≤ L) (n : ℕ) (p : E) :
    ∃ γ : ℝ → E, γ 0 = p ∧ ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1), HasDerivAt γ (X (γ t)) t := by
  have hmem : (0 : ℝ) ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    constructor <;> linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hpl : IsPicardLindelof (fun _ : ℝ => X) (tmin := -((n : ℝ) + 1)) (tmax := (n : ℝ) + 1)
      ⟨0, hmem⟩ p (L * ((n : ℝ≥0) + 1)) 0 L K := by
    refine IsPicardLindelof.of_time_independent (fun x _ => hL x) hK.lipschitzOnWith ?_
    simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, sub_zero,
      zero_sub, neg_neg, max_self, NNReal.coe_zero]
    exact le_rfl
  obtain ⟨γ, hγ0, hγ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨γ, hγ0, fun t ht => ?_⟩
  exact (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- A global solution through every point (gluing by uniqueness). -/
lemma exists_solution_global {X : E → E} {K L : ℝ≥0} (hK : LipschitzWith K X)
    (hL : ∀ p, ‖X p‖ ≤ L) (p : E) :
    ∃ γ : ℝ → E, γ 0 = p ∧ ∀ t, HasDerivAt γ (X (γ t)) t := by
  choose α hα0 hα using exists_solution_Ioo hK hL (p := p)
  let γ : ℝ → E := fun t => α ⌈|t|⌉₊ t
  have key : ∀ (n : ℕ) (t : ℝ), |t| < (n : ℝ) + 1 → γ t = α n t := by
    intro n t ht
    have hm : |t| < (⌈|t|⌉₊ : ℝ) + 1 := by
      have := Nat.le_ceil |t|
      linarith
    set m := min ⌈|t|⌉₊ n with hm_def
    have hmem : t ∈ Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1) := by
      have h1 : |t| < (m : ℝ) + 1 := by
        rcases le_total ⌈|t|⌉₊ n with h | h
        · rw [hm_def, min_eq_left h]; exact hm
        · rw [hm_def, min_eq_right h]; exact ht
      rw [abs_lt] at h1
      exact ⟨by linarith [h1.1], h1.2⟩
    have h0 : (0 : ℝ) ∈ Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1) := by
      constructor <;> linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have hsub : ∀ k, m ≤ k → Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1) ⊆
        Ioo (-((k : ℝ) + 1)) ((k : ℝ) + 1) := by
      intro k hk
      have : (m : ℝ) ≤ k := by exact_mod_cast hk
      exact Ioo_subset_Ioo (by linarith) (by linarith)
    have := ODE_unique_Ioo hK h0 (f := α ⌈|t|⌉₊) (g := α n)
      (fun s hs => hα _ s (hsub _ (min_le_left _ _) hs))
      (fun s hs => hα _ s (hsub _ (min_le_right _ _) hs)) (by rw [hα0, hα0])
    exact this hmem
  refine ⟨γ, ?_, fun t => ?_⟩
  · have : γ 0 = α 0 0 := key 0 0 (by simp)
    rw [this, hα0]
  · set N := ⌈|t|⌉₊ with hN
    have hN' : |t| < (N : ℝ) + 1 := by
      have := Nat.le_ceil |t|
      linarith
    have hopen : {s : ℝ | |s| < (N : ℝ) + 1} ∈ 𝓝 t := by
      apply (isOpen_lt continuous_abs continuous_const).mem_nhds
      exact hN'
    have heq : γ =ᶠ[𝓝 t] α N := by
      filter_upwards [hopen] with s hs
      exact key N s hs
    have hd : HasDerivAt (α N) (X (α N t)) t := by
      apply hα N t
      rw [abs_lt] at hN'
      exact ⟨by linarith [hN'.1], hN'.2⟩
    have hγt : γ t = α N t := key N t hN'
    rw [← hγt] at hd
    exact hd.congr_of_eventuallyEq heq

/-- Existence of a global flow. -/
theorem exists_isGlobalFlow {X : E → E} {K L : ℝ≥0} (hK : LipschitzWith K X)
    (hL : ∀ p, ‖X p‖ ≤ L) : ∃ φ : ℝ → E → E, IsGlobalFlow X φ := by
  choose γ hγ0 hγ using exists_solution_global hK hL
  exact ⟨fun s p => γ p s, ⟨hγ0, fun s p => hγ p s⟩⟩

end flows

/-! ## 2. Time reversal and Lipschitz dependence on the initial point -/

namespace IsGlobalFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : E → E} {φ : ℝ → E → E}

theorem continuous_time (hφ : IsGlobalFlow X φ) (p : E) : Continuous fun s => φ s p :=
  continuous_iff_continuousAt.2 fun s => (hφ.hasDerivAt s p).continuousAt

/-- Time reversal: `(s, p) ↦ φ (-s) p` is a global flow of `-X`. -/
theorem neg (hφ : IsGlobalFlow X φ) : IsGlobalFlow (fun x => -X x) (fun s p => φ (-s) p) where
  zero p := by simp [hφ.zero]
  hasDerivAt s p := by
    have h := (hφ.hasDerivAt (-s) p).scomp s (hasDerivAt_neg s)
    simpa [Function.comp_def] using h

/-- Grönwall: `dist (φ s p) (φ s q) ≤ dist p q · e^{K s}` for `s ≥ 0`. -/
theorem dist_le_nonneg {K : ℝ≥0} (hK : LipschitzWith K X) (hφ : IsGlobalFlow X φ) {s : ℝ}
    (hs : 0 ≤ s) (p q : E) : dist (φ s p) (φ s q) ≤ dist p q * Real.exp (K * s) := by
  have h := dist_le_of_trajectories_ODE (v := fun _ => X) (fun _ => hK)
    (f := fun t => φ t p) (g := fun t => φ t q) (a := 0) (b := s) (δ := dist p q)
    (hφ.continuous_time p).continuousOn
    (fun t _ => (hφ.hasDerivAt t p).hasDerivWithinAt)
    (hφ.continuous_time q).continuousOn
    (fun t _ => (hφ.hasDerivAt t q).hasDerivWithinAt)
    (by simp [hφ.zero]) s ⟨hs, le_rfl⟩
  simpa using h

/-- Lipschitz dependence on the initial point: `dist (φ s p) (φ s q) ≤ dist p q · e^{K |s|}`. -/
theorem dist_le {K : ℝ≥0} (hK : LipschitzWith K X) (hφ : IsGlobalFlow X φ) (s : ℝ) (p q : E) :
    dist (φ s p) (φ s q) ≤ dist p q * Real.exp (K * |s|) := by
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs]; exact hφ.dist_le_nonneg hK hs p q
  · rw [abs_of_neg hs]
    have hK' : LipschitzWith K (fun x => -X x) := LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_neg_neg]; exact hK.dist_le_mul x y
    have := hφ.neg.dist_le_nonneg hK' (neg_nonneg.2 hs.le) p q
    simpa using this

theorem lipschitzWith_space {K : ℝ≥0} (hK : LipschitzWith K X) (hφ : IsGlobalFlow X φ) (s : ℝ) :
    LipschitzWith ⟨Real.exp (K * |s|), (Real.exp_pos _).le⟩ (φ s) :=
  LipschitzWith.of_dist_le_mul fun p q => by
    have := hφ.dist_le hK s p q
    rw [mul_comm] at this
    exact this

theorem continuous_space {K : ℝ≥0} (hK : LipschitzWith K X) (hφ : IsGlobalFlow X φ) (s : ℝ) :
    Continuous (φ s) :=
  (hφ.lipschitzWith_space hK s).continuous

end IsGlobalFlow

/-! ## 3. The variational estimate: differentiability in the initial point -/

section variational

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : E → E} {φ : ℝ → E → E}

/-- Grönwall's bound with `δ = 0` and constant `K + 1 > 0`. -/
lemma gronwallBound_zero_le {K ε T : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound 0 (K + 1) ε T ≤ ε * Real.exp ((K + 1) * T) := by
  have hK1 : (K + 1 : ℝ) ≠ 0 := by positivity
  rw [gronwallBound_of_K_ne_0 hK1]
  simp only [zero_mul, zero_add]
  have hexp := Real.exp_pos ((K + 1) * T)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hε hexp.le, mul_nonneg hε hK]

/-- **The variational estimate.**  Let `X` be differentiable with `‖DX‖ ≤ K` everywhere and `DX`
uniformly continuous, let `φ` be a global flow of `X`, `p ∈ E`, `T ≥ 0`, and let
`D : ℝ → E →L[ℝ] E` solve the variational equation `D' = DX(φ t p) ∘ D`, `D 0 = 1`, on `[0, T]`.
Then `φ T` is differentiable at `p` with derivative `D T`. -/
theorem hasFDerivAt_flow_of_variational {K : ℝ≥0} (hX : Differentiable ℝ X)
    (hK : ∀ x, ‖fderiv ℝ X x‖₊ ≤ K) (hU : UniformContinuous (fderiv ℝ X))
    (hφ : IsGlobalFlow X φ) {T : ℝ} (hT : 0 ≤ T) (p : E) {D : ℝ → E →L[ℝ] E} (hD0 : D 0 = 1)
    (hD : ∀ t ∈ Icc 0 T, HasDerivAt D ((fderiv ℝ X (φ t p)).comp (D t)) t) :
    HasFDerivAt (φ T) (D T) p := by
  have hLip : LipschitzWith K X := lipschitzWith_of_nnnorm_fderiv_le hX hK
  have hK' : ∀ x, ‖fderiv ℝ X x‖ ≤ K := fun x => by exact_mod_cast hK x
  have hC₁ : 0 < Real.exp (K * T) := Real.exp_pos _
  have hC₂ : 0 < Real.exp ((K + 1) * T) := Real.exp_pos _
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  -- the modulus `η` with `η * e^{KT} * e^{(K+1)T} = c`
  obtain ⟨η, hηpos, hηc⟩ : ∃ η : ℝ, 0 < η ∧
      η * Real.exp (K * T) * Real.exp ((K + 1) * T) = c :=
    ⟨c / (Real.exp (K * T) * Real.exp ((K + 1) * T)), by positivity, by field_simp⟩
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.1 hU η hηpos
  have hev : ∀ᶠ h : E in 𝓝 0, ‖h‖ < δ / Real.exp (K * T) := by
    have : Metric.ball (0 : E) (δ / Real.exp (K * T)) ∈ 𝓝 (0 : E) :=
      Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [this] with h hh
    simpa using hh
  filter_upwards [hev] with h hh
  show ‖φ T (p + h) - φ T p - D T h‖ ≤ c * ‖h‖
  -- the derivative of the error curve `f t = φ t (p + h) - φ t p - D t h`
  have hf' : ∀ t ∈ Icc 0 T, HasDerivAt (fun t => φ t (p + h) - φ t p - D t h)
      (X (φ t (p + h)) - X (φ t p) - fderiv ℝ X (φ t p) (D t h)) t := by
    intro t ht
    have h1 := (hφ.hasDerivAt t (p + h)).sub (hφ.hasDerivAt t p)
    have h2 := (hD t ht).clm_apply (hasDerivAt_const t h)
    have h3 : HasDerivAt (fun t => φ t (p + h) - φ t p - D t h)
        (X (φ t (p + h)) - X (φ t p) - ((fderiv ℝ X (φ t p)).comp (D t) h + D t 0)) t :=
      h1.sub h2
    simpa using h3
  -- Lipschitz bound on the displacement
  have hu : ∀ t ∈ Icc 0 T, ‖φ t (p + h) - φ t p‖ ≤ ‖h‖ * Real.exp (K * T) := by
    intro t ht
    have := hφ.dist_le_nonneg hLip ht.1 (p + h) p
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at this
    refine this.trans ?_
    gcongr
    exact ht.2
  have hu' : ∀ t ∈ Icc 0 T, ‖φ t (p + h) - φ t p‖ < δ := by
    intro t ht
    refine (hu t ht).trans_lt ?_
    rwa [lt_div_iff₀ hC₁] at hh
  -- the key bound on the derivative of the error
  have hbound : ∀ t ∈ Ico 0 T,
      ‖X (φ t (p + h)) - X (φ t p) - fderiv ℝ X (φ t p) (D t h)‖
        ≤ (K + 1) * ‖φ t (p + h) - φ t p - D t h‖ + η * Real.exp (K * T) * ‖h‖ := by
    intro t ht
    have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
    -- mean value inequality on the closed ball around `φ t p`
    have hmv : ‖X (φ t (p + h)) - X (φ t p) - fderiv ℝ X (φ t p) (φ t (p + h) - φ t p)‖
        ≤ η * ‖φ t (p + h) - φ t p‖ := by
      have := (convex_closedBall (φ t p) ‖φ t (p + h) - φ t p‖).norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (f := X) (f' := fderiv ℝ X) (φ := fderiv ℝ X (φ t p)) (C := η)
        (x := φ t p) (y := φ t (p + h))
        (fun z _ => (hX z).hasFDerivAt.hasFDerivWithinAt)
        (fun z hz => by
          rw [← dist_eq_norm]
          exact (hδ' (lt_of_le_of_lt (Metric.mem_closedBall.1 hz) (hu' t ht'))).le)
        (Metric.mem_closedBall_self (norm_nonneg _))
        (by rw [Metric.mem_closedBall, dist_eq_norm])
      exact this
    have key : X (φ t (p + h)) - X (φ t p) - fderiv ℝ X (φ t p) (D t h) =
        (X (φ t (p + h)) - X (φ t p) - fderiv ℝ X (φ t p) (φ t (p + h) - φ t p))
          + fderiv ℝ X (φ t p) (φ t (p + h) - φ t p - D t h) := by
      simp only [map_sub]; abel
    rw [key]
    calc ‖(X (φ t (p + h)) - X (φ t p) - fderiv ℝ X (φ t p) (φ t (p + h) - φ t p))
          + fderiv ℝ X (φ t p) (φ t (p + h) - φ t p - D t h)‖
        ≤ ‖X (φ t (p + h)) - X (φ t p) - fderiv ℝ X (φ t p) (φ t (p + h) - φ t p)‖
          + ‖fderiv ℝ X (φ t p) (φ t (p + h) - φ t p - D t h)‖ := norm_add_le _ _
      _ ≤ η * ‖φ t (p + h) - φ t p‖
          + ‖fderiv ℝ X (φ t p)‖ * ‖φ t (p + h) - φ t p - D t h‖ :=
        add_le_add hmv (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ η * (‖h‖ * Real.exp (K * T)) + K * ‖φ t (p + h) - φ t p - D t h‖ := by
        gcongr
        · exact hu t ht'
        · exact hK' _
      _ ≤ (K + 1) * ‖φ t (p + h) - φ t p - D t h‖ + η * Real.exp (K * T) * ‖h‖ := by
        nlinarith [norm_nonneg (φ t (p + h) - φ t p - D t h)]
  -- Grönwall
  have hf0 : ‖φ 0 (p + h) - φ 0 p - D 0 h‖ ≤ 0 := by simp [hφ.zero, hD0]
  have hfc : ContinuousOn (fun t => φ t (p + h) - φ t p - D t h) (Icc 0 T) := fun t ht =>
    (hf' t ht).continuousAt.continuousWithinAt
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun t => φ t (p + h) - φ t p - D t h)
    (f' := fun t => X (φ t (p + h)) - X (φ t p) - fderiv ℝ X (φ t p) (D t h))
    (δ := 0) (K := (K : ℝ) + 1) (ε := η * Real.exp (K * T) * ‖h‖) (a := 0) (b := T)
    hfc (fun t ht => (hf' t (Ico_subset_Icc_self ht)).hasDerivWithinAt) hf0 hbound T ⟨hT, le_rfl⟩
  rw [sub_zero] at hG
  refine hG.trans ((gronwallBound_zero_le (by positivity) (by positivity)).trans (le_of_eq ?_))
  rw [← hηc]; ring

end variational

/-! ## 4. Compactly supported `C^1` fields on a finite-dimensional space -/

section compact

variable {E : Type*} [NormedAddCommGroup E]

/-- A continuous compactly supported map is bounded. -/
lemma exists_bound_of_hasCompactSupport {F : Type*} [NormedAddCommGroup F] {f : E → F}
    (hc : HasCompactSupport f) (hf : Continuous f) : ∃ L : ℝ≥0, ∀ p, ‖f p‖ ≤ L := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hf).isBounded.exists_norm_le
  exact ⟨⟨max C 0, le_max_right _ _⟩, fun p =>
    le_trans (hC _ (mem_range_self p)) (le_max_left _ _)⟩

variable [NormedSpace ℝ E]

/-- The derivative of a `C^1` compactly supported map is bounded. -/
lemma exists_nnnorm_fderiv_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) : ∃ K : ℝ≥0, ∀ p, ‖fderiv ℝ f p‖₊ ≤ K := by
  obtain ⟨K, hK⟩ :=
    exists_bound_of_hasCompactSupport (hc.fderiv ℝ) (hf.continuous_fderiv one_ne_zero)
  exact ⟨K, fun p => by rw [← NNReal.coe_le_coe]; exact hK p⟩

/-- A `C^1` compactly supported map is globally Lipschitz. -/
lemma exists_lipschitzWith_of_hasCompactSupport {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) :
    ∃ K : ℝ≥0, LipschitzWith K f := by
  obtain ⟨K, hK⟩ := exists_nnnorm_fderiv_le hc hf
  exact ⟨K, lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero) hK⟩

/-- The derivative of a `C^1` compactly supported map is uniformly continuous. -/
lemma uniformContinuous_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) : UniformContinuous (fderiv ℝ f) :=
  (hc.fderiv ℝ).uniformContinuous_of_continuous (hf.continuous_fderiv one_ne_zero)

/-- Every compactly supported `C^1` vector field on a complete space has a global flow. -/
theorem exists_isGlobalFlow_of_hasCompactSupport [CompleteSpace E] {X : E → E}
    (hc : HasCompactSupport X) (hX : ContDiff ℝ 1 X) : ∃ φ : ℝ → E → E, IsGlobalFlow X φ := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_hasCompactSupport hc hX
  obtain ⟨L, hL⟩ := exists_bound_of_hasCompactSupport hc hX.continuous
  exact exists_isGlobalFlow hK hL

/-- Outside the support the derivative vanishes. -/
lemma fderiv_eq_zero_of_notMem_tsupport {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {p : E} (hp : p ∉ tsupport f) : fderiv ℝ f p = 0 := by
  have h : f =ᶠ[𝓝 p] fun _ => 0 :=
    Filter.eventually_of_mem ((isClosed_tsupport f).isOpen_compl.mem_nhds hp)
      fun x hx => image_eq_zero_of_notMem_tsupport hx
  rw [h.fderiv_eq]; exact fderiv_const_apply 0

end compact

/-! ## 5. The augmented (variational) system with a cut-off in the linear variable -/

section augmented

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The cut-off augmented field on `E × (E →L E)`:
`Y_b (x, A) = b(A) • (X x, DX(x) ∘ A)`, with `b` a smooth bump on `E →L E`. -/
def augFieldCut (X : E → E) (b : ContDiffBump (0 : E →L[ℝ] E)) (q : E × (E →L[ℝ] E)) :
    E × (E →L[ℝ] E) :=
  (b q.2 • X q.1, b q.2 • (fderiv ℝ X q.1).comp q.2)

lemma contDiff_augFieldCut {X : E → E} (hX : ContDiff ℝ ∞ X) (b : ContDiffBump (0 : E →L[ℝ] E)) :
    ContDiff ℝ ∞ (augFieldCut X b) := by
  have hb : ContDiff ℝ ∞ (fun q : E × (E →L[ℝ] E) => b q.2) := b.contDiff.comp contDiff_snd
  have hD : ContDiff ℝ ∞ (fun q : E × (E →L[ℝ] E) => fderiv ℝ X q.1) :=
    (hX.fderiv_right (m := ∞) (by simp)).comp contDiff_fst
  exact (hb.smul (hX.comp contDiff_fst)).prodMk (hb.smul (hD.clm_comp contDiff_snd))

lemma hasCompactSupport_augFieldCut {X : E → E} (hc : HasCompactSupport X)
    (b : ContDiffBump (0 : E →L[ℝ] E)) : HasCompactSupport (augFieldCut X b) := by
  refine HasCompactSupport.intro (IsCompact.prod hc b.hasCompactSupport) fun q hq => ?_
  rw [Set.mem_prod, not_and_or] at hq
  rcases hq with hq | hq
  · simp [augFieldCut, image_eq_zero_of_notMem_tsupport hq, fderiv_eq_zero_of_notMem_tsupport hq]
  · simp [augFieldCut, image_eq_zero_of_notMem_tsupport hq]

/-- The norm of the second component of the cut-off field is at most `‖DX(x)‖ ‖A‖`. -/
lemma norm_augFieldCut_snd_le {X : E → E} (b : ContDiffBump (0 : E →L[ℝ] E))
    (q : E × (E →L[ℝ] E)) :
    ‖(augFieldCut X b q).2‖ ≤ ‖fderiv ℝ X q.1‖ * ‖q.2‖ := by
  show ‖b q.2 • (fderiv ℝ X q.1).comp q.2‖ ≤ ‖fderiv ℝ X q.1‖ * ‖q.2‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
  calc b q.2 * ‖(fderiv ℝ X q.1).comp q.2‖ ≤ 1 * (‖fderiv ℝ X q.1‖ * ‖q.2‖) :=
        mul_le_mul b.le_one (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) zero_le_one
    _ = ‖fderiv ℝ X q.1‖ * ‖q.2‖ := one_mul _

end augmented

/-! ## 6. Smoothness in space, by induction on the order -/

/-- The induction statement `S k`: for every finite-dimensional real normed space `E`, every
`C^∞` compactly supported field `X` on `E`, every global flow `φ` of `X` and every time `s`, the
time-`s` map `φ s : E → E` is `C^k`. -/
def SpaceSmooth (k : ℕ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (X : E → E),
    ContDiff ℝ ∞ X → HasCompactSupport X →
      ∀ φ : ℝ → E → E, IsGlobalFlow X φ → ∀ s : ℝ, ContDiff ℝ k (φ s)

/-- `S 0`: continuity in the initial point (Lipschitz dependence). -/
theorem spaceSmooth_zero : SpaceSmooth 0 := by
  intro E _ _ _ X hX hc φ hφ s
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_hasCompactSupport hc (hX.of_le (by simp))
  simp only [Nat.cast_zero, contDiff_zero]
  exact hφ.continuous_space hK s

section step

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : E → E} {φ : ℝ → E → E}

/-- The induction step for `s ≥ 0`: if `S k` holds, then `φ s` is `C^{k+1}`.  The derivative is
read off from the flow `Ψ` of the cut-off augmented field: `fderiv (φ s) p = (Ψ s (p, 1)).2`. -/
theorem contDiff_space_succ_nonneg (k : ℕ) (IH : SpaceSmooth k) (hX : ContDiff ℝ ∞ X)
    (hc : HasCompactSupport X) (hφ : IsGlobalFlow X φ) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ((k : WithTop ℕ∞) + 1) (φ s) := by
  obtain ⟨K, hK⟩ := exists_nnnorm_fderiv_le hc (hX.of_le (by simp))
  have hK' : ∀ x, ‖fderiv ℝ X x‖ ≤ K := fun x => by exact_mod_cast hK x
  have hX1 : Differentiable ℝ X := hX.differentiable (by simp)
  have hLip : LipschitzWith K X := lipschitzWith_of_nnnorm_fderiv_le hX1 hK
  have hU : UniformContinuous (fderiv ℝ X) := uniformContinuous_fderiv hc (hX.of_le (by simp))
  -- the bump on `E →L E`, equal to `1` on the ball of radius `R = e^{K s}`
  have hR : 0 < Real.exp (K * s) := Real.exp_pos _
  let b : ContDiffBump (0 : E →L[ℝ] E) :=
    ⟨Real.exp (K * s), 2 * Real.exp (K * s), hR, by linarith⟩
  -- the cut-off augmented field and its global flow `Ψ`
  have hYs : ContDiff ℝ ∞ (augFieldCut X b) := contDiff_augFieldCut hX b
  have hYc : HasCompactSupport (augFieldCut X b) := hasCompactSupport_augFieldCut hc b
  obtain ⟨Ψ, hΨ⟩ := exists_isGlobalFlow_of_hasCompactSupport hYc (hYs.of_le (by simp))
  have hΨk : ContDiff ℝ k (Ψ s) := IH _ _ hYs hYc Ψ hΨ s
  -- the two components of `t ↦ Ψ t (p, 1)`
  have hγ₁ : ∀ p t, HasDerivAt (fun t => (Ψ t (p, 1)).1)
      (b (Ψ t (p, 1)).2 • X (Ψ t (p, 1)).1) t := fun p t =>
    (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t (hΨ.hasDerivAt t (p, 1))
  have hγ₂ : ∀ p t, HasDerivAt (fun t => (Ψ t (p, 1)).2)
      (b (Ψ t (p, 1)).2 • (fderiv ℝ X (Ψ t (p, 1)).1).comp (Ψ t (p, 1)).2) t := fun p t =>
    (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t (hΨ.hasDerivAt t (p, 1))
  -- a priori bound: `‖(Ψ t (p, 1)).2‖ ≤ e^{K t} ≤ e^{K s}` on `[0, s]`
  have hbound : ∀ p, ∀ t ∈ Icc 0 s, ‖(Ψ t (p, 1)).2‖ ≤ Real.exp (K * s) := by
    intro p t ht
    have h := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := fun t => (Ψ t (p, 1)).2)
      (f' := fun t => b (Ψ t (p, 1)).2 • (fderiv ℝ X (Ψ t (p, 1)).1).comp (Ψ t (p, 1)).2)
      (δ := 1) (K := K) (ε := 0) (a := 0) (b := s)
      (fun t _ => (hγ₂ p t).continuousAt.continuousWithinAt)
      (fun t _ => (hγ₂ p t).hasDerivWithinAt)
      (by simp only [hΨ.zero]; exact ContinuousLinearMap.norm_id_le)
      (fun t _ => by
        rw [add_zero]
        refine (norm_augFieldCut_snd_le (X := X) b (Ψ t (p, 1))).trans ?_
        gcongr
        exact hK' _)
      t ht
    rw [gronwallBound_ε0, sub_zero, one_mul] at h
    exact h.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg))
  have hcut : ∀ p, ∀ t ∈ Icc 0 s, b (Ψ t (p, 1)).2 = 1 := fun p t ht =>
    b.one_of_mem_closedBall (mem_closedBall_zero_iff.2 (hbound p t ht))
  -- the first component is `φ t p` on `[0, s]` (forward uniqueness)
  have hfirst : ∀ p, ∀ t ∈ Icc 0 s, (Ψ t (p, 1)).1 = φ t p := by
    intro p t ht
    have h := dist_le_of_trajectories_ODE (v := fun _ => X) (fun _ => hLip)
      (f := fun t => (Ψ t (p, 1)).1) (g := fun t => φ t p) (a := 0) (b := s) (δ := 0)
      (fun t _ => (hγ₁ p t).continuousAt.continuousWithinAt)
      (fun t ht' => ((hγ₁ p t).congr_deriv
        (by rw [hcut p t (Ico_subset_Icc_self ht'), one_smul])).hasDerivWithinAt)
      (hφ.continuous_time p).continuousOn
      (fun t _ => (hφ.hasDerivAt t p).hasDerivWithinAt)
      (by simp [hΨ.zero, hφ.zero]) t ht
    rw [zero_mul] at h
    exact dist_le_zero.1 h
  -- the second component solves the variational equation along `φ · p` on `[0, s]`
  have hvar : ∀ p, ∀ t ∈ Icc 0 s, HasDerivAt (fun t => (Ψ t (p, 1)).2)
      ((fderiv ℝ X (φ t p)).comp (Ψ t (p, 1)).2) t := by
    intro p t ht
    refine (hγ₂ p t).congr_deriv ?_
    rw [hcut p t ht, one_smul, hfirst p t ht]
  -- hence `φ s` has derivative `(Ψ s (p, 1)).2` at every `p`
  have hderiv : ∀ p, HasFDerivAt (φ s) (Ψ s (p, 1)).2 p := fun p =>
    hasFDerivAt_flow_of_variational hX1 hK hU hφ hs p (D := fun t => (Ψ t (p, 1)).2)
      (by simp [hΨ.zero]) (hvar p)
  rw [contDiff_succ_iff_fderiv]
  refine ⟨fun p => (hderiv p).differentiableAt, by simp, ?_⟩
  have : fderiv ℝ (φ s) = fun p => (Ψ s (p, 1)).2 := funext fun p => (hderiv p).fderiv
  rw [this]
  exact contDiff_snd.comp (hΨk.comp (contDiff_id.prodMk contDiff_const))

end step

/-- `S k → S (k + 1)`. -/
theorem spaceSmooth_succ (k : ℕ) (IH : SpaceSmooth k) : SpaceSmooth (k + 1) := by
  intro E _ _ _ X hX hc φ hφ s
  rcases le_or_gt 0 s with hs | hs
  · have h := contDiff_space_succ_nonneg k IH hX hc hφ hs
    exact_mod_cast h
  · have h := contDiff_space_succ_nonneg k IH hX.neg (hc.comp_left (g := fun x => -x) neg_zero)
      hφ.neg (neg_nonneg.2 hs.le)
    simp only [neg_neg] at h
    exact_mod_cast h

theorem spaceSmooth (k : ℕ) : SpaceSmooth k := by
  induction k with
  | zero => exact spaceSmooth_zero
  | succ k ih => exact spaceSmooth_succ k ih

section space

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : E → E} {φ : ℝ → E → E}

/-- **Smooth dependence on the initial point, fixed time**: `φ s` is `C^∞` for every `s`. -/
theorem contDiff_space (hX : ContDiff ℝ ∞ X) (hc : HasCompactSupport X) (hφ : IsGlobalFlow X φ)
    (s : ℝ) : ContDiff ℝ ∞ (φ s) := by
  rw [contDiff_infty]
  intro k
  exact spaceSmooth k E X hX hc φ hφ s

end space

/-! ## 7. Joint smoothness by suspension -/

section joint

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : E → E} {φ : ℝ → E → E}

/-- The suspended field `(τ, x) ↦ (0, χ τ • X x)` on `ℝ × E`, with `χ τ = b τ * τ` for a bump
`b` on `ℝ` (so `χ τ = τ` for `|τ| ≤ b.rIn`). -/
def suspField (X : E → E) (b : ContDiffBump (0 : ℝ)) (q : ℝ × E) : ℝ × E :=
  (0, (b q.1 * q.1) • X q.2)

lemma contDiff_suspField (hX : ContDiff ℝ ∞ X) (b : ContDiffBump (0 : ℝ)) :
    ContDiff ℝ ∞ (suspField X b) :=
  contDiff_const.prodMk
    (((b.contDiff.comp contDiff_fst).mul contDiff_fst).smul (hX.comp contDiff_snd))

lemma hasCompactSupport_suspField (hc : HasCompactSupport X) (b : ContDiffBump (0 : ℝ)) :
    HasCompactSupport (suspField X b) := by
  refine HasCompactSupport.intro (IsCompact.prod b.hasCompactSupport hc) fun q hq => ?_
  rw [Set.mem_prod, not_and_or] at hq
  rcases hq with hq | hq
  · simp [suspField, image_eq_zero_of_notMem_tsupport hq]
  · simp [suspField, image_eq_zero_of_notMem_tsupport hq]

/-- `(s, (τ, x)) ↦ (τ, φ (χ τ * s) x)` is a global flow of the suspended field. -/
lemma isGlobalFlow_suspFlow (hφ : IsGlobalFlow X φ) (b : ContDiffBump (0 : ℝ)) :
    IsGlobalFlow (suspField X b) (fun s q => (q.1, φ (b q.1 * q.1 * s) q.2)) where
  zero q := by simp [hφ.zero]
  hasDerivAt s q := by
    have h1 : HasDerivAt (fun s : ℝ => b q.1 * q.1 * s) (b q.1 * q.1) s := by
      simpa using (hasDerivAt_id s).const_mul (b q.1 * q.1)
    have h2 := (hφ.hasDerivAt (b q.1 * q.1 * s) q.2).scomp s h1
    exact (hasDerivAt_const s q.1).prodMk h2

variable [FiniteDimensional ℝ E]

/-- **Smooth dependence on initial conditions.**  The global flow of a `C^∞` compactly supported
vector field on a finite-dimensional real normed space is `C^∞` jointly in `(s, p)`. -/
theorem contDiff_uncurry (hX : ContDiff ℝ ∞ X) (hc : HasCompactSupport X)
    (hφ : IsGlobalFlow X φ) : ContDiff ℝ ∞ (uncurry φ) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨s₀, p₀⟩
  have hR : 0 < |s₀| + 1 := by positivity
  let b : ContDiffBump (0 : ℝ) := ⟨|s₀| + 1, 2 * (|s₀| + 1), hR, by linarith⟩
  -- the time-one map of the suspended flow is smooth in the space variable `(τ, x)`
  have hsm : ContDiff ℝ ∞ (fun q : ℝ × E => (q.1, φ (b q.1 * q.1 * 1) q.2)) :=
    contDiff_space (contDiff_suspField hX b) (hasCompactSupport_suspField hc b)
      (isGlobalFlow_suspFlow hφ b) 1
  have hsm' : ContDiff ℝ ∞ (fun q : ℝ × E => φ (b q.1 * q.1 * 1) q.2) := contDiff_snd.comp hsm
  refine hsm'.contDiffAt.congr_of_eventuallyEq ?_
  have hopen : {q : ℝ × E | |q.1| < |s₀| + 1} ∈ 𝓝 (s₀, p₀) := by
    apply (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).mem_nhds
    show |s₀| < |s₀| + 1
    linarith
  filter_upwards [hopen] with q hq
  have hb : b q.1 = 1 := by
    apply b.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
    exact hq.le
  simp [Function.uncurry, hb]

end joint

end

end SmoothDep

/-! ## 8. The statement of `ContactMotions.lean` -/

open scoped ContDiff

open SmoothDep in
/-- **`SM.SmoothDependence`, structure-free.**  For a `C^∞` compactly supported vector field `X`
on `ℝ³` and any `φ : ℝ → ℝ³ → ℝ³` with `φ 0 p = p` and `∂_s φ s p = X (φ s p)`, the map
`uncurry φ : ℝ × ℝ³ → ℝ³` is `C^∞`.  (This is `SM.SmoothDependence` with `IsGlobalFlow X φ`
unfolded into its two fields.) -/
theorem smoothDependence_of_flow (X : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hX : ContDiff ℝ ∞ X) (hc : HasCompactSupport X)
    (φ : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (h0 : ∀ p, φ 0 p = p) (hd : ∀ s p, HasDerivAt (fun s => φ s p) (X (φ s p)) s) :
    ContDiff ℝ ∞ (Function.uncurry φ) :=
  SmoothDep.contDiff_uncurry hX hc ⟨h0, hd⟩

open SmoothDep in
/-- **`SM.SmoothDependence`** with the (copied) structure `SmoothDep.IsGlobalFlow`; literally the
body of `SM.SmoothDependence` in `ContactMotions.lean` once `SmoothDep.IsGlobalFlow` is identified
with `ContactMotions.IsGlobalFlow` (same fields, same order). -/
theorem smoothDependence_of_isGlobalFlow :
    ∀ X : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), ContDiff ℝ ∞ X →
      HasCompactSupport X → ∀ φ : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        SmoothDep.IsGlobalFlow X φ → ContDiff ℝ ∞ (Function.uncurry φ) :=
  fun _ hX hc _ hφ => SmoothDep.contDiff_uncurry hX hc hφ

end SM
