import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # SM fd:contact-motions — explicit contact motions (row 86)

Source: reference/SM/sm-3-statesum.tex:2586-2597 (statement), 2598-2611 (proof).  Drafted
2026-09-14 in work/drafts/fd/ (the fd block 84-88; row 85 fd:parameter-avoidance is the style
model, `ParameterAvoidance.lean`).  Pure analysis, Mathlib only.  Intended home:
`work/lean/SM/ContactMotions.lean`.
Main declaration: `SM.fd_contact_motions : SM.SmoothDependence → SM.ContactMotionsData`.
Check: `cd work/lean && lake env lean ../drafts/fd/ContactMotions.lean`.

## The printed statement (sm-3:2586-2597, verbatim)

"For a smooth compactly supported H : ℝ³ → ℝ, the vector field
X_H = −H_y ∂_x + (H_x + y H_z) ∂_y + (H − y H_y) ∂_z
has a global flow φ_H^s of coorientation-preserving contact diffeomorphisms for α = dz − y dx:
(φ_H^s)^*α = c_s^H α with a smooth positive function c_s^H, its conformal factor.  Finite
compositions of their small-time flows depend smoothly on the times and are arbitrarily C^k-close
to the identity on compact sets for each fixed finite k."

Printed proof (sm-3:2598-2611): `α(X_H) = H`, `ι_{X_H} dα = H_z α − dH`, so `L_{X_H} α = H_z α`;
differentiating the pullback and solving the scalar ODE gives
`(φ_H^s)^*α = exp(∫_0^s H_z ∘ φ_H^v dv) α`, the positive conformal factor; the field is bounded and
compactly supported, so trajectories do not escape in finite time, continuation gives all times,
backwards uniqueness the inverse; "smooth ODE dependence proves the last assertion".

## Printed notion → Lean

`ℝ³ = EuclideanSpace ℝ (Fin 3)`, `(x, y, z) = (p 0, p 1, p 2)`; `∞` is `C^∞`.

| printed | Lean |
|---|---|
| "smooth compactly supported `H`" (2587) | `ContactMotionsHyp H`: `ContDiff ℝ ∞ H`, `HasCompactSupport H` |
| `X_H` (2588-2590) | `ContactMotions.hamVF H p = !₂[−H_y, H_x + y H_z, H − y H_y]` with `pd H i p = fderiv ℝ H p (e i)` |
| `α = dz − y dx` | `ContactMotions.alpha p v = v 2 − p 1 * v 0` |
| "global flow `φ_H^s`" (2591) | `hamFlow H : ℝ → ℝ³ → ℝ³` with `IsGlobalFlow (hamVF H) (hamFlow H)`: `φ 0 = id`, `∂_s φ s p = X_H (φ s p)`; the flow law `φ (s+t) = φ s ∘ φ t` |
| "coorientation-preserving contact diffeomorphisms" (2591-2592) | `diffeo` (jointly `C^∞`, `φ_{−s}` the `C^∞` two-sided inverse), `contact`, `confFactor_pos` |
| `(φ_H^s)^*α = c_s^H α` (2592) | `alpha (φ s p) (fderiv ℝ (φ s) p v) = confFactor H s p * alpha p v` for all `p, v` |
| "a smooth positive function `c_s^H`, its conformal factor" (2593) | `confFactor H s p = exp (∫_0^s pd H 2 (φ v p) dv)` (`confFactor_eq`, the printed formula 2603-2606), `confFactor_pos`, `confFactor_smooth` (jointly in `(s, p)`) |
| "Finite compositions of their small-time flows depend smoothly on the times" (2594-2595) | `composeFlows n Hs a = φ_{H_0}^{a_0} ∘ ⋯ ∘ φ_{H_{n−1}}^{a_{n−1}}`; `compositions_smooth`: `C^∞` in `(a, p) ∈ ℝ^n × ℝ³` |
| "arbitrarily `C^k`-close to the identity on compact sets for each fixed finite `k`" (2595-2596) | `compositions_close`: `∀ K` compact, `k`, `ε > 0`, `∃ δ > 0`, `|a_i| < δ → ∀ j ≤ k, ∀ p ∈ K, ‖iteratedFDeriv ℝ j (Φ_a − id) p‖ < ε` |

## Route

* §1 coordinates: `e`, `alpha`, `pd`, `hamVF`; `alpha_hamVF : α(X_H) = H` (2599); `X_H` is `C^∞`
  and compactly supported (`contDiff_hamVF`, `hasCompactSupport_hamVF`).
* §2 global flows of a bounded globally Lipschitz field on a complete space: existence on
  `(−(n+1), n+1)` by `IsPicardLindelof.of_time_independent` with radius `L(n+1)`
  (`exists_solution_Ioo`), gluing by `ODE_solution_unique_of_mem_Ioo` (`exists_solution_global`,
  "ODE continuation gives all finite times", 2609-2610), `exists_isGlobalFlow`; uniqueness, flow
  law, inverse `φ (−s)`, bijectivity, `C^∞` in time (`IsGlobalFlow.*`).
* §3 compactly supported `C^1` fields on `ℝ³` are bounded and Lipschitz
  (`HasCompactSupport.isCompact_range`, `lipschitzWith_of_nnnorm_fderiv_le`);
  `globalFlow X := Classical.epsilon (IsGlobalFlow X)`.
* §4 the contact identity for a jointly smooth flow: the variational equation
  `∂_s Dφ_s = DX_H ∘ Dφ_s` from `ContDiffAt.isSymmSndFDerivAt` (`hasDerivAt_fderiv_flow`); the
  algebraic identity `α_q(DX_H(q) w) = dH_q(w) − H_y w_y` (`alpha_fderiv_hamVF`, no second
  derivatives of `H` needed since `(X_H)_z = H + y (X_H)_x`); the infinitesimal identity
  `∂_s α_{φ_s p}(Dφ_s v) = H_z(φ_s p) α_{φ_s p}(Dφ_s v)` (`hasDerivAt_alpha_flow`, the coordinate
  form of `L_{X_H} α = H_z α`, 2599-2601); the scalar ODE `∂_s c = (H_z ∘ φ) c` and its solution
  by constancy of `β e^{−∫}` (`alpha_flow_eq`, 2602-2605); smoothness of `c` via
  `c = α_{φ_s p}(Dφ_s ∂_z)` (`contDiff_confFactorOf`).
* §5 `composeFlows`, `contDiff_composeFlows` (induction), `composeFlows_close`: the partial
  iterated derivative is the full one restricted to the `ℝ³`-directions
  (`iteratedFDeriv_partial`, via `iteratedFDeriv_comp_add_left` and
  `ContinuousLinearMap.iteratedFDeriv_comp_right`), which is continuous in `(a, p)` and vanishes on
  `{0} × ℝ³`; `generalized_tube_lemma` on `{0} × K` gives `δ`.
* §6 the gap `SmoothDependence`, the bundle `ContactMotionsData`, the row `fd_contact_motions`.

## The gap (explicit hypothesis, no placeholder declaration)

`SM.SmoothDependence : Prop` — for a `C^∞` compactly supported field on `ℝ³`, every global flow is
`C^∞` jointly in `(s, p)`.  This is the classical smooth dependence of ODE solutions on the
initial point, which Mathlib (this pin) does not contain (`Mathlib/Analysis/ODE/*` has existence,
uniqueness, Grönwall and regularity in time only).  It is used exactly once
(`ContactMotionsHyp.contDiff_uncurry_hamFlow`); everything else, including the global existence
of the flow, its uniqueness, the group law and the `C^∞` time dependence, is unconditional
(`ContactMotionsHyp.isGlobalFlow`, `hamFlow_add`, `hamFlow_bijective`, `hamFlow_unique`,
`contDiff_hamFlow_time`), and the contact identity is proved for any jointly smooth flow of `X_H`
(`alpha_flow_eq`, `contact_of_contDiff`).  See `FD_84_86_FEASIBILITY.md` §1.

## Fidelity readings

* **FR-CM-1 (pullback in coordinates).** Mathlib has no pullback calculus of differential forms;
  `(φ_s)^*α = c α` is stated pointwise on vectors, `α_{φ_s p}(Dφ_s(p) v) = c_s(p) α_p(v)`.
* **FR-CM-2 (coorientation-preserving).** `c_s^H > 0` (the paper: "positive").
* **FR-CM-3 (smooth conformal factor).** `c` is shown `C^∞` jointly in `(s, p)`, which contains the
  printed "smooth function `c_s^H`" (smooth in `p` for each `s`).
* **FR-CM-4 (diffeomorphism).** Each `φ_H^s` is `C^∞` with the `C^∞` two-sided inverse `φ_H^{−s}`
  (the paper: "backwards uniqueness gives the inverse", 2610).
* **FR-CM-5 (compositions).** "Finite compositions of their small-time flows" is
  `composeFlows n Hs a` for any `n`, any Hamiltonians `H_0, …, H_{n−1}` satisfying the hypothesis
  and any times `a ∈ ℝ^n`; smooth dependence is joint in `(a, p)`; "small-time" enters through
  `|a_i| < δ` in the closeness clause.
* **FR-CM-6 (`C^k`-closeness).** "arbitrarily `C^k`-close to the identity on compact sets" is the
  uniform bound `‖D^j(Φ_a − id)(p)‖ < ε` for all `j ≤ k` and `p ∈ K` (the sup norm of the first
  `k` derivatives on `K`), for all `|a_i| < δ`.  The `δ` may depend on `K, k, ε` and the `H_i`. -/

namespace SM

open scoped ContDiff Topology NNReal
open Set Filter Function

noncomputable section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace ContactMotions

/-! ## 1. Coordinates, the contact form `α = dz − y dx`, the field `X_H` -/

/-- The standard basis vector `e i` of `ℝ³`; `(x, y, z) = (p 0, p 1, p 2)`. -/
def e (i : Fin 3) : ℝ³ := EuclideanSpace.single i 1

@[simp] lemma e_apply (i j : Fin 3) : e i j = if j = i then 1 else 0 := by
  simp [e]

/-- The contact form `α = dz − y dx` at `p`, evaluated on `v`: `α_p(v) = v_z − p_y v_x`. -/
def alpha (p v : ℝ³) : ℝ := v 2 - p 1 * v 0

/-- The partial derivative `∂_i H` (`H_x, H_y, H_z` for `i = 0, 1, 2`). -/
def pd (H : ℝ³ → ℝ) (i : Fin 3) (p : ℝ³) : ℝ := fderiv ℝ H p (e i)

/-- `X_H = −H_y ∂_x + (H_x + y H_z) ∂_y + (H − y H_y) ∂_z` (sm-3:2588-2590). -/
def hamVF (H : ℝ³ → ℝ) (p : ℝ³) : ℝ³ :=
  !₂[-(pd H 1 p), pd H 0 p + p 1 * pd H 2 p, H p - p 1 * pd H 1 p]

@[simp] lemma hamVF_apply_zero (H : ℝ³ → ℝ) (p : ℝ³) : hamVF H p 0 = -(pd H 1 p) := by
  simp [hamVF]

@[simp] lemma hamVF_apply_one (H : ℝ³ → ℝ) (p : ℝ³) :
    hamVF H p 1 = pd H 0 p + p 1 * pd H 2 p := by
  simp [hamVF]

@[simp] lemma hamVF_apply_two (H : ℝ³ → ℝ) (p : ℝ³) : hamVF H p 2 = H p - p 1 * pd H 1 p := by
  simp [hamVF]

/-- "Substitution gives `α(X_H) = H`" (sm-3:2599). -/
lemma alpha_hamVF (H : ℝ³ → ℝ) (p : ℝ³) : alpha p (hamVF H p) = H p := by
  simp only [alpha, hamVF_apply_two, hamVF_apply_zero]; ring

lemma alpha_e_two (p : ℝ³) : alpha p (e 2) = 1 := by simp [alpha]

lemma alpha_add (p v w : ℝ³) : alpha p (v + w) = alpha p v + alpha p w := by
  simp [alpha]; ring

lemma alpha_smul (p : ℝ³) (c : ℝ) (v : ℝ³) : alpha p (c • v) = c * alpha p v := by
  simp [alpha]; ring

/-- The `i`-th coordinate functional of `ℝ³` as a continuous linear map. -/
def coordCLM (i : Fin 3) : ℝ³ →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

@[simp] lemma coordCLM_apply (i : Fin 3) (p : ℝ³) : coordCLM i p = p i := rfl

/-- The coordinate functionals are smooth. -/
lemma contDiff_coord (i : Fin 3) : ContDiff ℝ ∞ (fun p : ℝ³ => p i) := (coordCLM i).contDiff

lemma hasFDerivAt_coord (i : Fin 3) (p : ℝ³) :
    HasFDerivAt (fun p : ℝ³ => p i) (coordCLM i) p :=
  (coordCLM i).hasFDerivAt

lemma fderiv_coord (i : Fin 3) (p v : ℝ³) : fderiv ℝ (fun p : ℝ³ => p i) p v = v i := by
  rw [(hasFDerivAt_coord i p).fderiv]; rfl

/-- Coordinate of a derivative: `(Df(p) v) i = D(f_i)(p) v`. -/
lemma fderiv_apply_coord {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ³} {p : F}
    (hf : DifferentiableAt ℝ f p) (v : F) (i : Fin 3) :
    fderiv ℝ f p v i = fderiv ℝ (fun q => f q i) p v := by
  have h : HasFDerivAt (fun q => f q i) ((coordCLM i).comp (fderiv ℝ f p)) p :=
    (coordCLM i).hasFDerivAt.comp p hf.hasFDerivAt
  rw [h.fderiv]; rfl

lemma hasDerivAt_coord {γ : ℝ → ℝ³} {γ' : ℝ³} {t : ℝ} (h : HasDerivAt γ γ' t) (i : Fin 3) :
    HasDerivAt (fun t => γ t i) (γ' i) t :=
  (coordCLM i).hasFDerivAt.comp_hasDerivAt t h

lemma contDiff_pd {H : ℝ³ → ℝ} (hH : ContDiff ℝ ∞ H) (i : Fin 3) : ContDiff ℝ ∞ (pd H i) := by
  have h1 : ContDiff ℝ ∞ (fun q : ℝ³ × ℝ³ => fderiv ℝ H q.1 q.2) :=
    hH.contDiff_fderiv_apply (m := ∞) (by simp)
  exact h1.comp (contDiff_id.prodMk contDiff_const)

lemma contDiff_hamVF {H : ℝ³ → ℝ} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (hamVF H) := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa using (contDiff_pd hH 1).neg
  · simpa using (contDiff_pd hH 0).add ((contDiff_coord 1).mul (contDiff_pd hH 2))
  · simpa using hH.sub ((contDiff_coord 1).mul (contDiff_pd hH 1))

/-- Outside the (closed) support of `H` every partial derivative vanishes. -/
lemma pd_eq_zero_of_notMem {H : ℝ³ → ℝ} {p : ℝ³} (hp : p ∉ tsupport H) (i : Fin 3) :
    pd H i p = 0 := by
  have h : H =ᶠ[𝓝 p] fun _ => 0 :=
    Filter.eventually_of_mem ((isClosed_tsupport H).isOpen_compl.mem_nhds hp)
      fun x hx => image_eq_zero_of_notMem_tsupport hx
  simp [pd, h.fderiv_eq]

lemma hasCompactSupport_hamVF {H : ℝ³ → ℝ} (hc : HasCompactSupport H) :
    HasCompactSupport (hamVF H) := by
  refine HasCompactSupport.intro hc fun p hp => ?_
  have h0 : H p = 0 := image_eq_zero_of_notMem_tsupport hp
  ext i
  fin_cases i <;> simp [pd_eq_zero_of_notMem hp, h0]

/-! ## 2. Global flows of bounded globally Lipschitz vector fields -/

section flows

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A global flow of the (autonomous) vector field `X`: `φ 0 = id` and
`∂_s φ s p = X (φ s p)` for all `s ∈ ℝ`, `p`. -/
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

/-- Existence on the symmetric interval `(−(n+1), n+1)` for every initial point: Picard–Lindelöf
with radius `a = L (n+1)`, which is available because `X` is bounded by `L` and `K`-Lipschitz on
the whole space ("trajectories cannot escape to infinity in finite time", sm-3:2607-2609). -/
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

/-- A global solution through every point ("ODE continuation gives all finite times",
sm-3:2609-2610): the local solutions on `(−(n+1), n+1)` agree where both are defined, by
uniqueness, and glue to one solution on `ℝ`. -/
lemma exists_solution_global {X : E → E} {K L : ℝ≥0} (hK : LipschitzWith K X)
    (hL : ∀ p, ‖X p‖ ≤ L) (p : E) :
    ∃ γ : ℝ → E, γ 0 = p ∧ ∀ t, HasDerivAt γ (X (γ t)) t := by
  choose α hα0 hα using exists_solution_Ioo hK hL (p := p)
  -- the glued curve
  let γ : ℝ → E := fun t => α ⌈|t|⌉₊ t
  have key : ∀ (n : ℕ) (t : ℝ), |t| < (n : ℝ) + 1 → γ t = α n t := by
    intro n t ht
    have hm : |t| < (⌈|t|⌉₊ : ℝ) + 1 := by
      have := Nat.le_ceil |t|
      linarith
    -- both solve on the smaller symmetric interval and agree at `0`
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
  · -- near `t`, `γ` coincides with `α N`, `N = ⌈|t|⌉₊`
    set N := ⌈|t|⌉₊ with hN
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

section flowProps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : E → E} {φ : ℝ → E → E}

namespace IsGlobalFlow

/-- Any two global flows of a globally Lipschitz field coincide. -/
theorem unique {K : ℝ≥0} (hK : LipschitzWith K X) (hφ : IsGlobalFlow X φ) {ψ : ℝ → E → E}
    (hψ : IsGlobalFlow X ψ) : ψ = φ := by
  ext s p
  have := ODE_unique_global hK (f := fun s => ψ s p) (g := fun s => φ s p)
    (fun s => hψ.hasDerivAt s p) (fun s => hφ.hasDerivAt s p) (t₀ := 0)
    (by simp [hψ.zero, hφ.zero])
  exact congrFun this s

/-- The flow law `φ (s + t) = φ s ∘ φ t` (a "flow", sm-3:2591), by uniqueness. -/
theorem add {K : ℝ≥0} (hK : LipschitzWith K X) (hφ : IsGlobalFlow X φ) (s t : ℝ) (p : E) :
    φ (s + t) p = φ s (φ t p) := by
  have := ODE_unique_global hK (f := fun s => φ (s + t) p) (g := fun s => φ s (φ t p))
    (fun s => by
      have := hφ.hasDerivAt (s + t) p
      exact this.comp_add_const s t)
    (fun s => hφ.hasDerivAt s (φ t p)) (t₀ := 0) (by simp [hφ.zero])
  exact congrFun this s

/-- `φ (−s)` inverts `φ s` ("backwards uniqueness gives the inverse", sm-3:2610). -/
theorem neg_apply {K : ℝ≥0} (hK : LipschitzWith K X) (hφ : IsGlobalFlow X φ) (s : ℝ) (p : E) :
    φ (-s) (φ s p) = p := by
  rw [← hφ.add hK, neg_add_cancel, hφ.zero]

theorem leftInverse {K : ℝ≥0} (hK : LipschitzWith K X) (hφ : IsGlobalFlow X φ) (s : ℝ) :
    LeftInverse (φ (-s)) (φ s) := fun p => hφ.neg_apply hK s p

theorem rightInverse {K : ℝ≥0} (hK : LipschitzWith K X) (hφ : IsGlobalFlow X φ) (s : ℝ) :
    RightInverse (φ (-s)) (φ s) := fun p => by
  have := hφ.neg_apply hK (-s) p
  rwa [neg_neg] at this

theorem bijective {K : ℝ≥0} (hK : LipschitzWith K X) (hφ : IsGlobalFlow X φ) (s : ℝ) :
    Bijective (φ s) :=
  ⟨(hφ.leftInverse hK s).injective, (hφ.rightInverse hK s).surjective⟩

theorem continuous_time (hφ : IsGlobalFlow X φ) (p : E) : Continuous fun s => φ s p :=
  continuous_iff_continuousAt.2 fun s => (hφ.hasDerivAt s p).continuousAt

/-- Solutions of a `C^n` autonomous ODE are `C^{n+1}` in time (an induction on `n` with
`deriv (φ · p) = X ∘ φ · p`). -/
theorem contDiff_time_nat (hφ : IsGlobalFlow X φ) (n : ℕ) (hX : ContDiff ℝ n X) (p : E) :
    ContDiff ℝ (n + 1) (fun s => φ s p) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_add]
    rw [contDiff_one_iff_deriv]
    refine ⟨fun s => (hφ.hasDerivAt s p).differentiableAt, ?_⟩
    have : deriv (fun s => φ s p) = fun s => X (φ s p) := funext fun s => (hφ.hasDerivAt s p).deriv
    rw [this]
    exact hX.continuous.comp (hφ.continuous_time p)
  | succ n ih =>
    have h := ih (hX.of_le (by exact_mod_cast Nat.le_succ n))
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun s => (hφ.hasDerivAt s p).differentiableAt, by simp, ?_⟩
    have : deriv (fun s => φ s p) = fun s => X (φ s p) := funext fun s => (hφ.hasDerivAt s p).deriv
    rw [this]
    have h' : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun s => φ s p) := by exact_mod_cast h
    exact hX.comp h'

/-- The flow is `C^∞` in time. -/
theorem contDiff_time (hφ : IsGlobalFlow X φ) (hX : ContDiff ℝ ∞ X) (p : E) :
    ContDiff ℝ ∞ (fun s => φ s p) := by
  rw [contDiff_infty]
  intro n
  exact (hφ.contDiff_time_nat n (hX.of_le (by exact_mod_cast le_top)) p).of_le
    (by exact_mod_cast Nat.le_succ n)

end IsGlobalFlow

end flowProps

/-! ## 3. Compactly supported `C^1` fields on `ℝ³` are bounded and globally Lipschitz -/

section compact

/-- A continuous compactly supported map is bounded. -/
lemma exists_bound_of_hasCompactSupport {F : Type*} [NormedAddCommGroup F] {f : ℝ³ → F}
    (hc : HasCompactSupport f) (hf : Continuous f) : ∃ L : ℝ≥0, ∀ p, ‖f p‖ ≤ L := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hf).isBounded.exists_norm_le
  exact ⟨⟨max C 0, le_max_right _ _⟩, fun p =>
    le_trans (hC _ (mem_range_self p)) (le_max_left _ _)⟩

/-- A `C^1` compactly supported map is globally Lipschitz. -/
lemma exists_lipschitzWith_of_hasCompactSupport {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ³ → F} (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) :
    ∃ K : ℝ≥0, LipschitzWith K f := by
  obtain ⟨K, hK⟩ := exists_bound_of_hasCompactSupport (hc.fderiv ℝ) (hf.continuous_fderiv one_ne_zero)
  exact ⟨K, lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero) fun p => by
    rw [← NNReal.coe_le_coe]; exact hK p⟩

/-- Every compactly supported `C^1` vector field on `ℝ³` has a global flow. -/
theorem exists_isGlobalFlow_of_hasCompactSupport {X : ℝ³ → ℝ³} (hc : HasCompactSupport X)
    (hX : ContDiff ℝ 1 X) : ∃ φ : ℝ → ℝ³ → ℝ³, IsGlobalFlow X φ := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_hasCompactSupport hc hX
  obtain ⟨L, hL⟩ := exists_bound_of_hasCompactSupport hc hX.continuous
  exact exists_isGlobalFlow hK hL

/-- The global flow of a vector field, chosen once and for all (the unique one when `X` is
globally Lipschitz). -/
def globalFlow (X : ℝ³ → ℝ³) : ℝ → ℝ³ → ℝ³ := Classical.epsilon (IsGlobalFlow X)

theorem isGlobalFlow_globalFlow {X : ℝ³ → ℝ³} (hc : HasCompactSupport X) (hX : ContDiff ℝ 1 X) :
    IsGlobalFlow X (globalFlow X) :=
  Classical.epsilon_spec (exists_isGlobalFlow_of_hasCompactSupport hc hX)

end compact
/-! ## 4. The contact identity for a jointly smooth global flow of `X_H` -/

section contact

variable {H : ℝ³ → ℝ} {φ : ℝ → ℝ³ → ℝ³}

/-- Time direction of the joint derivative: `DΦ(s,p)(1,0) = X_H(φ s p)` when `Φ = uncurry φ`. -/
lemma fderiv_uncurry_time (hφ : IsGlobalFlow (hamVF H) φ) (hs : ContDiff ℝ ∞ (uncurry φ)) (s : ℝ)
    (p : ℝ³) : fderiv ℝ (uncurry φ) (s, p) (1, 0) = hamVF H (φ s p) := by
  have hd : HasFDerivAt (uncurry φ) (fderiv ℝ (uncurry φ) (s, p)) (s, p) :=
    (hs.differentiable (by simp) (s, p)).hasFDerivAt
  have hc : HasDerivAt (fun s : ℝ => (s, p)) ((1 : ℝ), (0 : ℝ³)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s p)
  have h1 := hd.comp_hasDerivAt s hc
  exact h1.unique (hφ.hasDerivAt s p)

/-- Space direction of the joint derivative: `Dφ_s(p) v = DΦ(s,p)(0,v)`. -/
lemma fderiv_flow_space (hs : ContDiff ℝ ∞ (uncurry φ)) (s : ℝ) (p v : ℝ³) :
    fderiv ℝ (φ s) p v = fderiv ℝ (uncurry φ) (s, p) (0, v) := by
  have hd : HasFDerivAt (uncurry φ) (fderiv ℝ (uncurry φ) (s, p)) (s, p) :=
    (hs.differentiable (by simp) (s, p)).hasFDerivAt
  have h : HasFDerivAt (φ s)
      ((fderiv ℝ (uncurry φ) (s, p)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ³)) p :=
    hd.comp p (hasFDerivAt_prodMk_right s p)
  rw [h.fderiv]; simp

/-- `φ s` is smooth when the flow is jointly smooth. -/
lemma contDiff_flow_space (hs : ContDiff ℝ ∞ (uncurry φ)) (s : ℝ) : ContDiff ℝ ∞ (φ s) :=
  hs.comp (contDiff_const.prodMk contDiff_id)

lemma minSmoothness_two_le : minSmoothness ℝ 2 ≤ ∞ := by
  simp [minSmoothness_of_isRCLikeNormedField]

/-- The variational equation `∂_s (Dφ_s(p) v) = DX_H(φ_s p) (Dφ_s(p) v)`, from the symmetry of
the second derivative of the jointly smooth `Φ = uncurry φ`. -/
lemma hasDerivAt_fderiv_flow (hφ : IsGlobalFlow (hamVF H) φ) (hs : ContDiff ℝ ∞ (uncurry φ))
    (hH : ContDiff ℝ ∞ H) (s : ℝ) (p v : ℝ³) :
    HasDerivAt (fun s => fderiv ℝ (φ s) p v)
      (fderiv ℝ (hamVF H) (φ s p) (fderiv ℝ (φ s) p v)) s := by
  have hD1 : ContDiff ℝ ∞ (fderiv ℝ (uncurry φ)) := hs.fderiv_right (m := ∞) (by simp)
  have hDd : HasFDerivAt (fderiv ℝ (uncurry φ)) (fderiv ℝ (fderiv ℝ (uncurry φ)) (s, p)) (s, p) :=
    (hD1.differentiable (by simp) _).hasFDerivAt
  have hc : HasDerivAt (fun s : ℝ => (s, p)) ((1 : ℝ), (0 : ℝ³)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s p)
  -- the `s`-derivative of `s ↦ DΦ (s,p) (0,v)`
  have hDs : HasDerivAt (fun s => fderiv ℝ (uncurry φ) (s, p))
      (fderiv ℝ (fderiv ℝ (uncurry φ)) (s, p) (1, 0)) s := hDd.comp_hasDerivAt s hc
  have h1 : HasDerivAt (fun s => fderiv ℝ (uncurry φ) (s, p) (0, v))
      (fderiv ℝ (fderiv ℝ (uncurry φ)) (s, p) (1, 0) (0, v)) s := by
    have h := hDs.clm_apply (hasDerivAt_const s ((0 : ℝ), v))
    refine h.congr_deriv ?_
    simp
  -- symmetry of the second derivative
  have hsymm : fderiv ℝ (fderiv ℝ (uncurry φ)) (s, p) (1, 0) (0, v) =
      fderiv ℝ (fderiv ℝ (uncurry φ)) (s, p) (0, v) (1, 0) :=
    (hs.contDiffAt.isSymmSndFDerivAt minSmoothness_two_le) _ _
  -- the map `q ↦ DΦ q (1,0)` is `X_H ∘ Φ`
  have hXΦ : (fun q : ℝ × ℝ³ => fderiv ℝ (uncurry φ) q (1, 0)) =
      fun q => hamVF H (uncurry φ q) := by
    funext q
    exact fderiv_uncurry_time hφ hs q.1 q.2
  have hA : HasFDerivAt (fun q : ℝ × ℝ³ => fderiv ℝ (uncurry φ) q (1, 0))
      ((fderiv ℝ (fderiv ℝ (uncurry φ)) (s, p)).flip (1, 0)) (s, p) := by
    have h := hDd.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : ℝ³)) (s, p))
    refine h.congr_fderiv ?_
    simp
  have hB : HasFDerivAt (fun q : ℝ × ℝ³ => hamVF H (uncurry φ q))
      ((fderiv ℝ (hamVF H) (uncurry φ (s, p))).comp (fderiv ℝ (uncurry φ) (s, p))) (s, p) :=
    ((contDiff_hamVF hH).differentiable (by simp) _).hasFDerivAt.comp (s, p)
      (hs.differentiable (by simp) _).hasFDerivAt
  have hAB : (fderiv ℝ (fderiv ℝ (uncurry φ)) (s, p)).flip (1, 0) =
      (fderiv ℝ (hamVF H) (uncurry φ (s, p))).comp (fderiv ℝ (uncurry φ) (s, p)) := by
    rw [hXΦ] at hA
    exact hA.unique hB
  have h2 : fderiv ℝ (fderiv ℝ (uncurry φ)) (s, p) (0, v) (1, 0) =
      fderiv ℝ (hamVF H) (φ s p) (fderiv ℝ (φ s) p v) := by
    have h := congrArg (fun T : ℝ × ℝ³ →L[ℝ] ℝ³ => T (0, v)) hAB
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply] at h
    rw [h, fderiv_flow_space hs]
    rfl
  have h3 : (fun s => fderiv ℝ (φ s) p v) = fun s => fderiv ℝ (uncurry φ) (s, p) (0, v) := by
    funext s; exact fderiv_flow_space hs s p v
  rw [h3, ← h2, ← hsymm]
  exact h1

/-- `α_q(DX_H(q) w) = dH_q(w) − H_y(q) w_y`: the `z`- and `x`-components of `X_H` are
`H + y X_x` and `X_x`, so the second derivatives of `H` cancel (sm-3:2599-2600). -/
lemma alpha_fderiv_hamVF (hH : ContDiff ℝ ∞ H) (q w : ℝ³) :
    alpha q (fderiv ℝ (hamVF H) q w) = fderiv ℝ H q w - pd H 1 q * w 1 := by
  have hX : DifferentiableAt ℝ (hamVF H) q := (contDiff_hamVF hH).differentiable (by simp) q
  have hpd : DifferentiableAt ℝ (pd H 1) q := (contDiff_pd hH 1).differentiable (by simp) q
  have hHd : DifferentiableAt ℝ H q := hH.differentiable (by simp) q
  have h2 : fderiv ℝ (hamVF H) q w 2 =
      fderiv ℝ H q w - (q 1 * fderiv ℝ (pd H 1) q w + pd H 1 q * w 1) := by
    rw [fderiv_apply_coord hX w 2]
    have : (fun q => hamVF H q 2) = H - (fun q : ℝ³ => q 1) * pd H 1 :=
      funext fun q => hamVF_apply_two H q
    rw [this, (hHd.hasFDerivAt.sub ((hasFDerivAt_coord 1 q).mul hpd.hasFDerivAt)).fderiv]
    simp
  have h0 : fderiv ℝ (hamVF H) q w 0 = -(fderiv ℝ (pd H 1) q w) := by
    rw [fderiv_apply_coord hX w 0]
    have : (fun q => hamVF H q 0) = -(pd H 1) := funext fun q => hamVF_apply_zero H q
    rw [this, hpd.hasFDerivAt.neg.fderiv]
    simp
  simp only [alpha, h2, h0]
  ring

/-- `dH_q(w) = H_x w_x + H_y w_y + H_z w_z`. -/
lemma fderiv_apply_expand (H : ℝ³ → ℝ) (q w : ℝ³) :
    fderiv ℝ H q w = pd H 0 q * w 0 + pd H 1 q * w 1 + pd H 2 q * w 2 := by
  have hw : w = w 0 • e 0 + w 1 • e 1 + w 2 • e 2 := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [hw]
  simp only [map_add, map_smul, pd, smul_eq_mul]
  ring

/-- The infinitesimal contact identity along the flow: with `β_s(v) = α_{φ_s p}(Dφ_s(p) v)`,
`β_s'(v) = H_z(φ_s p) β_s(v)`.  This is the coordinate form of `L_{X_H} α = H_z α`
(sm-3:2599-2601: `α(X_H) = H`, `ι_{X_H} dα = H_z α − dH`). -/
lemma hasDerivAt_alpha_flow (hφ : IsGlobalFlow (hamVF H) φ) (hs : ContDiff ℝ ∞ (uncurry φ))
    (hH : ContDiff ℝ ∞ H) (s : ℝ) (p v : ℝ³) :
    HasDerivAt (fun s => alpha (φ s p) (fderiv ℝ (φ s) p v))
      (pd H 2 (φ s p) * alpha (φ s p) (fderiv ℝ (φ s) p v)) s := by
  have hw' : HasDerivAt (fun s => fderiv ℝ (φ s) p v)
      (fderiv ℝ (hamVF H) (φ s p) (fderiv ℝ (φ s) p v)) s :=
    hasDerivAt_fderiv_flow hφ hs hH s p v
  have hq : HasDerivAt (fun s => φ s p) (hamVF H (φ s p)) s := hφ.hasDerivAt s p
  have h2 := hasDerivAt_coord hw' 2
  have h0 := hasDerivAt_coord hw' 0
  have hy := hasDerivAt_coord hq 1
  have this : HasDerivAt (fun s => alpha (φ s p) (fderiv ℝ (φ s) p v))
      (fderiv ℝ (hamVF H) (φ s p) (fderiv ℝ (φ s) p v) 2 -
        (hamVF H (φ s p) 1 * fderiv ℝ (φ s) p v 0 +
          φ s p 1 * fderiv ℝ (hamVF H) (φ s p) (fderiv ℝ (φ s) p v) 0)) s :=
    h2.sub (hy.mul h0)
  refine this.congr_deriv ?_
  have key := alpha_fderiv_hamVF hH (φ s p) (fderiv ℝ (φ s) p v)
  rw [fderiv_apply_expand] at key
  simp only [alpha] at key ⊢
  simp only [hamVF_apply_one]
  linear_combination key

/-- The conformal factor `c_s^H(p) = exp (∫_0^s H_z (φ_v p) dv)` (sm-3:2603-2606), for a given
flow `φ` of `X_H`. -/
def confFactorOf (H : ℝ³ → ℝ) (φ : ℝ → ℝ³ → ℝ³) (s : ℝ) (p : ℝ³) : ℝ :=
  Real.exp (∫ v in (0 : ℝ)..s, pd H 2 (φ v p))

/-- "it is positive" (sm-3:2606). -/
lemma confFactorOf_pos (H : ℝ³ → ℝ) (φ : ℝ → ℝ³ → ℝ³) (s : ℝ) (p : ℝ³) :
    0 < confFactorOf H φ s p := Real.exp_pos _

lemma confFactorOf_zero (H : ℝ³ → ℝ) (φ : ℝ → ℝ³ → ℝ³) (p : ℝ³) : confFactorOf H φ 0 p = 1 := by
  simp [confFactorOf]

lemma hasDerivAt_integral_pd (hφ : IsGlobalFlow (hamVF H) φ) (hH : ContDiff ℝ ∞ H) (p : ℝ³)
    (s : ℝ) : HasDerivAt (fun s => ∫ v in (0 : ℝ)..s, pd H 2 (φ v p)) (pd H 2 (φ s p)) s := by
  have hcont : Continuous fun v => pd H 2 (φ v p) :=
    (contDiff_pd hH 2).continuous.comp (hφ.continuous_time p)
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt

/-- "the resulting scalar ODE" (sm-3:2602): `∂_s c = (H_z ∘ φ_s) c`. -/
lemma hasDerivAt_confFactorOf (hφ : IsGlobalFlow (hamVF H) φ) (hH : ContDiff ℝ ∞ H) (p : ℝ³)
    (s : ℝ) : HasDerivAt (fun s => confFactorOf H φ s p)
      (pd H 2 (φ s p) * confFactorOf H φ s p) s := by
  have := (hasDerivAt_integral_pd hφ hH p s).exp
  simpa [confFactorOf, mul_comm] using this

/-- **The contact identity** `(φ_H^s)^*α = c_s^H α` (sm-3:2592, 2603-2605), for any jointly smooth
global flow `φ` of `X_H`: `α_{φ_s p}(Dφ_s(p) v) = c_s^H(p) · α_p(v)`. -/
theorem alpha_flow_eq (hφ : IsGlobalFlow (hamVF H) φ) (hs : ContDiff ℝ ∞ (uncurry φ))
    (hH : ContDiff ℝ ∞ H) (s : ℝ) (p v : ℝ³) :
    alpha (φ s p) (fderiv ℝ (φ s) p v) = confFactorOf H φ s p * alpha p v := by
  have hβ' : ∀ s, HasDerivAt (fun s => alpha (φ s p) (fderiv ℝ (φ s) p v))
      (pd H 2 (φ s p) * alpha (φ s p) (fderiv ℝ (φ s) p v)) s := fun s =>
    hasDerivAt_alpha_flow hφ hs hH s p v
  have hI' : ∀ s, HasDerivAt (fun s => ∫ v in (0 : ℝ)..s, pd H 2 (φ v p)) (pd H 2 (φ s p)) s :=
    hasDerivAt_integral_pd hφ hH p
  -- `β e^{−I}` has zero derivative, hence is constant
  have hg : ∀ s, HasDerivAt (fun s => alpha (φ s p) (fderiv ℝ (φ s) p v) *
      Real.exp (-(∫ v in (0 : ℝ)..s, pd H 2 (φ v p)))) 0 s := by
    intro s
    have h := (hβ' s).mul ((hI' s).neg.exp)
    refine h.congr_deriv ?_
    ring
  have hconst := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt)
    (fun s => (hg s).deriv) s 0
  have hβ0 : alpha (φ 0 p) (fderiv ℝ (φ 0) p v) = alpha p v := by
    have : φ 0 = id := funext hφ.zero
    rw [this, fderiv_id]
    simp
  simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one, hβ0] at hconst
  rw [confFactorOf, ← hconst, Real.exp_neg, mul_left_comm, mul_inv_cancel₀ (Real.exp_ne_zero _),
    mul_one]

/-- The conformal factor is smooth in `(s, p)` ("a smooth positive function", sm-3:2593): it equals
`α_{φ_s p}(Dφ_s(p) ∂_z)`, a polynomial expression in the jointly smooth flow and its derivative. -/
theorem contDiff_confFactorOf (hφ : IsGlobalFlow (hamVF H) φ) (hs : ContDiff ℝ ∞ (uncurry φ))
    (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ³ => confFactorOf H φ q.1 q.2) := by
  have heq : (fun q : ℝ × ℝ³ => confFactorOf H φ q.1 q.2) =
      fun q => alpha (uncurry φ q) (fderiv ℝ (uncurry φ) q (0, e 2)) := by
    funext ⟨s, p⟩
    show confFactorOf H φ s p = alpha (φ s p) (fderiv ℝ (uncurry φ) (s, p) (0, e 2))
    rw [← fderiv_flow_space hs s p (e 2), alpha_flow_eq hφ hs hH, alpha_e_two, mul_one]
  rw [heq]
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ³ => fderiv ℝ (uncurry φ) q (0, e 2)) :=
    (hs.contDiff_fderiv_apply (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)
  simp only [alpha]
  exact ((contDiff_coord 2).comp h1).sub
    (((contDiff_coord 1).comp hs).mul ((contDiff_coord 0).comp h1))

end contact

/-! ## 5. The flow of `X_H`, finite compositions, `C^k`-closeness -/

/-- The global flow `φ_H` of `X_H`. -/
def hamFlow (H : ℝ³ → ℝ) : ℝ → ℝ³ → ℝ³ := globalFlow (hamVF H)

/-- The conformal factor `c_s^H` of `φ_H^s`. -/
def confFactor (H : ℝ³ → ℝ) (s : ℝ) (p : ℝ³) : ℝ := confFactorOf H (hamFlow H) s p

/-- The printed hypotheses on `H` (sm-3:2587): "a smooth compactly supported `H : ℝ³ → ℝ`". -/
structure ContactMotionsHyp (H : ℝ³ → ℝ) : Prop where
  /-- sm-3:2587 "smooth". -/
  smooth : ContDiff ℝ ∞ H
  /-- sm-3:2587 "compactly supported". -/
  compactSupport : HasCompactSupport H

namespace ContactMotionsHyp

variable {H : ℝ³ → ℝ} (h : ContactMotionsHyp H)
include h

theorem contDiff_hamVF : ContDiff ℝ ∞ (hamVF H) := ContactMotions.contDiff_hamVF h.smooth

theorem hasCompactSupport_hamVF : HasCompactSupport (hamVF H) :=
  ContactMotions.hasCompactSupport_hamVF h.compactSupport

theorem exists_lipschitzWith : ∃ K : ℝ≥0, LipschitzWith K (hamVF H) :=
  exists_lipschitzWith_of_hasCompactSupport h.hasCompactSupport_hamVF
    (h.contDiff_hamVF.of_le (by simp))

/-- "has a global flow `φ_H^s`" (sm-3:2591): unconditional. -/
theorem isGlobalFlow : IsGlobalFlow (hamVF H) (hamFlow H) :=
  isGlobalFlow_globalFlow h.hasCompactSupport_hamVF (h.contDiff_hamVF.of_le (by simp))

theorem hamFlow_zero (p : ℝ³) : hamFlow H 0 p = p := h.isGlobalFlow.zero p

theorem hamFlow_add (s t : ℝ) (p : ℝ³) : hamFlow H (s + t) p = hamFlow H s (hamFlow H t p) := by
  obtain ⟨K, hK⟩ := h.exists_lipschitzWith
  exact h.isGlobalFlow.add hK s t p

theorem hamFlow_leftInverse (s : ℝ) : LeftInverse (hamFlow H (-s)) (hamFlow H s) := by
  obtain ⟨K, hK⟩ := h.exists_lipschitzWith
  exact h.isGlobalFlow.leftInverse hK s

theorem hamFlow_rightInverse (s : ℝ) : RightInverse (hamFlow H (-s)) (hamFlow H s) := by
  obtain ⟨K, hK⟩ := h.exists_lipschitzWith
  exact h.isGlobalFlow.rightInverse hK s

theorem hamFlow_bijective (s : ℝ) : Bijective (hamFlow H s) :=
  ⟨(h.hamFlow_leftInverse s).injective, (h.hamFlow_rightInverse s).surjective⟩

/-- Any global flow of `X_H` is `hamFlow H`. -/
theorem hamFlow_unique {ψ : ℝ → ℝ³ → ℝ³} (hψ : IsGlobalFlow (hamVF H) ψ) : ψ = hamFlow H := by
  obtain ⟨K, hK⟩ := h.exists_lipschitzWith
  exact h.isGlobalFlow.unique hK hψ

/-- `φ_H^s p` is `C^∞` in `s`: unconditional. -/
theorem contDiff_hamFlow_time (p : ℝ³) : ContDiff ℝ ∞ (fun s => hamFlow H s p) :=
  h.isGlobalFlow.contDiff_time h.contDiff_hamVF p

/-- The contact identity, given the joint smoothness of `φ_H`. -/
theorem contact_of_contDiff (hs : ContDiff ℝ ∞ (uncurry (hamFlow H))) (s : ℝ) (p v : ℝ³) :
    alpha (hamFlow H s p) (fderiv ℝ (hamFlow H s) p v) = confFactor H s p * alpha p v :=
  alpha_flow_eq h.isGlobalFlow hs h.smooth s p v

theorem contDiff_confFactor_of_contDiff (hs : ContDiff ℝ ∞ (uncurry (hamFlow H))) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ³ => confFactor H q.1 q.2) :=
  contDiff_confFactorOf h.isGlobalFlow hs h.smooth

end ContactMotionsHyp

theorem confFactor_pos (H : ℝ³ → ℝ) (s : ℝ) (p : ℝ³) : 0 < confFactor H s p :=
  confFactorOf_pos _ _ _ _

/-- The conformal factor is the printed exponential (sm-3:2603-2606). -/
theorem confFactor_eq (H : ℝ³ → ℝ) (s : ℝ) (p : ℝ³) :
    confFactor H s p = Real.exp (∫ v in (0 : ℝ)..s, pd H 2 (hamFlow H v p)) := rfl

/-- `composeFlows n Hs a p = φ_{H_0}^{a_0} (φ_{H_1}^{a_1} (⋯ (φ_{H_{n-1}}^{a_{n-1}} p)))`, the
"finite compositions of their small-time flows" (sm-3:2594). -/
def composeFlows : (n : ℕ) → (Fin n → ℝ³ → ℝ) → (Fin n → ℝ) → ℝ³ → ℝ³
  | 0, _, _, p => p
  | n + 1, Hs, a, p => hamFlow (Hs 0) (a 0) (composeFlows n (Fin.tail Hs) (Fin.tail a) p)

/-- Compositions depend smoothly on the times (and the point), given the joint smoothness of each
flow (sm-3:2594-2595 "depend smoothly on the times"). -/
theorem contDiff_composeFlows (n : ℕ) (Hs : Fin n → ℝ³ → ℝ)
    (h : ∀ i, ContDiff ℝ ∞ (uncurry (hamFlow (Hs i)))) :
    ContDiff ℝ ∞ (fun q : (Fin n → ℝ) × ℝ³ => composeFlows n Hs q.1 q.2) := by
  induction n with
  | zero => exact contDiff_snd
  | succ n ih =>
    have ih' := ih (Fin.tail Hs) (fun i => h i.succ)
    have hA : ContDiff ℝ ∞ (fun q : (Fin (n + 1) → ℝ) × ℝ³ => q.1 0) :=
      (contDiff_apply ℝ ℝ 0).comp contDiff_fst
    have hB : ContDiff ℝ ∞ (fun q : (Fin (n + 1) → ℝ) × ℝ³ => (Fin.tail q.1, q.2)) := by
      refine ContDiff.prodMk ?_ contDiff_snd
      exact contDiff_pi.2 fun i => (contDiff_apply ℝ ℝ i.succ).comp contDiff_fst
    exact (h 0).comp (hA.prodMk (ih'.comp hB))

/-- At zero times the composition is the identity. -/
theorem composeFlows_zero (n : ℕ) (Hs : Fin n → ℝ³ → ℝ) (h : ∀ i p, hamFlow (Hs i) 0 p = p)
    (p : ℝ³) : composeFlows n Hs 0 p = p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show hamFlow (Hs 0) 0 (composeFlows n (Fin.tail Hs) 0 p) = p
    rw [ih (Fin.tail Hs) (fun i => h i.succ), h 0]

/-- The iterated derivative of a partial map `p ↦ f (a, p)` is the iterated derivative of `f`
restricted to the `G`-directions. -/
lemma iteratedFDeriv_partial {A G F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : A × G → F} (hf : ContDiff ℝ ∞ f) (a : A) (j : ℕ) (p : G) :
    iteratedFDeriv ℝ j (fun p => f (a, p)) p =
      (iteratedFDeriv ℝ j f (a, p)).compContinuousLinearMap
        fun _ => ContinuousLinearMap.inr ℝ A G := by
  have h1 : (fun p => f (a, p)) = (fun z => f ((a, 0) + z)) ∘ (ContinuousLinearMap.inr ℝ A G) := by
    funext p; simp
  have hf' : ContDiff ℝ ∞ (fun z => f ((a, 0) + z)) := hf.comp (contDiff_const.add contDiff_id)
  rw [h1, (ContinuousLinearMap.inr ℝ A G).iteratedFDeriv_comp_right hf' p (by simp),
    iteratedFDeriv_comp_add_left]
  simp

/-- "arbitrarily `C^k`-close to the identity on compact sets for each fixed finite `k`"
(sm-3:2595-2596), given the joint smoothness of each flow. -/
theorem composeFlows_close (n : ℕ) (Hs : Fin n → ℝ³ → ℝ)
    (h : ∀ i, ContDiff ℝ ∞ (uncurry (hamFlow (Hs i)))) (h0 : ∀ i p, hamFlow (Hs i) 0 p = p)
    {K : Set ℝ³} (hK : IsCompact K) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a : Fin n → ℝ, (∀ i, |a i| < δ) → ∀ j ≤ k, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ j (fun p => composeFlows n Hs a p - p) p‖ < ε := by
  set G : (Fin n → ℝ) × ℝ³ → ℝ³ := fun q => composeFlows n Hs q.1 q.2 - q.2 with hG
  have hGs : ContDiff ℝ ∞ G := (contDiff_composeFlows n Hs h).sub contDiff_snd
  have hΨc : ∀ j : ℕ, Continuous fun q => (iteratedFDeriv ℝ j G q).compContinuousLinearMap
      (fun _ : Fin j => ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ³) := fun j =>
    (ContinuousMultilinearMap.compContinuousLinearMapL _).continuous.comp
      (hGs.continuous_iteratedFDeriv (by simp))
  have hform : ∀ (j : ℕ) (a : Fin n → ℝ) (p : ℝ³),
      iteratedFDeriv ℝ j (fun p => composeFlows n Hs a p - p) p =
        (iteratedFDeriv ℝ j G (a, p)).compContinuousLinearMap
          (fun _ : Fin j => ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ³) := fun j a p =>
    iteratedFDeriv_partial hGs a j p
  have hzero : ∀ (j : ℕ) (p : ℝ³), (iteratedFDeriv ℝ j G (0, p)).compContinuousLinearMap
      (fun _ : Fin j => ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ³) = 0 := by
    intro j p
    rw [← hform]
    have : (fun p => composeFlows n Hs 0 p - p) = fun _ => (0 : ℝ³) :=
      funext fun p => by rw [composeFlows_zero n Hs h0 p, sub_self]
    rw [this, iteratedFDeriv_fun_zero]
    rfl
  let U : Set ((Fin n → ℝ) × ℝ³) := ⋂ j ∈ Finset.range (k + 1),
    {q | ‖(iteratedFDeriv ℝ j G q).compContinuousLinearMap
      (fun _ : Fin j => ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ³)‖ < ε}
  have hU : IsOpen U := isOpen_biInter_finset fun j _ => isOpen_lt (hΨc j).norm continuous_const
  have hsub : ({0} : Set (Fin n → ℝ)) ×ˢ K ⊆ U := by
    rintro ⟨a, p⟩ ⟨ha, hp⟩
    simp only [mem_singleton_iff] at ha
    subst ha
    simp only [U, mem_iInter, Set.mem_ofPred_eq]
    intro j _
    rw [hzero j p, norm_zero]; exact hε
  obtain ⟨u, v, hu, -, h0u, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hU hsub
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hu 0 (h0u rfl)
  refine ⟨δ, hδ, fun a ha j hj p hp => ?_⟩
  have haU : (a, p) ∈ U := by
    refine huv ⟨hball ?_, hKv hp⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact (pi_norm_lt_iff hδ).2 fun i => by simpa using ha i
  simp only [U, mem_iInter, Set.mem_ofPred_eq] at haU
  rw [hform]
  exact haU j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

end ContactMotions

/-! ## 6. The gap, the bundle, the row -/

open ContactMotions

/-- **The one missing Mathlib fact** (explicit hypothesis, no placeholder declaration): smooth
dependence of the flow on the initial point.  For a `C^∞` compactly supported vector field on
`ℝ³`, every global flow (there is exactly one, `IsGlobalFlow.unique`) is `C^∞` jointly in
`(s, p)`.  Mathlib (this pin) has existence, uniqueness, Grönwall (Lipschitz dependence on the
initial point) and `C^∞` dependence on time, but not this ("Smooth ODE dependence", sm-3:2611). -/
def SmoothDependence : Prop :=
  ∀ X : ℝ³ → ℝ³, ContDiff ℝ ∞ X → HasCompactSupport X →
    ∀ φ : ℝ → ℝ³ → ℝ³, IsGlobalFlow X φ → ContDiff ℝ ∞ (uncurry φ)

/-- fd:contact-motions (sm-3:2586-2597), one field per printed clause.  `hamFlow H = φ_H`,
`confFactor H s p = c_s^H(p) = exp ∫_0^s H_z ∘ φ_H^v`, `alpha p v = α_p(v) = v_z − p_y v_x`,
`composeFlows n Hs a = φ_{H_0}^{a_0} ∘ ⋯ ∘ φ_{H_{n-1}}^{a_{n-1}}`. -/
structure ContactMotionsData : Prop where
  /-- sm-3:2591 "has a global flow `φ_H^s`": `φ_H^0 = id`, `∂_s φ_H^s p = X_H(φ_H^s p)` on all of
  `ℝ × ℝ³`. -/
  isGlobalFlow : ∀ H, ContactMotionsHyp H → IsGlobalFlow (hamVF H) (hamFlow H)
  /-- sm-3:2591 "flow": the group law `φ_H^{s+t} = φ_H^s ∘ φ_H^t`. -/
  flow_add : ∀ H, ContactMotionsHyp H → ∀ s t p, hamFlow H (s + t) p = hamFlow H s (hamFlow H t p)
  /-- sm-3:2591-2592 "diffeomorphisms": `φ_H^s` is `C^∞` (jointly in `(s, p)`), and `φ_H^{−s}` is
  its (`C^∞`) two-sided inverse. -/
  diffeo : ∀ H, ContactMotionsHyp H → ContDiff ℝ ∞ (uncurry (hamFlow H)) ∧
    ∀ s, ContDiff ℝ ∞ (hamFlow H s) ∧ ContDiff ℝ ∞ (hamFlow H (-s)) ∧
      LeftInverse (hamFlow H (-s)) (hamFlow H s) ∧ RightInverse (hamFlow H (-s)) (hamFlow H s)
  /-- sm-3:2591-2593 "contact … for `α = dz − y dx`: `(φ_H^s)^*α = c_s^H α`": for every `p, v`,
  `α_{φ_H^s p}(Dφ_H^s(p) v) = c_s^H(p) α_p(v)`. -/
  contact : ∀ H, ContactMotionsHyp H → ∀ s p v,
    alpha (hamFlow H s p) (fderiv ℝ (hamFlow H s) p v) = confFactor H s p * alpha p v
  /-- sm-3:2591 "coorientation-preserving", sm-3:2593 "positive": `c_s^H > 0`. -/
  confFactor_pos : ∀ H, ContactMotionsHyp H → ∀ s p, 0 < confFactor H s p
  /-- sm-3:2593 "with a smooth positive function `c_s^H`": `c` is `C^∞` in `(s, p)`. -/
  confFactor_smooth : ∀ H, ContactMotionsHyp H →
    ContDiff ℝ ∞ (fun q : ℝ × ℝ³ => confFactor H q.1 q.2)
  /-- sm-3:2594-2595 "Finite compositions of their small-time flows depend smoothly on the times":
  `(a, p) ↦ φ_{H_0}^{a_0} ∘ ⋯ ∘ φ_{H_{n-1}}^{a_{n-1}} (p)` is `C^∞` on `ℝ^n × ℝ³`. -/
  compositions_smooth : ∀ (n : ℕ) (Hs : Fin n → ℝ³ → ℝ), (∀ i, ContactMotionsHyp (Hs i)) →
    ContDiff ℝ ∞ (fun q : (Fin n → ℝ) × ℝ³ => composeFlows n Hs q.1 q.2)
  /-- sm-3:2595-2596 "and are arbitrarily `C^k`-close to the identity on compact sets for each
  fixed finite `k`": for every compact `K`, `k`, `ε > 0` there is `δ > 0` such that all times
  `|a_i| < δ` give `‖D^j(Φ_a − id)(p)‖ < ε` for `j ≤ k`, `p ∈ K`. -/
  compositions_close : ∀ (n : ℕ) (Hs : Fin n → ℝ³ → ℝ), (∀ i, ContactMotionsHyp (Hs i)) →
    ∀ K : Set ℝ³, IsCompact K → ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∃ δ > 0, ∀ a : Fin n → ℝ,
      (∀ i, |a i| < δ) → ∀ j ≤ k, ∀ p ∈ K,
        ‖iteratedFDeriv ℝ j (fun p => composeFlows n Hs a p - p) p‖ < ε

/-- Under `SmoothDependence`, `φ_H` is jointly smooth. -/
theorem ContactMotions.ContactMotionsHyp.contDiff_uncurry_hamFlow (hsd : SmoothDependence)
    {H : ℝ³ → ℝ}
    (h : ContactMotionsHyp H) : ContDiff ℝ ∞ (uncurry (hamFlow H)) :=
  hsd _ h.contDiff_hamVF h.hasCompactSupport_hamVF _ h.isGlobalFlow

/-- **fd:contact-motions** (sm-3:2586-2597): the row, modulo the one explicit hypothesis
`SmoothDependence`. -/
theorem fd_contact_motions (hsd : SmoothDependence) : ContactMotionsData where
  isGlobalFlow _ h := h.isGlobalFlow
  flow_add _ h := h.hamFlow_add
  diffeo _ h := ⟨h.contDiff_uncurry_hamFlow hsd, fun s =>
    ⟨contDiff_flow_space (h.contDiff_uncurry_hamFlow hsd) s,
      contDiff_flow_space (h.contDiff_uncurry_hamFlow hsd) (-s),
      h.hamFlow_leftInverse s, h.hamFlow_rightInverse s⟩⟩
  contact _ h := h.contact_of_contDiff (h.contDiff_uncurry_hamFlow hsd)
  confFactor_pos H _ := confFactor_pos H
  confFactor_smooth _ h := h.contDiff_confFactor_of_contDiff (h.contDiff_uncurry_hamFlow hsd)
  compositions_smooth n Hs h := contDiff_composeFlows n Hs fun i => (h i).contDiff_uncurry_hamFlow hsd
  compositions_close n Hs h _ hK k _ hε :=
    composeFlows_close n Hs (fun i => (h i).contDiff_uncurry_hamFlow hsd)
      (fun i => (h i).hamFlow_zero) hK k hε

end

end SM
