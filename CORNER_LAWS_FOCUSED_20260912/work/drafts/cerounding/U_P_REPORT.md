# U_P_REPORT — unit P (cutoff), ce:rounding (row 89)

Unit P prover (pod subagent), 2026-09-14 09:15 UTC / 5:15am ET.  File: `work/drafts/cerounding/U_P.lean` (copy of
`Skeleton_FINAL.lean`; only the three U-P `sorry` bodies replaced, two helpers added).
Check: `cd work/lean && lake env lean ../drafts/cerounding/U_P.lean` — exit 0, **0 errors**; `grep -c sorry`
37 → 34 (the 4 non-leaf occurrences are in the header comment; the 30 remaining leaf `sorry`s are other units').
`diff Skeleton_FINAL.lean U_P.lean` removes exactly the three lines `  sorry` at skeleton lines 222, 227, 232;
everything else is additions.  No statement, name, definition or docstring changed.

## 1. Leaves proved (3/3)

| leaf | U_P.lean line | proof idea |
|---|---|---|
| `periodicBump_zero` | 231 | `cos 0 = 1 ≥ cos πr` ⇒ argument `≥ 1` ⇒ `smoothTransition.one_of_one_le` |
| `periodicBump_eq_one` | 248 | `cos 2πs = cos 2π\|s−n\|` and `2π\|s−n\| ≤ πr ≤ π` ⇒ `cos 2πs ≥ cos πr` (`cos_le_cos_of_nonneg_of_le_pi`) ⇒ argument `≥ 1` |
| `periodicBump_eq_zero` | 260 | `n := round s`, `\|s − round s\| ≤ 1/2` (`abs_sub_round`), `r ≤ \|s−n\|` ⇒ `2πr ≤ 2π\|s−n\| ≤ π` ⇒ `cos 2πs ≤ cos 2πr` ⇒ argument `≤ 0` ⇒ `zero_of_nonpos` |

Axioms of the three: standard (no `sorryAx`; the file's `#print axioms SM.ce_rounding` still shows `sorryAx` from
the other units, as expected).

## 2. Helpers added (both in `namespace SpatialLink`, immediately before the first leaf using them)

- `up_denom_pos {r} (hr : 0 < r) (hr' : r < 1/2) : 0 < cos (π r) − cos (2 π r)` (line 222, before
  `periodicBump_zero`) — `cos_lt_cos_of_nonneg_of_le_pi` with `0 ≤ πr`, `2πr ≤ π`, `πr < 2πr` (nlinarith with `pi_pos`).
- `up_cos_eq_cos_abs (s : ℝ) (n : ℤ) : cos (2 π s) = cos (2 π \|s − n\|)` (line 239, before
  `periodicBump_eq_one`) — `abs_mul`, `Real.cos_abs`, `Real.cos_sub_int_mul_two_pi`.

Text as inserted:

```lean
/-- (U-P helper) the denominator of the cutoff is positive: `cos πr > cos 2πr` for `0 < r < 1/2`
(`cos` strictly decreasing on `[0, π]`, `πr < 2πr ≤ π`) -/
theorem up_denom_pos {r : ℝ} (hr : 0 < r) (hr' : r < 1 / 2) :
    0 < Real.cos (Real.pi * r) - Real.cos (2 * Real.pi * r) := by
  have hpi := Real.pi_pos
  have h1 : 0 ≤ Real.pi * r := by positivity
  have h2 : 2 * Real.pi * r ≤ Real.pi := by nlinarith
  have h3 : Real.pi * r < 2 * Real.pi * r := by nlinarith
  linarith [Real.cos_lt_cos_of_nonneg_of_le_pi h1 h2 h3]

/-- `ρ(0) = 1` ("equal to one near zero"; `cos 0 = 1 ≥ cos πr`) -/
theorem periodicBump_zero {r : ℝ} (hr : 0 < r) (hr' : r < 1 / 2) : periodicBump r 0 = 1 := by
  unfold periodicBump
  apply Real.smoothTransition.one_of_one_le
  rw [one_le_div (up_denom_pos hr hr'), mul_zero, Real.cos_zero]
  linarith [Real.cos_le_one (Real.pi * r)]

/-- (U-P helper) `cos 2πs` depends on `s` only modulo `ℤ`, and then only on `|s − n|`
(`2π`-periodicity and evenness of `cos`) -/
theorem up_cos_eq_cos_abs (s : ℝ) (n : ℤ) :
    Real.cos (2 * Real.pi * s) = Real.cos (2 * Real.pi * |s - n|) := by
  have h : 2 * Real.pi * |s - n| = |2 * Real.pi * (s - n)| := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  rw [h, Real.cos_abs]
  have : 2 * Real.pi * (s - n) = 2 * Real.pi * s - n * (2 * Real.pi) := by ring
  rw [this, Real.cos_sub_int_mul_two_pi]

/-- `ρ = 1` on `dist(s, ℤ) ≤ r/2` -/
theorem periodicBump_eq_one {r : ℝ} (hr : 0 < r) (hr' : r < 1 / 2) {s : ℝ} {n : ℤ}
    (hs : |s - n| ≤ r / 2) : periodicBump r s = 1 := by
  unfold periodicBump
  apply Real.smoothTransition.one_of_one_le
  rw [one_le_div (up_denom_pos hr hr'), up_cos_eq_cos_abs s n]
  have hpi := Real.pi_pos
  have h1 : 0 ≤ 2 * Real.pi * |s - n| := by positivity
  have h2 : Real.pi * r ≤ Real.pi := by nlinarith
  have h3 : 2 * Real.pi * |s - n| ≤ Real.pi * r := by nlinarith
  linarith [Real.cos_le_cos_of_nonneg_of_le_pi h1 h2 h3]

/-- "with support strictly inside": `ρ = 0` where `dist(s, ℤ) ≥ r` -/
theorem periodicBump_eq_zero {r : ℝ} (hr : 0 < r) (hr' : r < 1 / 2) {s : ℝ}
    (hs : ∀ n : ℤ, r ≤ |s - n|) : periodicBump r s = 0 := by
  unfold periodicBump
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ (up_denom_pos hr hr').le
  rw [up_cos_eq_cos_abs s (round s)]
  have hpi := Real.pi_pos
  have hle := abs_sub_round s
  have hge := hs (round s)
  have h1 : 0 ≤ 2 * Real.pi * r := by positivity
  have h2 : 2 * Real.pi * |s - round s| ≤ Real.pi := by nlinarith
  have h3 : 2 * Real.pi * r ≤ 2 * Real.pi * |s - round s| := by nlinarith
  linarith [Real.cos_le_cos_of_nonneg_of_le_pi h1 h2 h3]
```

## 3. Mathlib pitfalls / notes for the assembler

- `one_le_div (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a` (Semifield version) is the convenient form; `one_le_div_iff` is
  the two-case disjunction and is awkward.  `div_nonpos_of_nonpos_of_nonneg : a ≤ 0 → 0 ≤ b → a / b ≤ 0`.
- `Real.cos_abs` rewrites `cos |x|`, so to move from `cos (2π|s−n|)` one must first rewrite `2π|s−n| = |2π(s−n)|`
  (`abs_mul`, `abs_of_pos`); the `←` direction of `cos_abs` does not fire on a target without an `abs`.
- Periodicity: `Real.cos_sub_int_mul_two_pi (x) (n : ℤ) : cos (x − n * (2π)) = cos x`; the argument must be
  reshaped with `ring` first (`2π(s − n) = 2πs − n·(2π)`).
- `abs_sub_round (x) : |x − round x| ≤ 1/2` (generic `FloorRing`), exactly the `round` fact needed for
  `periodicBump_eq_zero`.
- All the trigonometric inequalities go through `nlinarith` given `Real.pi_pos` in context (products `π * r` etc.).
- The full compile of U_P.lean takes ~9 s here (oleans cached), not 1 min.

## 4. FALLBACK: unit G (U-G) — all 10 leaves proved in a scratch file

Scratch: `/tmp/up/ug_scratch.lean` = header (same three imports, `namespace SM … namespace SpatialLink`,
`variable {c} (L)`) + skeleton lines 240-397 (the whole §4.2 through `end GermData`) with the 10 `sorry`s
replaced; `lake env lean` exit 0, **0 errors, 0 sorry**; `#print axioms` of `exists_germData`,
`u_strictMonoOn_or_strictAntiOn`, `chart_proj`, `abs_u_le_M` = `[propext, Classical.choice, Quot.sound]`.
I did NOT edit `U_G.lean`.

Leaves proved: `exists_germData`, `chart_proj`, `u_strictMonoOn_or_strictAntiOn`, `rect_subset_closedBall`,
`uMin_neg`, `uMax_pos`, `u_mem_Icc_of_mem`, `mem_Icc_of_u_mem`, `u_mem_Ioo_of_mem`, `abs_u_le_M`.

Helpers (all in `namespace GermData`, immediately before `u_strictMonoOn_or_strictAntiOn`):
`ug_exists_deriv_eq_slope`, `ug_strictMonoOn_of_deriv_pos`, `ug_strictAntiOn_of_deriv_neg`, `ug_deriv_u`,
`ug_deriv_u_pos_or_neg`.  The leaf's own docstring is byte-identical and sits directly above the leaf (i.e. after
the helpers), as Lean requires.

**IMPORTANT pitfall for U-G (whoever assembles it):** the plan's tools `strictMonoOn_of_deriv_pos` /
`strictAntiOn_of_deriv_neg` (Mathlib.Analysis.Calculus.Deriv.MeanValue) are **NOT in the import closure** of the
skeleton's three imports (`#check` fails: unknown identifier), nor are `exists_deriv_eq_slope` /
`exists_hasDerivAt_eq_slope`.  Rolle IS available (`exists_deriv_eq_zero`, via SM.FrontSmooth →
Mathlib.Analysis.Calculus.LocalExtr.Rolle), so the fallback reproves Lagrange from Rolle exactly as
SM/Curl.lean 784-826 does (`g_exists_hasDerivAt_eq_slope`, not importable either: SM.Curl is not in the closure).
No new import is needed with this route.  Other U-G notes:
- One-sign of `u'` on `J`: `IsPreconnected.intermediate_value` (available) with `ContDiff.continuous_deriv hu (by simp)`
  (the side goal `1 ≤ ∞` closes by `simp`; `le_top` does NOT work since `∞ = ↑⊤ ≠ ⊤` in `WithTop ℕ∞`), plus
  `ContDiff.differentiable hu (by simp)` for `∞ ≠ 0`.
- `deriv g.u t = deriv (yOf (L.T i)) t` is `deriv_sub_const _` after `show deriv (fun s => yOf (L.T i) s - g.y₀) t = _`.
- `chart_proj`: `simp only [chart, xzOf, xOf, zOf, u, x₀, y₀, z₀]` (do NOT unfold `yOf`, so that `rw [g.formula t ht]`
  rewrites only the two exposed `L.T i t`), then `ext <;> simp only <;> field_simp <;> ring`.
- `StrictAntiOn.le_iff_le` does not exist; the anti versions are `StrictAntiOn.le_iff_ge` / `StrictAntiOn.lt_iff_gt`.
- `Odd.pow_le_pow (hn : Odd n) : a ^ n ≤ b ^ n ↔ a ≤ b` (an iff, use `.mpr`) and `Odd.neg_pow` for the
  `−M³ ≤ u₋³` bound in `rect_subset_closedBall`; membership in `rect` via
  `simp only [rect, Set.mem_prod, Set.mem_Icc] at hp`; the sup norm via `mem_closedBall_zero_iff, Prod.norm_def,
  Real.norm_eq_abs`.
- `hu.1`/`hu.2` on `hu : x ∈ Set.Icc a b` works by defeq; `⟨_, _⟩` for `t ∈ g.J` works by defeq as in `t₀_mem_J`.

### U-G proof text (paste over skeleton lines 259-397 of the U-G copy; only `sorry` bodies replaced, helpers added)

```lean
/-- the printed hypothesis supplies the data (shrink `δ` to `min δ (1/3)`) -/
theorem exists_germData {i : Fin c} {t₀ : ℝ} (h : L.ExactCuspGerm i t₀) :
    Nonempty (L.GermData i t₀) := by
  obtain ⟨A, δ, hA, hδ, hy, hf⟩ := h
  have hsub : Set.Ioo (t₀ - min δ (1 / 3)) (t₀ + min δ (1 / 3)) ⊆ Set.Ioo (t₀ - δ) (t₀ + δ) :=
    Set.Ioo_subset_Ioo (by linarith [min_le_left δ (1 / 3)]) (by linarith [min_le_left δ (1 / 3)])
  exact ⟨{ A := A, δ := min δ (1 / 3), A_ne := hA, δ_pos := lt_min hδ (by norm_num),
           δ_le := min_le_right _ _,
           y_deriv_ne := fun t ht => hy t (hsub ht),
           formula := fun t ht => hf t (hsub ht) }⟩

namespace GermData

variable {L} {i : Fin c} {t₀ : ℝ}

/-- `x₀` (the germ data only fixes the cusp; the argument is for field notation) -/
def x₀ (_g : L.GermData i t₀) : ℝ := (L.T i t₀).1
/-- `y₀` -/
def y₀ (_g : L.GermData i t₀) : ℝ := yOf (L.T i) t₀
/-- `z₀` -/
def z₀ (_g : L.GermData i t₀) : ℝ := (L.T i t₀).2.2

variable (g : L.GermData i t₀)
/-- the chart coordinate `u = y − y₀`, as a function of the parameter -/
def u (t : ℝ) : ℝ := yOf (L.T i) t - g.y₀
/-- the chart interval -/
def J : Set ℝ := Set.Ioo (t₀ - g.δ) (t₀ + g.δ)
/-- ce:positive-chart: `X = (x − x₀)/A`, `Z = 3(z − z₀ − y₀(x − x₀))/(2A)` -/
def chart (p : Plane) : Plane :=
  ((p.1 - g.x₀) / g.A, 3 * (p.2 - g.z₀ - g.y₀ * (p.1 - g.x₀)) / (2 * g.A))
/-- its affine inverse -/
def unchart (w : Plane) : Plane :=
  (g.x₀ + g.A * w.1, g.z₀ + g.y₀ * g.A * w.1 + (2 * g.A / 3) * w.2)

theorem u_t₀ : g.u t₀ = 0 := by simp [u, y₀]

theorem u_smooth : ContDiff ℝ ∞ g.u := ((L.smooth i).snd.fst).sub contDiff_const

theorem t₀_mem_J : t₀ ∈ g.J := ⟨by linarith [g.δ_pos], by linarith [g.δ_pos]⟩

theorem isOpen_J : IsOpen g.J := isOpen_Ioo

theorem chart_unchart (w : Plane) : g.chart (g.unchart w) = w := by
  have hA := g.A_ne
  ext <;> simp only [chart, unchart] <;> field_simp <;> ring

theorem unchart_chart (p : Plane) : g.unchart (g.chart p) = p := by
  have hA := g.A_ne
  ext <;> simp only [chart, unchart] <;> field_simp <;> ring

theorem chart_injective : Function.Injective g.chart :=
  Function.LeftInverse.injective g.unchart_chart

theorem unchart_continuous : Continuous g.unchart := by
  unfold unchart; fun_prop

theorem chart_continuous : Continuous g.chart := by
  unfold chart; fun_prop

/-- "sends the front to `(u², u³)`" -/
theorem chart_proj {t : ℝ} (ht : t ∈ g.J) : g.chart (xzOf (L.T i) t) = (g.u t ^ 2, g.u t ^ 3) := by
  have hA := g.A_ne
  have hf := g.formula t ht
  simp only [chart, xzOf, xOf, zOf, u, x₀, y₀, z₀]
  rw [hf]
  ext <;> simp only <;> field_simp <;> ring

/-- the chart is affine: the displacement `(s, 0, y₀ s)` (physical, ce:physical-displacement) is the
normalized displacement `(s, 0)` -/
theorem chart_add_disp (p : Plane) (s : ℝ) :
    g.chart (p + s • ((g.A : ℝ), g.A * g.y₀)) = g.chart p + (s, 0) := by
  have hA := g.A_ne
  ext <;> simp only [chart, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, Prod.fst_zero,
    Prod.snd_zero] <;> field_simp <;> ring

/-- (U-G helper) Lagrange's mean value theorem for a differentiable function, from Rolle
(`exists_deriv_eq_zero`; Mathlib's `exists_deriv_eq_slope` / `strictMonoOn_of_deriv_pos` are
outside the import closure, as in SM/Curl.lean) -/
theorem ug_exists_deriv_eq_slope {f : ℝ → ℝ} (hf : Differentiable ℝ f) {a b : ℝ} (hab : a < b) :
    ∃ c ∈ Set.Ioo a b, deriv f c * (b - a) = f b - f a := by
  set m := (f b - f a) / (b - a) with hm
  have hba : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  have hd : ∀ x, HasDerivAt (fun x => f x - m * (x - a)) (deriv f x - m) x := fun x => by
    have h1 : HasDerivAt (fun x => m * (x - a)) (m * 1) x :=
      ((hasDerivAt_id x).sub_const a).const_mul m
    exact ((hf x).hasDerivAt.sub h1).congr_deriv (by ring)
  have hc : ContinuousOn (fun x => f x - m * (x - a)) (Set.Icc a b) :=
    (hf.continuous.sub (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
  have hI : f a - m * (a - a) = f b - m * (b - a) := by
    rw [hm, sub_self, mul_zero, sub_zero, div_mul_cancel₀ _ hba]; ring
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_zero hab hc hI
  refine ⟨c, hc, ?_⟩
  rw [(hd c).deriv] at hc'
  have : deriv f c = m := by linarith
  rw [this, hm, div_mul_cancel₀ _ hba]

/-- (U-G helper) strict monotonicity on an open interval from a positive derivative -/
theorem ug_strictMonoOn_of_deriv_pos {f : ℝ → ℝ} (hf : Differentiable ℝ f) {a b : ℝ}
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < deriv f x) : StrictMonoOn f (Set.Ioo a b) := by
  intro x hx y hy hxy
  obtain ⟨c, hc, hc'⟩ := ug_exists_deriv_eq_slope hf hxy
  have h1 := hpos c ⟨hx.1.trans hc.1, hc.2.trans hy.2⟩
  have h2 := mul_pos h1 (sub_pos.mpr hxy)
  linarith

/-- (U-G helper) strict antitonicity on an open interval from a negative derivative -/
theorem ug_strictAntiOn_of_deriv_neg {f : ℝ → ℝ} (hf : Differentiable ℝ f) {a b : ℝ}
    (hneg : ∀ x ∈ Set.Ioo a b, deriv f x < 0) : StrictAntiOn f (Set.Ioo a b) := by
  intro x hx y hy hxy
  obtain ⟨c, hc, hc'⟩ := ug_exists_deriv_eq_slope hf hxy
  have h1 := hneg c ⟨hx.1.trans hc.1, hc.2.trans hy.2⟩
  have h2 := mul_neg_of_neg_of_pos h1 (sub_pos.mpr hxy)
  linarith

/-- (U-G helper) `u' = y'` -/
theorem ug_deriv_u (t : ℝ) : deriv g.u t = deriv (yOf (L.T i)) t := by
  show deriv (fun s => yOf (L.T i) s - g.y₀) t = _
  exact deriv_sub_const _

/-- (U-G helper) `u'` is continuous and vanishes nowhere on `J`, so it has one sign there (IVT on the
connected interval) -/
theorem ug_deriv_u_pos_or_neg :
    (∀ t ∈ g.J, 0 < deriv g.u t) ∨ (∀ t ∈ g.J, deriv g.u t < 0) := by
  have hu : ContDiff ℝ ∞ g.u := g.u_smooth
  have hcont : Continuous (deriv g.u) := hu.continuous_deriv (by simp)
  have hne : ∀ t ∈ g.J, deriv g.u t ≠ 0 := fun t ht => by
    rw [ug_deriv_u]; exact g.y_deriv_ne t ht
  have hJ : IsPreconnected g.J := isPreconnected_Ioo
  rcases lt_or_gt_of_ne (hne t₀ g.t₀_mem_J) with h0 | h0
  · right
    intro t ht
    by_contra hcon
    push Not at hcon
    have hmem : (0:ℝ) ∈ Set.Icc (deriv g.u t₀) (deriv g.u t) := ⟨h0.le, hcon⟩
    obtain ⟨s, hs, hs0⟩ := hJ.intermediate_value g.t₀_mem_J ht hcont.continuousOn hmem
    exact hne s hs hs0
  · left
    intro t ht
    by_contra hcon
    push Not at hcon
    have hmem : (0:ℝ) ∈ Set.Icc (deriv g.u t) (deriv g.u t₀) := ⟨hcon, h0.le⟩
    obtain ⟨s, hs, hs0⟩ := hJ.intermediate_value ht g.t₀_mem_J hcont.continuousOn hmem
    exact hne s hs hs0

/-- `u` is strictly monotone or strictly antitone on the chart interval (`u' = y' ≠ 0` there,
continuous, so of one sign: "The coordinate u may increase or decrease") -/
theorem u_strictMonoOn_or_strictAntiOn : StrictMonoOn g.u g.J ∨ StrictAntiOn g.u g.J := by
  have hdiff : Differentiable ℝ g.u := g.u_smooth.differentiable (by simp)
  rcases g.ug_deriv_u_pos_or_neg with h | h
  · exact Or.inl (ug_strictMonoOn_of_deriv_pos hdiff h)
  · exact Or.inr (ug_strictAntiOn_of_deriv_neg hdiff h)

theorem u_injOn : Set.InjOn g.u g.J := by
  rcases g.u_strictMonoOn_or_strictAntiOn with h | h
  · exact h.injOn
  · exact h.injOn

/-- "The cubic coordinate is injective" (ce:cubic-difference) -/
theorem cube_injective : Function.Injective (fun u : ℝ => u ^ 3) :=
  (Odd.strictMono_pow (by decide : Odd 3)).injective

/-- "hence the full local arc is injective even at its cusp" -/
theorem proj_injOn_J : Set.InjOn (xzOf (L.T i)) g.J := by
  intro s hs t ht he
  have h1 := g.chart_proj hs
  have h2 := g.chart_proj ht
  rw [he, h2] at h1
  have h3 : g.u t ^ 3 = g.u s ^ 3 := (Prod.ext_iff.mp h1).2
  exact g.u_injOn hs ht (cube_injective h3).symm

/-! #### The rectangle package of a cusp interval `[t₀ − η, t₀ + η]` -/

/-- the smaller end value of `u` -/
def uMin (η : ℝ) : ℝ := min (g.u (t₀ - η)) (g.u (t₀ + η))
/-- the larger end value of `u` -/
def uMax (η : ℝ) : ℝ := max (g.u (t₀ - η)) (g.u (t₀ + η))
/-- `M = max(|u₋|, |u₊|)`, the bound of `|u|` on the interval -/
def M (η : ℝ) : ℝ := max |g.uMin η| |g.uMax η|
/-- the clean rectangle in normalized coordinates -/
def rect (η : ℝ) : Set Plane :=
  Set.Icc (-(g.M η) ^ 2) (2 * (g.M η) ^ 2) ×ˢ Set.Icc ((g.uMin η) ^ 3) ((g.uMax η) ^ 3)
/-- the sup-norm radius of the rectangle -/
def radius (η : ℝ) : ℝ := max (2 * (g.M η) ^ 2) ((g.M η) ^ 3)

theorem rect_convex (η : ℝ) : Convex ℝ (g.rect η) := (convex_Icc _ _).prod (convex_Icc _ _)

theorem rect_isCompact (η : ℝ) : IsCompact (g.rect η) := isCompact_Icc.prod isCompact_Icc

theorem rect_subset_closedBall (η : ℝ) : g.rect η ⊆ Metric.closedBall 0 (g.radius η) := by
  intro p hp
  simp only [rect, Set.mem_prod, Set.mem_Icc] at hp
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
  rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have hM : 0 ≤ g.M η := le_trans (abs_nonneg _) (le_max_left _ _)
  have hmin : |g.uMin η| ≤ g.M η := le_max_left _ _
  have hmax : |g.uMax η| ≤ g.M η := le_max_right _ _
  have hM2 : 0 ≤ (g.M η) ^ 2 := sq_nonneg _
  have hM3 : 0 ≤ (g.M η) ^ 3 := pow_nonneg hM 3
  have hlo : -(g.M η) ^ 3 ≤ (g.uMin η) ^ 3 := by
    have h := (Odd.pow_le_pow (by decide : Odd 3)).mpr (abs_le.mp hmin).1
    rwa [Odd.neg_pow (by decide : Odd 3)] at h
  have hhi : (g.uMax η) ^ 3 ≤ (g.M η) ^ 3 :=
    (Odd.pow_le_pow (by decide : Odd 3)).mpr (abs_le.mp hmax).2
  have hr1 := le_max_left (2 * (g.M η) ^ 2) ((g.M η) ^ 3)
  have hr2 := le_max_right (2 * (g.M η) ^ 2) ((g.M η) ^ 3)
  unfold radius
  apply max_le
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

/-- for `0 < η < δ` the two end values of `u` have opposite signs: `u₋ < 0 < u₊` -/
theorem uMin_neg {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) : g.uMin η < 0 := by
  have hm : t₀ - η ∈ g.J := ⟨by linarith, by linarith [g.δ_pos]⟩
  have hp : t₀ + η ∈ g.J := ⟨by linarith [g.δ_pos], by linarith⟩
  have h0 := g.u_t₀
  unfold uMin
  rw [min_lt_iff]
  rcases g.u_strictMonoOn_or_strictAntiOn with h | h
  · have := h hm g.t₀_mem_J (by linarith : t₀ - η < t₀)
    exact Or.inl (by linarith)
  · have := h g.t₀_mem_J hp (by linarith : t₀ < t₀ + η)
    exact Or.inr (by linarith)

theorem uMax_pos {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) : 0 < g.uMax η := by
  have hm : t₀ - η ∈ g.J := ⟨by linarith, by linarith [g.δ_pos]⟩
  have hp : t₀ + η ∈ g.J := ⟨by linarith [g.δ_pos], by linarith⟩
  have h0 := g.u_t₀
  unfold uMax
  rw [lt_max_iff]
  rcases g.u_strictMonoOn_or_strictAntiOn with h | h
  · have := h g.t₀_mem_J hp (by linarith : t₀ < t₀ + η)
    exact Or.inr (by linarith)
  · have := h hm g.t₀_mem_J (by linarith : t₀ - η < t₀)
    exact Or.inl (by linarith)

theorem M_pos {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) : 0 < g.M η :=
  lt_of_lt_of_le (abs_pos.mpr (g.uMax_pos hη hηδ).ne') (le_max_right _ _)

/-- on the closed cusp interval `u` runs through `[u₋, u₊]` -/
theorem u_mem_Icc_of_mem {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) {t : ℝ}
    (ht : t ∈ Set.Icc (t₀ - η) (t₀ + η)) : g.u t ∈ Set.Icc (g.uMin η) (g.uMax η) := by
  have hm : t₀ - η ∈ g.J := ⟨by linarith, by linarith [g.δ_pos]⟩
  have hp : t₀ + η ∈ g.J := ⟨by linarith [g.δ_pos], by linarith⟩
  have htJ : t ∈ g.J := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  unfold uMin uMax
  rcases g.u_strictMonoOn_or_strictAntiOn with h | h
  · have h1 := h.monotoneOn hm htJ ht.1
    have h2 := h.monotoneOn htJ hp ht.2
    exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_right _ _)⟩
  · have h1 := h.antitoneOn hm htJ ht.1
    have h2 := h.antitoneOn htJ hp ht.2
    exact ⟨(min_le_right _ _).trans h2, h1.trans (le_max_left _ _)⟩

/-- and, conversely, a chart parameter whose `u` lies in `[u₋, u₊]` is on the closed interval -/
theorem mem_Icc_of_u_mem {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) {t : ℝ} (ht : t ∈ g.J)
    (hu : g.u t ∈ Set.Icc (g.uMin η) (g.uMax η)) : t ∈ Set.Icc (t₀ - η) (t₀ + η) := by
  have hm : t₀ - η ∈ g.J := ⟨by linarith, by linarith [g.δ_pos]⟩
  have hp : t₀ + η ∈ g.J := ⟨by linarith [g.δ_pos], by linarith⟩
  have hlt : t₀ - η < t₀ + η := by linarith
  rcases g.u_strictMonoOn_or_strictAntiOn with h | h
  · have hmp : g.u (t₀ - η) < g.u (t₀ + η) := h hm hp hlt
    have e1 : g.uMin η = g.u (t₀ - η) := min_eq_left hmp.le
    have e2 : g.uMax η = g.u (t₀ + η) := max_eq_right hmp.le
    rw [e1, e2] at hu
    exact ⟨(h.le_iff_le hm ht).mp hu.1, (h.le_iff_le ht hp).mp hu.2⟩
  · have hmp : g.u (t₀ + η) < g.u (t₀ - η) := h hm hp hlt
    have e1 : g.uMin η = g.u (t₀ + η) := min_eq_right hmp.le
    have e2 : g.uMax η = g.u (t₀ - η) := max_eq_left hmp.le
    rw [e1, e2] at hu
    exact ⟨(h.le_iff_ge ht hm).mp hu.2, (h.le_iff_ge hp ht).mp hu.1⟩

/-- on the open interval `u` is strictly inside `(u₋, u₊)` -/
theorem u_mem_Ioo_of_mem {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) {t : ℝ}
    (ht : t ∈ Set.Ioo (t₀ - η) (t₀ + η)) : g.u t ∈ Set.Ioo (g.uMin η) (g.uMax η) := by
  have hm : t₀ - η ∈ g.J := ⟨by linarith, by linarith [g.δ_pos]⟩
  have hp : t₀ + η ∈ g.J := ⟨by linarith [g.δ_pos], by linarith⟩
  have htJ : t ∈ g.J := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  unfold uMin uMax
  rcases g.u_strictMonoOn_or_strictAntiOn with h | h
  · have h1 := h hm htJ ht.1
    have h2 := h htJ hp ht.2
    exact ⟨(min_le_left _ _).trans_lt h1, h2.trans_le (le_max_right _ _)⟩
  · have h1 := h hm htJ ht.1
    have h2 := h htJ hp ht.2
    exact ⟨(min_le_right _ _).trans_lt h2, h1.trans_le (le_max_left _ _)⟩

theorem abs_u_le_M {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) {t : ℝ}
    (ht : t ∈ Set.Icc (t₀ - η) (t₀ + η)) : |g.u t| ≤ g.M η := by
  have hu := g.u_mem_Icc_of_mem hη hηδ ht
  have h1 := neg_abs_le (g.uMin η)
  have h2 := le_abs_self (g.uMax η)
  have h3 := le_max_left |g.uMin η| |g.uMax η|
  have h4 := le_max_right |g.uMin η| |g.uMax η|
  have h5 := hu.1
  have h6 := hu.2
  unfold M
  rw [abs_le]
  constructor <;> linarith

end GermData
```
