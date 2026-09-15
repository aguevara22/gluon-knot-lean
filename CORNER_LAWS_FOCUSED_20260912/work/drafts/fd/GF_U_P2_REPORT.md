# GF_U_P2_REPORT.md — unit P2 (the collar) of `GF_Skeleton.lean` (row 87 fd:generic-front)

Date: 2026-09-14.  File: `work/drafts/fd/GF_U_P2.lean` (1068 lines; skeleton 625).
Compile: `cd work/lean && lake env lean ../drafts/fd/GF_U_P2.lean` → **0 errors**, 25 warnings
`declaration uses 'sorry'` (the 24 leaves of the other units + P2.2).  `grep -c sorry`: 27 before →
26 after (leaf `sorry` lines 26 → 25).  All statements, docstrings and the assembly are byte-identical
to the skeleton (checked line by line); only the body of `exists_collar` was filled and helpers
(`gp2_…`) were inserted before the two leaves.

## 1. Result

| leaf | status | axioms |
|---|---|---|
| **P2.1 `exists_collar`** (line 514) | **PROVED** | `[propext, sorryAx, Classical.choice, Quot.sound]` — `sorryAx` only through the black box P1.4 `deriv_y_ne_zero_at_cusp` |
| **P2.2 `stage1_stable`** (line 782) | **LEFT `sorry` — FALSE as stated** (§2) | — |
| `gp2_stage1_stable_of_lt` (the true form of P2.2, §3) | PROVED | `sorryAx` only through P0.1 `isContactIsotopy_hamIsotopy`, P0.2 `contact_preserves_legendrian`, P1.4 |

The analytic core (`gp2_injOn_front_critical`, `gp2_collar_of_cover`, `gp2_cert_stable`,
`gp2_far_stable`) is axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## 2. P2.2 is false as stated — counterexample

Statement: for **every** `δc` with `LocallyInjectiveFront L δc` and every family `Hs`,
`∃ r > 0, ∀ ‖a‖ < r, Stage1 (Φ_a ∘ L) ∧ LocallyInjectiveFront (Φ_a ∘ L) δc` (same `δc`).

Take `L(θ) = (sin 2θ, sin θ, cos θ − ⅓cos 3θ)`.  It is `Stage1`: Legendrian (`z′ = −sin θ + sin 3θ
= sin θ · 2cos 2θ = y x′`), embedded (`sin θ = sin η ∧ sin 2θ = sin 2η` forces `η ≡ θ`, the
candidates `η = π − θ` being excluded by `z`), immersed (`x′ = 2cos 2θ`, `y′ = cos θ` never vanish
together), `NoDoubleZero` (`x′² + x″² = 4`).  Its front has exactly one unordered double point,
`(θ₀, η₀) = (π/2, 3π/2)` (both fronts `(0, 0)`), transverse (`det = ∓8`), at circular distance
**exactly `π`**, and no other; hence `LocallyInjectiveFront L π` holds (`δc = π`).

Perturb with `m = 1`, `H = −χ·(y + 1)` where `χ` is a bump equal to `1` on `B(q, ½)` and supported
in `B(q, 1)`, `q = L(3π/2) = (0, −1, 0)` (so `L(π/2) = (0, 1, 0)` is outside the support).  Where
`χ = 1` the field is `X_H = (1, 0, −1)` (P3.1), so for `|a|` small `Φ_a` is the translation
`p ↦ p + a(1, 0, −1)` on `B(q, ¼)` and the identity near `L(π/2)`.  The double point moves by the
IFT to `(θ(a), η(a)) = (π/2, 3π/2 + a/2 + O(a²))` (first order: `−2dθ = −2dη + a`,
`−2dθ = 2dη − a`), so `circDist = π − |a|/2 < π = δc` for every `a ≠ 0` of either sign: the
conclusion fails for all `‖a‖ < r`, whatever `r`.

Numerical check: `GF_U_P2_probe.py` (pure Python; also `/tmp/fd/probe_p2.py`).  Output: double
points `(1.570796, 4.712389)` and its transpose only, `circDist = 3.141593`, collar for `δ* = π`
confirmed on a grid; `H^x`-perturbation `a = ±10⁻²`: new double point `η = 4.717389 / 4.707389`,
`circDist = 3.136593 < π`; `a = ±10⁻³`: `3.141093 < π`; `a = ±10⁻⁴`: `3.141543 < π`.

Why no hypothesis fix inside P2 helps: the leaf quantifies over all `δc`; the sharp `δc` (a double
point at distance exactly `δc`) is always a counterexample.  What is true is the collar with any
**smaller** width — proved as `gp2_stage1_stable_of_lt` (§3).  (`exists_collar` cannot be made to
return a "robust" `δc` without changing its statement; and `stage1_stable` would still be false for
other `δc`.)

## 3. What the assembler must do (tested patch for `step2`)

`step2` (skeleton lines 406-447) uses `stage1_stable h hδ m Hs hHs` with the collar `δc` from
`exists_collar`.  Replace it by the half width.  The following body compiles (tested in
`/tmp/fd/p2/P2_step2test.lean`: 0 errors, `fd_generic_front` still assembles, axioms unchanged):

```lean
  obtain ⟨δc, hδ⟩ := exists_collar h
  -- P2.2 is false with the width `δc` itself; work with the half width `δc / 2`, which persists
  -- (`gp2_stage1_stable_of_lt`).  The family is obtained with a provisional radius `1`, then shrunk.
  have hδ' : LocallyInjectiveFront L (δc / 2) :=
    gp2_locallyInjectiveFront_mono hδ (half_pos hδ.1) (half_le_self hδ.1.le)
  obtain ⟨m, Hs, r, hHs, hr, -, hC, hR⟩ := exists_CR_avoidance h hδ' 1 one_pos
  obtain ⟨rs, hrs, hstab⟩ :=
    gp2_stage1_stable_of_lt h hδ (half_pos hδ.1) (half_lt_self hδ.1) m Hs hHs
  -- … unchanged …, except `K2 δc`/`K3 δc` → `K2 (δc / 2)`/`K3 (δc / 2)` in `hU` and `hav`,
  -- and `collar := ⟨δc, hδa⟩` → `collar := ⟨δc / 2, hδa⟩`.
```

Exact statements to use:
```lean
theorem gp2_stage1_stable_of_lt {L : ℝ → ℝ³} (h : Stage1 L) {δc : ℝ}
    (hδ : LocallyInjectiveFront L δc) {δ' : ℝ} (hδ'pos : 0 < δ') (hδ' : δ' < δc)
    (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (hHs : ∀ i, ContactMotionsHyp (Hs i)) :
    ∃ r > 0, ∀ a : ℝ^m, ‖a‖ < r →
      Stage1 (composeFlows m Hs (par a) ∘ L) ∧
        LocallyInjectiveFront (composeFlows m Hs (par a) ∘ L) δ'
lemma gp2_locallyInjectiveFront_mono {L : ℝ → ℝ³} {δ δ' : ℝ} (h : LocallyInjectiveFront L δ)
    (hδ' : 0 < δ') (hle : δ' ≤ δ) : LocallyInjectiveFront L δ'
```
Downstream: `Stage2.collar` is existential (`∃ δc, …`), so the half width changes nothing for
P3.3/P3.4 (they take whichever `δc` is passed), P4, P5.6 (whose plan says "collar persists (P2.2
argument)" — use a smaller width there too) or the row theorem.  `stage1_stable` itself can then be
deleted from the skeleton or kept as a dead `sorry`; nothing else references it.

## 4. Proof architecture (P2.1 and the true P2.2)

*Certificate* on `Icc α β`: `(∀ θ, x′ ≠ 0) ∨ ((∀ θ, x″ ≠ 0) ∧ (∀ θ, y′ ≠ 0))` (regular/critical;
no sign conditions needed — see below).  Helpers, in order of appearance:

* `gp2_injOn_of_deriv_ne_zero` — Rolle (`exists_deriv_eq_zero`): `f′ ≠ 0` on `Ioo` ⇒ `InjOn f (Icc)`.
* `gp2_injOn_front_regular` — `x′ ≠ 0` ⇒ `(x, z)` injective.
* `gp2_injOn_front_critical` — **the integration by parts in mean-value form**: for `θ₁ < θ₂`,
  `x θ₁ = x θ₂ = X`, `z θ₁ = z θ₂`, the function `k = z − y (x − X)` has `k θ₁ = k θ₂` and
  `k′ = y′ (X − x)` (using `z′ = y x′`); Rolle gives `c` with `x c = X`; Rolle for `x` on
  `[θ₁, c]`, `[c, θ₂]` gives two zeros of `x′`, contradicting `InjOn (deriv x)` (from `x″ ≠ 0`).
  No integral, no sign normalisation, no existence of the critical point.
* `gp2_deriv_coordZ` — Legendrian ⇒ `deriv (coordZ L) = coordY L * deriv (coordX L)`.
* `gp2_injOn_front_of_cert`, `gp2_exists_cert` — certificate ⇒ `InjOn (front L)`; every `θ₀` of
  a `Stage1` curve has a certificate interval `Icc (θ₀ − ρ) (θ₀ + ρ)` (continuity of `x′, x″, y′`;
  P1.4 for `y′ ≠ 0` at a cusp).
* `gp2_periodic_front`, `gp2_circDist_le_pi`, `gp2_collar_of_reduced` — the collar follows from
  the statement for `θ ∈ Ico 0 (2π)`, `|θ − η| < δ`, `|θ − η| ≤ π`, `θ ≠ η` (shift by
  `toIcoMod`/`round`: `circDist θ η = |θ' − η'|`, `¬SameParam ↔ θ' ≠ η'`).
* `gp2_collar_of_cover` — cover with a Lebesgue number (`lebesgue_number_lemma_of_metric`) ⇒ collar.
* `exists_collar` = `gp2_exists_cert` + `choose` + Lebesgue number + `gp2_collar_of_cover`.
* P2.2 side: `gp2_eventually_of_compact` (tube lemma as `∀ᶠ a in 𝓝 0`), `gp2_contDiff_G`
  (`(θ, a) ↦ Φ_a (L θ)` smooth from `fd_contact_motions.compositions_smooth`),
  `gp2_composeFlows_par_zero`, `gp2_contDiff_D1`, `gp2_deriv_slice`, `gp2_deriv2_slice`
  (`x_a′, x_a″, y_a′` are coordinates of `DG(1,0)`, `D(DG(1,0))(1,0)` — jointly continuous),
  `gp2_periodic_deriv`, `gp2_exists_shift`, `gp2_circDist_le_abs`, `gp2_not_sameParam`,
  `gp2_locallyInjectiveFront_mono`, `gp2_cert_stable` (certificates are open in `a`),
  `gp2_far_stable` (pairs in one period with `δ ≤ |θ − η| ≤ min δ' π` form a compact set on which
  "fronts differ" is open), `gp2_stage1_stable_of_lt` (finite subcover of `[0, 2π]`, its Lebesgue
  number `δ`, `Filter.eventually_all_finset`, `Metric.eventually_nhds_iff`; `Stage1.circle/
  legendrian` from P0.1+P0.2 exactly as in `step1`; `NoDoubleZero` from the certificates after a
  `2π`-shift).

Total added: 24 helpers, ≈ 440 lines (plan estimate 600).

## 5. Mathlib pitfalls (v4.34.0-rc2 pin)

* `PiLp.proj 2 (fun _ : Fin m => ℝ) i` needs the ascription `(… : ℝ^m →L[ℝ] ℝ)` before `.contDiff`,
  and `fun a => par a i` must be `show`n as `fun a => a i` first (`par` does not unfold in unification).
* `Set.mem_setOf_eq` is deprecated → `Set.mem_ofPred_eq`.
* No `Function.Periodic.deriv`: use `deriv_comp_add_const` + `funext hf` (`gp2_periodic_deriv`).
* Shift into one period: `toIcoMod two_pi_pos 0 θ`, `toIcoMod_mem_Ico'`, `self_sub_toIcoMod`
  (+ `zsmul_eq_mul`); `Periodic.int_mul`, `Periodic.sub_int_mul_eq` for the transfer.
* `circDist` bounds: `abs_sub_round` (≤ π) and `round_le x 0` (≤ |θ − η|), after `field_simp`.
* `HasFDerivAt.comp_hasDerivAt θ h1` takes the point explicitly; `HasDerivAt.prodMk`,
  `Continuous.prodMk`, `ContDiff.prodMk` are the current names.
* `ContDiff.differentiable (by simp)`, `ContDiff.continuous_deriv (by simp)`,
  `contDiff_infty_iff_deriv` for the `x″` continuity; `ContDiff.contDiff_fderiv_apply (m := ∞) (by simp)`.
* `fd_contact_motions` is `SM.fd_contact_motions` (not in `SM.ContactMotions`); `composeFlows_zero`
  is `ContactMotions.composeFlows_zero` and needs `fun i p => (hHs i).hamFlow_zero p`.
* `lebesgue_number_lemma_of_metric` works with `ι := t` (subtype of a `Finset ℝ`) after
  `IsCompact.elim_finite_subcover`; convert `⋃ i ∈ t` with `mem_iUnion₂`.
* `linear_combination hc0` closes `y′ c (X − x c) = 0` from the expanded derivative identity.

## 6. For the executor

* Nothing in P2 needs the integral machinery (`intervalIntegral`) or `generalized_tube_lemma`
  beyond `gp2_eventually_of_compact`; the plan's "integration by parts" is replaced by Rolle.
* Black boxes used: P0.1, P0.2 (for the perturbed curve's `circle`/`legendrian`, as in `step1`),
  P1.4 (`y′ ≠ 0` at cusps).  If P1.4 is delayed, a 15-line inline proof (`deriv L θ ≠ 0`, `z′ = y x′`,
  coordinates via `hasDerivAt_coord`) would make `exists_collar` independent of P1.
* The P5.6 plan item "collar persists (P2.2 argument)" should likewise be stated with a smaller
  width; the same counterexample applies verbatim to any "same-width" persistence claim.
