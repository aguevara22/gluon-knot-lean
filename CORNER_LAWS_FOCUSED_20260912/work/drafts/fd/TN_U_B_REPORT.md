# TN_U_B_REPORT.md — Unit B (forms and the Moser field) of `TN_Skeleton.lean`

Date: 2026-09-14.  File: `work/drafts/fd/TN_U_B.lean` (1200 lines; skeleton 959).
Compile: `cd work/lean && lake env lean ../drafts/fd/TN_U_B.lean` — **0 errors**, 34 warnings, all
`declaration uses sorry` on the leaves of the other units (A1–A6, C1–C9, D1–D7, E1–E7, F1–F4).
`grep -c sorry`: 42 before → 36 after (the count includes the two docstring mentions in the module
header; leaves: 40 → 34).  Statements, definitions, names and docstrings untouched: `diff` against
`TN_Skeleton.lean` removes exactly six lines, each `  sorry`.

## Leaves proved (6/6)

| leaf | name | line | axioms |
|---|---|---|---|
| B1 | `contDiff_gfun` | 425 | propext, Classical.choice, Quot.sound |
| B2 | `gfun_periodic` | 471 | + `sorryAx` **only via A2 `chart_periodic`** (black box) |
| B3 | `dalphaT_eq` | 524 | propext, Classical.choice, Quot.sound |
| B4 | `exists_PN_radius` | 551 | + `sorryAx` via B2 → A2 |
| B5 | `contDiffOn_Vf` | 629 | propext, Classical.choice, Quot.sound |
| B6 | `exists_Vf_bound` | 686 | + `sorryAx` via `tb_gfun_periodic` → A2 |

Leaves left: none.  Once Unit A delivers `chart_periodic` (A2) the whole unit is axiom-clean.

## What each proof does

- **B1** `g = (c u y′ − c v x′ − c c′ u v)/a` smooth: `deriv T` smooth by `contDiff_infty_iff_deriv`;
  `aT = alpha (T θ) (deriv T θ)` by coordinate projections (`ContactMotions.contDiff_coord`);
  `cT = √(2 aT)` by `ContDiff.sqrt` with `aT > 0` (`aT_pos`); `deriv (cT T)` again by
  `contDiff_infty_iff_deriv`; assemble with `ContDiff.mul/sub/div`, the divisor `aT T p.1 ≠ 0`.
- **B2** `g` periodic from A2 (`aT, cT, deriv T` periodic) plus `deriv (cT T) (θ+2π) = deriv (cT T) θ`
  via `deriv_comp_add_const` and `funext` of the periodicity.  `g_u, g_v` periodic: the function
  `q ↦ g (q + (2π, 0))` equals `g`, so `fderiv_comp_add_right` gives
  `fderiv g (θ+2π, w) = fderiv g (θ, w)` (helper `tb_fderiv_gfun_shift`); no differentiability needed.
- **B3** explicit `HasFDerivAt` of `q ↦ α_t(q)(y)` (helper `tb_hasFDerivAt_alphaT`, derivative
  `y.1 • (t • Dg p) − y.2 0 • ((1+t) • coord₁∘snd) + y.2 1 • ((1−t) • coord₀∘snd)`), then
  `Dg(p)[x] = x_θ·Dg(p)(1,0) + x_u g_u + x_v g_v` by the basis decomposition `tb_vec_decomp`
  (`x = x.1•(1,0) + x.2 0•(0,e₀) + x.2 1•(0,e₁)`) and `map_add/map_smul`; the `g_θ` terms cancel
  under `ring`.
- **B4** the set `n = {((t,θ),w) | 1/2 < P ∧ 1 < N}` is open (`isOpen_lt`, continuity of `(t,θ,w) ↦
  (P, N)` by `fun_prop` from B1 and `contDiff_gu/gv`), contains the compact
  `(Icc (−4) 4 ×ˢ Icc 0 (2π)) ×ˢ {0}` (`Pf_core`, `Nf_core`); `generalized_tube_lemma` gives an open
  `v ∋ 0`, hence a ball of radius `ε`; `ρ := ε/2`.  Arbitrary `θ` is reduced to `[0, 2π)` by
  `Periodic.exists_mem_Ico₀` applied to `θ ↦ (P, N)` (periodic by B2).  Existential only, as the plan
  demands (no fixed constant).
- **B5** `N` is globally `C^∞` in `(t, p)` (`tb_contDiff_Nf`); on the set `N ≠ 0` from
  `GoodRadius.N_pos` (`Ioo ⊆ Icc`, `<` ⇒ `≤`); each of the three closed-form components is
  `ContDiffOn.div`; the `ℝ²` part via `contDiffOn_euclidean` + `fin_cases` + `simpa`;
  `ContDiffOn.prodMk`; `uncurry (Vf T)` is definitionally the pair.
- **B6** `G := max G₀ 0` bounds `|g|` on the `2ρ`-tube (`IsCompact.exists_bound_of_continuousOn` on
  `Icc 0 (2π) ×ˢ closedBall 0 (2ρ)`, extended to all `θ` by periodicity — helper
  `tb_exists_gfun_bound`, stated for any radius `r`).  With `N > 1`: `|a/N| ≤ |a|`
  (`tb_abs_div_le`), `|u|,|v| ≤ ‖w‖` (`PiLp.norm_apply_le`), `|2uv/N| ≤ 2‖w‖² ≤ 4ρ‖w‖`,
  `|u(1+g)/N|, |v(g−1)/N| ≤ (1+G)‖w‖`, `‖!₂[a,b]‖ ≤ |a| + |b|` (`tb_norm_vec2_le`), sup norm on the
  product (`Prod.norm_mk`, `max_le`).  **`C = 4ρ + 2(1+G)`**.

## Helpers added (all `tb_`-prefixed, each placed immediately before the leaf that uses it)

Before B1 (395–423): `tb_coord2` (def, `PiLp.proj` on `ℝ²`), `tb_coord2_apply` (`@[simp]`),
`tb_contDiff_coord2`, `tb_contDiff_coord3`, `tb_contDiff_snd_coord`, `tb_contDiff_deriv`,
`tb_contDiff_aT`, `tb_contDiff_cT`, `tb_contDiff_deriv_cT`.
Before B2 (444–469): `tb_cT_periodic`, `tb_deriv_cT_periodic`, `tb_gfun_periodic`,
`tb_gfun_comp_shift`, `tb_fderiv_gfun_shift`.
Before B3 (489–522): `tb_vec_decomp`, `tb_fderiv_gfun_apply`, `tb_hasFDerivAt_alphaT`.
Before B4 (534–549): `tb_PN_periodic`, `tb_continuous_PN`.
Before B5 (613–627): `tb_contDiff_Nf`.
Before B6 (659–684): `tb_norm_vec2_le`, `tb_abs_div_le`, `tb_exists_gfun_bound`.

Useful to other units: `tb_contDiff_aT`, `tb_contDiff_cT`, `tb_contDiff_deriv`,
`tb_contDiff_deriv_cT` (Unit A's A1/A3 need exactly these pieces); `tb_vec_decomp` and
`tb_fderiv_gfun_apply` (Unit D's `fderiv` bookkeeping on `ℝ × ℝ²`); `tb_contDiff_Nf` (Unit C/D:
`Nf` is globally smooth, so `muf` is smooth wherever `P, N ≠ 0`); `tb_norm_vec2_le`,
`tb_abs_div_le` (C6 Grönwall estimates); `tb_exists_gfun_bound` (any radius).

## Mathlib pitfalls at this pin (v4.34.0-rc2)

- `WithLp` is a structure: coordinates print as `w.ofLp i`; `(PiLp.proj 2 _ i).contDiff` does NOT
  unify directly with `fun p => p i` for `ℝ³` (metavariable left) — go through a named CLM def
  (`tb_coord2`, or reuse `ContactMotions.coordCLM`/`contDiff_coord` for `ℝ³`).
- `EuclideanSpace.single_apply` is deprecated (→ `PiLp.single_apply`); plain `simp` handles
  `EuclideanSpace.single` coordinates after `fin_cases`.
- `ContinuousLinearMap.add_apply/sub_apply/smul_apply` deprecated (since 2026-05-20) → root
  `add_apply`, `sub_apply`, `smul_apply`; `ContinuousLinearMap.snd_apply` does not exist — use
  `ContinuousLinearMap.coe_snd'` (`⇑(snd R M₁ M₂) = Prod.snd`).
- `Set.mem_setOf_eq` deprecated → `Set.mem_ofPred_eq`.
- `IsCompact.exists_bound_of_continuousOn'` is the multiplicative (`SeminormedGroup`) version; for
  `ℝ` use the additive `IsCompact.exists_bound_of_continuousOn` (instance mismatch error otherwise).
- `ContDiff.differentiable` takes `n ≠ 0` (`by simp` proves `∞ ≠ 0`), `ContDiff.fderiv_right` takes
  `m + 1 ≤ n` (`by simp`).
- `abs_add` does not exist; use `abs_add_le`; `abs_sub a b : |a − b| ≤ |a| + |b|`.
- `rw [abs_of_pos (by linarith)]` unifies with the FIRST `|_|` in the goal — give the argument
  explicitly (`show (0:ℝ) < N by linarith`).
- `unfold Pf Nf` leaves `Pf` inside `Nf` (order matters); use `unfold Nf Pf`.
- `fun_prop` proves continuity of `(t,θ,w) ↦ (P, N)` given `Continuous (gfun T)`, `Continuous (gu T)`,
  `Continuous (gv T)` and `∀ i, Continuous (fun w : ℝ² => w i)` as local hypotheses.
- Periodicity reduction: `Function.Periodic.exists_mem_Ico₀ (h : Periodic f c) (hc : 0 < c) x :
  ∃ y ∈ Ico 0 c, f x = f y` works for `f` valued in any type (used for the pair `(P, N)`).
- `fderiv_comp_add_right (a) : fderiv 𝕜 (fun x ↦ f (x + a)) x = fderiv 𝕜 f (x + a)` needs no
  differentiability — cleanest route to "fderiv of a periodic function is periodic".

## For the assembler / executor

- No statement, definition or docstring changed; the six replaced `sorry`s are the only removed lines.
- All B leaves are independent of Units C–F; B2/B4/B6 depend on A2 `chart_periodic` (statement only).
- `exists_goodRadius`, `Vf_periodic`, `muf_periodic`, `contDiff_gu/gv` (proved in the skeleton from
  B1/B2/B4) now compile from real proofs.
- Scratch and assembly script: `/tmp/tnb/` (`apply.py` rebuilds the file from the skeleton + the
  per-leaf snippets `b1b2.lean`, `b2.lean`, `b3.lean`, `b4.lean`, `b5.lean`, `b6.lean`).
