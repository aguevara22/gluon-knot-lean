# TN_U_F_REPORT.md — unit F (ambient isotopy Ψ) of `TN_Skeleton.lean`

Date: 2026-09-14.  File: `work/drafts/fd/TN_U_F.lean` (1192 lines; skeleton copy + unit F).
Compile: `cd work/lean && lake env lean ../drafts/fd/TN_U_F.lean` — **0 errors**, 36 `declaration uses sorry`
warnings (the 36 leaves of units A–E), 2 unused-variable warnings (see §4), ~8 s.
`grep -c sorry`: 42 before → 38 after (40 → 36 leaf sorries; the other two hits are prose).
`diff TN_Skeleton.lean TN_U_F.lean`: exactly the four `sorry` lines of F1–F4 removed, 237 lines added
(helpers + proof bodies); every definition, statement, name and docstring is byte-identical.

## 1. Leaves proved (4/4)

| leaf | name | axioms (`#print axioms`) |
|---|---|---|
| F1 | `pushfwd_apply` | propext, Classical.choice, Quot.sound |
| F2 | `contDiff_pushfwd` | propext, Classical.choice, Quot.sound |
| F3 | `hasCompactSupport_pushfwd` | propext, Classical.choice, Quot.sound |
| F4 | `psi_track` | + `sorryAx`, **only through E2 `norm_helix`** (unit E black box: `‖helix N b θ‖ = |b|`) |

Consequences for the assembly (checked): `ambientIsotopy` (F2 + F3 + row 86) is now **axiom-clean**;
`carries` and hence the `ambient`/`carries` fields of the row theorem depend on `sorryAx` only via E2.
No leaf was found false or under-hypothesised.  `hN : 0 < N` is not needed by F1–F3 (only F4 uses it, to
call F2/F3 — and even there only formally); `hm.open_map` was not needed anywhere (the IFT local inverse's
eventual right-inverse property replaces the openness of the image in F2).

## 2. Leaves left

None in unit F.

## 3. Helpers added (all `tf_`-prefixed, placed immediately before the leaf that uses them)

Before F1:
- `tf_periodic_int` — `H (θ + 2πk, w) = H (θ, w)` for `k : ℤ` (`Function.Periodic.int_mul`).
- `tf_shift_eq` — `p + (2πk, 0) = (p.1 + 2πk, p.2)`.
- `tf_periodic_int'` — the additive form `H (p + (2πk, 0)) = H p`.
- `tf_isOpen_solidTorus` — `IsOpen (solidTorus δ)`.
- `tf_fderiv_shift` — `fderiv ℝ H (p + (2πk, 0)) = fderiv ℝ H p` on the solid torus
  (`hasFDerivAt_comp_add_right` + `HasFDerivAt.congr_of_eventuallyEq` + `HasFDerivAt.fderiv`).
- `tf_helix_int` — `helix N b (θ + 2πk) = helix N b θ` (`Real.cos_add_int_mul_two_pi`, `N k : ℤ`).
- `tf_Vamb_shift` — `Vamb N b δ (p + (2πk, 0)) = Vamb N b δ p`.

Before F2:
- `tf_tube_subset` — `Icc 0 (2π) ×ˢ closedBall 0 R₂ ⊆ solidTorus δ` (`R₂ = b + (δ−b)/2 < δ`).
- `tf_isCompact_K` — `IsCompact (H '' (Icc 0 (2π) ×ˢ closedBall 0 R₂))` (the paper's `K`).
- `tf_R_sq_lt` — `R₁² < R₂²`; `tf_chiAmb_eq_one` (`s ≤ R₁²`), `tf_chiAmb_eq_zero` (`s ≥ R₂²`).
- `tf_exists_reduce` — `∃ θ₀ ∈ Icc 0 (2π), ∃ k : ℤ, θ = θ₀ + 2πk` (`Int.sub_floor_div_mul_nonneg/_lt`).
- `tf_pushfwd_eq_zero` — `X q = 0` for `q ∉ K` (any preimage has `‖w‖ > R₂`, so `χ = 0`, `V = 0`).
- `tf_contDiff_helix`, `tf_contDiff_Vamb` — smoothness of `helix N b` and of `V` on `ℝ × ℝ²`.
- `tf_exists_equiv` — an injective `A : ℝ × ℝ² →L[ℝ] ℝ³` is a `ContinuousLinearEquiv`
  (`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`, `ContinuousLinearEquiv.ofBijective`).
- `tf_contDiffAt_pushfwd_of_mem` — `ContDiffAt ℝ ∞ X (H p₀)` for `p₀` in the torus (the IFT core of F2).

Before F4:
- `tf_hasDerivAt_track` — for `s ∈ Ioo (−ε) (1+ε)`, `ε = (δ−b)/(4b)`, the curve `γ(s) = H(θ,(1−s)v(θ))`
  satisfies `γ′ = X(γ)` (there `|1−s| b ≤ R₁`, `χ = 1`, `V = (0,−v)`, and F1 identifies `X`).

Line numbers in the installed file:
- line 875  `tf_periodic_int`
- line 882  `tf_shift_eq`
- line 886  `tf_periodic_int'`
- line 891  `tf_isOpen_solidTorus`
- line 895  `tf_fderiv_shift`
- line 909  `tf_helix_int`
- line 916  `tf_Vamb_shift`
- line 922  `pushfwd_apply`
- line 939  `tf_tube_subset`
- line 945  `tf_isCompact_K`
- line 951  `tf_R_sq_lt`
- line 958  `tf_chiAmb_eq_one`
- line 963  `tf_chiAmb_eq_zero`
- line 968  `tf_exists_reduce`
- line 974  `tf_pushfwd_eq_zero`
- line 998  `tf_contDiff_helix`
- line 1005  `tf_contDiff_Vamb`
- line 1016  `tf_exists_equiv`
- line 1027  `tf_contDiffAt_pushfwd_of_mem`
- line 1062  `contDiff_pushfwd`
- line 1074  `hasCompactSupport_pushfwd`
- line 1109  `tf_hasDerivAt_track`
- line 1145  `psi_track`

## 4. Mathlib / Lean pitfalls met (for the assembler and the other units)

1. **`ContDiffAt.localInverse` / `ContDiffAt.to_localInverse` are NOT in scope** with the five imports
   (they live in `Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff`, which nothing imports).
   What IS available (via `SM.ContactMotions`' imports): `ContDiffAt.hasStrictFDerivAt'`,
   `HasStrictFDerivAt.localInverse`, `.toOpenPartialHomeomorph`, `.localInverse_apply_image`,
   `.eventually_right_inverse`, `.image_mem_toOpenPartialHomeomorph_target`, and
   `OpenPartialHomeomorph.contDiffAt_symm`.  `tf_contDiffAt_pushfwd_of_mem` unrolls
   `ContDiffAt.to_localInverse` by hand with these (the localInverse is definitionally
   `(toOpenPartialHomeomorph H).symm`, so `hinv_img` can be reused as `hsymm` by `exact`).
   Units A (A5/A6) and D (D7) planning to use `ContDiffAt.localInverse` should copy this pattern.
2. **`rw` and `Exists.choose`:** with `hex : ∃ p ∈ solidTorus δ, H p = q`, the goal mentions
   `hex.choose`, whose type depends on `q` (or on `p` in F1) — rewriting `q`/`p` in the goal fails with
   "motive is not type correct".  Fix: rewrite the *hypotheses* instead (`rw [← hpe] at h1 h2`) or split the
   goal with `Eq.trans ?_ hHp`.
3. `ContDiff.norm_sq` leaves the inner-product field `𝕜` undetermined (`failed to synthesize RCLike 𝕜`);
   use `contDiff_norm_sq ℝ` (explicit `𝕜`) composed with `contDiff_snd`.
4. `ContDiff.smul`/`ContDiff.comp` do not unify with `fun p => -c p • v p.1` directly (`helix N b ∘ Prod.fst`
   vs `fun p => helix N b p.1`): state each factor with an explicit `have h : ContDiff ℝ ∞ fun p => … :=`.
5. Smoothness of `!₂[a θ, b θ]` (`WithLp.toLp 2 ![…]`): `rw [contDiff_euclidean]; intro i; fin_cases i <;> simp <;> fun_prop`.
6. `field_simp` alone closes `(1 + (δ−b)/(4b)) * b = b + (δ−b)/4` (with `hb : b ≠ 0` in context); a trailing
   `ring` errors with "no goals".
7. `push_neg` is deprecated in this toolchain (warning; use `not_lt.1`/`push Not`).
8. `hm.immersion p₀.1 p₀.2` produces `fderiv ℝ H (p₀.1, p₀.2)`; structure eta makes `exact` accept
   `fderiv ℝ H p₀`-typed terms, and `hHp' : H hex.choose = H p` is accepted where `H (c.1, c.2) = H (p.1, p.2)`
   is expected — no `Prod.mk.eta` needed.
9. `pow_le_pow_left₀` is the current name of `0 ≤ a → a ≤ b → a^n ≤ b^n`.
10. `(∞ : WithTop ℕ∞) ≠ 0`, `∞ + 1 ≤ ∞`, `1 ≤ ∞`, and `finrank ℝ (ℝ × ℝ²) = finrank ℝ ℝ³` are all `by simp`.
11. The two remaining warnings are the unused-variable linter on `hN` in F2 and F3 (statements frozen;
    `0 < N` is not needed for smoothness or compact support).  Harmless.
12. The full file compiles in ~8 s while the other units are `sorry`; iterate on a copy directly.

## 5. What the executor / assembler must know

- Unit F depends on nothing from units A–D and on exactly one statement of unit E: `norm_helix` (E2).
- `psi_track` proves the identity on the whole of `Icc 0 1` via `ContactMotions.ODE_unique_Ioo` on
  `Ioo (−ε) (1+ε)`; the Lipschitz constant comes from `exists_lipschitzWith_of_hasCompactSupport'` (F2, F3).
- Generic helpers that other units may want to reuse instead of re-proving: `tf_periodic_int` (integer
  periodicity of `H`), `tf_helix_int` (helix periodicity, E5 needs it), `tf_exists_reduce` (angle reduction,
  D3/D5), `tf_isOpen_solidTorus`, `tf_exists_equiv` (injective ⇒ CLE in dimension 3, also A4/D6/D7),
  `tf_contDiff_helix` (E5/E6).  If another unit adds a lemma with the same name, the merge will error —
  all mine carry the `tf_` prefix, so collisions can only come from copies.
