# U_HT_REPORT — Unit HT (collar + turning), cf:lem-curl

File: `work/drafts/curl/U_HT.lean` (copy of `Skeleton_FINAL.lean`; statements byte-identical — the diff
against the skeleton removes exactly nine `  sorry` lines and adds 167 lines of proofs/helpers).
Check: `cd work/lean && lake env lean ../drafts/curl/U_HT.lean` → **0 errors** (≈8 s). `grep -c sorry`:
56 before → **47 after** (9 leaves closed; the count includes the two prose mentions of `sorry` in the header
and §7 banner). `#print axioms` for every HT leaf: `[propext, Classical.choice, Quot.sound]`.

## Leaves proved (9/9)

Unit H (sm-3:4080-4212, abstract in `f, g, φ`):
- `blend_smooth` — `ContDiff.comp/sub/mul/add` with `Real.smoothTransition.contDiff`.
- `blend_eq_left` — `(η−e₁)/lam ≤ 0`, `Real.smoothTransition.zero_of_nonpos`, `ring`.
- `blend_eq_right` — `1 ≤ (η−e₁)/lam` (`le_div_iff₀`), `Real.smoothTransition.one_of_one_le`, `ring`.
- `sep_of_deriv` — slope MVT on `g − f` over `[e₁, η]` (helper `ht_exists_deriv_eq_slope`), `deriv_sub`.
- `deriv_blend_ge` — `h' = (1−φ)f' + φg' + (φ'/lam)(g−f)` (helper `ht_hasDerivAt_blend`); `φ ≥ 0`,
  `φ' ≥ 0` (`Real.smoothTransition.monotone.deriv_nonneg`), `g ≥ f` from `sep_of_deriv`; the `φ(g'−f')`
  term is handled by the case split `η = e₁` (`φ(0) = 0`) / `η > e₁` (`hd`); `nlinarith`.
- `blend_between` — `0 ≤ φ ≤ 1`, `nlinarith`.
- `deriv_blend_le` — same derivative formula for `blend g f (e₂−lam) lam`; `g ≥ f` on the collar from the
  mirrored separation (helper `ht_sep_of_deriv_left`, slope MVT over `[η, e₂]`); the `(1−φ)(g'−f')` term
  by the case split `η = e₂` (`φ(1) = 1`) / `η < e₂` (`hd`).

Unit T (sm-3:4226-4244):
- `rot_shiftCurve` — `(shiftCurve c a).tangentLoop = c.tangentLoop.shift a` is **`rfl`** (all non-data fields
  are Props), then the accepted `tw_shift`.
- `rot_sub_rot_of_window` — `rot_sub_rot_of_replace` applied to `shiftCurve F.toClosedC1Curve s₁` and
  `shiftCurve F'.toClosedC1Curve s₁` with `lam = mu = s₂ − s₁`, `ψ = id`, lifts `θ(· + s₁)`, `θ'(· + s₁)`
  on `[0, s₂ − s₁]`; `hcompl` is the equality of unit tangents on the closed complementary arc
  `[s₂, s₁ + 1]`, endpoints included, obtained from `hsame` (helper `ht_offWindow_of_mem_Icc`: every
  `t ∈ [s₂, s₁+1]` is `OffWindow`) and `ht_deriv_eq_of_eqOn_Icc` (equal derivatives at every point of a
  nondegenerate closed interval on which two differentiable curves agree: `UniqueDiffWithinAt.eq_deriv`
  + `uniqueDiffOn_Icc` + `HasDerivWithinAt.congr` — no continuity of the derivative needed). Then
  `rot_shiftCurve` twice and `simp only [sub_add_cancel, zero_add]`.

## Leaves left

None in this unit.

## Helpers added (all `ht_`-prefixed, each placed immediately before the leaf that uses it, same section)

| helper | before | content |
|---|---|---|
| `ht_contDiff_profile (e₁ lam)` | `blend_smooth` | `η ↦ φ((η−e₁)/lam)` is `C^∞` |
| `ht_exists_deriv_eq_slope (hd : Differentiable ℝ d) (hab : a < b)` | `sep_of_deriv` | `∃ c ∈ Ioo a b, deriv d c * (b − a) = d b − d a` (MVT from Rolle) |
| `ht_hasDerivAt_blend hf hg e₁ lam η` | `deriv_blend_ge` | `HasDerivAt (blend f g e₁ lam) ((1−φ)f' + φg' + (φ'/lam)(g−f)) η` |
| `ht_sep_of_deriv_left hf hg h0 hd` | `deriv_blend_le` | `g > f` on `[e₂−lam, e₂)` from `f e₂ = g e₂`, `g' < f'` there |
| `ht_deriv_eq_of_eqOn_Icc hF hF' hab h ht` | `rot_sub_rot_of_window` | equal derivatives on a closed interval of agreement (endpoints included) |
| `ht_offWindow_of_mem_Icc (ht : t ∈ Icc s₂ (s₁+1))` | `rot_sub_rot_of_window` | `OffWindow s₁ s₂ t` |

`ht_exists_deriv_eq_slope` and `ht_deriv_eq_of_eqOn_Icc` are general and reusable (Unit G's
`ξ_strictMonoOn/ξ_strictAntiOn/η_strictMonoOn`, Unit A's `deriv_eq_of_offWindow`). They sit in the Unit H/T
positions of the file, *after* Unit G's leaves; if another unit wants them the assembler may hoist them
(helpers are not frozen) or that unit duplicates them under its own prefix.

## Mathlib pitfalls (pin 85e3a25e, Lean v4.34.0-rc2)

1. **The MVT file is not in the import closure.** `strictMonoOn_of_deriv_pos`, `strictAntiOn_of_deriv_neg`,
   `monotoneOn_of_deriv_nonneg`, `exists_deriv_eq_slope`, `exists_hasDerivAt_eq_slope`,
   `Convex.image_sub_lt_mul_sub_of_deriv_lt` (Mathlib/Analysis/Calculus/Deriv/MeanValue.lean) are all
   *unknown identifiers* under `import SM.Rounding, SM.LinkMoves, SM.PolynomialBlock`. Available instead:
   Rolle `exists_hasDerivAt_eq_zero` (LocalExtr/Rolle.lean), the fencing lemma
   `image_le_of_deriv_right_lt_deriv_boundary` (Calculus/MeanValue.lean), `is_const_of_deriv_eq_zero`,
   `constant_of_derivWithin_zero`, `eq_of_derivWithin_eq`, `Monotone.deriv_nonneg`. The slope MVT is
   `ht_exists_deriv_eq_slope` (12 lines from Rolle). Do not add imports to a unit file (the assembler
   concatenates units; imports are part of the shared header).
2. `Real.smoothTransition.monotone : Monotone Real.smoothTransition` exists; with `Monotone.deriv_nonneg`
   it gives `0 ≤ deriv φ x` for every `x` — no case analysis at `0`, `1` and no need for the Unit P
   `iteratedDeriv_eq_zero_of_const_left/right`.
3. `Real.smoothTransition.contDiff {n : ℕ∞}` — use `(n := 1)` (or leave `n` to unify with `∞`);
   `ContDiff.differentiable` wants `n ≠ 0`, discharged by `(by decide)` (as in FrontSmooth.lean), *not*
   `le_rfl`.
4. `HasDerivAt.comp` against a lambda: `have hφa : HasDerivAt (fun η => φ ((η−e₁)/lam)) _ η := hφ.comp η ha`
   fails (higher-order unification of `?h₂ ∘ ?h`); write `have := hφ.comp η ha; exact this`.
5. `simpa`/`field_simp` rewrite `(η − e₁)/lam` to `-(e₁ * lam⁻¹) + lam⁻¹ * η` *inside* function bodies, which
   then no longer match `blend`. `((hasDerivAt_id' η).sub_const e₁).div_const lam` already has the type
   `HasDerivAt (fun η => (η − e₁)/lam) (1/lam) η` by defeq — no `simpa` needed. Prove the derivative identity
   with `simp only [Pi.sub_apply]` (the `HasDerivAt.sub`/`.mul` output contains `(c − d) x` Pi-applications)
   followed by `ring` (it handles `x / lam` vs `x * (1/lam)`).
6. `(shiftCurve c a).tangentLoop = c.tangentLoop.shift a` is `rfl`; `rot` unfolds by `show tw _ = tw _`.
7. `OffWindow` arithmetic: from `t + n ∈ Ioo s₁ s₂` and `t ∈ Icc s₂ (s₁+1)` get `(n:ℝ) < 0` and `-1 < (n:ℝ)`
   by `linarith`, cast with `exact_mod_cast`, close with `omega`.

## Notes for the assembler / executor

- Unused-hypothesis warnings on the frozen statements are inherent and harmless: `hlam` in `blend_smooth`
  (smoothness holds for every `lam`, since `x/0 = 0`), `sep_of_deriv` (interval empty for `lam ≤ 0`) and
  `blend_between` (also `hη` unused: `f ≤ blend ≤ g` holds at every `η` with `f η ≤ g η`); `hpos` in
  `deriv_blend_ge` and `hneg` in `deriv_blend_le` are not needed for the inequalities `f' ≤ h'` / `h' ≤ f'`
  themselves — they are there for the consumer (Unit R) to conclude `h' > 0` / `h' < 0`. When porting to
  `SM/Curl.lean` the executor may drop them or keep them as printed; the proofs work either way.
- `rot_sub_rot_of_window` needs only `Differentiable` of both loops (from `SmoothLoop.differentiable`), the
  window facts `s₁ < s₂`, `s₂ − s₁ < 1`, and `hsame` on the closed arc `[s₂, s₁ + 1]` (which `OffWindow`
  supplies including endpoints). The assembly's use at `rot_eq` (§8) compiles unchanged.
- No leaf was false or needed a stronger hypothesis. Nothing was written under `work/lean`.
