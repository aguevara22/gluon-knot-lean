# TN_U_A_REPORT.md — Unit A (chart `F`) of `TN_Skeleton.lean`, row 84 fd:transverse-neighborhood

Date: 2026-09-14.  File: `work/drafts/fd/TN_U_A.lean` (1259 lines; started as a byte-identical copy
of `TN_Skeleton.lean`, 959 lines).  Check: `cd work/lean && lake env lean ../drafts/fd/TN_U_A.lean`
— **0 errors**, 33 `declaration uses sorry` warnings (the leaves of units B–F), ~11 s.
`grep -c sorry`: 42 before (40 leaves + 2 mentions in the header docstring) → 35 after (33 + 2).
`#print axioms` of all seven Unit-A leaves: `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

Statements, names and docstrings are untouched: `diff TN_Skeleton.lean TN_U_A.lean` removes exactly
seven lines, each `  sorry`; everything else is added lines (helpers + proof bodies).

## Leaves proved (7/7)

| id | name | line | proof in one line |
|---|---|---|---|
| A1 | `contDiff_chart` | 287 | `deriv T` smooth by `contDiff_infty_iff_deriv`; `aT` = coordinates of `T`, `deriv T` (`ContactMotions.contDiff_coord`); `cT` by `ContDiff.sqrt` with `2·aT > 0`; `E1 q = !₂[1,0,0] + q 1 • !₂[0,0,1]`; sums/`smul` |
| A2 | `chart_periodic` | 303 | `deriv_comp_add_const` + `funext` of `hT.circle.periodic` gives `deriv T` periodic; `simp only [aT/cT/chart, …]` |
| A3 | `fderiv_chart` | 353 | `ta_hasFDerivAt_chart`: explicit `HasFDerivAt` built from `HasFDerivAt.comp/smul/smul_const/add` with `toSpanSingleton`, `fst`, `snd`, `PiLp.proj`; then `.fderiv`, `ext i; fin_cases i <;> simp [E1, E2] <;> ring` |
| A4 | `exists_chart_bij_radius` | 445 | `{L ∣ Bijective L} = range (CLE → CLM)` is open (`ContinuousLinearEquiv.isOpen`); preimage under the continuous `fderiv ℝ (chart T)`; contains `Icc 0 (2π) ×ˢ {0}` (core injectivity + `finrank 3 = 3`); `generalized_tube_lemma`; `Metric.isOpen_iff` at `0`; `ρ = ε/2`; `θ` reduced by `Periodic.exists_mem_Ico₀` using `ta_fderiv_chart_periodic` |
| A5 | `exists_chart_inj_radius` | 487 | by contradiction (`push Not`); bad pairs reduced into `[0,2π]` with radii `1/(n+1)`; `IsCompact.tendsto_subseq` twice; `squeeze_zero_norm` for `w → 0`; `tendsto_nhds_unique` ⇒ `T a = T a'` ⇒ `a' = a + 2πk`; `HasStrictFDerivAt.toOpenPartialHomeomorph` at `(a,0)` (`ta_bijective_fderiv_core`), both sequences eventually in its source, `injOn` ⇒ contradiction |
| A6 | `chart_isOpen_image` | 576 | `isOpen_iff_mem_nhds`; CLE from bijectivity; `HasStrictFDerivAt.map_nhds_eq_of_equiv`; `Filter.image_mem_map` |
| A7 | `pullback_chart` | 1020 | A3 + `alpha` unfolded; `hg : aT·g = c u y′ − c v x′ − c c′ u v` (`field_simp`); `simp` on components; `linear_combination -τ * hg - (w 1 * η 0) * cT_sq` |

Leaves left in Unit A: **none**.  No leaf was found false or under-hypothesised.

## Helpers added (all `ta_`-prefixed, placed immediately before the first leaf that uses them)

Before A1 (260–285): `ta_contDiff_deriv`, `ta_contDiff_coord3`, `ta_contDiff_coord2`, `ta_contDiff_aT`,
`ta_contDiff_cT`, `ta_E1_eq`, `ta_contDiff_E1`.
Before A2 (295): `ta_deriv_periodic` (`deriv T (θ + 2π) = deriv T θ`).
Before A3 (313): `ta_hasFDerivAt_chart` (the `HasFDerivAt` form of A3 with an explicit CLM).
Before A4 (365–443): `ta_exists_cle_of_bijective` (bijective CLM `ℝ×ℝ² →L ℝ³` is a CLE),
`ta_isOpen_bijective` (the bijective CLMs form an open set), `ta_injective_fderiv_core`,
`ta_bijective_fderiv_core` (`DF(θ,0)` bijective), `ta_fderiv_chart_periodic` (`DF` is `2π`-periodic).
Before A5 (467–485): `ta_exists_reduce` (`∃ k : ℤ, θ − 2πk ∈ Icc 0 (2π)`), `ta_chart_periodic_int`
(`chart T (θ + 2πk, w) = chart T (θ, w)` for `k : ℤ`).

Reusable by other units (D6/D7 in particular): `ta_exists_cle_of_bijective` + `ContDiffAt.hasStrictFDerivAt`
give the `HasStrictFDerivAt f (↑e) x` needed for `HasStrictFDerivAt.map_nhds_eq_of_equiv`;
`ta_bijective_fderiv_core`'s finrank argument (`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`
with `(f := (L : ℝ × ℝ² →ₗ[ℝ] ℝ³))`, `hrank` by `simp`) is the injective ⇒ bijective step;
`ta_fderiv_chart_periodic` is the pattern for "fderiv of a periodic map is periodic"
(`HasFDerivAt.comp` with `(hasFDerivAt_id _).add_const`, then `funext` + `simp [periodicity]`).

## Mathlib pitfalls at this pin (v4.34.0-rc2, Mathlib 85e3a25e)

* `ContDiff.differentiable`, `ContDiff.continuous_fderiv`, `ContDiffAt.hasStrictFDerivAt` take `n ≠ 0`,
  not `1 ≤ n`; `(by simp)` proves `∞ ≠ 0`.  `ContDiff.iterate_deriv`/`contDiff_infty_iff_deriv` state
  `ContDiff 𝕜 (↑⊤)`, which is our `∞` (with `open scoped ContDiff`).
* `EuclideanSpace.proj i` has type `StrongDual …`; using `(EuclideanSpace.proj i).contDiff` against the
  expected type `ContDiff ℝ ∞ fun p => p i` fails to unify (the coercion is not unfolded).  Use
  `ContactMotions.coordCLM i` (ℝ³) or `(PiLp.proj 2 (fun _ : Fin 2 => ℝ) i : ℝ² →L[ℝ] ℝ)` (ℝ²); their
  application is `rfl`-reducible and `simp` evaluates it.  `EuclideanSpace.proj_apply` does not exist.
* Coordinates print as `x.ofLp i` (`WithLp` is a structure now); `simp` normalises `!₂[a,b,c] i`, `PiLp.add_apply`,
  `PiLp.smul_apply` fine; vector identities: `ext i; fin_cases i <;> simp [...] <;> ring`.
* `ext` on an equality of CLMs `ℝ × ℝ² →L[ℝ] ℝ³` goes too deep (splits through `inl/inr` and the `PiLp`
  coordinates, leaving `ℝ`-valued goals with anonymous indices).  Use
  `refine ContinuousLinearMap.ext fun ξ => ?_; obtain ⟨τ, η⟩ := ξ; ext i; fin_cases i …`.
* `convert h using 1` on `HasFDerivAt` goals produced instance-mismatch side goals
  (`Prod.instAddCommGroup = Prod.normedAddCommGroup.toAddCommGroup`, topologies).  Use
  `(h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)).congr_fderiv ?_` instead
  (function goal often `rfl`, CLM goal by `ext`/`simp`).
* `hcd.hasFDerivAt.comp (θ, w) hasFDerivAt_fst` with expected type `HasFDerivAt (fun p => cT T p.1) …`
  fails: the unifier unfolds `cT T` into `√ ∘ (2 * aT T ·)`.  Build the `have` WITHOUT an expected type
  (`hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ²) (p := (θ, w))`) and fix the function at the end.
* `push_neg` is deprecated (warning): use `push Not at h`.
* `Filter.image_mem_map` (namespaced), `Periodic.exists_mem_Ico₀`, `Periodic.int_mul` (gives `↑n * c`, so
  `rw [show 2 * π * k = k * (2 * π) by ring]` first), `IsCompact.tendsto_subseq (x := …)`,
  `StrictMono.id_le` (gives `id ≤ f`; `simp only [id] at this`), `tendsto_one_div_add_atTop_nhds_zero_nat`.
* `ta_exists_cle_of_bijective`: `(LinearEquiv.ofBijective (f : →ₗ) hf).toContinuousLinearEquiv`; the coercion
  equality `(↑e : CLM) = f` is `ContinuousLinearMap.ext fun x => rfl` (plain `ext; rfl` over-splits, see above).
* `generalized_tube_lemma isCompact_Icc isCompact_singleton` works directly with `Icc 0 (2π) ×ˢ {0}`;
  membership in `(fderiv ℝ (chart T)) ⁻¹' {L | Bijective L}` is definitionally `Bijective (fderiv …)`, so
  `exact` closes it without `mem_preimage`/`mem_setOf`.
* `linear_combination` sign: with `hg : aT·g = …` the coefficient is `-τ` (the residual printed by a wrong
  guess is `-2τ·(hg)`, i.e. the check reports twice the mistake).

## Notes for the assembler / executor

* Unit A has no dependence on other units; nothing here uses `GoodRadius` or unit-B leaves.  A7 uses only
  `fderiv_chart`, `cT_sq`, `aT_pos` and the definition of `gfun`.
* `pullback_chart` (A7) sits in `section model` (line 1020) as in the skeleton; its proof is
  self-contained (no helper).
* `ta_isOpen_bijective` uses `ContinuousLinearEquiv.isOpen` (Banach open mapping; `CompleteSpace (ℝ × ℝ²)`
  is found by instance search) — it is available through `SM.ContactMotions`'s imports; no import was added.
* Scratch files used: `/tmp/ta/scratchA.lean` (= file lines 1–258 + Unit A), `/tmp/ta/check1.lean`,
  `/tmp/ta/check2.lean` (name checks).  Total Unit A added text: 300 lines (helpers + bodies).
