# GF_U_P4_REPORT.md — unit P4 (transverse, finite double points) of `GF_Skeleton.lean`

Date: 2026-09-14.  File: `work/drafts/fd/GF_U_P4.lean` (792 lines; skeleton 625).
Compile: `cd work/lean && lake env lean ../drafts/fd/GF_U_P4.lean` — **0 errors**, 24 `declaration uses
sorry` warnings (the 24 leaves of the other units), no other warnings, ~7 s.
`grep -c sorry`: 27 before → 25 after (the two P4 leaves; the remaining 25 = 24 leaves + the mention in
the module docstring, line 15).  `diff GF_Skeleton.lean GF_U_P4.lean` removes exactly the two lines
`  sorry` of P4.1 and P4.2; every definition, statement, name and docstring is byte-identical.
`#print axioms` for both leaves: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, i.e. P4 does
not use any other unit's leaf (it needs only the `Stage2` fields).

## Leaves proved (2 of 2)

| leaf | name (line) | proof |
|---|---|---|
| P4.1 | `transverse_double_of_stage2` (476) | `x′(θ) ≠ 0`, `x′(η) ≠ 0` from `NoCuspOnBranch` (with `SameParam` symmetry for the second); `y(θ) ≠ y(η)` else `L θ = L η` coordinatewise (`ext i; fin_cases i`) and `IsEmbeddedCircle.injective` gives `SameParam`; `z′ = y x′` from `IsLegendrian` (`alpha` unfolded, coordinate derivatives via `ContactMotions.hasDerivAt_coord`); `det = x′(θ)x′(η)(y(η) − y(θ))` by `ring`, `mul_ne_zero`. |
| P4.2 | `finite_double_of_stage2` (584) | by contradiction: an infinite set `S = doublePoints ∩ Ico×Ico ⊆ Icc×Icc` (compact) has an accumulation point `(θ₀,η₀)` (`Set.Infinite.exists_accPt_of_subset_isCompact`); `G = gp4_G L` vanishes on `S`, is continuous, so `G(θ₀,η₀) = 0`, i.e. `front L θ₀ = front L η₀`.  Case `SameParam θ₀ η₀`: every pair in the ball of radius `δc/2` has `circDist < δc` (`gp4_circDist_le` with `k = −k₀`), so the collar forbids it being a double point — contradiction with `accPt_iff_nhds`.  Case `¬SameParam`: `(θ₀,η₀)` is a double point, transverse by `ht`, `G` is injective on a neighbourhood (`gp4_G_injOn_nhds`, IFT), so no second zero of `G` nearby — contradiction. |

No leaf was found false; no hypothesis needed changing.  The printed argument (sm-3:2715-2724) is
followed exactly; the "closed in compact `K₂`" step is replaced by the accumulation-point argument
above, which avoids proving that `circDist` is continuous (it involves `round`).

## Helpers added (all `gp4_`-prefixed, immediately before the leaf that uses them)

Before P4.1:
- `gp4_deriv_coord` (453): `deriv (coordX L) θ = deriv L θ 0` (and `Y`/`1`, `Z`/`2`) for `ContDiff ℝ ∞ L`.
- `gp4_deriv_z` (461): `deriv (coordZ L) θ = coordY L θ * deriv (coordX L) θ` for smooth Legendrian `L`.
- `gp4_sameParam_symm` (469): `SameParam θ η → SameParam η θ`.

Before P4.2:
- `gp4_circDist_le` (506): `circDist θ η ≤ |θ − η − 2πk|` for every `k : ℤ` (from `round_le`).
- `gp4_G` (518) — a helper **definition**: `gp4_G L (θ,η) = (x θ − x η, z θ − z η) : ℝ × ℝ`.
- `gp4_front_eq_iff` (521): `front L θ = front L η ↔ gp4_G L (θ, η) = 0`.
- `gp4_G_injOn_nhds` (526): at a transverse double point, `∃ U ∈ 𝓝 (θ₀,η₀), InjOn (gp4_G L) U` (strict derivative, `2×2` matrix injective from `det ≠ 0`, `LinearEquiv.ofBijective` → `toContinuousLinearEquiv`, `HasStrictFDerivAt.toOpenPartialHomeomorph`).

The first three (`gp4_deriv_coord`, `gp4_deriv_z`, `gp4_sameParam_symm`) are generic and could be
reused by P1.4, P3.3, P3.4 (`z′ = y x′`, symmetry of `SameParam`); the assembler may deduplicate.

## Mathlib pitfalls (this pin)

1. `HasStrictDerivAt.comp_hasStrictFDerivAt` does not unify against `fun p => f p.1` (higher-order
   pattern): state the goal as `f ∘ (Prod.fst : ℝ × ℝ → ℝ)` and first name
   `hf : HasStrictFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasStrictFDerivAt_fst`
   (passing `hasStrictFDerivAt_fst` inline leaves the implicit arguments unresolved).  The resulting
   `(h1.sub h2).prodMk (h3.sub h4)` (Pi-subtraction of functions) is accepted by `exact` for the
   `gp4_G` goal up to defeq.
2. `HasStrictFDerivAt.prodMk` is the function-level product (`.prod` is for `ContinuousLinearMap`).
3. Notation precedence: `ℝ × ℝ ≃L[ℝ] ℝ × ℝ` parses as `ℝ × (ℝ ≃L[ℝ] ℝ × ℝ)` — write
   `(ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)`; same for `→ₗ[ℝ]`.  (`→L[ℝ]` happened to parse.)
4. Building a `ContinuousLinearEquiv` from an injective CLM on `ℝ × ℝ`:
   `LinearMap.injective_iff_surjective (f := (A : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))).1`, then
   `(LinearEquiv.ofBijective _ hbij).toContinuousLinearEquiv`; `(E : _ →L[ℝ] _) = A` is closed by
   `ContinuousLinearMap.ext fun w => by simp [E]`.  Injectivity via `injective_iff_map_eq_zero`, the
   `2×2` computation by `simp [A]` (`A w = (xθ * w.1 − xη * w.2, zθ * w.1 − zη * w.2)`) and
   `linear_combination zη * h1 − xη * h2` / `zθ * h1 − xθ * h2` giving `det * w.1 = 0`, `det * w.2 = 0`.
   `Mathlib` also has `ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero`, but computing `.det`
   of a CLM on `ℝ × ℝ` looked harder than the above.
5. `HasStrictFDerivAt.toOpenPartialHomeomorph f` (an `OpenPartialHomeomorph`): use `.open_source`,
   `hf.mem_toOpenPartialHomeomorph_source`, `.injOn` and rewrite with
   `hf.toOpenPartialHomeomorph_coe` to get `InjOn f source`.
6. `rw [abs_mul]` on `|2 * π * t|` rewrites `|2 * π|` into `|2| * |π|` too; use `abs_mul (2 * π)`.
7. `Set.Infinite.exists_accPt_of_subset_isCompact hs hK hsub : ∃ x ∈ K, AccPt x (𝓟 s)`;
   `accPt_iff_nhds : AccPt x (𝓟 C) ↔ ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x`; `AccPt.clusterPt` +
   `mem_closure_iff_clusterPt` put the accumulation point in `closure S`.
8. `Prod.dist_eq` (sup metric) + `le_max_left/right` + `Real.dist_eq` for the ball in `ℝ × ℝ`.
9. Smoothness order: `hcx.hasStrictDerivAt (by simp)` (`∞ ≠ 0`), `hL.differentiable (by simp)`
   (`1 ≤ ∞`), as in `SM.ContactMotions`.  `fun_prop` proves `Continuous (gp4_G L)` after
   `unfold gp4_G` once `hcx.continuous`, `hcz.continuous` are in context.
10. `ext i; fin_cases i` on `EuclideanSpace ℝ (Fin 3)` gives goals with `⟨0,_⟩`-style indices; use
    `show L θ 0 = L η 0` before `exact congrArg Prod.fst hfr` (the `front` components are defeq to
    the coordinates).

## For the assembler / executor

- Copy lines 453–631 of `GF_U_P4.lean` (the P4 block from `gp4_deriv_coord` to the end of
  `finite_double_of_stage2`) over the P4 block of the skeleton; nothing else in the file changed.
- `step3` type-checks against the proved leaves unchanged.
- The scratch files used are `/tmp/p4/scratch.lean`, `/tmp/p4/axioms.lean` (six imports + skeleton
  lines 1-270 + the P4 block); nothing was written under `work/lean`.
