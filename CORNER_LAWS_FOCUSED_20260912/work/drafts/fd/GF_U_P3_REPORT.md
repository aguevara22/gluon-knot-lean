# GF_U_P3_REPORT.md — unit P3 of `GF_Skeleton.lean` (row 87 fd:generic-front)

Date: 2026-09-14.  File: `work/drafts/fd/GF_U_P3.lean` (1512 lines; skeleton 625).
Check: `cd work/lean && lake env lean ../drafts/fd/GF_U_P3.lean` → **0 errors**, exactly the 22
`declaration uses sorry` warnings of the other units' leaves, no other warning.
`grep -c sorry`: 27 before → 23 after (22 leaf sorries of units P0, P1, P2, P4, P5, P6 + the word in
the module docstring, line 15).  `diff GF_Skeleton.lean GF_U_P3.lean` = insertions only plus the four
lines `  sorry` of the P3 leaves; no statement, name or docstring changed.

## Leaves proved (4 of 4)

| leaf | name | axioms |
|---|---|---|
| P3.1 | `hamVF_local_models` | `[propext, Classical.choice, Quot.sound]` |
| P3.2 | `exists_CR_avoidance` | `[propext, sorryAx, Classical.choice, Quot.sound]` — `sorryAx` only through the black boxes P0.3 `fderiv_composeFlows_zero` and P1.4 `deriv_y_ne_zero_at_cusp` |
| P3.3 | `noCuspOnBranch_of_C` | `[propext, Classical.choice, Quot.sound]` |
| P3.4 | `noTriple_of_R` | `[propext, Classical.choice, Quot.sound]` |

Leaves left: none.  All four statements are true as stated; no hypothesis needed strengthening.

## How the proofs go

**P3.1.** `gp3_hamVF_congr` (`H₁ =ᶠ[𝓝 p] H₂ ⇒ hamVF H₁ p = hamVF H₂ p`, from
`Filter.EventuallyEq.fderiv_eq` and `.eq_of_nhds`) reduces `χ·f` to `f`; then explicit
`HasFDerivAt` computations give `hamVF (−(y−c)) p = !₂[1,0,c]` **at every `p`** (`gp3_hamVF_Hx`),
`hamVF 1 p = !₂[0,0,1]` (`gp3_hamVF_Hz`), and
`hamVF (−½(y−c)²) p = !₂[y−c, 0, −½(y−c)² + y(y−c)]` (`gp3_hamVF_H2`; `x`-velocity `y − c`, zero at
`y = c`).

**P3.2** (the bulk, ≈ 600 lines).  Structure:
1. *Joint map.* `gp3_G L m Hs (a, θ) := composeFlows m Hs a (L θ)` on `(Fin m → ℝ) × ℝ`, `C^∞` by
   `fd_contact_motions.compositions_smooth`; coordinates `gp3_Gk`.  The linear slice
   `gp3_σ d m j : ℝ^d × ℝ^m →L[ℝ] (Fin m → ℝ) × ℝ`, `z ↦ (par z.2, z.1 j)` (`par` is literally
   `⇑(PiLp.continuousLinearEquiv 2 ℝ _)`, `rfl`).  `gp3_Cmap_eq`/`gp3_Rmap_eq` rewrite `Cmap`, `Rmap`
   as `!₂[…]` of compositions with the slices ⇒ `gp3_contDiff_Cmap`, `gp3_contDiff_Rmap`
   (`contDiff_euclidean` + `fin_cases`).
2. *Derivative at `a = 0`.* `gp3_fderiv_Gk_zero`: `∂_{a_i} G_k(0,θ) = hamVF (Hs i) (L θ) k` from P0.3
   via `gp3_fderiv_slice_left` and `fderiv_apply_coord`.  The `x_a′(θ)` component needs the symmetry
   of mixed partials: `gp3_fderiv_fderiv_comm` (from `ContDiffAt.isSymmSndFDerivAt` with
   `ContactMotions.minSmoothness_two_le`, converting `fderiv (fun y => fderiv f y w) x v` to
   `fderiv (fderiv f) x v w` by `fderiv_clm_apply`).  Result: `gp3_fderiv_Cmap_zero`
   `fderiv (Cmap L m Hs) (t,0) (0, single i 1) = gp3_colC L (Hs i) (t 0) (t 1)` with
   `gp3_colC L H θ η = !₂[∂_θ (X_H(L θ))_x, X_H(L θ)_x − X_H(L η)_x, X_H(L θ)_z − X_H(L η)_z]`, and
   `gp3_fderiv_Rmap_zero` with `gp3_colR` (four components).  Both columns depend only on the single
   Hamiltonian `Hs i`, so the family can be assembled after the charts are chosen.
3. *Charts.* `gp3_exists_C_chart`: at `(θ₀, η₀)` with `x′(θ₀) = 0` and `L θ₀ ≠ L η₀`, bumps of radius
   `dist/2` at the two points (`ContDiffBump`, `gp3_exists_bump`), Hamiltonians
   `χ₁·(−½(y−y₀)²)`, `χ₂·(−(y−y_η))`, `χ₂·1`; columns `(y′(θ₀), 0, 0)`, `(0, −1, −y_η)`,
   `(0, 0, −1)` (P1.4 gives `y′(θ₀) ≠ 0`); independence by `Fintype.linearIndependent_iff` and the
   three coordinate equations.  `gp3_exists_R_chart`: bumps at `L η₀`, `L τ₀` of radius
   `min(dists)/2`, columns `(−1, −y_η, 0, 0)`, `(0,−1,0,0)`, `(0,0,−1,−y_τ)`, `(0,0,0,−1)`.
   The sets where the columns stay independent are open (`gp3_isOpen_colC/colR`, from
   `isOpen_setOfPred_linearIndependent` and `ContDiff.deriv'`).
4. *Family.* Zero sets `ZC ⊆ K2 δc`, `ZR ⊆ K3 δc` of the `a = 0` slices are compact; `choose` a chart
   per zero; `IsCompact.elim_nhds_subcover'` gives `Finset`s `bC`, `bR`; index type
   `κ := (↥bC × Fin 3) ⊕ (↥bR × Fin 4)`, `m := Fintype.card κ`, `Hs := HH ∘ (Fintype.equivFin κ).symm`,
   index maps `ιC k j := e (Sum.inl (k, j))`, `ιR`.
5. *Shrinking (generic).* `gp3_exists_paHyp`: for `K` compact, `F` `C^∞`, `d < q`, and any indexed
   family `ι : κ → Fin q → Fin m` such that every zero `(t, 0)`, `t ∈ K`, has independent columns
   `fderiv F (t,0) (0, single (ι k j) 1)` for some `k`, there is `r > 0` with
   `ParameterAvoidanceHyp d m q K 0 r' F` for all `0 < r' ≤ r`.  Proof: `W := ⋃ k {independent}` is
   open and has rank `q` (`gp3_finrank_of_indep`: `finrank_span_eq_card` + `Submodule.finrank_mono`
   + `rank_eq_iff_range_eq_top`); `S := (K × B̄₁) ∩ F⁻¹{0} \ W` is compact and misses `a = 0`, so
   `‖a‖` has a positive minimum on `S` (or `S = ∅`), and `r := min 1 (‖a_min‖/2)`.  No minima of
   `‖F‖` and no `generalized_tube_lemma` are needed.  Final radius `min (min rC rR) r₀`.

**P3.3 / P3.4.** Reduce `θ, η(, τ)` to `[0, 2π)` by `toIcoMod` (`gp3_exists_reduce`, giving
`SameParam θ θ̄`); `SameParam` is symmetric/transitive; `Φ_a ∘ L` is `2π`-periodic
(`gp3_periodic_comp`), so `front` and `deriv (coordX ·)` are invariant (`gp3_front_eq_of_sameParam`,
`gp3_deriv_coordX_eq_of_sameParam` via `deriv_comp_add_const`).  If some pair has
`circDist < δc` the collar `hδa` contradicts the front equality; otherwise the reduced tuple lies
in `K2 δc` (`K3 δc`) and `Cmap`/`Rmap` vanish there (`gp3_xParam_eq`, `gp3_frontParam_eq` are `rfl`),
contradicting `ha` via `mem_zeroParams`.  `hHs` is not needed in either leaf (`have _ := hHs`
silences the unused-variable linter; the statement is frozen).

## Helpers added (all `gp3_`-prefixed, placed before the leaf that first uses them)

Before P3.1: `gp3_hamVF_congr`, `gp3_hamVF_eq_zero_of_notMem`, `gp3_hamVF_Hx`, `gp3_hamVF_Hz`,
`gp3_pd_H2`, `gp3_hamVF_H2`, `gp3_hamVF_H2_zero`, `gp3_hamVF_H2_at`.

Before P3.2: circular distance — `gp3_circDist_eq` (`= 2π·min(fract u, 1−fract u)`),
`gp3_continuous_circDist`, `gp3_circDist_eq_zero_of_sameParam`, `gp3_not_sameParam_of_le_circDist`;
coordinates/compactness — `gp3_proj` (def), `gp3_proj_apply`, `gp3_continuous_apply`,
`gp3_contDiff_apply`, `gp3_isCompact_box`, `gp3_isCompact_K2`, `gp3_isCompact_K3`; `gp3_xParam_eq`,
`gp3_frontParam_eq`; partial derivatives — `gp3_fderiv_slice_left`, `gp3_deriv_slice_right`,
`gp3_fderiv_comp_clm`, `gp3_fderiv_fderiv_comm`, `gp3_contDiff_fderiv_apply`,
`gp3_fderiv_apply_coord` (any `ℝ^n`); joint map — `gp3_G`, `gp3_Gk` (defs), `gp3_contDiff_G`,
`gp3_contDiff_Gk`, `gp3_σ` (def), `gp3_σ_apply`, `gp3_par_zero`, `gp3_par_single`, `gp3_σ_zero`,
`gp3_σ_single`, `gp3_xParam_deriv`, `gp3_fderiv_Gk_zero`, `gp3_Cmap_eq`, `gp3_Rmap_eq`,
`gp3_contDiff_Cmap`, `gp3_contDiff_Rmap`, `gp3_colC`, `gp3_colR` (defs), `gp3_fderiv_diff_zero`,
`gp3_fderiv_xderiv_zero`, `gp3_fderiv_Cmap_zero`, `gp3_fderiv_Rmap_zero`; avoidance —
`gp3_finrank_of_indep`, `gp3_isOpen_indep`, `gp3_exists_paHyp`; bumps/charts — `gp3_exists_bump`,
`gp3_hyp_of_bump`, `gp3_hamVF_bump_far`, `gp3_hamVF_bump_near`, `gp3_eventually_near`,
`gp3_eventually_far`, `gp3_exists_C_chart`, `gp3_exists_R_chart`, `gp3_contDiff_colC`,
`gp3_contDiff_colR`, `gp3_isOpen_colC`, `gp3_isOpen_colR`.

Before P3.3: `gp3_sameParam_symm`, `gp3_sameParam_trans`, `gp3_exists_reduce`, `gp3_periodic_comp`,
`gp3_front_eq_of_sameParam`, `gp3_deriv_coordX_eq_of_sameParam`.

## Reusable by other units (for the assembler / unit P1)

- `gp3_exists_paHyp` is exactly the "uniform ball" step of P1.1 (`(d,q) = (1,2)`, `K = Kper1`): P1.1
  needs only `IsCompact Kper1`, `ContDiff ℝ ∞ (cuspMap L n Hs)`, and independent columns at the zeros
  of the `a = 0` slice.  `gp3_fderiv_xderiv_zero` (the `x_a′` column through the mixed-partial
  symmetry) and `gp3_fderiv_Gk_zero` give those columns; the `x_a″` column needs one more
  θ-derivative (not done here).
- `gp3_fderiv_fderiv_comm`, `gp3_fderiv_slice_left`, `gp3_deriv_slice_right`, `gp3_fderiv_comp_clm`,
  `gp3_fderiv_apply_coord` are generic calculus facts.
- `gp3_continuous_circDist`, `gp3_isCompact_box`, `gp3_exists_reduce`, the `SameParam` lemmas and
  the periodicity lemmas serve P2/P4 (collar, finiteness in one period square).
- `gp3_exists_bump`, `gp3_hyp_of_bump`, `gp3_hamVF_bump_far/near` are the bump-Hamiltonian toolkit
  for P1.1 and P5.4.

## Mathlib pitfalls met (this pin)

- `WithLp` is a structure: `a i` is `a.ofLp i`; `par = ⇑(PiLp.continuousLinearEquiv 2 ℝ _)` is
  `rfl`; `!₂[a,b,c] = WithLp.toLp 2 ![a,b,c]`.  `(!₂[…]) k` reduces by `simp` (and by `rfl`/`exact` at
  default transparency), but `simp only [Matrix.cons_val_two]` does not fire and `simpa` fails to
  see `![f,g,h] 2 = h` (reducible transparency) — use `simp only [Fin.sum_univ_three] at hg; exact hg`.
- `PiLp.proj 2 (fun _ => ℝ) i` leaves `𝕜` as a stuck metavariable; wrap it once as
  `gp3_proj d i : ℝ^d →L[ℝ] ℝ`.
- Deprecations (warnings only, avoided): `isOpen_setOf_linearIndependent` →
  `isOpen_setOfPred_linearIndependent`; `ContinuousLinearMap.sub_apply` → `sub_apply`;
  `EuclideanSpace.single_apply` → `PiLp.single_apply`; `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`;
  `push_neg` → `push Not`.
- `ContDiff.differentiable` now takes `n ≠ 0` (use `(by simp)`), `ContDiff.continuous_fderiv` too.
- `fderiv_sub` is the `Pi.sub` form; the lambda form is `fderiv_fun_sub` (same for `fderiv_fun_const`).
- `HasDerivAt.prodMk` / `hasFDerivAt_prodMk_left` (not `.prod`, `prod_mk`).
- `HasFDerivAt.comp` produces `g ∘ σ`; state the `fun z => g (σ z)` form via a `have … : HasFDerivAt
  (fun z => …)` ascription before `.fderiv`, or `rw` will not match.
- `simp` rewrites `-(p 1 - c)` to `c - p 1` and `-(1/2) * x` to `-(2⁻¹ * x)` *before* applying a
  user lemma about the original function: unfold `hamVF`/`pd` and rewrite with the `HasFDerivAt`
  first (`simp only [hamVF, pd, hd.fderiv]`), then `simp`.
- `ContDiffAt.isSymmSndFDerivAt` needs `minSmoothness ℝ 2 ≤ n`; `ContactMotions.minSmoothness_two_le`
  supplies it for `n = ∞`.
- `Function.Periodic.deriv` does not exist; use `deriv_comp_add_const` after `funext`.
- `IsCompact.elim_nhds_subcover'` returns `Finset ↥s`; `↥b` for `b : Finset ↥s` is a `Fintype`, so
  `Fintype.equivFin ((↥bC × Fin 3) ⊕ (↥bR × Fin 4))` builds the `Fin m` family.
