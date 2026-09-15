# U_L_REPORT — unit L (local analysis at time μ) of ce:rounding (row 89)

File: `work/drafts/cerounding/U_L.lean` (byte-identical copy of `Skeleton_FINAL.lean` + the nine unit-L
proof bodies + three helpers).  Prover: pod subagent, 2026-09-14.
Check: `cd work/lean && lake env lean ../drafts/cerounding/U_L.lean` — exit 0, **0 errors**, 24 warnings
`declaration uses sorry` (= the 33 − 9 leaves of the other units), the same cosmetic warnings as the
skeleton (2 unused simp args in `chart_add_disp`, `letI` style hints — two of them in my `core_joint_contDiff`
and `core_eventuallyEq_of_notMem`, which follow the skeleton's `letI : Fintype L.cuspSet := C.fin` idiom).
`grep -c sorry`: 37 before → 28 after (the 4 non-leaf hits are docstring/comment mentions).
`diff Skeleton_FINAL.lean U_L.lean | grep '^<'` = exactly nine lines `  sorry` — no definition, statement,
name or docstring was touched.

## Leaves proved (9 / 9) — all TRUE as stated, no hypothesis missing

| leaf | line | proof in one line |
|---|---|---|
| `core_joint_contDiff` | 588 | `unfold core`, `ContDiff.add` (`(L.smooth i).comp contDiff_snd`), `ContDiff.sum`, `split_ifs`, `unfold CuspChoice.disp`, `fun_prop` with `Real.smoothTransition.contDiff`, `u_smooth`, `chi_contDiff` in context |
| `arcs_disjoint_circle` | 646 | a common `t` puts `xzOf (L.T k.1.1) t` in `U k` (`arc_in`) and `xzOf (L.T k'.1.1) (t − n) = xzOf (L.T k'.1.1) t` (`projLoop.eq_add_int (−n)`) in `U k'`; `C.disjoint` |
| `chart_core` | 684 | `core_on_arc` + `xz_disp` give `xzOf core t = xzOf (L.T) t + s • (A, A y₀)`; `chart_add_disp`, `chart_proj` (`Icc_subset_J`) |
| `inside` | 696 | `mem_U_iff`, `chart_core`; `|μ ε u χ| ≤ M²` from `μ ∈ [0,1]`, `ε ≤ M`, `abs_u_le_M`, `χ ∈ [0,1]`; `u² ≤ M²` via `sq_abs`/`pow_le_pow_left₀`; cubes by `Odd.pow_le_pow` from `u_mem_Icc_of_mem` |
| `arc_regular` | 751 | see below |
| `arc_injOn` | 816 | `chart_core` twice, second components `u s³ = u t³`, `cube_injective`, `u_injOn` on `J` |
| `arc_no_crossing` | 828 | three cases, see below |
| `core_eventuallyEq_of_notMem` | 922 | supports `[t₀ − r, t₀ + r] ⊂ (a, b)` (`r < η`); `eventually_add_int_notMem_Icc`; `Filter.eventually_all` over `Fintype L.cuspSet`; then `core = L.T` by `Finset.sum_eq_zero` + helper `ul_chi_eq_zero_of_notMem_Icc` |
| `deriv_xz_ne_zero_of_notMem` | 953 | a zero puts `(i, fract t) ∈ cuspSet` (`projLoop.deriv_eq_add_int`, as in `regular_of_no_cusps`); that cusp `k` has `a_lt`/`lt_b`, so `t + (−⌊t⌋) ∈ Ioo (a k) (b k)` — contradiction with `h k rfl` |

**`arc_regular` (the printed 3111-3117).**  Suppose `deriv (xzOf core) t = 0`.  `HasDerivAt.prodMk` +
`.deriv` give `x′ = z′ = 0` for the core coordinates.  The two chart coordinates of the rounded arc, as
real functions `P s = (x s − x₀)/A`, `Q s = 3(z s − z₀ − y₀(x s − x₀))/(2A)`, therefore have derivative `0`
at `t` (`sub_const`, `const_mul`, `div_const`).  On the open arc they equal `u² + μ ε u χ` and `u³`
(helper `ul_chart_core_coords` = `chart_core` read componentwise), so by `Ioo_mem_nhds` +
`Filter.eventuallyEq_of_mem` + `HasDerivAt.congr_of_eventuallyEq` + `HasDerivAt.unique`:
`3 u(t)² u′(t) = 0` and `2 u u′ + μ ε (u′ χ + u χ′) = 0`, where `u′ = y′ ≠ 0` on `J` (`y_deriv_ne`; helper
`ul_hasDerivAt_u`).  Hence `u t = 0`, so `t = t₀` (`u_injOn`, `u_t₀`), so `χ t = 1` (`chi_cusp`), and the
first equation collapses to `μ ε u′(t₀) = 0` — impossible for `μ > 0`, `ε > 0`.  No sign assumption on `u′`
is used ("Composing with the smooth coordinate u preserves this when du/dθ < 0 as well").

**`arc_no_crossing` (3118-3131, CE-R10 probe).**  Let `xzOf (core μ q.1) q.2 = xzOf (core μ k.1.1) t ∈ U k`
(`inside`).
* Cases 1-2 (`q` lies mod 1 on the open arc of some `k'`): `inside` puts the point in `U k'`
  (periodicity via `coreLoop.eq_add_int`), so `k = k'` by `C.disjoint`, then `arc_injOn` gives
  `q.2 + n = t`, i.e. `SameParam (k.1.1, t) q` — contradiction.
* Case 3 (`q` on no open arc): `core_eq_of_notMem` makes the point `xzOf (L.T q.1) q.2 ∈ U k`; `clean` gives
  `q.1 = k.1.1` and `q.2 + n ∈ Icc a b`, and since it is not in `Ioo a b`, `q.2 + n ∈ {a, b}` — the unmoved
  parameter is an END of the arc, as the plan predicted.  Chart: `chart_proj` at the end vs `chart_core` at
  `t`; second components give `u(q.2+n)³ = u t³`, so `u(q.2 + n) = u t` (`cube_injective`).  But `u t ∈ Ioo uMin uMax`
  (`u_mem_Ioo_of_mem`) while `u a, u b ∈ {uMin, uMax}` (`uMin = min (u a) (u b)`, `uMax = max …`):
  `min_lt_iff`/`lt_max_iff` + `linarith` close both ends, for either direction of monotonicity of `u`.
  The leaf is TRUE as stated; nothing extra is needed.

## Helpers added (all in `namespace SpatialLink.Choices`, immediately before the leaf that uses them)

* `ul_hasDerivAt_u {i t₀} (g : L.GermData i t₀) (t) : HasDerivAt g.u (deriv (yOf (L.T i)) t) t` (line 728;
  does not mention `C`, so `C` is not an argument) — for `arc_regular`.
* `ul_chart_core_coords (μ) (k) {s} (hs : s ∈ Ioo a b) : (xOf core s − x₀)/A = u² + μ ε u χ ∧ 3(zOf core s − z₀ −
  y₀(xOf core s − x₀))/(2A) = u³` (line 737) — `chart_core` componentwise, for `arc_regular`.
* `ul_chi_eq_zero_of_notMem_Icc {k} (ch : L.CuspChoice k) {s} (h : ∀ n : ℤ, s + n ∉ Icc (k.1.2 − ch.r) (k.1.2 + ch.r)) :
  ch.chi s = 0` (line 905) — `periodicBump_eq_zero` in the parameter, for `core_eventuallyEq_of_notMem`.

## Black boxes used (other units' leaves, as hypotheses)

U-G: `chart_proj`, `u_strictMonoOn_or_strictAntiOn` (through the proved `u_injOn`), `uMax_pos` (through
`M_pos`), `u_mem_Icc_of_mem`, `u_mem_Ioo_of_mem`, `abs_u_le_M`, `rect_subset_closedBall` (through
`norm_chart_le_of_mem_U` — not actually needed by U-L).  U-C: `arc_in`, `clean`, `chi_eq_zero_of_notMem`
(through `disp_eq_zero_of_notMem` in the proved `core_eq_of_notMem`).  U-P: `periodicBump_zero` (through
`chi_cusp`), `periodicBump_eq_zero`.  No U-E leaf is used.

## Mathlib / Lean pitfalls met (for the assembler and the other units)

1. `HasDerivAt.add` / `.mul` / `.pow` return the Pi-form functions `f + g`, `f * g`, `f ^ n`; `convert … using 1`
   against a `fun s => …` target then leaves instance-equality goals (`Real.instAddCommGroup = …`).  Use the
   `to_fun` variants `HasDerivAt.fun_add`, `.fun_mul`, `.fun_pow` and normalise the derivative value with
   `HasDerivAt.congr_deriv` + `simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]` (the `pow` derivative is
   `↑n * f x ^ (n − 1) * f′`).  `sub_const`, `const_mul`, `div_const` are already in lambda form.
2. `∀ᶠ s in nhds t, … s + n …` with `n : ℤ` elaborates `s : ℤ` (the binder type is taken from the body):
   write `∀ᶠ (s : ℝ) in nhds t, … s + (n : ℝ) …`.
3. `deriv_xzOf` / `deriv_space` are declared in §4.7, AFTER the U-L leaves, so `arc_regular` cannot cite them;
   `(hx.prodMk hz).deriv` inline does the job (the skeleton's `core_xz_regular` glue uses `deriv_xzOf` only
   later, fine).
4. `Filter.eventually_all` needs `[Finite ι]`; `letI : Fintype L.cuspSet := C.fin` provides it.
   `eventually_add_int_notMem_Icc` is at `SM` top level in SM/FrontSmooth.lean (not in `SmoothFront`).
5. `Odd.pow_le_pow (hn : Odd n) : a ^ n ≤ b ^ n ↔ a ≤ b` is an iff (use `.mpr`); for `u² ≤ M²` with `u` of either
   sign use `sq_abs` and `pow_le_pow_left₀ (abs_nonneg _) h 2`.
6. `CuspChoice.a`/`.b` unfold to `k.1.2 − η` / `k.1.2 + η` by `rfl`; anonymous-constructor `⟨ht.1.le, ht.2.le⟩`
   for `t ∈ Icc (k.1.2 − η) (k.1.2 + η)` type-checks by defeq, no `unfold` needed (where `linarith` is
   involved, `unfold CuspChoice.a` or an explicit `rfl` equation is needed, as in `core_eventuallyEq_of_notMem`
   and `arc_no_crossing`).
7. `SameParam (k.1.1, t) q` unfolds to `k.1.1 = q.1 ∧ ∃ n, q.2 = t + n` — direction of the `Fin` equality
   matters (`hk'`, not `hk'.symm`; `clean` returns `q.1 = k.1.1`, so `hq' k hq1.symm`).
8. Compile time: the truncated file (through the first `end Choices`) compiles in ~8 s, the full file in ~8 s
   too on this pod — iterate freely.

## Nothing left for U-L

All nine leaves are proved; no counterexample, no strengthened hypothesis.  The assembler can take the nine
bodies (lines 588-965 region) and the three `ul_` helpers verbatim; they depend only on the frozen statements
of U-P/U-G/U-C leaves and on Mathlib.
