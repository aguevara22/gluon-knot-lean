# W3S_S2 — unit S2 (the cusp local model): report

2026-09-14, prover for unit S2 of the U8R sweep (W3_U8R_PLAN.md §3/S2, §4).  File:
`work/drafts/frontrows/W3S_S2.lean` (15,868 lines) = `W3_U8R_Skeleton.lean` (15,587) + ONE inserted helper block
+ the five S2 leaf bodies.  `diff W3_U8R_Skeleton.lean W3S_S2.lean` = six hunks, all inside `namespace U8R`,
`section SweepLeaves`:

| hunk | what |
|---|---|
| `14953a14954,15204` | the block `/-! ### S2 helpers -/ section S2Helpers … end S2Helpers` (251 lines), inserted immediately before the docstring of `cusp_arm_sign` |
| `14960c15211,15222` | `cusp_arm_sign` — ` := sorry` → ` := by …` (statement text byte-identical) |
| `14966c15228,15235` | `leftCusp_x_local` |
| `14971c15240,15247` | `rightCusp_x_local` |
| `14977c15253,15256` | `leftCusp_arms` |
| `14982c15261,15264` | `rightCusp_arms` |

No definition, statement, name or docstring changed; no other unit's `sorry` touched; no import added.

**Compile** (`cd work/lean && lake env lean ../drafts/frontrows/W3S_S2.lean`): exit 0, **0 errors**, 63 s; the only
warnings are the 53 `declaration uses sorry` of the other units plus the skeleton's pre-existing linter warnings
(lines 13451, 13472, 14137, 14256, 14793-14794 — none in the inserted block).  `grep -c sorry`: **58 before, 53
after** (= 4 front-move leaves + 49 sweep leaves of S1/S3/S4/S5/S6).  `#print axioms` on a probe copy for
`cusp_arm_sign`, `leftCusp_x_local`, `rightCusp_x_local`, `leftCusp_arms`, `rightCusp_arms`, `s2_loop_cusp_sign`,
`s2_cubic_iff`: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

## 1. Leaves proved (5 of 5)

| leaf | proof (lines) | route |
|---|---|---|
| `cusp_arm_sign` | 12 (+ helpers) | `s2_loop_cusp_sign (F.comp i)` after rewriting `acc_def`/`jerk_def`, `cuspDisc` unfolded |
| `leftCusp_x_local` | 8 | `exists_xvel_sign_of_isLeftCusp` gives `δ` and the sign of `x'` on both sides; `s2_local_min_of_sign (hasDerivAt_x F i)` gives the two monotonicities; the no-cusp clause is `isCusp_iff_xvel_eq_zero` + the sign |
| `rightCusp_x_local` | 8 | mirror (`exists_xvel_sign_of_isRightCusp`, `s2_local_max_of_sign`) |
| `leftCusp_arms` | 4 | `leftCusp_x_local` + `s2_arms_of_local_min` (IVT on each side), continuity `(F.comp i).continuous.fst` |
| `rightCusp_arms` | 4 | `rightCusp_x_local` + `s2_arms_of_local_max` |

Leaves left: none.  No leaf was found false or in need of a stronger hypothesis; the sign law of `cusp_arm_sign`
is exactly the one the plan checked numerically (later arm higher ↔ `0 < cuspDisc`).

## 2. The route for `cusp_arm_sign` (why 250 lines instead of the planned 900)

No Taylor expansion, no matching of the arms.  With `γ''(t₀) = (a, c)` (`a ≠ 0` by `cusp_nonvertical`) put
`φ(t) := z(t) − (c/a)·x(t)`.  Then `φ'(t₀) = 0` (cusp), `φ''(t₀) = c − (c/a)a = 0`, and
`φ'''(t₀) = d − (c/a)b = det(γ'', γ''')/a =: K ≠ 0`, where `γ'''(t₀) = (b, d)`.  Since `φ'''` is continuous
(`SmoothLoop.continuous_iteratedDeriv 3`), `φ''' > 0` on a `δ`-interval when `K > 0`; hence `φ''` is negative
before `t₀` and positive after (`φ''(t₀) = 0`, `strictMonoOn_of_deriv_pos` on the two closed half-intervals);
hence `φ' > 0` on both sides of `t₀` (`φ'(t₀) = 0`, decreasing before / increasing after); hence `φ` is strictly
increasing on `Icc (t₀−δ) t₀` and on `Icc t₀ (t₀+δ)`, so `φ(t₁) < φ(t₀) < φ(t₂)` for `t₁ < t₀ < t₂` in the
interval — for ANY such pair, matched or not.  When `x(t₁) = x(t₂)`, `z(t₂) − z(t₁) = φ(t₂) − φ(t₁)`, so
`z(t₁) < z(t₂)`.  For `K < 0` apply the same to `−φ`.  Finally `0 < K ↔ 0 < a·det = cuspDisc` because
`a·det = K·a²`.  (The plan's `u³(ad − bc)/(3a)` is the leading term of `φ(t₂) − φ(t₁)`; the monotonicity argument
makes the remainder estimate unnecessary.)

The chain `φ''' > 0 ⇒ φ'' sign ⇒ φ' > 0 off t₀ ⇒ φ(t₁) < φ(t₂)` is the generic `s2_cubic_lt`; `s2_cubic_iff` adds the
sign split; `s2_loop_cusp_sign` is the statement for one `SmoothLoop` in terms of `deriv`/`iteratedDeriv 2`/
`iteratedDeriv 3`, and the leaf only translates `IsCusp`, `acc`, `jerk`, `cuspDisc`, `xOf`, `zOf`.

## 3. Helpers added (all in `section S2Helpers`, names `s2_*`, no `F`-dependence except through `SmoothLoop`)

| helper | statement |
|---|---|
| `s2_strictMonoOn_Icc` / `s2_strictAntiOn_Icc` | `∀ t, HasDerivAt f (f' t) t`, `f' > 0` (resp. `< 0`) on `Ioo a b` ⇒ `StrictMonoOn f (Icc a b)` (resp. `StrictAntiOn`) — `strictMonoOn_of_deriv_pos`/`strictAntiOn_of_deriv_neg` with `convex_Icc`, `interior_Icc` |
| `s2_neg_pos_of_deriv_pos` | `f t₀ = 0`, `f' > 0` on `Ioo (t₀−δ) (t₀+δ)` ⇒ `f < 0` before `t₀`, `f > 0` after |
| `s2_pos_of_deriv_neg_pos` | `f t₀ = 0`, `f' < 0` before / `> 0` after ⇒ `f > 0` on both sides |
| `s2_lt_of_deriv_pos_off` | `f' > 0` on the interval except possibly at `t₀` ⇒ `f t₁ < f t₂` for `t₁ < t₀ < t₂` in it |
| `s2_cubic_lt` | `φ' (t₀) = φ'' (t₀) = 0`, `φ''' (t₀) > 0`, `φ'''` continuous ⇒ `∃ δ > 0`, `φ t₁ < φ t₂` for `t₀−δ < t₁ < t₀ < t₂ < t₀+δ` |
| `s2_cubic_iff` | same with `φ''' (t₀) ≠ 0`: `φ t₁ < φ t₂ ↔ 0 < φ''' (t₀)` |
| `s2_hasDerivAt_fst` / `s2_hasDerivAt_snd` | components of a `Plane`-valued `HasDerivAt` (`h.fst`/`h.snd`, i.e. `HasFDerivAtFilter.fst/snd` by defeq — the same trick as `hasDerivAt_xvel`) |
| `s2_hasDerivAt_deriv` / `s2_hasDerivAt_iteratedDeriv_two` | `γ'` has derivative `γ''`; `γ''` has derivative `γ'''` (for a `SmoothLoop`) |
| `s2_hasDerivAt_comb` | `z − k·x` has derivative `z' − k·x'` |
| `s2_loop_cusp_sign` | the cusp sign law for one `SmoothLoop` (§2) |
| `s2_dist_lt_of_mem_Ioo` | `t ∈ Ioo (t₀−δ) (t₀+δ) → dist t t₀ < δ` |
| `s2_local_min_of_sign` / `s2_local_max_of_sign` | from the `dist`-form sign statement of `exists_xvel_sign_of_is{Left,Right}Cusp` to `StrictAntiOn f (Ioc (t₀−δ) t₀) ∧ StrictMonoOn f (Ico t₀ (t₀+δ))` (resp. the mirror) |
| `s2_arms_of_local_min` / `s2_arms_of_local_max` | continuous `f`, the two monotonicities, `δ' > 0` ⇒ `∃ η > 0`, every `x ∈ Ioo (f t₀) (f t₀ + η)` (resp. `Ioo (f t₀ − η) (f t₀)`) is `f t₁ = f t₂ = x` with `t₁ ∈ Ioo (t₀−δ') t₀`, `t₂ ∈ Ioo t₀ (t₀+δ')` — `intermediate_value_Ioo`/`intermediate_value_Ioo'` at `ε = min δ δ'/2`, `η = min (f(t₀−ε) − f t₀) (f(t₀+ε) − f t₀)`; the max version is the min version for `−f` |

The generic helpers (`s2_strictMonoOn_Icc`, `s2_local_min_of_sign`, `s2_arms_of_local_min`, …) may be useful to
S1 (`regular_local_graph`: "x injective near a regular parameter" is `s2_strictMonoOn_Icc` with the constant sign
of `xvel`) and S3 (`cross_height_order`).

## 4. Pitfalls recorded

1. **`strictMonoOn_of_deriv_pos` IS in the import closure of the skeleton** (`Mathlib.Analysis.Calculus.Deriv.MeanValue`,
   import line 10) — W2_U8R_REPORT §5.4 said it was not, which was true of `W2_U8R.lean`'s imports, not of the
   skeleton's.  So the arc machinery (`nextCusp`, `arcEnd`, `strictMonoOn_x_of_isLeftCusp`) was not needed for
   `leftCusp_x_local`: `exists_xvel_sign_of_isLeftCusp` + `hasDerivAt_x` + `strictMonoOn_of_deriv_pos` suffice.
   `Mathlib.Analysis.Calculus.Taylor` is indeed not imported (`taylor_mean_remainder_lagrange` unknown) and was not
   needed.
2. **`(F.acc p).1 ≠ 0` against `(iteratedDeriv 2 (F.comp i).γ t₀).1 ≠ 0` by `exact` TIMES OUT** (`whnf`, > 200k
   heartbeats: the projection makes the unifier whnf `iteratedDeriv` through `iteratedFDeriv`).  `rfl` for the
   underlying equality is instant, and so is `rw [SmoothFront.acc_def, SmoothFront.jerk_def] at h; exact h`.  The
   leaf body therefore rewrites `acc_def`/`jerk_def` in the hypotheses and (after `unfold SmoothFront.cuspDisc`) in
   the goal before `exact`; the whole leaf then elaborates in < 20k heartbeats.  Passing `h : F.IsCusp (i, t₀)`
   where `deriv (F.comp i).γ t₀ = 0` is expected is fine (`have h' : deriv (F.comp i).γ t₀ = 0 := h`).
3. `HasDerivAt.fst`/`.snd` do not exist as constants; `h.fst` resolves to `HasFDerivAtFilter.fst` and is accepted
   only when the expected `HasDerivAt` type is given (`have hx : HasDerivAt (fun s => (f s).1) f'.1 t := h.fst`);
   chaining `.fst.const_mul` directly fails.  Hence `s2_hasDerivAt_fst/snd`.
4. `field_simp` closes the small algebraic goals of `s2_loop_cusp_sign` completely, so a following `ring` errors
   with "no goals"; the final version uses explicit `rw` chains (`div_mul_cancel₀`, `mul_div_cancel_left₀`,
   `sub_div`, `div_mul_eq_mul_div`, `div_self`) instead.
5. `Continuous.neg` gives `Continuous (-f)` (Pi negation), not `Continuous fun t => -f t`; when feeding it to a lemma
   whose `f` is implicit, pass `(f := fun t => -f t)` explicitly or `linarith` will not see through `(-f) t₀`.
6. `rw [iteratedDeriv_succ]` on the goal `deriv (iteratedDeriv 2 γ) t = iteratedDeriv 3 γ t` rewrites the wrong
   occurrence (`iteratedDeriv 2` → `deriv (iteratedDeriv 1 …)`); use
   `(congrFun (iteratedDeriv_succ (n := 2) (f := γ)) t).symm`.
7. Scratch loop: a copy truncated right after `rightCusp_arms` with the closing `end SweepLeaves / end / end U8R /
   end Leaves / end FrontRows / end SM` compiles in ~50 s; the generic helpers were developed in a 7-s probe file
   with the skeleton's 13 imports inside `namespace SM` (they mention only `SmoothLoop`, `Plane`, `det`).

## 5. For the merger

* Merge = the single insertion hunk `14953a14954,15204` + the five leaf-body hunks.  The block uses only Mathlib
  (`strictMonoOn_of_deriv_pos`, `strictAntiOn_of_deriv_neg`, `intermediate_value_Ioo(')`, `Metric.eventually_nhds_iff`,
  `lt_mem_nhds`, `interior_Icc`, `convex_Icc`) and `SmoothLoop.{hasDerivAt, contDiff_iteratedDeriv,
  continuous_iteratedDeriv}`, `SM.det`, `SM.Plane`; the leaf bodies use U8R §F (`exists_xvel_sign_of_isLeftCusp/
  _isRightCusp`, `isCusp_iff_xvel_eq_zero`, `hasDerivAt_x`) and `SmoothFront.{acc_def, jerk_def,
  acc_fst_ne_zero_of_isCusp, det_acc_jerk_ne_zero_of_isCusp}`.  Nothing from §G/§H, nothing from other units.
* `open Filter Topology` is scoped to `section S2Helpers` (for `𝓝` in `s2_cubic_lt`).
* If another unit's helper block also lands in `section SweepLeaves`, there is no name clash: all names here start
  with `s2_`.
