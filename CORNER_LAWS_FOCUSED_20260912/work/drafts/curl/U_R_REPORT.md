# U_R_REPORT — Unit R (the replacement), cf:lem-curl

Prover: Claude (subagent), 2026-09-14. File: `work/drafts/curl/U_R.lean` (copy of `Skeleton_FINAL.lean`, 2801 lines).
Check: `cd work/lean && lake env lean ../drafts/curl/U_R.lean` → exit 0, **0 errors**, 50 `declaration uses sorry`
warnings (the 54 skeleton leaves minus the 4 of this unit). `grep -c sorry`: 56 (skeleton) → 52 (the remaining 50 leaves
of other units + 2 mentions in the header/docstrings). `diff Skeleton_FINAL.lean U_R.lean | grep '^<'` shows exactly the
four removed `  sorry` lines: no definition, structure, statement, name or docstring was changed; everything else is
insertion (helpers) inside the Unit R section (§7, between `exists_cutFit` and `exists_glued_arc`, plus a small block
before `inserted_arc_props`).

## Leaves proved (4/4)

| leaf | lines | notes |
|---|---|---|
| `inserted_arc_props` | ≈110 + helpers | all nine clauses; the diameter bound in the repaired form `ℓ (x + 2)` |
| `exists_glued_arc` | ≈270 main body + ≈900 helpers | see "design" below |
| `exists_loop_of_arc` | ≈120 | periodic extension via a seam in the dead zone |
| `exists_smoothCurl` | ≈60 | assembly of `SmoothCurl` from the Unit G/R leaves |

Axioms (checked on a temp copy with `#print axioms`): `exists_loop_of_arc`, `r_glue`, `r_exists_reparam`,
`r_flat_bound`, `r_strictMonoOn_of_deriv_pos`, `r_glued_lift`, `r_glued_double` are `[propext, Classical.choice,
Quot.sound]`. `inserted_arc_props`, `exists_glued_arc`, `exists_smoothCurl` show `sorryAx` only through the Unit
1/2 black boxes they are meant to use: `hasDerivAt_cModel`, `cModel_double`, `fitA_smul`, `fitA_ray_minus/plus`,
`yFit_bound`, `xFit_pos` (U1); `det_vDir_u`, `planeDot_vDir_u`, `cut_displacement`, `ξ_strictMonoOn`,
`ξ_strictAntiOn`, `exists_chart`, `exists_disc_in_chart`, `exists_cutFit`, `disc_isDisc`, `p_mem_interior_disc`,
`tail_tangent_ne` (U2). No Unit 3 (H/T) leaf is used: the collar is not built as a graph (see design).

## Leaves left

None of Unit R.

## Design of `exists_glued_arc` (deviation in proof technique, not in statement — for AUTHOR_NOTES)

The printed proof (sm-3:4080-4212) builds the two collars as graphs `ξ = h(η)` over the longitudinal coordinate,
blending the graph functions `f` (old arc) and `g` (inserted arc) with the transition profile; this needs the inverse
functions of `η ∘ F` and `η ∘ (Φ ∘ c)` and the slope comparison `g' > f'`. The Lean proof instead blends *in the
parameter*: `N = F + Ψ · (G − F)` with `G = Φ ∘ c ∘ σ̃`, where `σ̃` is a smooth increasing change of variable
`[s₁, s₂] → [−2, 2]` whose end speeds are chosen so that `G` has exactly `F`'s **velocity** at both cuts
(`r_exists_reparam`, an FTC construction with a three-piece speed profile), and `Ψ = φ((t − s₁)/lam) φ((s₂ − t)/lam)`.
Then `G − F` vanishes to second order at each cut (`r_flat_bound`, two mean-value inequalities), so
`N' − F' = Ψ'(G − F) + Ψ(G' − F')` is `O(lam)` on a collar of width `lam` (`r_glue`) and a small `lam` puts `N'` in
the open quadrants of `F'(s₁)`, `F'(s₂)`. The geometric clauses then follow with no graph structure:
- in the disc: `N t` is a convex combination of `F t` (`CutFit.old_in_disc`) and `G t` (`CutFit.ins_in_disc`),
  the disc is convex (`r_disc_convex`);
- only double point: both parameters in an end zone (`⟨N', u⟩ > 0` there, so `N` is injective, `r_inj_of_dot_pos`),
  both in the model part (`cModel_double` through `inserted_arc_props`), or one on a collar (the collar lies within
  `2ε` of the cut point while the model part at distance `≥ lam₀` from the cut and the other collar are at positive
  distance from it — a compactness minimum `dm`, `dp`, and `ℓ' = |p₊ − p₋|`; `r_glued_double`);
- off the rest of the curve: `ξ(N s) > ξ(s₁)` as a convex combination of `ξ(F s) > ξ(s₁)` (`ξ_strictMonoOn/AntiOn`)
  and the model excess (`inserted_arc_props`), while a tail point in the disc has `ξ ≤ ξ(s₁)` (`r_glued_off`);
- (ii): the sign of `⟨N', v⟩` (positive before `q₀`, negative after, `0` at `q₀` with `⟨N', u⟩ < 0`) gives "never
  `u`, `−u` exactly at `q₀`" (`r_glued_tangent`);
- (iv): the lift is read off the same sign data: the angle relative to `u` starts in `(−π/2, 0)`, stays in `(−π, 0)`
  before `q₀` (IVT), equals `−π` at `q₀`, stays in `(−2π, −π)` after, and ends congruent to `θrel(s₂) ∈ (0, π/2)`
  mod `2π`, forcing the increment `θ(s₂) − θ(s₁) − 2π` (`r_glued_lift`). `glplus_increment_sub_invariant` is not
  needed.
The statement of `exists_glued_arc` is unchanged; every printed conclusion is established. This is a change of proof,
not of content (FR-C3 remains: a `C^∞` regular parametrisation on `[s₁, s₂]` with `F`'s jets at both ends is produced).

## Helpers added (all in namespace `SM.Curl`, names prefixed `r_`; 57 declarations)

r_fitA_zero r_det_fitA r_planeDot_fitA r_planeDot_add_left r_planeDot_smul_left r_planeDot_comm 
r_fitA_injective r_hasDerivAt_inserted r_euclideanLength_add_le r_euclideanLength_vDir r_planeDot_vDir_vDir 
r_planeDot_u_u r_cubic_bounds r_smoothTransition_deriv_bound r_deriv_smoothTransition_zero 
r_deriv_smoothTransition_one r_flat_bound r_strictMonoOn_of_deriv_pos r_prof r_profNeg r_prof_smooth 
r_profNeg_smooth r_prof_hasDerivAt r_profNeg_hasDerivAt r_prof_zero r_prof_one r_profNeg_zero r_profNeg_one 
r_prof_mem r_profNeg_mem r_prof_deriv_bound r_profNeg_deriv_bound r_prof_deriv_end r_profNeg_deriv_end r_glue 
r_exists_reparam r_exists_model r_planeDot_neg_left r_planeDot_sub_left r_abs_planeDot_le 
r_continuous_planeDot r_hasDerivAt_planeDot r_zone_of_eventually r_planeDot_normalize' r_euclideanLength_neg 
r_normalize_neg_u r_expand r_disc_convex r_cut_velocity r_collar_sign r_collar_sign_neg r_convex_gt 
r_inj_of_dot_pos r_glued_tangent r_glued_lift r_glued_double r_glued_off 

Two definitions are `noncomputable def`: `r_prof`, `r_profNeg` (the rising/falling profiles `φ((t−c)/lam)`,
`φ((c−t)/lam)`). The rest are theorems. Statements of the helpers are mine and may be reshaped by the assembler; the
leaf statements were not touched.

## Mathlib / toolchain pitfalls met (v4.34.0-rc2, Mathlib pin)

- `λ₀`, `t₋`, `d₊` are not identifiers (`λ` is a keyword; `₋`/`₊` are not identifier characters). Use `lam₀`, `tm`, `dp`.
- `Mathlib.Analysis.Calculus.Deriv.MeanValue` is **not** in the transitive imports of `SM.Rounding`/`SM.LinkMoves`/
  `SM.PolynomialBlock`: `strictMonoOn_of_deriv_pos`, `exists_deriv_eq_slope` are unavailable. Rolle
  (`exists_deriv_eq_zero`) and the norm mean-value inequality `Convex.norm_image_sub_le_of_norm_deriv_le` are available;
  `r_strictMonoOn_of_deriv_pos` is derived from Rolle. (No import was added to the file.)
- `isCompact_Icc.exists_bound_of_continuousOn`: the interval endpoints must be given on `isCompact_Icc (a := ..) (b := ..)`.
- `ContDiff.differentiable` wants `n ≠ 0` here: `(by decide)` for `∞`, `(by simp)` for `1`; `continuous_deriv` wants
  `1 ≤ n`: `(by exact_mod_cast le_top)`.
- `Int.fract_eq_iff.mpr ⟨by linarith, ..⟩` leaves the target `b` as a metavariable that `linarith` may instantiate
  arbitrarily: pass `(b := ...)` (likewise `(Int.floor_eq_iff (z := ..)).mpr`).
- `HasDerivAt` of a coordinate: no `HasDerivAt.fst`; use `(ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h`.
- `simpa` across `HasDerivAt.add/smul` fails on syntactically different (defeq) instance paths for `Plane`; `exact` works.
- The Unit P lemmas `iteratedDeriv_eq_zero_of_const_left/right`, `X_smul_normalize`, `X_det_smul_smul`,
  `E_planeComplex_add` live in `SM.CornerRounding`.
- `Real.smoothTransition.monotone` exists (used for `φ₂ ≤ φ₁`); `Real.sin_nonpos_of_nonnpos_of_neg_pi_le` does not —
  use `sin_nonneg_of_nonneg_of_le_pi` on `−x`.
- A monolithic 450-line proof of `exists_glued_arc` hit the 200000-heartbeat limit (an `nlinarith` over ~100
  hypotheses); split into the `r_glued_*` lemmas with small contexts. Avoid `nlinarith` in large contexts.
- Structure-instance literal `{ a := x, b := y,\n c := z }` (comma then newline) failed to parse; one field per line
  without commas works.
- `set` interacts badly with later `obtain`s (the abbreviation is not applied to new hypotheses); `obtain ⟨x, hx⟩ : ∃ x, x = e := ⟨_, rfl⟩`
  gives an opaque name with an equation, which is what the long proofs use.

## For the assembler / executor

- `exists_smoothCurl` consumes `exists_chart`, `exists_disc_in_chart`, `exists_cutFit`, `disc_isDisc`,
  `p_mem_interior_disc`, `tail_tangent_ne` (U2) exactly as the skeleton docstring says; `s₂ − s₁ < 1` comes from `S.short`.
- The unused-variable warnings on `hα'`, `hβ'`, `hr` in `exists_glued_arc` come from the frozen statement (the proof
  uses `hα`, `hβ`, `hθ`, `hmeets`, `cf`); harmless.
- Compile time of the whole file ≈ 60 s.
- Everything from `/-! #### Unit R helpers: `fitA` as a linear map ... -/` to `exists_smoothCurl` can be moved as one
  block when porting to `SM/Curl.lean`; nothing was written under `work/lean`.
