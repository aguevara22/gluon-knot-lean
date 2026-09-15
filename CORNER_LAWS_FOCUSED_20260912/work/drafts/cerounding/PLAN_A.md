# PLAN A — ce:rounding (row 89): fixed statement, construction, chain, units, risks

Row: ce:rounding, reference/SM/sm-3-statesum.tex:3029-3058 (statement; `\end{lemma}` at 3058), proof 3059-3170.
Architect A (emphasis: maximal REUSE of the accepted corner-rounding tools and the front-block GeomRounding), 2026-09-14.
Inputs: work/drafts/gap2/GAP2_STATEMENTS_MEMO.md §2, §3(d), §4 "89", §5; Gap2Statements.lean §3-§4 (compiles, 8 s);
SM/Rounding.lean (Unit P + construction), SM/FrontSmooth.lean (GeomRounding + consequences), SM/FrontRecordBridge.lean §2-3,
SM/FrontGeomModel.lean, SM/TransverseFront.lean (Space, xOf/yOf/zOf/xzOf, SameT, deriv_T pattern); AUTHOR_NOTES FR-1..FR-7, FR-R1..FR-R7.

Deliverables (this directory; nothing written under work/lean):
- `Statements_A.lean` (334 lines): the fixed statement. `cd work/lean && lake env lean ../drafts/cerounding/Statements_A.lean`:
  0 errors, 1 sorry (= `SM.ce_rounding : CeRoundingData`). `#print axioms` of `CeRoundingData`, `CuspRoundingFamily`,
  `CuspedProjection.not_isCusp_of_isDouble` = [propext, Classical.choice, Quot.sound].
- `Skeleton_A.lean` (1168 lines): §1-3 statement text verbatim; §4 construction; §4.5-4.8 chain; §5 assembly (PROVED);
  §6 row (PROVED from the chain). 0 errors, **36 sorry** (all leaf lemmas, listed in §4 below).
  `#print axioms SM.ce_rounding` = [propext, sorryAx, Classical.choice, Quot.sound].

## 1. Clause map (printed → tex line → Lean)

| # | printed clause | tex | Lean (Statements_A.lean) |
|---|---|---|---|
| H1 | "smooth oriented spatial embedding of a finite nonempty union of parameter circles in ℝ³ … its projection p=(x,z)" | 3031-3033 | `L : SpatialLink c` (`T : Fin c → ℝ → Space`, `C^∞`, 1-periodic, `embedded`, `regular`), `0 < c`; `L.projLoop i` |
| H2 | "Its only failures of regularity are finitely many isolated cusps" | 3033-3034 | `IsCusp i t := deriv (xzOf (L.T i)) t = 0`; `CuspedProjection.cusps_finite` |
| H3 | "all other projected coincidences are finitely many transverse double points" | 3034-3035 | `doubles_finite : (occSetOf L.projLoop).Finite`, `transverse` (det of projected velocities ≠ 0) |
| H4 | "no triple points or cusps on another branch" | 3035-3036 | `no_triple`; "cusp on another branch" excluded by `transverse` — PROVED `CuspedProjection.not_isCusp_of_isDouble` (`det 0 v = 0`) |
| H5 | "the two y heights at every double point are distinct" | 3036-3037 | `heights_distinct` (`L.height p ≠ L.height q`) |
| H6 | "At every cusp assume the exact germ, on a parameter interval with smooth coordinate u=y−y₀, [ce:exact-germ]" | 3037-3043 | `exact_germ : ∀ p ∈ cuspSet, ExactCuspGerm p.1 p.2` = `∃ A ≠ 0, δ > 0`, `y' ≠ 0` on `(t₀−δ,t₀+δ)`, the three formulas with `u = y t − y t₀` |
| H7 | "u may increase or decrease along the prescribed component orientation, which is not changed" | 3044-3045 | no sign condition on `y'`; orientation = parameter direction (T-1); the family keeps the parameter |
| H8 | "The formula is a hypothesis, not an appeal to a classification" | 3046-3047 | commentary (the hypothesis is `exact_germ`) |
| C1 | "a jointly smooth family L_λ, 0≤λ≤1, of oriented spatial embeddings with L_0=L" | 3049-3050 | `CuspRoundingFamily.fam : SpatialFamily c` (`G : ℝ → SpatialLink c`, `joint_smooth` on `ℝ × ℝ`), `start : fam.G 0 = L`; bundle field `smooth_embeddings_start` |
| C2 | "fixed outside disjoint cusp parameter intervals" | 3050-3051 | `a b : cuspSet → ℝ`, `a_lt`, `lt_b`, `len`, `intervals_disjoint` (on the circle, `∀ n : ℤ`), `fixed_outside`; bundle `fixed_outside_disjoint` |
| C3 | "for every λ>0 its xz projection is an ordinary finite regular generic diagram" | 3051-3052 | `generic : 0 < λ → λ ≤ 1 → (fam.G λ).RegularGenericProjection`; bundle `generic_slices` |
| C4 | "It cleanly smooths the cusps" | 3052-3053 | `clean : Nonempty (L.CleanCuspSmoothing (fam.G λ).projLoop)` (the definition sentence of ce:smoothing-record, = accepted `GeomRounding` field for field) |
| C5 | "creates no crossing, and retains every original crossing with its oriented decorated data" | 3053-3054 | `same_doubles`, `same_velocity` (NEW), `same_data` (sign, height order); bundle `clean_no_new_retains` |
| C6 | "All original parameter circles, component labels and traversal orientations are retained" | 3054-3055 | structural (same `Fin c`, same parameter; the family changes only `T`) + `fixed_outside`; bundle `circles_retained` (1-periodic in the same parameter, `= L` off the intervals) |
| C7 | "With no cusps take the constant family" | 3055 | bundle `no_cusps_constant : cuspSet = ∅ → ∀ λ, W.fam.G λ = L` (PROVED from `fixed_outside`, `CuspRoundingFamily.eq_of_no_cusps`) |
| C8 | "ordinary spatial deformation, not asserted Legendrian or positive transverse, no self-linking transport" | 3056-3058 | commentary; no field, nothing asserted |

Readings recorded (cite in the review): CE-1 orientation = parameter direction, smooth = `C^∞`, circle = 1-periodic map
(T-1, FR-3). CE-2 "embedding" = injective on the union of circles + nonvanishing derivative. CE-3 "cusp" = zero of the
projected velocity (the accepted `IsCusp ↔ vel = 0`). CE-4 "smooth coordinate u = y − y₀ on a parameter interval" =
`y' ≠ 0` on the open interval (strictly monotone `u`, either direction). CE-5 "jointly smooth" = `ContDiff ℝ ∞` of the
uncurried map on `ℝ × ℝ`; the family is indexed by `ℝ` (the memo's `SpatialFamily`) and the printed clauses concern
`[0,1]`. CE-6 "ordinary finite regular generic diagram" = `RegularGenericProjection` (regular, finitely many transverse
double points, no triple point, distinct heights — the over rule "smaller y" is then determined), as def:transverse-front
treats a smooth regular generic projection as "the diagram"; the polygonal record-carrying `Diagram` is the consumer's
FR-1 reading (`HeightMarking`) and is NOT produced by the row. CE-7 "cleanly smooths" = `CleanCuspSmoothing`, the
row-90 definition. CE-8 "oriented decorated data" = the unchanged branches (velocities), signs and height order at the
old double points. CE-9 "disjoint cusp parameter intervals" = disjoint on the circle (modulo `ℤ`).

## 2. Model decisions

- **MD-1 vocabulary.** Memo §3 reproduced byte-for-byte (`SpatialLink`, `projLoop`, `height`, `IsCusp`, `cuspSet`,
  `ExactCuspGerm`, `CuspedProjection`, `RegularGenericProjection`, `HeightMarking`, `CleanCuspSmoothing`,
  `SpatialFamily`), so one shared module can be ported for rows 89/90/91. `HeightMarking` is unused by 89 and kept.
- **MD-2 changes to the row-private `CuspRoundingFamily`** (only 89 uses it; 90/91 use `SpatialFamily`,
  `CleanCuspSmoothing`, `HeightMarking`): (a) `intervals_disjoint` quantified over integer translates (CE-9; the memo's
  real-interval version lets two arcs of one circle overlap across the period); (b) new field `same_velocity`
  (projected velocities at the old double points unchanged), which implies the sign half of `same_data` (kept verbatim).
- **MD-3 bundle shape.** `CeRoundingData` = existence field (the theorem) + one field per printed sentence of the
  conclusion read on a witness + `no_cusps_constant` (the accepted `RoundingData` pattern, SM/Rounding.lean:368-437).
  The memo's single-field bundle is the field `exists_family`, unchanged in type.
- **MD-4 time clamp.** `SpatialFamily.G : ℝ → SpatialLink c` demands embedded slices at EVERY real λ; the printed
  formula is embedded only on `[0,1]` ("embeddedness outside [0,1] is not claimed", 3111). The family is
  `G λ = slice (φ λ)`, `φ = Real.smoothTransition` (Unit P's profile): `φ 0 = 0`, `φ λ ∈ (0,1]` for `λ > 0`, so on
  `[0,1]` it is the printed family in the reparametrized time `μ = φ(λ)`, and every printed clause holds for `λ > 0`.
- **MD-5 cutoff in the parameter.** The printed `ρ(u)` is realised as the 1-periodic
  `periodicBump r (t − t₀) = φ((cos 2π(t−t₀) − cos 2πr)/(cos πr − cos 2πr))`: smooth/periodic by composition; `= 1` on
  `dist(t−t₀,ℤ) ≤ r/2`, `= 0` on `dist ≥ r`. Composed with `u⁻¹` it is a printed `ρ` (support strictly inside).
- **MD-6 chart and rectangle.** `GermData.chart` = ce:positive-chart (3062-3066), `unchart` its affine inverse; the
  projection is `(u², u³)` on the chart interval `J` (`chart_proj`), `δ ≤ 1/3` so `J` embeds in the circle. The clean
  neighbourhood is the pullback `U = unchart '' rect` of the rectangle `[−M², 2M²] × [u₋³, u₊³]` (`u₋ < 0 < u₊` the end
  values of `u` on `[t₀−η, t₀+η]`, `M = max(|u₋|, u₊)`): convex compact with interior (`IsDisc`), and `U ∩ p(L)` is exactly
  the arc because `Z = u³` is strictly monotone (ce:cubic-difference, 3121-3128) — no inverse of `u` is needed. The
  printed open `V` and `d` (3078-3096) become the `remote` field of `CuspChoice` (normalized sup-distance), chosen in
  `exists_remote_clearance`/`exists_eta`.
- **MD-7 displacement.** `disp μ t = (μ·ε·A·u(t)·χ(t)) • (1, 0, y₀)` = ce:physical-displacement (3105-3108), `Δy = 0`
  (`yOf_core`, PROVED: heights untouched everywhere); `core μ i t = L.T i t + Σ_{cusps k of i} disp_k μ t`; in the chart
  `(u² + μεuχ, u³)` = ce:rounding-formula (`chart_core`). Amplitude `ε ≤ M` keeps `X ∈ [−M², 2M²]` (no `√(1+y₀²)`
  estimate needed: the bound is taken in normalized coordinates).
- **MD-8 slices as `SpatialLink`.** Embeddedness and spatial regularity of a slice are DERIVED (PROVED in the skeleton)
  from the clean-smoothing witness on the raw loops `coreLoop μ` (no circularity): a spatial coincidence projects to a
  double point of the smoothing = a double point of `L` (`isDoubleOf_iff`) with distinct unchanged heights; a zero of
  `deriv core` would be a zero of the projected velocity (`regular_everywhere`).

## 3. Accepted declarations used (file:line)

`Space`, `xOf/yOf/zOf/xzOf` SM/TransverseFront.lean:100-109; `SameT` :125; `deriv_T`/`deriv_xz` pattern :621-644 (transcribed as
`deriv_space`, `deriv_xzOf`, PROVED); `det` SM/Polygon.lean:16; `Plane` :13; `IsDisc` SM/LinkMoves.lean:100; `SmoothLoop`
SM/FrontSmooth.lean:166 (+ `eq_add_int`, `deriv_eq_add_int` :196-216); `Param`, `SameParam` :242-297; `int_eq_of_add_mem_Icc` :1050,
`eventually_add_int_notMem_Icc` :1060; `GeomRounding` :1129 and its consequences :1170-1456 (`isDouble_iff` :1425, `deriv_eq_of_isDouble`
:1409, `regular_everywhere` :1373, `deriv_eq_of_notMem` :1339, `isOpen_closedArcFree` :1234) — TRANSCRIBED to `CleanCuspSmoothing` (leaves
U-R); `IsDoubleOf`, `occSetOf`, `crossSignOf` SM/FrontRecordBridge.lean:97-120, `GeomRounding.occSetOf_eq` :162, `crossSignOf_eq` :179;
`OccOf`, `GeomMarking` SM/FrontGeomModel.lean:76,120 (for `HeightMarking` only); Unit P: `Real.smoothTransition` (Mathlib
SmoothTransition.lean: `contDiff`, `nonneg`, `le_one`, `zero`, `pos_of_pos`, `zero_of_nonpos`, `one_of_one_le`), SM/Rounding.lean:595-693
(`smoothTransition_symm`, `smoothTransition_strictMonoOn`, `deriv_smoothTransition_pos`, `iteratedDeriv_eq_zero_of_const_left/right`
— the last two are the pattern for flatness if a unit wants derivative equality via local constancy); `RoundingData` :368 (bundle
pattern); `germFront` and its derivative lemmas SM/FrontSmooth.lean:845-900 (reusable for `chart_proj`/`arc_regular`: the projected
germ IS `germFront A y₀ x₀ z₀ ∘ u`).

## 4. The chain (36 leaves, Skeleton_A.lean line: exact statement), by unit

**U-P′ cutoff (3 leaves, ~150 lines, low risk).** `periodicBump_zero` (391): `0<r → r<1/2 → periodicBump r 0 = 1`;
`periodicBump_eq_one` (395): `|s − n| ≤ r/2 → periodicBump r s = 1`; `periodicBump_eq_zero` (400): `(∀ n:ℤ, r ≤ |s−n|) →
periodicBump r s = 0`. Tools: `Real.cos_lt_cos_of_nonneg_of_le_pi`, `Real.cos_int_mul_two_pi_add`/periodicity, `round`.
(PROVED already: `periodicBump_contDiff`, `_periodic`, `_nonneg`, `_le_one`, `exists_int_abs_lt_of_periodicBump_ne_zero`.)

**U-G germ/chart (8 leaves, ~600 lines, medium).** `exists_germData` (430): `ExactCuspGerm i t₀ → Nonempty (GermData i t₀)`
(shrink δ to `min δ (1/3)`); `chart_proj` (483): `t ∈ g.J → g.chart (xzOf (L.T i) t) = (g.u t^2, g.u t^3)` (from `formula`,
`field_simp; ring`); `u_strictMonoOn_or_strictAntiOn` (496): `StrictMonoOn g.u g.J ∨ StrictAntiOn g.u g.J` (`y'` continuous
nonzero on the interval has one sign: IVT on `deriv`, then `strictMonoOn_of_deriv_pos` Mathlib Deriv/MeanValue.lean:375 and its
`neg`); `rect_subset_closedBall` (535): `g.rect η ⊆ closedBall 0 (g.radius η)` (sup norm, `Prod.norm_def`); `uMin_neg` (539) /
`uMax_pos` (542): `0<η → η<g.δ → g.uMin η < 0`, `0 < g.uMax η` (`u t₀ = 0`, strict monotonicity, `a < t₀ < b`);
`u_mem_Icc_of_mem` (549): `t ∈ Icc (t₀−η) (t₀+η) → g.u t ∈ Icc (uMin) (uMax)`; `mem_Icc_of_u_mem` (554): `t ∈ g.J → g.u t ∈
Icc uMin uMax → t ∈ Icc (t₀−η) (t₀+η)`; `u_mem_Ioo_of_mem` (559): open version; `abs_u_le_M` (563): `t ∈ Icc … → |g.u t| ≤ g.M η`.
(PROVED: `chart_unchart`, `unchart_chart`, `chart_injective`, `chart_add_disp`, `u_injOn`, `cube_injective`, `proj_injOn_J`,
`rect_convex`, `rect_isCompact`, `M_pos`.)

**U-C one cusp (6 leaves, ~700 lines, medium-high; printed 3073-3096 + 3121-3131).** `chi_eq_zero_of_notMem` (632):
`(∀ n, t + n ∉ Ioo ch.a ch.b) → ch.chi t = 0` (`r < η`, U-P′); `isDisc_U` (664): `IsDisc ch.U` (affine image of the convex
compact rectangle; interior via `chart ⁻¹' interior rect`); `center_mem_interior_U` (667): `xzOf (L.T k.1.1) k.1.2 ∈ interior ch.U`
(`chart c = 0 ∈ (−M², 2M²) × (u₋³, u₊³)`); `arc_in` (684): `t ∈ Icc ch.a ch.b → xzOf (L.T k.1.1) t ∈ ch.U`; `clean` (689):
`xzOf (L.T q.1) q.2 ∈ ch.U → q.1 = k.1.1 ∧ ∃ n, q.2 + n ∈ Icc ch.a ch.b` (`remote` + `norm_chart_le_of_mem_U` exclude remote
parameters; chart parameters via `Z = u³` monotone and `mem_Icc_of_u_mem`); `arc_simple` (694): `t ∈ Icc a b → ¬SameParam (k.1.1,t)
q → xzOf (L.T q.1) q.2 ≠ xzOf (L.T k.1.1) t` (`clean` + `proj_injOn_J`). (PROVED: `a_lt`, `lt_b`, `len`, `r_lt_half`, `Icc_subset_J`,
`chi_contDiff`, `chi_periodic`, `chi_cusp`, `disp_*`, `xz_disp`, `norm_chart_le_of_mem_U`, `mem_U_iff`.)

**U-L local analysis at time μ (8 leaves, ~900 lines, HIGH; printed 3097-3131, 3132-3144).** `core_joint_contDiff` (745):
`ContDiff ℝ ∞ (fun p : ℝ×ℝ => C.core (φ p.1) i p.2)` (`ContDiff.sum`, `split_ifs`, `fun_prop`); `chi_eq_zero_of_ne` (790):
`k ≠ k' → k.1.1 = k'.1.1 → t ∈ Ioo (a k) (b k) → (C.ch k').chi t = 0` (interval disjointness on the circle from disc
disjointness + `arc_in`); `core_on_arc` (795): `t ∈ Ioo (a k) (b k) → C.core μ k.1.1 t = L.T k.1.1 t + (C.ch k).disp μ t`;
`chart_core` (800): `… → chart (xzOf (C.core μ k.1.1) t) = (u² + μ ε u χ, u³)` (`chart_proj` + `chart_add_disp` + `xz_disp`);
`inside` (806): `μ ∈ Icc 0 1 → t ∈ Ioo a b → xzOf (C.core μ k.1.1) t ∈ U` (`|μεuχ| ≤ M²`, `mem_U_iff`); `arc_regular` (813):
`0 < μ → t ∈ Ioo a b → deriv (xzOf (C.core μ k.1.1)) t ≠ 0` (derivative of `(x₀ + Au², z₀ + y₀Au² + ⅔Au³) + (μεAuχ)(1, y₀)` on the
open arc: `z' − y₀x' = 2Au²u' ≠ 0` off `t₀`; `x'(t₀) = μεA u'(t₀) ≠ 0` since `χ(t₀) = 1` — the printed 3113-3118 in physical
coordinates, no chart inverse); `arc_injOn` (819): `InjOn (xzOf (C.core μ k.1.1)) (Ioo a b)` (`Z = u³` via `chart_core`,
`chart_injective`); `arc_no_crossing` (825): `μ ∈ Icc 0 1 → t ∈ Ioo a b → ¬SameParam (k.1.1,t) q → xzOf (C.core μ q.1) q.2 ≠
xzOf (C.core μ k.1.1) t` (three cases: `q` on the same arc mod 1 → `arc_injOn`; on another arc → `inside` + `disjoint`; on no open
arc → `core_eq_of_notMem`, `clean` puts `q` at an END of the arc, and `Z(t) = u(t)³` is strictly between the end values,
`u_mem_Ioo_of_mem`).

**U-R record consequences (5 leaves, ~500 lines, low-medium; TRANSCRIPTION of FrontSmooth.lean 1170-1456 + FrontRecordBridge §3
from `F.comp/F.Cusp` to `L.projLoop/L.cuspSet`; SHARED with the row-90 unit — same names).** On `ρ : L.CleanCuspSmoothing G`:
`isDoubleOf_iff` (865): `IsDoubleOf G p q ↔ IsDoubleOf L.projLoop p q`; `deriv_eq_of_isDouble` (870): `IsDoubleOf L.projLoop p q →
deriv (G p.1).γ p.2 = deriv (xzOf (L.T p.1)) p.2`; `regular_everywhere` (876): `L.cuspSet.Finite → ∀ i t, deriv (G i).γ t ≠ 0`
(needs `IsCusp i t → (i, Int.fract t) ∈ cuspSet`, the analogue of `rep_mem_cuspSet`, from `(L.projLoop i).deriv_periodic`);
`occSetOf_eq` (880): `occSetOf G = occSetOf L.projLoop`; `intervals_disjoint` (885): `k ≠ k' → k.1.1 = k'.1.1 → ∀ n:ℤ,
Disjoint (Ioo (ρ.a k) (ρ.b k)) (Ioo (ρ.a k' + n) (ρ.b k' + n))`. (PROVED: `crossSignOf_eq`.)

**U-E existence of the choices (4 leaves, ~600 lines, medium-high; printed 3073-3096).** `cusp_image_injective` (1044):
`CuspedProjection → xzOf … k = xzOf … k' → k = k'` (a common image is a double point at a cusp: `not_isCusp_of_isDouble`; `¬SameParam`
from both in `Ico 0 1`); `exists_gap` (1049): `∃ gap > 0, ∀ k ≠ k', 2·gap < dist (image k) (image k')` (finite set of distinct
points); `exists_remote_clearance` (1057): `∀ g : GermData, ∃ d > 0, ∀ q, (q.1 ≠ k.1.1 ∨ ∀ n, q.2 + n ∉ g.J) → d < ‖g.chart (xzOf
(L.T q.1) q.2)‖` (the remote set is the projection of the compact `[t₀+δ−1, t₀−δ] ∪ other circles × [0,1]`, does not contain the
cusp image by `transverse`/`not_isCusp_of_isDouble` and `proj_injOn_J`; `Metric.infDist_pos_iff_notMem_closure`
HausdorffDistance.lean:574; transport through the affine `chart`); `exists_eta` (1066): `0<d → 0<ρ₀ → ∃ η, 0<η ∧ η<g.δ ∧ g.radius η
< d ∧ g.unchart '' g.rect η ⊆ closedBall (cusp image) ρ₀` (continuity of `u` at `t₀`, `u t₀ = 0`; Lipschitz bound of `unchart`).
(PROVED: `exists_cuspChoice_within` with `r := η/2`, `ε := M`; `exists_choices` by `choose` + `closedBall_disjoint_closedBall`.)

**Assembly (PROVED, ~230 lines):** `Choices.smoothing` (the `CleanCuspSmoothing` witness at `0 < μ ≤ 1`), `core_embedded`,
`core_regular`, `slice`, `fam`, `fam_zero`, `slice_generic`, `Choices.witness : CuspRoundingFamily L`, `exists_cuspRoundingFamily`,
`CuspRoundingFamily.eq_of_no_cusps`, `ce_rounding`.

Total estimate ≈ 3.5k lines (memo: 3-5k). Parallelisable as U-P′ ∥ U-G ∥ U-R ∥ (U-C after U-G) ∥ (U-L after U-G, U-C) ∥ (U-E after
U-G); statements never change; U-R first (row 90 needs it).

## 5. Interface with the row-90 unit (ce:smoothing-record)

Reuse `Statements_A.lean` §1 verbatim (identical to the memo). Row 90 needs, on `ρ : L.CleanCuspSmoothing G`, exactly U-R's
`isDoubleOf_iff`, `deriv_eq_of_isDouble`, `occSetOf_eq`, `crossSignOf_eq` (the transcribed `GeomRounding.eventuallyEq_of_isDouble`
may be added) plus the height rule from `HeightMarking.over_iff` — propose that U-R be one shared unit whose names are fixed here.
`CuspRoundingFamily.clean` hands row 90 the `D_ε = p(L_1)` smoothing as a `CleanCuspSmoothing (fam.G 1).projLoop` witness.

## 6. Risks (to record before the row is stated)

- **CR-1 (statement).** `RegularGenericProjection` is "the diagram" (CE-6, as def:transverse-front); the row does not deliver a
  polygonal `Diagram` with a `HeightMarking` (FR-1 is the consumer's). Consumers 90/91 take the marking as a hypothesis (memo).
- **CR-2 (statement).** `CuspRoundingFamily` exports more than printed: `same_velocity` (unchanged branches), `fixed_outside` for
  all real λ, slices for all real λ (MD-4 clamp), `RegularGenericProjection` on every `λ ∈ (0,1]` of the reparametrized time. A
  reviewer must accept the clamp `μ = φ(λ)` as "the" family (the printed family is its restriction to `[0,1]` reparametrized).
- **CR-3 (statement).** `heights_distinct` and "no cusp on another branch" are printed hypotheses that are consequences of
  `embedded` resp. `transverse`; both are kept/derived, none added as a redundant field (`not_isCusp_of_isDouble` PROVED).
- **CR-4 (construction/fidelity).** The clean neighbourhood is a chart-rectangle, not the printed disc `V`; the cutoff is in the
  parameter, not in `u`; the clearance constant is a normalized sup-norm bound, not `|A|εM√(1+y₀²) < d/2`. All are choices inside
  the printed existential proof, invisible in the statement; the reviewer of the PROOF must accept them (record in the report).
- **CR-5 (technical, high).** U-L `arc_regular`/`arc_no_crossing` and U-E `exists_remote_clearance` are the analytic core (~1.5k
  lines): derivative bookkeeping on `Space`-valued maps (only `deriv_space`/`deriv_xzOf` exist), compactness of the remote image,
  the three-case crossing argument. A false-leaf audit (as FR-R6) should probe `arc_no_crossing` case 3 (ends of the arc) and
  `mem_Icc_of_u_mem` with `u` decreasing.
- **CR-6 (technical).** `exists_germData` shrinks `δ`; `ExactCuspGerm`'s `δ` is unconstrained — if a unit prefers, `GermData.δ_le`
  can be dropped by using `min δ (1/3)` in `J`; the statement is unaffected.
- **CR-7 (scope).** The two printed disclaimers and 3132-3170 (contact-form computation ce:ordinary-not-contact) are commentary;
  nothing Legendrian/transverse or about `sl` is stated. Consumer: row 91 only (GAP-2, memo §1); 89 itself is not GAP-2-blocked.
