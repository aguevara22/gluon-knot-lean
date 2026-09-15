# PLAN FINAL — ce:rounding (row 89): verdict, fixed statement, construction, chain, units, risks

Row: ce:rounding, reference/SM/sm-3-statesum.tex:3029-3062 (lemma environment; statement 3031-3058,
`\status` 3059-3061, `\end{lemma}` 3062), proof 3063-3169.  Judge (pod subagent), 2026-09-14.
Inputs: PLAN_A.md / Statements_A.lean / Skeleton_A.lean; PLAN_B.md / Statements_B.lean / Skeleton_B.lean;
the printed text and proof; GAP-2 memo §3(d), §4 "89", §5 and its sketch; the accepted modules cited by both;
AUTHOR_NOTES FR-1..FR-7, FR-R1..FR-R7 and the two entries of 2026-09-14 ~07:51Z / ~08:17Z (rows 89/90
reclassified; row 90 ported with decision D-1); the ported library module work/lean/SM/CeSmoothingRecord.lean.

Deliverables (this directory; nothing written under work/lean; checked with `cd work/lean && lake env lean <file>`):
- `Statements_FINAL.lean` (252 lines): exit 0, exactly ONE `sorry` = `SM.ce_rounding : CeRoundingData`.
- `Skeleton_FINAL.lean` (1103 lines): exit 0, **33 `sorry`** = the leaves of §4 below, nothing else; assembly and
  row PROVED; `#print axioms SM.ce_rounding` = [propext, sorryAx, Classical.choice, Quot.sound];
  `SM.CeRoundingData`, `SM.CuspRoundingWitness`, `SM.SpatialLink.constWitness` (the "with no cusps" clause) =
  [propext, Classical.choice, Quot.sound] (no sorryAx).  Remaining warnings: 2 unused simp arguments (A's
  `chart_add_disp`), 5 style `letI` hints — cosmetic.

## 0. A fact both architects missed, and what it changes

Between the panel's launch and its delivery the row-90 unit was PORTED (work/lean/SM/CeSmoothingRecord.lean,
built, mapped, under review; AUTHOR_NOTES 2026-09-14 ~08:17Z) with **decision D-1**: `CleanCuspSmoothing` gained the
field `collar` ("agreeing with the old germs in endpoint collars"), and "rows 89 and 91 MUST import the vocabulary
from SM/CeSmoothingRecord.lean rather than redeclare the memo's sketch (K-8)".  Both A and B redeclare the sketch
(without `collar`), so neither file can be ported as is.  Consequences adopted here:
1. FINAL imports `SM.CeSmoothingRecord`; `SpatialLink`, `projLoop`, `height`, `IsCusp`, `cuspSet`, `ExactCuspGerm`,
   `CuspedProjection`, `RegularGenericProjection`, `HeightMarking`, `CleanCuspSmoothing` (with `collar`),
   `SpatialFamily`, `CuspRoundingFamily` are the library's.  A's plan §5 asked for exactly this ("U-R one shared unit
   whose names are fixed here"): the library already holds `CleanCuspSmoothing.isDoubleOf_iff`, `deriv_eq_of_isDouble
   (hfin)`, `occSetOf_eq`, `crossSignOf_eq (hfin)`, `eval_eq_of_isDouble`, proved.  A's unit U-R (5 leaves, ~500
   lines) disappears.
2. The construction supplies `collar` (A's cutoff has `r < η`: one new easy leaf `chi_eq_zero_on_collar`).
3. The two clauses on which B is more literal than the memo/library (`intervals_disjoint` on the circle; the
   neighbourhoods `U` and the intervals of the clean smoothing = those of the fixing clause) cannot be edited into
   the library structure from a draft; they are carried by `CuspRoundingWitness L extends CuspRoundingFamily L`
   (§1), so row 90's object is delivered unchanged and the stronger printed reading is still asserted.  §7 lists
   the fold-in the row-90 unit should adopt.

## 1. Verdict

| criterion | A | B | notes |
|---|---|---|---|
| FIDELITY (clause by clause) | 7.5 | 8.5 | B: literal `[0,1]` quantifiers, circle-disjointness, `U` tied to `clean`, "take the constant family" as an EXISTENCE (B) rather than "every witness is constant" (A); split "creates no / retains" fields.  A: bundle in the accepted `RoundingData` pattern (one field per printed sentence) — B's two-field bundle is complete but not the repo's pattern; A's `same_velocity` field exports more than printed (CE-8).  Both: memo vocabulary verbatim, hypotheses identical and faithful, "no cusp on another branch" derived (proved).  Neither has `collar` (§0), neither imports the library. |
| FEASIBILITY | 8.5 | 7.5 | A: 36 fine-grained leaves, all audited TRUE; no IVT (symmetric parameter interval `[t₀−η, t₀+η]`, rectangle adapted to `u`'s range); cutoff smooth/periodic by composition (proved), 3 trivial value leaves; family global by the smooth clamp; assembly proved.  B: 19 coarse leaves, all audited TRUE, 13 more already proved (constant family kernel-checked); but N5 (`exists_cuspChart`, IVT + monotone bookkeeping + clean, ~400 lines), I4 (the no-new-coincidence case analysis) and P1/P5 (smoothness of `u·ρ(u)` glued by `if`, then periodised by `round`) concentrate the risk in three big leaves; `SpatialFamily` change forces a library edit before anything ports. |
| REUSE | 8.5 | 7.0 | A: accepted `RoundingData` bundle pattern, `TransverseFront.deriv_T` pattern (`deriv_space`/`deriv_xzOf` proved), record consequences as ABSTRACT lemmas on `CleanCuspSmoothing` — exactly what the library now provides under the same names, so the swap is free.  B: Mathlib `ContDiffBump`, templates cited, but re-proves the record consequences concretely (`isDoubleOf_slice_iff`, `occSetOf_slice_eq`, I4/I5) — duplicated against row 90. |
| total | **24.5** | 23.0 | **Winner: A**, with B's grafts: literal clauses (circle-disjointness, `U` tie, constant family as witness), `regular_of_no_cusps`, `constFamily`; and the §0 library alignment. |

Leaf audit (truth), both designs — every leaf checked by hand against the construction:
- A: all 36 true.  Two notes: `CleanCuspSmoothing.deriv_eq_of_isDouble`/`regular_everywhere` as stated on an
  ABSTRACT smoothing are true but the eventual-equality route needs finiteness of `cuspSet` (the library version
  carries `hfin`; superseded).  `arc_no_crossing` case 3 (the unmoved parameter is an END of the arc; `u³` strictly
  between the end values) and `mem_Icc_of_u_mem` with `u` decreasing are correct — probes for the false-leaf audit.
- B: all 19 true.  `famMap_regular` for ALL `λ` is true (`Δy = 0`, `y′ ≠ 0` on the germ intervals; off every closed
  arc the map is locally `L`).  `exists_sep`/`remote_far` need `hL` (included; false without).  `famMap_inside`'s
  bound `|X| ≤ s²/4 + s²/4 < s²` holds because `ρ = 0` for `|u| ≥ s/2`.  `Φ_contDiff` needs `b − a < 1/4` at the
  half-integer seams (present).

## 2. Clause map (printed → tex → Lean; FINAL)

| # | printed | tex | Lean |
|---|---|---|---|
| H1 | smooth oriented spatial embedding of a finite nonempty union of parameter circles in ℝ³; p = (x,z) | 3031-3032 | `L : SpatialLink c` (library), `0 < c`; `L.projLoop i` |
| H2 | only failures of regularity: finitely many isolated cusps | 3033-3034 | `IsCusp`, `cuspSet.Finite` (`CuspedProjection.cusps_finite`) |
| H3 | other coincidences: finitely many transverse double points | 3034-3035 | `doubles_finite`, `transverse` |
| H4 | no triple points or cusps on another branch | 3035-3036 | `no_triple`; `CuspedProjection.not_isCusp_of_isDouble` (PROVED consequence of `transverse`) |
| H5 | the two y heights at every double point are distinct | 3036 | `heights_distinct` (a printed field; also a consequence of `embedded`) |
| H6 | exact germ at every cusp on a parameter interval with smooth coordinate u = y − y₀ | 3037-3042 | `exact_germ : ∀ p ∈ cuspSet, ExactCuspGerm p.1 p.2` (∃ A ≠ 0, δ > 0, `y′ ≠ 0` on `(t₀−δ,t₀+δ)`, the three formulas) |
| H7 | u may increase or decrease; orientation not changed; formula a hypothesis | 3043-3046 | `y′ ≠ 0` of either sign; parameter kept; `exact_germ` a field |
| C1 | jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings, L_0 = L | 3048-3049 | `fam : SpatialFamily c` (library: `G : ℝ → SpatialLink c`, `ContDiff ℝ ∞` on `ℝ × ℝ`), `start`; bundle `smooth_embeddings_start` |
| C2 | fixed outside disjoint cusp parameter intervals | 3049-3050 | `a b`, `a_lt`, `lt_b`, `len`, `fixed_outside` (library) + `intervals_disjoint_circle` (mod ℤ; FINAL) ; bundle `fixed_outside_disjoint` |
| C3 | for every λ > 0 its xz projection is an ordinary finite regular generic diagram | 3050-3051 | `generic : 0 < λ → λ ≤ 1 → RegularGenericProjection`; bundle `generic_slices` |
| C4 | it cleanly smooths the cusps | 3051-3052 | `clean` (library, `Nonempty (CleanCuspSmoothing …)`, incl. `collar`) + `U`, `clean_in` (FINAL: same `U`, same `a b` for all λ) |
| C5 | creates no crossing, retains every original crossing with its oriented decorated data | 3052-3053 | `same_doubles` (↔), `same_data` (sign, height order); branches unchanged as THEOREM `CuspRoundingFamily.deriv_eq_of_isDouble`; bundle `clean_no_new_retains` |
| C6 | all original parameter circles, component labels and traversal orientations are retained | 3053-3054 | structural (same `Fin c`, same parameter, T-1) + `fixed_outside`; bundle `circles_retained` |
| C7 | with no cusps take the constant family | 3054 | `CeRoundingData.const_of_no_cusps : … cuspSet = ∅ → ∃ W, ∀ λ, W.fam.G λ = L` (PROVED: `constWitness`) |
| C8 | ordinary spatial deformation, not Legendrian/positive transverse, no self-linking transport | 3055-3057 | commentary; no field |

Readings CE-1..CE-9 are in the header of Statements_FINAL.lean (to be copied into AUTHOR_NOTES before the row is stated).

## 3. Model decisions

- **MD-1 vocabulary = library.** Nothing of SM/CeSmoothingRecord.lean §1 is restated (D-1/K-8).  Added on top:
  `SpatialLink.ext'`, `CuspedProjection.not_isCusp_of_isDouble`, `CuspRoundingFamily.deriv_eq_of_isDouble`.
- **MD-2 witness = `CuspRoundingWitness extends CuspRoundingFamily`** with `intervals_disjoint_circle` (CE-9; the
  library's `intervals_disjoint` is its `n = 0` case), `U`, `clean_in` (CE-7).  `toCuspRoundingFamily` hands row 90
  its object (`CeRoundingData.exists_cuspRoundingFamily`, K-3 non-vacuity).
- **MD-3 bundle** in the accepted `RoundingData` pattern: `exists_family` (theorem) + five printed-sentence readings on
  a witness (projections) + `const_of_no_cusps` (B's literal reading; A's "every witness is constant" dropped).
- **MD-4 family/time.** The library's `SpatialFamily` (global `C^∞`, embedded slices for every real λ) is met by
  `G λ = slice (Real.smoothTransition λ)`; on `[0,1]` this is the printed family in the reparametrized time
  `μ = φ(λ)` (CE-5).  B's strip reading is NOT adopted (it would edit the ported library and buys little: the
  junk slices remain by type); it is recorded for the row-91 unit as the equivalent literal alternative (§7).
- **MD-5 construction = A** (chart `GermData`, rectangle `[−M², 2M²] × [u₋³, u₊³]`, `remote` clearance, cutoff
  `periodicBump` in the parameter, displacement `(μ ε A u χ) • (1, 0, y₀)`, `core`, `coreLoop`).  Deviations from the
  printed proof inside the existential (CR-4): rectangle not the disc `V`; cutoff in `t` not in `u`; normalized
  sup-norm bound with `ε = M` instead of `|A| ε M √(1+y₀²) < d/2`.
- **MD-6 regularity route (new).** Instead of A's abstract `regular_everywhere` (a ~135-line transcription of the
  closure argument of FrontSmooth.lean 1245-1380, absent from the library), the concrete construction gives it
  directly: off every open arc the cutoffs vanish on a NEIGHBOURHOOD (`core_eventuallyEq_of_notMem`, supports
  `[t₀ − r, t₀ + r]` strictly inside the arcs) and such a parameter is not a cusp (`deriv_xz_ne_zero_of_notMem`);
  `core_xz_regular` (PROVED glue) combines them with `arc_regular`.  This also yields `collar`.
- **MD-7 glue promoted from A's leaves** (now PROVED): `chi_eq_zero_of_ne`, `core_on_arc` (from the new leaf
  `arcs_disjoint_circle`), `core_on_collar`, `core_regular`, `slice_generic` (library lemmas with `hfin`).

## 4. The chain — 33 leaves (Skeleton_FINAL.lean line: statement), by unit

**U-P cutoff (3 leaves, ~150 lines, low; deps none).**
`periodicBump_zero` (221): `0<r → r<1/2 → periodicBump r 0 = 1`; `periodicBump_eq_one` (225): `|s − n| ≤ r/2 →
periodicBump r s = 1`; `periodicBump_eq_zero` (230): `(∀ n:ℤ, r ≤ |s − n|) → periodicBump r s = 0`.  Tools:
`Real.cos_lt_cos_of_nonneg_of_le_pi`, `Real.cos_le_cos_of_nonneg_of_le_pi`, `Real.cos_int_mul_two_pi_add`/periodicity,
`round`/`Int.fract`, `Real.smoothTransition.one_of_one_le`/`zero_of_nonpos`.  (PROVED: `_contDiff`, `_periodic`,
`_nonneg`, `_le_one`, `exists_int_abs_lt_of_periodicBump_ne_zero`.)

**U-G germ, chart, rectangle (10 leaves, ~600 lines, medium; deps none).**
`exists_germData` (260): `ExactCuspGerm i t₀ → Nonempty (GermData i t₀)` (shrink `δ` to `min δ (1/3)`);
`chart_proj` (313): `t ∈ g.J → g.chart (xzOf (L.T i) t) = (g.u t^2, g.u t^3)` (`formula`; `field_simp; ring`);
`u_strictMonoOn_or_strictAntiOn` (326): `y'` continuous, nonzero on the interval ⇒ one sign (IVT on `deriv`, then
`strictMonoOn_of_deriv_pos` / `strictAntiOn_of_deriv_neg`); `rect_subset_closedBall` (365): sup norm, `Prod.norm_def`
(no hypothesis needed); `uMin_neg` (369), `uMax_pos` (372): `u t₀ = 0`, strict monotonicity, `a < t₀ < b`;
`u_mem_Icc_of_mem` (379), `mem_Icc_of_u_mem` (384; needs `t ∈ g.J`), `u_mem_Ioo_of_mem` (389), `abs_u_le_M` (393).
(PROVED: `chart_unchart`, `unchart_chart`, `chart_injective`, `chart_add_disp`, `u_injOn`, `cube_injective`,
`proj_injOn_J`, `rect_convex`, `rect_isCompact`, `M_pos`.)

**U-C one cusp (7 leaves, ~600 lines, medium-high; deps U-P, U-G; printed 3073-3096, 3121-3131).**
`chi_eq_zero_of_notMem` (462): `(∀ n, t + n ∉ Ioo a b) → chi t = 0` (`r < η`, U-P); `isDisc_U` (494): affine image of
the compact convex rectangle, interior via `chart ⁻¹' interior rect`; `center_mem_interior_U` (497): `chart c = 0 ∈
(−M², 2M²) × (u₋³, u₊³)`; `arc_in` (514); `clean` (519): `remote` + `norm_chart_le_of_mem_U` exclude remote parameters,
chart parameters via `Z = u³` monotone and `mem_Icc_of_u_mem`; `arc_simple` (524): `clean` + `proj_injOn_J`;
`chi_eq_zero_on_collar` (531, NEW): on `(a, a+(η−r)) ∪ (b−(η−r), b)`, `r < |t − t₀| < η` and other translates are
`≥ 1 − η > r` (`δ ≤ 1/3`).  (PROVED: `a_lt`, `lt_b`, `len`, `r_lt_half`, `Icc_subset_J`, `chi_*`, `disp_*`, `xz_disp`,
`norm_chart_le_of_mem_U`, `mem_U_iff`, `disp_eq_zero_of_chi`, `b_eq`.)

**U-L local analysis at time μ (9 leaves, ~1000 lines, HIGH; deps U-G, U-C; printed 3097-3131).**
`core_joint_contDiff` (588): `ContDiff ℝ ∞ (fun p => core (smoothTransition p.1) i p.2)` (`ContDiff.sum`, `split_ifs`,
`fun_prop`); `arcs_disjoint_circle` (634, NEW): `k ≠ k' → same circle → ∀ n, Disjoint (Ioo a b) (Ioo (a'+n) (b'+n))`
(both points of the projection would lie in the disjoint discs `U k`, `U k'`: `arc_in` + periodicity); `chart_core`
(662): `chart (xzOf (core μ) t) = (u² + μ ε u χ, u³)` on the open arc (`core_on_arc` PROVED, `chart_proj`,
`chart_add_disp`, `xz_disp`); `inside` (668): `|μ ε u χ| ≤ M²`, `mem_U_iff`; `arc_regular` (675): `z′ − y₀ x′ = 2A u² u′`
off `t₀`, `x′(t₀) = μ ε A u′(t₀)` (`χ(t₀) = 1`) — derivative bookkeeping on `Space`-valued maps via `deriv_space`/
`deriv_xzOf`, the germ `formula` on the open `J` with `Filter.EventuallyEq.deriv_eq`; `arc_injOn` (681): `Z = u³`;
`arc_no_crossing` (687): three cases — same arc mod 1 (`arc_injOn`), another arc (`inside` + `disjoint`), no open arc
(`core_eq_of_notMem`, `clean` puts `q` at an END of the arc, `u(t)³` strictly between the end values,
`u_mem_Ioo_of_mem`); `core_eventuallyEq_of_notMem` (711, NEW): `(∀ k n, t + n ∉ Ioo a_k b_k) → core μ i =ᶠ[𝓝 t] L.T i`
(`eventually_add_int_notMem_Icc` on `[t₀−r, t₀+r] ⊂ (a, b)`, `periodicBump_eq_zero`, `Filter.eventually_all` over
`Fintype cuspSet`); `deriv_xz_ne_zero_of_notMem` (719, NEW): a zero of the projected velocity at `t` puts
`(i, fract t)` into `cuspSet` (`SmoothLoop.deriv_eq_add_int`), which lies in its own open arc — contradiction.
(PROVED: `core_zero`, `core_contDiff`, `core_periodic`, `yOf_core`, `core_eq_of_notMem`, `coreLoop`, `chi_eq_zero_of_ne`,
`core_on_arc`, `core_on_collar`, `core_xz_regular`, `smoothing` incl. `collar`.)

**U-E existence of the choices (4 leaves, ~600 lines, medium-high; deps U-G; printed 3073-3096).**
`cusp_image_injective` (915): a common image is a double point at a cusp (`not_isCusp_of_isDouble`; `¬SameParam`
from both in `Ico 0 1`); `exists_gap` (920): finite set of distinct points; `exists_remote_clearance` (928): the remote
set is the projection of the compact `{t ∈ [t₀−1/2, t₀+1/2] : ∀ n, t + n ∉ J} ∪ other circles × [0,1]`, misses the
cusp image by `transverse`/`not_isCusp_of_isDouble`, `Metric.infDist_pos_iff_notMem_closure`, transport through
the affine `chart`; `exists_eta` (937): continuity of `u` at `t₀` (`u t₀ = 0`) drives `radius η → 0`; Lipschitz bound
of `unchart`.  (PROVED: `exists_cuspChoice_within` with `r := η/2`, `ε := M`; `exists_choices`.)

**Assembly (PROVED, ~300 lines):** `Choices.smoothing : CleanCuspSmoothing (coreLoop μ)` (with `collar`),
`core_embedded`, `core_regular`, `slice`, `fam`, `fam_zero`, `slice_generic`, `witness : CuspRoundingWitness L`,
`exists_cuspRoundingWitness`, `noCusp`, `regular_of_no_cusps`, `constSmoothing`, `constWitness` (no sorryAx),
`ce_rounding`.

Total ≈ 2.9-3.0k lines (memo: 3-5k; A: 3.5k with U-R; B: 2.9-4.1k).  Parallelisation: U-P ∥ U-G ∥ (U-E after U-G) ∥
(U-C after U-P, U-G) ∥ (U-L after U-G, U-C).  Statements never change.  Recommended order inside U-L: `chart_core`,
`inside`, `arc_injOn`, `arcs_disjoint_circle`, `deriv_xz_ne_zero_of_notMem`, `core_eventuallyEq_of_notMem`,
`core_joint_contDiff`, then `arc_regular`, `arc_no_crossing`.

## 5. Accepted / library declarations used (file:line)

SM/CeSmoothingRecord.lean (row 90, library): the whole §1 vocabulary (141-331); `CleanCuspSmoothing.isDoubleOf_iff`
439, `deriv_eq_of_isDouble (hfin)` 420, `occSetOf_eq` 458, `crossSignOf_eq (hfin)` 473, `eval_eq_of_isDouble` 415,
`eventuallyEq_of_closedArcFree (hfin)` 392; `projLoop_γ` 164.  SM/TransverseFront.lean: `Space`, `xOf/yOf/zOf/xzOf`
100-109, `SameT` 125.  SM/FrontSmooth.lean: `SmoothLoop` 166 (+ `eq_add_int` 196, `deriv_eq_add_int` 216), `Param`,
`SameParam` 242-297, `int_eq_of_add_mem_Icc` 1050, `eventually_add_int_notMem_Icc` 1060.  SM/FrontRecordBridge.lean:
`IsDoubleOf` 97, `occSetOf` 105, `crossSignOf` 118.  SM/Polygon.lean: `Plane` 13, `det` 16.  SM/LinkMoves.lean:
`IsDisc` 100.  SM/Rounding.lean: `RoundingData` 368 (bundle pattern); imported also for the `fun_prop` cosine
lemmas.  Mathlib: `Real.smoothTransition` (`contDiff`, `nonneg`, `le_one`, `zero`, `pos_of_pos`, `one_of_one_le`,
`zero_of_nonpos`), `strictMonoOn_of_deriv_pos`, `Odd.strictMono_pow`, `Metric.closedBall_disjoint_closedBall`,
`Metric.infDist_pos_iff_notMem_closure`, `Filter.EventuallyEq.{deriv_eq, fun_comp}`, `Filter.eventually_all`.

## 6. Fidelity risks — to be written into work/AUTHOR_NOTES.md BEFORE the row is stated (cite in the review)

- **CE-R1 (FR-1, GAP-1).** `RegularGenericProjection` is "the diagram" (as def:transverse-front, sm-3:341-343); the row
  does not deliver a polygonal `Diagram` with a `HeightMarking`; consumers 90/91 take the marking as a hypothesis.
- **CE-R2 (family index, CE-5).** The library's `SpatialFamily` indexes the slices by all of `ℝ`, jointly `C^∞` on
  `ℝ × ℝ`, embedded everywhere; the printed family is "0 ≤ λ ≤ 1" and "embeddedness outside [0,1] is not claimed".  The
  witness meets the type through the time clamp `μ = Real.smoothTransition λ`; on `[0,1]` it is the printed family
  reparametrized.  The strip reading (`ContDiffOn … (Icc 0 1 ×ˢ univ)`, design B) is equivalent up to this
  reparametrization (`ContDiffOn.comp` one way, restriction the other) and is the literal alternative for row 91.
- **CE-R3 (derived and redundant hypotheses).** "no cusps on another branch" is derived from `transverse`
  (`not_isCusp_of_isDouble`, no field); `heights_distinct` is kept as the printed field though it follows from
  `embedded` (a double point with equal heights would be a spatial coincidence of distinct parameters).
- **CE-R4 (construction ≠ printed constants; invisible in the statement).** Chart-rectangle `[−M², 2M²] × [u₋³, u₊³]`
  instead of the disc `V`; cutoff `periodicBump` in the parameter instead of `ρ(u)`; normalized sup-norm clearance
  with `ε = M` instead of `|A| ε M √(1+y₀²) < d/2`.  The printed distance argument survives in `exists_remote_clearance`.
- **CE-R5 (`collar`, D-1).** "It cleanly smooths the cusps" refers to the row-90 class WITH `collar`; the construction
  supplies it (`r < η`); the reviewer of 89 must accept D-1 or ask the row-90 unit to drop it (row 90's proof does not
  use it).
- **CE-R6 (witness extension).** `CuspRoundingWitness extends CuspRoundingFamily` adds `intervals_disjoint_circle`
  (the library's ℝ-disjointness admits wrap-around overlap), `U` and `clean_in` (one neighbourhood and one interval per
  cusp for the whole family, the same intervals as the fixing clause).  Row 90 quantifies over the parent; §7.
- **CE-R7 (bundle shape, FR-R5 analogue).** Fields 2-6 of `CeRoundingData` are projections of the witness; the theorem
  content is `exists_family` and `const_of_no_cusps`.  `same_velocity` (A) is a theorem, not a field.
- **CE-R8 (readings).** "spatial embedding" = injective immersion of compact circles (`embedded` + `regular`, CE-2);
  orientation = parameter direction (T-1); `ExactCuspGerm` on an OPEN interval; `0 < c` never used (K-6).
- **CE-R9 (scope).** The two disclaimers and the contact computation 3132-3169 are commentary; nothing Legendrian /
  transverse / `sl` is stated.  Row 89 is not GAP-2-blocked; its only consumer is row 91 (via 90's `D_ε`).
- **CE-R10 (chain audit).** All 33 leaves judged true (§1).  False-leaf probes: `arc_no_crossing` case 3;
  `mem_Icc_of_u_mem` with `u` decreasing; `exists_remote_clearance` (compactness of the remote set uses `δ ≤ 1/3`);
  `chi_eq_zero_on_collar` (uses `1 − η > r`, from `δ ≤ 1/3`); `deriv_xz_ne_zero_of_notMem` (needs the cusp's own arc
  to contain the cusp: `a_lt`, `lt_b`).
- **CE-R11 (non-vacuity, B's R-8).** `CuspedProjection` is nonempty (a round circle at height 0: no cusp, no double
  point); a kernel-checked witness (~40 lines) is recommended before acceptance; a cusped witness is not needed.

## 7. Interface with the row-90 / row-91 units (definition changes to adopt or record)

1. **Recommended fold-in (row 90, before its acceptance; its port is under review):** in `CuspRoundingFamily`
   replace `intervals_disjoint` by the circle version `∀ k k', k ≠ k' → k.1.1 = k'.1.1 → ∀ n : ℤ, Disjoint (Ioo (a k)
   (b k)) (Ioo (a k' + n) (b k' + n))`, add `U : L.cuspSet → Set Plane`, strengthen `clean` to `∃ cs, cs.U = U ∧ cs.a = a
   ∧ cs.b = b`.  Row 90 uses only `fam.G 1`, `clean 1` (as `Nonempty`), `same_doubles`, `same_data` — unaffected
   (`Classical.choice` of the `∃` replaces `Classical.choice` of the `Nonempty` in `endSmoothing`).  Then
   `CuspRoundingWitness` collapses to the library structure and the row-89 files drop the extension (mechanical).
   If NOT adopted, nothing breaks: the extension stands and `toCuspRoundingFamily` feeds row 90.
2. **`collar` (D-1) is accepted** by row 89 and supplied by its construction; no change requested.
3. **`SpatialFamily.joint_smooth` (row 91 only):** the literal strip version `ContDiffOn ℝ ∞ … (Icc 0 1 ×ˢ univ)` is
   recorded as equivalent (CE-R2); not required.  If the row-91 unit adopts it, the row-89 skeleton changes `fam` to
   the clamp `max 0 (min 1 λ)` with `(core_joint_contDiff).contDiffOn.congr` (five lines; `core` is globally smooth).
4. Row 90 may cite `CeRoundingData.exists_cuspRoundingFamily` for its K-3 (non-vacuity of `CuspRoundingFamily L`)
   once row 89 is accepted.
5. Unchanged: `SpatialLink`, `CuspedProjection`, `RegularGenericProjection`, `HeightMarking`, `CleanCuspSmoothing`.
