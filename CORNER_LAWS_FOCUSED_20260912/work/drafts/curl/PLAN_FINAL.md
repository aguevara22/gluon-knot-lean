# PLAN FINAL — cf:lem-curl (exact negative-curl replacement): judge's decision, fixed statement, skeleton

Row 98 cf:lem-curl, reference/SM/sm-3-statesum.tex:3870-3891 (statement), 3892-4280 (proof); consumer
cf:thm-carrierfloor (C), sm-3:4282-4330, use at 4438-4455 ("Apply Lemma cf:lem-curl at each of the R downward
vertical tangencies … Choose each curl disc inside its corresponding rounding disc … P_T = P_{D̄}, T has no downward
vertical tangency, w(T) = −w − R, every crossing of T is negative").
Judge (architect subagent), 2026-09-14. Inputs: PLAN_A.md / Statements_A.lean / Skeleton_A.lean (Architect A:
maximal reuse, record-level carrying, existential disc) and PLAN_B.md / Statements_B.lean / Skeleton_B.lean
(Architect B: literal smooth reading, `Carried` kept, chart-disc hypothesis). All four candidate files re-checked with
the plain `cd work/lean && lake env lean <file>`: 0 errors each (statements 1 sorry each; Skeleton_A 49 sorries,
Skeleton_B 47). `SM/Rounding.olean` exists in work/lean since 2026-09-14 05:12 UTC, so both A's `/tmp` olean detour
and B's §0 verbatim copy of Rounding.lean:70-222 are moot; the FINAL files `import SM.Rounding`.

Deliverables (this directory; nothing written under work/lean):
- `Statements_FINAL.lean` (386 lines) — the fixed statement. `lake env lean`: 0 errors, the only `sorry` is the row
  `SM.cf_lem_curl : CurlData` (line 381). `#print axioms SM.CurlData` = [propext, Classical.choice, Quot.sound, SM.lp_lm]
  (`lp_lm` is the policy literature axiom behind `P`, as for every polynomial statement);
  `SM.Carried.toRecordCarried` = [propext, Classical.choice, Quot.sound].
- `Skeleton_FINAL.lean` (1130 lines) — statement verbatim (§1-4) + construction (§5) + packages (§6) + chain (§7,
  **54 `sorry`**, all leaves) + assembly (§8, PROVED from the leaves) + row (§9, PROVED). 0 errors; the only non-sorry
  warning is an inherited `<;>` linter note at line 567. `#print axioms SM.cf_lem_curl` = [propext, sorryAx,
  Classical.choice, Quot.sound, SM.lp_lm]. Compile time 22 s.
- Check: `cd work/lean && lake env lean ../drafts/curl/Statements_FINAL.lean` (and `Skeleton_FINAL.lean`).

## 0. Verdict: **A wins** (statement shape, hypotheses as printed, record-level class, existential disc in any
preassigned neighbourhood, local polygonal kink), with five grafts from B and two repairs

| criterion | A | B | decision |
|---|---|---|---|
| hypotheses | the printed list only: `RecordCarried F D` (the diagram), `tangent_at`, `isolated` on the arc, `[α, β]` with `β − α < 1`, `InjOn`, no occurrence parameter on the arc, a lift `θ` with `StrictMonoOn` | the printed list **plus** a chart disc `Δ₀` in which the polygon `X` is one crossing-free arc in the same cyclic gap as `p` (`Δ₀_disc`, `p_mem`, `Δ₀_curve`, `arc0`, `Δ₀_cover`, `Δ₀_clean`, `Δ₀_no_crossing`, `compat`) | **A**: B's extra package is not printed and narrows the row's domain (the lemma no longer applies to a bare carried smooth diagram); the handoff's rule is no domain narrowing. The consumer supplies A's fields directly from `RoundingWitness` (`direction_once`, `junction_embedded`, `same_strands`, `θ_lift`/`θ_strict`) |
| "such an oriented diagram" (class) | `RecordCarried` = accepted `Carried` minus `τ_eval` (polygon crossing *points* = curve double points) plus `twin_eval`; `Carried.toRecordCarried` proved; the shape of the accepted `SmoothFront.Marking` (FrontSmooth.lean:1001-1020: occurrence bijection, cyclic order, pairing, bits, signs — no point coincidence) | accepted `Carried` on input and output | **A**, with the deviation recorded as FR-C1: under FR-R1 a polygonal kink of `D` cannot sit at the smooth double point `q` unless the polygon is rerouted to `q`, which is exactly what B's unprinted `Δ₀` hypothesis buys. The record is what the printed proof's last paragraph uses (record isomorphism, rp:record-polynomial), `P` is well defined at record level, and the consumer's next step (the transverse front, sm-3:4457ff) reads a `Marking`-shaped record |
| the disc | `exists_curl`: `∀ S Δ₀, p ∈ interior Δ₀ → ∃ Δ ⊆ Δ₀, Nonempty (CurlWitness S Δ)` (+ the bare printed form `exists_curl'`); `IsDisc Δ`, `p ∈ interior Δ`, `disc_meets_arc` | `∀ ρ > 0`, `Δ = curlDisc p r` (closed Euclidean, `r ≤ ρ`), `Δ ⊆ Δ₀` | **A** (more general neighbourhood, both printed and strengthened forms exported); B's round disc is what A's proof constructs anyway (`Curl.disc`) |
| modification | `F' = F` off the parameter window `(s₁, s₂)` mod 1 | `F' = F` with velocity on `[s₊, s₋ + 1]` | **A + graft**: `unchanged_deriv` (B) added to `CurlWitness` and to `CurlData.disc` — the consumer reads the tangents at the other R − 1 tangency points |
| (i) P, double points, signs | `RI D D'`, `P D' = P D` (accepted `P_reidemeister_I`); `doublePoints F' \ Δ = doublePoints F \ Δ`; `old : D.Crossing ≃ {y // y ≠ kink}`, `old_point`, `old_sign` | `RIData Δ₀ X X'`, `P_eq`; `doubles_outside`; `points_outside`/`signs_outside` through `ri.out.ψ` | equal content; **A**'s bijection avoids `OuterCrossing Δ₀` in the statement. B's general `RIData.crossingPoint_ψ / sign_ψ / writhe_eq` grafted as reusable Unit-K helpers |
| (ii) | `no_u`, `one_neg_u` (∃! in `[0,1)`) | same | equal |
| (iii) | `kink`, `kink_mem`, `one_double`, `kink_neg` (+ `kink_smoothSign`) | `double_in_disc_iff`, `kink_point`, `kink_negative` | equal |
| (iv) | `rot_eq`, `writhe_eq` (+ `smoothWrithe_eq`) | same + the lift mechanism (`θ, θ'`, `sweep_old ∈ (0, π)`, `sweep_new`) exported | **A**: the printed clause; the mechanism stays in the proof package `SmoothCurl` (no consumer reads it) |
| chain probed false | `inserted_arc_props`: two clauses false (no `ℓ > 0` hypothesis; diameter bound `≤ 2ℓ` not uniform in `a, b, c, d`) — **repaired** (`hℓ`, bound `ℓ (x + 2)`) | `exists_insertedArc`: `InsertedArc.in_disc` must hold for *every* `Cuts K`, but `Cuts` has no smallness clause tying the inserted arc (`ℓ x`, with `x = 2ac/(q(bc+ad))` unbounded as `b, d → 0` near the chart ends) to `r` — false; `exists_gluedLoop.double_interior` fails in the boundary-touching case for the same reason | both single, local, in the smooth cut/fit step; FINAL merges the cut choice with the containment (`CutFit`) so the false form cannot recur |
| smooth-side decomposition | one 1800-line leaf `exists_smooth_arc` | `Cuts` → `InsertedArc` → `GluedLoop` (three packages) | **graft**: Unit R split into `CutFit` + `exists_cutFit` (cuts, fit, containment) and `exists_glued_arc` (collars, reparametrisation, bookkeeping) |
| polygonal kink | `KinkLocation` (a free interior edge point of `D` off other edges, in the cyclic gap of `t₀`) + a tiny local monogon (`RIData` in a small disc `U` about it) | a kink through the prescribed point `q` with prescribed strand directions inside the large disc `Δ₀` (routing from the arc's entry to `q` and on to its exit) | **A**: local splice (the SM/Smoothing.lean template), no planar routing; the `order_*` clauses are the same in both |
| "turns strictly positively" | `StrictMonoOn θ` of a lift (the proof's chart uses only this; the consumer has `θ_strict`) | `det(γ', γ'') > 0` on the arc (the model's criterion, sm-3:3900) | **A** (the consumer's form); B's reading is implied and noted in FR-C5 |
| effort | 49 leaves, ≈7850 lines, 2 waves | 47 leaves, ≈9000-10000 lines, 3-4 waves, plus consumer-side re-establishment of the `Δ₀` package after each curl | A; FINAL: 54 leaves, ≈8500 lines, 7 units, 2 waves |

Scores (0-10): FIDELITY A 8 / B 6.5 (A: one class deviation, FR-C1; B: four unprinted hypotheses + `compat`,
class kept). FEASIBILITY A 7.5 / B 5.5 (both typecheck; A one false leaf repaired, B two false leaves, larger and
harder kink, consumer bookkeeping). REUSE A 8 / B 8 (same accepted base; B's general `RIData` lemmas grafted).
Total A 23.5 / B 20.

Numeric sanity of the model (checked by hand on the printed formulas, sm-3:3893-3921, 3977-4006): `b(±2) = c(±2) =
(3, ∓6)`, `c'(−2) = (−4, −11) = 11 (q v₀ + u₀)`, `c'(2) = (4, −11) = 11 (−q v₀ + u₀)` with `q = 4/11`;
`A(q v₀ + u₀) = qx v + (1 + qy) u = H v + (Hb/a) u = (H/a) T₋`, `A(−q v₀ + u₀) = (H/c) T₊`; `det A = x`;
`1 − (qy)² = 4abcd/(bc+ad)²`; `det(c'(1), c'(−1)) = det((2,−2), (−2,−2)) = −8`; the loop `c([−1, 1])` is clockwise
(rightmost point `(0,0)` → bottom → leftmost `(−1, 0)` → top → back), so "later branch over" is negative under the
accepted `Diagram.sign x = sgn det(dir over, dir under)` (LinkDiagram.lean:552) — the convention `q₂` over `q₁`,
`double_neg : det (F' q₂) (F' q₁) < 0`, `order_pair` (under first) and `KinkInsertion.kink_neg` are mutually consistent.
Transverse excess of `Φ ∘ c` over the chord: `⟨A(c(t) − b(−2)), v⟩ = (4 − t²) x`, positive for `|t| < 2`.

## 1. Clause map (printed → Lean; tex lines; unchanged from A except the graft)

| tex | printed | Lean (Statements_FINAL.lean) |
|---|---|---|
| 3871-3872 | "rot as in lem:rot for polygons and cf:def-turning for closed C¹ regular curves" | `F.toClosedC1Curve.rot` (accepted bridge; only smooth curves occur in this row) |
| 3873-3874 | "F a connected C^∞ immersed circle — one component, finitely many transverse double points, no triple points" | `CurlSite.F : SmoothRegularLoop`; the double-point clauses are `RecordCarried` (`doubles`, `transverse`, theorem `no_triple`) |
| 3874 | "given with an oriented diagram" | `CurlSite.D : Diagram`, `CurlSite.carried : RecordCarried F D` (§2, FR-C1) |
| 3874-3875 | "p a point of F at which the tangent points in a fixed direction u" | `t₀`, `u`, `tangent_at : normalize (deriv F.γ t₀) = u`; `p := F.γ t₀` |
| 3875 | "isolated among such points" | `isolated : ∀ t ∈ Icc α β, T t = u → t = t₀` |
| 3876 | "lying in an embedded arc of F that contains no double point" | `α β`, `α < t₀ < β`, `β − α < 1`, `embedded : InjOn F.γ (Icc α β)`, `no_double : ∀ v n, τ v + n ∉ Icc α β` |
| 3877 | "along which the tangent turns strictly positively" | `θ`, `lift : IsLiftOn T θ α β`, `turns_pos : StrictMonoOn θ (Icc α β)` |
| 3878-3879 | "F may be modified inside a disc Δ meeting the rest of the diagram only in that arc" | `CurlWitness S Δ`: `unchanged` + **`unchanged_deriv`** (F' = F with velocity off the window `(s₁,s₂)` mod 1), `new_in_disc`, `old_in_disc`, `disc : IsDisc Δ`, `p_mem`, `disc_meets_arc`; existence `CurlData.exists_curl` (Δ inside any preassigned neighbourhood Δ₀ of p) and `exists_curl'` (as printed) |
| 3881-3883 (i) | "is again such an oriented diagram" | `F' : SmoothRegularLoop`, `D' : Diagram`, `carried' : RecordCarried F' D'`, `ri : RI D D'` |
| (i) | "satisfies P_{F'} = P_F" | `poly_eq : P D' = P S.D` |
| (i) | "has the same double points outside Δ, with the same signs" | `doubles_outside`, `old : D.Crossing ≃ {y // y ≠ kink}`, `old_point`, `old_sign` |
| 3884-3885 (ii) | "no point of Δ at which the tangent equals u, and exactly one at which it equals −u" | `no_u`, `one_neg_u` (∃! in `Ico 0 1`) |
| 3886 (iii) | "exactly one double point inside Δ, and it is negative" | `kink`, `kink_mem`, `one_double`, `kink_neg : D'.sign kink = −1` (+ `kink_smoothSign`) |
| 3887 (iv) | "rot(F') = rot(F) − 1 and w(F') = w(F) − 1" | `rot_eq`, `writhe_eq` (+ `smoothWrithe_eq`) |

Bundle `CurlData : Prop`: `exists_curl` (the theorem), `exists_curl'`, `disc`, `i`, `ii`, `iii`, `iv` (projections of
`CurlWitness`, the FR-R5 pattern). Main declaration `SM.cf_lem_curl : CurlData` (cf:* convention; not in the checker's
fixed-name list). Entry point from the rounding output: `CurlSite.ofCarried` (a `Carried` record through
`Carried.toRecordCarried`); for the second and later curls the consumer builds `CurlSite` from the previous witness's
`carried' : RecordCarried` directly.

## 2. Model decisions (retained from A; B's alternatives and why not)

D1 input class = rounding output: `SmoothRegularLoop` + a polygonal `Diagram` it carries. B: same.
D2 record-level carrying (FR-C1): `RecordCarried` = `Carried` − `τ_eval` + `twin_eval`. B keeps `Carried` and pays with the
unprinted `Δ₀` package (the polygon must be rerouted through the new double point inside a disc where it has one arc);
without such a hypothesis B's statement would be unprovable in general (the polygon may be far from `p`). A's notion is
`SmoothFront.Marking`'s and is what rp:record-polynomial needs; `P` of a smooth diagram is well defined at record level.
D3 disc: existential, strengthened to "inside any preassigned neighbourhood" (sm-3:4038-4041; consumer 4442); a ∀-Δ form
is false (a large disc can contain a −u tangency of the old arc). B's fixed round disc of radius ≤ ρ is a special case.
D4 modification = parameter window mod 1, with velocity (graft). B: one period `[s₊, s₋ + 1]` — equivalent.
D5 polynomial via the polygonal RI (`P_reidemeister_I`); the printed F°/record-isomorphism route is subsumed. B: same.
D6 signs/writhe on `D'`, transported by `RecordCarried.sign_eq`; `rot` by `rot_sub_rot_of_replace` after a seam shift.
B: same lemma; signs read as `Carried.smoothSign` (equal by `smoothSign_eq`).
D7 "isolated" = uniqueness on the arc (consumer: `direction_once`); "turns strictly positively" = `StrictMonoOn` of a
lift (consumer: `θ_strict`). B: local ∃δ isolation and `det(γ', γ'') > 0`; both implied by A's on the chart.
D8 (new) the smooth side is two provers: `CutFit`/`exists_cutFit` (cuts, fit coefficients, `ℓ > 0`, removed and inserted
arcs inside the disc — chosen together) and `exists_glued_arc` (collars, reparametrisation, all window facts).

## 3. Chain audit (every leaf statement checked for truth; the repairs)

Probed false and repaired (A): `inserted_arc_props` had hypotheses `s₁ < s₂`, `ξ s₁ = ξ s₂`, endpoint tangents in the
open quadrants — with `s₁, s₂` arbitrary reals this does not force `ℓ = η s₂ − η s₁ > 0`; for `ℓ ≤ 0` the clauses
"`deriv Φc (−2) = r • T s₁`, `r > 0`" and "`ξ s₁ < ⟨Φc t − p, v⟩`" fail. Repair: hypothesis `hℓ : η S s₁ < η S s₂`
(printed sm-3:3981, supplied by `η_strictMonoOn`). The diameter clause `|Φc t − p₋| ≤ 2ℓ` is false for large `x`
(`a = c = 1`, `b = d → 0` gives `x → ∞`); repair: `≤ ℓ (xFit a b c d + 2)` (proof: `(ℓ/12)(4x + 11 + 12) ≤ ℓ(x + 2)`).
Probed false, not adopted (B): `exists_insertedArc : ∀ K : Cuts S ρ, Nonempty (InsertedArc S K)` — `in_disc` needs the
cuts small enough for the inserted arc (diameter of order `ℓ x`) to fit in `curlDisc p r`; `Cuts` does not say so.
`exists_gluedLoop`'s `double_interior` has the same gap in the boundary case. FINAL's `CutFit` carries `ins_in_disc` and is
produced by the leaf that also chooses the cuts.
Checked true (statement-level reasoning recorded here for the provers):
- Unit M/F algebra: `fitA_ray_minus/plus` by substitution (§0 above); `det_fitA_pos`: `det(x v + y u, u) = x det(v, u)`;
  `yFit_bound`: `|bc − ad| < bc + ad`; `orderedRay_condition`: `det((−q,−1),(q,−1)) = 2q`, `det(av+bu, −cv+du) = ad + bc`
  (no positivity needed).
- Unit G: with `T = (cos θ, sin θ)`, `u = T t₀`, `v = −J u = (sin θ₀, −cos θ₀)`: `⟨T, u⟩ = cos θrel`, `⟨T, v⟩ = −sin θrel`,
  hence `hasDerivAt_η/ξ` (the parameter is not arclength: factor `|F'|`), `endpoint_tangent`, the monotonicity of `ξ`
  (`θrel < 0` on `[α', t₀)`, `> 0` on `(t₀, β']`, `|θrel| < π/2`) and of `η`; `exists_cuts` by IVT at a level below `0`
  chosen from `max(ξ(max(α', t₀ − δ/3)), ξ(min(β', t₀ + δ/3)))`; `exists_disc_in_chart` by compactness of
  `F([β', α' + 1])`, which misses `p` (embedded arc, no double point on it); `tail_tangent_ne`: `θrel ≠ 0, ±π`.
- Unit H: `blend` is `f` for `η ≤ e₁` and `g` for `η ≥ e₁ + lam` (`smoothTransition.zero_of_nonpos/one_of_one_le`);
  `h' = (1−φ) f' + φ g' + (φ'/lam)(g − f)` with `φ' ≥ 0`, `g ≥ f` (from `sep_of_deriv`) gives `h' ≥ f'`; the mirrored
  collar: `(g − f)' = g' − f' < 0` on `[e₂ − lam, e₂)` and `(g − f)(e₂) = 0` give `g ≥ f`, hence `h' ≤ f'`.
- Unit R: `exists_glued_arc`'s `N t ∈ disc` — collar points lie on `v`-segments between a removed-arc point and an
  inserted-arc point, both in the convex disc; `N s ≠ F t` for `s` in the open window, `t` off it — `N s` has
  `ξ > ξ(s₁)` (excess, and `h ≥ f > ξ(s₁)` on the collars), while `F t ∈ disc` forces `t + n ∈ [α', s₁] ∪ [s₂, β']` with
  `ξ ≤ ξ(s₁)`; `exists_loop_of_arc`: the periodic extension is smooth because `N = F` on a neighbourhood of each end
  and `s₂ − s₁ < 1`.
- Unit T: seam shift to `s₁`, `lam = mu = s₂ − s₁`, `ψ = id`; `hcompl` is the equality of unit tangents on `[s₂, s₁ + 1]`,
  which holds including the endpoints (`deriv_eq_of_offWindow`).
- Unit K: `KinkLocation` — the open cyclic gap of `D`'s traversal circle corresponding to `t₀`'s gap among the `τ`
  (`carried.order`) contains infinitely many interior edge points and only finitely many points of other edges;
  `KinkInsertion.order_pair` — the two kink occurrences are adjacent (no old occurrence in the tiny disc `U`), under
  first; `RIData.sign_ψ` — an outer crossing point is not on `∂U` (`Clean.frontier_injOn`: two traversal points would
  evaluate there), so `dir_pos` applies at both occurrences; `RIData.writhe_eq` — inner crossings of `D'` = `{kink}`.
- Unit C: `cycBetween_ext_of_insert_pair` — every triple is a rotation/reversal of an all-old, one-inserted or
  two-inserted triple or has a repetition (`not_cycBetween_self_*`); `cycBetween_fract_gap/pair` hold also when the
  window wraps past an integer (e.g. `x = 0.9, y = 1.1`, `τ ∈ [0.2, 0.8]`: `cycBetween τ 0.9 0.1`).
- Unit A: `deriv_eq_of_offWindow` at an endpoint `s₁` (mod 1): `F' = F` on `(s₁ − ε, s₁]` because the window is shorter
  than the period, both differentiable, so the derivatives agree; `one_double_of` — both parameters in the closed
  window ⇒ `only_double`; one in the open window ⇒ `arc_off_rest`; both off ⇒ a double point of `F` in `Δ`, excluded
  by `meets_arc` + `no_double`.
Proved in the skeleton (no sorry): Unit M algebra (8), `fitA_u₀/v₀`, `IsLiftOn.mono`, `shiftCurve`,
`τ_offClosedWindow`, `F'_τ`, `F'_fract`, `ri_of`, `no_u_of`, `deriv_eq_of_offClosedWindow` (from the open-window leaf),
`curlWitness` (every field), `exists_curl_main`, `cf_lem_curl`, and the statement-side `RecordCarried.no_triple`,
`doublePoints_eq`, `smoothWrithe_eq`, `Carried.toRecordCarried`.

## 4. Unit split (7 prover units on byte-identical copies of Skeleton_FINAL.lean; statements never change)

| unit | leaves (sorried) | content | est. lines | depends on | wave |
|---|---|---|---|---|---|
| **U1 MF** model + fit (11) | `hasDerivAt_cModel`, `hasDerivAt_bModel`, `cModel_double`; `fitA_add`, `fitA_smul`, `det_fitA_pos`, `fitA_ray_minus`, `fitA_ray_plus`, `yFit_bound`, `xFit_pos`, `orderedRay_condition` | sm-3:3893-3921, 3977-4006: `HasDerivAt.prodMk`, `field_simp; ring`, `nlinarith` | 450 | Mathlib | 1 |
| **U2 G** chart, cuts, disc, cut-fit (17) | `det_vDir_u`, `planeDot_vDir_u`, `expansion`, `exists_chart`, `hasDerivAt_η`, `hasDerivAt_ξ`, `ξ_strictMonoOn`, `ξ_strictAntiOn`, `η_strictMonoOn`, `exists_cuts`, `cut_displacement`, `endpoint_tangent`, `exists_disc_in_chart`, `disc_isDisc`, `p_mem_interior_disc`, `tail_tangent_ne`; `exists_cutFit` | sm-3:3959-3990, 4038-4041; IVT cuts; compactness; `CutFit` from cuts close to `t₀` (`x → 0`, `ℓ → 0`; may cite the bound of `inserted_arc_props` or prove `|Φc t − p₋| ≤ ℓ(x+2)` directly) | 1300 | Mathlib; statements of U1 | 1 |
| **U3 HT** collar + turning (9) | `blend_smooth`, `blend_eq_left`, `blend_eq_right`, `sep_of_deriv`, `deriv_blend_ge`, `blend_between`, `deriv_blend_le`; `rot_shiftCurve`, `rot_sub_rot_of_window` | sm-3:4080-4212 abstract in `f, g, φ` (Rounding.lean §8 Unit P lemmas `smoothTransition_strictMonoOn`, `deriv_smoothTransition_pos`, `iteratedDeriv_eq_zero_of_const_left/right`); `tw_shift`, `rot_sub_rot_of_replace` with `ψ = id` | 650 | Mathlib, SM.Rounding, SM.TurnLift | 1 |
| **U4 R** replacement (4) | `inserted_arc_props`, `exists_glued_arc`, `exists_loop_of_arc`, `exists_smoothCurl` | sm-3:4033-4079, 4213-4244: `Φ ∘ c` facts; the `C^∞` regular parametrisation on `[s₁, s₂]` (graphs over `η`, collars through `η ∘ F`, monotone change of variable for the model), lift increment via `glplus_increment_sub_invariant`; periodic extension; assembly of `SmoothCurl` | 1900 (glued arc ≈ 1400) | U1, U2, U3 (statements); `inserted_arc_props` and `exists_loop_of_arc` can start in wave 1 | 2 |
| **U5 K1** kink location + RI helpers (4) | `exists_kinkLocation`, `RIData.crossingPoint_ψ`, `RIData.sign_ψ`, `RIData.writhe_eq` | gap point off other edges (finitely many meeting points; `Regular`/`tail_off` for adjacent edges); the three general `RIData` lemmas (`OutsideMatch.eval_eq/dir_pos/over_eq/under_eq`, `Clean.frontier_injOn`, `inner_iff'`) | 600 | SM.LinkMoves, SM.LinkDiagramRecord | 1 |
| **U6 K2** kink insertion (1) | `exists_kinkInsertion` | the polygonal monogon at `L.r`: three new vertices in a small disc `U` about `r`, clockwise, later branch over; `Shadow.Generic`, `RIData` (`ArcCover`, `Clean`, `MoveMatch`), `old`/`oldVisit` correspondences, `visitCoord` order clauses, `kink_neg`, `writhe` (may use U5's helpers). Template: SM/Smoothing.lean `SpliceModel` and §0' generic-shadow lemmas, §5-§6e; SM/MarkedProducts.lean §R1 | 2500 | SM.LinkMoves, SM.Smoothing (patterns) | 1 (start first: critical path) |
| **U7 CA** record + assembly bookkeeping (8) | `cycBetween_ext_of_insert_pair`, `cycBetween_fract_gap`, `cycBetween_fract_pair`, `exists_carriedAssembly`; `deriv_eq_of_offWindow`, `doublePoints_diff_eq`, `one_neg_u_of`, `one_double_of` | cyclic-order extension by an inserted adjacent pair; `RecordCarried F' D'` with `τ'` = old `τ` / `fract q₁` / `fract q₂`; window/period bookkeeping (`Int.fract`, `SmoothLoop.eq_add_int`, `deriv_eq_add_int`) | 1100 | package statements only (`SmoothCurl`, `KinkLocation`, `KinkInsertion`, `CarriedAssembly`) | 1 |
| total | **54** | | ≈ 8500 | | 2 waves |

Critical path: U6 (2500) ‖ U2 → U4 (1300 + 1900). Check per unit: `cd work/lean && lake env lean ../drafts/curl/U_<unit>.lean`
(a copy of Skeleton_FINAL.lean with that unit's sorries filled). Assembly: concatenate the filled units into one file in
skeleton order (statements byte-identical), re-run `#print axioms SM.cf_lem_curl` (expected: [propext, Classical.choice,
Quot.sound, SM.lp_lm]), then port as `SM/Curl.lean` (imports `SM.Rounding`, `SM.LinkMoves`, `SM.PolynomialBlock`).

## 5. What the consumer cf:thm-carrierfloor (C) reads (sm-3:4423-4455)

Site at each of the R downward tangencies: `CurlSite.ofCarried` with `F = L_ε` (rounded curve, after the crossing
switch `D := switch-all`, still `Carried` since `Carried` reads over/under from the polygon), `u` = the downward vertical,
`t₀` = the tangency parameter, `[α, β] = [a j, b j]` the junction (`junction_embedded`; `same_strands` ⇒ `no_double`;
`θ j`, `θ_lift`, `θ_strict` ⇒ `lift`, `turns_pos`; `direction_once` ⇒ `isolated`; `b j − a j < 1`), `Δ₀ := cornerDisc C ε j`.
Output: `exists_curl` gives `Δ ⊆ Δ₀`; `unchanged`/`unchanged_deriv` + `disc_meets_arc` make the R supports disjoint and
the other tangencies untouched; `no_u`, `doubles_outside`, `old_sign`, `kink_neg` give "T has no downward vertical
tangency" and "every crossing negative"; `poly_eq` R times gives `P_T = P_{D̄}`; `writhe_eq` R times gives `w(T) = −w − R`;
`F'` is a `SmoothRegularLoop` for the transverse lift, and `carried' : RecordCarried` is the `Marking`-shaped record the
front step needs. For the second and later curls the site is built from `carried'` directly (`no_double` for `D'`: old
parameters as before, the two kink parameters lie in the previous window, disjoint from the other junctions).

## 6. Accepted declarations used (grep-verified 2026-09-14 in work/lean; A's list, unchanged)

SM/Rounding.lean:148 `SmoothRegularLoop`; :156 `toClosedC1Curve`; :162 `doublePoints`; :183 `Carried` (:189 `τ_eval`);
:205-222 `Carried.smoothSign/smoothWrithe`; :466 `CornerRounding.dirOf`; :603 `smoothTransition_strictMonoOn`; :640
`deriv_smoothTransition_pos`; :679/:686 `iteratedDeriv_eq_zero_of_const_left/right`; :2948 `roundedLoop`; :3008
`roundedWitness`; `RoundingWitness` fields `junction_embedded`, `same_strands`, `θ_strict`, `direction_once`,
`disc_only_modification` (:231-336).
SM/FrontSmooth.lean:144 `SmoothLoop` (`eq_add_int` :196, `deriv_eq_add_int` :216); :1001 `SmoothFront.Marking`.
SM/TurningNumber.lean:226 `normalize`; :228 `euclideanLength_normalize`; :241 `ClosedC1Curve`; :264 `tangentLoop`; :274 `rot`;
:102 `DirectionLoop.shift`; :215 `tw_shift`.
SM/TurnLift.lean:40 `IsLiftOn`; :55 `increment_eq`; :355 `rot_sub_rot_of_replace`; :394 `tangentLoop_T_eq_of_eventuallyEq`;
:409 `GLPlusPath`; :505 `glplus_increment_sub_invariant`; :385 `normalize_smul_of_pos`.
SM/Polygon.lean:16 `det`; SM/EuclideanPlane.lean:27 `planeDot`, :29 `euclideanLength`.
SM/LinkDiagram.lean:83 `Shadow`; :99 `seg`; :106 `dir`; :251 `Crossing`; :256 `Visit`; :372 `crossingPoint`; :394 `Generic`;
:404 `Pt`; :407 `eval`; :490 `Diagram`; :552 `sign`; :577 `writhe`; :597/:600 `overVisit/underVisit`; :650 `switch`.
SM/LinkDiagramRecord.lean:78 `cycBetween` (:85-95 `not_cycBetween_self_*`); :181 `visitCoord` (= `traversalKey` of the
visit's traversal point); :413 `twin` (:420 `twin_ne`). SM/Traversal.lean:12 `TraversalPoint`; :17 `traversalKey`.
SM/LinkMoves.lean:100 `IsDisc`; :145 `Shadow.Arc`; :198 `IsArc`; :208 `ArcCover`; :250 `OuterCrossing`; :316 `OutsideMatch`;
:342 `Clean`; :356 `MoveMatch`; :569 `RIData`; :590 `RI`; :778 `LinkEquiv.of_RI`; :943 `RIData.card_crossing`.
SM/LocalPolynomial.lean:22 `P`; SM/PolynomialBlock.lean:605 `P_reidemeister_I`.
Mathlib (pin 85e3a25e): `Real.smoothTransition` (+ `.zero_of_nonpos`, `.one_of_one_le`, `.contDiff`), `Int.fract`,
`intermediate_value_Icc`, `IsCompact.exists_forall_le`, `HasDerivAt.scomp`.

## 7. Fidelity risks — the executor writes these into AUTHOR_NOTES before the row is stated

FR-C1 (record-level carrying; the one class deviation). Input and output diagrams are `RecordCarried F D` — the accepted
`Carried` of cf:lem-rounding without `τ_eval` (no coincidence of the polygon's crossing *points* with the curve's double
points), plus `twin_eval`; occurrences, pairing, cyclic order, transversality and over/under-by-sign are shared. Forced
because a polygonal RI kink of `D` cannot sit at the smooth double point; coherent with the accepted `SmoothFront.Marking`
(record-level) and with the printed proof's own record-isomorphism step; `P` is well defined at record level
(rp:record-polynomial). The input accepts `Carried` through `Carried.toRecordCarried`. Reviewers of FR-R1 must be told
that the smooth-diagram class after a curl is `RecordCarried`, strictly weaker than `Carried` as an output.
FR-C2 (disc quantifier). `exists_curl` strengthens the printed ∃Δ to "inside any preassigned neighbourhood Δ₀ of p"
(the proof's sm-3:4038-4041; the consumer's 4442); the bare printed form is `exists_curl'`. A ∀-Δ form would be false.
FR-C3 (modification support). "Modified inside Δ" is read as equality of the *parametrised* curves, with velocity, off the
window `(s₁, s₂)` mod 1; the proof must produce a `C^∞` regular parametrisation of the replacement on `[s₁, s₂]` with `F`'s
jets at both ends (Unit R) — implicit in the printed proof (sm-3:4056-4079).
FR-C4 (polynomial). `P_{F'} = P_F` is `P D' = P D` from the polygonal RI (`P_reidemeister_I`), not the printed F°/record-
isomorphism route; both use lp:core's RI invariance (policy axiom `SM.lp_lm` appears in `#print axioms`, as for every
consumer of `P`).
FR-C5 (hypotheses). "Isolated" as uniqueness of the u-tangency on the arc; "turns strictly positively" as `StrictMonoOn` of
a lift `θ`; `β − α < 1`; the consumer's rounding junction supplies all three (`direction_once`, `θ_strict`, subdivision).
B's `det(γ', γ'') > 0` reading is implied by these on the chart.
FR-C6 (exports beyond print). `old_in_disc`, `disc_meets_arc`, the window `[s₁, s₂]`, `unchanged_deriv`,
`old : Crossing ≃ …`, `old_point`, `ri : RI D D'`, the smooth-sign/writhe corollaries; all supplied by the proof, read by
the consumer.
FR-C7 (effort). The polygonal kink insertion (U6, one leaf with a 16-field `KinkInsertion` spec) is a splice construction
comparable to a third of SM/Smoothing.lean; the smooth replacement (U4) is the analytic heart; total ≈ 8500 lines over
54 leaves in 7 units, 2 waves — about 2× cf:lem-rounding.
FR-C8 (chain repairs, recorded as FR-R6 was). A's `inserted_arc_props` was false in two clauses (missing `ℓ > 0`;
non-uniform diameter bound) — repaired here. B's `exists_insertedArc`/`exists_gluedLoop` were false for arbitrary cuts
(no smallness in `Cuts`) — not adopted; FINAL's `CutFit` chooses cuts and containment together.
FR-C9 (kink placement). The polygonal kink of `D'` is inserted at a free interior edge point `r` of `D` in the cyclic gap of
`t₀` (`KinkLocation.gap` compares `Int.fract t₀` with the occurrence parameters in `[0, 1)`; harmless since every
window parameter lies in the same gap); the smooth double point `q` and the polygonal kink point are unrelated (FR-C1).
The polygonal kink's sign convention must match the smooth model's `det(c'(1), c'(−1)) = −8` ("later branch over"):
fixed in `KinkInsertion.kink_neg`, `order_pair` and `SmoothCurl.double_neg`; consistent with `Diagram.sign`.
FR-C10 (check environment). Compiled with the plain `lake env lean` against the built `SM/Rounding.olean`
(2026-09-14 05:12 UTC); A's `/tmp` olean and B's §0 copy of Rounding.lean are no longer needed. Never `lake build` from a
draft; port as `SM/Curl.lean` after the units close.
