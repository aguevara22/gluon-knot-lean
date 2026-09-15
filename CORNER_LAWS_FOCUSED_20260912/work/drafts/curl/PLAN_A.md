# PLAN A — cf:lem-curl (exact negative-curl replacement): statement, model, chain (architect A)

Row 98 cf:lem-curl, reference/SM/sm-3-statesum.tex:3870-3891 (statement), 3892-4280 (proof; ends at 4280,
cf:thm-carrierfloor starts 4282). Architect A, 2026-09-14. Emphasis: maximal reuse of the rounding construction
(SM/Rounding.lean) and of the accepted polygonal RI move (SM/LinkMoves.lean `RIData`/`RI`); the curl = a polygonal
RI on the carried diagram + a smooth model inside one disc, linked through the carried record.

Deliverables (this directory):
- `Statements_A.lean` (377 lines): the fixed statement. 0 errors; the only `sorry` is the row `SM.cf_lem_curl : CurlData`.
- `Skeleton_A.lean` (1021 lines): statement verbatim (§1-4) + construction (§5) + packages (§6) + chain (§7, sorried
  leaves) + assembly (§8, PROVED from the leaves) + row (§9, PROVED). 0 errors, **49 `sorry`** (all leaves).
  `#print axioms SM.cf_lem_curl` = [propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm] (`lp_lm` is the policy
  literature axiom behind `P`); `SM.CurlData`, `SM.Carried.toRecordCarried` are `sorryAx`-free.
- Check command: `SM.Rounding` has no olean in work/lean yet (ported, not built), so `lake env lean` cannot import it;
  `/tmp/curl_check.sh <file>` = `cd work/lean && lake env bash -c 'LEAN_PATH=/tmp/curl_olean:$LEAN_PATH lean <file>'`
  with `/tmp/curl_olean/SM/Rounding.olean` compiled from work/lean/SM/Rounding.lean (10 s, exit 0) and symlinks to the
  built oleans. Nothing written under work/lean. Once `SM.Rounding` is built the plain command applies unchanged.

## 1. Clause map (printed → Lean; tex lines)

| tex | printed | Lean (Statements_A.lean) |
|---|---|---|
| 3871-3872 | "rot as in lem:rot for polygons and cf:def-turning for closed C¹ regular curves" | `F.toClosedC1Curve.rot` (accepted bridge, only smooth curves occur here) |
| 3873-3874 | "F a connected C^∞ immersed circle — one component, finitely many transverse double points, no triple points" | `CurlSite.F : SmoothRegularLoop`; the double-point clauses are `RecordCarried` (`doubles`, `transverse`, `no_triple` theorem) |
| 3874 | "given with an oriented diagram" | `CurlSite.D : Diagram`, `CurlSite.carried : RecordCarried F D` (§2, FR-C1) |
| 3874-3875 | "p a point of F at which the tangent points in a fixed direction u" | `t₀`, `u`, `tangent_at : normalize (deriv F.γ t₀) = u`; `p := F.γ t₀` |
| 3875 | "isolated among such points" | `isolated : ∀ t ∈ Icc α β, T t = u → t = t₀` |
| 3876 | "lying in an embedded arc of F that contains no double point" | `α β`, `α < t₀ < β`, `β − α < 1`, `embedded : InjOn F.γ (Icc α β)`, `no_double : ∀ v n, τ v + n ∉ Icc α β` |
| 3877 | "along which the tangent turns strictly positively" | `θ`, `lift : IsLiftOn T θ α β`, `turns_pos : StrictMonoOn θ (Icc α β)` |
| 3878-3879 | "F may be modified inside a disc Δ meeting the rest of the diagram only in that arc" | `CurlWitness S Δ`: `unchanged` (F' = F off the window `(s₁,s₂)` mod 1), `new_in_disc`, `old_in_disc`, `disc : IsDisc Δ`, `p_mem`, `disc_meets_arc`; existence `CurlData.exists_curl` (Δ inside any preassigned neighbourhood Δ₀ of p) and `exists_curl'` (as printed) |
| 3881-3883 (i) | "is again such an oriented diagram" | `F' : SmoothRegularLoop`, `D' : Diagram`, `carried' : RecordCarried F' D'`, `ri : RI D D'` |
| (i) | "satisfies P_{F'} = P_F" | `poly_eq : P D' = P S.D` |
| (i) | "has the same double points outside Δ, with the same signs" | `doubles_outside` (set equality of `doublePoints \ Δ`), `old : D.Crossing ≃ {y // y ≠ kink}`, `old_point`, `old_sign` |
| 3884-3885 (ii) | "no point of Δ at which the tangent equals u, and exactly one at which it equals −u" | `no_u`, `one_neg_u` (∃! in `Ico 0 1`) |
| 3886 (iii) | "exactly one double point inside Δ, and it is negative" | `kink`, `kink_mem`, `one_double`, `kink_neg : D'.sign kink = −1` (+ `kink_smoothSign`) |
| 3887 (iv) | "rot(F') = rot(F) − 1 and w(F') = w(F) − 1" | `rot_eq`, `writhe_eq` (+ `smoothWrithe_eq`) |

Bundle `CurlData : Prop`: `exists_curl` (the theorem), `exists_curl'`, `disc`, `i`, `ii`, `iii`, `iv` (projections of
`CurlWitness`, FR-R5 pattern). Main declaration `SM.cf_lem_curl : CurlData` (not in the checker's fixed-name list).

## 2. Model decisions

D1 (input class = rounding output). `F : SmoothRegularLoop` (Rounding.lean:148) and a polygonal `Diagram` it carries —
the vocabulary of the accepted row; `CurlSite.ofCarried` builds a site from a `Carried F D` (rounding's `carried`).
D2 (FR-C1, the one deviation from `Carried`). The accepted `Carried` (Rounding.lean:183) contains
`τ_eval : γ (τ v) = crossingPoint v`: the *polygon's* crossing points coincide with the curve's double points. A curl
inserts a smooth double point `q` near `p`, while the polygonal kink (an RI move on `D`) sits on an edge of `D`,
wherever that polygon lies; the two cannot coincide in general, and no planar isotopy can drag the kink to `q`
without crossing other edges. Hence `RecordCarried` (Statements_A.lean §1) = `Carried` minus `τ_eval` plus
`twin_eval : γ (τ v) = γ (τ (twin v))`; `Carried.toRecordCarried` is proved. This is exactly the shape of the accepted
front record `SmoothFront.Marking` (FrontSmooth.lean:1003-1020: occurrence bijection, cyclic order, pairing, bits,
signs — no point coincidence), so the smooth-diagram notion of the front block and of this row agree; the printed
"oriented diagram" of a smooth curve is its record with over/under choices, which is what `RecordCarried` states.
Input and output are both `RecordCarried`, so the consumer can iterate the lemma R times (sm-3:4438-4444).
D3 (disc). Existential as printed, strengthened to "inside any preassigned neighbourhood Δ₀": this is what the proof
does (sm-3:4038-4041 "the disc is fixed first and the cuts afterwards") and what cf:thm-carrierfloor (C) needs
(sm-3:4442 "Choose each curl disc inside its corresponding rounding disc"). A ∀-Δ form would be false (a large disc
can contain a −u tangency of the old arc).
D4 (modification = parameter window). `F' = F` outside `(s₁, s₂) ⊆ [α, β]` mod 1 (`OffWindow`), same parameter
circle; the consumer reads unchanged tangencies and crossings outside the disc from this. Cost: the replacement must
be parametrised on `[s₁, s₂]` with `F`'s jets at both ends (Unit R, leaf `exists_smooth_arc`).
D5 (polynomial). `P_{F'} = P_F` is `P D' = P D` from the accepted `P_reidemeister_I` (PolynomialBlock.lean:605) applied
to `RI D D'` — no record-isomorphism detour (the printed proof's F° step is subsumed by the polygonal RI).
D6 (signs, writhe, rot). Signs/writhe on the polygonal `D'` (accepted `Diagram.sign`/`writhe`), transported to the
smooth curve by `RecordCarried.sign_eq`; `rot` by the accepted arc-replacement clause `rot_sub_rot_of_replace`
(TurnLift.lean:355) after a seam shift (`shiftCurve`, `rot_shiftCurve` from `tw_shift`).
D7 (hypothesis "isolated"). Stated as uniqueness on the arc (consumer: `direction_once`); implied locally by strict
monotonicity; a user may shrink the arc.

## 3. What the consumer cf:thm-carrierfloor (C) reads (sm-3:4423-4444)
Input at each of the R downward tangencies: `CurlSite.ofCarried` with F = the rounded curve `L_ε` (after the
crossing switch: `D := switch-all`, still `Carried` since `Carried` reads over/under from `X`), `u` = the downward
vertical, `t₀` = the tangency parameter, `[α, β] = [a j, b j]` the junction (embedded: `junction_embedded`; no
double point: `same_strands`; lift `θ j`, `θ_strict`; isolation from `direction_once`), Δ₀ = `cornerDisc C ε j`.
Output: `exists_curl` gives Δ ⊆ Δ₀; `unchanged`+`disc_meets_arc` make the R supports disjoint; `no_u` and
`doubles_outside`/`old_sign`/`kink_neg` give "T has no downward vertical tangency" and "every crossing negative";
`poly_eq` gives `P_T = P_{\bar D}`; `writhe_eq` R times gives `w(T) = −w − R`; `F'` is a `SmoothRegularLoop`
for the transverse lift. Nothing more is needed from this row.

## 4. Reuse of the rounding construction and of the accepted moves
- Vocabulary: `SmoothRegularLoop`, `Carried` (→ `RecordCarried`), `SmoothRegularLoop.doublePoints`, `IsLiftOn`,
  `ClosedC1Curve.rot`, `normalize`, `det`, `planeDot`, `euclideanLength`, `IsDisc`, `RI`/`RIData`, `P`.
- Rounding proof module (Rounding.lean §8 Unit P): `smoothTransition_strictMonoOn` (:603), `deriv_smoothTransition_pos`
  (:640), `iteratedDeriv_eq_zero_of_const_left/right` (:679/:686) — the collar blend `blend` uses the same profile
  `Real.smoothTransition` (printed sm-3:4105 "the transition profile of Lemma cf:lem-rounding"); constancy of `φ` on
  the half-lines gives exact equality of the blend with `f`/`g` outside the collar, so the infinite-order joins are
  free. Unit A's `dirOf` facts and `normalize_smul_dirOf` (:~700) serve Unit G.
- Accepted turn lifts: `rot_sub_rot_of_replace`, `glplus_increment_sub_invariant` (TurnLift.lean:505; the printed GL⁺
  path `A_t`, sm-3:4226-4238), `IsLiftOn.increment_eq`, `tw_shift`.
- Polygonal side: `RIData` (LinkMoves.lean:569) is exactly the printed monogon deletion (its docstring cites this row);
  `RIData.card_crossing`, `componentCount_eq` (LinkMoves.lean:943-950); the splice machinery of SM/Smoothing.lean
  (`SpliceModel`, §0' generic-shadow lemmas) is the template for Unit K.

## 5. The chain (Skeleton_A.lean §7; exact statements there) and unit split

| unit | leaves (sorried) | content | est. lines | wave |
|---|---|---|---|---|
| M model | `hasDerivAt_cModel/bModel`, `cModel_double` (3) | c'(t), b'(t); c(s)=c(t) ⇒ s=t ∨ {s,t}={−1,1} (sm-3:4219-4221). Proved already: endpoints, turn signs, det=−8, excess, vertical iff | 150 | 1 |
| F fit | `fitA_add/smul`, `det_fitA_pos`, `fitA_ray_minus/plus`, `yFit_bound`, `xFit_pos` (7) | sm-3:3977-4006 by substitution; `1−(qy)² = 4abcd/(bc+ad)²` | 250 | 1 |
| G chart | `det_vDir_u`, `planeDot_vDir_u`, `expansion`, `exists_chart`, `hasDerivAt_η/ξ`, `ξ_strictMonoOn/AntiOn`, `η_strictMonoOn`, `exists_cuts`, `cut_displacement`, `endpoint_tangent`, `exists_disc_in_chart`, `disc_isDisc`, `p_mem_interior_disc`, `tail_tangent_ne` (16) | sm-3:3959-3990; IVT cuts; the disc by compactness of the rest of the curve (misses p: embedded arc, no double point) | 900 | 1 |
| H collar | `blend_smooth`, `blend_eq_left/right`, `sep_of_deriv`, `deriv_blend_ge`, `blend_between`, `deriv_blend_le` (7) | sm-3:4080-4212, abstract in f, g, φ; pointwise `h' ≥ f' > 0`, `f ≤ h ≤ g`; mirrored collar | 400 | 1 |
| R replacement | `inserted_arc_props`, `exists_smooth_arc`, `exists_loop_of_arc`, `exists_smoothCurl` (4) | Φ∘c (sm-3:4033-4054); the C^∞ regular parametrisation on [s₁,s₂] with F's jets (collars through η∘F, model by a smooth monotone change of variable equal to η∘F near its ends); periodic extension; assembly of `SmoothCurl` with cuts small enough for the disc and the lift increment (uses `glplus_increment_sub_invariant`) | 1800 | 2 (after M,F,G,H) |
| T turning | `rot_shiftCurve`, `rot_sub_rot_of_window` (2) | `tw_shift` on `tangentLoop`; the accepted `rot_sub_rot_of_replace` with seam at s₁, ψ = id, tangents equal off the window (`deriv_eq_of_offClosedWindow` + endpoint continuity) | 250 | 1 |
| K kink | `exists_kinkLocation`, `exists_kinkInsertion` (2) | gap point off other edges (finitely many meeting points, Regular/tail_off for adjacent edges); the polygonal monogon: 3 new vertices in a small disc U about r, clockwise, later branch over; generic shadow, `RIData` (arcs, `ArcCover`, `MoveMatch`), crossing/visit correspondence, `visitCoord` order clauses, writhe. Splice-style (Smoothing.lean) | 3000 | 1-2 |
| C record | `cycBetween_ext_of_insert_pair`, `cycBetween_fract_gap`, `cycBetween_fract_pair`, `exists_carriedAssembly` (4) | cyclic-order extension by an inserted adjacent pair (rotations/reversals of `cycBetween`, repeats false); `RecordCarried F' D'` with τ' = old τ / fract q₁ / fract q₂ (fields from `SmoothCurl`, `KinkInsertion`, no_double) | 700 | 2 (after K's spec, R's spec — statements only) |
| A assembly leaves | `deriv_eq_of_offClosedWindow`, `doublePoints_diff_eq`, `one_neg_u_of`, `one_double_of` (4) | window/period bookkeeping on `SmoothCurl` fields (`Int.fract`, `eq_add_int`) | 400 | 1 |
| total | **49** | | ≈ 7850 | 2 waves, ~9 provers |

Proved in the skeleton (no sorry): Unit M algebra (8 lemmas), `fitA_u₀/v₀`, `IsLiftOn.mono`, `shiftCurve`,
`τ_offClosedWindow`, `F'_τ`, `F'_fract`, `ri_of`, `no_u_of` (case split window/off-window using `isolated`),
`curlWitness` (every field), `exists_curl_main`, `cf_lem_curl`. Statements of the packages `SmoothCurl` (24 fields),
`KinkLocation`, `KinkInsertion` (16 fields), `CarriedAssembly` are the interfaces between units: byte-identical for
all provers; a prover of `exists_smoothCurl` may add intermediate lemmas but not change a package field.

Dependency order of leaves: M, F, G, H, T, K, A-leaves independent (wave 1); R needs M, F, G, H (and T only for the
`increment` field via `glplus_increment_sub_invariant`, accepted); C needs only the package statements.

## 6. Accepted declarations used (grep-verified 2026-09-14 in work/lean)
SM/Rounding.lean:148 `SmoothRegularLoop`; :156 `toClosedC1Curve`; :162 `doublePoints`; :183 `Carried` (:189 `τ_eval`);
:205-222 `Carried.smoothSign/smoothWrithe`; :466 `CornerRounding.dirOf`; :603 `smoothTransition_strictMonoOn`; :640
`deriv_smoothTransition_pos`; :679/:686 `iteratedDeriv_eq_zero_of_const_left/right`; :2948 `roundedLoop`; :3008
`roundedWitness` (consumer's Round(L,D,ε)); RoundingWitness fields `junction_embedded`, `same_strands`, `θ_strict`,
`direction_once`, `disc_only_modification` (:231-336) — the consumer's site data.
SM/FrontSmooth.lean:144 `SmoothLoop` (`eq_add_int` :196, `deriv_eq_add_int` :216); :1001 `SmoothFront.Marking` (record-level precedent).
SM/TurningNumber.lean:226 `normalize`; :228 `euclideanLength_normalize`; :241 `ClosedC1Curve`; :264 `tangentLoop`; :274 `rot`;
:102 `DirectionLoop.shift`; :215 `tw_shift`.
SM/TurnLift.lean:40 `IsLiftOn`; :55 `increment_eq`; :355 `rot_sub_rot_of_replace`; :394 `tangentLoop_T_eq_of_eventuallyEq`;
:409 `GLPlusPath`; :505 `glplus_increment_sub_invariant`; :385 `normalize_smul_of_pos`.
SM/Polygon.lean:16 `det`; SM/EuclideanPlane.lean:27 `planeDot`, :29 `euclideanLength`.
SM/LinkDiagram.lean:83 `Shadow`; :251 `Crossing`; :256 `Visit`; :372 `crossingPoint`; :394 `Generic`; :404 `Pt`; :407 `eval`;
:490 `Diagram`; :552 `sign`; :577 `writhe`; :597/:600 `overVisit/underVisit`; :650 `switch` (consumer); :99 `seg`.
SM/LinkDiagramRecord.lean:78 `cycBetween` (:85-95 `not_cycBetween_self_*`); :181 `visitCoord`; :413 `twin` (:420 `twin_ne`).
SM/Traversal.lean:12 `TraversalPoint`; :17 `traversalKey`.
SM/LinkMoves.lean:100 `IsDisc`; :145 `Shadow.Arc`; :198 `IsArc`; :208 `ArcCover`; :316 `OutsideMatch`; :342 `Clean`;
:356 `MoveMatch`; :569 `RIData`; :590 `RI`; :778 `LinkEquiv.of_RI`; :943 `RIData.card_crossing`.
SM/LocalPolynomial.lean:22 `P`; SM/PolynomialBlock.lean:605 `P_reidemeister_I`; :1096 `RecordPolynomialData` (not needed).
Mathlib (pin 85e3a25e): `Real.smoothTransition` (+ `.zero_of_nonpos`, `.one_of_one_le`, `.contDiff`), `Int.fract`,
`intermediate_value_Icc`, `IsCompact.exists_forall_le`, `HasDerivAt.scomp`.

## 7. Fidelity risks (to cite in the review of this row and of cf:thm-carrierfloor)
FR-C1 (record-level carrying): the output diagram is `RecordCarried F' D'`, not `Carried`; the polygon `D'`'s crossing
*points* are unrelated to `F'`'s double points (only the record — occurrences, pairing, cyclic order, signs — is
shared). Justified by D2; coherent with `Marking`; strictly weaker than `Carried` as an output, which a reviewer of
the rounding row's FR-R1 should note. The input accepts `Carried` through `toRecordCarried`.
FR-C2 (disc quantifier): `exists_curl` strengthens the printed ∃Δ to "inside any Δ₀"; the printed form is `exists_curl'`.
FR-C3 (modification support): "modified inside Δ" is read as equality of the *parametrised* curves off a window; the
proof must reparametrise the replacement on `[s₁, s₂]` with `F`'s jets (Unit R). The printed proof produces a C^∞
curve as a set/graph; the parametrisation is our addition (sm-3:4056-4079 leaves it implicit).
FR-C4 (polynomial): `P_{F'} = P_F` is `P D' = P D` via the polygonal RI; the printed proof's route (RI to F°, then
rp:record-polynomial) is not reproduced; both use lp:core's RI invariance (`P_reidemeister_I`).
FR-C5 (hypotheses): `isolated` as uniqueness on the arc (D7); "turns strictly positively" as `StrictMonoOn` of a lift
(the proof's chart uses only this); `β − α < 1` (an arc is shorter than the circle; forced by embeddedness anyway).
FR-C6 (exports beyond print): `old_in_disc`, `disc_meets_arc`, the window `[s₁, s₂]`, `old : Crossing ≃ …`,
`old_point`, the smooth-sign corollaries; all supplied by the proof and read by the consumer.
FR-C7 (Unit K size): the polygonal kink insertion is a splice construction comparable to a third of Smoothing.lean;
its statement `KinkInsertion` is fixed here so that the smooth side does not depend on its internals.
FR-C8 (check environment): compiled against a locally built `SM.Rounding` olean (identical source); re-check with plain
`lake env lean` once work/lean builds the ported module.
