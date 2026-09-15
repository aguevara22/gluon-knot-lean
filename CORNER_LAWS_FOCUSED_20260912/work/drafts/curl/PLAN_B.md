# PLAN B — cf:lem-curl (exact negative-curl replacement): literal smooth reading

Row 98, reference/SM/sm-3-statesum.tex:3870-3889 (statement; the lemma's proof 3892-4280; the consumer
cf:thm-carrierfloor 4282-4330 uses it at 4438-4455).  Architect B, 2026-09-14.  Emphasis: LITERAL fidelity
to the printed smooth statement (the curl as an explicit smooth arc replacement with its lift and swept angle,
exact rotation/writhe changes, the disc package), candid about the analytic cost and about where the polygonal
reading FR-R1 carries the diagram part.

Deliverables (this directory; nothing written under work/lean):
- `Statements_B.lean` (519 lines): the fixed statement.  `lake env lean` → 0 errors, one `sorry` (the row
  `SM.cf_lem_curl : CurlData`, line 514).  `#print axioms SM.CurlData.of_exists` = [propext, Classical.choice,
  Quot.sound, SM.lp_lm] (the literature interface enters through `P`, as for every polynomial statement).
- `Skeleton_B.lean` (1206 lines): statement verbatim (§0-§4) + construction (§5) + chain (§6) + assembly (§7,
  PROVED) + row (§8, PROVED from the chain).  0 errors, **47 leaf `sorry`** (all `:= by sorry` leaves; no sorry in
  glue).  `#print axioms SM.cf_lem_curl` = [propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm].
- Both files carry §0 = byte-identical copy of SM/Rounding.lean:70-222 (`PolygonDiagram`, `eucDist`, `cornerDisc`,
  `SmoothRegularLoop`, `Carried`), because `SM/Rounding.olean` is not built yet (no `.olean` at 2026-09-14) and
  drafts may not `lake build`.  PORT: delete §0, add `import SM.Rounding` (the copy equals the accepted text).

## 1. Clause map (tex line → Lean field)

| tex | printed clause | Lean (Statements_B.lean) |
|---|---|---|
| 3871-3872 | "rot as in lem:rot for polygons and cf:def-turning for closed C¹ curves" | `rot_eq` uses `ClosedC1Curve.rot` of `SmoothRegularLoop.toClosedC1Curve` on both sides (no polygon here) |
| 3873-3875 | "F a connected C^∞ immersed circle — one component, finitely many transverse double points, no triple points — given with an oriented diagram" | `F : SmoothRegularLoop`, `X : Diagram`, `CurlSite.carried : Carried F X` (FR-R1; `Carried.one`, `doubles`+`τ_inj` = no triple points, `transverse`) |
| 3875-3876 | "p a point of F at which the tangent points in a fixed direction u" | `t₀`, `u`, `u_unit`, `tangent_at : normalize (deriv F.γ t₀) = u`; `CurlSite.p := F.γ t₀` |
| 3876 | "isolated among such points" | `isolated` |
| 3876-3878 | "lying in an embedded arc of F that contains no double point and along which the tangent turns strictly positively" | `α β`, `α_lt`, `lt_β`, `arc_short`, `arc_simple`, `turns_pos : 0 < det γ' γ''` on `[α, β]` |
| 3878-3879 | "F may be modified inside a disc Δ meeting the rest of the diagram only in that arc" | chart disc `Δ₀` (site: `Δ₀_disc`, `p_mem`, `Δ₀_curve`, `arc0`, `Δ₀_cover`, `Δ₀_clean`, `Δ₀_no_crossing`, `compat`; FR-C1) and modification disc `Δ = curlDisc p r` (witness: `r`, `r_pos`, `r_le`, `disc_isDisc`, `p_in_disc`, `disc_sub`, `disc_meets_arc`); the modification: cuts `sm sp`, `old_in_disc`, `new_in_disc`, `unchanged`, `unchanged_deriv` |
| 3881-3883 (i) | "is again such an oriented diagram" | `F'`, `X'`, `carried' : Carried F' X'` |
| (i) | "satisfies P_{F'} = P_F" | `P_eq : P X' = P X` (from `ri : RIData Δ₀ X X'` via accepted `P_reidemeister_I`) |
| (i) | "same double points outside Δ, with the same signs" | `doubles_outside`, `points_outside`, `signs_outside` (through the outer-crossing bijection `ri.out.ψ`) |
| 3884-3885 (ii) | "no point of Δ at which the tangent equals u, and exactly one at which it equals −u" | `no_tangent_u`, `one_tangent_neg_u` (`∃!` parameter in `[0,1)`) |
| 3886 (iii) | "exactly one double point inside Δ, and it is negative" | `double_in_disc_iff`, `kink_point`, `kink_negative : carried'.smoothSign ri.kink = -1` |
| 3887 (iv) | "rot(F') = rot(F) − 1 and w(F') = w(F) − 1" | `rot_eq`, `writhe_eq` (+ proved corollaries `writhe_polygonal`, `kink_sign_polygonal`, `ri_rel : RI X X'`) |
| 3912-3914, 4232-4251 | mechanism: "its compatible lift increment is the old one minus 2π", "the old central arc … lifted sweep θ(s₊)−θ(s₋) lying in (0,π)" | `θ`, `θ_lift`, `θ_strictMono`, `sweep_old_pos`, `sweep_old_lt_pi`, `θ'`, `θ'_lift`, `lift_init`, `sweep_new` (exported; FR-C4) |

Bundle `CurlData : Prop` (line 445): `exists_curl` (the theorem: `∀ F X (S : CurlSite F X) ρ, 0 < ρ →
Nonempty (CurlWitness S ρ)`), `modified_inside_disc`, `i`, `ii`, `iii`, `iv` — projections of `CurlWitness`
(`CurlData.of_exists`, proved, line 494).  Main declaration `SM.cf_lem_curl : CurlData` (cf:* convention; not a
checker fixed-name row).

## 2. Model decisions

2.1 **Input class.** `F : SmoothRegularLoop` is exactly cf:lem-rounding's output class (the file header of
Rounding.lean §3 already names cf:lem-curl as its consumer); the diagram is `X : Diagram` with `Carried F X`
(FR-R1).  "Finitely many transverse double points, no triple points" are consequences of `Carried` (`doubles`,
`τ_inj`, `transverse`), so they are not repeated as hypotheses.

2.2 **The point, the arc, the turning.** Parameter-level: `t₀`, `[α, β]` with `β − α < 1`.  "Embedded arc
containing no double point" is the single clause `arc_simple : ∀ t ∈ [α,β], ∀ s, F.γ s = F.γ t → ∃ n : ℤ, s = t + n`
(injective on the arc AND no other passage of `F` through it).  "Turns strictly positively" is the printed
`det(γ', γ'') > 0` (sm-3:3900), parametrisation-free; the strictly increasing lift of the proof (3959-3966) is
derived (Unit C).  `isolated` is redundant given `turns_pos` but printed, so kept (harmless, as PREREVIEW §3).

2.3 **The disc: two discs (FR-C1, the main decision).**  In the smooth world "a disc Δ meeting the rest of the
diagram only in that arc" exists automatically (compactness).  Under FR-R1 the diagram has a polygonal half `X`
whose strands are unrelated to `F` away from the double points, and `Carried.τ_eval` forces the OUTPUT polygon
`X'` to pass through the new double point `q ∈ Δ`.  So the polygonal half must also meet the disc in one
crossing-free arc: the site carries a chart disc `Δ₀` (`IsDisc`, `p ∈ interior Δ₀`, `Δ₀_curve`,
`Δ₀_cover : X.Γ.ArcCover Δ₀ {arc0}`, `Δ₀_clean : Clean Δ₀ X`, `Δ₀_no_crossing`, `compat` = the arc `arc0` sits in
the same gap of the cyclic order as `p`).  The witness's `Δ = curlDisc p r ⊆ Δ₀` has preassigned radius `r ≤ ρ`
(sm-3:4024-4028 "the disc is fixed first and the cuts afterwards"), which is what the consumer needs
(4443-4445).  Clauses (ii), (iii), "outside Δ" are about `Δ`; the polygonal Reidemeister-I site is `Δ₀`.
Consumer fit: `Δ₀ := ` the rounding disc `D_i` (RoundingWitness (e): `disc_only_modification`,
`junction_embedded`, `disc_meets_out/in` give `Δ₀_curve`/`Δ₀_cover`/`Δ₀_clean`; `disc_no_double` gives
`Δ₀_no_crossing`; `same_strands` + the junction position give `compat`), and after one insertion the other
sites keep their hypotheses (`unchanged`, `disc_sub`, disjoint `D_i`).
Why not the alternatives: (a) `RI X X'` in a small disc about a point of X's arc puts the kink away from `q` —
`τ_eval` fails; (b) rerouting `X`'s arc to `q` needs planar topology; (c) any polygonal `X'` carried by `F'`
without an RI to `X` gives no route to `P X' = P X`.  The hypothesis is the honest price of FR-R1 and is exactly
what the disc package of cf:lem-rounding (e) was printed for ("its consumer asks for a disc meeting the diagram in
one embedded arc", sm-3:3697-3699).

2.4 **"Modified inside Δ".** Parametrised: `F' = F` with velocity on `[s₊, s₋ + 1]` (one period minus the open
cut), the removed and inserted sub-arcs inside `Δ`.  Stronger than the set statement, and what the consumer's
"disjoint supports … leave one another intact" reads.

2.5 **(i) polynomial and record.**  `P X' = P X` is stated as a field and proved in the assembly from the
exported `ri : RIData Δ₀ X X'` by the accepted `P_reidemeister_I` (the printed route 4252-4277 uses lp:core RI
invariance plus rp:record-polynomial; here the RI site already relates `X` and `X'`, so the record-isomorphism
step is absorbed).  "Same double points outside Δ, with the same signs" is stated both as sets
(`doubles_outside`) and through the accepted outer-crossing bijection (`points_outside`, `signs_outside`).

2.6 **(ii), (iii), (iv).**  Literal.  Signs are `Carried.smoothSign` = `sgn det(over velocity, under velocity)`
(def:positive-lift) — the printed "later branch over the earlier one" is realised by the kink insertion
(`over_second`) and checked by `Carried.sign_eq`.  `rot` is cf:def-turning's; `writhe` is `Carried.smoothWrithe`
(= `X'.writhe` by the accepted `smoothWrithe_eq`).

## 3. Reuse of the rounding lane and of accepted material

Reused as is: `SmoothRegularLoop`, `Carried` (+ `smoothSign`, `smoothWrithe`, `smoothSign_eq`, `smoothWrithe_eq`),
`eucDist`, `doublePoints` (Rounding.lean:126-222); `Real.smoothTransition` as the collar profile (the printed
"transition profile of Lemma cf:lem-rounding", sm-3:4105; PREREVIEW R-g); the accepted arc-replacement lemma
`rot_sub_rot_of_replace` (TurnLift.lean:355) for (iv) after a seam shift (`tw_shift`, TurningNumber.lean:215);
`IsLiftOn` and its increment lemmas (TurnLift.lean:40-76); the disc vocabulary `IsDisc`, `Arc`, `IsArc`,
`ArcCover`, `Clean`, `OutsideMatch`, `MoveMatch`, `RIData`, `RI` (LinkMoves.lean:100-590) and
`P_reidemeister_I` (PolynomialBlock.lean:605).  Once `SM.Rounding` is built, Unit P of the rounding chain
(`smoothTransition_symm/strictMonoOn`, `deriv_smoothTransition_pos`, `iteratedDeriv_eq_zero_of_const_left/right`,
Rounding.lean:595-690) serves the collar lemmas; `cornerDisc_isDisc`/`mem_interior_cornerDisc` (Unit E) are the
same proofs as `isDisc_curlDisc`/`mem_interior_curlDisc`.  Patterns to copy for Unit K: SM/Smoothing.lean §5
(1619, one strand through a disc), §6d (3685, cleanness), §6e (4313, the outside match), and
SM/MarkedProducts.lean §R1 (2713, a clean disc around an interior edge point).
New geometry: the positive-turn chart, the cuts, the rational model and its affine fit, the collars, the glued
loop, and the polygonal kink insertion.

## 4. The chain (Skeleton_B.lean §5-§7; exact statements there)

§5 definitions (`namespace Curl`): `ξ η` (chart coordinates), `bModel cModel` (sm-3:3893-3896), `v₀ u₀ qFit`,
`Hfit xFit yFit` (4001-4006), `Amap` (4007), `Φmap`, `insArc` (4020-4026, 4044), `collar` (4097-4105).
§6 leaves (47 `sorry`), by unit:
- **D** (3): `isDisc_curlDisc`, `mem_interior_curlDisc`, `exists_curlDisc_subset`.
- **M** (11, pure algebra of the model): `model_endpoints`, `deriv_bModel`, `deriv_cModel`,
  `deriv_model_endpoints` (`b'(±2) = (3/11) c'(±2)`), `det_bModel` (= 18/11), `det_cModel` (= −2(1+3t²)),
  `model_vertical_iff`, `deriv_model_zero`, `cModel_double` (`c s = c t, s ≠ t ⇒ {s,t} = {−1,1}`),
  `cModel_doublePoint`, `det_cModel_branches` (= −8), `cModel_excess` (4 − t²).
- **A** (9, algebra of the fit): `Amap_u₀`, `Amap_v₀`, `Amap_add`, `Amap_smul`, `Amap_ray_minus`
  (`A(q v₀ + u₀) = (H/a) T₋`), `Amap_ray_plus`, `det_Amap` (= x), `xFit_pos`, `one_sub_qy_sq`
  (`1 − (qy)² = 4abcd/(bc+ad)²`), `orderedRay_condition` (both outer determinants computed).
- **C** (3): `det_normalize_deriv` (`det(T,T') = det(γ',γ'')/|γ'|²`), `exists_smooth_lift` (a `C^∞` lift with
  `θ' = det(T,T')`), `exists_cuts : Nonempty (Cuts S ρ)` — the package `Cuts` (radius `r ≤ ρ` with
  `Δ ⊆ Δ₀`, chart interval `(a₁,b₁) ⊂ (α,β)` with strictly increasing lift `|θ − θ t₀| < π/2`, `disc_meets`,
  cuts with `ξ sm = ξ sp`, chord `ℓ u`, `old_in_disc`, `central_above`, `tails_below`, `η_strictMono`, the
  tangent coefficients `a b c d > 0`).
- **I** (1): `exists_insertedArc : Nonempty (InsertedArc S K)` — endpoints, positive-scale tangent rays,
  regular, `in_disc`, one double point at `t = ±1` with `det < 0`, `no_u`, `neg_u_iff` (only `t = 0`),
  `excess` (`ξ = ξ(s₋) + (ℓx/12)(4 − t²)`), compatible lift `θc` with increment old − 2π.
- **G1** (7, the collar as a graph): `collar_contDiff`, `collar_eq_left/right`, `deriv_collar_pos`
  (`h' ≥ f' > 0`, no smallness), `deriv_collar_neg` (mirror at `p₊`), `collar_between` (`f ≤ h ≤ g`),
  `graph_lift_increment` (a positive-slope graph has tangents `≠ ±u`, with a lift).
- **G2** (1): `exists_gluedLoop : ∃ G : GluedLoop S K, G.ins = I` — the `SmoothRegularLoop F'` equal to `F`
  outside the cut, the inserted arc in the middle up to a `C^∞` increasing `ψ`, collars of widths `lam lam'`,
  `new_in_disc`, the double point `s₁ < s₂` (negative, interior to `Δ`, unique on the cut), `cut_off_rest`,
  (ii) on the cut, the compatible lift `θ'` with `sweep_new`.
- **K** (4, polygonal): `exists_kinkInsertion : Nonempty (KinkInsertion X U a q d₁ d₂)` (`X'`, `RIData U X X'`,
  kink at `q`, first/second strands parallel to `d₁ d₂`, over = second, the induced occurrence map `φV` with
  `φV_over/under/surj`, `order_old`, `order_kink`, `order_kink_pair`), `RIData.crossingPoint_ψ`,
  `RIData.sign_ψ`, `RIData.writhe_eq` (`D'.writhe = D.writhe + sign kink`).
- **R** (1): `exists_carriedKink : Nonempty (CarriedKink S K G Kk)` — `Carried G.F' Kk.X'` with `signs_outside`,
  `kink_negative`, `writhe_eq`.
- **T** (1): `rot_sub_of_cut` (seam shift + `rot_sub_rot_of_replace`, `ψ = id`).
- **X** (4, global clauses from the pieces): `doubles_outside_of_pieces`, `double_in_disc_iff_of_pieces`,
  `no_tangent_u_of_pieces`, `one_tangent_neg_u_of_pieces`.
§7 assembly (PROVED): `exists_kink_of_glued` (hypotheses of Unit K from the site and `G`), `IsLiftOn.mono`,
`witness : CurlWitness S ρ` (every field: projections, `P_reidemeister_I ⟨Δ₀, Or.inr ⟨ri⟩⟩`, the `−1` arithmetic
of (iv) from `rot_sub_of_cut` + `sweep_new`, `sweep_old_lt_pi` from `θ_bound`), `exists_witness`.
§8 `cf_lem_curl := CurlData.of_exists …` (PROVED).

## 5. Unit split for parallel provers (statements byte-identical; fill your unit's sorries)

| unit | leaves | est. lines | depends on | notes |
|---|---|---|---|---|
| D discs | 3 | 150 | Mathlib | copy of rounding Unit E's disc lemmas (Euclidean via `planeComplex`) |
| M model | 11 | 450 | Mathlib | `deriv` of polynomial curves in `ℝ × ℝ` (`HasDerivAt.prodMk`), `nlinarith`/`ring` |
| A fit | 9 | 350 | Mathlib | `field_simp; ring` identities; positivity |
| C chart + cuts | 3 | 900 | D | lift via `∫ det(T,T')` + ODE uniqueness on the circle; IVT for the cuts; monotonicity of `ξ`, `η` |
| I inserted arc | 1 | 700 | M, A, C | endpoint/ray identities from A; double points from M; `excess`; the lift of `Φ∘c` via `GLPlusPath`-free direct computation or `glplus_increment_sub_invariant` (TurnLift.lean:505) |
| G1 collars | 7 | 500 | Mathlib (`smoothTransition`) | derivative formula of `collar`; sign bookkeeping as printed (4110-4200) |
| G2 glued loop | 1 | 2000-2500 | C, I, G1 | THE analytic core: graph representation of both arcs over `η` (inverse function, `ContDiffAt.to_localInverse` or hand-built), collars, a `C^∞` reparametrisation of the glued arc onto `[s₋, s₊]` with flat jets at the ends, then the double-point and tangent bookkeeping |
| K kink insertion | 4 | 2500-3500 | LinkMoves | explicit polygonal routing inside the convex disc (radial spokes to a small circle about `q`, chord paths, two diameters through `q`), `Shadow.Generic` via `single_generic_of`, `Clean`, `ArcCover`, `MoveMatch` bookkeeping (pattern: Smoothing.lean §5-§6e), the occurrence map and orders |
| R record | 1 | 600 | G2, K | `τ'` = old `τ` on old occurrences (F' = F there; crossings outside Δ₀), `s₁ s₂` for the kink; `order` from `compat` + `order_*`; `sign_eq` from `dir_first/second`, `over_second`, `det_neg` |
| T rotation | 1 | 150 | TurnLift | shift both loops by `s₋`, apply `rot_sub_rot_of_replace` with `lam = mu = s₊ − s₋`, `ψ = id`, `tw_shift` |
| X global | 4 | 500 | C, G2 | periodicity/`fract` bookkeeping; tails via `θ_bound` |
| total | 47 | ≈ 9000-10000 | | 3 waves: {D, M, A, G1, T} → {C, K} → {I, G2} → {R, X}; ~2.5-3× the rounding row |

Check per unit: `cd work/lean && lake env lean ../drafts/curl/U_<unit>.lean` (copy of Skeleton_B.lean).

## 6. Accepted declarations used (grep-verified 2026-09-14 in work/lean)

SM/Rounding.lean (copied as §0 until built): :80 `PolygonDiagram`; :126 `eucDist`; :148 `SmoothRegularLoop`
(+`toClosedC1Curve`); :162 `SmoothRegularLoop.doublePoints`; :183 `Carried`; :210 `smoothSign`; :214
`smoothWrithe`; :216 `smoothSign_eq`; :218 `smoothWrithe_eq`; :595-690 Unit P profile lemmas (for G1 later).
SM/FrontSmooth.lean:144 `SmoothLoop`; :227 `SmoothLoop.toClosedC1Curve`.
SM/TurningNumber.lean:119 `IsLift`; :202 `tw_eq_of_isSeamLift`; :215 `tw_shift`; :226 `normalize`; :241
`ClosedC1Curve`; :264 `tangentLoop`; :274 `rot`.
SM/TurnLift.lean:40 `IsLiftOn`; :55 `IsLiftOn.increment_eq`; :68 `increment_eq_zero_of_const`; :76
`IsLift.comp_isLiftOn`; :83 `exists_lift_of_unit`; :355 `rot_sub_rot_of_replace`; :380 `euclideanLength_smul`;
:385 `normalize_smul_of_pos`; :409 `GLPlusPath`; :505 `glplus_increment_sub_invariant`.
SM/LinkDiagram.lean:61 `PolyComp`; :251 `Crossing`; :256 `Visit`; :372 `crossingPoint`; :394 `Shadow.Generic`;
:490 `Diagram`; :552 `sign`; :577 `writhe`; :597 `overVisit`; :600 `underVisit`; :1413 `crossingParam`; :1435
`visitPt`.  SM/LinkPositiveLift.lean:160 `Shadow.single_generic_of` (Unit K).
SM/LinkDiagramRecord.lean:78 `cycBetween`; :181 `visitCoord`; :413 `twin`.  SM/Traversal.lean:17 `traversalKey`;
:73 `traversalBetween`.
SM/LinkMoves.lean:100 `IsDisc`; :104 `isDisc_closedBall`; :145 `Shadow.Arc` (+ `Inner`, `Mem`, `Before`); :198
`IsArc`; :208 `ArcCover`; :250 `OuterCrossing`; :275 `outerOverPt`; :316 `OutsideMatch`; :342 `Clean`; :348
`LocalFrame`; :356 `MoveMatch`; :569 `RIData`; :590 `RI`; :868 `Clean.crossingPoint_not_mem_frontier`; :892
`card_inner_eq_one`; :943 `RIData.card_crossing`.
SM/LocalPolynomial.lean:22 `P`.  SM/PolynomialBlock.lean:605 `P_reidemeister_I`.
SM/Polygon.lean:16 `det`.  SM/EuclideanPlane.lean:9 `planeComplex`; :27 `planeDot`; :29 `euclideanLength`.
Mathlib (pin 85e3a25e): `Real.smoothTransition` (SmoothTransition.lean:146; `.zero` :171, `.one` :175,
`.contDiff` :206, `.monotone` :223, `.zero_of_nonpos` :168, `.one_of_one_le` :161); `expNegInvGlue` :39.

## 7. Fidelity risks (to cite in the review of this row and of cf:thm-carrierfloor)

FR-C1 (major; the polygonal half of the disc).  The printed input needs only the smooth curve; under FR-R1 the
site additionally assumes a chart disc `Δ₀` in which the carried polygon `X` is one crossing-free arc in the same
gap as `p` (`Δ₀_cover`, `Δ₀_clean`, `Δ₀_no_crossing`, `compat`), and the Reidemeister-I site is `Δ₀`, not the
modification disc `Δ ⊆ Δ₀` of (ii)-(iii).  Forced by `Carried.τ_eval` (the output polygon must pass through the
new double point).  The consumer has it from cf:lem-rounding (e); a reviewer should check that no other consumer
applies cf:lem-curl to a bare smooth curve.
FR-C2 (parametrised modification).  `F' = F` as parametrised curves outside the open cut `(s₋, s₊)`, with the
velocity; the printed statement is set-level ("modified inside Δ").  Stronger; it is what the proof does
("the rest of the curve is F itself") and what the consumer's disjoint-support argument reads.
FR-C3 (the disc is round and preassigned).  Printed: some disc `Δ`; here `Δ = curlDisc p r` (closed Euclidean)
with `r ≤ ρ` for every `ρ > 0` (sm-3:4024-4028).  Stronger, needed at 4443-4445.  `Δ₀` may be any accepted
`IsDisc` (round in the consumer).
FR-C4 (exports beyond the printed clauses).  The tangent lifts `θ θ'` of the removed/inserted sub-arcs with
`lift_init`, `sweep_old ∈ (0, π)`, `sweep_new = old − 2π`; `unchanged_deriv`; `kink_point`; the bijections
`points_outside`/`signs_outside`; `disc_isDisc`, `p_in_disc`.  All supplied by the construction; the lift fields
are the printed mechanism of (iv) (3912-3914, 4232-4251) and are what a transverse-front consumer reads.
FR-C5 (turning hypothesis).  "Turns strictly positively" is rendered by `det(γ', γ'') > 0` on the closed arc
(the model's own criterion, 3900).  A reviewer preferring "strictly increasing lift" gets it from Unit C
(`exists_smooth_lift`, `θ' = det(T,T') > 0`).  `isolated` is redundant under this reading (kept as printed).
FR-C6 (compat through `Int.fract t₀`).  The site parameter `t₀` is any real; `compat` compares
`Int.fract t₀` with the occurrence parameters `τ ∈ [0,1)`.  For the consumer `t₀` lies inside a junction
interval `[a j, b j] ⊂ [0,1]`, so `fract` is the identity there.
FR-C7 (`(ii)` counted on parameters).  "Exactly one point of Δ at which the tangent equals −u" is `∃!` over the
fundamental period `[0,1)`; since `F'` is injective on the cut except at the kink (which has no `−u` tangent),
this is the same as the point count.
FR-C8 (cost, candidly).  The smooth side (Units C, I, G1, G2, X ≈ 4500-5000 lines) is the printed proof:
chart/inverse-function representation of both arcs as graphs, the affine fit, the collars, a `C^∞`
reparametrisation of the glued arc onto `[s₋, s₊]`, and the double-point bookkeeping.  The polygonal side (Units
K, R ≈ 3000-4000 lines) has no printed counterpart: it is the price of FR-R1 (a polygonal kink through a
prescribed point with prescribed strand directions inside a convex disc, with the accepted `RIData`/`MoveMatch`
bookkeeping, following Smoothing.lean §5-§6e).  Total ≈ 9000-10000 lines, ~2.5-3× cf:lem-rounding.  The row
cannot be closed before `SM/Rounding.olean` exists (import) — until then the drafts carry the §0 copy.
FR-C9 (chain hygiene).  Package structures (`Cuts`, `InsertedArc`, `GluedLoop`, `KinkInsertion`, `CarriedKink`)
bundle the printed paragraph conclusions; their existence leaves are the only place where the printed
construction is not yet a definition (the cuts, the collar widths, the reparametrisation `ψ`, the polygon `X'`).
`KinkInsertion` carries `order_old/order_kink/order_kink_pair` because the accepted `RIData`/`OutsideMatch`
does not state cyclic-order preservation of the outer occurrences; the explicit construction proves it.
Numeric sanity (not run here; recommended for Unit I/G2 as for the rounding lane): the printed model values
`b(±2) = c(±2) = (3, ∓6)`, `det(c'(1), c'(−1)) = −8`, `1 − (qy)² = 4abcd/(bc+ad)²` are checked symbolically in
Units M/A.
