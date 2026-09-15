# PLAN FINAL — cf:lem-rounding (rounding): judge's decision, fixed statement, skeleton

Row: cf:lem-rounding, reference/SM/sm-3-statesum.tex:3644-3700 (statement), 3701-3869 (proof).
Judge (architect subagent), 2026-09-14. Inputs: PLAN_A.md / Rounding_statement_A.lean / Skeleton_A.lean
(Architect A, model-first) and PLAN_B.md / Rounding_statement_B.lean / Skeleton_B.lean (Architect B, proof-first).
All four candidate files re-checked with `cd work/lean && lake env lean <file>`: 0 errors each (statements 1 sorry
each; Skeleton_A 79 sorry tokens, Skeleton_B 96).

Deliverables (this directory):
- `Rounding_statement_FINAL.lean` (442 lines) — the fixed statement. 0 errors, 0 warnings other than the single
  `sorry` (the row `SM.cf_lem_rounding : RoundingData`). `#print axioms` of `RoundingData`, `RoundingWitness`,
  `Carried.smoothWrithe_eq`, `PolygonDiagram.toDiagram_ofDiagram`, `RoundingData.of_diagram`:
  [propext, Classical.choice, Quot.sound].
- `Skeleton_FINAL.lean` (1297 lines) — statement text verbatim (§1-6) + construction (§7) + chain (§8) +
  assembly (§9, PROVED) + row (§10, PROVED from the chain). 0 errors, 0 non-sorry warnings, **52 `sorry`**
  (all leaf lemmas; 28 of the 80 leaves of the merged chain were proved here).
  `#print axioms SM.cf_lem_rounding` = [propext, sorryAx, Classical.choice, Quot.sound].
Nothing written under work/lean.

## 0. Verdict: **A wins** (model, statement shape, `Carried`), with five grafts from B

| criterion | A | B | decision |
|---|---|---|---|
| clearance / witness form | existential (`∃ ε₀ > 0, ∀ ε ∈ (0,ε₀), Nonempty (RoundingWitness C D ε)`) — the printed sentence | named construction in the statement (`clearance L`, `roundedCurve L ε`, 25 statement-level defs); printed ∃-form a corollary | **A**: printed form; the construction stays in the proof module (still a *named def*, `CornerRounding.roundedWitness`, which cf:thm-carrierfloor (A) can cite); a definitional slip in the construction is then caught by the proof, not fixed into the statement. B's `clearance` also deviates from the printed ε₀(L) (sup-metric `infDist`, cap `1`) — invisible under A's form |
| input | `PolygonDiagram C` (3 fields = accepted `Diagram` on `Shadow.single C`, `toDiagram` an abbrev) | `D : Diagram`, `D.Γ = Shadow.single ⟨n,hn,L⟩` + `subst` in every field | **A** + graft: `PolygonDiagram.ofDiagram`, `toDiagram_ofDiagram` and `RoundingData.of_diagram` give the accepted-`Diagram` entry point without transport in the clause fields |
| smooth class | `SmoothLoop` + separate `regular` | `SmoothRegularLoop extends SmoothLoop` | **B**: one named class for "C^∞ regular closed plane curve" (also cf:lem-curl's input); `rot` via the accepted bridge |
| carried record | `Carried γ X`: τ, pairing by `twin`, transversality, **cyclic** order (`cycBetween`/`visitCoord`), over/under = X's via sign consistency | `Carries γ D`: `par_dir` (velocities positive multiples of D's edge directions), **linear** order `visitCoord < ↔ par <` | **A**: B's `par_dir` and linear order are rounding-specific (a general immersed circle carrying a PL model has neither), so B's record cannot serve cf:lem-curl; A's is the `Marking`-shaped general notion (FR-1). Strand direction is a clause-(c) fact of the witness (A: `same_strand_dir`) |
| (a) | set form outside discs + parametric straight parts | same content | equal |
| (b) | lift `θ j` C^∞, `IsLiftOn`, const on half-lines, start/end, increment, strict mono/anti, ∃ per angle + `InjOn T`, `deriv θ ≠ 0` on the open arc, flatness of θ | + explicit "no more" (`θ ∈ uIcc`), ∃! per angle, **curve-level flatness** (`iteratedDeriv m γ = 0`, m ≥ 2) | **A + grafts**: `θ_range`, `θ_unique` (∃!), `flat_ends_curve` |
| (c) | double points = crossing points; occurrence on the straight *parameter* interval of its edge, velocity a positive multiple of the edge; signs; writhe | `γ (par v) ∈ seg` (automatic) + `par_dir`, quantified over every record | **A** (stronger "same strands") |
| (d) | `Lε.toClosedC1Curve.rot = rotationNumber C.P` | `∀ c : ClosedC1Curve, c.γ = γ → c.rot = rotationNumber L` | **A** (direct) |
| (e) | IsDisc, disjoint, centre, off non-incident edges, no double point, exact ε-sub-segments, contains the junction, straight parts off discs | + junction is **all** of the curve in the disc, junction **embedded** | **A + grafts**: `disc_only_modification`, `junction_embedded` (the consumer's "one embedded arc") |
| chain lemma probed false | `tangentField_periodic` stated with NO hypothesis: false for non-regular polygons (e.g. `P0=P1=(0,0), P2=(1,0)`: turns 0,0,π ⇒ rotationNumber = ½ ⇒ Θ(t+1) = Θ(t)+π) — **fixed** (`hreg : Regular C.P`) and proved | `roundDisc_inter_edge_in`: hypothesis `ε ≤ edgeLen C.P (k - 1)` with ℕ-subtraction names edge 0 at k = 0 while the conclusion is about edge n−1: false for a polygon with |δ_{n−1}| < ε ≤ |δ_0| (harmless at its only instantiation) | both single, local; neither affects the statement |
| effort | 83 leaves, ≈4150 lines est. | ≈150 lemmas, ≈4000 lines est. | comparable; FINAL: 52 leaves remain (≈3300 lines est.) |

Numeric probe of the shared analytic core (`juncArc_mem_disc` / B's J7, the riskiest lemma of both chains) with the
actual `smoothTransition` profile, ϑ ∈ {0.3, 1, 2, 2.9, 3.1, −1.5, −3}: max distance to the corner = ε exactly and only
at the two endpoints, interior max < ε, endpoint error 0, bisector-frame bounds |x_w| ≤ ε cos(ϑ/2), |x_z| ≤ ε|sin(ϑ/2)|
hold, ℓ ≤ 2ε. Consistent with the printed triangle argument (sm-3:3772-3818) and B's frame estimate.

## 1. Model decision (Q1-Q5) with the fidelity argument per clause

### Input — "L a closed polygon … D an oriented diagram whose underlying plane curve is L"
`C : PolyComp` (LinkDiagram.lean:61: def:polygon object, `3 ≤ k`, `L = C.P`, corners `C.P i`, edges `edge C.P i`,
Polygon.lean:49). `D : PolygonDiagram C` = `generic : (Shadow.single C).Generic`, `overStrand`, `over_mem`;
`D.toDiagram : Diagram := ⟨Shadow.single C, …⟩` is an `abbrev`, so `D.toDiagram.Γ = Shadow.single C` by `rfl` and every
clause field talks about the accepted `Diagram` vocabulary (`Visit`, `Crossing`, `crossingPoint`, `sign`, `writhe`,
`twin`, `visitCoord`, `overVisit`). The printed hypotheses are `Shadow.Generic` (LinkDiagram.lean:394) field by field:
"turns exist" = `regular`; "finitely many double points, all transversal" = `transverse` (finiteness automatic);
"none a corner; no corner on a non-incident edge" = `tail_off`; `no_triple` is part of the accepted class of oriented
diagrams (def:positive-lift) and of the consumers' hypotheses (cf:thm-carrierfloor (B),(C)) — recorded, not printed in
the lemma. "and are nonzero" = the extra hypothesis `∀ i, principalTurn C.P i ≠ 0` (RegularLocus.lean:15). No generic
parent polygon is assumed (carrierfloor (C)). `PolygonDiagram.ofDiagram D hD` / `toDiagram_ofDiagram` (proved) and
`RoundingData.of_diagram` (proved) give the entry point from any accepted `D : Diagram` with `D.Γ = Shadow.single C`.

### Output curve (Q1) — "a C^∞ regular closed plane curve L_ε"
`Lε : SmoothRegularLoop` := accepted `SmoothLoop` (FrontSmooth.lean:144, `ContDiff ℝ ∞`, 1-periodic — FR-3) +
`regular : ∀ t, deriv γ t ≠ 0`. `rot` is `ClosedC1Curve.rot` (TurningNumber.lean:274) of the accepted bridge
`SmoothLoop.toClosedC1Curve` (FrontSmooth.lean:227) — one notion of `rot`, as the printed scoping sentence demands.
Not `SmoothFront`/`Marking`: a rounded polygon may have vertical tangents and carries a *chosen* over/under; the front
class (`no_vertical`, slope rule) cannot host it. Extra (stronger) conclusion: constant speed `speed = Λ`
(parameter = arclength/Λ), which makes the printed "parametrized by arclength" in (b) an exact translation.

### Output diagram (Q1, FR-1) — "a diagram D_ε carried by it"
`Carried Lε D.toDiagram` (statement §4): occurrence parameters `τ : Visit → [0,1)`, injective, at the crossing point;
every double point of `Lε` is a pair `(τ v, τ (twin v))`; transverse; cyclic order = the accepted `visitCoord`
order via `cycBetween` (LinkDiagramRecord.lean:78/181 — the same shape as `Marking.between_iff`, FrontSmooth.lean:949);
over/under = `D`'s, checked by `sign det(γ'(τ over), γ'(τ under)) = D.sign x` (def:positive-lift's sign,
LinkDiagram.lean:552). `D_ε` *is* `D` (`carried : Carried Lε D.toDiagram`): the printed (c) says the record is "the
same" (proof sm-3:3853-3857 "the over/under assignment is inherited"), and carrierfloor (C) reads exactly this ("the
rounded diagram and the original polygonal diagram have the same named record"). Nothing in `Carried` refers to edge
directions of `D`, so cf:lem-curl's input "a connected C^∞ immersed circle given with an oriented diagram" is
`(γ : SmoothRegularLoop) (D : Diagram) (Carried γ D)` with no rounding-specific baggage (this is why B's `Carries`,
with `par_dir` and a linear order, was not adopted). Coherence with the front block: a later
`SmoothDiagram := Σ γ D, Carried γ D` receives instances both from cusp-free `Marking`s and from `roundedCarried`.

### Clearance (Q3)
`exists_clearance : ∀ C D, (∀ i, principalTurn C.P i ≠ 0) → ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀), Nonempty (RoundingWitness C D ε)`
— the printed existential in the conclusion. The explicit printed value `ε₀(L) = ⅓ min{η_v, η_e, η_ℓ, η_X}`
(sm-3:3822-3833; empty minimum "+∞" read as `η_ℓ`) is `CornerRounding.clearance C` in the skeleton, a function of the
polygon `C` alone (the crossings of `Shadow.single C` depend only on `C`) — carrierfloor (B) "Take ε₁ = ε₀(L)" can cite
it by name; `Admissible C D ε` bundles "turns nonzero", `0 < ε`, `ε < clearance C`.

### Clause (a)
`outside : ∀ p ∉ ⋃ i, cornerDisc C ε i, (p ∈ range Lε.γ ↔ p ∈ polygonImage C)` (the printed set statement; the discs
are the CLOSED Euclidean ε-discs `cornerDisc`, via `euclideanLength`, EuclideanPlane.lean:29, not the product metric)
and `straight` (parametric form on `[b j, a (j+1)]`, read by (b)-(d) and by carrierfloor (B) "each straight portion
contributes zero tangent increment").

### Clause (b) (Q2)
Junction at corner `j` = parameter interval `[a j, b j]` of the subdivision `0 = a 0 < b 0 < a 1 < ⋯ < b (k−1) < a k = 1`
(the pattern of the accepted `rot_eq_rotationNumber_of_rounding`, TurnLift.lean:314); by (e) it is exactly the part of
the curve inside the disc about `q_j`, so "inside the disc about q_i" = "on `[a j, b j]`". Fields (each a printed
phrase): `θ j` C^∞ on ℝ, `IsLiftOn T (θ j) (a j) (b j)` (accepted interval lift, TurnLift.lean:40), constant on the two
half-lines; `tangent_start/end` ("from δ_{i−1}/|δ_{i−1}| to δ_i/|δ_i|"); `θ_sweep : θ (b) − θ (a) = ϑ_i` and `θ_range`
("sweeping an arc of length exactly |ϑ_i| and no more"); `θ_strict` (StrictMonoOn / StrictAntiOn by the sign of ϑ_i);
`θ_unique` (∃! parameter per angle of the arc) and `direction_once` (`InjOn T`) ("attaining each direction of that arc
at exactly one parameter"); `immersion : deriv (θ j) t ≠ 0` on the open arc (arclength derivative = this / speed);
`flat_ends` (all derivatives of θ of order ≥ 1 vanish at both ends) and `flat_ends_curve` (all derivatives of the curve
of order ≥ 2 vanish at both ends — "the junction meeting the straight edges flat to infinite order"; C^∞-ness across the
ends is `Lε.smooth`). The printed commentary (monotonicity and the derivative are separate exports) is honoured. The
transition profile is not in the statement (printed: "the profile fixed in the proof"); it is `Real.smoothTransition`
in the skeleton, definitionally the printed `f(t)/(f(t)+f(1−t))`, `f = expNegInvGlue`.

### Clause (c)
`same_double_points : doublePoints Lε.γ = {crossingPoint x}`; `same_strands : τ v ∈ Ioo (b (label v)) (a (label v + 1))`
(the occurrence is traversed on the straight part of its strand's edge) and `same_strand_dir` (velocity a positive
multiple of that edge) — the printed "with the same strands"; `same_signs : smoothSign x = D.sign x` and `same_writhe`.

### Clause (d)
`rot_eq : Lε.toClosedC1Curve.rot = rotationNumber C.P` (cf:def-turning on the left, lem:rot on the right).

### Clause (e) (Q4)
Discs `cornerDisc C ε i`, accepted `IsDisc` (LinkMoves.lean:100); `disc_disjoint`, `disc_center`,
`disc_off_nonincident`, `disc_no_double`, `disc_meets_out/in` (= exactly `subsegOut/In`, the two ε-sub-segments),
`disc_contains_modification`, `disc_only_modification` (a point of the curve in disc `j` is on the junction `j`),
`junction_embedded` (`InjOn` on `[a j, b j]`), `straight_off_discs`. The last three are the consumer's "a disc meeting the
diagram in one embedded arc" (sm-3:3697-3699), established in the printed proof (injectivity 3808-3811, discs meet
nothing else 3835-3840).

### Bundle
`RoundingData : Prop`, 7 fields: `exists_clearance` (the theorem — the printed existence sentence),
`smooth_regular_carried`, `a`, `b`, `c`, `d`, `e` (the reading of each printed clause on a witness; they are
projections of `RoundingWitness`, proved in the skeleton's row). Main declaration `SM.cf_lem_rounding : RoundingData`
(not in the checker's fixed-name list; named per the cf:* convention). Corollary `RoundingData.of_diagram` (proved).

## 2. Proof plan (Q5) — the construction (Skeleton_FINAL.lean §7, from Skeleton_A §6)
Angle-first, determinate in `(C, ε)`: `φ := Real.smoothTransition`; per corner `u_j, v_j, ϑ_j`, accumulated angle
`θu 0 = arg u_0`, `θu (j+1) = θu j + ϑ_j`; junction data `M ϑ = ∫₀¹ cos(ϑ(φ−½))`, `juncLen ε ϑ = ε·2cos(ϑ/2)/M ϑ`
(= printed `ε|u+v|/|m(φ)|`), `juncArc A0 ε θu ϑ s = A0 + juncLen • ∫₀ˢ (cos,sin)(θu + ϑφ)` (= printed `γ_ℓ`, `s = σ/ℓ`);
lengths `ℓ_j`, `str_j = |δ_j| − 2ε`, `Λ = Σ(ℓ_j + str_j)`, `a j`, `b j` (cumulative arclength / Λ);
`Θ t = θu 0 + 2π rot·⌊t⌋ + Σ_j ϑ_j φ((fract t − a j)Λ/ℓ_j)`; `tangentField = dirOf ∘ Θ`;
`curveMap t = A0 0 + Λ • ∫₀ᵗ tangentField`; `liftAt j t = θu j + ϑ_j φ((t − a j)Λ/ℓ_j)`;
`τ v = b j + (crossingParam·|δ_j| − ε)/Λ`; `clearance C = ⅓ min{ηv, ηe, ηℓ, ηX}` (Euclidean `far` through `planeComplex`).
Assembly (§9, proved): `roundedLoop : SmoothRegularLoop`, `roundedCurve`, (d) via the ACCEPTED
`rot_eq_rotationNumber_of_rounding` with the lifts `liftAt`, `roundedCarried`, `doublePoints_roundedLoop`,
`roundedWitness` (every field), and the row (§10). Proved leaves (28): profile symmetry, `dirOf` facts, junction
derivative (FTC) and endpoint (`juncArc_one` from `integral_juncDir`), smoothness of `juncAngle/juncDir/liftAt/
tangentField/curveMap`, `hasDerivAt_curveMap`, `curveMap_periodic` (periodic integrand + zero period integral),
`tangentField_periodic` (now with `Regular`), `Θ_add_one`, `θu_last`, `uDir_succ`, subdivision facts
(`ℓ_pos`, `str_pos`, `Λ_pos`, `a_last`, `a_lt_b`, `b_lt_a`, `junction_arg_b`), `liftAt_const_left/right`, `liftAt_b`,
`turn_bounds`, plus the witness-field derivations `θ_range`, `θ_unique`, `disc_only_modification`, `junction_embedded`.

## 3. Remaining chain (52 `sorry`, all leaves; exact statements in Skeleton_FINAL.lean §8)

Unit P (4): `smoothTransition_strictMonoOn` (for `0 ≤ s < t ≤ 1`: `f(s)f(1−t) < f(t)f(1−s)` ⇔ `1/t + 1/(1−s) < 1/s + 1/(1−t)`,
no derivatives), `deriv_smoothTransition_pos` (quotient rule from `expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul` with
`p = 1`, `f' = x⁻² f`), `iteratedDeriv_eq_zero_of_const_left/right` (continuity of `iteratedDeriv m f` + vanishing on an
open half-line: `Filter.EventuallyEq.iteratedDerivWithin_eq` with `s = univ` / `iteratedDerivWithin_univ`, or induction on
`m` with `Filter.EventuallyEq.deriv_eq`).
Unit A (7): `dirOf_injOn_of_lt_pi`, `M_pos` (integrand ≥ cos(ϑ/2) > 0), `juncLen_pos`, `integral_juncDir` (reflection
`t ↦ 1−t`, `intervalIntegral.integral_comp_sub_left`, `smoothTransition_symm`), `juncArc_mem_disc` (bisector frame:
`x_w` strictly increasing from `−ε cos α` to `ε cos α`, `|x_z| ≤ ε sin α` from `sgn ϑ·∫₀ˢ sin β ≤ 0` and `∫₀¹ sin β = 0`
read off `juncArc_one`; fallback: the printed cone+chord argument), `juncArc_mem_open_disc` (strict `x_w`),
`juncArc_injOn` (`x_w' = cos β ≥ cos α > 0`).
Unit G (17): `dirOf_θu`, `dirOf_θu_add_turn` (induction with `principalAngle_coe_angle` RotationNumber.lean:13 +
`Real.Angle.angle_eq_iff_two_pi_dvd_sub`, `Complex.norm_mul_exp_arg_mul_I`), `three_mul_lt_edgeLength` (clearance
arithmetic), `Θ_smooth` (local case analysis: away from integers `fract` affine and `⌊·⌋` constant; at an integer `m`,
`Θ =ᶠ θu 0 + 2π rot·m + ϑ_0 φ((t−m)Λ/ℓ_0)` on both sides since `Σϑ = 2π rot`; `ContDiffAt.congr_of_eventuallyEq`),
`Θ_on_junction`, `Θ_on_straight` (sum splitting: earlier profiles 1, later 0; `t = 1` case via `θu_last`),
`integral_tangentField_junction` (substitution + `integral_juncDir`), `integral_tangentField_straight`,
`integral_tangentField_period` (`sum_integral_adjacent_intervals` over the `2k` pieces + telescoping `Σδ_j = 0`,
`sum_edges` Polygon.lean:85), `curveMap_a/b`, `curveMap_on_junction/straight` (same value at one end, same derivative,
`constant_of_has_deriv_right_zero` or FTC difference), `liftAt_strictMonoOn/AntiOn` (Unit P ∘ affine),
`deriv_liftAt_ne_zero` (chain rule + `deriv_smoothTransition_pos`), `tangent_injOn_junction` (`dirOf_injOn_of_lt_pi` +
strict monotonicity, `|ϑ| < π`).
Unit E (9): `clearance_pos` (finite positive minima: distinct corners from `tail_off` + `k ≥ 3`; `η_e` from compactness of
closed edges (image of `Icc 0 1` under `edgePoint`) + `tail_off`; `η_ℓ` from `Regular`; `η_X` from
`Generic.crossingPoint_mem_interior` + `tail_off`; `IsClosed.notMem_iff_infDist_pos` — check the `notMem` spelling),
`cornerDisc_isDisc`, `mem_interior_cornerDisc` (Euclidean ball pulled back by the linear isometry `planeComplex`;
sup-ball of radius ε/2 inside), `cornerDisc_disjoint` (`|q_i − q_j| ≥ η_v > 3ε`), `cornerDisc_disjoint_edge`
(`dist(q_i, 𝓔_i) ≥ η_e > ε`), `crossingPoint_notMem_cornerDisc`, `cornerDisc_inter_edge_out/in` (points of edge `i` within
`ε` of `q_i` are the parameters `≤ ε/|δ_i|`), `three_mul_lt_dist_crossing`.
Unit X (15): `curveMap_junction_mem_disc` (Unit A + `curveMap_on_junction`), `curveMap_straight_notMem_discs`,
`range_curveMap_outside`, `τ_mem_straight`, `τ_mem_Ico`, `curveMap_τ`, `deriv_curveMap_τ`, `τ_injective`,
`doubles_curveMap` (case analysis on the two pieces: junction–junction only within one disc where the arc is simple;
junction–straight excluded by the open-disc strictness; straight–straight = a crossing of `L` via
`regular_adjacent_meet` (SM/CS3.lean:84, per PLAN_B) and `Generic.common_point_unique`, whose occurrences have exactly the
parameters `τ v`, `τ (twin v)`), `transverse_τ`, `order_τ` (`τ` strictly increasing in `visitCoord`, both lexicographic in
(edge, crossing parameter); `cycBetween` preserved by strictly increasing maps; seam: no crossing in the ε-piece before
`A₀(q_0)`), `sign_τ` (bilinearity of `det`, positive scalars), `cover` (the `2k` pieces cover `[0,1)`),
`iteratedDeriv_curveMap_a/b` (`deriv curveMap = Λ • tangentField`, `tangentField` constant on the open straight part
before/after the junction — by periodicity for `j = 0` — so `iteratedDeriv (m−1) tangentField` vanishes there; then the
localised half-line flatness lemma).

## 4. Unit split for parallel provers (statements byte-identical; fill your unit's sorries; others are black boxes)

| unit | leaves | est. lines | depends on | order |
|---|---|---|---|---|
| P profile | 4 | 300 | Mathlib only | wave 1 |
| G1 angles + clearance arithmetic (`dirOf_θu`, `dirOf_θu_add_turn`, `three_mul_lt_edgeLength`) | 3 | 200 | — | wave 1 |
| E clearance/discs | 9 | 450 | — | wave 1 |
| A junction | 7 | 800 | P | wave 2 |
| G2 `Θ`, curve pieces, integrals | 10 | 800 | P, A, G1 | wave 2 |
| G3 lifts (`liftAt_strictMonoOn/AntiOn`, `deriv_liftAt_ne_zero`, `tangent_injOn_junction`) | 4 | 200 | P, A(`dirOf_injOn_of_lt_pi`) | wave 2 |
| X doubles / record / flatness / cover | 15 | 900 | A, G, E | wave 3 |
| total | 52 | ≈ 3650 | | ≈ 3 waves, ~8 h wall with 7 provers |

Check command per unit: `cd work/lean && lake env lean ../drafts/rounding/U_<unit>.lean` (copy of Skeleton_FINAL.lean).

## 5. Accepted declarations used (grep-verified 2026-09-14 in work/lean by the judge unless marked †)
SM/FrontSmooth.lean:144 `SmoothLoop`; :227 `SmoothLoop.toClosedC1Curve`; :949 `SmoothFront.Marking` (coherence);
:1129 `GeomRounding` (pattern: witness structure + `Nonempty`).
SM/TurningNumber.lean:119 `IsLift`; :226 `normalize`; :228 `euclideanLength_normalize`; :241 `ClosedC1Curve`; :264
`tangentLoop`; :274 `rot`; :60 `circleExp_planeComplex`.
SM/TurnLift.lean:40 `IsLiftOn`; :55 `IsLiftOn.increment_eq`; :68 `increment_eq_zero_of_const`; :283
`two_pi_mul_rotationNumber`; :291 `sum_range_natCast_eq_sum_zmod`; :314 `rot_eq_rotationNumber_of_rounding`; :380
`euclideanLength_smul`; :385 `normalize_smul_of_pos`.
SM/RotationNumber.lean:10 `rotationNumber`; :13 `principalAngle_coe_angle`; :45 `rotationNumber_integer`.
SM/RegularLocus.lean:12 `Regular`; :15 `principalTurn`. SM/RegularPairs.lean:8 `RegularPair`; :54 `principalAngle`;
:56 `principalAngle_bounds`. SM/EuclideanPlane.lean:9 `planeComplex`; :27 `planeDot`; :29 `euclideanLength`;
`euclideanLength_formula`, `euclideanLength_pos`.
SM/Polygon.lean:16 `det`; :49 `edge`; :51 `edgePoint`; :54 `edgeSegment`; :57 `edgeInterior`; :60 `incident`; :85 `sum_edges`.
SM/LinkDiagram.lean:61 `PolyComp` (+`instNeZeroK`); :99 `seg`; :106 `dir`; :245 `IsCrossing`; :251 `Crossing`; :256
`Visit`; :372 `crossingPoint`; :394 `Shadow.Generic`; :414 `Generic.common_point_unique`; :456
`Generic.crossingPoint_mem_interior`; :463 `Generic.crossingPoint_injective`; :490 `Diagram`; :552 `Diagram.sign`;
:577 `Diagram.writhe`; :597 `overVisit`; :600 `underVisit`; :1413 `crossingParam`; :1589 `Shadow.single`; :1594
`singleStrandEquiv`; :1661 `singleCrossingEquiv`; :1703 `single_crossingPoint`.
SM/LinkDiagramRecord.lean:78 `cycBetween`; :181 `visitCoord`; :413 `twin`; :420 `twin_ne`; :745 `singleDiagram` (coherence).
SM/LinkMoves.lean:100 `IsDisc`. SM/LinkPositiveLift.lean:160 `Shadow.single_generic_of` (input construction).
† SM/CS3.lean:84 `regular_adjacent_meet` (cited by PLAN_B; to be re-verified by Unit X). † SM/Crossings.lean:88 `edgePoint_injective`.
Mathlib (pin): `Real.smoothTransition` (SmoothTransition.lean:146; `.zero` :171, `.one` :175, `.zero_of_nonpos` :168,
`.one_of_one_le` :161, `.pos_denom` :157, `.contDiff` :206, `.monotone` :223, `.pos_of_pos`, `.lt_one_of_lt_one`),
`expNegInvGlue` :39, `expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul` :100; `intervalIntegral.integral_hasDerivAt_right`,
`integral_add_adjacent_intervals`, `Function.Periodic.intervalIntegral_add_eq` (IntervalIntegral/Periodic.lean:344),
`contDiff_infty_iff_deriv`, `Real.contDiff_cos/sin` (Trigonometric/Deriv.lean:367/328 — needs its import),
`Real.cos_add_int_mul_two_pi`, `Int.floor_add_one`, `Int.fract_add_one`, `intermediate_value_uIcc`,
`StrictMonoOn.injOn`, `Finset.sum_pos`.

## 6. Fidelity risks (to be cited in the review of this row and of its consumers)
FR-R1 (FR-1 for the rounding lane): `D_ε` is the polygonal `Diagram D` read through `Carried` (the smooth diagram's
over/under is `D.overStrand`, checked by sign consistency); coherent with `SmoothFront.Marking`. A reviewer wanting a
genuinely smooth diagram class is pointed to `Carried` as that class's defining record.
FR-R2 (existential form): the bundle is the printed ∃-form; the named construction `CornerRounding.roundedWitness`,
`CornerRounding.clearance` lives in the proof module and is what cf:thm-carrierfloor (A) ("one curve and one diagram
Round(L,D,ε)") must cite — that row will have to import the rounding proof module, not only the statement.
FR-R3 (hypotheses): `no_triple` enters through `PolygonDiagram.generic` (accepted class of oriented diagrams; the
consumers assume it) — not printed in the lemma. The `RoundingWitness` exports strictly more than printed: constant speed,
the parametric straight form, `same_strands` on the open straight parameter interval, curve-level flatness of order ≥ 2,
"junction = all of the curve in the disc" and embeddedness. All are supplied by the construction and read downstream.
FR-R4 (parameter): the printed junction is by arclength σ ∈ [0, ℓ]; the row uses arclength/Λ so that `L_ε` is a
`SmoothLoop` (period 1); (b)'s "angular derivative nonzero" is parametrisation-independent, `immersion` is stated for
`deriv θ`.
FR-R5 (bundle shape): fields 2-7 of `RoundingData` are projections of `RoundingWitness` (the per-clause reading), the
theorem is field 1; the fixed content of (a)–(e) is the field list of `RoundingWitness`.
FR-R6 (chain, recorded): A's `tangentField_periodic` lacked `Regular` (false as stated; fixed and proved here); B's
`roundDisc_inter_edge_in` is false at `k = 0` (ℕ-subtraction) — not adopted.
FR-R7 (Mathlib pin): `Real.smoothTransition` has no strict-monotonicity / derivative-sign / flatness lemmas; Unit P
supplies them. `IsClosed.notMem_iff_infDist_pos` spelling to be checked by Unit E.
