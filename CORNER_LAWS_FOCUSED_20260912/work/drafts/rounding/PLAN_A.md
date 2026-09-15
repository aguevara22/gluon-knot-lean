# PLAN A — cf:lem-rounding (rounding), model-first architecture

Row: cf:lem-rounding, reference/SM/sm-3-statesum.tex:3644-3700 (statement), 3701-3869 (proof).
Architect A, 2026-09-14. Deliverables in this directory:
- `Rounding_statement_A.lean` — FIXED-STATEMENT candidate. Compiles (`lake env lean`, 8 s), 1 `sorry`
  (the row theorem `SM.cf_lem_rounding : RoundingData`). Axioms of the statement objects
  (`RoundingData`, `RoundingWitness`, `Carried.smoothWrithe_eq`): propext, Classical.choice, Quot.sound.
- `Skeleton_A.lean` — statement text verbatim + the explicit construction (§6) + 83 chain lemmas
  (§7, 79 `sorry`) + assembly (§8-9). Compiles with no errors and no warnings other than `sorry`;
  `#print axioms SM.cf_lem_rounding` = [propext, sorryAx, Classical.choice, Quot.sound].
  The assembly (witness from chain, bundle from witness, clause (d) via the accepted lem-turnlift
  (iii-a), clause (c) "same double points" from the carried record) is PROVED; only leaf lemmas are `sorry`.
Check command: `cd work/lean && lake env lean ../drafts/rounding/<file>`. Nothing written under work/lean.

## 1. Model decision (Q1-Q5), with the fidelity argument per clause

### Input: "L a closed polygon … D an oriented diagram whose underlying plane curve is L"
`C : PolyComp` (SM/LinkDiagram.lean:61 — the accepted def:polygon object `LabelledTuple k`, `3 ≤ k`;
`L = C.P`, corners `C.P i`, edges `edge C.P i` = `δ_i`, Polygon.lean:49). The diagram is
`PolygonDiagram C` (new, 3 fields): `generic : (Shadow.single C).Generic`, `overStrand`, `over_mem`, with
`toDiagram : Diagram := ⟨Shadow.single C, generic, overStrand, over_mem⟩` (an `abbrev`, so `toDiagram.Γ`
is `Shadow.single C` by `rfl`). This is exactly the accepted one-component `Diagram` (LinkDiagram.lean:490)
on `Shadow.single C` (LinkDiagram.lean:1589); the accepted `singleDiagram C hP ov hov`
(LinkDiagramRecord.lean:745) is the special case of a def:generic parent polygon. The printed hypothesis
list is the accepted `Shadow.Generic` (LinkDiagram.lean:394) field by field:
- "the principal turns of L all exist" = `regular` (`Regular C.P`, RegularLocus.lean:12);
- "finitely many double points, all transversal" = `transverse` (finiteness is automatic for a polygon:
  finitely many edge pairs, each meeting at most once);
- "none of them a corner … no corner lies on an edge other than the two incident to it" = `tail_off`;
- `no_triple` is not printed in the lemma but IS part of "an oriented diagram" (def:positive-lift,
  sm-3:325-327 "no triple points") and of the consumers' hypotheses (cf:thm-carrierfloor (B),(C)). Not a
  narrowing.
- "and are nonzero" = the extra hypothesis `∀ i, principalTurn C.P i ≠ 0` (RegularLocus.lean:15).
No generic parent polygon is assumed (carrierfloor (C): "These conditions are stated here so that no
generic parent polygon is assumed").

### Output curve: "a C^∞ regular closed plane curve L_ε" (Q1)
`Lε : SmoothLoop` (FrontSmooth.lean:144, accepted: `ContDiff ℝ ∞ γ`, `Periodic γ 1`) with
`regular : ∀ t, deriv Lε.γ t ≠ 0`. The accepted `C¹` object of cf:def-turning is reached by the accepted
bridge `SmoothLoop.toClosedC1Curve` (FrontSmooth.lean:205), so `rot` in (d) is literally
`ClosedC1Curve.rot` (TurningNumber.lean:274) — no second smooth-curve class, no duplicate `rot`.
Why not `SmoothFront`/`Marking`: a rounded polygon may have vertical tangents and carries a *chosen*
over/under, while `SmoothFront` imposes `no_vertical` and reads over/under from the slope rule; the front
class cannot host `L_ε`. Why not a bare `ClosedC1Curve` upgraded ad hoc: `SmoothLoop` already is the
accepted "`C^∞` 1-periodic map" (FR-3), and reusing it keeps one smooth vocabulary for the front block
and the cf:* chain.
Extra (stronger) conclusion exported: constant speed (`const_speed : ‖γ'‖ = speed`), i.e. the
parameter is arclength up to one constant — this is what the construction produces and what makes the
printed "parametrized by arclength" clause of (b) an exact translation (`σ = speed · (t − a j)`,
`ℓ = speed · (b j − a j)`).

### Output diagram: "and a diagram D_ε carried by it" (Q1, FR-1)
Decision: a genuinely smooth diagram is *a regular smooth loop together with the polygonal record it
carries* — `Carried (γ : SmoothLoop) (X : Diagram)` (new, §3 of the statement file): occurrence
parameters `τ : X.Γ.Visit → ℝ` in `[0,1)`, injective, `γ (τ v) = crossingPoint v.1`; every double point
of `γ` is a pair `(τ v, τ (twin v))`; transversality; the cyclic order of the `τ v` is that of the accepted
`visitCoord` (LinkDiagramRecord.lean:181) via `cycBetween` (LinkDiagramRecord.lean:78); the over/under
assignment is `X`'s, checked by `sign det(γ'(τ over), γ'(τ under)) = X.sign x` (def:positive-lift's sign,
LinkDiagram.lean:552). This is FR-1 ("the diagram as a polygonal Diagram carrying the smooth curve's
named record") instantiated for immersed circles, the same shape as the front block's `Marking`
(FrontSmooth.lean:949: component/occurrence bijection, `cycBetween`, `twin`, over bit, sign) minus the
front-specific slope rule; it is the one notion the three consumers read: cf:lem-curl ("F given with
an oriented diagram", `P_{F'} = P_F` through the record), cf:thm-carrierfloor (A) ("one curve and one
diagram": `roundedLoop`, `D` unchanged), (B) (the unit-tangent map of `L_ε`), (C) (`P_D`, `w`, `R`
on the polygonal `D`). For the rounding, `D_ε` *is* `D`: the witness field `carried : Carried Lε D.toDiagram`.
Justification: the printed (c) says the double points, strands, over/under, signs and writhe are "the
same" — the record is literally inherited (proof, sm-3:3853-3857 "the over/under assignment is
inherited"), so the only content is geometric (the double points of `L_ε` are the crossing points, on
the same edges, with the same velocities' orientation), which is exactly what `Carried` + (c) state.

### The clearance (Q3)
Bundle field `exists_clearance : ∀ C D, (∀ i, principalTurn C.P i ≠ 0) → ∃ ε₀, 0 < ε₀ ∧ ∀ ε, 0 < ε →
ε < ε₀ → Nonempty (RoundingWitness C D ε)` — the printed existential, quantified in the conclusion.
The proof's explicit value `ε₀(L) = ⅓ min{η_v, η_e, η_ℓ, η_X}` (sm-3:3822-3833, empty minimum read as
`+∞` — here as `η_ℓ`) is the definition `CornerRounding.clearance C D` in the skeleton, with
`clearance_pos`; carrierfloor (B) ("Take ε₁ = ε₀(L)") can cite it by name.

### Clause (a)
Two fields: `outside : ∀ p ∉ ⋃ i, cornerDisc C ε i, (p ∈ range Lε.γ ↔ p ∈ polygonImage C)` — the printed
set statement, with the discs the CLOSED Euclidean `ε`-discs `cornerDisc C ε i = {p | ‖p − q_i‖ ≤ ε}`
(the same discs as in (e); Euclidean via `euclideanLength`, EuclideanPlane.lean:29, not the product
metric) — and `straight : ∀ j < k, ∀ t ∈ [b j, a (j+1)], Lε.γ t = Lε.γ (b j) + (speed (t − b j)) • δ_j/|δ_j|`
(the parametric form of "coincides with L": the straight parts run along the edges), which (b)-(d)
read.

### Clause (b) (Q2)
The junction at corner `j` is the parameter interval `[a j, b j]` of the subdivision
`0 = a 0 < b 0 < a 1 < ⋯ < b (k−1) < a k = 1` (the pattern of the accepted
`rot_eq_rotationNumber_of_rounding`, TurnLift.lean:314); its image is inside the disc
(`disc_contains_modification`) and the open straight parts are outside every disc
(`straight_off_discs`), so "inside the disc about q_i" = "on `[a j, b j]`". Fields, each a printed phrase:
- lift: `θ j : ℝ → ℝ`, `C^∞` on `ℝ` (`θ_smooth`), `IsLiftOn T (θ j) (a j) (b j)` (`θ_lift`, the accepted
  interval lift, TurnLift.lean:40), constant on the adjacent straight parts (`θ_const_left/right`; the
  consumer (B) concatenates "straight-part arguments with the junction lifts");
- "from δ_{i−1}/|δ_{i−1}| to δ_i/|δ_i|": `tangent_start`, `tangent_end` (`T (a j) = normalize (edge (j−1))`,
  `T (b j) = normalize (edge j)`);
- "sweeping an arc of length exactly |ϑ_i| and no more": `θ_sweep : θ j (b j) − θ j (a j) = ϑ_j`, which with
  strict monotonicity makes the swept arc exactly the closed arc between the two directions;
- "moves strictly monotonically, in the sense of sgn ϑ_i": `θ_strict` (`StrictMonoOn` if `ϑ_j > 0`,
  `StrictAntiOn` if `ϑ_j < 0`; `ϑ_j ≠ 0` by hypothesis);
- "attaining each direction of that arc at exactly one parameter": `θ_attained` (every angle of
  `uIcc (θ (a j)) (θ (b j))` is attained on `[a j, b j]`) and `direction_once : InjOn T (Icc (a j) (b j))`;
- "an immersion on the open junction arc: … angular derivative is nonzero at every interior parameter":
  `immersion : ∀ t ∈ Ioo (a j) (b j), deriv (θ j) t ≠ 0` (arclength derivative = this / speed);
- "at the two ends it and all its derivatives vanish, … flat to infinite order":
  `flat_ends : ∀ m ≥ 1, iteratedDeriv m (θ j) (a j) = 0 ∧ iteratedDeriv m (θ j) (b j) = 0` (the `C^∞`-ness of
  `L_ε` across the endpoints is the structure field `Lε.smooth`).
The transition profile is NOT in the statement (the printed statement exposes properties; the profile is
"fixed in the proof"); it is the definition `Real.smoothTransition` in the skeleton's construction.

### Clause (c)
`same_double_points : Carried.doublePoints Lε = {crossingPoint x}` (set equality, printed "the same
double points"); `same_strands : τ v ∈ Ioo (b (label v).val) (a ((label v).val + 1))` and
`same_strand_dir : ∃ r > 0, Lε.γ' (τ v) = r • edge C.P (label v)` (printed "with the same strands", read
as: the occurrence of strand `s` is traversed on the straight part of edge `s`, in its direction);
`same_signs : carried.smoothSign x = D.toDiagram.sign x` ("the same over/under assignment and hence the
same crossing signs" — the sign of the smooth diagram is computed from velocities in `D`'s over-first
order, def:positive-lift); `same_writhe : carried.smoothWrithe = D.toDiagram.writhe`
(LinkDiagram.lean:577).

### Clause (d)
`rot_eq : (Lε.toClosedC1Curve regular).rot = rotationNumber C.P` — cf:def-turning `rot` on the left,
lem:rot `rotationNumber` (RotationNumber.lean:10) on the right, as the printed preamble says.

### Clause (e) (Q4)
The discs are `cornerDisc C ε i`; fields: `disc_isDisc` (accepted `IsDisc`, LinkMoves.lean:100 — the
clean-disc vocabulary), `disc_disjoint`, `disc_center` (`q_i ∈ interior`), `disc_off_nonincident`
(`¬ incident i j → Disjoint (disc i) (edgeSegment j)`, Polygon.lean:60/54), `disc_no_double`
(`crossingPoint x ∉ disc i`), `disc_meets_out/in` (`disc i ∩ edgeSegment i = subsegOut`, `disc i ∩
edgeSegment (i−1) = subsegIn`: exactly the two sub-segments of length `ε`), `disc_contains_modification`
(`Lε.γ '' [a j, b j] ⊆ disc j`) and `straight_off_discs`. All but the last two are facts about the polygon
and `ε < ε₀` alone (Unit E).

### Bundle (`RoundingData`, 7 fields = 7 printed sentences/clauses)
`exists_clearance`, `smooth_regular_carried`, `a`, `b`, `c`, `d`, `e`; fields 2-7 are projections of
`RoundingWitness` (proved in the skeleton), field 1 is the theorem. Main declaration
`SM.cf_lem_rounding : RoundingData`. (The row is not in the checker's fixed-name list; name per the
convention of the cf:* rows.)

## 2. Proof plan (Q5) — the construction as definitions (Skeleton_A.lean §6)

Profile `φ := Real.smoothTransition` = `expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1−x))`, i.e.
EXACTLY the printed `f(t)/(f(t)+f(1−t))`, `f = e^{−1/t}` (Mathlib SmoothTransition.lean:146; Mathlib
gives `C^∞`, `φ = 0` on `(−∞,0]`, `= 1` on `[1,∞)`, monotone; we add symmetry, strict monotonicity, `φ' > 0`).
Per corner `j` (angles rather than vectors): `u_j = normalize (edge (j−1))`, `v_j = normalize (edge j)`,
`ϑ_j = principalTurn`, accumulated angle `θu 0 = arg u_0`, `θu (j+1) = θu j + ϑ_j` (so `dirOf (θu j) = u_j`,
`dirOf (θu j + ϑ_j) = v_j` by `v = u·e^{iϑ}`, the definition of the principal angle through `cornerRotor`).
Junction (abstract, Unit A): `juncDir θu ϑ s = (cos, sin)(θu + ϑ φ(s))`,
`M ϑ = ∫₀¹ cos(ϑ(φ − ½))` (> 0), `juncLen ε ϑ = ε · 2cos(ϑ/2) / M ϑ` (= printed `ε|u+v|/|m(φ)|`),
`juncArc A0 ε θu ϑ s = A0 + juncLen • ∫₀ˢ juncDir` (= printed `γ_ℓ` in the profile parameter `s = σ/ℓ`),
with `juncArc 1 = A0 + ε(u+v) = A1`.
Global (Unit G): lengths `ℓ_j = juncLen ε ϑ_j`, `str_j = |δ_j| − 2ε`, `Λ = Σ (ℓ_j + str_j)`,
`a j = (Σ_{i<j} (ℓ_i + str_i))/Λ`, `b j = a j + ℓ_j/Λ`;
`Θ t = θu 0 + 2π rot(L)·⌊t⌋ + Σ_{j<k} ϑ_j φ((fract t − a j)Λ/ℓ_j)`;
`tangentField = dirOf ∘ Θ`; `curveMap t = A0 0 + Λ • ∫₀ᵗ tangentField`; `liftAt j t = θu j + ϑ_j φ((t − a j)Λ/ℓ_j)`;
`τ v = b j + (crossingParam·|δ_j| − ε)/Λ` (`j` = strand label of `v`).
Why angle-first: smoothness and regularity of `L_ε` are automatic (`L_ε' = Λ (cos Θ, sin Θ)`, never 0,
`C^∞` by `contDiff_infty_iff_deriv` once `Θ` is), the unit tangent is `dirOf ∘ Θ` and `Θ` is the global
lift (so (b) and (d) are read off), the speed is the constant `Λ` (arclength), and the `C^∞` gluing
"flat to infinite order" is the flatness of `φ` at `0` and `1`. Closedness = `∫₀¹ tangentField = 0` =
the telescoping `Σ_j [ε(u_j+v_j) + (|δ_j| − 2ε) v_j] = ε Σ (u_j − v_j) + Σ δ_j = 0` (`u_{j+1} = v_j`,
`sum_edges`). Determinacy for carrierfloor (A) is definitional: `Round(L,D,ε) = (roundedLoop, D)`.

## 3. Chain of lemmas (exact statements in Skeleton_A.lean §7; `h : Admissible C D ε` bundles
"turns nonzero", `0 < ε`, `ε < clearance C D`)

Unit P (profile, 5): `smoothTransition_symm : φ(1−t) = 1 − φ t`; `smoothTransition_strictMonoOn :
StrictMonoOn φ (Icc 0 1)`; `deriv_smoothTransition_pos : 0<t<1 → 0 < deriv φ t`;
`iteratedDeriv_eq_zero_of_const_left/right : ContDiff ℝ ∞ f → (∀ t ≤ x, f t = c) → 1 ≤ m →
iteratedDeriv m f x = 0` (general; gives `flat_ends` from `θ_const_left/right`).
Unit A (one junction, 14): `dirOf_unit`, `normalize_smul_dirOf`, `dirOf_injOn_of_lt_pi`,
`contDiff_juncAngle/juncDir`, `M_pos`, `juncLen_pos`, `integral_juncDir : ∫₀¹ juncDir =
(M ϑ/(2cos(ϑ/2))) • (dirOf θu + dirOf (θu+ϑ))` (the bisector symmetry, sm-3:3742-3749), `juncArc_zero/one`,
`hasDerivAt_juncArc`, `juncArc_mem_disc : s ∈ Icc 0 1 → eucDist (juncArc s) (A0 + ε•dirOf θu) ≤ ε`
(printed triangle argument sm-3:3752-3806: cone coordinates `λ(s) = ε − ℓ∫₀ˢ a ≥ 0`, `μ(s) = ℓ∫₀ˢ b ≥ 0`
with `juncDir = a u + b v`, `a,b ≥ 0`; chord `λ+μ ≤ ε` from `∫₀ˢ (a−b) ≥ 0` by the antisymmetry
`a−b = 2cos(ϑ/2) sin(ϑ(½−φ))/sin ϑ`; then `‖−λu + μv‖ ≤ λ+μ`), `juncArc_mem_open_disc` (strict for
`0<s<1`), `juncArc_injOn` (bisector coordinate `x_w' = cos β ≥ cos(ϑ/2) > 0`).
Unit G (global, 42): angles `turn_bounds`, `dirOf_θu`, `dirOf_θu_add_turn`, `θu_last`, `uDir_succ`;
subdivision `ℓ_pos`, `str_pos`, `Λ_pos`, `a_zero` (proved), `a_last`, `a_lt_b`, `b_lt_a`, `b_sub_a` (proved);
`Θ_smooth` (local case analysis: away from integers `fract` is affine and `⌊·⌋` constant; at an integer
`m` the function is `θu 0 + 2π rot·m + ϑ_0 φ((t−m)Λ/ℓ_0)` on a neighbourhood, all other terms being `0`
(right) or absorbed (`Σϑ_j = 2π rot`, left), so `ContDiffAt` by `congr_of_eventuallyEq`); `Θ_add_one`;
`Θ_on_junction : t ∈ Icc (a j) (b j) → Θ t = liftAt j t`; `Θ_on_straight : t ∈ Icc (b j) (a (j+1)) → Θ t =
θu (j+1)`; `tangentField_periodic/smooth/unit`; `hasDerivAt_curveMap` (FTC
`intervalIntegral.integral_hasDerivAt_right`), `curveMap_smooth` (`contDiff_infty_iff_deriv`),
`deriv_curveMap` (proved); piece integrals `integral_tangentField_junction = (ε/Λ)•(u_j+v_j)`
(substitution + `integral_juncDir`), `integral_tangentField_straight = (str_j/Λ)•v_j`,
`integral_tangentField_period = 0` (`sum_integral_adjacent_intervals` over the `2k` pieces + telescoping),
`curveMap_periodic`, `curveMap_a/b`, `curveMap_on_junction` (= `juncArc` under `s = (t−a j)Λ/ℓ_j`),
`curveMap_on_straight`; lifts `liftAt_smooth`, `liftAt_const_left/right`, `liftAt_a` (proved), `liftAt_b`,
`liftAt_strictMonoOn/AntiOn` (Unit P composed with the affine map), `deriv_liftAt_ne_zero` (chain rule +
`deriv_smoothTransition_pos`), `normalize_deriv_curveMap` (proved), `liftAt_isLiftOn` (proved),
`tangent_injOn_junction` (`dirOf_injOn_of_lt_pi` + strict monotonicity, `|ϑ| < π`).
Unit E (clearance/discs, 10): `clearance_pos` (finite positive minima: distinct corners from `tail_off` +
`Regular`; `η_e` from compactness of closed edges in `ℂ` via `planeComplex` and `tail_off`; `η_ℓ` from
`Regular`; `η_X` from `Generic.crossingPoint_mem_interior` + `tail_off`), `cornerDisc_isDisc` (convex,
compact, `q_i` interior — Euclidean ball pulled back by the linear isometry `planeComplex`),
`mem_interior_cornerDisc`, `cornerDisc_disjoint` (`|q_i − q_j| ≥ η_v > 3ε`), `cornerDisc_disjoint_edge`
(`dist(q_i, 𝓔_i) ≥ η_e > ε`), `crossingPoint_notMem_cornerDisc`, `cornerDisc_inter_edge_out/in` (points of
edge `i` within `ε` of `q_i` are the parameters `≤ ε/|δ_i|`), `three_mul_lt_edgeLength`,
`three_mul_lt_dist_crossing`.
Unit X (double points / carried record, 12): `curveMap_junction_mem_disc` (Unit A + `curveMap_on_junction`),
`curveMap_straight_notMem_discs` (a point of the open straight part is at distance `> ε` from `q_j`,
`q_{j+1}` along the edge and outside the other discs by `cornerDisc_disjoint_edge`),
`range_curveMap_outside` (the straight parts cover each edge minus its two `ε`-sub-segments, the
junctions lie in the discs), `τ_mem_straight` (`ε < crossingParam·|δ| < |δ| − ε` from
`three_mul_lt_dist_crossing`), `τ_mem_Ico`, `curveMap_τ`, `deriv_curveMap_τ`, `τ_injective`,
`doubles_curveMap` (case analysis on the two pieces containing `s`, `t`: junction–junction only within one
disc, where the arc is simple (`juncArc_injOn`) and `Θ` is monotone; junction–straight only at the shared
endpoint, excluded by `s ≠ t` and the open-disc strictness; straight–straight = a crossing of `L`
(`Generic.common_point_unique`) whose two occurrences are `τ v`, `τ (twin v)`), `transverse_τ`
(velocities are positive multiples of edge directions, `D.generic.transverse`), `order_τ` (`τ` is a
strictly increasing function of `visitCoord = j + crossingParam`; `cycBetween` is preserved by strictly
increasing maps), `sign_τ` (`det (r•u) (r'•v) = r r' det u v`, `r,r' > 0`).
Assembly (proved in the skeleton): `roundedLoop`, `roundedLoop_speed/regular`, `roundedCurve`,
`rot_roundedCurve` (from the ACCEPTED `rot_eq_rotationNumber_of_rounding` with `a, b, liftAt`),
`roundedCarried`, `doublePoints_roundedLoop`, `roundedWitness` (every field a chain lemma),
`cf_lem_rounding`.

## 4. Accepted declarations used (grep-verified 2026-09-14, work/lean)

SM/FrontSmooth.lean:144 `structure SmoothLoop`; :205 `SmoothLoop.toClosedC1Curve`; :949 `Marking`
(cited for coherence only); :1014 `GeomRounding` (cited only).
SM/TurningNumber.lean:119 `IsLift`; :154 `DirectionLoop.lift`; :156 `lift_isLift`; :200 `tw`; :226
`normalize`; :228 `euclideanLength_normalize`; :241 `structure ClosedC1Curve`; :264 `tangentLoop`; :274 `rot`.
SM/TurnLift.lean:40 `IsLiftOn`; :55 `IsLiftOn.increment_eq`; :68 `increment_eq_zero_of_const`; :314
`rot_eq_rotationNumber_of_rounding`; :380 `euclideanLength_smul`; :385 `normalize_smul_of_pos`.
SM/RotationNumber.lean:10 `rotationNumber`; :45 `rotationNumber_integer`.
SM/RegularLocus.lean:12 `Regular`; :15 `principalTurn`; :18 `regular_iff_edges`; :41 `principalTurn_spec`.
SM/RegularPairs.lean:8 `RegularPair`; :54 `principalAngle`; :56 `principalAngle_bounds`; :61 `principalAngle_cos`.
SM/EuclideanPlane.lean:9 `planeComplex`; :29 `euclideanLength`; :55 `cornerRotor`.
SM/Polygon.lean:16 `det`; :49 `edge`; :51 `edgePoint`; :54 `edgeSegment`; :60 `incident`; :85 `sum_edges`.
SM/LinkDiagram.lean:61 `PolyComp`; :251 `Shadow.Crossing`; :256 `Shadow.Visit`; :372 `Shadow.crossingPoint`;
:394 `Shadow.Generic`; :456 `Generic.crossingPoint_mem_interior`; :463 `Generic.crossingPoint_injective`;
:490 `Diagram`; :552 `Diagram.sign`; :577 `Diagram.writhe`; :597 `overVisit`; :600 `underVisit`; :627 `isOver`;
:1413 `crossingParam`; :1421 `crossingParam_pos`; :1435 `visitPt`; :1449 `eval_visitPt`; :1589 `Shadow.single`;
:1594 `singleStrandEquiv`; :1603 `singleStrandEquiv_apply`.
SM/LinkDiagramRecord.lean:78 `cycBetween`; :181 `visitCoord`; :413 `twin`; :420 `twin_ne`; :745
`singleDiagram` (coherence).
SM/LinkMoves.lean:100 `IsDisc`.
SM/LinkPositiveLift.lean:160 `Shadow.single_generic_of` (label-level criterion; useful to build inputs).
Mathlib (pin 85e3a25): `Real.smoothTransition` (SmoothTransition.lean:146; `.zero`, `.one`,
`.zero_of_nonpos`, `.one_of_one_le`, `.contDiff`, `.monotone`, `.pos_of_pos`, `.lt_one_of_lt_one`,
`expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul` :100), `intervalIntegral.integral_hasDerivAt_right`
(FundThmCalculus.lean:725), `contDiff_infty_iff_deriv` (ContDiff/Deriv.lean:103), `contDiff_iff_contDiffAt`,
`ContDiffAt.congr_of_eventuallyEq`, `ContDiff.continuous_iteratedDeriv` (IteratedDeriv/Defs.lean:285),
`intermediate_value_uIcc`, `Circle`/`Complex.exp_mul_I`, `IsClosed.not_mem_iff_infDist_pos`.

## 5. Unit split for parallel provers, estimated lines, order

| unit | lemmas | est. lines | depends on | notes |
|---|---|---|---|---|
| P profile | 5 | 350 | Mathlib only | `deriv_smoothTransition_pos` via the quotient rule from `hasDerivAt_polynomial_eval_inv_mul 1` (`f' = x⁻² f`); flatness via left-limit of the continuous `m`-th derivative |
| A junction | 14 | 900 | P | complex-exponential form `planeComplex (dirOf α) = exp(αI)`; the chord inequality is the hardest piece (~250 lines) |
| G1 angles+subdivision | 13 | 300 | — | `dirOf_θu` by induction with `v = u·e^{iϑ}` from `cornerRotor`/`principalAngle` (`Complex.abs_mul_exp_arg_mul_I`) |
| G2 Θ, curveMap, integrals | 18 | 900 | G1, A, P | `Θ_smooth` local case analysis (~200); piece integrals by `intervalIntegral.integral_comp_mul_add`-type substitutions; `sum_integral_adjacent_intervals` on the `2k`-piece partition |
| G3 lifts | 11 | 250 | P, G1, G2 | mostly compositions with the affine map `t ↦ (t − a j)Λ/ℓ_j` |
| E clearance/discs | 10 | 450 | — | all in `ℂ` via `planeComplex`; `Finset.inf'_le`/`le_inf'` |
| X doubles/record | 12 | 1000 | A, G, E | `doubles_curveMap` is the largest single lemma (~400); `order_τ` needs a small `cycBetween`-preservation lemma |
| total leaf work | 83 | ≈ 4150 | | assembly already proved (Skeleton §8-9, ~130 lines) |

Suggested order: P, G1, E in parallel (independent); then A and G2; then G3 and X. Each unit is
checkable in isolation by copying Skeleton_A.lean and filling its `sorry`s (the file compiles in ~8 s).

## 6. Risks

R1 (medium) `Θ_smooth`: the floor/fract definition needs a careful local argument at integers; if it
stalls, fall back to defining `Θ` on `[0,1]` and the loop by `Int.fract` with a one-sided-derivative
matching lemma — same statement, no change to the witness.
R2 (medium) chord inequality `juncArc_mem_disc`: needs the sum-to-product identity and the antisymmetry
of `∫₀ˢ (a − b)`; the disc radius `ε` is sharp (endpoints on the boundary), so no slack argument exists.
R3 (low-medium) `doubles_curveMap`: bookkeeping over the `2k` pieces of the parameter circle; the
junction–straight case needs the open-disc strictness (`juncArc_mem_open_disc`) and the straight parts'
distance `> ε` from the corners.
R4 (fidelity, recorded) `no_triple` is a hypothesis through `PolygonDiagram.generic` (the accepted class
of oriented diagrams and the consumers' hypotheses require it; the printed lemma's "oriented diagram"
has it by def:positive-lift). `same_strands` uses the open straight interval (stronger than printed).
Constant speed is an extra conclusion (the construction provides it).
R5 (design) `Carried` is a new structure parallel to `Marking`; cf:lem-curl and cf:thm-carrierfloor (R),(A),(B),(C)
must be stated on `Carried` (one component). A later refactor could express `Marking` for cusp-free
one-component fronts through `Carried`; not needed now.
R6 (Mathlib) `Real.smoothTransition` has no strict-monotonicity or derivative-sign lemma in the pin; Unit P
supplies them (elementary). `IsClosed.not_mem_iff_infDist_pos` name may differ (`notMem` spelling) — check.
