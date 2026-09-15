# PLAN B — cf:lem-rounding (row 97), proof-first architecture

Architect B, 2026-09-14 (pod, rounding-lane design panel).  Source: reference/SM/sm-3-statesum.tex
3644-3700 (statement), 3701-3869 (proof).  Consumers read: cf:lem-curl (3870-3891, the input class
"connected C^∞ immersed circle … given with an oriented diagram"), cf:thm-carrierfloor (4282-4340;
(A) 4291-4303 "the construction in the proof of that lemma returns *one* curve and *one* diagram
Round(L,D,ε)"; (B) 4374-4415 reads (b) as junction lifts with positive angular derivative, each level
met once; (C) 4423-4450 reads (c),(d),(e): "the rounded diagram and the original polygonal diagram
have the same named record", rot preserved, discs pairwise disjoint meeting no crossing).

Deliverables (all compile with `lake env lean`, Lean v4.34.0-rc2 / Mathlib 85e3a25e):

| file | content | status |
|---|---|---|
| `work/drafts/rounding/Rounding_statement_B.lean` (459 lines) | definitions the statement needs, `RoundingData` (one field per printed clause), `RoundingData.printed` (the printed ∃-form, proved), `theorem SM.cf_lem_rounding : RoundingData := by sorry` | 0 errors, 0 warnings, exactly 1 `sorry` (the row) |
| `work/drafts/rounding/Skeleton_B.lean` (1255 lines) | the statement part byte-identical (sections 0-5) + the chain of 150 lemmas/defs (96 `by sorry`) + `cf_lem_rounding` PROVED from the chain (unit R has no sorry) | 0 errors, 0 warnings |
| this file | design record | — |

---

## 1. Model decisions and fidelity, clause by clause

### Q1 — the target class and the carried diagram (FR-1 kept)

**Decision.** `L_ε` is a `SmoothRegularLoop` := the accepted `SmoothLoop` (SM/FrontSmooth.lean:144, `ContDiff ℝ ∞`,
1-periodic; the accepted FR-3 reading of "smooth" = C^∞, parameter circle = 1-periodic map of ℝ) plus `regular : ∀ t,
deriv γ t ≠ 0`.  Its rotation is `ClosedC1Curve.rot` of the curve `SmoothLoop.toClosedC1Curve` (FrontSmooth:205 →
TurningNumber:241/274): ONE notion of rot, the accepted cf:def-turning one, exactly as the printed scoping sentence
demands ("Here rot is as in lem:rot for polygons and cf:def-turning for closed C¹ regular curves").  Not a
`ClosedC1Curve` upgraded to C^∞: `ClosedC1Curve` carries an explicit `γ'` field, and building a second smooth class on
it would duplicate `SmoothLoop`; the bridge `toClosedC1Curve` is already accepted.

**"a diagram D_ε carried by it".**  D_ε is a *polygonal* `Diagram` (SM/LinkDiagram.lean:490) and "carried by the
smooth curve" is the record `Carries γ D` (statement §2): occurrences ↔ parameters in [0,1) (`par`), positions
(`par_eval`: the curve is at the crossing point), strand directions (`par_dir`: velocity a positive multiple of
`Shadow.dir`), injectivity, completeness (`double_par`: every double point of γ is a pair of occurrences of one
crossing), and cyclic order (`par_order`, against the accepted `Diagram.visitCoord`, LinkDiagramRecord:181).  The
over/under bits and the signs are those of the polygonal diagram; on the smooth side they read as `Carries.sign x =
sgn det(γ'(par (overVisit x)), γ'(par (underVisit x)))` and `Carries.writhe`, and the generic lemmas
`Carries.sign_eq`, `Carries.writhe_eq` (skeleton 1164, 1168) show they coincide with `D.sign`, `D.writhe`.

This is the one-component analogue of the accepted `SmoothFront.Marking` (FrontSmooth:949: component bijection,
occurrence bijection, `cycBetween`, `twin`, `overBit`, `sgn`) with two differences forced by the objects: (i) a rounded
polygon has vertical edges in general, so it is NOT a `SmoothFront` (field `no_vertical`), and the over rule of fronts
(smaller slope) does not apply — the over/under is a *choice*, which is precisely the polygonal diagram's `overStrand`;
(ii) `Marking` maps occurrences of the smooth object to visits of `S`; here the direction is `D.Γ.Visit → ℝ` because the
smooth side has no independent occurrence type (its double points are characterised by `double_par`).  Both records
answer the same question — "which polygonal Diagram does this smooth curve carry?" — so the front block and the rounding
lane share ONE reading (FR-1: smooth diagrams are read polygonally through their named record).  For cf:lem-curl the
input "C^∞ immersed circle given with an oriented diagram" is `(γ : SmoothRegularLoop, D : Diagram, Carries γ.γ D)`,
and its output needs a new `Carries` onto a diagram with one more crossing — the same vocabulary.

**Here D_ε := D itself.**  Clause (c) asserts that the diagram carried by L_ε has *the same* double points, strands,
over/under, signs and writhe as D; under FR-1 "the same named record" IS the same polygonal diagram, and
cf:thm-carrierfloor(C) reads exactly this ("the rounded diagram and the original polygonal diagram have the same
named record, including the single original component, so rp:record-polynomial gives equal P values", sm-3:4430-4432).
So the preamble field `diagram : Nonempty (Carries (roundedCurve L ε) D)` carries the whole content of "a diagram D_ε
carried by L_ε", and clause (c) is stated as the record-free consequences (below).

### Q3 — the clearance is a named object in the conclusion

`clearance L := ⅓ · sInf (clearanceSet L)`, the printed `ε₀(L) = ⅓ min{η_v, η_e, η_ℓ, η_X}` (sm-3:3819-3828) with the
four finite families of distances as printed: `η_v` corner–corner (Euclidean), `η_e` corner to non-incident closed edge
(`Metric.infDist`, which on `Plane = ℝ×ℝ` is the sup-metric distance, ≤ the Euclidean one, so the separation it gives
is at least as strong; `η_e ≤ 1`-capping is harmless), `η_ℓ` edge lengths, `η_X` corner to double point (over the
accepted polygon-level `Crossing L`, SM/Crossings.lean:15/41, so that `clearance` depends on L alone — printed
"ε₀(L)").  The element `1` implements "min over an empty index set is +∞" (sm-3:3829) without a case split.  The field
`clearance_pos` is the printed "there is a clearance ε₀(L) > 0", and the row's ∀ ε ∈ (0, ε₀) is the binder of every
other field.  The printed existential form (∃ ε₀ > 0, ∀ ε …, ∃ L_ε D_ε …) is the corollary `RoundingData.printed`
(statement file, proved without sorry).

**Why the witnesses are named rather than existential.**  cf:thm-carrierfloor(A) is a statement ABOUT the
construction of this proof ("Round(L,D,ε) = (L_ε, D_ε) … one curve and one diagram at those data"); an existential
row would leave (A) nothing to refer to.  Naming `roundedCurve L ε` and `clearance L` costs nothing in fidelity (the
bundle implies the printed ∃-form) and is what the proof-first architecture computes with anyway.

### Hypotheses (H-1)

Printed: polygon L; D a diagram whose curve is L; turns exist and are nonzero; finitely many double points, all
transversal, none a corner; no corner on a non-incident edge.  Lean: `L : LabelledTuple n`, `3 ≤ n`, `D : Diagram`
with `D.Γ = Shadow.single ⟨n, hn, L⟩` (LinkDiagram:1589), `∀ i, principalTurn L i ≠ 0`.  The accepted `Diagram` requires
`D.Γ.Generic` (LinkDiagram:394): `regular` = "the principal turns exist" (RegularLocus:12/15, `principalAngle_bounds`
RegularPairs:56 gives |ϑ| < π, used at sm-3:3701 "Since 0 < |ϑ_i| < π"); `transverse` = "all transversal";
`tail_off` = "no corner on a non-incident edge" (and, with regularity, "none of them a corner":
`Generic.crossingPoint_mem_interior` LinkDiagram:456); `no_triple`; finiteness is automatic (finitely many edge
pairs).  So the only hypothesis not already in `Diagram` is "nonzero".  No hypothesis is added (no genericity `G1`, no
parent polygon — the printed text insists on this, sm-3:3660-3668 of the CV twin).  Fidelity note: the printed
hypotheses are restated by the reviewer against `Generic`'s fields; the skeleton's unit C lemmas
`regular_of_generic`, `corner_notMem_edge_of_generic`, `crossingPoint_ne_corner_of_generic` are the audit.

### Clause (a) — `ClauseA`

Printed: "L_ε coincides with L outside the union of the discs of radius ε about the corners."  Lean, two conjuncts:
(a-param) on every straight parameter interval `[jEnd k, jStart (k+1)]` the curve is the arclength traversal of the
edge k from `A₁(q_k)` to `A₀(q_{k+1})`: `γ t = A1 k + (Λ t − cumEnd k) • cornerOut k`; (a-set) the trace of L_ε
outside the discs equals the trace of L outside the discs.  (a-set) is the literal sentence; (a-param) is the
parametrised form the construction gives and the consumers use ("Each straight portion contributes zero tangent
increment", sm-3:4393).  Both are discharged by `roundedCurve_straight` (G9) and `trace_eq_outside_discs` (E).

### Clause (b) — `ClauseB`

Printed sentence by sentence → Lean, on the junction interval `[a, b] = [jStart k, jEnd k]` with
`T t = normalize (deriv γ t)` and the printed lift `θ = junctionLift L ε k` (= `θ_u + ϑ_k φ(σ/ℓ_k)`, σ = Λt − cum k):
* "parametrized by arclength": `∀ t, euclideanLength (deriv γ t) = Λ` (constant speed; the period-1 parameter is
  arclength/Λ, so "angular derivative nonzero" is parametrisation-independent).
* "the unit tangent moves … from δ_{i−1}/|δ_{i−1}| to δ_i/|δ_i|": `IsLiftOn T θ a b` (TurnLift:40, the accepted
  lift-on-an-interval), `T a = cornerIn k`, `T b = cornerOut k`.
* "sweeping an arc of length exactly |ϑ_i|": `θ b − θ a = cornerTurn k` (signed, so also the sense);
  "and no more": `∀ t ∈ Icc a b, θ t ∈ uIcc (θ a) (θ b)`.
* "strictly monotonically, in the sense of sgn ϑ_i": `0 < ϑ → StrictMonoOn θ (Icc a b)` and
  `ϑ < 0 → StrictAntiOn θ (Icc a b)`.
* "attaining each direction of that arc at exactly one parameter": `∀ ψ ∈ uIcc (θ a) (θ b), ∃! t, t ∈ Icc a b ∧ θ t = ψ`
  AND `InjOn T (Icc a b)` (directions, not just angles; |ϑ| < π makes them equivalent).
* "the unit-tangent map is an immersion on the open junction arc … its angular derivative is nonzero at every interior
  parameter": `ContDiff ℝ ∞ θ ∧ ∀ t ∈ Ioo a b, deriv θ t ≠ 0`.
* "at the two ends it and all its derivatives vanish": `∀ m ≥ 1, iteratedDeriv m θ a = 0 ∧ iteratedDeriv m θ b = 0`.
* "the junction meeting the straight edges flat to infinite order": `∀ m ≥ 2, iteratedDeriv m γ a = 0 ∧ iteratedDeriv m γ b = 0`
  (the straight edges have vanishing derivatives of order ≥ 2; the first derivative is matched by `T a`, `T b`).

The printed commentary (why both clauses are exported) is honoured: monotonicity and the derivative are separate
conjuncts.  The lift is the explicit printed formula, not an existential — stronger and what carrierfloor(B) needs
("Concatenating straight-part arguments with the junction lifts supplied by (b)").

### Clause (c) — `ClauseC`

"same double points": `{p | ∃ s t, IsDoublePt γ s t ∧ p = γ s} = range D.Γ.crossingPoint`; "with the same strands":
for every carrying record, each occurrence is met on its strand's segment running in the strand's direction (this is
`Carries.par_dir` + `mem_seg`; stated so that it is visible in the clause); "the same over/under assignment": D_ε = D
(FR-1) — the over branch at x is the branch through `par (overVisit x)`; "and hence the same crossing signs and the
same writhe": `∀ rec, rec.sign x = D.sign x` and `rec.writhe = D.writhe`.  Quantifying over every carrying record
(rather than the constructed one) keeps the clause record-free and is provable generally (`Carries.sign_eq` from
`par_dir` and bilinearity of `det`).

### Clause (d) — `ClauseD`

`∀ c : ClosedC1Curve, c.γ = γ → c.rot = rotationNumber L`: rot of cf:def-turning for any closed-C¹-regular structure on
the function (avoids a dependent proof term in the statement), equal to the accepted lem:rot value `rotationNumber`
(RotationNumber:10).  Proof by the accepted `rot_eq_rotationNumber_of_rounding` (TurnLift:314, cf:lem-turnlift
(iii-a)) — the printed argument verbatim ("the total turning is Σ ϑ_i … rotation is 1/2π times total turning,
cf:lem-turnlift(iii), which is also the value assigned to L by lem:rot").

### Clause (e) — `ClauseE`

Discs `roundDisc (L k) ε` (round, Euclidean — the printed "disc of radius ε about q_i"; `IsDisc`, LinkMoves:100, the
accepted clean-disc vocabulary, proved for round discs in `isDisc_roundDisc`).  Conjuncts: `IsDisc`; `q_k ∈ interior`
("about each corner", as `GeomRounding.center`); pairwise disjoint; disjoint from non-incident edges; contains no
double point of L (`Crossing L`, polygon-level); meets the arriving edge exactly in `{q − s u : 0 ≤ s ≤ ε}` and the
leaving edge exactly in `{q + s v : 0 ≤ s ≤ ε}`; contains the junction arc (`∀ t ∈ Icc a b, γ t ∈ D_k`); the junction arc is
ALL of the curve in the disc (`∀ t ∈ Ico 0 1, γ t ∈ D_k → t ∈ Icc a b`) and is embedded (`InjOn γ (Icc a b)`) — the last
two are the consumer's "a disc meeting the diagram in one embedded arc" (sm-3:3697-3699), which the printed proof
establishes (injectivity sm-3:3808-3811; the discs meet nothing else sm-3:3835-3840).

### Recorded fidelity readings (to be cited in the review)

* **R-1 (FR-1 for the rounding lane).** D_ε is the polygonal `Diagram D` carried through `Carries`; "over/under
  assignment" of the smooth diagram = D's `overStrand`.  Same reading as the front block's `Marking`.
* **R-2 (named witnesses).** The bundle is about `roundedCurve L ε` / `clearance L`; the printed ∃-form is a proved
  corollary.  Justified by cf:thm-carrierfloor(A).
* **R-3 (metric for η_e).** `Metric.infDist` is in the sup metric; only used as a lower bound for the Euclidean
  distance, so the clearance is (slightly) smaller than the printed one — still "a clearance".  The cap `1` in
  `clearanceSet` is the printed "+∞ for an empty family".
* **R-4 (period-1 parameter).** The printed junction is by arclength σ ∈ [0, ℓ]; the row uses arclength/Λ so that L_ε is
  a `SmoothLoop` (period 1).  Constant speed Λ is exported in (b).
* **R-5 (seam).** The parameter 0 of L_ε is `A₀(q_0)` (start of the junction at the corner `L 0`); the traversal
  coordinate of D starts at the corner `L 0`.  No crossing lies in the ε-piece between them, so `par_order` (cyclic
  order of occurrences) holds with the plain `<`.

---

## 2. The construction and the proof-first shortcuts

Printed objects → definitions (statement §3): `profile := Real.smoothTransition` (Mathlib
Analysis/SpecialFunctions/SmoothTransition.lean:146 — definitionally `f(x)/(f(x)+f(1−x))` with
`f = expNegInvGlue`, :39, the printed φ and f); `junctionAngle θ₀ ϑ ℓ σ = θ₀ + ϑ φ(σ/ℓ)`; `junctionCurve A₀ θ₀ ϑ ℓ σ
= A₀ + ∫₀^σ (cos, sin)(junctionAngle)` (componentwise `intervalIntegral`, defined for all σ ∈ ℝ: straight before 0 and
after ℓ automatically, since φ is constant there); `junctionMean`, `junctionLength ε θ₀ ϑ = ε|u+v|/|m(φ)|` (printed
sm-3:3764-3771); corner data `cornerIn/cornerOut/cornerArg/cornerTurn/cumArg/A0/A1/edgeLen/arcLen`; arclength
bookkeeping `cum` (recursive), `cumEnd`, `total = Λ`; the global tangent angle
`globalAngle L ε σ = θ_{u_0} + Σ_k ϑ_k φ((σ − cum k)/ℓ_k)`; `roundedArc L ε σ = A₀(q_0) + ∫₀^σ (cos, sin)(globalAngle)`;
`roundedCurve L ε t = roundedArc L ε (Λ · fract t)`.

Design choices that make every clause a computation:

1. **One global smooth angle instead of piecewise gluing.**  `globalAngle` is a finite sum of smooth functions of σ on
   all of ℝ (each `φ((σ − cum k)/ℓ_k)` is C^∞ on ℝ), so `roundedArc` is C^∞ on ℝ by FTC (`hasDerivAt_primitive`,
   `contDiff_primitive`) with unit speed (`unitDir` has length 1): regularity is free.  On the zone of corner k,
   `[cum k, cum (k+1)]`, the earlier profiles are 1 and the later ones 0, so `globalAngle = junctionAngle (cumArg k) ϑ_k ℓ_k
   (σ − cum k)` (G2, a `Finset.sum_range_succ` split) and `roundedArc = junctionCurve (A0 k) … (σ − cum k)` (G5: same
   value at `cum k` by induction — `junctionCurve_end` + `A1_add_straight` — and same derivative).  Only ONE gluing point
   remains, the seam t ∈ ℤ, where `roundedCurve` agrees near the seam with the junction curve at q_0 extended backwards
   (G7/G8: `roundedArc_seam`, `roundedCurve_eventuallyEq_seam`); smoothness at the seam is `ContDiffAt.congr_of_eventuallyEq`.
2. **Endpoint by symmetry, in vector form.**  `junctionMean θ₀ ϑ = (∫₀¹ cos(ϑ(φ−½))) • unitDir(θ₀+ϑ/2)` (J1, from
   `profile_symm` and the substitution t ↦ 1−t) with coefficient ≥ cos(ϑ/2) > 0 (|ϑ(φ−½)| ≤ |ϑ|/2 < π/2), and
   `u + v = 2cos(ϑ/2) • unitDir(θ₀+ϑ/2)` (J2).  Hence `ℓ = 2ε cos(ϑ/2)/∫cos(…)`, `0 < ℓ ≤ 2ε` (J3), and
   `junctionCurve ℓ = A₀ + ℓ m(φ) = A₀ + ε(u+v)` (J6, `intervalIntegral.integral_comp_div`).
3. **Disc containment without the cone inequalities.**  In the bisector frame (w = unitDir(θ₀+ϑ/2), z = w⊥):
   x_w(σ) = −ε cos(ϑ/2) + ∫₀^σ cos β is strictly increasing (cos β ≥ cos(ϑ/2) > 0) from −ε cos(ϑ/2) to +ε cos(ϑ/2) (its value
   at ℓ is read off J6), so |x_w| ≤ ε cos(ϑ/2); x_z(σ) = ε sin(ϑ/2) + ∫₀^σ sin β with sgn(ϑ)·∫₀^σ sin β ≤ 0 (β has the sign
   of ϑ(φ−½): negative then positive for ϑ > 0, symmetric, and ∫₀^ℓ sin β = 0 is again read off J6) and
   |∫₀^σ sin β| ≤ ℓ|sin(ϑ/2)| ≤ 2ε|sin(ϑ/2)|, so |x_z| ≤ ε|sin(ϑ/2)|.  Then |γ − q|² = x_w² + x_z² ≤ ε² (J7); strict inside
   (J7') because x_w is strictly monotone; injectivity of the junction on all of ℝ from x_w (J8); outside [0, ℓ] the
   straight continuation is outside the disc (J9).  The printed triangle T_i is not needed (the disc is what (e) asks).
4. **Closure by telescoping.**  `roundedArc Λ = A0 0` from G5 at k = n−1 and `A1_add_straight` at k = n−1 (with
   `(n : ZMod n) = 0`), i.e. Σ_k [ε(u_k+v_k) + (|δ_k|−2ε)v_k] = Σ_k δ_k + ε Σ_k (u_k − u_{k+1}) = 0.
5. **Angle bookkeeping through `unitDir`.**  `unitDir (cumArg k) = cornerIn k` for all k (C: induction with
   `principalAngle_coe_angle` RotationNumber:13 + `Real.Angle.angle_eq_iff_two_pi_dvd_sub`), and
   `cumArg n = θ_{u_0} + 2π rot(L)` (`two_pi_mul_rotationNumber` TurnLift:283, `rotationNumber_integer`
   RotationNumber:45) — so the tangent at the seam matches.
6. **Profile facts elementary.**  Strict monotonicity on [0,1] needs no derivative: for s < t,
   f(s)f(1−t) < f(t)f(1−s) ⇔ 1/t + 1/(1−s) < 1/s + 1/(1−t) (P2).  The derivative formula (P3) comes from Mathlib's
   `expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul` with p = 1 (`f' = x⁻² f` everywhere) and the quotient rule;
   positivity on (0,1) is termwise.  Flatness at the ends (P4) is the continuity argument: a C^∞ function constant on
   one side of a has `iteratedDeriv m` vanishing there and continuous, hence 0 at a (helper
   `iteratedDeriv_eq_zero_of_const_left/right`; affine version for the curve, order ≥ 2).  No Taylor/Faà di Bruno.
7. **(c) by containment.**  A double point of L_ε cannot involve a junction parameter: the junction at q_k is inside D_k,
   D_k meets the rest of L_ε only at A₀, A₁ (`roundedCurve_mem_roundDisc_iff`), and the junction is injective; so both
   parameters are on open straight parts, the point lies on two edges of L off the ε-ends; adjacent edges meet only at
   their common corner (`regular_adjacent_meet`, SM/CS3.lean:84, accepted), so the edges are remote and the point is a
   `Crossing L` = a crossing of D (`Shadow.singleCrossingEquiv` LinkDiagram:1661, `single_crossingPoint` :1703), whose
   two occurrences have exactly these parameters (`edgePoint_injective` Crossings:88).  Conversely each occurrence gives
   the parameter `crossingPar v = (cumEnd j + τ|δ_j| − ε)/Λ` (τ = `Diagram.crossingParam`, LinkDiagram:1413), on the
   straight part because the crossing point is ≥ 3ε₀ > ε from both ends of its edge (η_X).

---

## 3. Accepted declarations used (grep-verified 2026-09-14, work/lean)

| declaration | file:line | role |
|---|---|---|
| `SmoothLoop`, `SmoothLoop.toClosedC1Curve` | SM/FrontSmooth.lean:144, :205 | the C^∞ closed curve class; bridge to rot |
| `SmoothFront.Marking` (model for `Carries`) | SM/FrontSmooth.lean:949 | FR-1 analogue |
| `ClosedC1Curve`, `tangentLoop`, `rot`, `normalize`, `euclideanLength_normalize` | SM/TurningNumber.lean:241, :264, :274, :226, :228 | rot of cf:def-turning; unit tangent |
| `IsLiftOn`, `IsLiftOn.increment_eq`, `rot_eq_rotationNumber_of_rounding`, `two_pi_mul_rotationNumber`, `sum_range_natCast_eq_sum_zmod`, `normalize_smul_of_pos` | SM/TurnLift.lean:40, :55, :314, :283, :291, :385 | clause (b) lifts, clause (d), sign transport |
| `Plane`, `det`, `edge`, `edgeSegment`, `edgeInterior`, `incident` | SM/Polygon.lean:13, :16, :49, :54, :57, :60 | polygon vocabulary |
| `planeComplex`, `planeDot`, `euclideanLength` | SM/EuclideanPlane.lean:9, :27, :29 | Euclidean geometry of the plane |
| `Regular`, `principalTurn`, `principalAngle`, `principalAngle_bounds` | SM/RegularLocus.lean:12, :15; SM/RegularPairs.lean:54, :56 | turns exist, |ϑ| < π |
| `rotationNumber`, `principalAngle_coe_angle`, `rotationNumber_integer`, `rotation_number` | SM/RotationNumber.lean:10, :13, :45; SM/RotationTheorem.lean:14 | lem:rot value; angle bookkeeping |
| `IsCrossing`, `Crossing`, `crossingPoint`, `edgePoint_injective` | SM/Crossings.lean:12, :15, :41, :88 | double points of L (clearance, (e)) |
| `PolyComp`, `Shadow`, `Shadow.seg`, `Shadow.dir`, `Shadow.crossingPoint`, `Shadow.Generic`, `Generic.common_point_unique`, `Generic.crossingPoint_mem_interior`, `Diagram`, `Diagram.sign`, `Diagram.writhe`, `overVisit`, `underVisit`, `crossingParam`, `visitPt`, `Shadow.single`, `single_adjacent_iff`, `single_incidentTail_iff`, `single_seg`, `single_dir`, `singleCrossingEquiv`, `single_crossingPoint` | SM/LinkDiagram.lean:61, :83, :99, :106, :372, :394, :414, :456, :490, :552, :577, :597, :600, :1413, :1435, :1589, :1614, :1622, :1630, :1636, :1661, :1703 | the polygonal diagram class and its one-component form |
| `Diagram.visitCoord`, `cycBetween` | SM/LinkDiagramRecord.lean:181, :78 | cyclic order of occurrences |
| `IsDisc`, `isDisc_closedBall` | SM/LinkMoves.lean:100, :104 | clean-disc vocabulary |
| `regular_adjacent_meet` | SM/CS3.lean:84 (namespace SM) | adjacent edges meet only at the corner (unit D) |
| `intersection_parameters_unique` | SM/Segment.lean:55 | transverse segments meet once |
| Mathlib `expNegInvGlue`, `Real.smoothTransition`, `.contDiff`, `.monotone`, `.zero_of_nonpos`, `.one_of_one_le`, `.pos_of_pos`, `.lt_one_of_lt_one`, `expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul` | Analysis/SpecialFunctions/SmoothTransition.lean:39, :146, :206, :223, :168, :161, :197, :194, :100 | the printed φ and its four properties |
| Mathlib `intervalIntegral.integral_hasDerivAt_right`, `integral_comp_div`, `sum_integral_adjacent_intervals`, `strictMonoOn_of_deriv_pos`, `intermediate_value_Icc`, `Real.Angle.angle_eq_iff_two_pi_dvd_sub`, `Complex.norm_mul_exp_arg_mul_I`, `Set.Nonempty.csInf_mem`, `Filter.EventuallyEq.iteratedDerivWithin_eq`, `ContDiff.continuous_iteratedDeriv` | FundThmCalculus:725; IntervalIntegral/Basic:1117; Deriv/MeanValue:375; … | analysis toolbox |

Nothing accepted is duplicated: no new rot, no new lift notion, no new disc notion, no new polygonal diagram; the only
new classes are `SmoothRegularLoop` (a one-field extension) and `Carries` (the one-component carrying record).

---

## 4. The chain (exact statements in Skeleton_B.lean; line numbers of that file)

Notation: `h : Admissible C ε` bundles `gen : (Shadow.single C).Generic`, `turn : ∀ i, principalTurn C.P i ≠ 0`,
`pos : 0 < ε`, `lt : ε < clearance C.P` (skeleton 725).  `mkSingle C gen ovr mem : Diagram := ⟨Shadow.single C, gen, ovr, mem⟩` (718).

### Unit P — profile (469-548), ~350 lines
| lemma | statement | note |
|---|---|---|
| `profile_symm` (490) | `profile (1 - t) = 1 - profile t` | algebra on the quotient |
| `profile_strictMonoOn` (494) | `StrictMonoOn profile (Icc 0 1)` | §2.6 |
| `hasDerivAt_expNegInvGlue` (498) | `HasDerivAt expNegInvGlue ((t⁻¹)^2 * expNegInvGlue t) t` | Mathlib p = 1 |
| `hasDerivAt_profile` (503) | quotient rule, printed formula | |
| `deriv_profile_pos` (510) | `0 < t → t < 1 → 0 < deriv profile t` | termwise positivity |
| `iteratedDeriv_eq_zero_of_const_left/right` (514, 518) | C^∞ g constant on `Iio a`/`Ioi a` ⇒ `iteratedDeriv m g a = 0` (m ≥ 1) | continuity of `iteratedDeriv m g` (`ContDiff.continuous_iteratedDeriv`), vanishing on an open half-line (`Filter.EventuallyEq.iteratedDerivWithin_eq` with `s = univ`), closure |
| `iteratedDeriv_eq_zero_of_affine_left/right` (524, 528) | affine on a half-line ⇒ order ≥ 2 vanish | same, one derivative down |
| `iteratedDeriv_profile_zero/one` (533, 537) | PROVED from the helpers | |
| `hasDerivAt_primitive` (543) | FTC for `∫₀^x f`, f continuous | `integral_hasDerivAt_right` |
| `contDiff_primitive` (548) | C^∞ f ⇒ C^∞ primitive | `contDiff_succ_iff_deriv`/`contDiff_infty_iff_deriv` |

### Unit J — one junction (557-706), ~900 lines (split J1 = 557-680 geometry/endpoint, J2 = 689-706 containment/injectivity + the angle clauses 571-610)
Key statements (variables `θ₀ ϑ ε ℓ`, `A₀`):
* `junctionAngle_strictMonoOn/StrictAntiOn` (581/584), `junctionAngle_mem_uIcc` (588), `junctionAngle_existsUnique` (592),
  `deriv_junctionAngle_ne_zero` (596), flatness PROVED from P4 (600/605), `junctionTangent_injOn` (610).
* `hasDerivAt_junctionCurve` (614): `HasDerivAt (junctionCurve A₀ θ₀ ϑ ℓ) (junctionTangent θ₀ ϑ ℓ σ) σ`;
  `contDiff_junctionCurve` (621); `junctionCurve_of_nonpos` (626): `= A₀ + σ • unitDir θ₀`; `junctionCurve_of_le` (630);
  curve flatness PROVED (635/640).
* `junctionMean_eq` (651), `cos_half_le_junctionMean_coeff` (657), `unitDir_add_unitDir` (663),
  `euclideanLength_unitDir_add` (666), `junctionLength_pos/le` (670/674),
  `junctionCurve_end` (679): `junctionCurve A₀ θ₀ ϑ ℓ ℓ = A₀ + ε • (unitDir θ₀ + unitDir (θ₀ + ϑ))` for `ℓ = junctionLength ε θ₀ ϑ`.
* `junctionCurve_mem_roundDisc` (689): `σ ∈ Icc 0 ℓ → junctionCurve … σ ∈ roundDisc (A₀ + ε • unitDir θ₀) ε`;
  `junctionCurve_lt_of_mem_Ioo` (694); `junctionCurve_notMem_roundDisc` (700); `junctionCurve_injective` (706).

### Unit C — corner data, clearance, discs (718-868), ~600 lines
* H-1 audit from `gen`: `regular_of_generic` (735, PROVED), `corner_notMem_edge_of_generic` (739),
  `corner_injective_of_generic` (743), `crossingPoint_ne_corner_of_generic` (747), `crossingPoint_mem_edgeInterior_of_generic` (752).
* angles: `abs_cornerTurn_lt_pi` (760), `unitDir_cornerArg` (763), `unitDir_add_cornerTurn` (768), `cornerIn_succ` (771),
  `unitDir_cumArg` (779), `cumArg_count` (786): `cumArg C.P C.k = cornerArg C.P 0 + 2π rotationNumber C.P`.
* lengths: `edgeLen_pos` (789), `edge_eq_edgeLen_smul` (791), `A1_add_straight` (796): `A1 k + (|δ_k| − 2ε) • cornerOut k = A0 (k+1)`.
* Euclidean length as a norm: `euclideanLength_add_le` (800), `euclideanLength_sub_rev` (803), `dist_le_euclideanLength` (807).
* clearance: `clearanceSet_finite` (809), `clearanceSet_pos` (816), `clearance_pos` (819), `three_clearance_le` (821) and the
  four PROVED specialisations (823-834).
* discs: `isDisc_roundDisc` (839), `mem_interior_roundDisc` (841), `roundDisc_disjoint` (848), `roundDisc_disjoint_edge` (852),
  `crossingPoint_notMem_roundDisc` (857), `roundDisc_inter_edge_in/out` (862/868).

### Unit G — global assembly (882-1045), ~800 lines
`arcLen_pos/le`, `straight_pos` (PROVED), `cum_*`, `total_pos`, `cumEnd_lt_total`; `globalAngle_zone` (918),
`globalAngle_zone_left` (924), `globalAngle_of_nonpos/of_total_le` (929/931), `contDiff_globalAngle` (934),
`hasDerivAt_roundedArc` (936), `contDiff_roundedArc` (939), `roundedArc_zone` (944), `roundedArc_cum` (949),
`roundedArc_total` (952), `roundedArc_seam` (956), `roundedCurve_periodic` (962, PROVED), `roundedCurve_eq_arc` (966,
PROVED), `roundedCurve_eventuallyEq_arc/seam` (971/975), `contDiff_roundedCurve` (980), `hasDerivAt_roundedCurve` (982),
`deriv_roundedCurve` (986, PROVED), `deriv_roundedCurve_ne_zero` (990), `euclideanLength_deriv_roundedCurve` (992),
`normalize_deriv_roundedCurve` (995), `jStart_*`/`jEnd_*` (1000-1016, PROVED), `roundedCurve_junction` (1020),
`roundedCurve_straight` (1026), `tangent_junction` (1036), `tangent_straight` (1040), `cover` (1045).

### Unit E — clauses (a) (b) (d) (e) (1060-1094), ~600 lines
`roundedCurve_junction_mem_roundDisc` (1060), `roundedCurve_straight_notMem_roundDisc` (1066),
`roundedCurve_mem_roundDisc_iff` (1072), `roundedCurve_injOn_junction` (1076), `trace_eq_outside_discs` (1080),
`clauseA` (1084, PROVED from G9 + trace), `clauseB` (1087), `clauseD` (1092), `clauseE` (1094).

### Unit D — the carried diagram and (c) (1108-1185), ~700 lines
`crossingPar` (1108, def), `crossingPar_mem` (1116), `crossingPar_mem_straight` (1119), `roundedCurve_crossingPar` (1123),
`deriv_roundedCurve_crossingPar` (1127), `crossingPar_injective` (1131), `crossingPar_order` (1135),
`double_eq_crossingPar` (1145), `carries` (1150, PROVED record), `Carries.sign_eq` (1164), `Carries.writhe_eq` (1168,
PROVED), `Carries.mem_seg` (1175, PROVED), `doublePoints_eq_crossingPoints` (1181), `clauseC` (1185, PROVED).

### Unit R — the row (1201-1255), PROVED
`cf_lem_rounding : RoundingData`: destructure `D`, `subst` the shadow equation, build `Admissible`, apply the unit
theorems (with `(C := ⟨n, hn, L⟩)` explicit — needed, otherwise the unifier unfolds `clearance` while solving
`?C.P =?= L` and times out).

Sorry count: 96 (`by sorry`), 113 declarations transitively depend on a sorry.  Estimated total when filled:
~4,000 lines of new Lean (P 350, J 900, C 600, G 800, E 600, D 700, + the 460-line statement).

---

## 5. Unit split for parallel provers

All provers work on a private copy of Skeleton_B.lean (`work/drafts/rounding/U_<unit>.lean`), keep every statement
byte-identical, fill their own unit's sorries, and may use the other units' sorried lemmas as black boxes.  Order of
launch (dependencies only through statements, so all can run in parallel; the merge is by concatenation):

| unit | scope (skeleton lines) | may assume | est. lines / hours | difficulty |
|---|---|---|---|---|
| **P** | 469-548 | Mathlib only | 350 / 3-4 h | low-medium (the `iteratedDeriv` helpers are the only subtle part: use `Filter.EventuallyEq.iteratedDerivWithin_eq` with `s = univ` + `iteratedDerivWithin_univ`, then continuity/closure) |
| **J1** | 557-680 (unitDir lemmas, angle clauses, curve derivative/straightness, mean, length, endpoint) | P | 500 / 5-6 h | medium (integral substitution `integral_comp_div`; `junctionMean_eq` by the reflection t ↦ 1−t: `intervalIntegral.integral_comp_sub_left`) |
| **J2** | 689-706 (containment, strictness, outside, injectivity) | P, J1 | 450 / 5-6 h | medium-high (the x_w / x_z estimates of §2.3; state the frame lemmas `planeDot (junctionCurve σ − q) w = …` first) |
| **C** | 735-868 | none (polygon library) | 600 / 5-6 h | medium (clearance positivity through `Set.Nonempty.csInf_mem`; `Metric.infDist_pos` via compactness `isCompact_edgeSegment`-style lemma — check SM/Segment*.lean / GenericTopology.lean for an accepted compactness of `edgeSegment`; `isDisc_roundDisc` through the CLE `Complex.equivRealProdCLM`) |
| **G** | 884-1045 | P, J1, C | 800 / 7-8 h | medium-high (bookkeeping; `roundedArc_zone` by `constant_of_has_deriv_right_zero` on the difference; the seam by `eventuallyEq`) |
| **E** | 1060-1094 | P, J1, J2, C, G | 600 / 5-6 h | medium (clause (b) is transport of J's angle lemmas along the affine map t ↦ Λt − cum k: note `junctionLift_eq` is `rfl`; (d) is the accepted `rot_eq_rotationNumber_of_rounding` with `a := jStart`, `b := jEnd`) |
| **D** | 1116-1181 | C, G, E (`roundedCurve_mem_roundDisc_iff`, `roundedCurve_injOn_junction`, `cover`, `roundedCurve_straight`) | 700 / 7-8 h | high (the `subst`-free shape is already arranged: everything is on `mkSingle C gen ovr mem`, strands are `⟨0, j⟩`, use `single_seg`/`single_dir`/`single_adjacent_iff`/`singleCrossingEquiv`/`single_crossingPoint`) |

Critical path: P → J1 → J2 → E (and G) → D; with 7 provers in parallel ~8 h wall time, ~40-45 agent-hours.

---

## 6. Risks

1. **`iteratedDeriv` helpers (P4).**  Mathlib has `Filter.EventuallyEq.iteratedDerivWithin_eq`, not a bare
   `iteratedDeriv` congruence; go through `iteratedDerivWithin_univ`.  Fallback: prove `iteratedDeriv m g = 0` on
   `Iio a` by induction with `iteratedDeriv_succ` and `deriv` of a locally constant function
   (`Filter.EventuallyEq.deriv_eq`), then continuity.  Low risk, ~80 lines.
2. **`contDiff_primitive`.**  Needs `ContDiff ℝ ∞ (fun x => ∫₀^x f)`: by `contDiff_infty_iff_deriv` (or
   `contDiff_succ_iff_deriv` + `contDiff_all_iff_nat`) with `deriv = f` from FTC.  `IntervalIntegrable` of a continuous
   function is `Continuous.intervalIntegrable`.  Low risk.
3. **Disc containment (J2).**  The estimate of §2.3 needs `∫₀^σ sin β ≤ 0`-type inequalities from pointwise sign
   information (`intervalIntegral.integral_nonpos_of_forall_le`-style lemmas) and `∫₀^ℓ sin β = 0` read off
   `junctionCurve_end` (its second frame coordinate).  Medium risk of length, not of truth; the printed proof's
   triangle argument is the fallback and is longer.
4. **Compactness of `edgeSegment`** for `Metric.infDist_pos_iff_notMem_closure` (name in this Mathlib: check
   `Metric.infDist_pos_iff_notMem_closure` / `IsClosed.notMem_iff_infDist_pos`).  If no accepted lemma gives
   `IsCompact (edgeSegment L j)`, prove it as the image of `Icc 0 1` under the continuous `edgePoint` (10 lines).
5. **`Admissible.lt` is used as `ε < ε₀ ≤ ⅓ η`.**  Several places need `2ε < 3ε₀ ≤ η` (disc disjointness) — fine since
   ε₀ > 0; and `ε < |δ_k| − ε` for the straight parts — from `3ε₀ ≤ |δ_k|`.  Arithmetic only.
6. **`par_order` (D2).**  `visitCoord v = traversalKey (visitPt v).2 = j.val + τ` (LinkDiagramRecord:181, Traversal:17)
   vs `crossingPar v = (cumEnd j + τ|δ_j| − ε)/Λ`: both lexicographic in `(j.val, τ)`; needs `cumEnd` strictly
   increasing (G) and, inside an edge, `τ ↦ cumEnd j + τ|δ_j| − ε` increasing with range inside
   `(cumEnd j, cum (j+1))`.  Medium bookkeeping.
7. **Unifier timeouts with `PolyComp` projections.**  Seen once (row assembly); cured by explicit `(C := …)`.  Provers
   should keep `C` explicit when applying unit lemmas at `⟨n, hn, L⟩`.
8. **Fidelity review.**  The named-witness form (R-2) and FR-1 (R-1) must be cited in the reviewer brief; the printed
   ∃-form is available as `RoundingData.printed` to show equivalence of strength.  The metric remark R-3 should be
   stated in the brief.  If the judge prefers an existential bundle, `RoundingData.printed`'s statement is a drop-in
   alternative row (same clauses, same definitions) with no change to the chain.

---

## 7. Coherence with the front block and the consumers

* Front block (SM/FrontSmooth.lean): `SmoothLoop` reused as is; `SmoothRegularLoop` is the regular case (a front
  component with no cusps is one: `SmoothFront.toClosedC1Curve` :784 shows the same bridge).  `Carries` is the
  one-component, choice-over/under counterpart of `Marking`; a later "smooth diagram" row can define
  `SmoothDiagram := (γ : SmoothRegularLoop) × (D : Diagram) × Carries γ.γ D` and both `Marking` (for cusp-free fronts)
  and `carries` (for rounded polygons) produce instances.
* cf:thm-carrierfloor(A): `Round(L, D, ε) := (roundedCurve L ε, D)` with `carries` the record; determinacy is
  definitional.  (B): the lifts `junctionLift L ε k`, their positive derivative (`ClauseB`), the straight tangents
  (`tangent_straight`), the subdivision `jStart/jEnd` are exactly its inputs.  (C): `Carries.writhe_eq`, `ClauseD`,
  `ClauseE` (pairwise disjoint discs containing no crossing) are the facts it cites.
* cf:lem-curl: input `(γ : SmoothRegularLoop, D, Carries γ.γ D)`; the disc vocabulary `roundDisc`/`IsDisc` and the
  double-point predicate `IsDoublePt` are reusable; its "positively turning arc" hypothesis is `deriv θ > 0` on a lift,
  the form `ClauseB` exports.
