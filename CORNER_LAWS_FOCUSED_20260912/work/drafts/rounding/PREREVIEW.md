# PRE-REVIEW — cf:lem-rounding fixed statement (Rounding_statement_FINAL.lean)

Independent auditor, 2026-09-14. Not the formal fidelity review. Object: `work/drafts/rounding/Rounding_statement_FINAL.lean`
(442 lines; `cd work/lean && lake env lean ../drafts/rounding/Rounding_statement_FINAL.lean` → 0 errors, one
`sorry` warning at :437 = the row `SM.cf_lem_rounding`). Printed statement: `reference/SM/sm-3-statesum.tex:3644-3700`;
proof skimmed 3701-3869 for the objects only. Decision record read: `PLAN_FINAL.md` (§1 model, §6 FR-R1..R7).
Accepted definitions re-read in `work/lean/SM/` (`SmoothLoop`, `SmoothLoop.toClosedC1Curve`, `IsLiftOn`,
`ClosedC1Curve`/`tangentLoop`/`rot`, `normalize`, `euclideanLength`, `det`, `edge`/`edgeSegment`/`incident`,
`Regular`/`principalTurn`/`principalAngle_bounds`, `rotationNumber`, `PolyComp`, `Shadow.single`,
`Shadow.Generic` (`regular`, `tail_off`, `transverse`, `no_triple`), `IncidentTail`, `Adjacent`, `Diagram.sign`/`writhe`/
`overVisit`/`underVisit`, `crossingPoint`, `crossingParam`, `visitPt`, `visitCoord` (= `traversalKey` = `edge.val + param`),
`cycBetween`, `twin`, `IsDisc`, `Shadow.single_generic_of`) and Mathlib `Real.smoothTransition` (pin 85e3a25e).

## 0. Verdict

**Jointly satisfiable; no blocking issue found.** `PolygonDiagram C`, `Carried Lε D.toDiagram`, `RoundingWitness C D ε`
and the bundle `RoundingData` admit a common model — the printed construction — and no field combination is
provably contradictory under the row's hypotheses (`Generic`, all principal turns nonzero, `0 < ε < ε₀`). The one
"contradiction" present is the intended one: `RoundingWitness C D ε` is EMPTY when some `principalTurn C.P j = 0`
(§1.5) or when `ε ≤ 0`; both are excluded by the hypotheses of `exists_clearance`, so this mirrors the printed
"nonzero" hypothesis rather than defeating the theorem. The Rolle-type trap that hit an earlier rounding notion
(open clean interval vs. a class forcing equal endpoint values) does not recur: the endpoint angles differ exactly
when the turn is nonzero, the immersion clause is on the OPEN arc, and flatness at the ends is compatible with it.

Fidelity: every printed sub-clause of (a)-(e) has a field (§2.1). Fields beyond the printed text are those of
FR-R3/FR-R4 plus a handful not explicitly listed there (§2.2, non-blocking). Nothing makes the row trivially
true: the theorem content is `exists_clearance`; the clause fields of `RoundingData` are projections by design
(FR-R5) and are the fixed content only through the `RoundingWitness` field list (§3).

## 1. Non-vacuity, structure by structure

### 1.1 `PolygonDiagram C` (input)
`generic : (Shadow.single C).Generic`, `overStrand`, `over_mem`. Inhabited for polygons with and without crossings:
`Shadow.single_generic_of` (LinkPositiveLift.lean) builds `Generic` from label-level facts, and `overStrand` is
free (vacuous with no crossing). Concrete instances with all turns nonzero: any convex triangle (turns
116.6°, 135°, 108.4° for (0,0),(3,0),(1,2)); the figure-eight quadrilateral (0,0),(2,2),(2,0),(0,2) with one
transverse double point (1,1), turns ±135°, rot 0; an octagon with two crossings, rot −1 (numeric check §1.6).
So the hypotheses of `exists_clearance` are satisfiable — no vacuous theorem. `no_triple` is an extra hypothesis
relative to the printed lemma text (FR-R3); it is genuinely used (it is what makes `Carried.τ_inj` provable:
without it two crossings could share a point on one strand and get the same `τ`), and it is part of the accepted
class "oriented diagram" that the printed sentence "let D be an oriented diagram" names.

### 1.2 `SmoothRegularLoop`
`SmoothLoop` (C^∞, period 1) + `regular`. `toClosedC1Curve` is the accepted bridge; `rot` is unique. Fine.

### 1.3 `Carried γ X` — transversality, cyclic order, sign consistency
- `one : X.Γ.c = 1` — `rfl` for `Shadow.single C` (the skeleton's `roundedCarried` uses `one := rfl`).
- `τ_mem`, `τ_inj`, `τ_eval`, `doubles`: the construction puts occurrence `v` at
  `τ v = b j + (crossingParam·|δ_j| − ε)/Λ` with `j = label v`; distinct visits on one strand have distinct
  `crossingParam` (`Generic.crossingPoint_injective`, i.e. `no_triple`); `doubles` needs the rounded curve to be
  injective on `[0,1)` except at crossings — junction arcs embedded and in pairwise disjoint discs, straight
  parts outside all discs, straight–straight coincidences are the polygon's crossings (transversality + `tail_off`
  exclude corners on non-incident edges). Consistent.
- `transverse`: velocities on straight parts are positive multiples of `edge j`; `Generic.transverse` gives
  `det ≠ 0`. Consistent.
- `order` (bi-implication of `cycBetween`): `visitCoord v = (label v).val + crossingParam v` (LinkDiagram.lean:1435
  `visitPt`, Traversal.lean:17 `traversalKey`), lexicographic in (edge, parameter); `τ` is lexicographic in the same
  pair because `b j < τ v < a (j+1) < b (j+1)`. A strictly increasing map on a finite set of reals preserves
  `cycBetween` (each disjunct is a chain of two strict inequalities), and the cut points (`0 ↔ A₀(q₀)`, `0 ↔ P 0`)
  have no occurrence between them (crossings lie > 3ε from every corner). When two of `v, w, z` coincide both
  sides are False (`τ_inj`, `visitCoord_injOn`). Consistent.
- `sign_eq` vs `X.sign x = sign det(dir over, dir under)`: with `γ'(τ v) = r_v • edge (label v)`, `r_v > 0`,
  `det` scales by `r_o r_u > 0`; signs agree. Consistent with `RoundingWitness.same_strand_dir`.

### 1.4 `RoundingWitness C D ε` — the specific concerns
(i) **Interval conventions vs. period 1.** `0 = a 0 < b 0 < a 1 < ⋯ < b (k−1) < a k = 1`; junction `j` on
`[a j, b j]`, straight `j` on `[b j, a (j+1)]`; the last straight part is `[b (k−1), 1]`. Closedness is a constraint,
not a conflict: `junction_end j` + `straight j` at `t = a (j+1)` + `junction_start (j+1)` force
`edge j = (2ε + speed·(a (j+1) − b j)) • normalize (edge j)`, i.e. `speed·(a (j+1) − b j) = |δ_j| − 2ε`, satisfiable
iff `|δ_j| > 2ε` (clearance `ε < η_ℓ/3`). At the seam (`j = k−1`) the same identity is read against
`junction_start 0` through `γ 1 = γ 0` (periodicity) and `((0 : ZMod k) − 1) = ((k−1 : ℕ) : ZMod k)`. The
skeleton's `a`, `b` (cumulative arclength / Λ) satisfy exactly this.
(ii) **`flat_ends` at both ends with `iteratedDeriv`.** `θ j` is C^∞ on ℝ and constant on `(−∞, a j]` and
`[b j, ∞)` (`θ_const_left/right`), hence every derivative of order ≥ 1 vanishes at both ends (continuity of
`iteratedDeriv m θ` + vanishing on an open half-line). Compatible with `immersion` (`deriv θ ≠ 0` on the OPEN
arc) — the model is `θu + ϑ·smoothTransition((t − a)/(b − a))`: `φ' > 0` on `(0,1)` (exact formula
`(f'(t)f(1−t) + f(t)f'(1−t))/(f+f(1−t))²`, both numerator terms positive) and `φ` constant on both half-lines.
No Rolle obstruction: Rolle would need `θ (a j) = θ (b j)`, i.e. `θ_sweep = 0`, i.e. `principalTurn = 0`,
excluded. `flat_ends_curve` (`m ≥ 2`) reads the straight part on the other side of each end (at `a 0 = 0` via
periodicity of `iteratedDeriv m γ`); `m = 1` is correctly NOT required (`γ'(a j) = speed • u_j ≠ 0`).
(iii) **`direction_once` (CLOSED arc) / `immersion` (OPEN arc).** `T (a j) = u_j`, `T (b j) = v_j`; `u_j ≠ v_j`
iff `principalAngle ≠ 0` (equality iff positively collinear), so injectivity on the closed arc is consistent;
the swept arc has length `|ϑ_j| < π` (`principalAngle_bounds` from `Regular`), so `(cos, sin)` is injective on
the angle range and `θ_unique` + `direction_once` are simultaneously satisfiable. The open/closed split is right.
(iv) **Disc clauses (junction = all of the curve in the disc).** `cornerDisc` is the CLOSED Euclidean disc — required,
since `γ (a j)`, `γ (b j)` are at distance exactly ε. `disc_contains_modification` (junction in the closed disc:
the printed triangle argument, numerically the max over the junction is ε attained only at the endpoints),
`straight_off_discs` (open straight part strictly outside every disc: distance to `q_j` is `ε + speed(t − b j) > ε`,
to `q_{j+1}` is `> ε` iff `t < a (j+1)`, to non-incident corners `> ε` by `disc_off_nonincident`),
`disc_only_modification` on `Ico 0 1` (a curve point in disc `j` is on junction `j`: other junctions lie in disjoint
discs, straight parts are outside; at the seam `t → 1⁻` the distance to `q_0` stays `> ε`, and `1 ∉ Ico 0 1`),
`junction_embedded` (bisector coordinate strictly increasing). Pairwise disjointness needs `|q_i − q_j| > 2ε`;
corners are distinct under `Generic` (`tail_off` for non-incident pairs, `Regular` for consecutive ones).
`disc_meets_out/in` are exact equalities and need only `ε ≤ |δ|`. All consistent with `outside` ((a) as a set
statement): outside the discs the curve is the union of the closed straight sub-segments, the polygon is the union
of the open ones — equal sets.
(v) **`same_strands` on the OPEN straight parameter interval.** Crossing points are at Euclidean distance
`> 3ε` from every corner (`ε < η_X/3`), so `crossingParam·|δ_j| − ε ∈ (0, |δ_j| − 2ε)` strictly — consistent
with `Carried.τ_mem` (`a (j+1) ≤ 1`).
(vi) **Constant speed vs. parametric straight form.** `straight` prescribes `γ (b j) + (speed·(t − b j)) • n_j`,
whose derivative has Euclidean length `speed` (`|n_j| = 1`); on the junction the printed unit-speed arc `γ_ℓ(σ)`
is read with `σ = speed·(t − a j)`. `const_speed` is the printed "parametrized by arclength" up to the factor
`speed = Λ` (FR-R4) and is what makes `immersion` (stated for `deriv θ`) equivalent to the printed arclength
derivative statement.

### 1.5 The intended emptiness (not a defect, record it)
If `principalTurn C.P j = 0` for some `j < k`: `θ_sweep` gives `θ (b j) = θ (a j)`, `θ_range` then makes `θ j`
constant on `[a j, b j]`, so `deriv θ j = 0` on `(a j, b j)` (nonempty by `a_lt_b`), contradicting `immersion`.
Hence `RoundingWitness C D ε` is uninhabited for such `(C, D)`; likewise for `ε ≤ 0` (`disc_center`). This is
exactly the printed hypothesis "nonzero" and "ε ∈ (0, ε₀)", carried by `exists_clearance`; the clause fields of
`RoundingData`, being universally quantified over witnesses, are unaffected.

### 1.6 Numeric check of the printed construction (independent of the skeleton's probe)
`/tmp/prereview/round_check.py` (plain Python, the printed `φ`, `ℓ = ε|u+v|/|m(φ)|`): triangle, figure-eight
quadrilateral (1 crossing), octagon (2 crossings), at `ε = 0.5·ε₀` and `0.95·ε₀` with the printed
`ε₀ = ⅓ min{η_v, η_e, η_ℓ, η_X}`: junction endpoint error ≤ 2e-14; `max(dist to corner) − ε ≤ 2e-14` with the
maximum only at the endpoints (interior strictly inside); straight parts strictly outside every disc; bisector
coordinate strictly monotone; occurrence order along the rounded curve = `visitCoord` order; all `τ ∈ (0,1)`;
`φ(0) = 0`, `φ(1) = 1`, `φ' > 0` on the interior (an apparent `φ'(0.001) = 0` in a first run is IEEE underflow of
`e^{−1000}`, not a zero of `φ'`).

## 2. Fidelity red flags

### 2.1 Printed clauses → fields (all present)
Preamble ("rot as in lem:rot for polygons and cf:def-turning for C¹ curves"): `rot_eq` uses exactly those two.
Hypotheses: turns exist = `Generic.regular`; nonzero = `∀ i, principalTurn ≠ 0`; finitely many transversal double
points, none a corner = `transverse`, `tail_off`; no corner on a non-incident edge = `tail_off`. Existence sentence
= `exists_clearance`. (a) = `outside`. (b) strictly monotone in the sense of sgn ϑ = `θ_strict`; from/to =
`tangent_start/end`; arc exactly |ϑ| and no more = `θ_sweep`, `θ_range`; each direction at exactly one parameter =
`θ_unique`, `direction_once`; immersion on the open arc = `immersion` (+ `const_speed`, `θ_lift`); "at the two
ends it and all its derivatives vanish" = `flat_ends` (`m ≥ 1`, correct: "it" is the angular derivative); "flat to
infinite order" = `flat_ends_curve` + `Lε.smooth`. (c) double points = `same_double_points`; strands =
`same_strands`, `same_strand_dir`; over/under = `carried` (D_ε is D); signs = `same_signs`; writhe = `same_writhe`.
(d) = `rot_eq`. (e) pairwise disjoint closed discs = `disc_isDisc`, `disc_disjoint` (`cornerDisc` is closed by
`≤`; `IsDisc` = compact convex with interior); one about each corner = `disc_center`; no non-incident edge =
`disc_off_nonincident`; no double point = `disc_no_double`; exactly the two ε-sub-segments = `disc_meets_out/in`;
whole modification = `disc_contains_modification`. No printed clause lacks a field.

### 2.2 Fields with no printed counterpart — coverage by FR-R1..R7 and the residue (all non-blocking)
Covered: `Carried` (FR-R1); existential form + named construction in the proof module (FR-R2); `no_triple`,
`const_speed`, `straight`, `same_strands` on the open interval, `flat_ends_curve`, `disc_only_modification`,
`junction_embedded` (FR-R3); parameter = arclength/Λ, `immersion` for `deriv θ` (FR-R4); bundle shape (FR-R5).
Residue, not named in §6 of PLAN_FINAL.md (recommend adding to FR-R3/FR-R4 so the formal reviewer is not surprised):
- R-a. `θ j` is a C^∞ function on ALL of ℝ, constant on both half-lines (`θ_smooth`, `θ_const_left/right`). The
  printed lift lives on the junction only; the extension is the device that makes `flat_ends` a two-sided
  `iteratedDeriv` statement. Satisfiable (`liftAt`), strictly more than printed.
- R-b. The subdivision `a b` with `a_zero/a_last/a_lt_b/b_lt_a` and the junction endpoints `junction_start/end`
  (= the proof's `A₀ = q_i − εu`, `A₁ = q_i + εv`) are proof objects promoted into the witness (header table does
  say so). Fine, but they fix a particular parametrisation and seam (`t = 0` at `A₀(q₀)`).
- R-c. `same_strand_dir` (velocity a positive multiple of the edge) is the "with their orientations" of the proof
  (sm-3:3855-3856), not of the statement text.
- R-d. `straight_off_discs` is derivable from `disc_only_modification` + the interval ordering (redundant).
- R-e. Printed (e) is existential ("there are ... discs"); the Lean fixes them as the radius-ε Euclidean discs.
  A specialisation consistent with (a) ("the discs of radius ε") and with the printed proof; strictly stronger.
- R-f. Quantifier order of the clearance: `∀ C D, ∃ ε₀` lets `ε₀` depend on the over/under assignment, whereas the
  printed `ε₀(L)` (and consumer cf:thm-carrierfloor (B) "Take ε₁ = ε₀(L)") depends on `L` alone. The skeleton's
  `clearance C` already depends only on `C`, so `∀ C, (∀ i, turn ≠ 0) → ∃ ε₀ > 0, ∀ D ε, … ` costs nothing and is
  the more faithful reading. Recommend the swap (or record the weaker reading explicitly).
- R-g. Two consumers cite proof-internal objects: cf:lem-curl (sm-3:4105 "the transition profile of Lemma
  cf:lem-rounding") and cf:thm-carrierfloor (sm-3:4291-4300 clause (A) "the construction in the proof"; 4493 "the
  explicit flat transition profile φ displayed in the proof"). The statement exports neither `Real.smoothTransition`
  nor `Round(L,D,ε)`; FR-R2 covers (A). Extend FR-R2 to the profile: those rows must import the proof module and
  cite `CornerRounding.*` / `Real.smoothTransition` by name.
- R-h. Consumer (B) parametrises "with s = 0 in the interior of a straight part"; the Lean seam is the start of
  junction 0. A downstream `tw_shift`/reparametrisation, not a defect here.

## 3. Trivial-truth check
- `exists_clearance` is the theorem and is not trivially true: its hypotheses are satisfiable (§1.1), and its
  conclusion `Nonempty (RoundingWitness C D ε)` on an open interval of ε is a strong statement (the witness forces
  `0 < ε`, all turns nonzero, the closure identity of §1.4(i), an embedded junction inside each closed disc, and the
  full `Carried` record). No hypothesis contains any conclusion field.
- Fields `smooth_regular_carried`, `a`–`e` of `RoundingData` are projections of `RoundingWitness` and are proved
  in the skeleton by field access alone (FR-R5). They are trivially true BY DESIGN; the formal reviewer must treat
  the `RoundingWitness` field list as the fixed content of (a)–(e), not the bundle fields. This is already stated in
  the file header and in FR-R5; it is the one place where a reviewer reading only `RoundingData` could be misled.
- Redundant (derivable) witness fields, harmless: `same_signs` (= `carried.sign_eq`), `same_writhe`,
  `same_double_points` (from `carried.doubles/τ_eval/τ_inj` + `twin_ne`; the skeleton proves it that way),
  `flat_ends` (from `θ_smooth` + `θ_const_*`), `straight_off_discs` (R-d), `direction_once` (from `θ_unique`,
  `θ_lift`, `|ϑ| < π`). Their presence does not weaken the row.

## 4. Minor notes
- `#print axioms` claims of PLAN_FINAL.md not re-run here; the statement file itself is `sorry`-free except the row.
- `grep -c sorry Skeleton_FINAL.lean` = 54 lines vs. "52 sorry tokens" in the plan — doc-comment mentions,
  not extra leaves (not re-audited; the skeleton is outside this pre-review's object).
- `IsDisc (cornerDisc C ε i)` needs compactness in the product topology of `ℝ × ℝ`: closed (`≤` of a continuous
  function) and bounded (Euclidean ≥ sup norm). Unit E's `cornerDisc_isDisc` is straightforward.
