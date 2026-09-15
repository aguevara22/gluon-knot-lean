# Feasibility memo — rows 104 (cb:embedded-rotation) and 57 (lem:gauss-two-discs)

Date: 2026-09-14.  Toolchain: Lean v4.34.0-rc2, Mathlib pin 85e3a25e (`work/lean`).  Re-opens the
deferral of AUTHOR_NOTES.md:2342-2352 / 3827-3831 ("PL Jordan–Schoenflies, multi-thousand-line").
Sources: row 57 statement sm-3:428-436, proof 437-542; row 104 statement sm-3:4760-4764, proof 4765-4800.
Consumers: row 104 is cited only by lem:corner-values (105, GAP-2-blocked via cb:singleton ← thm:floor),
which uses only `|r_Q| = 1` (sm-3:4811); row 57 is cited only by 104 (for a triangulation of the bounded
region, 4765-4767), by 105 through 104, and by two non-checklist lemmas (gauss-sphere-isotopy, gauss-pl-model).

## 0. Summary

| row | verdict | estimate | two hardest steps | statement file |
|---|---|---|---|---|
| 104 cb:embedded-rotation | **FEASIBLE** without row 57: a polygonal secant-lift (Hopf Umlaufsatz) argument on the accepted `rotationNumber`/`principalTurn`/`IsLiftOn` layer; no triangulation, no Jordan, no ear theorem; identity checked numerically (§1.3) | ≈ 2 500 lines (range 2 000–3 200) | (a) the 2n−1-piece decomposition of the secant diagonal with floor/fract bookkeeping (§1.4 S7), ≈ 400; (b) `Embedded ⇒` traversal injective mod n and the Generic/no-crossing bridge (S2), ≈ 350 | `work/drafts/pldiscs/EmbeddedRotation_Statement.lean` (0 errors, 3 sorry) + leaf skeleton `EmbeddedRotation_Leaves.lean` (0 errors, all leaves sorry) |
| 57 lem:gauss-two-discs | **INFEASIBLE now** as a row (all five clauses): the two-region clause is HARD (4 000–6 000 alone), the PL-disc clause is the PL Schoenflies content (5 000–8 000 on top, new PL vocabulary), the two extension clauses are cheap only on convex model discs; total 12 000–20 000 lines, several lanes, no Mathlib support (no Jordan, no planar Euler, no triangulations); its only non-GAP-2 consumer no longer needs it | 12 000–20 000 | (a) PL-disc structure of both closures (collapses + regular neighbourhoods, sm-3:492-534); (b) two complementary regions (sm-3:457-491 or a ray-parity proof) | none written (recommendation: keep DEFERRED; §2.6) |

## 1. Row 104 cb:embedded-rotation (statement sm-3:4760-4764, proof 4765-4800)

### 1.1 What the statement needs (statement ≠ printed proof)

The claim is "every embedded regular polygon has rotation +1 or −1, according to its traversal
orientation around the bounded complementary region".  Only the proof cites row 57 (4765: "supplies a
finite straight triangulation of the bounded complementary region, a disc with Euler characteristic
one"); the statement does not.  The printed proof also states what "embedded" allows: straight
subdivisions with zero principal turn (4791 "including zero at a straight subdivision"), so the domain is
wider than `Generic` (G1 forbids flat vertices).  A different proof of the same statement is admissible;
the row's claim is the statement.

Printed notion → accepted vocabulary:
* polygon, edges `ℓ_i`, segments → `LabelledTuple n`, `edge`, `edgeSegment`, `remote`, `adjacent` (Polygon.lean);
* regular, principal turns, rotation → `Regular`, `principalTurn`, `rotationNumber` (RegularLocus.lean,
  RotationNumber.lean); lem:rot = `SM.rotation_number` (RotationTheorem.lean:14, all clauses incl.
  `rotationNumber (reversal P) = -rotationNumber P`, `2|rot| < n`, `n = 3 → rot = ±1`);
* embedded → **new** `Embedded P` (statement file): every edge nonzero, remote edge segments disjoint,
  consecutive edge segments meet exactly in their common vertex — the simple closed polygonal curve on
  def:polygon's vocabulary.  There is no accepted polygon-level "embedded"/"simple" predicate (grep:
  none); the accepted crossing-free notions are `IsEmpty (Crossing P)` (Crossings.lean:15, remote
  segments meeting) at the polygon level and `Diagram.IsCrossingFreeCircle` (LinkDiagram.lean:587) at the
  diagram level, both used by the consumer chain (`positiveLift_isCrossingFreeCircle`, CBBlocks
  `no_blocks`).  Bridge leaf: `Generic P → IsEmpty (Crossing P) → Embedded P` via
  `g1_successive_intersection` (G1Consequences.lean:19, exactly the consecutive clause);
* "bounded complementary region" / "traversal orientation around it" → not available (that is Jordan);
  rendered locally at **supporting vertices** `IsSupportingVertex P N i` (the polygon lies in the closed
  half-plane `⟪N, x − P i⟫ ≥ 0`): there the bounded region is on the polygon's side, and "traversal
  orientation around it" is the sign of the principal turn (§1.8 FR-ER-2).

Mathlib check (precise): no Jordan curve theorem, no winding/turning number, no π₁(S¹), no planar
graphs, no Euler formula, no triangulations (`Geometry.SimplicialComplex` has faces/down-closure only,
no Euler characteristic); `Geometry/Polygon/Basic.lean` has a bare `Polygon` with `boundary` and
`HasNondegenerateVertices`, no simplicity/interior; available: covering-space lifting through
`Circle.exp` (already wrapped as `exists_lift_of_unit` for `ℝ` and `ℝ × ℝ`, TurnLift.lean:83),
`Complex.continuousAt_arg` on `slitPlane` (already wrapped: `regularPair_slitPlane`), `Real.Angle`,
`Convex` API, `IsPreconnected.intermediate_value`.

### 1.2 The route: polygonal secant lift (no triangulation)

Base the polygon at a supporting vertex `v = P 0` (shift; `rotationNumber_shift`, `principalTurn_shift`,
`Embedded.shift`).  Let `γ = traversal P : ℝ → Plane`, `γ(k + t) = P k + t·e_k`, period `n`.  On the
convex region `R = {(s,t) : 0 ≤ s, t ≤ n, ½ ≤ t − s ≤ n − ½}` the secant direction
`σ(s,t) = normalize(γ t − γ s)` is defined (γ injective mod n = `Embedded`) and continuous; retract `ℝ²`
onto `R` by clamping and lift with `exists_lift_of_unit` on `ℝ × ℝ`: a continuous `Θ : ℝ² → ℝ` with
`σ = (cos Θ, sin Θ)` on `R`.  Telescoping `Θ` around the boundary of `R` (no homotopy needed):

`Θ(n−½, n) − Θ(0, ½)` [diagonal `t = s + ½`] `= [Θ(n−½,n) − Θ(½,n)]` [top leg] `+ [Θ(½,n) − Θ(0,n−½)]`
[cut `t = s + n − ½`] `+ [Θ(0,n−½) − Θ(0,½)]` [left leg].

* Diagonal, `s ∈ [k, k+½]`: `γ(s+½) − γ(s) = ½ e_k`, constant ⇒ increment 0
  (`IsLiftOn.increment_eq_zero_of_const`).  `s ∈ [k+½, k+1]`: `= (k+1−s) e_k + (s−k−½) e_{k+1}`, a
  positive combination sweeping from `e_k` to `e_{k+1}` ⇒ increment `ϑ_{k+1}` (sector lemma S4).
  Over `s ∈ [0, n−½]` this covers vertices `1..n−1`: diagonal increment `= Σ_{k≠0} ϑ_k`.
* Cut, `s ∈ [0, ½]`: `γ(s+n−½) − γ(s) = γ(s−½) − γ(s) = −[(½−s) e_{−1} + s e_0]` ⇒ increment `ϑ_0`
  (sector lemma; negation does not change increments).
* Left leg: `t ↦ normalize(γ t − v)`, `t ∈ [½, n−½]`, increment `I`.  Top leg: `s ↦ normalize(v − γ s)`
  `= −(left leg)`, increment `I`.

Hence **`Σ_i ϑ_i = 2 I + 2 ϑ_0`** (leaf `sum_principalTurn_eq_two_mul`).  At a supporting vertex all
`γ t − v` lie in a closed half-plane, so `|I| ≤ π` (half-plane lemma S5); the leg runs from `½ e_0` to
`−½ e_{−1}`, so `I ≡ π − ϑ_0 (mod 2π)`.  With `|ϑ_0| < π`: `Σϑ = 2π + 4πm`, `|Σϑ| < 4π` ⇒ `Σϑ = ±2π`,
i.e. `rot = ±1`; if `ϑ_0 > 0` then `m = 0` (`rot = 1`), if `ϑ_0 < 0` then `m = −1` (`rot = −1`)
(leaf `assembly`).  The lowest-leftmost vertex is supporting for `N = (1,0)` with `ϑ ≠ 0` (a flat
turn there would force both incident edges vertical and antiparallel, contradicting `consecutive`).

### 1.3 Numerical check of the identity

`Σϑ = 2I + 2ϑ_0` was evaluated (python, 20 000-step lift of the leg) on six random star-shaped simple
polygons with an inserted flat vertex, both orientations, and on a non-star-shaped L-shaped octagon:
`Σϑ/2π ∈ {+1, −1}` and `(2I + 2ϑ_0)/2π` agree to 1e-12 in every case, with the sign of `ϑ_0` at the
lowest-leftmost vertex.  The classical statement (Hopf Umlaufsatz for polygons) is textbook.

### 1.4 Step → tool → lines

| step | Mathlib / project tool | status | lines |
|---|---|---|---|
| S1 `traversal P`, period `n`, continuity, `γ(k+t) = P k + t e_k` | `Int.floor`, `Int.fract`, `edgePoint`, `ZMod` casts; continuity by gluing on `[k, k+1]` | new | 250 |
| S2 `Embedded ⇒ Regular`; `Embedded ⇒ γ injective mod n`; `Embedded.shift`; bridge `Generic ∧ IsEmpty (Crossing P) ⇒ Embedded` | `edgeSegment_shift`, `g1_successive_intersection`, `remote`/`adjacent` case split (`adjacent_distinct_cases`), `IsCrossing` | new | 350 |
| S3 secant map nonvanishing/continuous on `R`; clamp retraction `ℝ² → R`; global lift `Θ` | `continuous_normalize_comp`, `exists_lift_of_unit` (α = `ℝ × ℝ`), `euclideanLength_normalize` | new (lift device exists) | 250 |
| S4 sector lemma: path in the positive cone of a `RegularPair (u,v)`, from ray `u` to ray `v` ⇒ increment `= principalAngle u v` | `principalAngle = arg (cornerRotor u ·)`, `Complex.continuousAt_arg` on `slitPlane` (`regularPair_slitPlane` pattern), `const_of_circleExp_eq_one` / `IsLiftOn.increment_eq` | new | 200 |
| S5 half-plane lemma: nonvanishing path with `⟪N, c s⟫ ≥ 0` ⇒ `|increment| ≤ π` | `cos(θ − θ_N) ≥ 0`, `IsPreconnected.image`, interval inside `⋃_m [2πm − π/2, 2πm + π/2]` | new | 180 |
| S6 `IsLiftOn.neg` (lift + π), `increment_coe_angle` (increment ≡ arg b − arg a), restriction of `Θ` to the four boundary paths as `IsLiftOn` | `principalAngle_coe_angle`, `IsLiftOn.circleExp_coe`, `Real.Angle.coe_eq_zero_iff` | new | 150 |
| S7 diagonal: `2n−1` pieces `[k,k+½]`, `[k+½,k+1]` with the explicit formulas; telescoping to `Σ_{k≠0} ϑ_k` | S1, S4, `Finset.sum_range_succ`, `sum_range_natCast_eq_sum_zmod` (TurnLift.lean:291) | new | 400 |
| S8 cut piece (cone at vertex 0, negated), top leg = −(left leg) | S4, S6 | new | 150 |
| S9 supporting vertex: leg endpoints `½ e_0`, `−½ e_{−1}`; half-plane containment (convex combination of `P j − v`); `I ≡ π − ϑ_0` | `planeDot` linearity, `Complex.arg_neg_coe_angle`, `principalTurn_coe_angle` | new | 200 |
| S10 lowest-leftmost vertex: existence (`Finset.exists_min_image` twice), supporting for `N = (1,0)`, `ϑ ≠ 0` | `principalAngle_eq_zero_iff` (positive multiple), `consecutive` clause | new | 150 |
| S11 assembly: `Real.Angle` congruence → `∃ m : ℤ`, case analysis, `2π rot = Σϑ` (`two_pi_mul_rotationNumber`), shift back to vertex `i`, bundle | `two_pi_mul_rotationNumber`, `rotationNumber_shift`, `principalTurn_shift` | new | 200 |
| **total** | | | **≈ 2 500** |

Overrun risk: S7 (floor arithmetic across the wrap `n−½ … n`) and S2 (case split on which edges the two
parameters lie on, including the wrap pair `(n−1, 0)`); a 30 % overrun gives 3 200, still one unit.

### 1.5 Alternatives considered

* **A0 printed route** (triangulate the bounded region, Euler count `F = 2I + B − 2`, angle sums,
  4765-4797): needs the existence of a finite straight triangulation of the bounded region *and* its
  Euler characteristic 1 — that is row 57's content (§2); ≥ 6 000 lines.  Rejected.
* **A1 ear / diagonal induction** (two-ears theorem; leftmost vertex convex; farthest vertex inside the
  ear triangle gives a diagonal; split and induct): needs point-in-triangle via `det` signs, diagonal
  non-crossing against every edge, simplicity of both pieces, additivity of principal turns at the two
  diagonal endpoints (a real, not mod-2π, identity needing the "diagonal inside the interior angle"
  side condition), `deleteVertex`-style index surgery (CuspLawTree has some); base case lem:rot (iv).
  Estimate 3 500–5 000, many geometric case splits.  Rejected in favour of A3.
* **A3 secant lift** (§1.2): chosen.  Everything is one continuous function on a convex region plus
  four one-dimensional increment computations; the only geometry is "positive combination" and
  "closed half-plane".
* **A4 rounding + smooth Hopf**: `rot_eq_rotationNumber_of_rounding` (TurnLift.lean:314) links the
  polygon to a `C¹` curve, but the accepted rounding gives no simplicity of the rounded curve, and the
  smooth secant argument needs a `C¹` extension to the diagonal; more work than A3 for no gain.

### 1.6 Statement check (`EmbeddedRotation_Statement.lean`, 0 errors)

`structure EmbeddedRotationData [NeZero n] (P : LabelledTuple n) : Prop` with one field per printed
clause: `pm_one : rotationNumber P = 1 ∨ rotationNumber P = -1` (4762 "rotation +1 or −1");
`orientation : ∀ N i, IsSupportingVertex P N i → (0 < principalTurn P i → rotationNumber P = 1) ∧
(principalTurn P i < 0 → rotationNumber P = -1)` (4762-4764 "according to its traversal orientation
around the bounded complementary region", read at supporting vertices); `exists_supporting : ∃ N i,
IsSupportingVertex P N i ∧ principalTurn P i ≠ 0` (non-vacuity, so the sign is determined).
Row theorem `SM.cb_embedded_rotation [NeZero n] (hn : 3 ≤ n) (P) (hreg : Regular P) (hemb : Embedded P) :
EmbeddedRotationData P := sorry`.  Bridges (sorry): `embedded_of_generic_of_isEmpty_crossing`,
`Embedded.regular`.  Row 104 has no fixed checker name (not in axiom-policy `targets`).

### 1.7 Verdict

**FEASIBLE**, ≈ 2 500 lines, one prover unit (two provers in parallel as for rows 84/87: A = S1-S3 +
S7-S8, B = S4-S6 + S9-S11, meeting at `sum_principalTurn_eq_two_mul` / `leg_increment`).  Decisive
reasons: (1) the lifting device and the `IsLiftOn` increment calculus exist and are accepted
(TurnLift.lean); (2) the identity `Σϑ = 2I + 2ϑ_0` needs no homotopy, only a global lift on `ℝ²` and
telescoping; (3) the two new analytic lemmas (sector, half-plane) are 200 lines each with direct
Mathlib tools; (4) nothing depends on row 57.  Hardest: S7 and S2.

### 1.8 Fidelity risks (row 104)

* **FR-ER-1** (4762 "embedded"): rendered as the simple closed polygonal curve `Embedded P` on
  def:polygon vocabulary, wider than "generic with `m = 0`" (flat vertices allowed, as 4791 requires);
  the narrower consumer form is reached by the bridge leaf.  Reviewers should confirm `Embedded` is
  what "embedded" means at 4762 (the proof's "the region is an embedded disc", 4792, agrees).
* **FR-ER-2** (4762-4764 "according to its traversal orientation around the bounded complementary
  region"): the bounded complementary region is not defined in the accepted layer (it is row 57's
  object); the sign clause is read at supporting (convex-hull) vertices, where the bounded region lies on
  the polygon's side and a left turn means "bounded region on the left".  Consumers use only `|r| = 1`
  (4811).  A global rendering (winding number of `P` about a point just inside a supporting vertex
  equals `rot`, and vanishes far away) would cost ≈ 800–1 200 more lines and is not proposed.
* **FR-ER-3** (4762 "regular"): `Regular P` is kept as a hypothesis although `Embedded P` implies it
  (leaf `Embedded.regular`); harmless.
* **FR-ER-4** (4797-4798 "the opposite traversal negates every turn and gives −1"): not a separate field;
  it is lem:rot (iii) `rotationNumber (reversal P) = -rotationNumber P` in `SM.rotation_number`, and the
  sign clause covers both orientations through the sign of the supporting turn.
* **FR-ER-5** (4765-4767): the proof route differs from the printed one (no row 57, no Euler count).
  `blueprint/DEPENDENCIES.json` lists `lem:gauss-two-discs` under `cb:embedded-rotation`; `tools/claims.py`
  uses that column only to pick the next unit (not a checker gate), so the accept must record "proved
  independently of row 57" in the review brief and AUTHOR_NOTES.
* **FR-ER-6** (4791 "including zero at a straight subdivision"): flat vertices are in the domain and
  the sector lemma yields increment 0 for a positively collinear pair, as printed.
* **FR-ER-7**: `IsSupportingVertex` uses the Euclidean `planeDot` with `N` pointing into the polygon's
  half-plane; the lowest-leftmost vertex is supporting for `N = (1, 0)`.

### 1.9 Leaf skeleton plan (`EmbeddedRotation_Leaves.lean`, all sorry, typechecked)

Order of proof, with the leaf names: (1) `traversal_add_nat`, `continuous_traversal`,
`traversal_int_add` [S1]; (2) `Embedded.regular`, `Embedded.traversal_injective`, `Embedded.shift`,
`isSupportingVertex_shift`, `embedded_of_generic_of_isEmpty_crossing` [S2]; (3) `exists_secant_lift`
on `secantRegion n` [S3]; (4) `increment_eq_principalAngle_of_cone` [S4]; (5)
`abs_increment_le_pi_of_halfplane` [S5]; (6) `IsLiftOn.neg`, `increment_coe_angle` [S6]; (7)
`sum_principalTurn_eq_two_mul` [S7-S8, the key identity]; (8) `leg_increment` [S9]; (9)
`exists_supporting_vertex_turn_ne_zero` [S10]; (10) `assembly` and `cb_embedded_rotation` [S11].
Leaves (4), (5), (6), (10) are polygon-free and can be proved first by a second prover.

## 2. Row 57 lem:gauss-two-discs (statement sm-3:428-436, proof 437-542)

### 2.1 Clauses and what each would mean

| clause | tex | accepted vocabulary / new vocabulary needed |
|---|---|---|
| 57a "a simple polygonal circle in the oriented sphere has exactly two complementary regions" | 430-431 | circle = `Embedded P` (§1); sphere = `OnePoint Plane` (Mathlib topology; `Plane = ℝ × ℝ`); regions = connected components of the complement (`connectedComponentIn`); clause = `Nat.card (ConnectedComponents (range γ)ᶜ) = 2`, in the plane "one bounded, one unbounded" |
| 57b "both closures are PL discs" | 431 | **new**: PL disc = image of a convex polygon (`IsDisc`, LinkMoves.lean:100, is convex-compact-with-interior; adequate as the model) under a homeomorphism affine on each triangle of a finite triangulation with positive determinants; needs finite straight triangulations (no Mathlib API: `Geometry.SimplicialComplex` has no finiteness/dimension/Euler) and PL maps |
| 57c "finite prescribed positive PL boundary maps between such discs extend to positive PL disc maps" | 431-433 | boundary map = the accepted def:gauss-record rendering `ExtendsPiecewiseAffine` / `rexB_pl` (LinkRecordExtension.lean:726, 169: positive, piecewise affine in `TraversalPoint` coordinates); extension = PL homeomorphism of the closures with positive determinants restricting to it |
| 57d "a continuous positive boundary map also extends to a topological disc map" | 433-434 | orientation-preserving boundary homeomorphism (`traversalBetween`-preserving `Equiv` + continuity) extends to a homeomorphism of the closures |
| 57e "the statement includes the exterior region" | 434 | 57b-d for the closure of the unbounded region in the sphere (one-point compactification; printed radial cap 448-456) |

### 2.2 The constructive route, clause by clause (Lean cost)

| printed step | tex | Lean content | lines | status |
|---|---|---|---|---|
| arrangement of edge lines + auxiliary lines in a rectangle, convex cells, fan triangulation, `C` a simple edge cycle of a finite triangulation, cap = compactified exterior | 437-456 | data structure for a finite triangulation of the rectangle containing `P` as a subcomplex (cells of a line arrangement, their convexity, fan subdivision, edge subdivision at intersections); radial cap homeomorphism | 3 000–4 500 | not started; nothing in Mathlib |
| `F₂` chains: `V−E+F = 2`, invariance under the three subdivision moves, connectivity of vertex-edge and dual graphs, rank counts, `C = ∂(face assignment)` unique up to complement | 457-476 | finite chain complex over `ZMod 2`, Euler characteristic, spanning trees, rank arguments (Mathlib: `SimpleGraph` trees exist; no Euler formula) | 2 000–3 000 | not started |
| colouring ⇒ exactly two connected regions, each with boundary `C`, no pinch | 477-491 | local fan analysis at vertices of `C`, dual-graph connectivity | 1 000–1 500 | not started |
| collapses ⇒ `χ(R) ≤ 1`, `χ(R₀)+χ(R₁) = 2` ⇒ both residual graphs are trees | 492-504 | free-face collapse on the finite complex, Euler bookkeeping | 800–1 200 | not started |
| regular neighbourhoods, notch PL homeomorphisms (eq. gauss-triangle-notch), leaf induction ⇒ disc parametrisations of `R₀, R₁` | 505-534 | explicit PL maps, positivity of every affine piece, compatibility of widths | 2 500–4 000 | not started; this is 57b/57e proper |
| identification with convex discs; fan extension of finite positive PL boundary maps | 535-537 | on a convex model disc: subdivide boundary, one interior vertex, affine fans, positive determinants by cyclic order | 1 000–1 500 | **FEASIBLE alone** |
| radial extension of a continuous positive boundary map `(r,u) ↦ (r, b(u))` | 537-542 | on a convex model disc: `gauge`/radial coordinates, continuity at the centre by the radial bound, inverse via `b⁻¹` (Alexander trick) | 800–1 200 | **FEASIBLE alone** |

Alternative for 57a in the plane (ray-parity, not printed): winding/parity function locally constant off
the image (200), zero far away (200), changes by one across an edge (300), every point joins a point near
the polygon by a segment (400), points near the polygon on one side are path-connected along a strip
(1 500–2 500, the hard part), assembly (300): ≈ 4 000–5 500 lines for 57a alone; it gives no PL disc.

### 2.3 What is provable, what is genuinely out of reach

* Provable in principle: every clause; nothing needs an unformalisable input.  The **cheap** parts are
  57c and 57d **on convex model discs** (≈ 2 000 lines together) — note the earlier deferral note's
  phrase "topological extension clause = Alexander trick / Schoenflies" overstates: the radial Alexander
  trick on a convex disc is the easy clause; the Schoenflies content is 57b (the closures *are* PL discs).
* Out of reach now (budget, not mathematics): 57a+57b+57e — a finite-triangulation / regular-
  neighbourhood library or a strip-connectivity proof, 10 000–17 000 lines, several lanes, high
  integration risk, with no accepted consumer that needs them once 104 is proved by §1.
* A row is accepted whole; the two cheap clauses cannot be booked separately.

### 2.4 Verdict

**INFEASIBLE now** (12 000–20 000 lines; > 10 000 ⇒ beyond HARD).  Recommendation: keep row 57
DEFERRED with this memo as the reason; do not open a lane.  If the project later wants 57 anyway, the
order is 57c/57d on convex discs (2 000, self-contained), then 57a by ray-parity (4 000–5 500), then 57b
by ear triangulation of the bounded region + inductive fan PL homeomorphisms (5 000–8 000), then 57e.

### 2.5 Fidelity risks (row 57, for any future statement)

* **FR-TD-1** (430 "simple polygonal circle in the oriented sphere"): a plane polygon with the point at
  infinity added; "oriented" enters only through "positive" maps (positive determinants / orientation-
  preserving boundary maps).
* **FR-TD-2** (430-431 "complementary regions"): connected components of the complement in the sphere; in
  the plane the same two regions with the unbounded one non-compact — the closure-is-a-PL-disc clause
  for the exterior only makes sense in the sphere (434, 448-456).
* **FR-TD-3** (431 "PL discs"): PL homeomorphic to a convex polygon via a finite straight triangulation;
  the document never fixes the triangulation, so any finite one is admissible.
* **FR-TD-4** (431-433 "finite prescribed positive PL boundary maps"): read as the accepted
  `ExtendsPiecewiseAffine`-style data (finitely many marks, affine between them, orientation-preserving);
  "between such discs" means between the two closures of two different embedded polygons, not only
  interior-to-exterior of one.
* **FR-TD-5** (433-434 "topological disc map"): a homeomorphism of closures, no PL or smoothness claim.
* **FR-TD-6** (437 "no Jordan or Schoenflies conclusion is being assumed"): a formalisation must not
  import 57a to prove 57b; the printed order (triangulation first) or the ray-parity order both respect this.

## 3. Consumers and recommendation

Row 104 proved by §1 makes row 57 consumer-free among the 132 (105 is GAP-2-blocked and uses only
`|r_Q| = 1`).  Open a prover unit for 104 on `EmbeddedRotation_Statement.lean` + `_Leaves.lean`
(≈ 2 500 lines, two provers, a few hours on the lane pattern of rows 84/87/88/89); leave 57 DEFERRED.
Reachable ceiling without GAP-2 rises by one (104), not two.
