# ER_PLAN — row 104 cb:embedded-rotation, prover plan (polygonal secant / Hopf route)

Date: 2026-09-14.  Toolchain: Lean v4.34.0-rc2, Mathlib pin 85e3a25e.  Source: sm-3:4760-4764 (proof
4765-4800).  Feasibility: `PLDISCS_FEASIBILITY.md` §1 (verdict FEASIBLE, ≈ 2 500 lines).

## 0. Files and status

| file | role | status |
|---|---|---|
| `work/drafts/pldiscs/EmbeddedRotation_Skeleton.lean` (411 lines) | **the unit file**: §1 statement part, §2 route definitions, §3-§5 the 23 leaves (`sorry`), §6 assembly (proved) | `cd work/lean && lake env lean ../drafts/pldiscs/EmbeddedRotation_Skeleton.lean`: **0 errors**, 23 warnings `declaration uses sorry` (= the 23 leaves), `#print axioms SM.cb_embedded_rotation` = `[propext, sorryAx, Classical.choice, Quot.sound]` — `sorryAx` enters only through the leaves |
| `work/drafts/pldiscs/EmbeddedRotation_Statement.lean` | fixed statement (0 errors, 3 sorry) | statement part reproduced **byte-identically** in the skeleton: Statement lines 22-50 (`Embedded`, `IsSupportingVertex`, `EmbeddedRotationData`, with docstrings) = Skeleton lines 25-53; Statement lines 52-54 (docstring + signature of `SM.cb_embedded_rotation` up to `:= by`) = Skeleton lines 389-391 |
| `work/drafts/pldiscs/EmbeddedRotation_Leaves.lean` | earlier leaf sketch | superseded by the skeleton (kept for the record) |

Provers edit the skeleton **in place**: replace `sorry` bodies only; do not touch §1, §2 or §6; the file
must compile after every leaf; when all 23 are done `#print axioms` must show no `sorryAx`.  Helper
lemmas may be added *above* the leaf that uses them (inside the unit's section).

## 1. Route (what the assembly already proves)

`γ = traversal P`, `γ(k+t) = P k + t·e_k`, period `n`.  On the convex `secantRegion n`
(`½ ≤ t − s ≤ n − ½`, `0 ≤ s`, `t ≤ n`) the secant direction `secantDir P (s,t) = normalize (γ t − γ s)` is
a continuous unit map (A9, B9, B8); the clamp `secantRetract n` (B1-B3) makes it a continuous unit map on
`ℝ²`, and `exists_lift_of_unit` (TurnLift.lean:83) gives a global angle `Θ` (`exists_secant_lift`, proved).
Telescoping `Θ` around the boundary (`boundary_telescoping`, proved) with the four increments
C1 (diagonal `= Σ_{i≠0} ϑ_i`), C2 (cut `= ϑ_0`), C3 (top = left `= I`) gives
`Σ ϑ_i = 2 I + 2 ϑ_0` (`sum_principalTurn_eq_two_mul`, proved).  C4 gives `|I| ≤ π` and `I ≡ π − ϑ_0`;
`assembly` (proved, pure arithmetic) yields `Σϑ = ±2π` with the sign of `ϑ_0`; `based_rotation` (proved)
converts to `rotationNumber`; `cb_embedded_rotation` (proved) shifts a supporting vertex to index 0
(`isSupportingVertex_shift` proved, `Embedded.shift` A10, `regular_shift`, `principalTurn_shift`,
`rotationNumber_shift`) and uses C5 for non-vacuity.

## 2. Units

| unit | leaves | est. lines | uses (statements only) | character |
|---|---|---|---|---|
| **U-A** traversal calculus, embeddedness, shifts, bridges | A1-A11 (skeleton 114-173) | ≈ 750 | Polygon.lean, G1Consequences.lean, Crossings.lean, Mathlib floor/fract | index/floor arithmetic, segment case splits |
| **U-B** retraction and increment lemmas | B1-B7 (skeleton 176-222); B8, B9 are already proved | ≈ 700 | TurnLift.lean lift calculus, `Complex.arg`, `Real.Angle`, connectedness | one-dimensional analysis, no polygons |
| **U-C** boundary increments, supporting vertex | C1-C5 (skeleton 250-291) | ≈ 860 | A1, A3-A6, A9 and B4-B7 (as black boxes), `IsSecantLift.isLiftOn_comp` (skeleton 105), `IsLiftOn.increment_eq` (TurnLift.lean:55) | piecewise telescoping, angle bookkeeping |

Cross-dependencies: U-A and U-B are independent of everything; U-C consumes the *statements* of U-A
(A1, A3, A4, A5, A6, A9) and U-B (B4, B5, B6, B7).  All statements are fixed in the skeleton, so the
three units run in parallel; U-C's provers may assume the others' leaves.

## 3. Leaves

Sizes are estimates in lines of Lean.  "Tools" are file:line under `work/lean/` unless prefixed `Mathlib/`.

### U-A

| leaf | line | statement in words | proof sketch | tools | size |
|---|---|---|---|---|---|
| A1 `traversal_add_nat` | 114 | `γ (x + n) = γ x` | `⌊x + n⌋ = ⌊x⌋ + n`, `fract (x + n) = fract x`, and `((⌊x⌋ + n : ℤ) : ZMod n) = ⌊x⌋` (`ZMod.natCast_self`) | Mathlib/Algebra/Order/Floor/Ring.lean:182 `floor_add_intCast`, `Int.fract_add_int`, `ZMod.natCast_self`, `Int.cast_add` | 40 |
| A2 `continuous_traversal` | 119 | `γ` is continuous | at non-integers `⌊·⌋` is locally constant and `fract` continuous; at an integer `k`: right limit `edgePoint P k 0 = P k`, left limit `edgePoint P (k−1) 1 = P k` (`edgePoint_one`), via `continuousAt_iff_continuous_left_right` and `tendsto_fract_left'`/`right'`; alternatively `ContinuousOn` on each `Icc k (k+1)` (affine, A3) glued by `ContinuousOn.union_of_isClosed`-style lemmas | Mathlib/Topology/Order/LeftRight.lean:140, Mathlib/Topology/Algebra/Order/Floor.lean:181, G1Consequences.lean:13-16 `edgePoint_zero/one` | 120 |
| A3 `traversal_int_add` | 123 | for `0 ≤ t ≤ 1`, `γ (k + t) = P k + t • e_k` | if `t < 1`: `⌊k+t⌋ = k`, `fract = t` (Mathlib/Algebra/Order/Floor/Ring.lean:141 `floor_eq_iff`); if `t = 1`: `⌊k+1⌋ = k+1`, `fract = 0`, and `edgePoint P (k+1) 0 = P (k+1) = P k + 1 • e_k` (`edge`) | `Int.floor_eq_iff`, `Int.fract`, Polygon.lean:49-51 `edge`, `edgePoint` | 60 |
| A4 `traversal_diag_const` | 128 | `s ∈ [k, k+½]` ⇒ `γ(s+½) − γ(s) = ½ e_k` | write `s = k + t`, `t ∈ [0, ½]`, apply A3 twice (`t` and `t + ½ ≤ 1`), subtract | A3, `smul_sub`, `ring` on scalars | 40 |
| A5 `traversal_diag_cone` | 135 | `s ∈ [k+½, k+1]` ⇒ `γ(s+½) − γ(s) = (k+1−s) e_k + (s−k−½) e_{k+1}` | `s = k + t`, `t ∈ [½, 1]`: `γ s = P k + t e_k` (A3), `γ (s+½) = P (k+1) + (t − ½) e_{k+1}` (A3 with `k+1`, `t − ½ ∈ [0, ½]`), and `P (k+1) = P k + e_k`; collect | A3, `edge`, `Nat.cast_succ`/`Int.cast` bookkeeping for `((k+1 : ℕ) : ZMod n)` | 70 |
| A6 `traversal_cut_cone` | 142 | `s ∈ [0, ½]` ⇒ `γ(s + n − ½) − γ(s) = −((½−s) e_{−1} + s e_0)` | `γ (s + n − ½) = γ (s − ½)` (A1 with `x = s − ½`), `s − ½ = (−1 : ℤ) + (s + ½)` with `s + ½ ∈ [½, 1]` (A3), `γ s = P 0 + s e_0` (A3, `k = 0`), `P 0 = P (−1) + e_{−1}`; collect | A1, A3, `edge`, `Int.cast_neg`, `Int.cast_one` | 70 |
| A7 `Embedded.regular` | 148 | embedded ⇒ regular | `regular_iff_edges`: edges nonzero by `edge_ne_zero`; if `e_i = r e_{i−1}`, `r < 0`, the point `P i − min(1, |r|)/2 · … ` lies in `edgeSegment P (i−1) ∩ edgeSegment P i` and differs from `P i`, contradicting `consecutive (i−1)` (`edgeSegment`, `edgePoint` parameters `s = 1 − t|r|`, `t` small) | RegularLocus.lean:19 `regular_iff_edges`, Polygon.lean:51-57, `Set.ext_iff` on `consecutive` | 120 |
| A8 `Embedded.traversal_injective` | 152 | `γ x = γ y` ⇒ `y − x ∈ nℤ` | reduce to `x, y ∈ [0, n)` by A1; let `k = ⌊x⌋`, `l = ⌊y⌋` (as `ZMod n` indices). `k = l`: same edge, `fract x ≠ fract y` ⇒ `(fract x − fract y) • e_k = 0` ⇒ `e_k = 0`, contradiction. `remote k l`: `remote_disjoint`. adjacent distinct (`adjacent_distinct_cases`): the common point is `P (k+1)` (or `P k`), which `γ` attains on `[k, k+1)` only at parameter `0` of edge `k+1` — but then the other point has `fract ≠ 0` on the edge ending there, forcing `(1 − fract) • e = 0`; wrap pair `(n−1, 0)` included via `ZMod` | Polygon.lean:63-66 `adjacent`/`remote`, G1Consequences.lean:38 `adjacent_distinct_cases`, `Set.disjoint_left`, `Int.floor_eq_iff` | 250 |
| A9 `Embedded.traversal_sub_ne_zero` | 157 | on the region the secant vector is nonzero | if `γ t = γ s` then `t − s = m n` (A8); `½ ≤ t − s ≤ n − ½` forces `0 < m < 1`, impossible for `m : ℤ` | A8, `Int.cast` inequalities, `omega`-free `nlinarith` | 50 |
| A10 `Embedded.shift` | 162 | `Embedded (shift a P)` | `edge_shift`, `edgeSegment_shift` (Polygon.lean:71, 79), `shift a P (i+1) = P (i+1+a)`; `remote` is an index predicate (`remote i j ↔ remote (i+a) (j+a)` by `ring_nf` on `ZMod`) | Polygon.lean:71-81 | 60 |
| A11 `embedded_of_generic_of_isEmpty_crossing` | 169 | generic + no crossing ⇒ embedded | `edge_ne_zero` from `g1` (G1Consequences.lean:108, clause `hg.2.1`); `consecutive` = `g1_successive_intersection` (G1Consequences.lean:19); `remote_disjoint`: a common point of remote segments is an `IsCrossing P {i, j}` (Crossings.lean:12), contradicting `IsEmpty` | G1Consequences.lean:19, 108; Crossings.lean:12-15; `Set.not_nonempty_iff_eq_empty`, `Set.disjoint_iff_inter_eq_empty` | 60 |

### U-B

| leaf | line | statement in words | proof sketch | tools | size |
|---|---|---|---|---|---|
| B1 `secantRetract_mem` | 176 | the clamp lands in the region (`n ≥ 1`) | unfold; `d ∈ [½, n − ½]` by `le_max_left`, `max_le` (needs `½ ≤ n − ½`), `s ∈ [0, n − d]` by `le_max_left`, `max_le` (needs `0 ≤ n − d`); then the four inequalities are `s ≥ 0`, `s + d ≤ n`, `½ ≤ d`, `d ≤ n − ½` | `le_max_left/right`, `max_le`, `min_le_left/right`, `le_min`, `linarith` | 60 |
| B2 `secantRetract_eq_self` | 180 | identity on the region | on the region `min (n−½) (t−s) = t − s`, `max ½ (t−s) = t − s`, `min (n − (t−s)) s = s`, `max 0 s = s`; `Prod.ext` with `s + (t − s) = t` | `max_eq_right`, `min_eq_right`, `Prod.ext`, `add_sub_cancel` | 50 |
| B3 `continuous_secantRetract` | 184 | continuity | `Continuous.max`, `Continuous.min`, `continuous_fst`, `continuous_snd`, `continuous_const`, `Continuous.prodMk` (`Continuous.prod_mk`) | Mathlib/Topology/Order/Lattice.lean (`Continuous.max/min`) | 40 |
| B4 `increment_eq_principalAngle_of_cone` | 192 | path in the closed positive cone of a regular pair `(u,v)` from ray `u` to ray `v`: lift increment `= principalAngle u v` | `g s := θ s − θ a − principalAngle u (c s)`; each `c s` is a `RegularPair` partner of `u` (a nonneg combination `αu + βv`, not both zero, is never a nonpositive multiple of `u`: else `β v` would be a nonpositive multiple of `u`, contradicting `huv`), so `cornerRotor u (c s) ∈ slitPlane` (`regularPair_slitPlane`) and `principalAngle u ∘ c` is continuous on `[a,b]` (`Complex.continuousAt_arg`, RegularPairs.lean:54 `principalAngle = arg (cornerRotor u ·)`); `Circle.exp (g s) = 1` for every `s` (both `θ s − θ a` and `principalAngle u (c s)` are the angle from `u` to `c s` modulo `2π`: `IsLiftOn.circleExp_coe`, `principalAngle_coe_angle`); `g a = 0` (`principalAngle u (r u) = 0`, `principalAngle_eq_zero_iff`); `const_of_circleExp_eq_one` on `Icc a b` gives `g b = 0`; finally `principalAngle u (r v) = principalAngle u v` (`Complex.arg_real_mul`) | TurnLift.lean:50, 96; RegularPairs.lean:31, 54, 70; RotationNumber.lean:13; Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean:185, 579; `isPreconnected_Icc` | 200 |
| B5 `abs_increment_le_pi_of_halfplane` | 203 | nonvanishing path in `{⟪N,·⟫ ≥ 0}`: `|Δθ| ≤ π` | let `ν = arg N`; `⟪N, c s⟫ ≥ 0` ⇔ `cos (θ s − ν) ≥ 0` (`planeDot` of `(cos θ, sin θ)` with `N = |N| (cos ν, sin ν)`); `f s := θ s − ν` is continuous on `[a,b]` with `cos (f s) ≥ 0`, i.e. `f s ∈ ⋃_m [2πm − π/2, 2πm + π/2]`; the image of `[a,b]` is an interval (`IsPreconnected.image`, `isPreconnected_Icc`) contained in that union, hence in one component (an interval meeting two components contains a point of an open gap `(2πm + π/2, 2πm + 3π/2)` where `cos < 0`); so `|f b − f a| ≤ π` | Mathlib/Topology/Connected/Basic.lean:294, `Real.cos_nonneg_iff`/`Real.cos_neg_of_pi_div_two_lt_of_lt`, `IsPreconnected.intermediate_value` | 180 |
| B6 `IsLiftOn.neg` | 210 | `−u` is lifted by `θ + π` | `Real.cos_add_pi`, `Real.sin_add_pi`, `Prod.neg_mk`; continuity `ContinuousOn.add` | Mathlib trig | 30 |
| B7 `increment_coe_angle` | 216 | `(θ b − θ a : Angle) = arg (c b) − arg (c a)` | `IsLiftOn.circleExp_coe` at `a`, `b`: `Circle.exp (θ s) = planeComplex (normalize (c s))`, and `arg (normalize (c s)) = arg (c s)` (positive multiple, `Complex.arg_real_mul`; `planeComplex_smul`); `Real.Angle.coe_sub`, `Circle.exp` ↔ `Real.Angle` (`Circle.exp_eq_exp` / `Real.Angle.coe_eq_coe_iff`) | TurnLift.lean:50; TurningNumber.lean:60 `circleExp_planeComplex`; Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean:185; Mathlib/Analysis/SpecialFunctions/Trigonometric/Angle.lean:77 | 100 |

### U-C

| leaf | line | statement in words | proof sketch | tools | size |
|---|---|---|---|---|---|
| C1 `diag_increment` | 250 | `Θ(n−½, n) − Θ(0, ½) = Σ_i ϑ_i − ϑ_0` | `φ s := (s, s+½)` maps `[0, n−½]` into the region; `θ := Θ ∘ φ` is an `IsLiftOn` of `s ↦ secantDir P (φ s)` on every subinterval (`IsSecantLift.isLiftOn_comp`, skeleton 105). Pieces: on `[k, k+½]` (`k < n`) the direction is constant (A4) ⇒ `θ(k+½) = θ k` (`IsLiftOn.increment_eq_zero_of_const`, TurnLift.lean:68); on `[k+½, k+1]` (`k+1 < n`) the vector is `(k+1−s) e_k + (s−k−½) e_{k+1}` (A5), a cone path from ray `e_k` to ray `e_{k+1}` ⇒ `θ(k+1) − θ(k+½) = principalAngle e_k e_{k+1} = ϑ_{k+1}` (B4, `hreg`). Sum over `k = 0..n−2` of `ϑ_{k+1}` plus the last constant piece `[n−1, n−½]` = `Σ_{j=1}^{n−1} ϑ_j = Σ_{i : ZMod n} ϑ_i − ϑ_0` (`Finset.sum_range_succ`, `sum_range_natCast_eq_sum_zmod` TurnLift.lean:291, `Fin`/`ZMod` cast of `k+1`) | skeleton 105; TurnLift.lean:55, 68, 291; A4, A5, B4 | 350 |
| C2 `cut_increment` | 258 | `Θ(½, n) − Θ(0, n−½) = ϑ_0` | `φ s := (s, s + n − ½)` on `[0, ½]` lies in the region (`t − s = n − ½`, `t ≤ n`); the vector is `−((½−s) e_{−1} + s e_0)` (A6); by B6 the lift of the negated path differs by `π`, so the increment equals that of the cone path from ray `e_{−1}` to ray `e_0`, which is `principalAngle e_{−1} e_0 = ϑ_0` (B4 with `hreg 0`, `edge P (0−1) = edge P (−1)`) | A6, B4, B6, `IsLiftOn.increment_eq` (TurnLift.lean:55) | 80 |
| C3 `top_increment_eq_left` | 265 | top-leg increment = left-leg increment | for `s ∈ [½, n−½]`: `secantDir P (s, n) = normalize (γ n − γ s) = normalize (γ 0 − γ s) = −secantDir P (0, s)` (A1 with `x = 0`, `normalize_neg` TurnLift.lean:231); both `(s, n)` and `(0, s)` lie in the region; `Θ ∘ topPath` is a lift of the negated left direction, `(Θ ∘ leftPath) + π` is another (B6); `IsLiftOn.increment_eq` | A1, B6, TurnLift.lean:55, 231 | 80 |
| C4 `left_increment` | 275 | at a supporting base vertex: `|I| ≤ π` and `(I : Angle) = π − ϑ_0` | vector `c t := γ t − P 0` on `[½, n−½]`, nonzero (A9 with `p = (0,t)`); half-plane: `γ t = (1−τ) P k + τ P (k+1)` (A3) so `⟪N, γ t − P 0⟫ = (1−τ)⟪N, P k − P 0⟫ + τ⟪N, P (k+1) − P 0⟫ ≥ 0` (`hsupp.2`); B5 ⇒ `|I| ≤ π`. Endpoints: `c ½ = ½ e_0` (A3, `k = 0`), `c (n−½) = γ(−½) − P 0 = −½ e_{−1}` (A1, A3 with `k = −1`, `t = ½`); B7 ⇒ `(I : Angle) = arg(−½ e_{−1}) − arg(½ e_0) = (arg e_{−1} + π) − arg e_0` (`Complex.arg_neg_coe_angle` Arg.lean:449, `Complex.arg_real_mul` :185) `= π − ϑ_0` (`principalTurn_coe_angle` RotationNumber.lean:24 with `hreg`, `edge P (0−1) = edge P (−1)`); `abel` | A1, A3, A9, B5, B7; RotationNumber.lean:24; Arg.lean:185, 449 | 200 |
| C5 `exists_supporting_vertex_turn_ne_zero` | 286 | a supporting vertex with nonzero turn exists | `Finset.univ.exists_min_image` (Mathlib/Data/Finset/Max.lean:534) for `x`, then among the minimisers for `y` (or minimise the lexicographic pair `(x, y)` via `toLex`); `N = (1, 0)`: `⟪N, P j − P i⟫ = (P j).1 − (P i).1 ≥ 0`. Turn `≠ 0`: `principalAngle_eq_zero_iff` (RegularPairs.lean:70) would give `e_i = r e_{i−1}`, `r > 0`; `x`-minimality gives `(e_{i−1}).1 ≤ 0 ≤ (e_i).1`, hence both `x`-components vanish and both edges are vertical; `y`-minimality among leftmost vertices gives `(P (i−1)).2 ≥ (P i).2 ≤ (P (i+1)).2`, so `e_{i−1}` points down and `e_i` up, contradicting `r > 0` (edges nonzero by `edge_ne_zero`) | Mathlib/Data/Finset/Max.lean:534; RegularPairs.lean:70; `Prod` coordinates of `edge` | 150 |

## 4. Truth checks (python, 2026-09-14; seeds fixed; scripts in the probe transcript)

* Key identity `Σϑ = 2I + 2ϑ_0` and `Σϑ/2π = ±1`: 6 random star-shaped simple polygons with an inserted
  flat vertex (both orientations) and a non-star-shaped L-shaped octagon; agreement to `1e-12`; sign =
  sign of `ϑ_0` at the lowest-leftmost vertex (PLDISCS_FEASIBILITY.md §1.3).
* B4 sector lemma: 2 000 random regular pairs (including flat pairs, `ϑ = 0`) and random continuous
  cone paths `α(s)u + β(s)v` from ray `u` to ray `v`: `max |lift increment − principalAngle u v| = 6.2e-15`.
* B5 half-plane bound: 2 000 random nonvanishing paths in a random closed half-plane (angle random
  walk clipped to `[−π/2, π/2]`, random radii): `max |increment| = 3.1394 < π`, 0 violations.
* A4/A5/A6 piece formulas: 600 random checks on random `LabelledTuple`s (`n = 3..8`, any position):
  `max error = 6.4e-15`.
* C1-C4 on 60 random simple polygons based at the lowest-leftmost vertex (6 000-step lifts):
  diagonal `= Σϑ − ϑ_0` (err `4.7e-14`), cut `= ϑ_0` (`1.8e-14`), top = left (exact), `|I| ≤ π` (no
  excess), `(I − (π − ϑ_0))/2π` integer (residual `5.4e-15`).

No leaf is believed false.  The two whose *hypotheses* deserve a reviewer's eye: B4 requires the cone
path's endpoints on the rays of `u` and `v` with `(u,v)` a `RegularPair` (flat allowed, antiparallel
excluded) — exactly what A5/A6 deliver under `hreg`; C4's half-plane containment needs `hsupp` in the
form `∀ j, 0 ≤ ⟪N, P j − P 0⟫`, which is the definition of `IsSupportingVertex P N 0`.

## 5. Fidelity risks (verbatim from PLDISCS_FEASIBILITY.md §1.8)

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

## 6. Hand-over checklist

1. Three prover subagents, one per unit, same file, disjoint line ranges (U-A 114-173, U-B 176-222,
   U-C 250-291); merge by leaf.  2. After merge: `lake env lean` 0 errors, 0 `sorry`, `#print axioms
   SM.cb_embedded_rotation` = `[propext, Classical.choice, Quot.sound]`.  3. Port as `work/lean/SM/EmbeddedRotation.lean`
   (statement part unchanged), map row 104 → `SM.cb_embedded_rotation`, review brief to state
   "proved independently of lem:gauss-two-discs (row 57)" (FR-ER-5) and the reading of "embedded" (FR-ER-1).
