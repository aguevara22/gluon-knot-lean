# DESIGN A — rows 99 cf:thm-carrierfloor and 100 thm:floor (fidelity-first), 2026-09-15

Architect A (fidelity emphasis). Companion sketch: `work/drafts/floor/Sketch_A.lean` (483 lines;
`cd work/lean && lake env lean ../drafts/floor/Sketch_A.lean` exits 0 in ~10 s warm; the statement
sections §1-§6 and §8 are sorry-free, the proof-route sections §7 and §8.1 carry 13 `sorry` leaves).
Axioms of the statement bundles: `CarrierFloorData` = [propext, Classical.choice, Quot.sound, SM.lp_lm]
(the policy axiom behind `P`), `FloorTheoremData` adds `SM.lit_homfly` (behind `cornerHomfly = homfly ∘ positiveLift`,
as def:C), `TransverseFrontBound` = [.., SM.lp_lm]. Nothing written under work/lean.

Sources read: sm-3-statesum.tex 4282-4339 (row 99 statement), 4340-4575 (proof), 4576-4602 (row 100 + proof),
3644-3700 (cf:lem-rounding), 3870-3891 (cf:lem-curl), 3328-3340 (def:transverse-front), 981-992
(lp:coefficient-transport), 325-345 (def:positive-lift); sm-1-polygons.tex 407-470 (lem:rot, lem:uniformrot);
the memo work/drafts/gap2/GAP2_STATEMENTS_MEMO.md §3(c), §4 (99, 100) and Gap2Statements.lean §1, §7-§8; the
accepted modules listed in the sketch header; work/AUTHOR_NOTES.md D-GAP2, D-GAP2-2b; work/drafts/curl/PLAN_FINAL.md §0-§2.

## 0. Decisions in one table

| question | decision |
|---|---|
| one bundle or four | FOUR clause bundles `CarrierFloorRData / AData / BData / CData` (one field per printed clause each) and ONE row bundle `CarrierFloorData` with fields `clauseR clauseA clauseB clauseC`; the row theorem `SM.cf_thm_carrierfloor : CarrierFloorData` is one declaration; (R)(A)(B) can be proved and reviewed now, (C) waits for row 94 |
| row names | `SM.cf_thm_carrierfloor : CarrierFloorData`, `SM.thm_floor : FloorTheoremData` — neither row has a fixed name in work/lean/axiom-policy.json `targets` (only thm:C-S3/S5/S7, thm:C-soft, thm:comparison do); the cf_* / thm_* convention of the accepted rows |
| (C) hypothesis class | `CarrierFloorCHyp C X`: `shadow : X.Γ = Shadow.single C`, `positive`, `turn_exists : Regular C.P`, `turn_ne`, `turn_lt_pi`, `generic : (Shadow.single C).Generic`, `alternative : UniformOrOneDissent C` — exactly the printed list, redundant printed clauses KEPT (constructor `CarrierFloorCHyp.of_diagram` derives them, sketch §5) |
| "after reversing if necessary" | literal: `UniformOrOneDissent C := AllPosOrOneNeg C.P ∨ AllPosOrOneNeg (reversal C.P)` (the memo's 4-way disjunction is a theorem, not the definition); for thm:floor `AllLeftOrOneRight Q ∨ AllLeftOrOneRight (reversal Q)` on the corner polygon |
| (B) orientation | the claim is made for the NORMALISED polygon (`BClaim C D` or `BClaim C.reverse D.reverse`), FR-FL-B1 |
| `f_D ≠ 0` clause | literal: `zZeroPart (P X) ≠ 0 → bound ≤ mindegAZ (zZeroPart (P X))`, with `zZeroPart f` the `z⁰` row of `f` as an element of `R` (new def, two coefficient lemmas proved in the sketch); the memo's support form becomes a corollary |
| the mirror `D̄` | the printed `D̄` is the CROSSING SWITCH (sm-3:4431, 4533), not the accepted reflection `Diagram.mirror`; new `Diagram.switchAll` + its transport (unit U-SW), FR-FL-C4; the reflection route is the recorded fallback |
| the rotation "so that u is the downward vertical" | applied to the SMOOTH curve only (unit U-ROT); the polygon `X` never moves because carrying is record-level — depends on the contact lane keeping `Carries` record-level, FR-FL-C6 |
| row-94 bound | hypothesis `TransverseFrontBound` (sketch §1), `cf_thm_carrierfloor_C_of_bound : TransverseFrontBound → CarrierFloorCData` (D-F11/D-F14 pattern); `thm_floor_of_bound` likewise |

## 1. Row 99 — clause-by-clause transcription (sm-3:4282-4339) and fidelity risks

### (R) sm-3:4283-4290 → `CarrierFloorRData` (sketch §2)

| printed | field | accepted vocabulary |
|---|---|---|
| "Let D be an oriented knot diagram and −D the same diagram with every arrow reversed. Then P_{−D} = P_D" | `P_reverse : ∀ X, X.componentCount = 1 → P X.reverse = P X` | `Diagram.reverse` (LinkDiagram.lean:1213, "reversing the orientation of every component"), `P` (LocalPolynomial.lean:22) |
| "consequently an oriented knot and its reverse have the same polynomial" | `knot_reverse : ∀ X X', X.componentCount = 1 → LinkEquiv X X' → P X'.reverse = P X` | the knot = the `LinkEquiv` class (design D2, LinkMoves.lean:760); "its reverse" is presented by `X'.reverse` for any diagram `X'` of the knot; the polynomial of a knot is `P`/`homfly` of any diagram (`homfly_descent`, LinkInterfaces.lean:395) |
| "Moreover −D has the same crossing signs" | `sign_reverse` | accepted `Diagram.reverse_sign` (LinkDiagram.lean:1219) verbatim |
| "and the same writhe as D" | `writhe_reverse` | accepted `Diagram.reverse_writhe` (1227) |
| "and the rotation of its underlying plane curve is the negative of that of D" + scoping sentence "rot as in lem:rot for polygons and cf:def-turning for the underlying plane curve of a smooth diagram" | `rot_reverse_polygon : X.Γ = single C → X.reverse.Γ = single C.reverse ∧ rotationNumber C.reverse.P = −rotationNumber C.P`; `rot_reverse_curve : ∀ γ : ClosedC1Curve, γ.reverse.rot = −γ.rot` | `rotationNumber_reversal` (RotationReversal.lean:55), `ClosedC1Curve.rot_reverse` (TurnLift.lean:261) |

FR-FL-R1 (knot vs link): the field is stated for knot diagrams as printed; the printed proof (4349-4356) proves
it "on all oriented link diagrams", so the library lemma `ur_P_reverse_all` is unconditional and the row field is
its restriction. FR-FL-R2 ("its reverse have the same polynomial"): the knot is the `LinkEquiv` class; nothing spatial
is asserted (D2). FR-FL-R3 (smooth diagram): the scoping sentence's smooth case is rendered as the accepted curve
identity `rot_reverse`; the reversal of a CARRIED smooth diagram (`Carried γ X → Carried γ.reverse X.reverse`, signs
and writhe kept) is not a field — no consumer reads it ((B) and (C) normalise at polygon level). If the reviewer wants
the smooth diagram itself reversed, add the record-transport field (est. +250 lines) — flagged, not adopted.

### (A) sm-3:4291-4305 → `Round`, `junctionTemplate`, `CarrierFloorAData` (sketch §3)

`Round C D ε h := CornerRounding.roundedWitness h` (Rounding.lean:3008) — the record IS the accepted named construction,
a function of `(L, D, ε)`; the admissibility proof `h : Admissible C D ε` (Rounding.lean:585: `turn_ne`, `0 < ε`,
`ε < clearance C`) is "ε ∈ (0, ε₀(L))" with `ε₀(L) = clearance C` (571, the witness of `cf_lem_rounding.exists_clearance`).

| printed | field |
|---|---|
| "returns one curve and one diagram at those data" | `one_record` (proof irrelevance, `rfl`), `one_curve : (Round …).Lε = roundedLoop h` (`rfl`), `one_diagram : Nonempty (Carried (Round …).Lε D.toDiagram) ∧ smoothWrithe = D.writhe` (the record's own `carried`, `same_writhe`) |
| "the junction inserted at the corner q_i is determined by ε, by the two incident unit directions and by the transition profile, which is fixed once and for all" | `junction_determined`: on `[a j, b j]`, reparametrised to `s ∈ [0,1]`, the curve equals `junctionTemplate (C.P j) (uDir C j) (vDir C j) ε s := juncArc (q − ε u) ε (arg u) (principalAngle u v) s` — a function of `(q, u, v, ε)` alone; the profile is `Real.smoothTransition` inside `juncArc` (Rounding.lean:483) |
| "the arc length ℓ is then determined by the endpoint condition" | `length_determined`: `speed · (b j − a j) = juncLen ε ϑ_j` (480) and `L_ε(b j) = q_j + ε v_j` (the endpoint condition) |
| "and the rest of the curve is L itself" | `rest_is_L` = accepted (a) (`outside`, `straight`) |

FR-FL-A1: `junction_determined` is stronger than the memo's image equality (it fixes the parametrisation); it is true of
the construction (`curveMap_on_junction` Rounding.lean:1668 with `θu C j` replaced by `arg (uDir)`: `dirOf_θu` 1207 +
`G1_dirOf_arg` 1172 give `θu ≡ arg (uDir) mod 2π`; `principalAngle (uDir) (vDir) = principalTurn` needs scale-invariance
of `principalAngle` — `cornerRotor` is `star (planeComplex u) * planeComplex v`, so `Complex.arg_real_mul`; ~40 lines).
FR-FL-A2: (A) asserts "uniqueness of the fixed construction's record, not uniqueness among all smoothings" (4362-4364) —
rendered by making `Round` a definition; no ∀-over-witnesses field exists (correct: other `RoundingWitness`es exist).

### (B) sm-3:4306-4318 → `AllPosOrOneNeg`, `UniformOrOneDissent`, `TangencyCount`, `BClaim`, `CarrierFloorBData` (sketch §4)

| printed | Lean |
|---|---|
| "closed polygon with nonzero edges and nonzero principal turns, finitely many transverse double points, no triple points, no corner at a double point and no corner on a non-incident edge, carrying a diagram D" | `C : PolyComp`, `D : PolygonDiagram C` (its `generic : (Shadow.single C).Generic` = regular/tail_off/transverse/no_triple, Rounding.lean:80-93), `∀ i, principalTurn C.P i ≠ 0` |
| "after reversing orientation if necessary, either all principal turns are positive, or exactly one is negative and all others are positive" | `UniformOrOneDissent C := AllPosOrOneNeg C.P ∨ AllPosOrOneNeg (reversal C.P)` |
| "Put R = |rot(L)|" | `|rotationNumber C.P|` (RotationNumber.lean; lem:rot `SM.rotation_number`) |
| "there are a direction u ∈ S¹ and an ε₁ > 0 such that for every ε ∈ (0, ε₁)" | `∃ u ε₁, euclideanLength u = 1 ∧ 0 < ε₁ ∧ ε₁ ≤ clearance C ∧ ∀ ε, 0 < ε → ε < ε₁ → ∀ h : Admissible C D ε, …` |
| "the rounded curve L_ε of the record Round(L,D,ε) has exactly R points at which its unit tangent equals u and exactly R at which it equals −u" | `TangencyCount (Round C D ε h) u R ∧ TangencyCount … (−u) R`: the parameter set `{t ∈ [0,1) ∣ W.T t = u}` is FINITE with `ncard = R` |
| "at each of them the tangent crosses that direction in the positive sense" | third conjunct: each such `t` lies in a junction `(a j, b j)` and `0 < deriv (W.θ j) t` (`θ j` the junction lift, `θ_lift`, of cf:lem-rounding (b)) |

FR-FL-B1 (the normalised orientation): for an all-negative `L` the tangent crosses `u` in the NEGATIVE sense, so the
literal claim for `Round(L, D, ε)` is false in the reversed alternative; the printed proof "perform[s] the allowed
normalization once" (4368-4370) and proves the claim for the normalised polygon. Rendering:
`tangencies : … → (AllPosOrOneNeg C.P ∧ BClaim C D) ∨ (AllPosOrOneNeg (reversal C.P) ∧ BClaim C.reverse D.reverse)`,
with `PolygonDiagram.reverse D := ofDiagram D.toDiagram.reverse rfl`. This is what (C) consumes (it normalises first).
The count clause alone is orientation-symmetric but proving it for the un-normalised polygon needs the rounding/reversal
commutation (not accepted); not adopted. FR-FL-B2 ("points" of the curve): parameters of the fundamental period; the
tangent is constant on straight parts, so every such parameter is inside a junction; `ncard` needs the explicit
`Set.Finite` conjunct (`ncard` of an infinite set is `0`). FR-FL-B3 ("crosses in the positive sense"): positive
derivative of the accepted junction lift, as the printed proof reads it ("unique with positive angular derivative",
4394-4396); a local ∃-lift formulation is implied. FR-FL-B4: `ε₁ ≤ clearance C` is added so that the record exists at
every `ε ∈ (0, ε₁)` (the proof takes `ε₁ = ε₀(L)`, 4371); the admissibility proof is quantified (`∀ h`), irrelevant by
`one_record`. FR-FL-B5: "nonzero edges" is inside `Regular` (`D.regular`), "finitely many double points" is implicit in
`Generic.transverse` (finitely many edge pairs) — as in the accepted cf:lem-rounding row.

### (C) sm-3:4319-4337 → `CarrierFloorCHyp`, `zZeroPart`, `CarrierFloorCData` (sketch §5)

Hypothesis class, one field per printed clause (the "versus `Diagram.generic` / `Shadow.single`" comparison):

| printed clause | field | relation to the accepted class |
|---|---|---|
| "oriented knot diagram … whose underlying plane curve is a closed polygon L" | `shadow : X.Γ = Shadow.single C` | one component is `(single C).c = 1` (LinkDiagram.lean:1589) |
| "all of whose crossings are positive" | `positive : ∀ x, X.IsPositive x` | `IsPositive` (547) |
| "with writhe w" | `X.writhe` in the conclusion | `writhe` (577) |
| "all principal turns existing" | `turn_exists : Regular C.P` | = `X.generic.regular 0` after `shadow` (redundant, kept) |
| "nonzero" | `turn_ne` | not in `Generic` (zero turns allowed there) — genuinely extra |
| "and of magnitude below π" | `turn_lt_pi : ∀ i, |principalTurn C.P i| < π` | implied by `Regular` (`principalAngle_bounds`, RegularPairs.lean:56: the principal angle of a regular pair lies in `(−π, π)`) — redundant, kept |
| "finitely many double points, all transversal, no triple points, none of them a corner of L, no corner of L on a non-incident edge" | `generic : (Shadow.single C).Generic` | field for field: `transverse` (+finiteness), `no_triple`, `tail_off` (a vertex on no non-incident edge segment covers both corner clauses), `regular`; = `X.generic` after `shadow` (redundant, kept) |
| "R the absolute value of its Whitney rotation number" | `|rotationNumber C.P|` | lem:rot |
| "after reversing the orientation if necessary … either every principal turn is positive, or exactly one is negative and every other is positive" | `alternative : UniformOrOneDissent C` | as (B) |

`CarrierFloorCHyp.of_diagram` (PROVED in the sketch) builds the class from `shadow`, `positive`, `turn_ne`, `alternative`.
FR-FL-C1: the three redundant fields are printed hypotheses ("stated here so that no generic parent polygon is assumed",
4327-4329) and are kept so the class is exactly the printed one; consumers use `of_diagram`. FR-FL-C2 (the conclusion):
`((1 − w : ℤ) : ℝ) − |rot| ≤ (mindegAZ (P X) : ℝ)` — `R` real as printed; `P X ≠ 0` (lp:core `ne_zero`) makes `mindegAZ`
the printed `mindeg_a` (def:adeg, AdegDefinition.lean). FR-FL-C3 (`f_D`): `zZeroPart f := ofCoeff (filter (·.2 = 0) f.coeff)`
is `[z⁰]P_D` read inside `R` so that `mindeg_a` applies; the row field is literal (`zZeroPart (P X) ≠ 0 → …`); the
memo's support form `coeffAt d k (P X) ≠ 0 → bound ≤ d` is a corollary (`coeffAt_zZeroPart_zero/of_ne`, proved).
FR-FL-C4 (mirror, PROOF ROUTE): see §3(C) step 2. FR-FL-C5: the parenthesis "which by clause (R) changes neither P_D,
nor the crossings and their signs, nor w, nor R" is a proof remark, rendered by consuming (R) in the route, not a field.

## 2. Row 100 thm:floor (sm-3:4576-4585) → `AllLeftOrOneRight`, `CarrierUniformOrOneDissent`, `FloorTheoremData` (sketch §8)

| printed | Lean |
|---|---|
| "Let Q be a subpolygon of a decomposition of a generic polygon" | `hn : 3 ≤ n`, `P`, `hP : Generic P`, `S`, `hS : IsDecomposition hn hP S`, `q : Component hn hP S`, read as `ccpCornerPolygon hn hP S q` (def:C, CornerStateSum.lean header) |
| "after possibly reversing its orientation either all turns are left, or exactly one turn is right" | `CarrierUniformOrOneDissent := AllLeftOrOneRight Q ∨ AllLeftOrOneRight (reversal Q)`, `AllLeftOrOneRight Q := (∀ j, turn Q j = 1) ∨ (∃ j₀, turn Q j₀ = −1 ∧ ∀ j ≠ j₀, turn Q j = 1)` (def:chirotope `turn : SignType`, left = 1; `turn_reversal`) |
| "mindeg_a H⁺_Q ≥ 1 − m_Q − |r_Q| = d_Q" | `cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) ∧ 1 − (m_Q : ℝ) − |carrierRotation| ≤ (mindegAZ … : ℝ)` (both the `ℤ` form with def:C's `cornerSlot` and the printed real form; `cornerSlot_cast` CornerStateSum.lean:87 is the printed `=`) |
| "H⁺_Q ∈ ℤ[a^{±1}, z²], so mindeg_z H⁺_Q ≥ 0" | `z_parity : (∀ d k, coeffAt d k H ≠ 0 → ∃ j : ℕ, k = 2 j) ∧ 0 ≤ mindegZZ H` (no turn hypothesis; the printed "so" is the second conjunct) |

FR-FL-F1: the memo's `CarrierUniform ∨ one-dissent-of-sign-τ` (4-way) is replaced by the literal reversal form; equivalent
since carrier turns are nonzero (lem:carriers (ii)). FR-FL-F2: "all turns are left" = `turn = 1` for every corner of the
corner polygon (original vertices and smoothing corners alike, lem:carriers (ii)). FR-FL-F3: `z_parity` is stated for every
subpolygon of a decomposition (the printed sentence has no turn hypothesis and is lp:core's knot clause).

## 3. Proof routes (accepted lemmas by file:line)

(R) — unit U-R, ~350 lines. `Q := fun D => P D.reverse` is an `RCompetitor` (CoefficientTransport.lean:23): `planar`,
`reidemeister_I/II/III` from `reverseCarries_linkEquiv`'s generator pieces (LinkMoves.lean:2418, 2455, 2459, 3071, 3117,
3231) and `lp_core.planar/reidemeister_*` (PolynomialBlock.lean:1117-1150); `circle`: `IsCrossingFreeCircle` is carried
(same `c`, crossings in bijection by `Shadow.reverseCrossingEquiv`, LinkDiagram.lean:1199); `skein`: `IsSkeinTriple.reverse`
(LinkMoves.lean:3318, sides kept) + `lp_core.skein`. Then `coefficient_transport Q P` (137). `knot_reverse` from
`P_eq_homfly` + `homfly_descent` (PROVED in the sketch from `ur_P_reverse_all`). Rotation fields: accepted, PROVED in the
sketch (`rotationNumber_reversal` needs `Regular`, from `X.generic.regular`).

(A) — unit U-A, ~120 lines: `one_record`, `one_curve`, `one_diagram`, `rest_is_L` PROVED in the sketch (`rfl` /
projections); `junction_determined` from `curveMap_on_junction` (Rounding.lean:1668) + `dirOf_θu` (1207) + `G1_dirOf_arg`
(1172) + scale invariance of `principalAngle`; `length_determined` from `b_sub_a` (1277: `b j − a j = ℓ j / Λ`), `speed = Λ`,
`ℓ = juncLen ε (turn C j)` (504) and `curveMap_b` (1661: `L_ε(b j) = A1 j = q_j + ε v_j`).

(B) — unit U-B, ~3000 lines, the printed proof 4366-4416 with the direction a parameter: library lemma
`ub_tangencyCount_of_admissible` (for every `u` with `AdmissibleDirection C u`: unit, `±u` no edge direction, `±u` outside
the closed swept arc `{dirOf (arg u_j + s ϑ_j)}` of every negative turn — sm-3:4372-4376) at every admissible `ε`, and
`ub_exists_admissibleDirection`; the row's `BClaim` follows with `ε₁ = clearance C` (PROVED in the sketch from the two
leaves). Inside: (i) `rot(L) = R ≥ 1` in both normalised cases by `uniform_rotation` (UniformRotation.lean:64) through
`principalTurn_sign` (12); (ii) the concatenated lift: the junction lifts `θ j` (`θ_lift`, `θ_const_left/right`, Rounding.lean
§5) glued with the constant straight-part arguments, seam in a straight part (`b 0 < a 1`); increment `Σ ϑ_j = 2π rot(L)`
(`G2_sum_turn` 1289); (iii) levels `φ + 2πk` met only inside increasing junctions (edge directions excluded by `hu`; the
decreasing junction excluded by the arc clause), each exactly once (`θ_unique`, `θ_strict`, `immersion`): the count
`⌊x + R⌋ − ⌊x⌋ = R` (`Int.floor` arithmetic); (iv) finiteness from finitely many junctions and uniqueness per junction;
(v) positive derivative: `θ_strict` + `immersion` ⇒ `0 < deriv (θ j) t` on the open junction. Existence of `u`: the forbidden
set is `2k` points plus (one-dissent) a closed arc of length `α < π` with its antipode, total length `2α < 2π`; pick the
midpoint direction of the complementary open arc and perturb off the finite set (or `Set.Finite`-avoidance on `S¹`).

(C) — sm-3:4417-4575. Chain of diagrams, all on the FIXED polygon `X` except step 1:
1. Normalise (unit U-C, uses (R)): if `alternative` holds for `reversal C.P`, replace `(C, X)` by `(C.reverse, X.reverse)`:
   `P` kept (`P_reverse`), `writhe` kept (`reverse_writhe`), signs kept (`reverse_sign`), `|rot|` kept
   (`rotationNumber_reversal`), `generic` = `X.reverse.generic`, `turn_ne/turn_lt_pi` via `principalTurn_reversal`
   (RotationReversal.lean:49). WLOG `AllPosOrOneNeg C.P`.
2. Mirror (unit U-SW + U-ι): `D̄ := X.switchAll` (`withOver underStrand`, LinkDiagram.lean:637) — "the diagram with every
   crossing switched", SAME shadow, all crossings negative (`switch_sign_self` pattern), `writhe = −w`;
   `P X.switchAll = ι (P X)` (`usw_P_switchAll`) by `coefficient_transport` on `Q := fun D => ι (P D.switchAll)`, which is an
   `RCompetitor`: `ι` is a ring hom (`iotaHom := AddMonoidAlgebra.lift ℤ R (ℤ×ℤ) (unitPowers aUnit⁻¹ (−zUnit))`, so
   `ι(a) = a⁻¹, ι(z) = −z`, sketch §7.4; typechecks), the switch-all transport `SwitchAllCarries` of `Reparam`, `Deform`, `RI`,
   `RII`, `RIII` (same shadow, over ↦ under; RII's "same over strand at both crossings" and RIII's "same strict height order"
   are preserved) and `IsSkeinTriple Dp Dm D0 → IsSkeinTriple Dm.switchAll Dp.switchAll D0.switchAll` (`Dm = Dp.switch x`
   ⇒ `Dm.switchAll = Dp.switchAll.switch x` with `x` positive there; the oriented smoothing is over-data-independent,
   `OutsideMatch.switch` LinkMoves.lean:1926 pattern), then "multiplied by −1" gives the skein of `ι ∘ P ∘ switchAll`
   (sm-3:4536-4548). `degAZ (ι f) = −mindegAZ f` for `f ≠ 0` (`ui_degAZ_iotaHom`: `coeffAt d k (ι f) = (−1)^k coeffAt (−d) k f`,
   `degAZ_spec` LinkLaurentRing.lean:455, `mindegAZ_spec` 513).
   FR-FL-C4: the accepted `Diagram.mirror` (LinkDiagram.lean:1379) is the REFLECTION `(x,y) ↦ (x,−y)` — a different diagram of
   the mirror knot with a different underlying curve; the printed proof needs "the same underlying plane curve — hence the same
   tangencies" (4431-4433), which only the switch gives. `mirrorCarries_linkEquiv` (LinkMoves.lean:1837) and
   `IsSkeinTriple.mirror` (2048) are the template for U-SW (~430 lines there) but cannot replace it. Fallback if U-SW stalls:
   `D̄' := X.reverse.mirror` (all negative, `P = ι(P X)` from (R) + the accepted mirror transport) whose curve is the
   reflected reversed polygon — rounding it keeps turning sense and downward tangencies, but every (B)/(A) transport must be
   redone on `C.reverse.mirror` (+~700 lines, worse fidelity). Not adopted.
3. Round (units (A),(B)): `W := Round C D̄ ε` for an admissible `ε` (`D̄ : PolygonDiagram C` via `ofDiagram`, shadow `rfl`);
   `ub_tangencyCount_of_admissible` gives the `R = rot(L)` `u`-tangencies (`R : ℕ` from `rotationNumber_integer` and
   `1 ≤ rot`), each inside a positive junction with `0 < deriv (θ j)`. (`rot(L_ε) = rot(L)`: `rot_roundedCurve` 2970.)
4. Curls (unit U-CURLS, `ucurl_exists_curled`): induction on the finite tangency set. Invariant after `k` curls: a
   `SmoothRegularLoop F_k`, a `Diagram X_k` with `RecordCarried F_k X_k` (Curl.lean:52), `F_k = L_ε` with velocity off the `k`
   chosen discs (`unchanged`, `unchanged_deriv`), `P X_k = P D̄`, `writhe X_k = −w − k`, all signs `−1`, the remaining `R − k`
   `u`-tangencies untouched. Each step: `CurlSite.ofCarried`-shaped site (Curl.lean:352; for `k ≥ 1` from the previous
   `carried'` directly, PLAN_FINAL §1 last line) with arc = the junction `[a j, b j]` (`junction_embedded`, `same_strands` ⇒
   no occurrence on it, `θ_lift`/`θ_strict` ⇒ `StrictMonoOn`, `direction_once` ⇒ `isolated`), disc `Δ ⊆ cornerDisc C ε j`
   (`exists_curl` with `Δ₀ := cornerDisc`, `disc_center`; discs pairwise disjoint `disc_disjoint`, `disc_no_double`), so the
   supports are disjoint and "leave one another intact"; `no_u` in `Δ`, `unchanged_deriv` outside ⇒ after `R` steps no
   `u`-tangency anywhere (tangencies of `L_ε` are exactly the `R` points, all inside their discs); `poly_eq`, `writhe_eq`,
   `kink_neg`, `old_sign`. Output: `T = (F_R, X_R)`, `P X_R = P D̄ = ι(P X)`, `writhe X_R = −w − R`, all negative.
   Est. 1000-1400 lines (the invariant bookkeeping, not analysis).
5. Rotate (unit U-ROT, `urot_exists_rotated`): `F' := rotationMap φ ∘ F_R` with `rotationMap φ u = (0, −1)`; `RecordCarried F' X_R`
   (same `τ`, `det` preserved by a rotation, cyclic order untouched), unit tangents rotated ⇒ no `(0,−1)`-tangency.
   FR-FL-C6: the polygon `X_R` is NOT rotated; this is legitimate because `RecordCarried` and the assumed `Carries` are
   record-level (no point coincidence clause). If the contact lane's final `Carries` adds `γ (τ v) = crossingPoint v` (as the
   accepted `Carried` has, Rounding.lean:183), then `Diagram.rotate` and `P (rotate X) = P X` (a `Deform` rotation path or a
   `RecordIso`) become necessary: +~600 lines. Flag to the contact lane NOW.
6. Transverse lift (unit U-LIFT, `ulift_exists_transverse_lift`, sm-3:4456-4523): `K.T := (x, y, z)` with `(x, z) = F'.γ`,
   `v = |F'′|`, `y₀ = −x′/(v + z′)` (smooth since `v + z′ > 0` — no downward vertical tangency — and `F'` regular), the identity
   `z′ − y₀ x′ = v > 0` (*); crossing constants `c_O < c_U` at each `(τ (overVisit x), τ (underVisit x))` by the printed case
   analysis on `det(t_O, t_U) < 0` (all crossings negative); vertical branches (`x′ = 0`, hence `z′ > 0`) impose no constraint, so
   the printed "at a crossing branch there is no vertical tangency" is NOT needed (the accepted curl witness does not export
   it); bumps `ψ_j` with disjoint cyclic supports on which `z′ − c_j x′ > 0` (Mathlib `ContDiffBump`, periodised by
   `round`; the printed `φ`-bump is one choice); `y := y₀ + Σ ψ_j (c_j − y₀)` smooth, 1-periodic, `z′ − y x′ > 0`; injectivity:
   equal points ⇒ equal projections ⇒ same parameter mod 1 or a double point pair where `y` differs; the `TransverseKnot`
   fields (TransverseFront.lean:571): `immersion`, `doubles_finite`, `transverse`, `no_triple` from `RecordCarried`
   (`doubles`, `transverse`, `no_triple` Curl.lean:52-116); `K.front.Carries X_R`: `over_eq` from `c_O < c_U` (`IsOver` 734),
   `sign_eq` from `RecordCarried.sign_eq` (`crossSign` 278 vs `SignType.sign`); `K.front.writhe = X_R.writhe` (front crossing
   pairs ↔ crossings via `τ`). Est. 1800-2500 lines.
7. Conclude (unit U-C): `hbound K X_R h`: `−w − R ≤ −degAZ (P X_R) − 1 = −degAZ (ι (P X)) − 1 = mindegAZ (P X) − 1`
   (`P_ne_zero` PolynomialBlock.lean:793), i.e. `1 − w − R ≤ mindegAZ (P X)`; cast to ℝ with `R = |rot|`. `floor_zZero`:
   `supp (zZeroPart f) ⊆ supp f` ⇒ `mindegAZ f ≤ mindegAZ (zZeroPart f)` (`mindegAZ_spec`).

## 4. thm:floor route (unit U-F, sketch §8.1)

`a_floor`: `C := carrierPolyComp hn hP S q hS` (LinkPositiveLift.lean:211: `⟨ccpCornerCount, ccpCornerCount_ge_three,
ccpCornerPolygon⟩`), `X := positiveLift hn hP S q hS` (596); `shadow := rfl` (`positiveLift_Γ` 607 = `Shadow.single
(carrierPolyComp …)` definitionally); `positive := positiveLift_isPositive` (618); `turn_ne := ccpCornerPolygon_turn_ne_zero`
(CarrierCornerPolygon.lean:579, lem:carriers (ii)); `alternative`: `turn = 1 ↔ 0 < principalTurn` by `principalTurn_sign`
(UniformRotation.lean:12) + `ccpCornerPolygon_regular` (679), and for the reversed alternative `principalTurn_reversal`;
`CarrierFloorCHyp.of_diagram` supplies the rest (the printed proof's own remark that lem:carriers gives every geometric
hypothesis "except that no corner lies on a non-incident edge, which holds directly" is `ccpCornerPolygon_tail_off`, already
inside `carrierShadow_generic` 580). Then `floor` gives `(1 − m_Q) − |rot Q| ≤ mindegAZ (homfly (positiveLift …))` with
`w = m_Q` (`positiveLift_writhe_eq_carrierCrossingCount` 820), `P = homfly` (`P_eq_homfly` 667), `rot Q = carrierRotation`
(UniformDefinition.lean:42, `rfl`), `= carrierRotationInt` (`carrierRotationInt_cast` CornerStateSum.lean:73), and
`cornerSlot_cast` (87) turns the real inequality into `cornerSlot ≤ mindegAZ` (`Int.cast_le`). `z_parity`: `P_knot_support`
(PolynomialBlock.lean:815) with `positiveLift_componentCount` (610) and `P_eq_homfly`; `0 ≤ mindegZZ` from `mindegZZ_spec`
(LinkLaurentRing.lean:614: a coefficient at `mindegZZ` is nonzero, so `mindegZZ = 2j ≥ 0`). ~250 lines, provable NOW
(`z_parity` unconditionally; `a_floor` from `CarrierFloorCData`).

## 5. Unit decomposition (byte-identical skeleton copies; statements frozen; leaves `sorry`; helper prefixes)

Skeleton = Sketch_A.lean §1-§8 with the leaf statements of §7/§8.1 frozen; every unit file is a byte-identical copy of the
skeleton plus proofs of its leaves and `<prefix>_`-prefixed helpers; an assembler merges (the curl-lane pattern,
work/drafts/curl/ASSEMBLY_REPORT.md).

| unit | leaves | prefix | lines | hours (prover wave) | status/blocker |
|---|---|---|---|---|---|
| U-R reversal | `ur_P_reverse_all` | `ur_` | 350 | 3-4 | provable now |
| U-A record | `junction_determined`, `length_determined` | `ua_` | 120 | 2 | provable now |
| U-B tangencies | `ub_tangencyCount_of_admissible`, `ub_exists_admissibleDirection` | `ub_` | 3000 (split: U-B1 lift concatenation + count 1800, U-B2 direction choice 500, U-B3 junction positivity/finiteness 700) | 16-24 | provable now |
| U-ι involution | `ui_degAZ_iotaHom` (+ `coeffAt_iotaHom`) | `ui_` | 250 | 2-3 | provable now |
| U-SW switch-all | `usw_P_switchAll` (+ `SwitchAllCarries` ×5, skein) | `usw_` | 700 | 6-8 | provable now; NEW transport on the moves layer (FR-FL-C4) |
| U-ROT rotation | `urot_exists_rotated` | `urot_` | 300 | 2-3 | provable now |
| U-CURLS iteration | `ucurl_exists_curled` | `ucurl_` | 1200 | 8-12 | provable now (consumes accepted `cf_lem_curl`) |
| U-LIFT transverse lift | `ulift_exists_transverse_lift` (split: U-L1 `y₀` and (*) 400, U-L2 crossing constants 300, U-L3 bumps/gluing 600, U-L4 embedding + `TransverseKnot` fields 500, U-L5 `Carries` + writhe 400) | `ul_` | 2200 | 14-20 | provable now (pure analysis) |
| U-C assembly of (C) | `cf_thm_carrierfloor_C_of_bound` | `uc_` | 600 | 4-6 | needs U-R..U-LIFT; row assembled once row 94 lands (`TransverseFrontBound` discharged by the contact lane) |
| U-F thm:floor | `uf_a_floor_of_C`, `uf_z_parity` | `uf_` | 250 | 2-3 | `z_parity` now; `a_floor` from (C) |
| total | 13 leaves | | ≈ 9000 | ≈ 60-85 prover-hours, 2-3 waves | |

Wave plan: wave 1 = U-R, U-A, U-ι, U-ROT, U-F(z), U-B2/U-B3, U-L1/U-L2 (independent, small); wave 2 = U-B1, U-SW,
U-L3/U-L4/U-L5, U-CURLS; wave 3 = U-C assembly (+ U-F(a)). (R), (A), (B) can be mapped `implemented` as clause theorems
after their own review before (C) exists; the row theorem stays unmapped until row 94 (D-F11/D-F14 pattern).

## 6. Riskiest analytic steps and how to bound them

1. U-LIFT gluing (`y` smooth and periodic with `z′ − y x′ > 0`): bound by proving the pointwise identity first
   (`z′ − y x′ = (1 − ψ_j)(z′ − y₀x′) + ψ_j (z′ − c_j x′)` on each support, `= v` elsewhere), choosing window radii by a
   compactness/continuity lemma (`z′ − c_j x′ > 0` near `s_j`, finitely many `j`, radii `< 1/2` and pairwise disjoint mod 1),
   and using Mathlib `ContDiffBump` (`ContDiffBump.contDiff`, `one_of_mem_closedBall`, `zero_of_le_dist`) periodised by
   `round` (locally constant off half-integers where the bump vanishes). Probe false-statement risk: the window disjointness
   must be stated mod 1 (cyclic), as the sketch's docstring says.
2. U-LIFT embeddedness: only the double-point pairs can collide in projection (`RecordCarried.doubles`), and there `y` takes the
   distinct values `c_O ≠ c_U` (bump equal to 1 at the two parameters); state and prove this as its own leaf before the
   `TransverseKnot` packaging.
3. U-B1 count identity: the concatenated lift is a `C⁰` (indeed `C^∞`) lift on `[0,1]` with the seam in a straight part;
   the count of solutions of `θ(t) ≡ φ (mod 2π)` on `[0,1)` equals `⌊(θ(1) − φ)/2π⌋ − ⌊(θ(0) − φ)/2π⌋` only when `θ` is
   piecewise monotone with the levels avoided at all non-increasing points — the decreasing junction is handled by the arc
   clause of `AdmissibleDirection` (its whole swept arc misses `±u`). State the pure-real lemma ("monotone-on-pieces level
   counting") separately and probe it on a two-junction example before the geometric wrapper.
4. U-CURLS invariant: the site of the `(k+1)`-st curl must be re-established on `F_k` (velocity unchanged on the junction:
   `unchanged_deriv` with the window inside the OTHER disc, `disc_meets_arc`/`disc_only_modification` to keep the arcs apart).
   Freeze the invariant as a `structure CurlState k` in the skeleton (fields listed in §3 step 4) so provers cannot drift.
5. U-SW: the accepted `RIIIData` (LinkMoves.lean:639) names its arcs by height (`a` top, `b` middle, `c` bottom, fields
   `top_ab`, `top_ac`, `mid_bc` and primed); a switch-all reverses the height order, so `RIIIData.switchAll` is the relabelling
   `a ↔ c`, `xab ↔ xbc` (the `Separates`/`ArcCover`/end fields are over-data-free). Checked against the field list; the leaf
   can be frozen as stated. Fallback recorded in §3 step 2.
6. Dependence on the contact lane: `Carries` must stay record-level (FR-FL-C6) and the bound must be stated with `P` (or
   `homfly`, interchangeable by `P_eq_homfly`) of ANY carrying diagram; both are the memo's form — confirm with that lane.

## 7. Fidelity risks (consolidated)

FR-FL-R1 knot-vs-link scope of `P_reverse`; FR-FL-R2 "the same polynomial" = `P` of `LinkEquiv`-equivalent diagrams (D2);
FR-FL-R3 smooth-diagram reversal rendered at curve level only; FR-FL-A1 junction template stated parametrically (stronger than
image equality, true of the construction); FR-FL-A2 "one record" = `Round` is a function, no uniqueness among smoothings
claimed; FR-FL-B1 (B) asserted for the normalised orientation (the literal reversed reading is false in the sense clause);
FR-FL-B2 "points" = parameters mod 1, finiteness explicit; FR-FL-B3 "crosses positively" = positive derivative of the junction
lift; FR-FL-B4 `ε₁ ≤ clearance` added, admissibility proof quantified; FR-FL-B5 "nonzero edges"/"finitely many double points"
inside `Regular`/`Generic`; FR-FL-C1 redundant printed hypotheses kept (`turn_exists`, `turn_lt_pi`, `generic`); FR-FL-C2 `R`
real, `mindegAZ` on the nonzero `P X`; FR-FL-C3 `f_D` as the `z⁰` row inside `R`; FR-FL-C4 the printed mirror is the crossing
switch, the accepted `Diagram.mirror` is a reflection — new `switchAll` transport (proof route only, statement unaffected);
FR-FL-C5 the "(R) changes nothing" parenthesis is a proof remark; FR-FL-C6 the coordinate rotation is applied to the smooth
curve only, relying on record-level carrying (contact-lane dependency); FR-FL-C7 the transverse lift uses a Mathlib bump in
place of the printed `φ`-bump and drops the unneeded "no vertical tangency at a crossing branch" (both proof devices);
FR-FL-F1 literal reversal form for thm:floor's alternative; FR-FL-F2 "turns" are all corner turns of the corner polygon;
FR-FL-F3 `z_parity` without turn hypothesis.

## 8. FINAL_REVIEW sentences (proposed)

"Row 99 cf:thm-carrierfloor: stated as `SM.CarrierFloorData` (clauses `CarrierFloorRData/AData/BData/CData`,
work/drafts/floor/Sketch_A.lean) on the accepted rounding record `SM.Round := CornerRounding.roundedWitness`; (R), (A), (B)
provable now under the frozen interfaces; (C) proved conditionally as `cf_thm_carrierfloor_C_of_bound` from the row-94 writhe
bound `TransverseFrontBound` (contact lane), via cf:lem-curl, the crossing-switch identity `P_{D̄} = ι(P_D)` and the transverse
lift; readings FR-FL-*." "Row 100 thm:floor: stated as `SM.FloorTheoremData`; `z_parity` provable now (lp:core knot support);
`a_floor` from clause (C) on the positive lift (`thm_floor_of_C`); assembled once row 94 lands."
