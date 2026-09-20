# PREREVIEW — rows 99 cf:thm-carrierfloor and 100 thm:floor (Statements_FINAL.lean, frozen 2026-09-15)

Independent auditor, 2026-09-15.  Object: `work/drafts/floor/Statements_FINAL.lean` (730 lines; `lake env lean` from
`work/lean`: 0 errors, 23 `sorry` warnings = the 23 leaves).  Printed source: `reference/SM/sm-3-statesum.tex` 4282-4339
(row 99 statement), 4340-4575 (proof), 4576-4602 (row 100).  This is a PRE-review (non-vacuity, fidelity red flags,
triviality, truth probes), not the formal fidelity review.  Nothing under `work/lean` was touched.  Probe scripts:
`/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/{probes.py,iota_probe.lean}`
(the Lean probe is reproduced in §4.2 below).

## 0. Verdict in one paragraph

The row statements ((R), (A), (B), (C) and thm:floor) are jointly satisfiable and non-trivial: a concrete positive knot
diagram (a 61-gon inscribed in the locally convex curve r = 1 + 0.25 cos(3θ/2), rot 2, 3 positive crossings) satisfies every
hypothesis field of `CarrierFloorCHyp`, and the pentagram (cinquefoil, 5 crossings, rot 2) does as well; on both the printed
bound is met with equality by direct HOMFLY computation in the campaign convention.  The (B) count and the positive crossing
sense were confirmed numerically on the actual construction (`Real.smoothTransition` profile) and the sense flips for the
reversed orientation exactly as FR-FL-B1 says.  No printed clause of (R)(A)(B)(C)/thm:floor is without a field, and every
extra field is one of the recorded FR-FL-* risks.  ONE frozen proof-route leaf is FALSE as stated and must be amended before
its unit starts: `MirrorSubstitutionData.coeff` uses `(-1) ^ k.toNat`, which is `1` for every negative `k`; Lean-verified
counterexample `f = z⁻¹, d = 0, k = −1` (§4.2).  It does not touch the row statements (the `(C)` assembly consumes only
`degAZ_eq`/`ne_zero`), so it is blocking for unit U-ι, not for the statement review.  FR-FL-B1 / C4 / C8 are argued in §2.3;
my expectation is non-blocking for all three, with B1 the one a strict reviewer is most likely to press.

## 1. Non-vacuity

### 1.1 The concrete diagram (probe `probes.py`, section (i))

* `C`: the 61-gon with vertices `(r cos θ_k, r sin θ_k)`, `θ_k = 4πk/61`, `r = 1 + 0.25 cos(1.5 θ_k)` (the curve is locally
  convex since `1 − 3.25·0.25 > 0`).  Checked numerically: `Regular` (all edges nonzero, no antiparallel consecutive pair);
  all 61 principal turns positive, `max |ϑ| = 0.095π < π`; `rot = 2.000000`; exactly 3 double points, all transverse and in
  edge interiors (no corner at a double point); no corner on a non-incident edge; no triple point.  So `X.generic`,
  `turn_exists`, `turn_ne`, `turn_lt_pi`, `generic` and `alternative` (first branch of `UniformOrOneDissent`) all hold.
  `positive`: at each double point exactly one of the two over choices gives `det(u_o,u_u) > 0`, so a `PolygonDiagram C`
  with every crossing positive exists (`X := D.toDiagram`, `shadow := rfl`).  `w = 3`, `R = 2`.
* Pentagram `{5/2}` (5 vertices on the unit circle at angles `144°·k`): all turns `0.8π`, `rot = 2`, 5 transverse crossings,
  no corner incidence, no triple point.  `w = 5`, `R = 2`.
* One-dissent instance: the 61-gon with vertex 10 pushed inside the chord of its neighbours (35 %): exactly one negative
  turn (`−0.0193`), all others positive, still `rot = 2`, 3 transverse crossings, no corner incidence.  So the second
  alternative of `AllPosOrOneNeg` is populated too.
* Conclusion plausibility (probe section (vi), skein `a P₊ − a⁻¹ P₋ = z P₀`, `P(○) = 1`, hence `P(unlink₂) = (a − a⁻¹)/z`):
  `P(3₁⁺) = 2a⁻² − a⁻⁴ + a⁻²z²`, `mindeg_a = −4 = 1 − 3 − 2` (equality); `f_D = 2a⁻² − a⁻⁴`, `mindeg_a = −4` (equality);
  `P(T(2,5)) : mindeg_a = −6 = 1 − 5 − 2` (equality).  z-exponents all even (`InSupportM 1`), `mindeg_z = 0 ≥ 0`.  The
  mirror identity `P(D̄) = ι(P D)` checked on the trefoil: `P(3₁⁻) = 2a² − a⁴ + a²z² = P(3₁⁺)(a⁻¹, −z)`, and
  `max deg_a P(D̄) = 4 = −mindeg_a P(D)`.

### 1.2 Field-by-field satisfiability

| object | verdict | reason |
|---|---|---|
| `CarrierFloorCHyp C X` | satisfiable | §1.1; the three redundant fields follow from `shadow`+`X.generic` (`of_diagram`, compiled) |
| `CornerRounding.Admissible C D ε` / `Round` | satisfiable | `clearance_pos D.generic` (Rounding.lean:2025), `turn_ne` as above |
| `BClaim C D` | satisfiable, non-vacuous | `∃ u ε₁`: `ε₁ := clearance C > 0`, `ε₁ ≤ clearance` by `le_rfl`; the inner `∀ h : Admissible` is inhabited for every `ε ∈ (0, ε₁)`, so the claim is not vacuous; `TangencyCount` at `u` and `−u` both with positive sense — confirmed on the actual construction (§4.3) |
| `tangencySet` / `CrossesPositively` / `TangencyCount` | consistent | `Finite ∧ ncard = R ∧ ∀ t, CrossesPositively` — each tangency found lies in an open junction of positive turn with `deriv θ_j > 0` (§4.3); `ncard` of an infinite set would be `0`, guarded by the explicit `Finite` conjunct (FR-FL-B2) |
| `CarrierFloorBData.tangencies` | consistent | hypothesis `UniformOrOneDissent C` populated in both branches (§1.1); conclusion's two branches each carry their normalisation witness |
| `TransverseFrontBound` | satisfiable (TRUE if row 94 is) and NOT refuted | it is the sl-free Bennequin/Franks–Williams–Morton bound `sl ≤ mindeg_v P − 1` with `v = a⁻¹` and `sl = w(front)` (Etnyre convention, smaller-`y` over, `z′ − y x′ > 0`); the `TransverseKnot` class is non-empty: the figure-eight front `x = sin 2πt, z = −½ sin 4πt` with `y = y₀ + ψ₀(c_O − y₀) + ψ_{1/2}(c_U − y₀)`, `c_O = −2 < c_U = 2`, has no downward vertical tangency, `z′ − y x′ ≥ 4.16 > 0`, one negative crossing, embedded (§4.4) — a transverse unknot with `w = −1 ≤ −0 − 1`: the bound is sharp there, not violated.  A crossing-free front is impossible (a simple closed curve has a downward vertical tangency), consistent with `sl(unknot) ≤ −1` |
| `FdContactShape sl` → `TransverseFrontBound` | PROVED in the file | `transverseFrontBound_of_fdContactShape` |
| `liftY0`, `LiftAdmissible` | consistent | `v + z′ > 0` off downward tangencies; `z′ − y₀ x′ = v` verified numerically to machine precision |
| `circBump δ s₀` | as documented | `= 1` at `s₀`, `= 0` at circle distance `≥ δ`, values in `[0,1]`, 1-periodic, `C^∞` for `δ ∉ ℤ` (`1 − cos 2πδ ≠ 0`); verified numerically |
| `liftY`, `liftT` | consistent | proof devices (no leaf mentions them); the lift on the figure-eight is positively transverse and injective (§4.4) |
| `ul_exists_constants` hypotheses | satisfiable | random sampling over all five sign patterns (§4.5) |
| `ucurl_exists_curled` hypotheses | satisfiable | `TangencyCount` at `u` for the all-negative `D̄` (the record's curve does not depend on the over data: `roundedLoop h` is `curveMap C ε`); `hneg` by `switchAll` |
| `CarrierUniformOrOneDissent` (row 100) | satisfiable | any all-left corner polygon (e.g. convex decompositions); equivalent to the memo's 4-way form since carrier turns are nonzero (lem:carriers (ii)) |

No provably contradictory field combination was found.  In particular the two `TangencyCount` conjuncts of `BClaim` (at `u`
and at `−u`, both positive sense) are simultaneously true on the construction (§4.3), and the reversed-orientation branch of
`tangencies` is about `Round C.reverse D.reverse`, whose junction lifts are increasing exactly where the original's were
decreasing.

## 2. Fidelity red flags

### 2.1 Printed clauses → fields (completeness)

(R): scoping sentence → `rot_reverse_polygon` (lem:rot `rotationNumber`) + `rot_reverse_curve` (cf:def-turning `ClosedC1Curve.rot`);
"P_{−D} = P_D" → `P_reverse` (knot case, FR-FL-R1); "consequently … same polynomial" → `knot_reverse` (FR-FL-R2); "same crossing
signs" → `sign_reverse`; "same writhe" → `writhe_reverse`; "rotation … negative" → the two `rot_reverse_*` fields.  Complete.

(A): "returns one curve and one diagram at those data" → `one_record`, `one_curve`, `one_diagram`; "junction … determined by ε,
the two incident unit directions and the transition profile, fixed once and for all" → `junction_determined` (template =
`juncArc` with the fixed `Real.smoothTransition`, FR-FL-A1); "arc length ℓ determined by the endpoint condition" →
`length_determined`; "the rest of the curve is L itself" → `rest_is_L`; "Write Round(L,D,ε) = (L_ε, D_ε)" → `def Round`.
"For every ε ∈ (0, ε₀(L))" and "hypotheses of Lemma cf:lem-rounding" → `Admissible C D ε` (+ `D.generic`).  Complete.

(B): hypothesis list → `C : PolyComp`, `D : PolygonDiagram C`, `∀ i, principalTurn ≠ 0` (FR-FL-B5); "after reversing orientation
if necessary, either … or …" → `UniformOrOneDissent C`; "R = |rot(L)|" → `|rotationNumber C.P|`; "u ∈ S¹" → `euclideanLength u = 1`;
"ε₁ > 0, for every ε ∈ (0, ε₁)" → `0 < ε₁ ∧ … ∀ ε, 0 < ε → ε < ε₁`; "the rounded curve L_ε of the record Round(L,D,ε)" →
`Round C D ε h`; "exactly R points at which its unit tangent equals u and exactly R at which it equals −u" → the two
`TangencyCount`s; "at each of them the tangent crosses that direction in the positive sense" → `CrossesPositively` (FR-FL-B3).
Complete (modulo FR-FL-B1, §2.3).

(C): every hypothesis clause has a field (`shadow`, `positive`, `X.writhe`, `turn_exists`, `turn_ne`, `turn_lt_pi`, `generic`,
`|rotationNumber|`, `alternative`); the two commentary sentences ("The finiteness/transversality … are what Lemma cf:lem-rounding
asks …", "stated here so that no generic parent polygon is assumed") and the parenthesis "which by clause (R) changes neither …"
are remarks (FR-FL-C1, C5); cf:eq-floor → `floor`; "the same bound holds for f_D whenever f_D ≠ 0" → `floor_zZero` (FR-FL-C3).
Complete.

thm:floor: "subpolygon of a decomposition of a generic polygon" → `(hn, P, hP, S, hS, q)`; "after possibly reversing its
orientation either all turns are left, or exactly one turn is right" → `CarrierUniformOrOneDissent` (FR-FL-F1, F2);
"mindeg_a H⁺_Q ≥ 1 − m_Q − |r_Q| = d_Q" → `a_floor` (ℤ form with `cornerSlot` and the printed real form); "H⁺_Q ∈ ℤ[a^{±1}, z²],
so mindeg_z ≥ 0" → `z_parity` (FR-FL-F3).  Complete.

### 2.2 Fields / conjuncts with no printed counterpart

All are recorded risks or harmless consequences: `TangencyCount.Finite` (B2); `ε₁ ≤ clearance C` (B4 — strengthens the
existential, provable with `ε₁ = ε₀(L)` as the proof does); the normalisation-witness conjuncts `AllPosOrOneNeg C.P` /
`AllPosOrOneNeg (reversal C.P)` in `tangencies` (part of the B1 rendering; each is implied by the hypothesis in its branch);
`rot_reverse_polygon`'s first conjunct `X.reverse.Γ = Shadow.single C.reverse` (R3, definitional); `one_diagram`'s writhe
conjunct ("the diagram data are inherited", proof text); `knot_reverse` (R2); the redundant (C) hypotheses (C1).  The
corollaries `junction_local` and `floor_support` are theorems, not fields.  Nothing unrecorded.

Two small documentation inaccuracies (cosmetic): the header says "the only `sorry`s are the proof-route leaves of §8", but
`CarrierFloorAData.junction_local` (§3, l.189) and `CarrierFloorCData.floor_support` (§5, l.328) also carry `sorry`; and the
Statements file's docstring for `MirrorSubstitutionData.coeff` writes `(−1)^k` while the Lean says `k.toNat` (see §3/§4.2).

### 2.3 The three named risks, both sides

**FR-FL-B1 (clause (B) asserted for the normalised orientation).**
*For blocking:* grammatically "after reversing orientation if necessary" qualifies the hypothesis ("Assume …"), while the
conclusion names `Round(L, D, ε)`, the record at the GIVEN `L`.  In the reversed alternative the Lean row says nothing about
`Round C D ε h` itself, only about `Round C.reverse D.reverse ε h'`; the count half of the literal claim ("exactly R points with
tangent u and R with −u") is TRUE for the given orientation too (the tangency sets are orientation-independent as sets; my
probe finds 2 and 2 in both orientations, §4.3), so the row drops a true literal sub-claim, and
`Round(−L, −D, ε) = reverse(Round(L, D, ε))` is not proved, so the dropped part cannot be recovered from the asserted one.
*Against blocking:* the sense clause of the literal reading is FALSE for an all-right-turning `L` (probe: senses `−1, −1`
after reversal), so a literal formalisation would be unprovable; the printed proof itself performs the normalisation once
(4368-4370) and never returns to the un-normalised record; the only consumer, (C), normalises first by (R) and reads (B) on
the normalised polygon (4417-4430, "Fix ε … pass to the rounding record … By clause (B) there is a direction u …"), so the
row as stated is exactly what is consumed; the deviation is disclosed (B1) and the reviewers' standard on this project has
accepted disclosed readings forced by the proof (FINAL_REVIEW table, e.g. rows 93, 153).  *Expectation:* non-blocking.
*Cheap hardening if pressed:* add an orientation-free count field for `Round C D ε h` itself — the level-count argument with
`|rot|` levels met in the decreasing junctions is symmetric (`liftAt_strictAntiOn`) — or a field `crosses in the sense
sgn(rot L)`.  Either is a true strengthening; neither is needed by (C).

**FR-FL-C4 (the printed `D̄` is the crossing switch, not `Diagram.mirror`).**
*For blocking:* the accepted library has `Diagram.mirror` (reflection) and `MirrorCarries`; the route introduces
`Diagram.switchAll` and a NEW transport `SwitchAllCarriesUnit` (planar/RI/RII/RIII/circle/skein) — the largest un-vetted
proof obligation in the plan, whose truth depends on the accepted move data (`Reparam`, `RIData`, `RIIData.same_over`,
`RIIIData`, `MoveMatch`) being natural under exchanging over/under everywhere.  *Against blocking:* the row STATEMENT never
mentions `D̄`; (C) is stated on `P_D`, `w`, `R` only, so C4 cannot affect statement fidelity; the printed proof literally
says "Switch every crossing. The result is a diagram D̄ … with the same underlying plane curve — hence the same tangencies"
(4431-4433) — the reflection would move the curve, reflect `u`, and reverse the crossing sense of every tangency, breaking
the hand-off to cf:lem-curl, so the switch is the faithful and the simpler route; `IsSkeinTriple Dp Dm D0 →
IsSkeinTriple Dm.switchAll Dp.switchAll D0.switchAll` is checked by hand (`Dm = Dp.switch x` ⇒ `Dp.switchAll =
Dm.switchAll.switch x`, `x` positive in `Dm.switchAll`); the mirror identity `P(D̄) = P_D(a⁻¹, −z)` is true (§1.1 check).
*Expectation:* non-blocking for the statement review; a proof-effort risk only.

**FR-FL-C8 (record-level reading `K.Reads X` = `HeightMarking`).**
*For blocking:* `TransverseFrontBound` hard-codes the contact lane's `Reads := Nonempty (K.spatial.HeightMarking
K.spatial.projLoop X)` copied from a DRAFT (`work/drafts/contact/Sketch_A.lean` §4, not yet accepted); if row 94 is accepted
with a different reading relation (or with point coincidence), `cf_thm_carrierfloor_of_bound`'s hypothesis is not literally
what row 94 provides and the `_of_bound` theorems cannot be discharged by it; the printed proof says the front "and its
smaller-y over/under assignments are exactly the diagram T" (4521-4522), which one may read as coincidence of the smooth front
with the polygonal `T`.  *Against blocking:* the front is smooth and `P` is defined on polygonal diagrams, so the only meaning
"P_T" can have is `P X` for a polygonal `X` reading the front's record (rp:record-polynomial), and rows 90/91 fixed that
reading as `HeightMarking` (occurrence bijection, cyclic order, twin pairing, over = smaller height, signs) — the two contact
designs and both contact sketches use exactly this; `transverseFrontBound_of_fdContactShape` is PROVED, so if row 94 lands in
the `FdContactShape` form the composite follows, and if it lands in another form the composite is a two-line re-derivation
(the (C) assembly consumes only `TransverseFrontBound`); the hypothesis quantifies over the whole Lean `TransverseKnot` class,
every member of which is "finite regular generic" by its fields, matching the printed domain of fd:representative-bound; the
conditional-theorem pattern (D-F11/D-F14) is the accepted way to state a row on an un-landed input.  *Expectation:*
non-blocking; a coordination item with the contact lane, to be re-checked when row 94 is accepted.

## 3. Triviality

* No hypothesis class is empty (§1).  `CarrierFloorCHyp` is inhabited by the 61-gon, the pentagram, and the one-dissent
  variant; `Admissible` by `clearance_pos`; `UniformOrOneDissent` in both branches.
* `TransverseFrontBound` is not refutable by any instance found (the figure-eight transverse unknot meets it with equality),
  so the conditional theorems are not vacuously provable through a false hypothesis.
* (A) is largely definitional in Lean (`one_record`, `one_curve` are `rfl`; `one_diagram`, `rest_is_L` are record fields);
  this mirrors the printed clause, which is a determinacy statement about the named construction (FR-FL-A2; the printed
  proof says explicitly "This asserts uniqueness of the fixed construction's record, not uniqueness among all possible
  smoothings", 4362-4364).  The non-definitional content is `junction_determined` and `length_determined`.  Not a triviality
  defect.
* `ub_levelCount`'s hypothesis `0 < rotationNumber C.P` is superfluous (the conclusion forces `rot ≥ 0` anyway) but harmless.
* The FALSE leaf of §4.2 does not make anything trivially true; it makes one unit unprovable.

## 4. Truth probes of the 23 leaves

### 4.1 Table (line = `sorry` warning line in Statements_FINAL.lean)

| # | leaf | line | verdict | one-line reason |
|---|---|---|---|---|
| 1 | `CarrierFloorAData.junction_local` | 189 | TRUE | both junction images are `junctionTemplate q u v ε '' [0,1]` by `junction_determined` (the affine reparametrisation of `[a j, b j]` onto `[0,1]` is onto, `a j < b j`) |
| 2 | `CarrierFloorCData.floor_support` | 328 | TRUE | `mindegAZ_spec (P_ne_zero X)`: every present `a^d z^k` has `mindegAZ ≤ d`; compose with `floor` |
| 3 | `ur_P_reverse_all` | 395 | TRUE | `D ↦ P D.reverse` is an `RCompetitor`: `reverseCarries_planarIsotopic/RI/RII/RIII` (LinkMoves.lean 2459, 3071, 3117, 3231), `IsSkeinTriple.reverse` (3318), reversed crossing-free circle is one; `coefficient_transport` |
| 4 | `ua_junction_determined` | 415 | TRUE | `curveMap_on_junction` (Rounding.lean:1668) gives `juncArc (A0 j) ε (θu j) (turn j) ((t−a j)Λ/ℓ j)`; at `t = a j + s(b j − a j)` the argument is `s` (`b_sub_a`); `θu j ≡ arg(uDir j) mod 2π` (`G1_θu_coe_angle`) and `juncArc` is 2π-periodic in that slot; `principalAngle (uDir j) (vDir j) = principalTurn j` by scale invariance of `arg`; `A0 j = C.P j − ε • uDir j` by definition |
| 5 | `ua_length_determined` | 422 | TRUE | `speed = Λ`, `b j − a j = ℓ j / Λ`, `ℓ j = juncLen ε (turn j)`; `curveMap_b : curveMap (b j) = A1 j = C.P j + ε • vDir j` |
| 6 | `ub_globalLift` | 456 | TRUE | `normalize_deriv_curveMap` (1785) + `Θ_on_junction` (1469); `Round C D ε h` is `roundedWitness h` definitionally with `θ := liftAt` |
| 7 | `ub_exists_direction` | 466 | TRUE | `θu (j+k) = θu j + 2π rot` so the forbidden classes mod π are the k values `θu j` plus, for the single negative turn, a closed arc of length `\|ϑ₋\| < π`; the complement in `ℝ/πℤ` is non-empty |
| 8 | `ub_levelCount` | 479 | TRUE | levels `φ + 2πn` are met only inside increasing junctions (straight parts and junction ends sit at `θu j ≢ φ mod π`; the decreasing junction's closed arc contains none), once each (`liftAt_strictMonoOn`), with `deriv (liftAt j) > 0` there; per-junction count = floor difference (probe §4.3: 0 violations in 20 000 random junctions), telescoping to `⌊x + rot⌋ − ⌊x⌋ = rot` (`θu_last`, integer `rot`); finiteness from finitely many junctions each contributing finitely many levels |
| 9 | `ub_tangencyCount_of_admissible` | 491 | TRUE | `AdmissibleDirection` gives `hφ`/`harc` for `φ := arg u` via `dirOf_θu` and `G1_θu_coe_angle`; `rot ≥ 1` from `uniform_rotation` through `principalTurn_sign`; `-u = dirOf (φ + π)` |
| 10 | `ub_exists_admissibleDirection` | 500 | TRUE | `u := dirOf φ` from leaf 7; `normalize (edge (j−1)) = uDir j = dirOf (θu j)` |
| 11 | `usw_switchAll_sign` | 534 | TRUE | `det` antisymmetry, `SignType.sign_neg` |
| 12 | `usw_switchAll_writhe` | 537 | TRUE | sum of leaf 11 |
| 13 | `usw_carried_switchAll` | 540 | TRUE | `Carried` fields other than `sign_eq` are over-data free; `sign_eq` transforms by `det` swap and leaf 11 |
| 14 | `usw_switchAllCarries` | 557 | TRUE (plausible) — DOUBTFUL only in the definitional details | `skein` checked by hand (`Dm = Dp.switch x ⇒ Dp.switchAll = Dm.switchAll.switch x`, `x` positive in `Dm.switchAll`, oriented smoothing over-data free); `circle` trivial; `planar/ri/rii/riii` need the accepted `Reparam`/`Deform`/`RIData`/`RIIData.same_over`/`RIIIData`/`MoveMatch` to be natural under a global over/under exchange — expected (RII keeps "same over arc", RIII is a relabelling `(a,b,c) ↦ (c,b,a)`), not verified line by line here |
| 15 | `ui_mirrorSubstitution` | 576 | **FALSE as frozen** | field `coeff` says `coeffAt d k (ι f) = (-1) ^ k.toNat * coeffAt (-d) k f`; `Int.toNat k = 0` for `k < 0`, so the sign factor is `1` for every negative `k`; Lean-verified counterexample §4.2: `ι z⁻¹ = −z⁻¹`, `coeffAt 0 (−1) (ι z⁻¹) = −1 ≠ 1`.  The other five fields are TRUE (`ι_a`, `ι_aInv`, `ι_z` by `lift_single`; `degAZ_eq`, `ne_zero` since `ι` permutes monomials `a^d z^k ↦ ±a^{−d} z^k`).  Fix: `(-1) ^ k.natAbs` (or `Int.negOnePow k`, or drop the field — the (C) assembly uses only `degAZ_eq`/`ne_zero`) |
| 16 | `usw_P_switchAll` | 582 | TRUE | `Q := ι ∘ P ∘ switchAll` is an `RCompetitor` (leaf 14 + `P_skein` under `ι`: `a⁻¹ ι P(Dm̄) − a ι P(Dp̄) = −z ι P(D0̄)` rearranges to the campaign skein), so `Q = P`; `ι ∘ ι = id`.  Numerically confirmed on the trefoil (§1.1) |
| 17 | `urot_exists_rotated` | 599 | TRUE | `φ := −π/2 − arg u`; `rotPlane φ` is a linear isometry commuting with `deriv` and `normalize`, preserving `det`, so every `RecordCarried` field transports; `G` smooth/periodic/regular |
| 18 | `ucurl_exists_curled` | 612 | TRUE (plausible) — DOUBTFUL only in two technical sub-steps | induction on the `R` tangencies with `cf_lem_curl.exists_curl` at `Δ₀ := cornerDisc C ε j`; each site: `[α,β] := [a j, b j]` (`b j − a j < 1`, `junction_embedded`, `direction_once`, `θ_lift`, `θ_strict` with `turn j > 0` forced by `deriv θ_j t₀ > 0`, `same_strands` puts all visits in open straight parts); after a curl the curve and its derivative are unchanged off the window, the kink visits stay in `Δ ⊆ cornerDisc j`, disjoint from every other junction's disc.  Sub-steps not exported by the accepted records: (a) `S.p ∈ interior Δ₀` needs the junction interior to lie in the OPEN corner disc (true: the arc is convex, inside triangle `A0 q A1`, whose only boundary-circle points are `A0`, `A1`), `RoundingWitness` exports only closed-disc membership; (b) the parameters of the old visits are unchanged after a curl (true: `old_point` + `F' = F` off the window + the crossing point is outside `Δ`) |
| 19 | `ul_exists_constants` | 654 | TRUE | the admissible sets are half-lines `(−∞, m)` for `x′ > 0`, `(m, ∞)` for `x′ < 0`, all of `ℝ` for `x′ = 0` (`z′ > 0`); `c_O < c_U` fails only when `x′_O < 0 < x′_U` and `m_O ≥ m_U`, excluded by `det = x′_O x′_U (m_U − m_O) < 0`.  Probe §4.5: 0 failures in 5 sign classes (≈100 000 samples); with `det > 0` and `x′_O < 0 < x′_U` it fails in 25 064/25 064 samples, so `hdet` is exactly the needed hypothesis |
| 20 | `ulift_exists_transverse_lift` | 664 | TRUE | `y := y₀ + Σ ψ_v (c_v − y₀)`; positivity on each bump support by convexity `(1−ψ)(z′ − y₀x′) + ψ(z′ − c x′) > 0`; embedded since the only projection coincidences are visit pairs with `c_O < c_U`; `K.Reads X`: `HeightMarking` fields from `RecordCarried` (`Φ` via `τ`, `pair_eq` from `doubles`, `between_iff` from `order`, `over_iff` by `c_O < c_U`, `sgn_eq` from `sign_eq`); `front.writhe = X.writhe` since each double point enters once over-first.  Numerically realised on the figure-eight (§4.4) |
| 21 | `cf_thm_carrierfloor_C_of_bound` | 678 | TRUE (conditional on leaf 15's fix) | normalise by (R); `D̄ := switchAll`; (B) at `ε := ε₁/2`; leaf 18 with `R := rot`; leaf 17; leaf 20; `hbound`; `−w − R ≤ −degAZ(ι(P X)) − 1 = mindegAZ (P X) − 1` by leaf 16 and `degAZ_eq`; `floor_zZero` by `supp (zZeroPart f) ⊆ supp f`.  Note the record's curve `roundedLoop h` does not depend on `D`, so (B)'s count for `Round C D` transfers to `Round C D̄` by `rfl` |
| 22 | `uf_a_floor_of_C` | 703 | TRUE | `positiveLift_Γ` is `Shadow.single (carrierPolyComp …)` by `rfl`; `positiveLift_isPositive`; `ccpCornerPolygon_turn_ne_zero` (`IsDecomposition` is membership in `independentSupports`, DecompositionDefinition.lean:15) + `principalTurn_sign`; `AllLeftOrOneRight → AllPosOrOneNeg` and the reversal branch via `principalTurn_reversal`; `positiveLift_writhe_eq_carrierCrossingCount`, `P_eq_homfly`, `cornerSlot_cast` |
| 23 | `uf_z_parity` | 713 | TRUE | `P_support` with `positiveLift_componentCount = 1`, `P_eq_homfly`; `mindegZZ_spec (P_ne_zero _)` gives a supported `z`-exponent `= 2j ≥ 0` |

Totals: 22 TRUE (2 of them flagged plausible/doubtful in definitional or technical detail: leaves 14 and 18), 1 FALSE (leaf 15).

### 4.2 The Lean counterexample to leaf 15 (compiled, 0 errors, against `import SM.LinkLaurentRing`)

```lean
import SM.LinkLaurentRing
namespace SM
open Link AddMonoidAlgebra Classical
noncomputable section
def iotaHom : R →+* R :=
  (AddMonoidAlgebra.lift ℤ R (ℤ × ℤ) (unitPowers (R.aUnit⁻¹) (-R.zUnit))).toRingHom
example : ((-1 : ℤ) ^ ((-1 : ℤ).toNat)) = 1 := by decide
theorem iotaHom_zInv : iotaHom R.zInv = -R.zInv := by
  unfold iotaHom R.zInv
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AddMonoidAlgebra.lift_single]
  simp only [one_smul, unitPowers, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, zpow_zero, one_mul]
  have h : ((-R.zUnit) ^ (-1 : ℤ) : Rˣ) = -(R.zUnit⁻¹) := by
    rw [zpow_neg_one]; exact inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
  rw [h]; simp; rfl
theorem coeff_field_fails :
    coeffAt 0 (-1) (iotaHom R.zInv) ≠ (-1) ^ ((-1 : ℤ).toNat) * coeffAt (-0) (-1) R.zInv := by
  rw [iotaHom_zInv]; simp [coeffAt, R.zInv]
end
end SM
```

So `MirrorSubstitutionData iotaHom` is refutable and `ui_mirrorSubstitution` cannot be proved as frozen.  Recommended
amendment (statement-level, judge's approval): `coeff : ∀ f d k, coeffAt d k (ι f) = (-1) ^ k.natAbs * coeffAt (-d) k f`.
(`(-1)^{|k|} = (-1)^k`.)  The docstring already says `(−1)^k`.

### 4.3 The tangency count on the actual construction (probe section (ii))

`Θ(t) = θu 0 + Σ_j ϑ_j φ((t − a_j)Λ/ℓ_j)` with `φ = Real.smoothTransition`, `ℓ_j = 2ε cos(ϑ_j/2)/M(ϑ_j)`, `M` by quadrature,
`ε = 0.02`, `u = dirOf φ` with `φ` admissible (random, away from every edge direction mod π and from the negative turn's swept
arc).  Levels `φ + 2πn` (tangent `u`) and `φ + π + 2πn` (tangent `−u`) counted by floor jumps on 200 000 samples.

| polygon | rot | #`u` | senses | in positive junction | #`−u` | senses | reversed: rot, #`u`, senses, #`−u`, senses |
|---|---|---|---|---|---|---|---|
| 61-gon trefoil | 2 | 2 | +,+ | yes, yes | 2 | +,+ | −2, 2, (−,−), 2, (−,−) |
| pentagram | 2 | 2 | +,+ | yes, yes | 2 | +,+ | −2, 2, (−,−), 2, (−,−) |
| one-dissent 61-gon | 2 | 2 | +,+ | yes, yes | 2 | +,+ | −2, 2, (−,−), 2, (−,−) |

Every tangency parameter lies in an open junction of positive turn with junction length `b_j − a_j ≈ 0.003 < 1` (CurlSite
`short`), the count equals `\|rot\|` in both orientations (FR-FL-B1's "count is orientation-symmetric") and the crossing sense is
`+` exactly in the normalised orientation (FR-FL-B1's "the literal sense clause is false for the reversed orientation").
Level-count identity: `⌊x + R⌋ − ⌊x⌋ = R` on 10 000 random `(x, R ∈ ℤ)`; per-junction "number of levels strictly inside the swept
arc = |floor difference|, with sign = sign(turn)" on 20 000 random junctions: 0 violations.

### 4.4 The transverse lift on a concrete front (probe section (v))

Front `x = sin 2πt`, `z = −½ sin 4πt`: no downward vertical tangency (both vertical tangents point up), `v + z′ > 0`
everywhere, `z′ − y₀ x′ = v` to machine precision, one double point (`t = 0`, `t = ½`) with `det(v_O, v_U) = −78.96 < 0`
(negative with `t = 0` over), constants `c_O = −2 < c_U = 2` admissible, `δ = 0.03`: `circBump` is `1` at `s₀`, `0` at circle
distance `≥ δ`, in `[0,1]`; the lift has `z′ − y x′ ≥ 4.16 > 0` everywhere, `y(0) = −2 < y(½) = 2` (over = smaller `y`), and no
non-adjacent near-coincidence of lifted points (embedded).  A `TransverseKnot` with a one-negative-crossing front reading a
one-crossing polygonal `X`: `w = −1 ≤ −degAZ(P X) − 1 = −1`.

### 4.5 `ul_exists_constants` (probe section (iv))

Random `(v_O, v_U)` with `det < 0`, downward verticals excluded, classified by sign pattern: `x′_O > 0`: 29 847 samples, 0
failures; `x′_O < 0, x′_U < 0`: 14 811, 0; `x′_O < 0 < x′_U`: 14 886, 0; `x′_O = 0`: 20 192, 0; `x′_U = 0`: 20 002, 0.  Control:
`det > 0` with `x′_O < 0 < x′_U`: 25 064/25 064 fail — the determinant hypothesis is used exactly where the printed proof uses it.

## 5. Recommendations

1. BEFORE unit U-ι starts: amend `MirrorSubstitutionData.coeff` to `(-1) ^ k.natAbs` (or delete the field).  Statement-level
   change to a proof-route leaf; rows 99/100 untouched.
2. Non-blocking, optional hardening of (B) if the statement reviewer presses FR-FL-B1: an orientation-free count field for
   `Round C D ε h` itself (true; symmetric proof through `liftAt_strictAntiOn`).
3. Unit U-CHAIN should plan for an "open corner disc" lemma (`t ∈ Ioo (a j) (b j) → Lε.γ t ∈ interior (cornerDisc C ε j)`) and
   for the visit-parameter invariance after a curl; both are true but not exported by the accepted records.
4. Re-check `TransverseKnot.Reads` against the accepted row-94 module when it lands (FR-FL-C8); the composite lemma is proved
   and cheap to re-derive.
5. Fix the two cosmetic doc inaccuracies (§2.2).
