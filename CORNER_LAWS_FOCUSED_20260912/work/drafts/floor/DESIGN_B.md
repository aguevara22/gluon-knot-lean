# DESIGN B — rows 99 cf:thm-carrierfloor and 100 thm:floor: statements fixed for PROOF FEASIBILITY

Architect B, 2026-09-15 (pod, floor lane). Companion sketch `work/drafts/floor/Sketch_B.lean` (370 lines;
`cd work/lean && lake env lean ../drafts/floor/Sketch_B.lean` exits 0 in ~11 s; 0 `sorry`, 0 `axiom`; `#print axioms`
of every bundle = [propext, Classical.choice, Quot.sound] plus `SM.lp_lm` / `SM.lit_homfly` behind `P` / `homfly`).
Nothing written under work/lean. Emphasis: start from the printed proofs (sm-3:4340-4575, thm:floor 4586-4606) and the
accepted lemmas, determine what each step needs, then state the rows so that the proofs compose.

## 0. Findings that change the picture

1. **cf:lem-curl (row 98) is ACCEPTED**, not "in progress": `SM.cf_lem_curl : CurlData` (work/lean/SM/Curl.lean:8366,
   bundle :309, `CurlSite` :141, `CurlWitness` :203, entry `CurlSite.ofCarried` :352). Clause (C) can be *proved* today
   modulo the row-94 bound. Row 91 is `implemented` (SM/ContactPath.lean, D-GAP2); rows 84-90, 93 accepted; 94 pending.
2. **The printed `D̄` is "the diagram with every crossing switched" (sm-3:4425, 4533)** — NOT the accepted
   `Diagram.mirror` (LinkDiagram.lean:1379: *reflection in the first axis with over data kept*). The memo's plan
   "`MirrorCarries`" therefore does not apply to the object the proof uses. B introduces `Link.Diagram.switchAll :=
   D.withOver D.underStrand D.under_mem` (same shadow, so the rounded curve still carries it: the crux for the curl chain)
   and proves the substitution identity for it by coefficient transport with a *new* switch-all move transport (§4.C.4).
3. **The rounding construction has a GLOBAL tangent-angle lift** `CornerRounding.Θ C ε` (Rounding.lean:516) with
   `Θ_on_junction` :1469, `Θ_on_straight` :1480, `Θ_add_one` :1462, `normalize_deriv_curveMap` :1785 (`T t = dirOf (Θ t)`),
   `θu_last` :1223 (`θu k = θu 0 + 2π rot`), `G2_θu_eq` :1281, `liftAt_strictMonoOn/AntiOn` :1742/1751,
   `tangent_injOn_junction` :1820, `juncArc_mem_open_disc` :1104, `curveMap_on_junction` :1668. Since
   `Round C D ε h := CornerRounding.roundedWitness h` (:3008) *definitionally* (`Lε.γ = curveMap C ε` by rfl, `θ = liftAt`),
   clause (B) is a floor-counting exercise on `Θ`, not a re-derivation of lifts: estimate 2.0k lines, not 4k.
4. **The transverse lift needs no `x′ ≠ 0` at crossings** (the printed "At a crossing branch there is no vertical tangency"
   is not delivered by `CurlWitness` for kink branches): a 5-case choice of constants handles `x′ = 0` (then `z′ > 0`, any
   constant is admissible). §5.

## 1. Inputs read

sm-3:4282-4339 (statement), 4340-4575 (proof), 4576-4606 (thm:floor), 3870-3891 (curl), 3644-3700 (rounding);
work/drafts/gap2/GAP2_STATEMENTS_MEMO.md §3(c), §4 "99"/"100", Gap2Statements.lean §1, §7-§8; work/AUTHOR_NOTES.md D-GAP2,
D-GAP2-2b; work/drafts/curl/PLAN_FINAL.md §0-§6; work/lean: SM/Rounding.lean (:80 `PolygonDiagram`, :148 `SmoothRegularLoop`,
:183 `Carried`, :231 `RoundingWitness`, :368 `RoundingData`, :585 `Admissible`, :571 `clearance`, :3131 `cf_lem_rounding`),
SM/Curl.lean (:36 `RecordCarried`, :128 `Carried.toRecordCarried`), SM/TransverseFront.lean (:270 `SmoothKnotDiagram`, :555
`TransverseKnot`, `front`, `vertical_up`, `writhe`, `crossSign`), SM/LinkDiagram.lean (:490 `Diagram`, :547 `IsPositive`, :552
`sign`, :577 `writhe`, :637 `withOver`, :1213 `reverse`, :1219 `reverse_sign`, :1227 `reverse_writhe`, :1379 `mirror`,
:1589 `Shadow.single`), SM/LinkMoves.lean (:316 `OutsideMatch`, :569 `RIData`, :620ff `RIIData`/`RIIIData`, :713
`OrientedSmoothingData`, :751 `IsSkeinTriple`, :1135/1139 `MirrorCarries`/`ReverseCarries`, :2048 `IsSkeinTriple.mirror`,
:3238 `reverseCarries_linkEquiv`, :3318 `IsSkeinTriple.reverse`), SM/CoefficientTransport.lean (`RCompetitor`,
`coefficient_transport` :137), SM/PolynomialBlock.lean (:648 `P_rcompetitor`, :667 `P_eq_homfly`, :765 `P_support`, :793
`P_ne_zero`, :815 `P_knot_support`, :1096 `RecordPolynomialData`, :1120 `LpCoreData`), SM/LinkLaurentRing.lean (:286 `coeffAt`,
:446 `degAZ`, :506 `mindegAZ`, :513 `mindegAZ_spec`, :607 `mindegZZ`, :614 `mindegZZ_spec`, :846 `InSupportM`, :1016 `R.toRG`),
SM/AdegDefinition.lean, SM/TurningNumber.lean (:226 `normalize`, :241 `ClosedC1Curve`, :274 `rot`), SM/TurnLift.lean (:40
`IsLiftOn`, :237 `ClosedC1Curve.reverse`, :261 `rot_reverse`, :409 `GLPlusPath`), SM/RotationReversal.lean
(`principalTurn_reversal`, `rotationNumber_reversal`), SM/UniformRotation.lean (`principalTurn_sign`, `uniform_rotation`),
SM/PrincipalAngles.lean:9 (`PrincipalAngleSpec`: `−π < θ < π`), SM/CornerStateSum.lean (`cornerSlot`, `cornerSlot_cast`,
`carrierRotationInt_cast`, `cornerHomfly`), SM/UniformDefinition.lean (`CarrierUniform`, `carrierRotation`),
SM/CarriersLemma.lean (`CarriersLemmaData.corner_polygons`), SM/CarrierCornerPolygon.lean (:679 `ccpCornerPolygon_regular`,
:822 `carriers_clause_ii`), SM/LinkPositiveLift.lean (:211 `carrierPolyComp`, :596 `positiveLift`, :610 `_componentCount`,
:618 `_isPositive`, :820 `positiveLift_writhe_eq_carrierCrossingCount`), work/lean/lean-declarations.json.

## 2. Row 99 — the statement (Sketch_B.lean §1)

Decision: **one row bundle `CarrierFloorData` with four clause fields `R A B C`, each its own `structure … : Prop`** (one
field per printed clause at both levels). Names: `SM.cf_thm_carrierfloor : CarrierFloorData` (the row; free name, cf:*
convention), library theorems `cf_thm_carrierfloor_R/_A/_B` (provable now) and `cf_thm_carrierfloor_C_of_bound :
FloorRoute → TransverseFrontBound → CarrierFloorCData` (D-F11/D-F14 pattern); the row is assembled as
`⟨R, A, B, C_of_bound route fd_contact.writhe_bound⟩` once row 94 lands.

| printed (tex) | Lean | note |
|---|---|---|
| (R) "P_{−D} = P_D" 4287 | `P_reverse : ∀ X, P X.reverse = P X` | for all link diagrams, as the printed proof shows (coefficient transport); the knot case is a specialisation |
| "an oriented knot and its reverse have the same polynomial" 4288 | `knot_reverse : X.componentCount = 1 → LinkEquiv X X' → P X'.reverse = P X` | FR-FL-13 |
| "same crossing signs and the same writhe" 4288-4289 | `sign_reverse`, `writhe_reverse` (accepted `reverse_sign`, `reverse_writhe`) | |
| "the rotation of its underlying plane curve is the negative" 4289-4290 | `rot_reverse_polygon : ∀ X i, rotationNumber (X.reverse.Γ.comp i).P = −rotationNumber (X.Γ.comp i).P`; `rot_reverse_curve : γ.reverse.rot = −γ.rot` | FR-FL-1: the scoping sentence 4283-4285 gives two readings (lem:rot for polygons, cf:def-turning for smooth diagrams); both stated |
| (A) "one curve and one diagram at those data" 4292-4293 | `Round C D ε h := CornerRounding.roundedWitness h`; `one_record` (proof irrelevance), `diagram_eq` (`D_ε = D`, `Carried`) | |
| "the junction … is determined by ε, by the two incident unit directions and by the transition profile" 4293-4296 | `junction_local` (image of the junction interval equal for equal corner, `uDir`, `vDir`, `ε`) | the profile is `Real.smoothTransition`, fixed in Rounding.lean §7 |
| "the rest of the curve is L itself" 4297 | `rest_is_L` (= accepted (a) `outside`) | |
| (B) hypotheses 4306-4309 | `PolygonDiagram C` (its `generic` is the printed list), `∀ i, principalTurn C.P i ≠ 0` | |
| "after reversing orientation if necessary, either all … positive, or exactly one negative" 4309-4311 | `PositiveMajority C`; the reversed case = the clause applied to `(C.reverse, PolygonDiagram.ofDiagram D.toDiagram.reverse rfl)` | FR-FL-5 |
| "R = |rot(L)|" 4311 | `|rotationNumber C.P|` (ℝ; an integer by lem:rot) | FR-FL-11 |
| "a direction u ∈ S¹ and an ε₁ > 0 such that for every ε ∈ (0, ε₁)" 4312-4313 | `∃ u ε₁, euclideanLength u = 1 ∧ 0 < ε₁ ∧ ε₁ ≤ clearance C ∧ ∀ ε (h : Admissible C D ε), ε < ε₁ → …` | FR-FL-12: `Round` exists only for admissible `ε`; the printed proof takes `ε₁ = ε₀(L)` |
| "exactly R points at which its unit tangent equals u and exactly R at which it equals −u" 4315-4316 | `(tangencySet W u).ncard = R`, `tangencySet W u := {t ∈ [0,1) ∣ W.T t = u}` | FR-FL-2 |
| "at each of them the tangent crosses that direction in the positive sense" 4316-4317 | `CrossesPositively W t := ∃ j < k, t ∈ Ioo (a j) (b j) ∧ 0 < deriv (W.θ j) t` | FR-FL-3 |
| (C) hypotheses 4319-4331 | `CarrierFloorCHyp C X`: `shadow : X.Γ = Shadow.single C`, `positive`, `turn_ne`, `turn_lt_pi`, `alternative : UniformOrOneDissent C`; double points/corners = `X.generic` | FR-FL-6 |
| "min deg_a P_D ≥ 1 − w − R" 4332-4334 | `floor : (1 − X.writhe : ℝ) − |rotationNumber C.P| ≤ mindegAZ (P X)` | |
| "the same bound holds for f_D = [z⁰]P_D whenever f_D ≠ 0" 4336 | `floor_f : coeffAt d 0 (P X) ≠ 0 → 1 − w − R ≤ d` (literal: a present monomial of `f_D`), `floor_support` (all `k`) | FR-FL-4 |

Fidelity risks to record (FR-FL-*):
- **FR-FL-1** "rotation of its underlying plane curve" for a polygonal `Diagram` = `rotationNumber` of each component's
  polygon (lem:rot), stated for all components (a knot diagram has one); the smooth reading is `ClosedC1Curve.rot`.
- **FR-FL-2** "exactly R points" = `Set.ncard` of the *parameter* set in `[0,1)`; parameters ↔ points because every
  `u`-tangency lies in a junction, the curve is injective on each junction (`junction_embedded`) and distinct junctions
  lie in disjoint corner discs (`disc_disjoint`).
- **FR-FL-3** "crosses in the positive sense" = positive derivative of the junction lift `W.θ j` (cf:lem-rounding (b)) at the
  parameter — the printed proof's "positive angular derivative" (4409).
- **FR-FL-4** the `f_D` sentence is stated on the coefficients of `a^d z^0` (the monomials of `f_D`); no separate
  Laurent-polynomial degree of `zRow 0 (P X)` is introduced.
- **FR-FL-5** (B) is stated on the normalised data; for the reversed alternative the printed clause refers to the record of
  `(−L, −D)`, a *different* `RoundingWitness` (the printed proof: "perform the allowed normalization once", 4353). Proving
  `Round(−L,−D,ε) = reverse (Round(L,D,ε))` is NOT undertaken (would need the profile symmetry `smoothTransition_symm`
  through the whole construction). `UniformOrOneDissent C := PositiveMajority C ∨ PositiveMajority C.reverse` is equivalent
  to the memo's four-way disjunction by `principalTurn_reversal` (small lemma).
- **FR-FL-6** the class of (C): `Shadow.single C` + `X.generic` (`regular` = "principal turns existing", `transverse`,
  `no_triple`, `tail_off` = "none a corner, no corner on a non-incident edge", finiteness built into `Crossing`) plus the
  explicit `turn_ne` and the printed-but-redundant `turn_lt_pi` (`principalAngle_bounds`).
- **FR-FL-7** `D̄ = Diagram.switchAll` (the printed definition, 4533), not `Diagram.mirror`; "of the mirror knot" is
  commentary (no mirror-knot notion is formalised). The identity `P_{D̄}(a,z) = P_D(a⁻¹,−z)` is stated with an explicit ring
  endomorphism `ι` (`MirrorSubstitutionData`), as the printed `ι`.
- **FR-FL-8** "Rotate coordinates so that u is the downward vertical" = a linear rotation of the *curve*; the polygonal record
  is rotation-invariant (`det` preserved), so `RecordCarried` transports and the polygon itself is not rotated.
- **FR-FL-9** fd:contact enters as the explicit hypothesis `TransverseFrontBound` with the memo's `Carries` copied verbatim
  ("to be unified with the contact lane"); if the lane fixes `homfly X` instead of `P X`, `P_eq_homfly` bridges.
- **FR-FL-10** thm:floor's "all turns left, or exactly one right, after possibly reversing" = `CarrierUniform ∨ one dissent`.
- **FR-FL-11** `R` real (`|rotationNumber|`), the memo's ℝ-cast inequality kept; the ℤ form follows from `rotationNumber_integer`.
- **FR-FL-12** `ε₁ ≤ clearance C` in (B). **FR-FL-13** "the knot presented by D" read through `LinkEquiv` (design D2).

## 3. Row 100 — the statement (Sketch_B.lean §2)

`SM.thm_floor : FloorTheoremData` (free name; keep the memo's) with `a_floor` (hypothesis `CarrierUniformOrOneDissent`;
`cornerSlot ≤ mindegAZ (cornerHomfly …)` on def:C's objects) and `z_parity` (`InSupportM 1 …`, `0 ≤ mindegZZ …`). Library
theorems now: `thm_floor_z_parity` (provable today) and `thm_floor_of_C : CarrierFloorCData → FloorTheoremData`
(`FloorAssemblyShape`); the row once 94 lands. Unchanged from the memo except the dependency is made explicit.

## 4. Proof routes, clause by clause (accepted lemma → file:line)

**(R)** `Q := fun D => P D.reverse` is an `RCompetitor` (CoefficientTransport.lean:23): `planar` from
`reverseCarries_planarIsotopic` (LinkMoves:2459) + `P_planar` (PolynomialBlock:604); `RI/RII/RIII` from `reverseCarries_RI/RII/RIII`
(:3071/:3117/:3231) + `P_reidemeister_*` (:605-607); `circle`: `IsCrossingFreeCircle.reverse` (new, 15 lines: `c` is rfl, crossings
via `reverseCrossingEquiv` LinkDiagram:1199); `skein` from `reverse_skein` (:3328) + `P_skein` (:638). Then `coefficient_transport Q P`
(:137) with `P_rcompetitor` (:648). `knot_reverse`: `homfly_spec.descent` (LinkInterfaces:118) + `P_eq_homfly`. `sign_reverse`,
`writhe_reverse`: LinkDiagram:1219/:1227. `rot_reverse_polygon`: `X.reverse.Γ.comp i = (X.Γ.comp i).reverse` (rfl),
`rotationNumber_reversal (X.generic.regular i)` (RotationReversal.lean). `rot_reverse_curve`: TurnLift:261. **≈150 lines.**

**(A)** `one_record`: `rfl` (proof irrelevance). `diagram_eq`: `⟨(Round …).carried⟩`. `rest_is_L`: field `outside`.
`junction_local`: `curveMap_on_junction` (:1668) gives `Lε.γ '' Icc (a j) (b j) = juncArc (A0 j) ε (θu j) (turn j) '' Icc 0 1`
(the affine reparametrisation `(t − a j)Λ/ℓ` maps `Icc (a j) (b j)` onto `Icc 0 1`: `G2_arg_b` :1340); `A0 j = C.P j − ε•uDir j`
(:525); `turn j = principalAngle (uDir) (vDir)` is scale-invariant (`principalAngle` of normalised directions: new lemma
`principalAngle_normalize`, ~40 lines) and `θu C j` is *an* argument of `uDir j` (`dirOf_θu` :1207), so two data with equal
`(P j, uDir, vDir, ε)` give `juncArc` data differing by `θu ↦ θu + 2πm` — `juncArc` is `2π`-periodic in `θu` (`dirOf`
periodicity, ~30 lines). **≈250 lines.**

**(B)** (Sketch §3.6). B-LIFT: `W.T t = dirOf (Θ C ε t)` (`normalize_deriv_curveMap` :1785, `tangentField` :522) and
`Θ = liftAt j` on junctions (:1469), `= θu (j+1)` on straight parts (:1480). B-CHOICE (4362-4368): pick `φ` with
`θu j ≢ φ (mod π)` for all `j` (finite set of forbidden classes) and, if one turn `ϑ₋ < 0`, `φ + nπ ∉ [θu j₋ + ϑ₋, θu j₋]`: the
complement of `A ∪ (A+π)` in a period is the open interval `(θu j₋, θu j₋ + ϑ₋ + π)` of length `π + ϑ₋ > 0`
(`turn_bounds` :1155 gives `|ϑ| < π`); an open interval minus finitely many points is nonempty (`Set.Infinite.diff`). B-COUNT
(4383-4419): on `[0,1)` the partition `[a j, b j) ∪ [b j, a (j+1))` (`a_zero`, `a_last`, `a_lt_b`, `b_lt_a`); levels
`φ + 2πn` are never met on straight parts (choice) nor at junction ends (`liftAt_a` :1714, `liftAt_b` :1717) nor inside the
negative junction (`θ_range` + choice); inside a positive junction `liftAt` is `StrictMonoOn` (:1742) and continuous
(`liftAt_smooth` :1684), so each level in `Ioo (θu j) (θu j + ϑ_j)` is attained exactly once (`θ_unique`, field), i.e. the
solution count is `#{n : θu j < φ + 2πn < θu j + ϑ_j} = ⌊x_{j+1}⌋ − ⌊x_j⌋` with `x_j := (θu j − φ)/2π ∉ ℤ` (`Int.card_Ioc`,
`Int.floor` monotonicity); `θu (j+1) = θu j + turn j` (`G2_θu_eq` :1281) telescopes to `⌊x_0 + rot⌋ − ⌊x_0⌋ = rot`
(`θu_last` :1223, `rotationNumber_integer`, `Int.floor_add_intCast`). `rot ≥ 1` in the normalised case: `uniform_rotation`
(UniformRotation.lean) via `principalTurn_sign` (turn signs ↔ `turn`). Positivity of `deriv (liftAt j) t`: `G3_hasDerivAt_liftAt`
(:1761), `deriv_liftAt_ne_zero` (:1773), monotone ⇒ `0 ≤ deriv` ⇒ `0 <`. The `−u` count is the same with `φ + π`.
Needs from lem:uniformrot: only `rot ≥ 1` (clause (i)/(ii)); from cf:lem-rounding (b): the fields `θ_lift`, `θ_strict`,
`θ_unique`, `θ_range`, `direction_once`, `immersion` — all read off `roundedWitness` (:3008). **≈2000 lines.**

**(C)** (printed 4423-4575). Steps, with the interface each consumes:
1. WLOG `PositiveMajority C` by (R): from `alternative` either directly or pass to `(C.reverse, X.reverse)`:
   `X.reverse.Γ = Shadow.single C.reverse` (rfl: `(single C).reverseShadow = single C.reverse` checked by `rfl` in the probe),
   `P X.reverse = P X`, `X.reverse.writhe = X.writhe`, `|rotationNumber (reversal C.P)| = |rotationNumber C.P|`,
   positivity (`reverse_sign`), `turn_ne`/`turn_lt_pi` (`principalTurn_reversal`). ~120 lines (unit C-ASSEMBLE).
2. `D := PolygonDiagram.ofDiagram X shadow` (:107; `toDiagram_ofDiagram` :114). (B) gives `(u, ε₁)`; take `ε := ε₁/2`,
   `h : Admissible` (`turn_ne`, `0 < ε`, `ε < clearance`), `W := Round C D ε h`. `R := rot ≥ 1`, `W.curve.rot = rot` (`rot_eq`).
3. `Xbar := X.switchAll`; `Carried W.Lε Xbar` (`SwitchAllBasicUnit`: `τ` unchanged, `overVisit`/`underVisit` exchanged,
   `det_swap` Chirotope.lean:30, `SignType.sign_neg`); all signs `−1` (from `positive`), writhe `−w`.
4. Curl chain (`CurlChainUnit`, §6 unit CURL-CHAIN): iterate over `tangencySet W u` (finite, card `R`). State after `i`
   curls: `(F_i, X_i, c_i : RecordCarried F_i X_i)` with `P X_i = P Xbar`, `X_i.writhe = −w − i`, all negative,
   `F_i = W.Lε` with derivative off the union of the used windows `(s₁,s₂)_l ⊂ (a j_l, b j_l)`, `{t ∈ [0,1) ∣ T_i t = u}` =
   the unused tangencies, double points of `F_i` = crossing points of `X` ∪ kink points (each inside `Δ_l ⊆ cornerDisc j_l`).
   Site for the next tangency `t₀ ∈ Ioo (a j) (b j)`: `CurlSite` fields from `RoundingWitness` — `embedded` (`junction_embedded`,
   `F_i = W.Lε` on the junction), `no_double` (a `τ'` in the junction would put a double point of `F_i` in `cornerDisc j`:
   crossing points are excluded by `disc_no_double`, kink points by `disc_disjoint`), `lift`/`turns_pos` (`θ_lift`, `θ_strict.1`;
   the junction is positive because `0 < deriv (θ j) t₀` excludes `StrictAntiOn`), `isolated` (`direction_once`), `short`
   (`b j − a j < 1` from the chain `a 0 = 0 < … < a k = 1`), `Δ₀ := cornerDisc C ε j` with `p ∈ interior Δ₀`
   (`juncArc_mem_open_disc` :1104 through `curveMap_on_junction`). `exists_curl` gives `Δ ⊆ Δ₀`; the invariants propagate by
   `unchanged`/`unchanged_deriv`/`new_in_disc`/`no_u`/`doubles_outside`/`one_double`/`old`/`old_sign`/`kink_neg`/`poly_eq`/
   `writhe_eq`. Distinct tangencies lie in distinct junctions (`direction_once`), so the windows are pairwise disjoint and
   later sites are untouched — the printed "leave one another intact" (4443-4445).
5. `RotationUnit`: `G := rotPlane φ ∘ F_R` with `rotPlane φ u = downDir`; `RecordCarried G X_R` (`det (ρa) (ρb) = det a b`);
   no `downDir` tangency. **Not** the accepted `GLPlusPath` (no path needed).
6. `TransverseLiftUnit` (§5) gives `K` with `xzOf K.T = G.γ`, `K.front.Carries X_R`; `CarriesWritheUnit`: `K.front.writhe =
   X_R.writhe = −w − R`.
7. `TransverseFrontBound K X_R`: `−w − R ≤ −degAZ (P X_R) − 1 = −degAZ (ι (P X)) − 1 = mindegAZ (P X) − 1`
   (`P X_R = P Xbar = ι (P X)` by `SwitchAllPolynomialUnit`; `degAZ_eq` of `MirrorSubstitutionData`, `P_ne_zero` :793). Hence
   `floor`; `floor_f`/`floor_support` by `mindegAZ_spec` :513.
Substitution identity (4531-4566), `SwitchAllPolynomialUnit`: `Q := fun D => ι (P D.switchAll)` is an `RCompetitor`: moves by
`SwitchAllCarriesUnit` + `P_planar`/`P_reidemeister_*` + `ι` a ring hom; `circle` (`P_circle` :609, `ι 1 = 1`); `skein`: from
`IsSkeinTriple Dm.switchAll Dp.switchAll D0.switchAll` and `P_skein`, apply `ι` (`ι a = a⁻¹`, `ι a⁻¹ = a`, `ι z = −z`) and
rearrange — exactly the printed "multiplied by −1" (4540-4544). Then `coefficient_transport Q P`.
`SwitchAllCarriesUnit`: the moves are shadow-level relations with over data only in `OutsideMatch.over_eq/under_eq` (:316,
swap), `RIData` (kink of either sign: nothing to do), `RIIData.same_over` (:620ff: `OverOn a'` ↔ `OverOn b'` after switching, via
`Separates`), `RIIIData` (rename `(a,b,c) ↦ (c,b,a)`: `top_*` ↔ `mid_*` after switching, `BeforeOn` shadow-level); `Reparam`
(:373: `over_map/over_surj` need the under-visit version — a lemma that a reparametrisation carries the *pair* of visits of a
crossing, ~80 lines) and `Deform` (:427: `deform` keeps `overStrand` by label, so `switchAll` commutes by rfl/ext);
`IsSkeinTriple`: `Dm = Dp.switch x` ⇒ `Dm.switchAll = Dp.switchAll.switch x`, `x` positive in `Dm.switchAll`, smoothing
transported by `OutsideMatch` swap + the arcs (`over_on_a`/`under_on_b` exchange `a ↔ b`, `a₀ ↔ b₀`). **≈450 lines.**
`MirrorSubstitutionData`: `ι := AddMonoidAlgebra.lift ℤ (ℤ×ℤ) R (Multiplicative.ofAdd (d,k) ↦ a^{−d}·(−z)^k)` (units of `R`,
`R.aUnit`, `R.zUnit` LinkLaurentRing:168/170); `coeff` from `lift_single`; `degAZ_eq` from `degAZ_eq_of_spec` (:465) +
`mindegAZ_spec`. **≈300 lines.**

**thm:floor** `a_floor`: `C := carrierPolyComp hn hP S q hS` (LinkPositiveLift:211), `X := positiveLift …` (:596), `shadow` rfl
(`positiveLift_Γ`), `positive` (:618), `turn_ne`/`turn_lt_pi` from `carriers_clause_ii` (CarrierCornerPolygon:822: `Regular`,
`turn ≠ 0`) via `principalTurn_sign` and `principalAngle_bounds`, `alternative` from `CarrierUniformOrOneDissent` via
`principalTurn_sign` (SignType ↔ real sign). (C) gives `(1 − writhe) − |rot| ≤ mindegAZ (P X)`; `positiveLift_writhe_eq_
carrierCrossingCount` (:820), `carrierRotation = rotationNumber (ccpCornerPolygon)` (rfl), `cornerSlot_cast`
(CornerStateSum), `P_eq_homfly`; cast ℝ → ℤ (`Int.cast_le`). `z_parity`: `P_support` (:765) with `positiveLift_componentCount`
(:610) and `P_eq_homfly`; `0 ≤ mindegZZ`: `mindegZZ_spec` (:614) + `P_knot_support` (:815) (`k = 2j ≥ 0`). **≈250 lines.**

## 5. The transverse lift (sm-3:4456-4523): exact needs and how the risk is bounded

Input `F : SmoothRegularLoop`, `X`, `c : RecordCarried F X`, no `downDir` tangency, all signs `−1`. Formulas (Sketch §3.4):
`v = euclideanLength (deriv F.γ s)`, `y₀ = −x′/(v + z′)` (`liftY0`), bump `ψ_{s₀,δ}(s) = smoothTransition((cos 2π(s−s₀) −
cos 2πδ)/(1 − cos 2πδ))` (`circBump`), `y = y₀ + Σ_v ψ_{τ v,δ}·(c_v − y₀)` (`liftY`), `T = (x, y, z)` (`liftT`).
Analytic facts needed (each a leaf):
- L1 `v + z′ > 0`: `v ≥ |z′|` (`abs_le_norm`-type on `planeComplex`), equality only if `x′ = 0 ∧ z′ ≤ 0`, excluded by regularity
  and the no-`downDir` hypothesis (`normalize (0, z′) = (0, −1)` for `z′ < 0`: `normalize_smul_of_pos`). ~80 lines.
- L2 `y₀` is `C^∞` and 1-periodic: `ContDiff.fst/snd` of `deriv F.γ` (`F.smooth.iterate_deriv`/`ContDiff.deriv'`),
  `ContDiff.sqrt` (Mathlib.Analysis.SpecialFunctions.Sqrt:164, `v = √(x′²+z′²)`; or `ContDiffAt.norm`) with L1 for the
  denominator; periodicity from `SmoothLoop.deriv_periodic`. ~120 lines.
- L3 `z′ − y₀ x′ = v` (pure algebra with `v² = x′² + z′²`, `field_simp`, `nlinarith`). ~40 lines.
- L4 bump: `C^∞` (`smoothTransition.contDiff`, `Real.contDiff_cos`), 1-periodic (`Real.cos_add_two_pi`-type), `= 1` at `s₀`
  (`one_of_one_le`), `= 0` unless `∃ n, |s − s₀ − n| < δ` (`zero_of_nonpos`, `Real.cos_lt_cos_of_nonneg_of_le_pi` on the
  circle distance), `∈ [0,1]`. Requires `0 < δ < 1/2`. ~250 lines (the circle-distance ↔ cosine monotonicity is the fiddly part).
- L5 constants (`LiftConstantsUnit`, 4477-4494): five cases on `(x′_O, x′_U)` signs with `det(t_O,t_U) < 0` used only when
  `x′_O < 0 < x′_U` (`det = x′_O x′_U (m_U − m_O)`); cases `x′ = 0` use `z′ > 0` (no `downDir`). ~250 lines.
- L6 disjointness: `δ` below half the minimal circle distance of the finitely many `τ v` (`τ_inj`, `Finset.min'` over
  `Finset.univ.offDiag`) and below each admissibility radius (`z′ − c_v x′ > 0` open, `Metric.continuousAt_iff`, finitely many).
  At most one bump is nonzero at any `s`: `Finset.sum_eq_single`. ~200 lines.
- L7 positivity `z′ − y x′ > 0`: convex combination `(1−b)·v + b·(z′ − c_v x′)` with `b ∈ (0,1]`. ~80 lines.
- L8 `y (τ v) = c_v` (`ψ_{τ v}(τ v) = 1`, others `0`). ~40 lines.
- L9 `TransverseKnot` fields: `smooth` (L2, L4, `ContDiff.prodMk`), `periodic`, `embedded` (`xz` equal ⇒ `F.γ s = F.γ t` ⇒
  `SameT ∨` a double point ⇒ `(τ v, τ (twin v))` by `c.doubles` after `Int.fract` reduction ⇒ `y` values `c_O ≠ c_U`, contradiction),
  `positive` (L7 with `deriv (zOf T) = z′` etc. via `HasDerivAt.prodMk` uniqueness, as `TransverseFront.deriv_xz`), `immersion`
  (`xzOf T = F.γ` by `funext`/`Prod.mk.eta`), `doubles_finite` (image of `Fintype X.Γ.Visit` under `v ↦ (τ v, τ (twin v))`),
  `transverse` (`c.transverse` after reduction), `no_triple` (`c.no_triple`, Curl.lean:88). ~500 lines.
- L10 `Carries`: `τ`, `twin_double` (`twin_eval`, `τ_inj`, `twin_ne`), `doubles`, `order` (verbatim), `over_eq` (L8, `c_O < c_U`),
  `sign_eq` (`crossSign_eq_sign` TransverseFront + `c.sign_eq`). `CarriesWritheUnit`: bijection `x ↦ (τ (overVisit x), τ (underVisit x))`
  onto `crossingPairs` (`isOver_xor` for uniqueness), `Finset.sum_nbij'`. ~300 lines.
Risk bound: no piecewise definitions (periodicity and smoothness of `circBump` are free), no `x′ ≠ 0` assumption, the only
compactness/IVT-free analytic content is L1/L4; everything else is algebra and finite bookkeeping. **Total ≈1500-1900 lines.**

## 6. Unit decomposition (byte-identical skeleton copies of `Sketch_B.lean` §3 interfaces; statements frozen; leaves `sorry`;
helper prefix per unit)

| unit | prefix | proves | lines | hours | deps | wave |
|---|---|---|---|---|---|---|
| U-R | `R_` | `CarrierFloorRData` (§4 (R)) | 150 | 2 | accepted only | 1 |
| U-A | `A_` | `CarrierFloorAData` | 250 | 3 | Rounding internals | 1 |
| U-B1 | `B1_` | `GlobalLiftUnit`, `DirectionChoiceUnit` | 600 | 7 | Rounding internals, `turn_bounds` | 1 |
| U-B2 | `B2_` | `LevelCountUnit` (floor counting, telescoping, positive derivative) | 900 | 10 | B1 statements | 1 |
| U-B3 | `B3_` | `CarrierFloorBData` from B1+B2 (`−u` via `φ+π`, `rot ≥ 1` by `uniform_rotation`, `ε₁ := clearance`) | 450 | 5 | B1, B2 | 2 |
| U-MIR-ι | `I_` | `∃ ι, MirrorSubstitutionData ι` | 300 | 4 | Laurent ring | 1 |
| U-MIR-SW | `SW_` | `SwitchAllBasicUnit`, `SwitchAllCarriesUnit` | 450 | 6 | LinkMoves | 1 |
| U-MIR-EQ | `ME_` | `SwitchAllPolynomialUnit ι` | 80 | 1 | ι, SW | 2 |
| U-CHAIN | `CH_` | `CurlChainUnit` (state structure, step lemma, `Finset` induction) | 1800 | 20 | `cf_lem_curl`, Rounding fields | 1 |
| U-ROT | `RO_` | `RotationUnit` | 250 | 3 | Curl (`RecordCarried`) | 1 |
| U-LIFT-1 | `L1_` | L1-L4 (`liftY0`, `circBump` facts) | 500 | 6 | Mathlib | 1 |
| U-LIFT-2 | `L2_` | L5-L8 (`LiftConstantsUnit`, disjointness, positivity) | 550 | 6 | L1 statements | 1 |
| U-LIFT-3 | `L3_` | L9-L10: `TransverseLiftUnit`, `CarriesWritheUnit` | 800 | 9 | L1, L2 | 2 |
| U-C | `C_` | `cf_thm_carrierfloor_C_of_bound : FloorRoute → TransverseFrontBound → CarrierFloorCData` (WLOG, composition, degree algebra) | 500 | 5 | all unit statements | 2 |
| U-FLOOR | `F_` | `thm_floor_z_parity`, `thm_floor_of_C` | 250 | 3 | def:C, lp:core | 1 |
| total | | | **≈ 7,800** | **≈ 90 prover-h; 3 waves, ~12-16 h wall with 8 provers** | | |

Critical path: U-CHAIN (1800) ‖ U-B2 (900) → U-B3; U-LIFT-1/2 → U-LIFT-3; then U-C. Check per unit: `cd work/lean && lake env lean
../drafts/floor/U_<unit>.lean`. Assembly: concatenate in sketch order, `#print axioms` (expected: [propext, Classical.choice,
Quot.sound, SM.lp_lm, SM.lit_homfly] for the (R)(A)(B) theorems and the `_of_bound` theorems), port as `SM/CarrierFloor.lean`
(imports SM.Curl, SM.TransverseFront, SM.UniformRotation, SM.CornerStateSum, SM.LinkPositiveLift, Mathlib …Sqrt).

## 7. Risks, ranked, with mitigations

1. **Curl-chain bookkeeping** (U-CHAIN): the invariant "double points of `F_i` ⊆ crossing points ∪ kink points" and "distinct
   tangencies ⇒ distinct junctions ⇒ disjoint windows" carry the whole induction; mitigation: state the invariant as a
   `structure CurlChainState : Prop`, prove one step lemma, induct on `Finset` (`Finset.induction_on`) over the tangency set;
   probe the step statement for truth before proving (the `no_double` field is the delicate one — see §4.C.4).
2. **Transverse lift, bump support/disjointness** (L4, L6): circle-distance vs cosine monotonicity; mitigation: `circBump`
   through `cos` (periodicity/smoothness free); reduce to `s ∈ [s₀ − 1/2, s₀ + 1/2)` by `Int.fract`; `δ < 1/4`.
3. **Switch-all move transport** (U-MIR-SW): the `Reparam` under-visit lemma and `RIIIData` relabelling; mitigation: the
   shadow is unchanged, so only over-data fields move; probe each structure's fields (they are listed in §4.C) before proving.
4. **(B) level counting**: floor telescoping with non-integer endpoints; mitigation: prove the one-junction count as a lemma
   about `StrictMonoOn` continuous `θ` on `Icc` and integer levels, then sum.
5. **(A) `junction_local`** needs `principalAngle` scale invariance and `2π`-periodicity of `juncArc` in `θu` — small but new.
6. **Interface drift with the contact lane**: `Carries` and the bound's ring (`P` vs `homfly`); mitigation: the lift unit exports
   `xzOf K.T = F.γ` and the record data separately, so a different final `Carries` is re-assembled in U-LIFT-3 only.
7. Fidelity: FR-FL-5 (B stated on normalised data) and FR-FL-7 (`switchAll` vs `mirror`) must be accepted by the statement
   reviewer; both follow the printed proof's own words (4353, 4533).

## 8. Reporting shape

Until row 94: `CarrierFloorRData/AData/BData` proved and reviewed as library theorems; `CarrierFloorCData` and `FloorTheoremData`
stated; `cf_thm_carrierfloor_C_of_bound`, `thm_floor_of_C`, `thm_floor_z_parity` proved. Rows 99/100 stay unmapped (the map's
declarations are row theorems). FINAL_REVIEW sentence: "Row 99: clauses (R)(A)(B) proved (`cf_thm_carrierfloor_R/_A/_B`); (C)
proved conditionally on the fd:contact writhe bound (`cf_thm_carrierfloor_C_of_bound`, hypothesis `TransverseFrontBound`);
row 100 likewise (`thm_floor_of_C`, `thm_floor_z_parity`)." When 94 lands: `cf_thm_carrierfloor := ⟨R, A, B, C_of_bound route
fd_contact.writhe_bound⟩`, `thm_floor := thm_floor_of_C cf_thm_carrierfloor.C`, map, review, accept.
