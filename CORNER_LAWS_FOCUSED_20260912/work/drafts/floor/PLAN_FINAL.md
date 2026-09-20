# PLAN FINAL — rows 99 cf:thm-carrierfloor and 100 thm:floor: judge's decision, fixed statements, route, units

Rows 99 (reference/SM/sm-3-statesum.tex:4282-4339 statement, 4340-4575 proof) and 100 (4576-4585 statement,
4586-4602 proof). Judge (subagent), 2026-09-15 ~15:00Z. Inputs: DESIGN_A.md / Sketch_A.lean (Architect A, fidelity
emphasis) and DESIGN_B.md / Sketch_B.lean (Architect B, proof feasibility). Both sketches re-checked with the plain
`cd work/lean && lake env lean <file>`: Sketch_A 0 errors, 12 declarations with `sorry` (13 leaves); Sketch_B 0 errors,
0 `sorry` (statement-level only: its route is `def … : Prop` interfaces, no assembly proved). Also read: the printed
statements and proofs, cf:lem-rounding (3644-3700), cf:lem-curl (3870-3891), def:transverse-front (3328-3340),
lem:rot / lem:uniformrot (sm-1:407-470), the accepted modules cited below (grep-verified), the gap2 memo §3(c)/§4 and
Gap2Statements.lean §1/§7-§8, work/drafts/curl/PLAN_FINAL.md (the pattern), AUTHOR_NOTES D-GAP2/D-GAP2-2b, and — decisive
for the interface — the PARALLEL contact-lane designs work/drafts/contact/DESIGN_A.md §3-§4, DESIGN_B.md §3-§5,
Sketch_A.lean §4, Sketch_B.lean §0/§4 (row 94, written 14:24-14:31Z, same hour as the floor designs).

Deliverables (this directory; nothing written under work/lean):
- `Statements_FINAL.lean` (730 lines) — the fixed statements + the frozen proof-route leaves.
  `cd work/lean && lake env lean ../drafts/floor/Statements_FINAL.lean`: 0 errors, 11 s warm; 23 declarations use
  `sorry` (the 21 unit leaves of §8 and the two stated corollaries `CarrierFloorAData.junction_local`,
  `CarrierFloorCData.floor_support`); the clause assemblies `cf_thm_carrierfloor_R/_A/_B`, the conditional rows
  `cf_thm_carrierfloor_of_bound`, `thm_floor_of_C`, `thm_floor_of_bound` and the interface derivation
  `transverseFrontBound_of_fdContactShape` are PROVED from the leaves.
  `#print axioms`: `CarrierFloorData` = [propext, Classical.choice, Quot.sound, SM.lp_lm] (the policy axiom behind
  `P`); `FloorTheoremData` = [.., SM.lit_homfly] (behind `cornerHomfly = homfly ∘ positiveLift`, as def:C);
  `TransverseFrontBound`, `FdContactShape`, `transverseFrontBound_of_fdContactShape` = [.., SM.lp_lm];
  `CarrierFloorCHyp.of_diagram`, `iotaHom`, `zZeroPart` = [propext, Classical.choice, Quot.sound].
- this file.

## 0. Verdict: **A wins** (statement shape: one field per printed clause, redundant printed hypotheses kept, knot-case
(R), literal reversal alternatives, `f_D` as the `z⁰` row, both ℤ/ℝ forms of thm:floor's display), with B's route
grafted and ONE judge's repair that neither candidate has (the row-94 interface, §2.1)

| criterion | A | B | decision |
|---|---|---|---|
| (R) `P_reverse` | knot diagrams (`componentCount = 1`), as printed; library lemma `ur_P_reverse_all` unconditional | all diagrams (the proof's generality) | **A**: the row field is the printed sentence ("Let D be an oriented knot diagram"); a widened field is a reviewer flag for no gain, the general lemma stays in the library (FR-FL-R1) |
| (R) rotation of the polygonal curve | `X.Γ = single C → X.reverse.Γ = single C.reverse ∧ rot C.reverse = −rot C` | `∀ i : Fin X.Γ.c, rot (X.reverse.Γ.comp i) = −rot (X.Γ.comp i)` | **A** (the knot diagram's ONE underlying curve, and the identification of `−D`'s curve with the reversed polygon is part of the field); B's per-component form is a corollary |
| (A) locality clause | `junction_determined`: the junction on `[a j, b j]`, rescaled to `[0,1]`, EQUALS `junctionTemplate q u v ε` (a function of `(q, u, v, ε)` + the fixed profile) | `junction_local`: equal `(q, u, v, ε)` ⇒ equal junction images (two records) | **A + graft**: A's parametric form is "determined by" made literal and implies B's (stated as the corollary `CarrierFloorAData.junction_local`); `length_determined` is a separate printed sub-clause (A only) |
| (B) hypothesis form | `UniformOrOneDissent C → (AllPosOrOneNeg C.P ∧ BClaim C D) ∨ (AllPosOrOneNeg (reversal C.P) ∧ BClaim C.reverse D.reverse)` | `PositiveMajority C → ∃ u ε₁ …` (normalised data only) | **A** (the printed hypothesis "after reversing orientation if necessary" is the row's hypothesis; the conclusion names the orientation the claim holds for, FR-FL-B1). Equivalent to B's given `k ≥ 3` (both orientations cannot be positive-majority) |
| (B) vocabulary | `TangencyCount W u R := Finite ∧ ncard = R ∧ ∀ t, crosses positively` (inline set) | `tangencySet`, `CrossesPositively` named; no `Finite` conjunct (implied by `ncard = R ≥ 1`) | **graft B's names into A's shape**: `tangencySet`, `CrossesPositively`, `TangencyCount` with the explicit `Finite` (FR-FL-B2) |
| (C) hypothesis class | 7 fields = the printed list, redundant ones kept (`turn_exists`, `turn_lt_pi`, `generic`); `of_diagram` PROVED | 5 fields (drops `turn_exists`, `generic`: covered by `X.generic`) | **A**: "These conditions are stated here so that no generic parent polygon is assumed" (sm-3:4327-4329) is a printed instruction; same class either way, A's is field-for-field (FR-FL-C1) |
| (C) `f_D` sentence | `floor_zZero : zZeroPart (P X) ≠ 0 → bound ≤ mindegAZ (zZeroPart (P X))` (new 1-line def, two coefficient lemmas proved) | `floor_f : coeffAt d 0 (P X) ≠ 0 → bound ≤ d` + `floor_support` | **A + graft**: the printed sentence is a `mindeg_a` statement about the Laurent polynomial `f_D`, rendered literally; B's coefficient form is the corollary `CarrierFloorCData.floor_support` (FR-FL-C3) |
| (C) conclusion | `((1 − w : ℤ) : ℝ) − |rot| ≤ (mindegAZ (P X) : ℝ)` | same | equal (FR-FL-C2) |
| thm:floor alternative | `AllLeftOrOneRight Q ∨ AllLeftOrOneRight (reversal Q)` (literal reversal, `turn = 1` left) | `CarrierUniform ∨ ∃ τ ≠ 0, one dissent of sign −τ` (memo's 4-way) | **A** (literal; equivalent since carrier turns are nonzero, FR-FL-F1) |
| thm:floor display | `cornerSlot ≤ mindegAZ H ∧ 1 − m_Q − |r_Q| ≤ mindegAZ H` (ℤ and the printed ℝ form) | ℤ form only | **A** (the printed `= d_Q` is `cornerSlot_cast`; both readings exported) |
| `z`-parity | `∀ d k, coeffAt d k H ≠ 0 → ∃ j, k = 2j` spelled out | `InSupportM 1 H` (accepted `M_1 = ℤ[a^{±1}, z²]`, lp:support) | **B** (reuse of the accepted set; its docstring is the printed membership) |
| the mirror `D̄` | `Diagram.switchAll := withOver underStrand`, new transport; reflection fallback recorded | same, plus `switchAll_Γ`/`switchAll_overStrand` rfl lemmas, `SwitchAllBasicUnit`, `SwitchAllCarriesUnit`, `MirrorSubstitutionData`, `SwitchAllPolynomialUnit` | **B's unit interfaces** on A's `iotaHom` (explicit `AddMonoidAlgebra.lift`, typechecks as `R →+* R`) |
| rotation | `rotationMap φ` (name CLASHES with the accepted `SM.rotationMap : Plane →ₗ[ℝ] Plane`, SM/StarPolygons.lean:44), φ given | `rotPlane`, `downDir`, `∃ φ G, … ∧ (T_G = downDir ↔ T_F = u)` | **B** (no clash; the choice of `φ` inside the leaf) |
| (B) proof route | concatenated lift built by hand from the junction lifts `θ j` + straight constants (3000 lines) | the construction's GLOBAL angle `Θ C ε` (Rounding.lean:516) with `normalize_deriv_curveMap` (1785), `Θ_on_junction/straight` (1469/1480), `θu_last` (1223), `G2_θu_eq` (1281), `liftAt_*` (1714-1773) — 2000 lines | **B** (the lift already exists in the accepted module; `Round C D ε h` is `roundedWitness h` definitionally so `θ j = liftAt j`, `Lε.γ = curveMap`). Frozen as sub-leaves `ub_globalLift`, `ub_exists_direction`, `ub_levelCount`; A's `AdmissibleDirection` leaves kept as the library form the row consumes |
| curl chain | invariant sketched; `CurlSite.ofCarried` for the first curl, previous `carried'` afterwards; 1200 lines | invariant analysed field by field (`no_double` via `disc_no_double` + `disc_disjoint`, windows disjoint since distinct tangencies lie in distinct junctions); `CurlChainUnit` Prop; 1800 lines | **A's leaf signature** (`ucurl_exists_curled` on `D : PolygonDiagram C` all-negative, `Round C D ε h` inside) **with B's invariant analysis** as the unit brief (§3(C) step 4) |
| transverse lift | Mathlib `ContDiffBump` periodised by `round`; `Carries` output | explicit closed-form `liftY0`, `circBump` (via `cos`, periodicity/smoothness free), `liftY`, `liftT`, 5-case constants, L1-L10 leaf list; `Carries` output | **B's formulas** (frozen as defs), **output CHANGED to `TransverseKnot.Reads` (a `HeightMarking`)** — §2.1 |
| row-94 interface | memo's `SmoothKnotDiagram.Carries` copied; `TransverseFrontBound` on it; FR-FL-C6 "depends on the contact lane keeping `Carries` record-level" | same copy; "interface drift" listed as risk 6 | **NEITHER**: the contact lane has dropped `Carries` (never in work/lean) for the accepted `SpatialLink.HeightMarking` of `K.spatial`. Repaired here (§2.1); both designs' lift units would have produced an object row 94 does not consume |
| sketch evidence | assemblies PROVED from leaves (R from 1 leaf, B from 2, A 4/6 fields, `of_diagram`, `zZeroPart` lemmas, row/thm:floor conditionals) | 0 `sorry` because nothing beyond `rfl` is proved | A |
| effort | ≈ 9000 lines, 60-85 h, 3 waves | ≈ 7800 lines, ≈ 90 h, 3 waves | FINAL ≈ 8000 lines (§4) |

Scores (1-10): FIDELITY A 8.5 / B 7 (A: literal clause map, redundant hypotheses kept, knot-case (R), both forms of
the thm:floor display; one new definition `zZeroPart`, `junction_determined` stronger than printed but true of the
construction — both flagged. B: `P_reverse` widened to all diagrams, printed redundant hypotheses dropped, ℤ-only
display, memo's 4-way alternative, `f_D` as coefficients; plus `InSupportM 1`). FEASIBILITY A 7.5 / B 8 (both typecheck;
A's sketch proves the clause assemblies; B finds the accepted global lift `Θ`, the closed-form bump, the 5-case
constants and analyses `no_double`; BOTH miss that the contact lane dropped `Carries` — the lift unit as designed by
either would not plug into row 94). REUSE A 8 / B 8.5 (B reaches deeper into Rounding.lean internals and reuses
`InSupportM`, `degAZ_eq_of_spec`, `carriers_clause_ii`). Totals A 24 / B 23.5 — A on statements, B's route grafted.

## 1. Clause map (printed → Lean; tex lines; Statements_FINAL.lean)

### Row 99 (R) sm-3:4283-4290 → `CarrierFloorRData` (§2)

| tex | printed | Lean |
|---|---|---|
| 4283-4285 | "Here rot is as in Lemma lem:rot for polygons and Definition cf:def-turning for the underlying plane curve of a smooth diagram" | scopes the last sentence: two fields, `rot_reverse_polygon` (`rotationNumber`, lem:rot) and `rot_reverse_curve` (`ClosedC1Curve.rot`, cf:def-turning) |
| 4285-4287 | "Let D be an oriented knot diagram and −D the same diagram with every arrow reversed. Then P_{−D} = P_D" | `P_reverse : ∀ X, X.componentCount = 1 → P X.reverse = P X` (`Diagram.reverse` LinkDiagram.lean:1213 "reversing the orientation of every component") |
| 4287-4288 | "consequently an oriented knot and its reverse have the same polynomial" | `knot_reverse : ∀ X X', X.componentCount = 1 → LinkEquiv X X' → P X'.reverse = P X` (the knot = the `LinkEquiv` class, D2; its reverse presented by `X'.reverse`) |
| 4288-4289 | "Moreover −D has the same crossing signs" | `sign_reverse` = accepted `Diagram.reverse_sign` (1219) verbatim |
| 4289 | "and the same writhe as D" | `writhe_reverse` = accepted `Diagram.reverse_writhe` (1227) |
| 4289-4290 | "and the rotation of its underlying plane curve is the negative of that of D" | `rot_reverse_polygon : X.Γ = single C → X.reverse.Γ = single C.reverse ∧ rotationNumber C.reverse.P = −rotationNumber C.P`; `rot_reverse_curve : γ.reverse.rot = −γ.rot` |

### Row 99 (A) sm-3:4291-4305 → `Round`, `junctionTemplate`, `CarrierFloorAData` (§3)

| tex | printed | Lean |
|---|---|---|
| 4291-4292 | "Let L and D satisfy the hypotheses of Lemma cf:lem-rounding. For every ε ∈ (0, ε₀(L))" | `C : PolyComp`, `D : PolygonDiagram C`, `h : CornerRounding.Admissible C D ε` (Rounding.lean:585: `turn_ne`, `0 < ε`, `ε < clearance C`; `clearance` 571 = the accepted `ε₀(L)`) |
| 4292-4293 | "the construction … returns one curve and one diagram at those data" | `Round C D ε h := CornerRounding.roundedWitness h` (3008) — a FUNCTION; `one_record` (proof irrelevance), `one_curve` (`= roundedLoop h`, 2948), `one_diagram` (`Carried … D.toDiagram`, `smoothWrithe = writhe`) |
| 4293-4296 | "the junction inserted at the corner q_i is determined by ε, by the two incident unit directions and by the transition profile, which is fixed once and for all" | `junction_determined`: on `[a j, b j]` rescaled to `s ∈ [0,1]`, `L_ε = junctionTemplate (C.P j) (uDir C j) (vDir C j) ε s := juncArc (q − ε u) ε (arg u) (principalAngle u v) s` (`juncArc` 483, profile `Real.smoothTransition` inside) |
| 4296-4297 | "the arc length ℓ is then determined by the endpoint condition" | `length_determined`: `speed · (b j − a j) = juncLen ε ϑ_j` (480) ∧ `L_ε(b j) = q_j + ε v_j` |
| 4297 | "and the rest of the curve is L itself" | `rest_is_L` = accepted (a) (`outside`, `straight`) |
| 4298-4304 | "Write Round(L,D,ε) = (L_ε, D_ε) … rounding record" | the definition `Round`; `L_ε = (Round …).Lε`, `D_ε = D` |

### Row 99 (B) sm-3:4306-4318 → `AllPosOrOneNeg`, `UniformOrOneDissent`, `tangencySet`, `CrossesPositively`, `TangencyCount`, `BClaim`, `CarrierFloorBData` (§4)

| tex | printed | Lean |
|---|---|---|
| 4306-4309 | "closed polygon with nonzero edges and nonzero principal turns, finitely many transverse double points, no triple points, no corner at a double point and no corner on a non-incident edge, carrying a diagram D" | `C : PolyComp`, `D : PolygonDiagram C` (`generic : (Shadow.single C).Generic` = regular / tail_off / transverse / no_triple, Rounding.lean:80-93), `∀ i, principalTurn C.P i ≠ 0` (FR-FL-B5) |
| 4309-4311 | "after reversing orientation if necessary, either all principal turns are positive, or exactly one is negative and all others are positive" | `UniformOrOneDissent C := AllPosOrOneNeg C.P ∨ AllPosOrOneNeg (reversal C.P)` |
| 4311 | "Put R = |rot(L)|" | `|rotationNumber C.P|` (ℝ; an integer by lem:rot) |
| 4312-4313 | "a direction u ∈ S¹ and an ε₁ > 0 such that for every ε ∈ (0, ε₁)" | `∃ u ε₁, euclideanLength u = 1 ∧ 0 < ε₁ ∧ ε₁ ≤ clearance C ∧ ∀ ε, 0 < ε → ε < ε₁ → ∀ h : Admissible C D ε, …` (FR-FL-B4) |
| 4313-4316 | "the rounded curve L_ε of the record Round(L,D,ε) from clause (A) has exactly R points at which its unit tangent equals u and exactly R at which it equals −u" | `TangencyCount (Round C D ε h) u R ∧ TangencyCount … (−u) R`, `tangencySet W u := {t ∈ [0,1) ∣ W.T t = u}` FINITE with `ncard = R` (FR-FL-B2) |
| 4316-4317 | "at each of them the tangent crosses that direction in the positive sense" | `∀ t ∈ tangencySet, CrossesPositively W t := ∃ j < k, t ∈ Ioo (a j) (b j) ∧ 0 < deriv (W.θ j) t` (FR-FL-B3) |
| — | the orientation the claim is made for | `tangencies : … → UniformOrOneDissent C → (AllPosOrOneNeg C.P ∧ BClaim C D) ∨ (AllPosOrOneNeg (reversal C.P) ∧ BClaim C.reverse D.reverse)`, `PolygonDiagram.reverse D := ofDiagram D.toDiagram.reverse rfl` (FR-FL-B1) |

### Row 99 (C) sm-3:4319-4337 → `CarrierFloorCHyp`, `zZeroPart`, `CarrierFloorCData` (§5)

| tex | printed | Lean |
|---|---|---|
| 4320-4321 | "oriented knot diagram all of whose crossings are positive, with writhe w, whose underlying plane curve is a closed polygon L" | `shadow : X.Γ = Shadow.single C` (one component), `positive : ∀ x, X.IsPositive x` (LinkDiagram.lean:547), `X.writhe` (577) in the conclusion |
| 4321-4322 | "with all principal turns existing, nonzero, and of magnitude below π" | `turn_exists : Regular C.P`, `turn_ne`, `turn_lt_pi : |principalTurn C.P i| < π` |
| 4322-4324 | "finitely many double points, all transversal, no triple points, none of them a corner of L, no corner of L on a non-incident edge" | `generic : (Shadow.single C).Generic` (`transverse` + finiteness, `no_triple`, `tail_off` covers both corner clauses, `regular`) |
| 4324-4325 | "R the absolute value of its Whitney rotation number" | `|rotationNumber C.P|` |
| 4325-4329 | the three commentary sentences on the hypotheses | no field; the redundant fields are KEPT because of "stated here so that no generic parent polygon is assumed" (FR-FL-C1); `CarrierFloorCHyp.of_diagram` derives them from `X.generic` |
| 4329-4332 | "after reversing the orientation if necessary — which by clause (R) changes neither P_D, nor the crossings and their signs, nor w, nor R — either every principal turn is positive, or exactly one is negative and every other is positive" | `alternative : UniformOrOneDissent C`; the parenthesis is a proof remark consumed in step 1 of the route (FR-FL-C5) |
| 4333-4335 | "mindeg_a P_D(a,z) ≥ 1 − w − R" (cf:eq-floor) | `floor : ((1 − X.writhe : ℤ) : ℝ) − |rotationNumber C.P| ≤ (mindegAZ (P X) : ℝ)` (`P X ≠ 0` by `P_ne_zero`, so `mindegAZ` is def:adeg's `mindeg_a`; FR-FL-C2) |
| 4336 | "and the same bound holds for f_D(a) = [z⁰]P_D(a,z) whenever f_D ≠ 0" | `floor_zZero : zZeroPart (P X) ≠ 0 → bound ≤ mindegAZ (zZeroPart (P X))`, `zZeroPart f := ofCoeff (filter (·.2 = 0) f.coeff)` (FR-FL-C3); corollary `floor_support` (coefficient form) |

Row bundle `CarrierFloorData : Prop` with fields `clauseR clauseA clauseB clauseC`; proposed row name
`SM.cf_thm_carrierfloor : CarrierFloorData` (free: work/lean/axiom-policy.json `targets` fixes only thm:C-S3/S5/S7,
thm:C-soft, thm:comparison, prop:C-*, cor:C-inherits, SM:corner_laws_and_soft, Bridge/R/CV names).

### Row 100 thm:floor sm-3:4576-4585 → `AllLeftOrOneRight`, `CarrierUniformOrOneDissent`, `FloorTheoremData` (§7)

| tex | printed | Lean |
|---|---|---|
| 4577 | "Let Q be a subpolygon of a decomposition of a generic polygon" | `hn : 3 ≤ n`, `hP : Generic P`, `hS : IsDecomposition hn hP S`, `q : Component hn hP S`; `Q = ccpCornerPolygon hn hP S q` (def:C) |
| 4577-4579 | "after possibly reversing its orientation either all turns are left, or exactly one turn is right" | `CarrierUniformOrOneDissent := AllLeftOrOneRight Q ∨ AllLeftOrOneRight (reversal Q)`; `AllLeftOrOneRight Q := (∀ j, turn Q j = 1) ∨ (∃ j₀, turn Q j₀ = −1 ∧ ∀ j ≠ j₀, turn Q j = 1)` (def:chirotope `turn : SignType`, left = 1) (FR-FL-F1, F2) |
| 4580-4581 | "mindeg_a H⁺_Q ≥ 1 − m_Q − |r_Q| = d_Q" | `a_floor : … → cornerSlot ≤ mindegAZ (cornerHomfly …) ∧ 1 − (m_Q : ℝ) − |carrierRotation| ≤ (mindegAZ … : ℝ)` (`cornerSlot_cast` CornerStateSum.lean:87 is the printed `=`) |
| 4581-4582 | "H⁺_Q ∈ ℤ[a^{±1}, z²], so mindeg_z H⁺_Q ≥ 0" | `z_parity : InSupportM 1 H ∧ 0 ≤ mindegZZ H` (no turn hypothesis, FR-FL-F3; `InSupportM 1` = `M_1 = ℤ[a^{±1}, z²]`, LinkLaurentRing.lean:846) |

Proposed row name `SM.thm_floor : FloorTheoremData` (free).

## 2. Model decisions

### 2.1 The row-94 interface hypothesis — JUDGE'S REPAIR (both candidates wrong in the same way)

Facts. (i) The gap2 memo's `SmoothKnotDiagram.Carries` is NOT in work/lean (grep). (ii) The contact lane's two designs
(work/drafts/contact/DESIGN_A.md §3 "No new `Carries` structure … reuse `HeightMarking` (FR-FC-1)"; DESIGN_B.md §3
"the memo's `SmoothKnotDiagram.Carries` is NOT in work/lean (grep) and is dropped", D-SC-3) both state fd:contact as

```
structure FdContactData : Prop where
  over_rule_sign      : … (definitional on row 92)
  front_writhe        : ∀ K : TransverseKnot, sl K = (K.front.writhe : ℝ)
  representative_bound : ∀ K X, K.Reads X → sl K ≤ -((degAZ (P X) : ℤ) : ℝ) - 1
```
with `K.Reads X := Nonempty (K.spatial.HeightMarking K.spatial.projLoop X)`, `K.spatial : SpatialLink 1` (T := fun _ =>
K.T, …, regular := K.deriv_T_ne_zero — identical in both contact sketches), and `sl : TransverseKnot → ℝ` the document's
fd:framed-linking number through the accepted row 88 (SM/LinkingCalculus.lean `selfLinking`). (iii) The accepted
`SpatialLink.HeightMarking G S` (SM/CeSmoothingRecord.lean:219-237) is RECORD-LEVEL: `e : Fin c ≃ Fin S.Γ.c`,
`Φ : OccOf G ≃ S.Γ.Visit`, `comp_eq`, `between_iff` (cyclic order), `pair_eq` (twin pairing), `over_iff` (over bit ↔
smaller height), `sgn_eq` (sign = `crossSignOf`); no clause ties polygon crossing POINTS to double points — the shape of
the accepted `SmoothFront.Marking` (FrontSmooth.lean:1001) and of the curl lane's `RecordCarried`.

Decision. Statements_FINAL.lean §1 copies `TransverseKnot.spatial` and `TransverseKnot.Reads` VERBATIM from the contact
sketches (to be deleted when SM/FdContact.lean lands; the names then resolve to the accepted ones), states

```
def TransverseFrontBound : Prop :=
  ∀ (K : TransverseKnot) (X : Diagram), K.Reads X → K.front.writhe ≤ -degAZ (P X) - 1
```
(the sl-free composite of the two displays, exactly what sm-3:4525-4531 consumes: "sl(K_T) = w(T) = −w − R … max deg_a
P_{D̄} ≤ −sl(K_T) − 1"), and PROVES `transverseFrontBound_of_fdContactShape : FdContactShape sl → TransverseFrontBound`
where `FdContactShape sl` is the pair `front_writhe ∧ representative_bound` in the contact lane's exact ℝ-form (Sketch_B's
cast placement `((-degAZ (P X) - 1 : ℤ) : ℝ)` is `push_cast`-equal; probed). When row 94 lands:
`cf_thm_carrierfloor := cf_thm_carrierfloor_of_bound (transverseFrontBound_of_fdContactShape ⟨fd_contact.front_writhe,
fd_contact.representative_bound⟩)`, `thm_floor := thm_floor_of_C cf_thm_carrierfloor.clauseC`. If the contact lane
changes the ring (`homfly X`), `P_eq_homfly` bridges; if it changes the reading, only §1 and the lift leaf's output move.

Consequences for the route (FR-FL-C6 CONFIRMED, FR-FL-C8 NEW). The transverse-lift leaf outputs `K.Reads X` (a
`HeightMarking` of `K.spatial.projLoop`, whose `γ` is `xzOf K.T = F.γ` by `rfl`) built from `RecordCarried F X` and the
constants `c_O < c_U`: `Φ⁻¹ v := ⟨(0, τ v), _⟩` (`τ v` is an occurrence by `twin_eval`, `twin_ne`, `τ_inj`; `Φ` by
`Equiv.ofBijective`, surjective by `doubles`), `between_iff` from `order`, `pair_eq` from `doubles` + `τ_inj`,
`over_iff` from `y (τ (overVisit x)) = c_O < c_U = y (τ (underVisit x))` (`overBit` LinkDiagramRecord.lean:470),
`sgn_eq` from `RecordCarried.sign_eq` and `crossSignOf` (FrontRecordBridge.lean:118, `if 0 < det … then 1 else −1`). The
coordinate rotation (step 5) is applied to the smooth curve only and is now KNOWN to be legitimate — the reading row 94
consumes has no point-coincidence clause. The front-writhe identity `K.front.writhe = X.writhe` is part of the lift leaf
(bijection `x ↦ (τ (overVisit x), τ (underVisit x))` onto `crossingPairs`, TransverseFront.lean:350, `isOver_xor` for
uniqueness, `Finset.sum_nbij'`).

### 2.2 Retained from A (statements) — reasons in §0's table

`Round := CornerRounding.roundedWitness` (the record IS the accepted named construction — no ∃ over an unnamed family,
rem:rounding-record); `junctionTemplate` + parametric `junction_determined`; the (B) disjunctive form on
`UniformOrOneDissent`; the 7-field `CarrierFloorCHyp` with `of_diagram`; `zZeroPart`; four clause bundles + one row bundle;
`AllLeftOrOneRight` + literal reversal for thm:floor; ℤ ∧ ℝ `a_floor`.

### 2.3 Grafted from B

`tangencySet`, `CrossesPositively`; `InSupportM 1` in `z_parity`; `Diagram.switchAll` rfl lemmas, `SwitchAllCarriesUnit`
(as a `structure … : Prop`), `MirrorSubstitutionData ι` (stated for A's explicit `iotaHom : R →+* R`); `rotPlane`,
`downDir`, the `∃ φ` form of the rotation leaf; the explicit lift formulas `liftY0`, `circBump`, `liftY`, `liftT`,
`LiftAdmissible`, the constants leaf `ul_exists_constants`; the `Θ`-based sub-leaves of (B). Not adopted: B's `FloorRoute`
bundle / `CAssemblyShape` (the leaves are theorems in one file; the assembly `cf_thm_carrierfloor_C_of_bound` is itself a
unit, as in the curl lane), B's 4-way `CarrierUniformOrOneDissent`, B's coefficient-only `f_D` clause, B's all-diagram
`P_reverse` field.

### 2.4 Names

`SM.cf_thm_carrierfloor`, `SM.thm_floor` (rows, declared only when row 94 lands); library: `cf_thm_carrierfloor_R/_A/_B`,
`cf_thm_carrierfloor_C_of_bound`, `cf_thm_carrierfloor_of_bound`, `thm_floor_of_C`, `thm_floor_of_bound`,
`transverseFrontBound_of_fdContactShape`; leaf prefixes `ur_ ua_ ub_ usw_ ui_ urot_ ucurl_ ul_ uc_ uf_`. Avoided:
`rotationMap` (accepted `SM.rotationMap`, StarPolygons.lean:44). No clash for any name in work/lean/SM, CV, Bridge (grep).

## 3. Proof routes, clause by clause (accepted lemmas by file:line; all grep-verified 2026-09-15)

**(R) — U-R, ≈ 250 lines.** `Q := fun D => P D.reverse` is an `RCompetitor` (CoefficientTransport.lean:23): `planar`
from `reverseCarries_planarIsotopic` (LinkMoves.lean:2459) + `P_planar` (PolynomialBlock.lean:604); `reidemeister_I/II/III`
from `reverseCarries_RI/RII/RIII` (3071/3117/3231) + `P_reidemeister_*` (605-607); `circle`: `IsCrossingFreeCircle` is
carried (`c` is `rfl`, crossings via `Shadow.reverseCrossingEquiv` LinkDiagram.lean:1199; new 15-line lemma) + `P_circle`
(609); `skein`: `IsSkeinTriple.reverse` (3318) / `reverse_skein` (3328) + `P_skein` (638). Then `coefficient_transport Q P
hQ P_rcompetitor` (137; 648). `knot_reverse`, `sign_reverse`, `writhe_reverse`, both rotation fields: PROVED in the file
(`P_eq_homfly` 667, `homfly_descent` LinkInterfaces.lean:395, `reverse_sign` 1219, `reverse_writhe` 1227,
`rotationNumber_reversal` RotationReversal.lean:55 with `Regular` from `X.generic`, `ClosedC1Curve.rot_reverse`
TurnLift.lean:261).

**(A) — U-A, ≈ 200 lines.** Four fields PROVED (`rfl`, projections). `ua_junction_determined`: `curveMap_on_junction`
(Rounding.lean:1668: `curveMap (a j + s (b j − a j)) = juncArc (A0 j) ε (θu j) (turn j) s` after `G2_arg_b` 1340),
`A0 j = C.P j − ε • uDir C j` (525), `θu C j ≡ arg (uDir C j) (mod 2π)` (`dirOf_θu` 1207 + `G1_dirOf_arg` 1172),
`juncArc` 2π-periodic in `θu` (`dirOf` periodicity, ~30 lines), `principalAngle (uDir) (vDir) = principalTurn` by scale
invariance (`cornerRotor u v = star u * v`, EuclideanPlane.lean:55; `Complex.arg_real_mul`, Mathlib Arg.lean:185; ~40
lines). `ua_length_determined`: `b_sub_a` (1277), `speed = Λ`, `ℓ = juncLen ε (turn C j)` (480/504), `curveMap_b` (1661:
`= A1 j = C.P j + ε • vDir`). `junction_local` corollary: both images equal `junctionTemplate q u v ε '' Icc 0 1`.

**(B) — U-B1/U-B2/U-B3, ≈ 1950 lines** (the printed proof 4366-4416 on the accepted global angle).
- U-B1 `ub_globalLift`: `T t = dirOf (Θ C ε t)` is `normalize_deriv_curveMap` (1785) with `tangentField` (522);
  `Θ = liftAt j` on `Icc (a j) (b j)` is `Θ_on_junction` (1469) (and `= θu (j+1)` on straight parts, `Θ_on_straight` 1480);
  `(Round C D ε h).θ j = liftAt C ε j` and `.Lε.γ = curveMap C ε` are `rfl` on `roundedWitness` (3008).
  `ub_exists_direction`: the forbidden set is `{θu j + nπ}` (finitely many classes mod `π`: `θu (j + k) = θu j + 2π rot`,
  `θu_last` 1223 / `G2_θu_eq` 1281) and, one-dissent, the closed arc `[θu j₋ + ϑ₋, θu j₋]` with its `π`-translates
  (`|ϑ₋| < π`, `turn_bounds` 1155); the complement in a period is an open interval of length `π − |ϑ₋| > 0` minus finitely
  many points (`Set.Infinite.diff`, `Set.Ioo_infinite`).
- U-B2 `ub_levelCount`: partition `[0,1) = ⋃ [a j, b j) ∪ [b j, a (j+1))` (`a_zero`, `a_last`, `a_lt_b`, `b_lt_a`); no
  level `φ + 2πn` on straight parts (`Θ_on_straight` + `hφ`), at junction ends (`liftAt_a` 1714, `liftAt_b` 1717), or in
  the negative junction (`θ_range` + `harc`); in a positive junction `liftAt` is `StrictMonoOn` (1742) and continuous
  (`liftAt_smooth` 1684), each level of `Ioo (θu j) (θu j + ϑ_j)` attained exactly once (`θ_unique`), count
  `⌊x_{j+1}⌋ − ⌊x_j⌋` with `x_j := (θu j − φ)/2π ∉ ℤ` (`Int.card_Ioc`-type counting); telescoping by `G2_θu_eq` to
  `⌊x_0 + rot⌋ − ⌊x_0⌋ = rot` (`θu_last`, `rotationNumber_integer` RotationNumber.lean:45, `Int.floor_add_intCast` Mathlib
  Floor/Ring.lean:182); positivity of `deriv (liftAt j) t`: `G3_hasDerivAt_liftAt` (1761), `deriv_liftAt_ne_zero` (1773),
  monotone ⇒ `0 ≤ deriv` ⇒ `0 <`. Finiteness: finitely many junctions, uniqueness per junction. State the pure-real
  "monotone-on-pieces level counting" lemma separately and probe it on a two-junction example first (A §6.3).
- U-B3: `ub_tangencyCount_of_admissible` from `ub_levelCount` at `φ` and `φ + π` (`dirOf (φ + π) = −dirOf φ`; the
  `φ + π` forbidden set equals the `φ` one since `n` ranges over ℤ), `AdmissibleDirection C u` ⇔ B-CHOICE for any argument
  `φ` of `u` (`dirOf (θu j) = uDir C j` 1207, `dirOf_θu_add_turn` 1212 for the arc), `rot ≥ 1` in both normalised cases
  (`uniform_rotation` UniformRotation.lean:64 (i)/(iii) through `principalTurn_sign` 12), `|rot| = rot`;
  `ub_exists_admissibleDirection` with `u := dirOf φ`. `ub_BClaim` and `cf_thm_carrierfloor_B` PROVED in the file
  (`clearance_pos` 2025, `principalTurn_reversal` RotationReversal.lean:49).

**(C) — sm-3:4417-4575; chain on the FIXED polygon `X` except step 1.**
1. Normalise (in U-C, uses (R)): if `alternative` holds for `reversal C.P`, replace `(C, X)` by `(C.reverse, X.reverse)`:
   `X.reverse.Γ = single C.reverse` (`rfl` after `shadow`), `P` kept (`ur_P_reverse_all`), `writhe` (`reverse_writhe`),
   signs (`reverse_sign` ⇒ positivity), `|rot|` (`rotationNumber_reversal`), `generic := X.reverse.generic`,
   `turn_ne/turn_lt_pi` via `principalTurn_reversal`. WLOG `AllPosOrOneNeg C.P`. ≈ 120 lines.
2. Mirror (U-SW, U-ι, U-EQ): `Xbar := X.switchAll` (`withOver underStrand under_mem`, LinkDiagram.lean:637), same shadow;
   `usw_switchAll_sign` (`det_swap` Chirotope.lean:30 + `SignType.sign_neg`), all signs `−1`, `usw_switchAll_writhe = −w`;
   `usw_carried_switchAll` (τ unchanged, over/under visits exchanged). `usw_P_switchAll : P X.switchAll = ι (P X)`:
   `Q := fun D => ι (P D.switchAll)` is an `RCompetitor` — moves by `usw_switchAllCarries` + `P_planar/P_reidemeister_*`
   + `ι` a ring hom; `circle` (`P_circle`, `map_one`); `skein` from `IsSkeinTriple Dm.switchAll Dp.switchAll D0.switchAll`
   + `P_skein`, apply `ι` (`ι_a`, `ι_aInv`, `ι_z`) and rearrange — the printed "multiplied by −1" (4540-4544); then
   `coefficient_transport Q P` and `ι ∘ ι = id` on the range. `SwitchAllCarriesUnit` (the analogue of `MirrorCarries`,
   LinkMoves.lean:1135, whose accepted proofs 1391-2062 are the template but are about the REFLECTION `Diagram.mirror`
   1379, FR-FL-C4): `Reparam` (370: `over_map/over_surj` need an under-visit version — a lemma that a reparametrisation
   carries the PAIR of visits of a crossing, ~80 lines), `Deform` (462: `deform` keeps `overStrand` by label, so
   `switchAll` commutes by `rfl`/ext), `OutsideMatch.over_eq/under_eq` swap (316), `RIData` (kink of either sign),
   `RIIData.same_over` (599-627: the two disjuncts swap `a' ↔ b'`), `RIIIData` (639-697: relabel `(a,b,c) ↦ (c,b,a)`,
   `xab ↔ xbc`, `top_* ↔ mid_*`; `Separates`/`ArcCover`/`BeforeOn`/end fields are over-data-free), skein triples
   (`Dm = Dp.switch x` ⇒ `Dm.switchAll = Dp.switchAll.switch x` with `x` positive there; `OrientedSmoothingData` 713 with
   `over_on_a/under_on_b` exchanged `a ↔ b`, `a₀ ↔ b₀`; pattern `OutsideMatch.switch` 1926). `ui_mirrorSubstitution`:
   `iotaHom := (AddMonoidAlgebra.lift ℤ R (ℤ×ℤ) (unitPowers (R.aUnit⁻¹) (−R.zUnit))).toRingHom` (`unitPowers`
   LinkLaurentRing.lean:1224, units 168/170), `coeff` from `lift_single`, `degAZ_eq` from `degAZ_eq_of_spec` (465) +
   `mindegAZ_spec` (513), `ne_zero` from `coeff`.
   Fallback if U-SW stalls (recorded, not adopted): `D̄' := X.reverse.mirror` (all negative, `P = ι (P X)` from (R) + the
   accepted `mirrorCarries_linkEquiv` 1837 / `IsSkeinTriple.mirror` 2048); its curve is the reflected reversed polygon, so
   every (B)/(A) transport must be redone on `C.reverse.mirror` (+~700 lines, worse fidelity).
3. Round: `D̄ := PolygonDiagram.ofDiagram Xbar rfl` (Rounding.lean:107; `toDiagram_ofDiagram` 114), (B)'s `u`, `ε₁`
   (`ub_exists_admissibleDirection C`, direction depends on `C` only), `ε := ε₁/2`, `h : Admissible C D̄ ε`,
   `ub_tangencyCount_of_admissible C D̄ …` gives `TangencyCount (Round C D̄ ε h) u |rot|`; `R : ℕ := rot` (`1 ≤ rot`,
   `rotationNumber_integer`); `rot_eq` (the record) if `rot(L_ε)` is needed.
4. Curls (U-CHAIN, `ucurl_exists_curled`): induction over the finite `tangencySet` (`Finset.induction_on` on
   `hcount.1.toFinset`). State after `i` curls, frozen as `structure CurlChainState` in the unit: `(F_i, X_i, RecordCarried
   F_i X_i)`, `P X_i = P D̄`, `X_i.writhe = −w − i`, all signs `−1`, `F_i = L_ε` WITH VELOCITY off the union of the used
   windows `(s₁, s₂)_l ⊆ (a j_l, b j_l)` (`unchanged`, `unchanged_deriv`), `{t ∈ [0,1) ∣ T_i t = u}` = the unused
   tangencies, every double point of `F_i` is a crossing point of `L` or a kink point inside a used `Δ_l ⊆ cornerDisc C ε
   j_l`. Site for the next tangency `t₀ ∈ Ioo (a j) (b j)` (`CrossesPositively`): `CurlSite` (Curl.lean:141) fields from
   the `RoundingWitness` — `embedded` (`junction_embedded`; `F_i = L_ε` on the junction), `no_double` (an occurrence
   parameter in `[a j, b j]` would put a double point of `F_i` in `cornerDisc j`: crossing points excluded by
   `disc_no_double`, kink points by `disc_disjoint` — B's analysis, the delicate field), `lift`/`turns_pos` (`θ_lift`,
   `θ_strict.1`; the junction is positive because `0 < deriv (θ j) t₀` excludes `StrictAntiOn`), `isolated`
   (`direction_once`), `short` (`b j − a j < 1` from the chain `a 0 = 0 < … < a k = 1`); `Δ₀ := cornerDisc C ε j`, `p ∈
   interior Δ₀` (`juncArc_mem_open_disc` 1104 via `curveMap_on_junction`); `cf_lem_curl.exists_curl S Δ₀ _` (Curl.lean:
   309ff, 8366) gives `Δ ⊆ Δ₀`; propagate by `unchanged`, `unchanged_deriv`, `new_in_disc`, `no_u`, `doubles_outside`,
   `one_double`, `old`, `old_sign`, `kink_neg`, `poly_eq`, `writhe_eq`. Distinct tangencies lie in distinct junctions
   (`direction_once`) and the junctions' discs are disjoint (`disc_disjoint`), so windows are disjoint and later sites are
   untouched — the printed "leave one another intact" (4443-4445). First site through `CurlSite.ofCarried` (352) from
   `(Round …).carried`; later sites from the previous `carried'`. After `R` steps no `u`-tangency (`no_u` in each `Δ`,
   `unchanged_deriv` outside; the tangencies of `L_ε` were exactly the `R` points). ≈ 1500 lines.
5. Rotate (U-ROT, `urot_exists_rotated`): `φ` with `rotPlane φ u = downDir` (`u` unit: `u = (cos α, sin α)`, `φ := −π/2 −
   α`); `G.γ := rotPlane φ ∘ F.γ` is a `SmoothRegularLoop` (linear map, `deriv` commutes, `rotPlane` injective);
   `RecordCarried G X` (same `τ`, `det (ρ a) (ρ b) = det a b`, `twin_eval`/`doubles` through injectivity, `order`
   verbatim); `normalize (ρ v) = ρ (normalize v)` (isometry), so `T_G t = downDir ↔ T_F t = u`. ≈ 250 lines.
6. Lift (U-LIFT-1/2/3, `ulift_exists_transverse_lift`; sm-3:4456-4523), on `(x, z) = G.γ`: L1 `v + z′ > 0` (`v ≥ |z′|`,
   equality only at `x′ = 0 ∧ z′ ≤ 0`, excluded by regularity and no-`downDir`); L2 `liftY0` `C^∞` (`ContDiff.deriv'`,
   `ContDiffAt.norm`/`sqrt` with L1) and 1-periodic (`SmoothLoop.deriv_periodic`); L3 `z′ − y₀ x′ = v` (algebra with
   `v² = x′² + z′²`); L4 `circBump` `C^∞` (`Real.smoothTransition.contDiff`, `Real.contDiff_cos`), 1-periodic
   (`Real.cos_add_two_pi`), `= 1` at `s₀` (`smoothTransition.one_of_one_le` Mathlib SmoothTransition.lean:161), `= 0` at
   circle distance `≥ δ` (`zero_of_nonpos` 168 + cosine monotonicity on `[0, π]`), values in `[0,1]`; needs `0 < δ < 1/2`
   (`Int.fract` reduction to `[s₀ − 1/2, s₀ + 1/2)`); L5 `ul_exists_constants` (5 cases on `(x′_O, x′_U)` signs, `det =
   x′_O x′_U (m_U − m_O)` used only when `x′_O < 0 < x′_U`; vertical branches free since `z′ > 0`); L6 `δ` below half
   the minimal circle distance of the finitely many `τ v` (`τ_inj`, `Finset.min'` on `offDiag`) and below each
   admissibility radius (openness of `z′ − c_v x′ > 0`, `Metric.continuousAt_iff`); at most one bump nonzero
   (`Finset.sum_eq_single`); L7 `z′ − y x′ = (1 − b) v + b (z′ − c_v x′) > 0`; L8 `y (τ v) = c_v`; L9 `TransverseKnot`
   fields (TransverseFront.lean:571): `smooth` (`ContDiff.prodMk`), `periodic`, `embedded` (equal points ⇒ equal `xz` ⇒
   `SameT` or a `(τ v, τ (twin v))` pair by `doubles` after `Int.fract` reduction, where `y` takes `c_O ≠ c_U`),
   `positive` (L7 via `HasDerivAt.prodMk` uniqueness), `immersion` (`xzOf T = G.γ` by `funext`), `doubles_finite`
   (image of the finite `Visit` type under `v ↦ (τ v, τ (twin v))`), `transverse`, `no_triple` (`RecordCarried.transverse`,
   `no_triple` Curl.lean:88); L10 the `HeightMarking` (§2.1) and `K.front.writhe = X.writhe`. ≈ 1950 lines.
7. Conclude (U-C): `hbound K X_R hread : K.front.writhe ≤ −degAZ (P X_R) − 1`; `K.front.writhe = X_R.writhe = −w − R`;
   `P X_R = P D̄ = ι (P X)` (`poly_eq` chain, `toDiagram_ofDiagram`, `usw_P_switchAll`); `degAZ (ι (P X)) = −mindegAZ (P X)`
   (`ui_mirrorSubstitution.degAZ_eq`, `P_ne_zero` PolynomialBlock.lean:793); so `1 − w − R ≤ mindegAZ (P X)` in ℤ, cast
   to ℝ with `R = |rot|` (`Int.cast_le`, `abs_of_pos`). `floor_zZero`: `supp (zZeroPart f) ⊆ supp f`
   (`coeffAt_zZeroPart_zero/of_ne`) ⇒ `mindegAZ f ≤ mindegAZ (zZeroPart f)` by `mindegAZ_spec` (513) twice.
   `floor_support` corollary: `mindegAZ_spec.2`. ≈ 550 lines.

**thm:floor — U-F, ≈ 250 lines.** `uf_a_floor_of_C`: `C := carrierPolyComp hn hP S q hS` (LinkPositiveLift.lean:211),
`X := positiveLift hn hP S q hS` (596); `shadow := rfl` (`positiveLift_Γ` 607 = `Shadow.single (carrierPolyComp …)`
definitionally); `positive := positiveLift_isPositive` (618); `turn_ne` from `ccpCornerPolygon_turn_ne_zero`
(CarrierCornerPolygon.lean:579; `S ∈ independentSupports` from `hS`) through `principalTurn_sign` (UniformRotation.lean:12)
and `ccpCornerPolygon_regular` (679) (or `carriers_clause_ii` 822); `alternative` from `CarrierUniformOrOneDissent`:
`turn = 1 ↔ 0 < principalTurn` (`principalTurn_sign`), for the reversed alternative `principalTurn_reversal` + `turn` of
`reversal`; `CarrierFloorCHyp.of_diagram` supplies the rest (the printed remark that lem:carriers gives every geometric
hypothesis "except that no corner lies on a non-incident edge, which holds directly" is `ccpCornerPolygon_tail_off` inside
`carrierShadow_generic` 580). Then `hC.floor` gives `(1 − writhe) − |rot| ≤ mindegAZ (P X)`; `w = m_Q`
(`positiveLift_writhe_eq_carrierCrossingCount` 820), `P = homfly` (`P_eq_homfly` 667) so `P X = cornerHomfly` (`rfl`
after unfolding), `rot Q = carrierRotation` (UniformDefinition.lean:42, `rfl`), `carrierRotationInt_cast`
(CornerStateSum.lean:73), `cornerSlot_cast` (87), `Int.cast_le`. `uf_z_parity`: `P_support` (765) with
`positiveLift_componentCount` (610) and `P_eq_homfly` give `InSupportM 1`; `0 ≤ mindegZZ` from `mindegZZ_spec` (614: a
coefficient at `mindegZZ` is nonzero, so `mindegZZ = 2j ≥ 0` by `P_knot_support` 815). `z_parity` provable NOW.

## 4. Unit decomposition (byte-identical copies of Statements_FINAL.lean; statements frozen; leaves `sorry`; helpers prefixed)

Check per unit: `cd work/lean && lake env lean ../drafts/floor/U_<unit>.lean`. Assembly: concatenate in file order, clash
scan, `#print axioms` (expected [propext, Classical.choice, Quot.sound, SM.lp_lm] for the (R)(A)(B) theorems and
`cf_thm_carrierfloor_of_bound`, plus `SM.lit_homfly` for the thm:floor theorems), port as `SM/CarrierFloor.lean`
(imports SM.Curl, SM.TransverseFront, SM.CeSmoothingRecord, SM.CornerStateSum, SM.LinkPositiveLift, SM.UniformRotation)
after the statement review; §1 of the file is deleted when the contact lane's module provides `spatial`/`Reads`.

> **Note 2026-09-19** (work/port/docdebt patch 10; OPEN_ITEMS_20260916.md §E-19 — the `#print axioms` expectation above is
> STALE): at assembly `cf_thm_carrierfloor_R` and `uf_z_parity` also depend on `SM.lit_homfly` and `SM.lp_lm_uniqueness`
> (`coefficient_transport` on `lp_lm_uniqueness`; the frozen `knot_reverse` proof on `lit_homfly`; AUTHOR_NOTES L5602-5605), and
> the ACCEPTED rows 99 `cf:thm-carrierfloor` and 100 `thm:floor` carry the full nine-axiom set (std + H + HD + LM + LMU + NG + SC,
> through row 94 fd:contact; FINAL_REVIEW.md §4.3). The table below is the 2026-09-15 plan as written.

| unit | prefix | leaves (Statements_FINAL.lean §8) | lines | hours | deps | wave |
|---|---|---|---|---|---|---|
| U-R | `ur_` | `ur_P_reverse_all` | 250 | 3 | accepted only | 1 |
| U-A | `ua_` | `ua_junction_determined`, `ua_length_determined`, `CarrierFloorAData.junction_local` | 200 | 3 | Rounding internals | 1 |
| U-B1 | `ub1_` | `ub_globalLift`, `ub_exists_direction` | 600 | 7 | Rounding internals, `turn_bounds` | 1 |
| U-B2 | `ub2_` | `ub_levelCount` (+ the pure-real level-counting lemma) | 900 | 10 | B1 statements | 1 |
| U-B3 | `ub3_` | `ub_tangencyCount_of_admissible`, `ub_exists_admissibleDirection` | 450 | 5 | B1, B2 | 2 |
| U-ι | `ui_` | `ui_mirrorSubstitution` | 300 | 4 | Laurent ring | 1 |
| U-SW | `usw_` | `usw_switchAll_sign`, `usw_switchAll_writhe`, `usw_carried_switchAll`, `usw_switchAllCarries` | 550 | 7 | LinkMoves | 1 |
| U-EQ | `ueq_` | `usw_P_switchAll` | 100 | 1 | ι, SW | 2 |
| U-CHAIN | `ucurl_` | `ucurl_exists_curled` (`CurlChainState`, one-step lemma, `Finset` induction) | 1500 | 18 | `cf_lem_curl`, Rounding fields | 1 (critical path) |
| U-ROT | `urot_` | `urot_exists_rotated` | 250 | 3 | Curl (`RecordCarried`) | 1 |
| U-LIFT-1 | `ul1_` | L1-L4 helpers (`liftY0` smooth/periodic, (*), `circBump` facts) — no leaf of its own; exports helper lemmas | 500 | 6 | Mathlib | 1 |
| U-LIFT-2 | `ul2_` | `ul_exists_constants` + L6-L8 helpers | 550 | 6 | L1 statements | 1 |
| U-LIFT-3 | `ul3_` | `ulift_exists_transverse_lift` (L9 `TransverseKnot` fields, L10 `HeightMarking` + front writhe) | 900 | 10 | L1, L2 | 2 |
| U-C | `uc_` | `cf_thm_carrierfloor_C_of_bound`, `CarrierFloorCData.floor_support` | 550 | 6 | all unit statements | 2 |
| U-F | `uf_` | `uf_a_floor_of_C`, `uf_z_parity` | 250 | 3 | def:C, lp:core | 1 |
| total | | 23 leaves | **≈ 7850 (say 8000)** | ≈ 92 prover-h; 2 waves + assembly; ~14-18 h wall with 8 provers | | |

Critical path: U-CHAIN (1500) ‖ U-B2 (900) → U-B3; U-LIFT-1/2 → U-LIFT-3; then U-C. First units to launch (wave 1, all
against the frozen statements): U-CHAIN, U-B2, U-B1, U-LIFT-1, U-LIFT-2, U-SW, U-ι, U-R, U-A, U-ROT, U-F (`uf_z_parity`
first — provable now and cheap). (R), (A), (B) and `thm_floor_z_parity` can be mapped as clause theorems after their own
review; the row theorems stay unmapped until row 94 lands (D-F11/D-F14 pattern).

## 5. Fidelity risks FR-FL-* — the executor writes these into AUTHOR_NOTES BEFORE the rows are stated

FR-FL-R1 (knot vs link). `P_reverse` is stated for knot diagrams as printed; the printed proof proves it on all oriented
link diagrams, so the library lemma `ur_P_reverse_all` is unconditional and the row field its restriction.
FR-FL-R2 ("the same polynomial"). The knot is the `LinkEquiv` class (D2); "its reverse" is presented by `X'.reverse` for
any diagram `X'` of the knot; nothing spatial is asserted.
FR-FL-R3 (smooth diagram). The scoping sentence's smooth case is the accepted curve identity `ClosedC1Curve.rot_reverse`;
the reversal of a CARRIED smooth diagram is not a field (no consumer reads it; (B)/(C) normalise at polygon level). The
polygonal field also asserts `X.reverse.Γ = Shadow.single C.reverse` (definitional).
FR-FL-A1 (junction template). `junction_determined` fixes the PARAMETRISATION on `[a j, b j]` (stronger than image
equality); true of the construction (`curveMap_on_junction`); B's image form is the corollary `junction_local`.
FR-FL-A2 ("one record"). `Round` is a definition; no uniqueness among all smoothings is claimed (4362-4364); other
`RoundingWitness`es exist.
FR-FL-B1 (normalised orientation). For an all-negative `L` the tangent crosses `u` in the NEGATIVE sense, so the literal
claim for `Round(L, D, ε)` is false in the reversed alternative; the printed proof "perform[s] the allowed normalization
once" (4368-4370). `tangencies` asserts `BClaim` for the normalised polygon (`C` or `C.reverse` with `D.reverse`).
`Round(−L, −D, ε) = reverse (Round(L, D, ε))` is NOT proved (would need the profile symmetry through the construction).
FR-FL-B2 ("points"). Parameters of the fundamental period, `Set.ncard` with an explicit `Set.Finite` conjunct (the
`ncard` of an infinite set is `0`); parameters ↔ points since every `u`-tangency lies in a junction, the curve is
injective there (`junction_embedded`) and distinct junctions lie in disjoint discs (`disc_disjoint`).
FR-FL-B3 ("crosses in the positive sense"). Positive derivative of the accepted junction lift `W.θ j` at the parameter
(the printed proof's "positive angular derivative", 4394-4396).
FR-FL-B4. `ε₁ ≤ clearance C` added so the record exists at every `ε ∈ (0, ε₁)` (the proof takes `ε₁ = ε₀(L)`); the
admissibility proof is quantified (`∀ h`), irrelevant by `one_record`.
FR-FL-B5. "nonzero edges" is inside `Regular` (`D.regular`), "finitely many double points" inside `Generic.transverse`
(finitely many edge pairs) — as in the accepted cf:lem-rounding row.
FR-FL-C1 (redundant hypotheses kept). `turn_exists`, `turn_lt_pi`, `generic` are printed hypotheses ("stated here so
that no generic parent polygon is assumed") and are fields; consumers use `CarrierFloorCHyp.of_diagram`.
FR-FL-C2. `R` real as printed; `mindegAZ` is def:adeg's `mindeg_a` because `P X ≠ 0` (lp:core).
FR-FL-C3 (`f_D`). `zZeroPart f` is `[z⁰]P_D` read inside `R` so that `mindeg_a` applies; the row field is literal; the
coefficient/support form is the corollary `floor_support`.
FR-FL-C4 (the mirror `D̄`). The printed `D̄` is the CROSSING SWITCH (sm-3:4431, 4533), not the accepted reflection
`Diagram.mirror`; the proof route builds `Diagram.switchAll` and a NEW move transport `SwitchAllCarriesUnit`; the
statement is unaffected; the reflection route is the recorded fallback.
FR-FL-C5. The parenthesis "which by clause (R) changes neither P_D, nor the crossings and their signs, nor w, nor R" is a
proof remark, consumed in the route's step 1, not a field.
FR-FL-C6 (rotation). "Rotate coordinates so that u is the downward vertical" is applied to the SMOOTH curve only; the
polygon `X` is not moved. Legitimate because the record row 94 consumes (`HeightMarking`) and the curl lane's
`RecordCarried` are record-level (no point-coincidence clause) — confirmed on the accepted `HeightMarking`.
FR-FL-C7 (proof devices). A closed-form periodic bump (`circBump`, via `Real.smoothTransition ∘ cos`) replaces the printed
piecewise `φ`-bump; the printed "at a crossing branch there is no vertical tangency" is not needed (vertical branches
have `z′ > 0` and impose no constraint; the accepted curl witness does not export it).
FR-FL-C8 (the lift's front reads `T`) — NEW. "Its front and its smaller-y over/under assignments are exactly the diagram
T" (4520-4522) is rendered as `K.Reads X_R`: a `HeightMarking` of `K.spatial.projLoop` reading the curled polygon `X_R`
(occurrences ↔ visits, cyclic order, pairing, over = smaller `y`, signs); "exactly" = record isomorphism (rp:record-
polynomial), not point coincidence. The gap2 memo's `SmoothKnotDiagram.Carries` is dropped, following the contact lane.
FR-FL-C9 (row 94 as hypothesis) — NEW. fd:contact enters as the explicit `TransverseFrontBound` (the sl-free composite
of its two displays on the `Reads` reading), derived from the contact lane's `FdContactData` shape by
`transverseFrontBound_of_fdContactShape`; rows 99(C) and 100 stay conditional (`_of_bound`) until row 94 is accepted;
the row theorems are declared and mapped only then (D-F11/D-F14).
FR-FL-F1. thm:floor's "after possibly reversing its orientation either all turns are left, or exactly one turn is right"
is the literal reversal form `AllLeftOrOneRight Q ∨ AllLeftOrOneRight (reversal Q)`; equivalent to the memo's 4-way form
since carrier turns are nonzero (lem:carriers (ii)).
FR-FL-F2. "turns" = `turn` (def:chirotope) at every corner of the corner polygon `ccpCornerPolygon` (original vertices and
smoothing corners alike).
FR-FL-F3. `z_parity` has no turn hypothesis (the printed sentence has none; it is lp:core's knot clause); `ℤ[a^{±1}, z²]`
is the accepted `InSupportM 1` (`M_1`); "so mindeg_z ≥ 0" is the second conjunct.

## 6. Accepted declarations used (grep-verified 2026-09-15 in work/lean)

SM/Rounding.lean: `PolygonDiagram` 80, `ofDiagram` 107, `toDiagram_ofDiagram` 114, `cornerDisc` 129, `polygonImage` 140,
`SmoothRegularLoop` 148, `Carried` 183, `RoundingWitness` 231 (fields `θ_lift θ_strict θ_unique θ_range direction_once
immersion junction_embedded disc_disjoint disc_no_double disc_center same_strands rot_eq same_writhe outside straight
a_zero a_last a_lt_b b_lt_a`), `dirOf` 466, `juncLen` 480, `juncArc` 483, `uDir` 489, `vDir` 491, `turn` 493, `θu` 497,
`Θ` 516, `tangentField` 522, `A0` 525, `curveMap` 530, `liftAt` 534, `clearance` 571, `Admissible` 585,
`juncArc_mem_open_disc` 1104, `turn_bounds` 1155, `G1_dirOf_arg` 1172, `dirOf_θu` 1207, `dirOf_θu_add_turn` 1212,
`θu_last` 1223, `b_sub_a` 1277, `G2_θu_eq` 1281, `G2_sum_turn` 1289, `G2_arg_b` 1340, `Θ_add_one` 1462, `Θ_on_junction`
1469, `Θ_on_straight` 1480, `curveMap_b` 1661, `curveMap_on_junction` 1668, `liftAt_smooth` 1684, `liftAt_a` 1714,
`liftAt_b` 1717, `liftAt_strictMonoOn` 1742, `liftAt_strictAntiOn` 1751, `G3_hasDerivAt_liftAt` 1761,
`deriv_liftAt_ne_zero` 1773, `normalize_deriv_curveMap` 1785, `tangent_injOn_junction` 1820, `clearance_pos` 2025,
`roundedLoop` 2948, `rot_roundedCurve` 2970, `roundedWitness` 3008, `cf_lem_rounding` 3131.
SM/Curl.lean: `RecordCarried` 52 (`no_triple` 88, `doublePoints_eq`), `Carried.toRecordCarried` 118, `CurlSite` 141,
`CurlWitness` 203, `CurlData` 309 (`exists_curl`), `CurlSite.ofCarried` 352, `cf_lem_curl` 8366.
SM/TransverseFront.lean: `xzOf` 109, `SmoothKnotDiagram` 189, `IsDouble` 230, `crossSign` 278, `crossSign_eq_sign` 299,
`crossingPairs` 350, `crossingPairs_xor_swap` 381, `writhe` 389, `TransverseKnot` 571, `deriv_xz` 633, `vertical_up`
668, `deriv_T_ne_zero` ~690, `IsDouble`/`y_ne_of_isDouble` 716ff, `IsOver`, `front` 738.
SM/CeSmoothingRecord.lean: `SpatialLink` 141, `projLoop` 157, `height` 167, `RegularGenericProjection` 204,
`HeightMarking` 219. SM/FrontRecordBridge.lean: `IsDoubleOf` 97, `occSetOf` 105, `crossSignOf` 118;
SM/FrontGeomModel.lean: `SmoothFront.OccOf` 76.
SM/LinkDiagram.lean: `Diagram` 490, `underStrand` 505, `under_mem` 507, `IsPositive` 547, `sign` 552, `writhe` 577,
`componentCount` 580, `withOver` 637, `switch` 650, `switch_sign_self` 688, `reverseCrossingEquiv` 1199, `reverse` 1213,
`reverse_sign` 1219, `reverse_writhe` 1227, `mirror` 1379 (NOT used in the route), `Shadow.single` 1589.
SM/LinkDiagramRecord.lean: `compOf` 164, `visitCoord` 181, `twin` 413, `twin_ne` 420, `overBit` 470.
SM/LinkMoves.lean: `OutsideMatch` 316, `ReparamData` 370, `DeformData` 462, `PlanarIsotopic` 516, `RIData` 569, `RIIData`
599, `RIIIData` 639, `OrientedSmoothingData` 713, `IsSkeinTriple` 751, `LinkEquiv` 760, `MirrorCarries` 1135,
`ReverseCarries` 1139, `reverseCarries_planarIsotopic` 2459, `reverseCarries_RI/RII/RIII` 3071/3117/3231,
`reverseCarries_linkEquiv` 3238, `IsSkeinTriple.reverse` 3318, `reverse_skein` 3328; templates `mirrorCarries_*`
1391-1837, `OutsideMatch.switch` 1926, `IsSkeinTriple.mirror` 2048.
SM/CoefficientTransport.lean: `RCompetitor` 23, `coefficient_transport` 137. SM/PolynomialBlock.lean: `P_planar` 604,
`P_reidemeister_I/II/III` 605-607, `P_circle` 609, `P_skein` 638, `P_rcompetitor` 648, `P_eq_homfly` 667, `P_support`
765, `P_ne_zero` 793, `P_knot_support` 815. SM/LinkInterfaces.lean: `homfly_descent` 395.
SM/LinkLaurentRing.lean: `R.a/z/aInv` 159-165, `R.aUnit/zUnit` 168/170, `coeffAt` 286, `degAZ` 446, `degAZ_spec` 455,
`degAZ_eq_of_spec` 465, `mindegAZ` 506, `mindegAZ_spec` 513, `mindegZZ` 607, `mindegZZ_spec` 614, `InSupportM` 846,
`unitPowers` 1224.
SM/CornerStateSum.lean: `carrierRotationInt` 61, `carrierRotationInt_cast` 73, `cornerSlot` 82, `cornerSlot_cast` 87,
`cornerHomfly` 96. SM/UniformDefinition.lean: `CarrierUniform` 27, `carrierRotation` 42. SM/CarrierCrossings.lean:
`carrierCrossingCount` 62. SM/LinkPositiveLift.lean: `carrierPolyComp` 211, `carrierShadow_generic` 580, `positiveLift`
596, `positiveLift_Γ` 607, `positiveLift_componentCount` 610, `positiveLift_isPositive` 618,
`positiveLift_writhe_eq_carrierCrossingCount` 820. SM/CarrierCornerPolygon.lean: `ccpCornerPolygon` 357,
`ccpCornerPolygon_turn_ne_zero` 579, `ccpCornerPolygon_regular` 679, `carriers_clause_ii` 822.
SM/UniformRotation.lean: `principalTurn_sign` 12, `uniform_rotation` 64. SM/RotationReversal.lean:
`principalTurn_reversal` 49, `rotationNumber_reversal` 55. SM/RotationNumber.lean: `rotationNumber_integer` 45.
SM/Chirotope.lean: `turn` 13, `det_swap` 30. SM/RegularLocus.lean: `Regular` 12, `principalTurn` 15.
SM/RegularPairs.lean: `principalAngle` 54, `principalAngle_bounds` 56. SM/EuclideanPlane.lean: `cornerRotor` 55.
SM/TurningNumber.lean: `normalize` 226, `ClosedC1Curve` 241, `rot` 274. SM/TurnLift.lean: `ClosedC1Curve.reverse` 237,
`rot_reverse` 261.
Mathlib: `Complex.arg_real_mul` (Arg.lean:185), `Int.floor_add_intCast` (Floor/Ring.lean:182),
`Real.smoothTransition.one_of_one_le` / `zero_of_nonpos` (SmoothTransition.lean:161/168), `Finset.sum_eq_single`.

## 7. Reporting shape and FINAL_REVIEW sentences

Until row 94: `CarrierFloorRData/AData/BData` proved and reviewed as library theorems (`cf_thm_carrierfloor_R/_A/_B`);
`CarrierFloorCData`, `FloorTheoremData` stated; `cf_thm_carrierfloor_C_of_bound`, `cf_thm_carrierfloor_of_bound`,
`thm_floor_of_C`, `thm_floor_of_bound`, `uf_z_parity` proved; rows 99/100 UNMAPPED (the map's declarations are row
theorems; a row theorem with a hypothesis is not the row, D-F11/D-F13). When 94 lands:
`cf_thm_carrierfloor := cf_thm_carrierfloor_of_bound (transverseFrontBound_of_fdContactShape ⟨…⟩)`,
`thm_floor := thm_floor_of_C cf_thm_carrierfloor.clauseC`; map, review, accept.

FINAL_REVIEW (proposed): "Row 99 cf:thm-carrierfloor: stated as `SM.CarrierFloorData` (clauses
`CarrierFloorRData/AData/BData/CData`, one field per printed clause) on the accepted rounding record `SM.Round :=
CornerRounding.roundedWitness`; (R), (A), (B) proved as library theorems; (C) proved conditionally as
`cf_thm_carrierfloor_C_of_bound` from the row-94 writhe bound `TransverseFrontBound` (fd:contact's two displays on the
accepted `HeightMarking` reading of the transverse knot's front), via cf:lem-curl, the crossing-switch identity
`P_{D̄} = ι(P_D)` and the transverse lift; readings FR-FL-R1…F3." "Row 100 thm:floor: stated as `SM.FloorTheoremData`;
`z_parity` proved (lp:core knot support); `a_floor` from clause (C) on the positive lift (`thm_floor_of_C`); assembled
once row 94 lands."

## 8. Blocking risks (ranked)

1. Row 94 (contact lane) — the ONLY unconditional blocker: `cf_thm_carrierfloor` and `thm_floor` cannot be declared
   before `SM.FdContactData` exists; the interface here is aligned with BOTH contact designs, but if the judged contact
   FINAL changes the reading relation or `spatial`, §1 of the statements and the output clause of
   `ulift_exists_transverse_lift` move with it (the rest of the lane is untouched). Confirm with the contact judge before
   U-LIFT-3 starts.
2. U-CHAIN (1500 lines): the `no_double` field of later sites and the disjoint-window invariant; mitigate by freezing
   `CurlChainState` and probing the one-step lemma for truth before proving.
3. U-B2 level counting (900 lines): non-integer floor endpoints, telescoping; mitigate by the separate pure-real lemma.
4. U-LIFT-1/2 bump support and `δ` choice (circle distance vs cosine monotonicity); mitigate by `Int.fract` reduction and
   `δ < 1/4`.
5. U-SW (550 lines): the `Reparam` under-visit lemma and the `RIIIData` relabelling — new transport on the moves layer;
   fallback `X.reverse.mirror` recorded (+700 lines, worse fidelity).
6. Reviewer acceptance of FR-FL-B1 (clause (B) on the normalised orientation), FR-FL-C4 (switch, not reflection),
   FR-FL-C8 (front "exactly the diagram T" as a record-level `HeightMarking`).
