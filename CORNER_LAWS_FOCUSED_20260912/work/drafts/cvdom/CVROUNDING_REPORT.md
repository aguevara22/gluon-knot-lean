# Row 152 — CV:lem:rounding — report

File: `work/drafts/cvdom/CVRounding.lean` (439 lines). Main declaration `CV.rounding : CV.CVRoundingData`
(Prop bundle, one field per printed sentence / clause; name per DECISION_FINAL.md §3 R3, `CV.<label>` for
PROVE rows).

Compiled 2026-09-14 05:32 UTC / 01:32am ET with `cd work/lean && lake env lean ../drafts/cvdom/CVRounding.lean`:
exit 0, 0 errors, 0 warnings, no incomplete proofs, no new axioms. `#print axioms` on a /tmp copy, for
`CV.rounding`, `CV.rounding_of_diagram`, `CV.exists_witness_of_lt_clearance`, `CV.roundingRecord`,
`CV.clearance_pos`, `CV.single_generic_of_diagrammatic`, `CV.Diagrammatic.regular`,
`CV.crossingPoints_eq_selfIntersections`, `CV.rotCurve_eq_rot`, `CV.doublePoints_eq_selfIntersections`,
`CV.OverUnder.toDiagram_ofDiagram`, `CV.OverUnder.toPolygonDiagram_ofPolygonDiagram`: each
`[propext, Classical.choice, Quot.sound]`. No clause mentions HOMFLY, so `SM.lit_homfly` does not appear.
Imports: `SM.Rounding` (the SM row, built by the executor at 05:12 UTC / 01:12am ET — before that the file
was checked with `SM.Rounding` compiled to a /tmp overlay olean, the U5a/U0 pattern, same result),
`SM.LinkPositiveLift` (`Shadow.single_generic_of`), `CV.TurnLift` (→ `CV.RotationSmooth`, `CV.Rotation`,
`CV.Setup`: `rotCurve`, `rot`, `rot_eq_rotationNumber`, `Regular.three_le`), `CV.CarrierBridges`
(→ `CV.Events`, `SM.GeoCarrierGeometry`: `crossingPoint_mem_selfIntersections`,
`exists_crossing_of_selfIntersection`, `CarrierGeometry.ofDiagrammatic`, `CarrierGeometry.regular`).
Nothing written under work/lean; `lake build` not run.

Sources. CV: reference/R/CV/d3_floor.tex, `lem:rounding`, statement 31–93, proof 94–261 (clearance display
230–236, positivity 241–247, (e) concluded 251, (a)/(c) 255, (d) 255–260). SM: reference/SM/sm-3-statesum.tex,
`cf:lem-rounding`, statement 3644–3693 (`\status` 3693), proof 3694–3868 (clearance 3843, positivity
3848, (e) 3858, (a)/(c) 3862). SM row: `SM.cf_lem_rounding : SM.RoundingData`, work/lean/SM/Rounding.lean
(3153 lines; fixed statement work/drafts/rounding/Rounding_statement_FINAL.lean; plan
work/drafts/rounding/PLAN_FINAL.md §1, §6).

## 1. Clause → field map (tex lines of BOTH papers)

| CV d3_floor.tex | SM sm-3 | printed sentence / clause | Lean (field of `CV.CVRoundingData`, or binder) | proof |
|---|---|---|---|---|
| 32 | 3645–3646 | "Here rot is as in Definition def:rot." (SM: "Lemma lem:rot for polygons and Definition cf:def-turning for closed C¹ regular curves") | not a clause; fixes the reading of (d): `CV.rotCurve` (= `SM.ClosedC1Curve.rot`, decision F6, CV/RotationSmooth.lean:62) for `L_ε`, the `ε_i` ray formula `CV.rot L hreg : ℤ` (CV/Rotation.lean:138) for `L` | — |
| 33–35 | 3647–3649 | "Let L be a closed polygon with corners q₁,…,q_c, and let D be an oriented diagram whose underlying plane curve is L — L together with an over/under assignment at each of its double points." | binder `{n : ℕ} [NeZero n] (L : LabelledTuple n)`; `D : OverUnder (polyComp L hreg)` = `overStrand : (Shadow.single C).Crossing → (Shadow.single C).Strand`, `over_mem` (file §1); `polyComp L hreg : PolyComp := ⟨n, hreg.three_le, L⟩` | `crossingPoints_eq_selfIntersections`: the crossings of `Shadow.single (polyComp L hreg)` are CV's double points `selfIntersections L` |
| 35–38 | 3649–3652 | "Assume the principal turns of L all exist and are nonzero; that L has finitely many double points, all transversal, none of them a corner; and that no corner of L lies on an edge of L other than the two incident to it." | `hreg : Regular L` (CV:def:regular (B)), `hturn : ∀ i, principalTurn L i ≠ 0`, `hL : Diagrammatic L` (CV:def:diagrammatic, d1_setup.tex:316–320 = exactly the printed list) | `single_generic_of_diagrammatic hL hreg : (Shadow.single (polyComp L hreg)).Generic` — SM's input hypothesis |
| 38–41 | 3652–3656 | "Then there is a clearance ε₀(L) > 0 such that for every ε ∈ (0, ε₀(L)) there is a C^∞ regular closed plane curve L_ε, and a diagram D_ε carried by it, with these properties." | `exists_clearance : ∀ {n} [NeZero n] (L) (hL) (hreg), (∀ i, principalTurn L i ≠ 0) → ∃ ε₀, 0 < ε₀ ∧ ∀ (D : OverUnder (polyComp L hreg)) ε, 0 < ε → ε < ε₀ → Nonempty (RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε)` | `⟨clearance L hreg, clearance_pos hL hreg, fun D _ hε hε₀ => ⟨roundingRecord hL hreg hturn D hε hε₀⟩⟩` — the named construction `SM.CornerRounding.clearance` / `roundedWitness` (SM/Rounding.lean:571, 3008) through `roundingAdmissible` |
| 39–40 | 3654–3655 | "a C^∞ regular closed plane curve L_ε, and a diagram D_ε carried by it" | `smooth_regular_carried`: `ContDiff ℝ ∞ W.Lε.γ ∧ Periodic W.Lε.γ 1 ∧ (∀ t, deriv W.Lε.γ t ≠ 0) ∧ Nonempty (Carried W.Lε (D.toPolygonDiagram hL).toDiagram)` | `SM.cf_lem_rounding.smooth_regular_carried` on the bridge |
| 41–43 | — | "The clearance is part of the conclusion and is quantified here …" | reading, no field: the bundle's existence field is the ∃-form; the printed value is exported separately as `CV.clearance` (§2 of the file) | — |
| 45–55 | — | "The hypothesis names a curve and a diagram … It does not name a generic parent polygon …" | reading, no field: both `L` and `D` are bound; the hypothesis class is `Diagrammatic` (not `CV.Generic`), no parent polygon anywhere | — |
| 57–58 | 3657–3658 | (a) "L_ε coincides with L outside the union of the discs of radius ε about the corners." | `a`: `(∀ p ∉ ⋃ i, cornerDisc (polyComp L hreg) ε i, p ∈ range W.Lε.γ ↔ p ∈ ⋃ i : ZMod n, edgeSegment L i) ∧ ∀ j < n, ∀ t ∈ Icc (W.b j) (W.a (j+1)), W.Lε.γ t = W.Lε.γ (W.b j) + (W.speed * (t − W.b j)) • normalize (edge L j)` | `SM.cf_lem_rounding.a` (fields `outside`, `straight` of `RoundingWitness`); `polygonImage` unfolds to CV's `⋃ edgeSegment L i` |
| 59–66 (+68–79) | 3659–3666 (+3668–3679) | (b) strictly monotone unit tangent from δ_{i−1}/\|δ_{i−1}\| to δ_i/\|δ_i\|, arc exactly \|τ_i\|, each direction once; immersion on the open junction, all derivatives vanish at the ends | `b` (17 conjuncts, SM's field list verbatim with `principalTurn L j`, `edge L j`): junction `[W.a j, W.b j]` inside the disc, `θ j` C^∞ lift (`IsLiftOn W.T`), constant speed, `W.T (a j) = normalize (edge L (j−1))`, `W.T (b j) = normalize (edge L j)`, increment `= principalTurn L j`, range in `uIcc`, `StrictMonoOn`/`StrictAntiOn` by the sign, `∃!` parameter per angle, `InjOn W.T`, `deriv (θ j) t ≠ 0` on `Ioo`, `iteratedDeriv m (θ j) = 0` (m ≥ 1) and `iteratedDeriv m W.Lε.γ = 0` (m ≥ 2) at both ends, `θ j` constant on the two half-lines | `SM.cf_lem_rounding.b`; `CV.principalTurn = SM.principalTurn` is `rfl` (`principalTurn_eq_sm`) |
| 80–82 | 3680–3682 | (c) "L_ε has the same double points as L, with the same strands, the same over/under assignment and hence the same crossing signs and the same writhe." | `c`: `doublePoints W.Lε.γ = selfIntersections L ∧ (∀ v, W.carried.τ v ∈ Ioo (W.b (label v)) (W.a (label v + 1)) ∧ ∃ r > 0, deriv W.Lε.γ (W.carried.τ v) = r • edge L (label v)) ∧ (D.toPolygonDiagram hL).overStrand = D.overStrand ∧ (∀ x, W.carried.smoothSign x = D'.toDiagram.sign x) ∧ W.carried.smoothWrithe = D'.toDiagram.writhe` | `doublePoints_eq_selfIntersections W` (= `W.same_double_points` + `crossingPoints_eq_selfIntersections`), `W.same_strands`, `W.same_strand_dir`, `rfl`, `W.same_signs`, `W.same_writhe` |
| 83 | 3683 | (d) "rot(L_ε) = rot(L)." | `d` (`[NeZero n]`): `rotCurve W.curve = (rot L hreg : ℝ)` | `rotCurve_eq_rot W` = `W.rot_eq` (right-hand side SM's `rotationNumber`) rewritten by the accepted `CV.rot_eq_rotationNumber hreg` (decision F2) |
| 84–91 | 3684–3692 | (e) pairwise disjoint closed discs D_i about the corners; no non-incident edge, no double point, incident edges met exactly in the two ε-sub-segments, the whole modification inside; "a disc meeting the diagram in one embedded arc" | `e` (11 conjuncts, SM's list with `L i`, `edgeSegment L j`, `i : ZMod n`): `IsDisc`, `Disjoint`, `L i ∈ interior`, `Disjoint (cornerDisc …) (edgeSegment L j)` for `¬ incident i j`, crossing points outside, `∩ edgeSegment L i = subsegOut`, `∩ edgeSegment L (i−1) = subsegIn`, junction inside disc `j`, "only the junction is inside", `InjOn W.Lε.γ` on the junction, open straight parts outside every disc | `SM.cf_lem_rounding.e` |
| 230–247 (proof) | 3843–3856 (proof) | `ε₀(L) = ⅓ min{…}`, "Every listed quantity is positive" | `CV.clearance L hreg := CornerRounding.clearance (polyComp L hreg)`; `CV.clearance_pos hL hreg` | `CornerRounding.clearance_pos (single_generic_of_diagrammatic hL hreg)` |
| thm:carrierfloor (A) 745–760 | cf:thm-carrierfloor (A) | "Round(L, D, ε) = (L_ε, D_ε)", the record of the fixed construction | `CV.roundingRecord hL hreg hturn D hε hε₀ : RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε`; `roundingRecord_eq` (= `CornerRounding.roundedWitness _`), `roundingRecord_Lε` (its curve is `CornerRounding.roundedLoop _`), `exists_witness_of_lt_clearance` ("Take ε₁ = ε₀(L)", (B)) | `rfl` |
| thm:carrierfloor (C) 776–786 | cf:thm-carrierfloor (C) | input "an oriented knot diagram … whose underlying plane curve is a closed polygon L" | `OverUnder.ofDiagram C D hD` for `D : Diagram`, `hD : D.Γ = Shadow.single C`; `OverUnder.toDiagram_ofDiagram`: the carried diagram is `D`; `rounding_of_diagram` (the existence sentence in that form) | `PolygonDiagram.ofDiagram`, `toDiagram_ofDiagram` (SM row) |

## 2. CV versus SM, clause by clause (design task (1))

Hypotheses (CV 33–38 / SM 3647–3652): word for word the same — a closed polygon with corners, an oriented
diagram on it (an over/under assignment at each double point), principal turns existing and nonzero,
finitely many transverse double points none a corner, no corner on a non-incident edge. Clauses (a)–(e)
(CV 57–91 / SM 3657–3692): word for word the same, `τ_i` (CV) for `ϑ_i` (SM). Exactly three differences:

1. Scoping sentence (CV 32 / SM 3645–3646). CV: one Definition def:rot for polygons (the `ε_i` ray formula,
   d1_setup.tex:734–739) and for closed C¹ regular curves (`rot(γ) = tw(T_γ)`, 775–780). SM: Lemma lem:rot
   (`rotationNumber = Σϑ_i/2π`) for polygons, Definition cf:def-turning for curves. The curve notion is the
   same definition under two names (decision F6, `CV.rotCurve γ = γ.rot` by `rfl`); the polygon notions
   agree only as a theorem (`CV.rot_eq_rotationNumber`, decision F2). Hence (d) is stated as
   `rotCurve W.curve = (rot L hreg : ℝ)` and proved from SM's `rot_eq` by that theorem — no identification.
2. Two commentary paragraphs in CV only (41–43, 45–55). Rendered as readings: the bundle's existence field
   is the printed ∃-form (the clearance is quantified in the conclusion); the row binds both `L` and `D`
   (clause (c) reads `D`'s over/under assignment, signs and writhe); no generic parent polygon is assumed —
   the hypothesis class is `CV.Diagrammatic` (thm:carrierfloor (B), d3:762, names exactly this class), not
   `CV.Generic`; the peer's polygon `((0,0),(1,0),(−2,−2),(2,0),(−2,1))` of 50–52 is in scope.
3. The polygon's printed domain. CV: `L : LabelledTuple n` (def:polygon), CV:def:regular, CV:def:diagrammatic.
   SM: `C : PolyComp` with `(Shadow.single C).Generic` (`regular`, `tail_off`, `transverse`, `no_triple`).
   The bridge is §3 below.

SM's `RoundingWitness` exports strictly more than printed (constant speed, parametric straight form,
occurrence parameters on the open straight intervals, curve-level flatness of order ≥ 2, "junction = all of
the curve in the disc", embeddedness; PLAN_FINAL.md FR-R3). CV's fields inherit exactly these extras, in the
same conjuncts, so the two rows are comparable field by field.

## 3. The bridge used (design task (2))

* `CV.polyComp L hreg : PolyComp := ⟨n, hreg.three_le, L⟩` — the SM one-component polygon object of CV's
  labelled polygon (`k = n`, `P = L`, both `rfl`). `n ≥ 3` (CV:def:polygon) comes from `CV.Regular.three_le`
  under the accepted CV binder `[NeZero n]` (CV.Setup, CV.Rotation, CV:lem:uniformrot); no `hn` hypothesis
  is added (DECISION_FINAL.md R5). This is the coercion that the accepted `CV.curveOf` (CV/FullTwist.lean:91)
  performs in the other direction (a one-component `Diagram` → its polygon).
* `CV.single_generic_of_diagrammatic hL hreg : (Shadow.single (polyComp L hreg)).Generic` — the accepted
  label-level criterion `Shadow.single_generic_of` (SM/LinkPositiveLift.lean:160) fed with: `regular` from
  `hreg` via `regular_iff_sm`; `tail_off` = the last clause of `Diagrammatic` ("no vertex on a non-incident
  edge"); `transverse` = clause 2 of the accepted `Diagrammatic.crossingGeometry` (CV/Setup.lean:1566;
  `remote` is `¬ adjacent` by definition); `no_triple` = its clause 3 (`G2`). No carrier machinery
  (GeoCornerPolygon / GeoPositiveLift) is involved: those bridge a *carrier's corner polygon*; here `L` is the
  polygon itself, and the same `Shadow.single` object is what those modules also produce
  (`geoCarrierShadow_generic` is `single_generic_of` on the corner polygon).
* `CV.Diagrammatic.regular (hn) (hL) : Regular L` — tier 1 (`CarrierGeometry.ofDiagrammatic`, CV/CarrierBridges.lean)
  plus the accepted `CarrierGeometry.regular`: the "turns exist" hypothesis is redundant for `n ≥ 3` (reading R2).
* `CV.crossingPoints_eq_selfIntersections hL hreg` — the crossing points of `Shadow.single (polyComp L hreg)`
  are CV:def:diagrammatic's `selfIntersections L`: `Shadow.single_crossingPoint` (SM/LinkDiagram.lean:1703,
  the shadow's crossing point is `SM.crossingPoint` of `singleCrossingEquiv`) with the accepted
  `CV.crossingPoint_mem_selfIntersections` and `CV.exists_crossing_of_selfIntersection` (CV/Events.lean:225,
  236 — the two halves of `CV.crossingPoint_bijOn`, CV:def:interlace's vertex set).
* `CV.OverUnder C` (over strand + membership) with `toPolygonDiagram hL : PolygonDiagram (polyComp L hreg)`
  (SM's `generic` field supplied by CV's hypotheses), `ofPolygonDiagram`, `toPolygonDiagram_ofPolygonDiagram`
  (round trip is the identity, proof irrelevance), `ofDiagram`/`toDiagram_ofDiagram` (from any accepted
  `Diagram` on the single polygon; the carried diagram is that `Diagram`).
* The witness is transported as is: the CV bundle's clause fields are stated on
  `W : RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε` and proved by `SM.cf_lem_rounding.<field>`
  (fields `smooth_regular_carried`, `a`, `b`, `e`), by the witness projections plus the two CV re-readings
  (`c`), and by `rotCurve_eq_rot` (`d`). Nothing CV asserts is missing from SM's witness: the only CV-specific
  assertions are (c)'s "same double points" in CV's vocabulary (a set equality proved through the bridge above)
  and (d)'s `rot` in CV's definition (a rewrite by `rot_eq_rotationNumber`); (c)'s "same over/under assignment"
  is `rfl` because `D_ε` is `D` (FR-R1).

## 4. Readings

R1 (binder). `{n : ℕ} [NeZero n] (L : LabelledTuple n)`, as in CV.Rotation / CV:lem:uniformrot; `n ≥ 3` is
`Regular.three_le`. No `hn`.

R2 (hypotheses as printed). `hreg : Regular L` ("the principal turns of L all exist") is listed although,
for `n ≥ 3`, `Diagrammatic L` implies it (`Diagrammatic.regular`); the printed statement lists it separately,
and SM's `Shadow.Generic` has the corresponding `regular` field. `hturn : ∀ i, principalTurn L i ≠ 0` is CV's
`principalTurn` (`rfl`-equal to SM's). "Finitely many double points, all transversal, none of them a corner;
no corner on a non-incident edge" is `Diagrammatic L`, the accepted rendering of this list (d1_setup.tex:316–320),
which CV's own consumer (B) names as the input class (d3:762). `Diagrammatic` also carries "exactly two
preimages" (no triple point), which thm:carrierfloor (C), d3:784–786, describes as "repeat[ing] the
shared-image clause of Definition def:diagrammatic"; SM's `no_triple` is thus supplied by CV's printed
hypothesis class, not silently added (contrast PLAN_FINAL.md FR-R3 on the SM side).

R3 (the diagram `D`). `OverUnder (polyComp L hreg)`: "L together with an over/under assignment at each of its
double points" is exactly the over strand at each crossing of the one-component shadow, the double points
being `selfIntersections L` (`crossingPoints_eq_selfIntersections`). Taking SM's `PolygonDiagram` directly
would have duplicated CV's printed hypotheses in its `generic` field; `OverUnder` keeps the data and lets the
hypotheses do their printed work. Conversions in both directions and from an accepted `Diagram` are provided.

R4 (`D_ε` is `D`, FR-R1). `W.carried : Carried W.Lε (D.toPolygonDiagram hL).toDiagram`; the printed "same
over/under assignment" is the identity of over strands (`rfl`); "same crossing signs and writhe" compare the
smooth signs `sgn det(velocity_over, velocity_under)` with `Diagram.sign`/`writhe` — the vocabulary the
accepted CV rows ax:homfly / def:homfly already use for polygonal diagrams.

R5 ((c) "same double points"). Stated in CV's vocabulary: `SmoothRegularLoop.doublePoints W.Lε.γ =
selfIntersections L`. "Same strands" is SM's reading (each occurrence traversed on the straight part of its
strand's edge, in that edge's direction) — CV has no separate vocabulary for strands of a polygon.

R6 ((d) `rot`). Both sides CV:def:rot: `rotCurve` (curve) and `rot L hreg` (polygon, the `ε_i` ray formula,
cast to `ℝ`). SM's `rotationNumber` appears only inside the proof (`rot_eq_rotationNumber`, decision F2).

R7 (discs). "The disc of radius ε about q_i" is the closed Euclidean disc `cornerDisc (polyComp L hreg) ε i`
(SM's model, Euclidean not product metric); the two ε-sub-segments are `subsegOut`/`subsegIn`; "edges of L"
are `edgeSegment L i` (CV:def:polygon's `[p_i, p_{i+1}]`, `polygon_definition.edge_segment`). CV has no
disc vocabulary of its own, so SM's is used unchanged.

R8 (parameter). As in SM (FR-R4): `L_ε` is 1-periodic with constant speed; the printed arclength along the
junction is `speed · (t − a j)`; (b)'s "angular derivative nonzero" is parametrisation-independent.

R9 (shape). As in SM (FR-R5): the existence field is the theorem, the clause fields hold for every witness
and are SM's projections re-read; the fixed content of (a)–(e) is the field list of `SM.RoundingWitness`.

R10 (named construction, FR-R2). The printed statement is existential; thm:carrierfloor (A) needs the record
by name. `CV.clearance`, `CV.clearance_pos`, `CV.roundingRecord` (with `roundingRecord_eq`, `roundingRecord_Lε`)
and `CV.exists_witness_of_lt_clearance` export SM's `CornerRounding.clearance` / `roundedWitness` /
`roundedLoop` on CV's binder; the (A)/(B) rows can cite them without touching SM's namespace.

## 5. Fidelity risks (to be cited in the review of this row and of its consumers)

Inherited from the SM row (PLAN_FINAL.md §6): FR-R1 (the smooth diagram is the polygonal `Diagram D` read
through `Carried`; here made explicit by the `rfl` conjunct of (c)), FR-R2 (∃-form plus a separately named
construction), FR-R3 (the witness exports more than printed — same extras here), FR-R4 (arclength/speed
parameter), FR-R5 (bundle shape), FR-R7 (the Mathlib pin's `Real.smoothTransition` lemmas live in the SM row).

CV-specific:

* FR-CV1 (new CV-side structure). `CV.OverUnder` is a new data structure (two fields). It is the printed
  "over/under assignment"; SM's `PolygonDiagram` is recovered by `toPolygonDiagram` and the round trip is the
  identity. A reviewer preferring the SM object directly can read every field through
  `toPolygonDiagram_ofPolygonDiagram`.
* FR-CV2 (binder `[NeZero n]`). The instance binder is the accepted CV convention for labelled polygons and is
  weaker than `hn : 3 ≤ n` (which the row derives from regularity). It is not a scope change.
* FR-CV3 (redundant hypothesis). `hreg : Regular L` follows from `Diagrammatic L` for `n ≥ 3`
  (`Diagrammatic.regular`). Kept because printed (35–36); harmless.
* FR-CV4 (no-triple). The lemma's own hypothesis list (35–38) does not say "no triple points"; the accepted
  rendering of 36–38, `Diagrammatic`, does (exactly two preimages), and both CV consumers assume it ((C),
  d3:784–786; (B) via "diagrammatic"). A reading of 36–38 admitting triple points is outside both papers'
  diagram classes (SM's `Diagram` has `no_triple`); no such reading is offered.
* FR-CV5 (`rot` of the polygon). `CV.rot` is the computable `ε_i` ray formula (needs `Regular L`, hence the
  `hreg` argument in the statement of (d)); the identification with `Σ τ_i / 2π` is the accepted theorem
  `rot_eq_rotationNumber`, cited in the proof only (decision F2). The curve `rot` is one definition under two
  names (decision F6).
* FR-CV6 (consumer entry). thm:carrierfloor (C) starts from "an oriented knot diagram" `D : Diagram` with
  `componentCount = 1`; entry into this row needs `D.Γ = Shadow.single C` (`OverUnder.ofDiagram`). A
  one-component shadow is propositionally the single shadow of its component, but no library lemma states
  `D.Γ.c = 1 → D.Γ = Shadow.single (D.Γ.comp ⟨0, _⟩)` yet (see open items).
* FR-CV7 (vocabulary of (c) "same strands"). Rendered in SM's occurrence vocabulary (`Visit`, `label`,
  `carried.τ`); CV's text has no finer notion of "strand" for a polygon than its edges, which `label` names.

## 6. Open items

1. `SM.cf_lem_rounding` (work/lean/SM/Rounding.lean) is under review. This row consumes its fixed statement
   (`RoundingWitness`, `RoundingData`, `Carried`, `PolygonDiagram`, `cornerDisc`, `subsegOut/In`,
   `SmoothRegularLoop`) and its named construction (`CornerRounding.clearance`, `clearance_pos`, `Admissible`,
   `roundedWitness`, `roundedLoop`); the clause fields here are its projections, so any change accepted there
   propagates mechanically (field lists to re-sync: `b`, `c`, `e`).
2. For thm:carrierfloor (C): a lemma `Shadow.eq_single_of_c_eq_one` (or `Diagram.Γ_eq_single` on
   `componentCount = 1`) turning a one-component `Diagram` into `hD : D.Γ = Shadow.single (curveOf-polygon)`;
   with it `rounding_of_diagram` applies verbatim. Not needed for the present row.
3. Port: module `work/lean/CV/Rounding.lean` (imports as above), namespace `CV`. Name-safety scan done
   (grep over work/lean SM/CV/Bridge/RProof heads): `polyComp`, `OverUnder`, `clearance`, `roundingRecord`,
   `roundingAdmissible`, `single_generic_of_diagrammatic`, `crossingPoints_eq_selfIntersections`,
   `Diagrammatic.regular`, `rotCurve_eq_rot`, `doublePoints_eq_selfIntersections`, `CVRoundingData`,
   `rounding`, `rounding_of_diagram`, `exists_witness_of_lt_clearance` — no collisions (note the accepted
   `CV.Admissible` is the ray predicate of CV:def:rot; the helper here is `roundingAdmissible`, a theorem
   producing `SM.CornerRounding.Admissible`).
4. The two commentary paragraphs (41–43, 45–55) and (b)'s commentary (68–79) are readings, not fields
   (the SM row does the same for 3668–3679).

## 7. Declarations (work/drafts/cvdom/CVRounding.lean, namespace `CV`)

`polyComp`, `polyComp_k`, `polyComp_P`, `single_generic_of_diagrammatic`, `Diagrammatic.regular`,
`crossingPoints_eq_selfIntersections`, `OverUnder` (structure; `overStrand`, `over_mem`),
`OverUnder.toPolygonDiagram`, `OverUnder.toPolygonDiagram_overStrand`, `OverUnder.toPolygonDiagram_toDiagram_Γ`,
`OverUnder.ofPolygonDiagram`, `OverUnder.toPolygonDiagram_ofPolygonDiagram`, `OverUnder.ofDiagram`,
`OverUnder.toDiagram_ofDiagram`, `clearance`, `clearance_pos`, `roundingAdmissible`, `roundingRecord`,
`roundingRecord_eq`, `roundingRecord_Lε`, `rotCurve_eq_rot`, `doublePoints_eq_selfIntersections`,
`CVRoundingData` (structure, fields `exists_clearance`, `smooth_regular_carried`, `a`, `b`, `c`, `d`, `e`),
`rounding`, `rounding_of_diagram`, `exists_witness_of_lt_clearance`.
