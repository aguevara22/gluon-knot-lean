# CV/R tail — DESIGN A (fidelity and specification first), 2026-09-15

Architect A for the CV/R tail lane. Rows (tools/claims.py 1-based): **155** CV:thm:carrierfloor, **165**
CV:singleton_D_i, **174–178** R:generic_selected / extreme_pair_zero / extreme_transport / extreme_selected /
cv_theorem, **183** Bridge:theorem, **184** SM:corner_laws_and_soft. Companion sketch
`work/drafts/cvtail/Sketch_A.lean` (666 lines): `cd work/lean && lake env lean ../drafts/cvtail/Sketch_A.lean`
exits 0, exactly 2 `sorry` (the two route leaves §5: `CV.singleton_D_i_of_floor`,
`RProof.extreme_pair_zero_of_singleton`), every statement sorry-free; `#print axioms` of the proved assemblies
`CV.carrierfloor_D`, `CV.carrierfloor_of_sm`, `RProof.cv_R_of_rows`, `Bridge.sm_R_of_rows`,
`SM.corner_laws_and_soft_of` = standard + the registered `SM.lit_homfly` (+ `SM.lp_lm`, `SM.lp_lm_uniqueness`
where `P = homfly` is used). Nothing written under work/lean.

Inputs read: d3_floor.tex 700–1012 (thm:carrierfloor, rem:curlauthor, rem:floorscope); d6_vertexedge.tex
2640–2790, 2886–2947 ((D)(i) and its proof), 1157–1166 (def:markeddata); d1_setup.tex 487–512, 908–930;
d10_axioms.tex 18–24, 387–425; sm-6-comparison.tex 105–120, 299–345; sm-4-knotlaws.tex 1149–1151; TARGETS.md,
EXECUTION.json, R_ASSEMBLY_SPEC.md, OPEN_WORK.md, PROOF_PLAN.md, BRIDGE.md §1, §3; the four RA files of rows
174–177; work/lean/RProof/{Cores,X1Rows,X1Rows2,GenericTransport}.lean, Bridge/{B1,B3,B4,SmR}.lean,
SM/HypR.lean, CV/{Rounding,UniformRot,Curl,X1,Axioms,SelectorA,ChamberInvRow}.lean, SM/{ALawful,CChamber,
CSilent,CS3,CS5}.lean; work/drafts/gap2/{GAP2_STATEMENTS_MEMO.md,Gap2Statements.lean}, rlane2/NOTES_FINAL.md,
floor/Sketch_A.lean, contact/Sketch_A.lean (no PLAN_FINAL / Statements_FINAL exists yet in floor/, contact/,
corner/ — the memo shapes are taken as the assumed interface, §2.1); AUTHOR_NOTES D-GAP2, D-GAP2-2b, row-91
acceptance, D-F11, D-F14, the R-lane panel entry, the CV:lem:rounding / CV:lem:curl entries;
work/reports/cv-lane-plan-20260913.md §155, §161–165, §174–178, §183 and rule F6.

## 0. Where the statements come from (the spec, row by row)

* 155, 165: CV text (d3, d6), through the F6 rule: "(R),(A),(B),(C) verbatim = SM cf:thm-carrierfloor …
  this lane must NOT prove them twice: the CV rows 152–155 are to be stated as re-exports of the SM cf:*
  rows" (plan §2 F6, §155(2)); the pattern is the ACCEPTED CV:lem:rounding (`CV.rounding`,
  CV/Rounding.lean:297–420: CV binder `L : LabelledTuple n`, `Diagrammatic L`, `Regular L`, nonzero turns,
  `D : OverUnder (polyComp L hreg)`; SM objects at `polyComp L hreg`, `D.toPolygonDiagram hL`; the CV-specific
  readings (c),(d) re-read in CV vocabulary) and CV:lem:curl (CV/Curl.lean, same objects, `rotCurve`).
* 174–178: fixed names (lean/axiom-policy.json `targets`); the checker only pins the NAME
  (tools/check_lean.py:104–109); the STATEMENTS are already frozen and accepted as bundles in
  work/lean/RProof/X1Rows.lean (`GenericSelectedData` 1434, `ExtremePairZeroData` 1483,
  `ExtremeTransportData` 1628, `ExtremeSelectedData` 1757, `CvTheoremData`/`CvRNear`/`ChamberInvII`
  1834–1879) with the row shape of the accepted siblings (`theorem <name> (hn) (E) (e f g) h3 h4e h4f h4g
  (hE) : ∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ <Row>Data hn E e f g δ`, e.g. `exterior` X1Rows2.lean:1966,
  `generic_transport` GenericTransport.lean:11157) and `RProof.cv_R : CV.hyp_R` (X1Rows.lean:23, 1827;
  CV.hyp_R = 114–133, accepted row CV:ax:R). This design DOES NOT restate them; it fixes the assembly.
* 183: EXECUTION.json "Bridge:theorem"; TARGETS.md "Apply the proved CV R theorem to obtain SM R"; BRIDGE.md
  §3 (19)–(21); the library theorem `SM.sm_R_of_cv_R : CV.hyp_R → SM.hyp_R` (Bridge/SmR.lean:52).
* 184: TARGETS.md "Exact final target" (quoted in full in Sketch §6) and EXECUTION.json tasks FINAL.

## 1. Fidelity risks, recorded BEFORE the statements

**FR-CV-155-1 (F6 bridge).** (R)(A)(B)(C) are stated on CV's printed domain and PROVED from the SM row-99
bundles by conditional theorems (`carrierfloor_*_of_sm`); the SM bundles are the MEMO shapes
(Gap2Statements.lean §7), copied into Sketch §1 and labelled "to be unified with lane floor". Floor lane
Sketch_A differs: (A) adds `junctionTemplate`, (B) states the claim "in the normalised orientation"
(`AllPosOrOneNeg C.P ∧ BClaim C D ∨ AllPosOrOneNeg (reversal C.P) ∧ BClaim C.reverse D.reverse`), (C) uses
`zZeroPart` for `f_D`. Whatever lands, the CV bridge changes only in `carrierfloor_B_of_sm` /
`carrierfloor_C_of_sm` (a cast layer), never in the CV statements — unless the floor lane's (B) keeps the
normalised-orientation disjunction, in which case CV (B) must follow it (the CV text is identical to SM's:
"after reversing the orientation of L if necessary … Then there are u, ε₁ …" — the memo reads the record of
`L` itself; the floor lane reads the record of the normalised polygon; the CV lane takes the floor lane's
ruling; the memo reading is the stronger one and is what the printed proof does, sm-3:4368–4370 "perform
the allowed normalization once").
**FR-CV-155-2 ((R) on knots).** "Let K be an oriented knot … P_{−K} = P_K": rendered as `homfly X.reverse =
homfly X` on a one-component diagram `X` of `K` AND at the knot level `LinkEquiv X X' → homfly X'.reverse =
homfly X` (the memo's two fields). "Knot" = `LinkEquiv` class (design D2). The polynomial letter is CV's
`homfly` (CV:def:homfly), bridged by `SM.lp_core.eq_homfly`.
**FR-CV-155-3 ((R) rotation).** "rotation number of the underlying plane curve negated" has a polygon field
(`CV.rot`, `reversal`, both regularity proofs as parameters — the accepted `CV.rot_reversal`, CV/Rotation.lean:416,
already IS this clause) and a `C¹` field (`CV.rotCurve γ.reverse = -rotCurve γ`; `rotCurve` is `γ.rot` by
`abbrev`, F6). Nothing about the DIAGRAM's reversed curve being the reversed curve is asserted (neither text says
it).
**FR-CV-155-4 ((A)).** "one curve and one diagram at those data" = proof irrelevance of `roundingRecord`
(`rfl`); "D_ε" = `Carried … D` (FR-R1 of CV:lem:rounding: the rounded diagram is `D` itself); "the arc length ℓ is
then determined by the endpoint condition" is proof commentary (no field, as in the memo); "the rest of the
curve is L itself" = the accepted `CV.rounding.a` clause (set form, `⋃ edgeSegment L i`).
**FR-CV-155-5 ((B)).** "exactly R points" = `Set.ncard` of the parameter set in `[0,1)` (memo/floor reading;
the junction map is injective there, cf:lem-rounding (b)); `R = rotAbs L hreg : ℕ` (CV:def:rot) — an
integer count, no real cast in the CV statement; "crosses that direction in the positive sense" = the point
lies in a junction `(a j, b j)` with `0 < deriv (θ j) t` (the lift of cf:lem-rounding (b)); `ε₁ ≤ ε₀(L)` added so
the record exists (printed proof: `ε₁ = ε₀(L)`). (B)'s "exactly one is negative" (d3:764) omits "and every
other is positive", which (C) has (rem:curlauthor tightened only (C)); with all turns nonzero the two read
the same; both rendered by `TurnsUniformOrOneDissent` (four disjuncts, = memo `UniformOrOneDissent` by
`Iff.rfl`).
**FR-CV-155-6 ((C)).** Hypotheses one field each (`shadow`, `positive`, `turn_ne`, `turn_lt_pi`,
`alternative`) with `hL : Diagrammatic L` and `hreg : Regular L` as parameters (the double-point/corner list
of d3:781–786 IS CV:def:diagrammatic, as (C) itself says; "all principal turns existing" is `Regular`).
Conclusion in ℤ: `1 - X.writhe - rotAbs L hreg ≤ mindegAZ (homfly X)` (mindegAZ is the integer value with the
`0` convention at `f = 0`; `homfly X ≠ 0` by lp:core, so no gap) and the `f_D` clause in SUPPORT form
`∀ d, coeffAt d 0 (homfly X) ≠ 0 → 1 - w - R ≤ d` ("whenever f_D ≠ 0" is the vacuity of the support form) —
NOT a `zZeroPart` object. The bridge from SM's real-cast form is `rotAbs_intCast_real` + `exact_mod_cast`.
**FR-CV-155-7 ((D)).** "carrying no residual piece" = `piecesOn hG.crossingGeometry S q = ∅`; "so that
P_{S,L} = 1 and w_{S,L} = 0 by def:X1's empty conventions" is commentary on the hypothesis, INCLUDED in the
conclusion as its first conjunct (a theorem of the accepted CV:def:X1, `X1_definition.empty_conventions`);
"all its principal turns are nonzero" on the carrier's CORNER POLYGON `geoCornerPolygon` (CV:def:wind's
corners, CV:def:rot reads `R(L)` there — `carrierR` is `rotAbs` of it); the alternative likewise; "R(L) ≥ 1"
= `1 ≤ carrierR` (ℕ); "min deg_a P_{S,L} = 0 ≥ 1 − w − R" = `mindegAZ (groupedPoly) = 0 ∧ 1 - groupedWrithe -
carrierR ≤ 0`. The nonzero-turn hypothesis is printed but not consumed by the proof (uniformrot needs only
the sign pattern); kept, unused (`_hturn`).
**FR-CV-155-8 (row bundle).** Row declaration `CV.carrierfloor : CV.CarrierFloorData` with five clause
fields; no policy name; the row is mapped only when all five clauses are theorems (D-F11): (D) now, (R)(A)(B)
when the floor lane proves them, (C) when fd:contact/cf:lem-curl land. Partial acceptance is not a row.
**FR-CV-165-1 (f_A and the degree gap).** `f_A = [z^0] P_{S,A}` (def:markeddata); "min deg_a f_A ≥ slot + 2"
rendered in support form `∀ d, coeffAt d 0 (groupedPoly) ≠ 0 → slot + 2 ≤ d` (the consumer
`ExtremePairZeroData.pair_row_zero` needs only `Ω₁ = 0`, which the printed "so" derives — PROVED,
`omega1_eq_zero_of_gap`). PROOF_PLAN step 5: "`CV:singleton_D_i` requires only the stated degree gap and zero
conclusion" — both are fields; nothing of (D)(ii)–(v) is stated.
**FR-CV-165-2 (singleton piece carried by A).** "{c} a singleton residual piece of S carried by A" =
`c ∈ U(S)`, `pieceLabels (pieceOf c) = {c}`, `pieceOf c ∈ piecesOn q` (def:X1's "assigned to L by
lem:carriers (iv)") — exactly the shape the accepted `ExtremePairZeroData.third_singleton_piece` produces
(X1Rows.lean:1520–1527), so the consumer needs no translation. "uniform carrier" = CV:def:wind's
`CarrierUniform` (one nonzero sign at every corner).
**FR-CV-165-3 (dependency column).** claims.py lists `cb:singleton` (SM row 103) as a dependency of 165. On
the CV domain (`CV.Generic P`, larger than `SM.Generic`) the SM row cannot be CONSUMED (B4's dictionary holds
only on SM-generic polygons); it is the TEMPLATE (plan §165(2): "SM cb:singleton's proof is the same chain
with cb:products/thm:floor"). Row 165 is proved on the geo layer (CV:lem:carriers (iv) at `insert c S`,
CV:cor:groupedknot (B), CV:lem:uniformrot, CV:lem:turnlift (ii), CV:ax:homfly knot parity, and 155 (C)/(D)).
Coordination ask (§7): the corner lane should prove cb:singleton's geometric core at tier 1
(`CrossingGeometry`) so 103 and 165 share it; if it proves 103 on `IsDecomposition` only, 165 is a separate
~1.5k-line unit.
**FR-R-174..177 (frozen).** The bundles are accepted text; readings already recorded (AUTHOR_NOTES 06:35Z
panel; rlane2/NOTES_FINAL.md §12 items 1–13): fixed labels `a = x_ef, b = x_eg, c = x_fg` with canonical +
relabelled branches; sides named by local graphs, never by coorientation; `hn` explicit; `T_ν(J)` =
`rowTerm` = `CV.X1Summand` (absent rows `0`). Row 175's `pair_row_zero` is the only field of 174–177 whose proof
does NOT need 155 (C): it needs 165 (its `third_singleton_piece` presupposition is accepted, `PRE_175_*`).
**FR-R-178.** `RProof.cv_R : CV.hyp_R` (R6 form, all side parameters); the assembly IS the accepted
`hyp_R_of_near_of_chamberinv (A2_cvRNear_of_rows …) chamberinv_ii` (X1Rows.lean:2825–2940); `ChamberInvII` is
the accepted CV row 147 (ii) `CV.chamberinv_ii` (ChamberInvRow.lean:78) read with `.symm` — PROVED here
(`chamberInvII_of_row147`). Spec sentences: R_ASSEMBLY_SPEC "Finally sum the proved identities (4) over the
same finite outside-support set in (3). Equality is preserved by finite summation, giving exactly CV ax:R";
OPEN_WORK item 4 "Sum all fibre identities to prove CV ax:R on its entire printed simple/transversal
forced-bundle domain" — the domain is `E.IsSimpleRIII` (CV:def:event, accepted), unchanged.
**FR-B-183.** `Bridge.sm_R : SM.hyp_R` is a RESTATEMENT: `SM.sm_R_of_cv_R RProof.cv_R` (Bridge/SmR.lean
header and 52). BRIDGE.md §3's proof (B1–B3 make the germ a simple transversal RIII event, ax:R gives (20), B4
(17)/(18) gives (21)) is exactly `SM.hyp_R_of_cv_hyp_R` (SmR.lean:27–47) + `Bridge.B4.pointwise`. No new
mathematics; the row is the instantiation at the proved `RProof.cv_R`. `SM.hyp_R` (accepted definition row)
is the all-side-parameters form `∀ tp tm`, equivalent to the chamber form by prop:C-chamber
(`hyp_R_iff_base`).
**FR-F-184-1 (shape).** `SM.corner_laws_and_soft : SM.CornerLawsAndSoftData`, a `structure : Prop` whose
fields are THE ACCEPTED BUNDLES `CChamberData`, `CSilentData`, `CS3Data`, `CS5Data`, the Prop `hyp_R`, and
Props for the three pending rows in the shape of cor:A-lawful's accepted `ALawfulData` fields
(SM/ALawful.lean:44–135) with `amplitude` → `cornerStateSum` (`VertexEdgeLawC`, `CuspLawC`, `SoftTheoremC`,
`ReversalLawC`, `CyclicLawC`, `TrianglesC`). TARGETS: "Define its conclusion as the conjunction of these actual
C identities, with their printed quantifiers, signs and domains. Do not replace it by a theorem about a freely
supplied lawful function. … It must not retain an R assumption" — the structure is that conjunction; the
conditional `corner_laws_and_soft_of (hR : hyp_R) …` is library material; the ROW is its instantiation at
`Bridge.sm_R`, `thm_C_S7`, `cor_C_inherits`, `thm_C_soft` — R discharged, no parameter.
**FR-F-184-2 (genericity of children).** `C` is defined on generic polygons only (def:C), so C(λ₁), C(λ₂),
C(P(0)∖j), C(P̄), C(P_ε) need `Generic` proofs: rendered as `∃ h : Generic …` inside the identities (the
domain checks of cor:C-inherits' printed proof, sm-6:322–345: halves by lem:children (ii), deletion by (G1)
hypothesis + the (G2) argument, P_ε by lem:soft-generic, P̄ by `generic_reversal` — accepted, so `ReversalLawC`
uses it directly). This is what the corner lane's thm:C-S7 / thm:C-soft / cor:C-inherits bundles must supply
("to be unified with lane corner": if they state `Generic λ ∧ …` as `ALawfulData` does, the final theorem's
Props are re-shaped to theirs — the field TYPES change, not the theorem).
**FR-F-184-3 (coverage).** TARGETS' list ↔ fields: chamber constancy (`chamber`), silent E/C (`silent`), flat
(`flat`), vertex–edge both bigon branches + sliding (`vertex_edge` on `VertexEdgeAt`, which is bigon ∨ sliding
by `vertexEdge_bigon_or_sliding`), triple (`triple : hyp_R`), full cusp on the (G1) domain incl. threaded
(`cusp`, no emptiness hypothesis), empty-cusp zero retained (`empty_cusp`), soft in every sector incl.
zero-selector (`soft`: every `SoftAdmissible q`), reversal/cyclic/normalizations inherited with cor:A-lawful
(`reversal`, `cyclic` = def:C's cyclic invariance `cornerStateSum_genericShift`, `triangles` = `C(K₁) = −1`,
`C(K₋₁) = +1` on `star 1`, `starNeg 1`). Root independence has no C analogue (C has no root) and is not a
field. The cusp law's `κ` clause follows `ALawfulData.cusp_law` (κ = ±1, the rotation jump).

## 2. The statements (Sketch_A.lean; exact text there)

### 2.1 Row 155 — `CV.CarrierFloorData` = `clauseR/A/B/C/D` (Sketch §2)
* (R) `CV.CarrierFloorRData`: `homfly_reverse`, `knot_reverse`, `sign_reverse`, `writhe_reverse`,
  `rot_reverse_polygon` (`CV.rot`), `rot_reverse_curve` (`CV.rotCurve`).
* (A) `CV.CarrierFloorAData`: `one_record`, `diagram_carried`, `junction_local`, `rest_is_L`, all on
  `roundingRecord hL hreg hturn D hε hε₀` (CV/Rounding.lean:245).
* (B) `CV.CarrierFloorBData.tangencies`: `∀ L hL hreg hturn D, TurnsUniformOrOneDissent L → ∃ u ε₁, |u| = 1 ∧
  0 < ε₁ ∧ ε₁ ≤ clearance L hreg ∧ ∀ ε hε hε₀, ε < ε₁ → ncard{T = u} = rotAbs L hreg ∧ ncard{T = −u} = rotAbs L
  hreg ∧ (positive crossing in a junction)`.
* (C) `CV.CarrierFloorCHyp L hreg X` (5 fields) and `CV.CarrierFloorCData` (`floor`, `floor_z0`).
* (D) `CV.CarrierFloorDData.floor_D` — PROVED (`CV.carrierfloor_D`).
* Bridges (D-F11 conditional theorems, PROVED): `carrierfloor_R_of_sm`, `carrierfloor_A_of_sm`,
  `carrierfloor_B_of_sm`, `carrierfloor_C_of_sm`, `carrierfloor_of_sm : SM.CarrierFloor{R,A,B,C}Data →
  CV.CarrierFloorData`. Row theorem once the floor lane lands: `CV.carrierfloor := carrierfloor_of_sm
  cf.clauseR cf.clauseA cf.clauseB cf.clauseC`.

### 2.2 Row 165 — `CV.SingletonDiData` (`degree_gap`, `factor_zero`), Sketch §3
Row theorem `CV.singleton_D_i : SingletonDiData`; `SingletonDiData.of_degree_gap` PROVED (the printed
"so"); `singleton_D_i_of_floor (hC : CV.CarrierFloorCData) : SingletonDiData` LEAF.

### 2.3 Rows 174–178 — frozen (X1Rows.lean); assembly PROVED (Sketch §4)
`RProof.RowShape D` = the sibling signature; `rowShape_170/172/173` the accepted rows;
`RProof.cv_R_of_rows (h174 h175 h176 h177 : RowShape @…Data) : CV.hyp_R` PROVED. Row 178 :=
`cv_R_of_rows generic_selected extreme_pair_zero extreme_transport extreme_selected`.
`extreme_pair_zero_of_singleton (h165 : CV.SingletonDiData) : RowShape @ExtremePairZeroData` LEAF.

### 2.4 Row 183 — `Bridge.sm_R : SM.hyp_R := SM.sm_R_of_cv_R RProof.cv_R` (Sketch §5; `sm_R_of_rows` PROVED)

### 2.5 Row 184 — `SM.CornerLawsAndSoftData` (11 fields) and `corner_laws_and_soft_of` PROVED (Sketch §6)
Row := `corner_laws_and_soft_of Bridge.sm_R ⟨thm_C_S7⟩ ⟨cor_C_inherits cusp⟩ ⟨thm_C_soft⟩ ⟨cor_C_inherits
reversal⟩ ⟨cor_C_inherits triangles⟩` (the last three are the corner lane's bundles re-read).

## 3. Proof routes and consumed lemmas (file:line)

* 155 (R): floor lane U-R (lp:coefficient-transport `SM.coefficient_transport`, `ReverseCarries`
  LinkMoves.lean:1172, `IsSkeinTriple.reverse`, `reverse_sign`, `reverse_writhe`, `rotationNumber_reversal`,
  `ClosedC1Curve.reverse`); CV side: `lp_core.eq_homfly` (PolynomialBlock), `CV.rot_reversal`
  (CV/Rotation.lean:416, accepted) — DONE in the sketch.
* 155 (A): floor lane U-A on `CornerRounding.roundedWitness` (SM/Rounding.lean); CV side: `rfl`,
  `RoundingWitness.carried`, `CV.rounding.a` (CV/Rounding.lean:406) — DONE.
* 155 (B): floor lane U-B (lem:uniformrot + cf:lem-rounding (b) lifts, plane geometry); CV side:
  `roundingAdmissible` (CV/Rounding.lean:235), `rotAbs_cast` (CV/Rotation.lean:149), `rot_eq_rotationNumber`
  (374), `Int.cast_abs` — DONE.
* 155 (C): floor lane U-C (the switch `switchAll`, the ring involution, `SM.cf_lem_curl` at the `R`
  tangencies, the transverse lift, `TransverseFrontBound` ← contact lane row 94 ← src:contact + rows 84–93
  + row 91 (accepted 14:25Z)); CV side: `lp_core.eq_homfly`, `rotAbs_intCast_real` — DONE.
* 155 (D): `groupedPoly_of_piecesOn_eq_empty`, `groupedWrithe_of_piecesOn_eq_empty`, `carrierR_cast`,
  `carrierPolygon_cvRegular` (CV/X1.lean:52–101), `uniformrot.pos_ge_one/neg_le_neg_one/one_dissent`
  (CV/UniformRot.lean:271–306), `regular_reversal'`, `rot_reversal` (CV/Rotation.lean:412–421),
  `SM.principalTurn_reversal` (SM/RotationReversal.lean:49), `mindegA_single` (LinkLaurentRing.lean:502),
  `AddMonoidAlgebra.one_def` — DONE (`carrierfloor_D`, `one_le_abs_rot_of_alternative`, `mindegAZ_one`).
* 165: the printed chain d6:2890–2947 on the geo layer: `insert c S ∈ Ind` (CV.mem_Ind_iff + `c ∈ U`);
  pieces of `S'` = pieces of `S` minus `{c}` (`pieceLabels`, `residualGraph` isolated vertex); carriers of `S'`
  (CV:lem:carriers (i)–(iv), CV/CarriersLemma.lean; the split of `q` into two `GeoComponent`s under
  `geoSmoothingSuccessor`); `groupedPoly`/`groupedWrithe` factorisation through CV:cor:groupedknot (B)
  (CV/GroupedKnot.lean: `P_{S,L}` = homfly of the carrier's positive lift, a one-component diagram) and the
  single-crossing unknot (SM lc:single-crossing, accepted); knot parity `CV.ax_homfly.knot_parity`,
  `zRow_zero_mul_of_inSupportM_one` (CV/Axioms.lean); rotation additivity via CV:lem:turnlift (ii)
  (CV/TurnLift.lean) with the two smoothing corners' opposite turns (`principalAngle` of `det(u,v)`, `det(v,u)`);
  `uniformrot` (i)/(ii) ⇒ `R(A) = R(Λ₁) + R(Λ₂)`; 155 (C) on each loop's positive lift (hypotheses:
  positivity `positiveLift_isPositive`-style, turns nonzero by (G1)/(G5), `|τ| < π` automatic, diagrammatic by
  lem:carriers, alternative) or (D) when a loop carries no piece; add the two support bounds.
* 175 `pair_row_zero`: `rowTerm_of_mem_Ind`, `wind = ∏ weight`, `weight_of_mixed` (`wind ≠ 0 ⇒ every carrier
  uniform`), the owner of `{z}` (`piecesOn`/`pieceOwner`, `mem_piecesOn_iff`), `PRE_175_third_singleton_piece`
  (X1Rows.lean:1560), then 165 `factor_zero` and `Finset.prod_eq_zero`. Then `extreme_pair_zero :=
  ⟨δ of parity, PRE_175_*, pair_row_zero⟩` (shape of `availability_zero_one` X1Rows2.lean:3619).
* 174, 176, 177: the RA ledgers (R_GENERIC_SELECTED_COUPLE_PROOF.md §1–5, R_EXTREME_SINGLETON_TRANSPORT_PROOF.md
  §1–3, R_EXTREME_SELECTED_COUPLE_PROOF.md §1–3) on `Omega1/carrierR/groupedPoly` with CV:lem:fulltwist
  (CV/FullTwist.lean, accepted), CV:lem:homflyrows (ii)/(iii) (CV/HomflyRows.lean, accepted), CV:selector_A,
  knot parity, uniformrot, turnlift (ii), CV:cor:groupedknot, the accepted G11 RIII move toolkit
  (RProof/GenericTransport.lean, X1Rows3.lean), an RII move (G10, open) and, for 177, an ambient isotopy
  through the wall of a two-component diagram (G10/G11, open) — and 155 (C)/(D) for the floor steps. Not
  designed here beyond the frozen statements; each is its own ~1k-line lane (plan §174/176/177).
* 178: `cv_R_of_rows` DONE. 183: DONE. 184: DONE modulo the corner lane's three rows + 183.

Interface hypotheses (explicit, never mapped): `SM.CarrierFloor{R,A,B,C}Data` (floor lane),
`CV.CarrierFloorCData` (this lane, for 165), `CV.SingletonDiData` (for 175), the four `RowShape` rows (for
178/183), `SM.hyp_R`, `VertexEdgeLawC`, `CuspLawC`, `SoftTheoremC`, `ReversalLawC`, `TrianglesC` (corner lane,
for 184).

## 4. Provable NOW (inputs all accepted)

* **155 (D)** — proved in the sketch (`CV.carrierfloor_D`, 45 lines).
* **155 (R)(A)(B)(C) ← SM 99** — the four bridges proved (conditional; unconditional the moment
  `SM.cf_thm_carrierfloor` lands; the (R) polygon clause and (A)'s `rest_is_L`/`diagram_carried`/`one_record`
  need no SM input at all).
* **165's "so"** — `SingletonDiData.of_degree_gap` proved.
* **178 ← 174–177** — `cv_R_of_rows` proved; **183 ← 178** — `sm_R_of_cv_R`/`sm_R_of_rows` proved;
  **184 ← 183 + corner lane** — `corner_laws_and_soft_of` proved (chamber, silent, flat, empty-cusp, cyclic
  fields discharged by the accepted rows).
* Unconditional claim closures available now: NONE of the rows closes today (155 needs (C) ← fd:contact;
  165 needs 155 (C); 175 needs 165; 174/176/177 need 155 (C) and G10; 178/183/184 need all of them).
  `provable_now` in the row sense: none; in the clause sense: 155(D) and every assembly.

## 5. Units (byte-identical skeleton copies of Sketch_A.lean; statements frozen; leaves `sorry`; helper prefixes)

| unit | content | leaves | inputs | est. lines / hours |
|---|---|---|---|---|
| **U-CVF** (prefix `cvf_`) | port-ready module `CV/CarrierFloor.lean`: §2 statements, the four bridges, (D) | none | accepted only | 350 / 1 (statement review + port after the floor lane's bundle names are final) |
| **U-SDI** (prefix `sdi_`) | `singleton_D_i_of_floor`: (a) `insert c S` independent, `U(S') = U(S) ∖ {c}`, pieces of `S'` = pieces of `S` ∖ `{c}` (pure graph, ~250); (b) the split of the carrier `q` into `Λ₁, Λ₂ : GeoComponent (insert c S)` and the other carriers unchanged (CV:lem:carriers at `S'`, ~400); (c) `groupedPoly`/`groupedWrithe` factorisation through cor:groupedknot (B) + lc:single-crossing (~300); (d) `f_A = f₁ f₂` by knot parity (~60); (e) rotation additivity + signs (turnlift (ii), uniformrot; ~250); (f) (C)/(D) on each loop and the sum (~150) | 1 → ~6 sub-leaves | 155 (C) as hypothesis; accepted CV rows 136, 138, 139, 142, 145, 153, 158, 160 | 1400 / 10–14 |
| **U-PZ** (prefix `pz_`) | `extreme_pair_zero_of_singleton` and the row `RProof.extreme_pair_zero` | 1 | 165 as hypothesis; accepted `PRE_175_*`, `weight_of_mixed`, `rowTerm_of_mem_Ind` | 150 / 1–2 |
| **U-CVR** (prefix none; fixed names) | `RProof.cv_R := cv_R_of_rows …`, `Bridge.sm_R := SM.sm_R_of_cv_R RProof.cv_R` | 0 | rows 174–177 | 20 / 0.5 |
| **U-FIN** | `SM.corner_laws_and_soft := corner_laws_and_soft_of Bridge.sm_R …` with the corner lane's bundles re-read into `VertexEdgeLawC` etc. (re-shape the Props to their bundles if they differ) | 0 | 183, thm:C-S7, thm:C-soft, cor:C-inherits | 60 / 1 |
| (not this lane) U-GS / U-ET / U-ES | rows 174, 176, 177 | — | 155 (C), G10 | ~1000 each / 3 lanes |

Reviews: one statement review per row module (U-CVF: 155 with the F6 reading list §1; U-SDI: 165; the
fixed-name rows 174–178/183/184 have their statements accepted or dictated — review the INSTANTIATION only).

## 6. Riskiest steps

1. **155 (C) is the only GAP-2 successor in the lane**: everything from 165 downwards waits on
   fd:contact → cf:thm-carrierfloor (C). If the contact lane declares `src_contact` and row 94 late, 165/175
   and the three R rows stall; the bridges here are ready and cost nothing.
2. **Bundle-shape drift** between the memo (assumed here), floor Sketch_A/B and the floor lane's final
   `Statements_FINAL`: only the cast layer of `carrierfloor_B_of_sm` / `carrierfloor_C_of_sm` moves, unless
   (B) is stated on the normalised polygon (FR-CV-155-1) — then CV (B) follows and the reviewer re-reads d3:761–776.
3. **165 on the geo layer**: the carrier split at `insert c S` is the hardest geometric step (the same step
   the corner lane needs for cb:singleton); if the corner lane proves it only on `IsDecomposition`, U-SDI pays
   the full 1.4k. Ask (§7) to share the tier-1 core.
4. **174/176/177 need an RII move and (177) an ambient isotopy through the wall (G10)** — outside this
   design; the frozen bundles do not change, but `RProof.cv_R` is unreachable without them.
5. **184's pending field shapes** (`∃ Generic` of children, κ clause, ℚ multiplier) must match the corner
   lane's bundles or be re-shaped; the theorem `corner_laws_and_soft_of` is robust to that (field types only).
6. **`hn : 3 ≤ n` bookkeeping** in 184's cusp/soft fields (`by have := hf.1; omega`, `by omega` at `n+1`)
   follows `ALawfulData`; a corner-lane statement with a different `hn` derivation is defeq but may need
   `convert`.

## 7. Coordination asks

* Floor lane: keep the memo's (B) reading (record of `L` itself) or say so; export `SM.cf_thm_carrierfloor :
  CarrierFloorData` with the four clause bundles as fields (this lane reads `cf.clauseR` etc.).
* Corner lane: state cb:singleton's geometric core (carrier split at `insert c S`, piece transfer) at tier 1
  (`CrossingGeometry`, as `SM.GeoCarrier` is) so that 165 consumes it; state thm:C-S7 / thm:C-soft /
  cor:C-inherits with the genericity of the children inside the identity (FR-F-184-2) — or tell this lane the
  shape so `VertexEdgeLawC`/`CuspLawC`/`SoftTheoremC` are replaced by their bundles before U-FIN.
* Contact lane: nothing from this lane; 155 (C) consumes only the sl-free bound through the floor lane.
