# PLAN_A — the eight front certificate rows (tools/claims.py rows 76-83), architect A (maximal reuse)

2026-09-14. Deliverables (all under work/drafts/frontrows/, checked with `cd work/lean && lake env lean <file>`,
Lean v4.34.0-rc2, project Mathlib pin): **Statements_A.lean** (254 lines; 0 errors; exactly eight `sorry` = the
row theorems `SM.ng_commutation`, `SM.ng_front_I`, `SM.ng_front_II`, `SM.ng_front_III`, `SM.ng_deletions`,
`SM.ng_circle`, `SM.ng_cusp_skein`, `SM.ng_local_front_bound` — the fixed names of the brief; axiom-policy.json
fixes only `SM.ng_finite_word` among the front rows), **Skeleton_A.lean** (1067 lines; 0 errors; definitions and
bundles byte-identical to the Statements; **36 sorried leaves**, all glue proved, the eight rows assembled;
`#print axioms`: rows 76-82 reach `sorryAx`, the standard three and `SM.lp_lm` (through `P`), row 83 additionally
`SM.ng_finite_word`; `certificate_laws` and `blockPlacement` are sorry-free). Source: reference/SM/sm-3-statesum.tex
(tex lines below); design of record work/reports/front-block-design-FINAL-20260913.md (§2 G1, §3, §5 items 3-6,
§8 risk 3, §9 FR-5/FR-6); AUTHOR_NOTES entries FR-1..FR-7, D-F1..D-F6, "ng:finite-word ACCEPTED", "hinv obligation
closed", "β2 ported"; β2 report work/drafts/front/BETA2_REPORT.md §4, §6 (i)-(iii), §7.

## 1. Decision (a): the reading — every certificate row on `OWord` through `SM.realize`

A closed oriented word `W : OWord` (SM/FrontWords.lean) stands for the front `realize W : PLFront`
(SM/FrontRealize.lean:1243, the grid realization with the standard placement). Printed "front" → `realize W`;
`D(F)` → `(realize W).downCount` (FrontPL.lean:436), `w(F)` → `(realize W).writhe` (:452, the accepted writhe of
`PLFront.diagram`, :361), `s(F)` → `(realize W).sCount` (:458), `d(F) = deg_a P_{S(F)}` (display ng:defect,
sm-3:1896-1898) → `degAZ (P (realize W).diagram)` — a PL front is its own ordinary diagram (wedge cusps are legal
corners), so `S(F) = F.diagram` is the identity rounding (FINAL §2 G1 (ii)); `B(F)` → `(realize W).defect`
(:462). The moves are the accepted word patterns: `IsComm` (FrontWords.lean:418, with the two-strand index shift
:412), `IsTypeI` :425, `IsTypeII` :433 (incl. the right-cusp versions), `IsTypeIII` :441, `IsZigzagDeletion` :450,
`IsCrossedCuspShortcut` :456, `IsCircleDeletion` :463, `IsCuspSkeinStep`/`IsCuspSkein` :475/:483 (bits from the
(t,u) table), lifted to `Pres`/`Del`/`Skein` on `OWord` (:1017-1027). "Deformations through fronts without a singular
event" → `SM.PLFront.Deform` (new, Statements §0): a generic `DeformData` of the diagrams (LinkMoves.lean:462; same
crossing pairs, generic intermediates) all of whose intermediate polygons are nonvertical (no cusp event in the PL
class, where a cusp is an x-reversal vertex).

**Narrowing, stated plainly (FR-5).** Printed rows 76 (first sentence), 77-82 and 83 quantify over arbitrary fronts
of Definition ng:front-domain (sm-3:1825-1841, the smooth class `SmoothFront`, row 73). Lean: 77-82 and the field
`on_words` of 83 are on fronts represented by finite elementary front words — exactly the fronts on which the printed
certificate section computes (sm-3:1904-1919 "Use Rutherford's elementary front words") and the only ones the word
procedure ng:finite-word visits. The printed justification is the second sentence of ng:commutation (sm-3:1924-1925
"Every supplied finite front can be represented by a finite elementary front word"). **Decision:** it is a printed
clause of a row and is KEPT as the field `representation` of row 76, stated on the smooth class (FINAL's
`ng_commutation_word_statement`, strengthened by `s`): every `F : SmoothFront` has a `W : OWord` with the same `s`,
`D`, `w`, whose diagram carries the named record of every rounding `S(F)` (hence `P_{S(F)} = P_{realize W}` by
`presentations`, PolynomialBlock.lean:1177). It is the block's single analytic bridge (76b, FINAL §8 risk 1); row
83's printed clause `on_fronts` is derived from it and `on_words` in 20 lines (`front_bound_of_word_bound`). So rows
76 and 83 close only when 76b lands; rows 77-82 do not depend on it. Fallback recorded (needs Mark's decision, FINAL
§10 item 2): drop `representation`/`on_fronts` and disclose a class narrowing on 76/83/93.

Second disclosed reading: the deformation clause is on the PL class (`PLFront.Deform`, all PL fronts — not only
realizations), not on smooth families; the smooth-class deformation invariance is NOT stated (no consumer uses it:
the descent of row 83 runs on the word chain, and deformations enter only the proofs of ng:deletions and of the
representation). Companion leaf `PLFront.deform_realizeAt`: a change of placement is such a deformation.

## 2. Clause maps (printed clause → field; tex lines)

| row | printed clause (sm-3) | field | Lean reading |
|---|---|---|---|
| 76 | 1922-1923 "Disjoint-gadget commutations ... preserve D, w, d" | `commutation` | `IsComm W W' → D = D ∧ w = w ∧ degAZ P = degAZ P` on `realize` |
| 76 | 1923 "and hence B" | `commutation_B` | `defect = defect` |
| 76 | 1922-1923 "deformations through fronts without a singular event preserve D, w, d" | `deformation` | `PLFront.Deform F F' → ...` (PL class) |
| 76 | 1923 "and hence B" | `deformation_B` | `F.defect = F'.defect` |
| 76 | 1924-1925 "Every supplied finite front can be represented by a finite elementary front word." | `representation` | `∀ F : SmoothFront, ∃ W, s/D/w equal ∧ ∀ S, IsRounding F S → RecordIso S.record (realize W).diagram.record` |
| 77 | 1951 "The front type-I moves preserve B." | `typeI_B` | `IsTypeI W W' → defect = defect` (deletion direction, FR-6) |
| 78 | 1973 "preserve D, w, d" / "and hence B" | `typeII`, `typeII_B` | four variants incl. right cusps (1988-1989) |
| 79 | 1991 "preserve D, w, d" / "and hence B" | `typeIII`, `typeIII_B` | either direction |
| 80 | 2010 "Deleting an empty zigzag lowers s by two" | `zigzag_s` | `(realize W').sCount + 2 = (realize W).sCount` |
| 80 | 2010 "and cannot increase B" | `zigzag_B` | `defect W' ≤ defect W` |
| 80 | 2010-2011 "the crossed-cusp shortcut lowers s by one" / "cannot increase B" | `crossedCusp_s`, `crossedCusp_B` | `l_i σ_i ↦ l_i (!d)`, `σ_i r_i ↦ r_i` |
| 81 | 2047-2048 "Deleting a separated standard front circle with nonempty remainder preserves B." | `circle_deletion_B` | `IsCircleDeletion` (remainder `≠ []` in the definition) |
| 81 | 2048-2049 "A single standard front circle, and any union of such circles, has B = 0." | `standard_circles_B` | `(realize W).IsStandardCircles → defect = 0` (FrontPL.lean:513) |
| 82 | 2077-2080 "For either principal direction ..., B of the earlier branch ≥ min{B other branch, B smoothing}" | `skein_B` | `Skein A A' C → min (defect A') (defect C) ≤ defect A`; `IsCuspSkein` is symmetric so both lines of ng:skein-defect (2158-2163) |
| 82 | 2080-2081 "The smoothing has one fewer singularity" | `smoothing_s` | `sCount C + 1 = sCount A` |
| 82 | 2081-2082 "the principal branches have the same singularity count" | `principal_s` | `sCount A' = sCount A` |
| 83 | 2306-2311 (display ng:front-inequality) on realized words | `on_words` | `w − D ≤ −degAZ P − 1` for `realize W`, `S = F.diagram` |
| 83 | 2306-2311 "For every front F on the domain of Definition ng:front-domain, with the same polynomial evaluated on its actual ordinary cusp rounding" | `on_fronts` | `∀ F S, F.IsRounding S → F.writhe − F.downCount ≤ −degAZ (P S) − 1` (`SmoothFront.defect_nonneg_iff`, FrontSmooth.lean:1524, is this shape) |

Proof displays are companion lemmas, not fields: ng:type-I-counts 1964-1966 (`typeI_counts`), ng:zigzag-counts
2020-2022 (`zigzag_counts_syn`), ng:crossed-cusp-counts 2034-2036 (`crossedCusp_counts_syn`), ng:circle-counts
2064-2067 (`circle_counts_syn`, `circle_d`), the (t,u) table 2107-2118 (`skein_counts_syn`), ng:skein-plus/minus
2137-2142 (`degAZ_skein_pos/neg`).

## 3. Decision (b): quantities and their changes on realizations — the two engines

**Counts engine (syntactic, unit T-cnt).** `(realize W).downCount = W.letters.downCountFrom []` and
`(realize W).writhe = W.letters.writheFrom []` for `W.letters ≠ []` (β2 `realize_downCount` :911, `realize_writhe`
:915 of FrontRealizeCorrespondence.lean; `realize_sCount` :901). A factor replacement `X ++ P ++ Y ↦ X ++ P' ++ Y`
with the same typing effect changes the letter-traced counts only by the factors' own contributions at the cut
`c₀ = run X []` (`counts_replace`, from `downCountFrom_append`/`writheFrom_append`); each pattern's factor contribution
is a finite computation on the symbolic cut `A ++ w ++ R` (`Letter.step_eq_some_iff` FrontWords.lean:159,
`act_window` :192, the `run_*` lemmas :537-880): type I `ΔD = 1, Δw = 1`; II, III, comm `0, 0`; zigzag `Δw = 0`,
`ΔD ∈ {0, 2}`; crossed cusp `Δw = −1` (sign −1 deleted), `ΔD = ±1`; circle `ΔD = 1`, `Δw = 0`; skein `D` common,
`w_A = w_C + σ`, `w_{A'} = w_C − σ`, `σ = ±1` (the FrontWords sanity `decide` examples :340-378 are these facts on
concrete cuts). Nonemptiness of every word involved is proved in the skeleton (`IsTypeI.ne_nil`: the curl needs a
through-strand, so `X ++ Y ≠ []`; β2 `IsZigzagDeletion.ne_nil`; circle by definition; others contain a letter).

**Polynomial engine (geometric, two routes).**
(i) *Disc-local Reidemeister sites on β2 block setups* for II, III, crossed cusp, and I (curl vs zigzag):
`BlockSetup.ofReplace X P Y P' hP hP' hW h` (skeleton, proved) packs the standard placement on the `P` side and the
new `blockPlacement |X| |P| |P'|` (proved `StrictMono`; `PlAgree` by `plAgree_of`, FrontRealizeGeometry.lean:629;
`SameEffect` by `sameEffect_of_replace` :498). Then `B.F = realize ⟨X ++ P ++ Y, hW⟩` definitionally, `P B.F'.diagram
= P (realize ⟨X ++ P' ++ Y, _⟩).diagram` by `P_realizeAt_eq_realize` (FrontRealizeDeform.lean:234, via `P_planar`
PolynomialBlock.lean:604 on β2's `deformData` :182). A site `Nonempty (RIData B.U B.F'.diagram B.F.diagram)` (resp.
RII, RIII) gives `P (realize W) = P (realize W')` by `P_reidemeister_I/II/III` (:605-607) — glue `P_eq_of_R*_site`,
proved. Inside a site: `LocalFrame` = `isDisc_blockRect` :88 + `clean_blockRect` :414 under `ExitsBlock` :393 (every
component has an exterior strand: `X ++ Y ≠ []` for all patterns, shown above); `MoveMatch` = `BlockSetup.outsideMatch`
:1624 + the component bijection (T-arc: components are cycles of `next`; the two blocks connect their boundary slots
identically for RI/RII/RIII — a finite computation with `next_cases` FrontRealizeSlots.lean:965 and `next_ext`
FrontRealizeGeometry.lean:778); arcs = the runs of interior slots from an entering to an exiting boundary slot
(`Arc` LinkMoves.lean:145, `IsArc` :198, `ArcCover` :208; ends on the frontier by `pt_extSlot` :1117, inner points
inside by `piecePt_mem_interior_blockRect_of_int`); `inner_iff` = `crossingPoint_mem_interior_iff` :425; `OverOn`/
`same_over`/height order = `overStrand_crossingOf` (Correspondence :650: the descending strand is over); `BeforeOn` =
order along `next`. (ii) *The named record* (`presentations`, PolynomialBlock.lean:1177; `Diagram.record`
LinkDiagramRecord.lean:500; `RecordIso` LinkRecord.lean:539) for the moves that are NOT Reidemeister moves of the
ordinary diagram: commutation (76), zigzag deletion (80; the empty-factor case β2 §6 (i): `X ++ Y` has no column
for the factor, so no literal outside match — the record sees only `σ` visits and their cyclic order, which are
unchanged), circle deletion (81; `RecordIso (realize W).record (realize W').record.addFree` + `P_addFree`
:1036, `P_before = δ P_after`), and the skein switch (82; `realize A'` vs `(realize A).switch x` — the printed
argument sm-3:2093-2097 "the full named records are identical"; a `Deform` is impossible here because the cusp
vertex must cross the through-strand). Record of a realization (unit T-rec): visits = the two slots of each `σ`
letter (`crossingEquiv` :606, over = `σSlotA`), successor `nextVisit` :258 = first `σ` slot along `next`
(`toSlot_succ` FrontRealizeSlots.lean:1291: the parameter circle IS the `next`-cycle; visit point at parameter 1/2,
`crossingParam_eq_half`; `nextVisit_no_between` :335 + `cycNext_unique` :124 characterize it), twin :413 = the other
slot, `overBit` :470, sign = `sign_crossingOf` :677 (`bit k m = bit k (m+1)`); exterior visits correspond by
`shiftIdx` :469 with `cut_ext`/`letterAt_ext`/`bit_ext` :555-588.

**Degree engine (unit T-deg).** `degAZ` LinkLaurentRing.lean:446, `degAZ_mul` :733 (domain `R`), `degA_add_le`
:431, `degA_aInv` :440, `degA_z` :441, `degAZ_eq_of_spec` :465, `R.delta` :193, `P_ne_zero` PolynomialBlock.lean:793,
`P_crossingFree` :688 (`P = δ^{c−1}`), `P_recursion_pos/neg` :693/:697 (the two solved skein directions of
ng:skein-plus/minus, taking `IsOrientedSmoothing` and the sign of `x`).

## 4. The chain (exact leaf statements are in Skeleton_A.lean; glue proved there)

- **76** `commutation` := `realize_counts_eq_of_syn` (T-cnt-4 `comm_counts_syn`) + `presentations` (T-rec-1
  `comm_recordIso`); `deformation` := U76-1 `Deform.downCount_eq`, U76-2 `Deform.writhe_eq`, `Deform.P_eq` (proved:
  `P_planar (PlanarIsotopic.of_deform ⟨h.toDeformData⟩)`); `representation` := U76-4 `representation_by_word`.
- **77** `typeI_B` := `typeI_counts` (T-cnt-5) + `typeI_P` (proved): curl `l_m σ_{m−1} r_m` vs zigzag `l_m (!d) r_{m−1}`
  (resp. `l_m σ_{m+1} r_m` vs `l_{m+1} d r_m`) on `typeIBlockL/R` (effect equalities U77-1/2
  `run_typeI_*_zigzag`), RI site U77-3 → `P_reidemeister_I`; then the zigzag is an `IsZigzagDeletion` instance →
  T-rec-2 `zigzag_recordIso` → `presentations`.
- **78** `typeII` := T-cnt-6 + `typeII_P` (proved from the four RII sites U78-1..4 on `typeIIBlockLL/LR/RL/RR`, effect
  by `run_typeII_*` FrontWords.lean:587-653); `typeII_B` by `defect_eq_of_counts`.
- **79** `typeIII` := T-cnt-7 + `typeIII_P` (RIII site U79-1 on `typeIIIBlock`, effect by `run_typeIII_aux`/`of_split`
  :686/:724; the other direction by symmetry of the conclusion).
- **80** `zigzag_s`/`crossedCusp_s` (proved: β1 `IsZigzagDeletion.sCount` :1061, `IsCrossedCuspShortcut.sCount` :1066 +
  `realize_sCount`); `zigzag_B` := T-cnt-8 + T-rec-2 (`ΔB ∈ {0, 2}` by `omega`); `crossedCusp_B` := T-cnt-9 + RI sites
  U80-1/2 on `crossedCuspBlockL/R` (`run_crossedCusp_l/r` :801/:814) (`ΔB ∈ {0, 2}`).
- **81** `circle_deletion_B` := T-cnt-10 + `circle_d` (proved: `P_addFree` on T-rec-3 + T-deg-3); `standard_circles_B`
  (proved, leaf-free except T-deg-2): `D = c` by β2 `realize_downCount_eq_c_of_isStandardCircles` (Standard :622; empty
  word via `realize_nil` :1250 + `IsStandardCircles.downCount_eq_c` :603), `w = 0` (`IsStandardCircles.writhe_eq_zero`
  FrontPL.lean:518), `P = δ^{c−1}`, `degAZ δ^{c−1} = c − 1`.
- **82** `skein_B` (proved from `SkeinSite`): for `IsCuspSkeinStep A A' C` the site U82-1 `skein_site` gives `x`, an
  oriented smoothing `D₀` (`OrientedSmoothingData` LinkMoves.lean:713 on `BlockSetup.ofEffect X [l_{m+1} d, σ_m] Y C`
  with `hE` from `run_skein_A/Ctop/Cbottom` :857-880) with `P D₀ = P (realize C)`, `RecordIso (realize A').record
  ((realize A).switch x).record`, and `sign x = w_A − w_C`; with T-cnt-11: `σ = 1` → `P_recursion_pos` → T-deg-4 →
  `omega`; `σ = −1` → `P_recursion_neg` → T-deg-5 → `omega`. The reflected direction `IsCuspSkeinStep A' A C` uses the
  site U82-2 `skein_site_refl` (the crossing is the `σ_{m+1}` of `A`'s factor `l_m σ_{m+1}`) and the same counts with
  `σ ↦ −σ`. `smoothing_s`/`principal_s` proved (β1 `IsCuspSkein.sCount` :1081).
- **83** `on_words` (proved): `certificate_laws` builds `(wordMovesOf (sCount ∘ realize) (defect ∘ realize)
  OWord.IsStandardCircleBase).Laws` — `pres_B` from 76.`commutation_B`, 77, 78.`typeII_B`, 79.`typeIII_B`; `del_B`
  from 80 and 81.`circle_deletion_B`; `skein_B` from 82; `pres_s/del_s/skein_s` from β2 `wordMoves_pres_s/del_s/skein_s`
  (Correspondence :1000-1028, definitionally the same `Moves` fields); `base_B` from 81.`standard_circles_B` +
  `realize_isStandardCircles_of_base` (Base :566) — then `SM.ng_finite_word_bound` (FrontInterfaces.lean:499; the
  axiom :480 through `ng_finite_word_finiteWordStatement` :492 and `word_bound_of` FrontWords.lean:1237). `on_fronts`
  (proved): `front_bound_of_word_bound` = FINAL's `localFrontBound_of`, from `representation` and `presentations`.

## 5. Unit split (36 leaves; Lean lines; one prover per unit unless noted; calibration FINAL §7: geometric
construction units carry a ×1.5-2 tail)

| unit | leaves | consumes | est. lines |
|---|---|---|---|
| T-cnt | `downCountFrom_append`, `writheFrom_append`, `counts_replace`, `comm_counts_syn`, `typeI/II/III_counts_syn`, `zigzag/crossedCusp/circle_counts_syn`, `skein_counts_syn` (11) | FrontWords `run_*`, `step_eq_some_iff`, `act_window`; β2 `downCountFrom_nil_eq_sum` :821 optional | 700-1000 |
| T-deg | `degAZ_delta`, `degAZ_delta_pow`, `degAZ_delta_mul`, `degAZ_skein_pos`, `degAZ_skein_neg` (5) | LinkLaurentRing `degAZ_mul`, `degA_add_le`, `degA_eq_degAZ`, `degAZ_eq_of_spec`, `coeffAt` | 200-350 |
| T-rec (critical path: 76, 77, 80, 81, 82) | `comm_recordIso`, `zigzag_recordIso`, `circle_recordIso_addFree`, and the record half of `skein_site`/`skein_site_refl` (3 + shared) | traversal bridge (`toSlot_succ`, `traversalKey`, `crossingParam_eq_half`, `nextVisit_no_between`, `cycNext_unique`); visits ≃ `σ` slots (`crossingEquiv`); exterior correspondence (`shiftIdx`, `next_ext`, `cut_ext`); block traversal per pattern (`next_cases`, `nextPair_*`); `Record.addFree` (PolynomialBlock :911), `switchRecordIso` :686 | 2200-3200 (shared core 1400-2000; per-pattern traces 150-250 each) |
| T-arc (inside U77/78/79/80 sites; one shared module first) | — | `Arc`/`IsArc`/`ArcCover`; `MoveMatch` component bijection from block traces; `BeforeOn`/`OverOn` via `visitPt_over/underVisit_crossingOf`; `pt_extSlot`, `piecePt_mem_interior_blockRect_of_int`, `clean_blockRect`, `crossingPoint_mem_interior_iff` | 900-1300 |
| U76 | `Deform.downCount_eq`, `Deform.writhe_eq`, `deform_realizeAt` (3) | `DeformData.crossings/generic`, `cusp_det_ne_zero` FrontPL:203, IVT/connectedness on `[0,1]` for sign constancy, `withVertices_vpath` Deform:89, `nonvertical` Realize:1213 | 700-1000 |
| U76b | `representation_by_word` (1) | FrontSmooth, FrontRecordBridge, FrontGeomModel; PL model of a smooth front + vertical sweep | 7500-11000 (last; ~40% in horizon) |
| U77 | `run_typeI_left/right_zigzag`, `typeI_site_left/right` (4) | T-arc, `BlockSetup.ofReplace` | 500-800 |
| U78 | `typeII_site_ll/lr/rl/rr` (4) | T-arc; `overStrand_crossingOf`, `sign_crossingOf` | 1200-1800 |
| U79 | `typeIII_site` (1) | T-arc; three arcs, `BeforeOn` reversal | 600-900 |
| U80 | `crossedCusp_site_l/r` (2) | T-arc | 500-800 |
| U82 | `skein_site`, `skein_site_refl` (2; each two smoothing sites `C_top`/`C_bottom`) | `OrientedSmoothingData`, `BlockSetup.ofEffect`, T-arc, T-rec (switch record) | 1200-1600 |
| **plannable core (all but U76b)** | 35 leaves | | **≈ 9,700 (8,700-12,750)** ≈ 70-95 prover agent-hours at 7-8 h/kloc |

Order: T-cnt ∥ T-deg ∥ T-rec-core ∥ T-arc-core (4 lanes) → per-pattern traces/sites (U79, U78, U80, U77 need
T-arc; U80-zigzag, U81, U76-comm need T-rec; U82 needs both) → U76 deformation → 83 closes automatically (already
assembled) → U76b last. Row acceptance order: 79, 78, 80, 81, 77, 82 (each independent of 76b), then 76 and 83 together.

## 6. Decision (c): row 83 and the `Laws` it consumes

`on_words W` is `0 ≤ (realize W).defect` unfolded. The instance `certificate_laws` (skeleton, sorry-free given the
seven bundles) supplies the seven `Moves.Laws` clauses for `wordMovesOf (fun W => (realize W).sCount)
(fun W => (realize W).defect) OWord.IsStandardCircleBase` — the axiom's own shape (`ng_finite_word_bound`), so
neither `finiteWordStatement_wordMoves_of` nor `SM.wordMoves` is needed. `base_B` uses the accepted forward bridge
`realize_isStandardCircles_of_base` (the open converse, β2 §7 item 1, is NOT needed). The `s`-clauses are β2's
`wordMoves_*_s`, which already handle the empty word (`realize [] = standard circle`, `s = 2`; the empty word is
isolated under every move). Rows 76-82 are consumed only through their `_B`/`skein_B`/`standard_circles_B`/
`circle_deletion_B`/`zigzag_B`/`crossedCusp_B` fields.

## 7. Decision (d): fidelity risks to record (AUTHOR_NOTES before the rows are stated)

- **R-1 (class narrowing on the certificate rows, FR-5).** Rows 77-82 and `on_words` are on realized words; the
  printed rows are on fronts. Kept faithful through the printed second sentence of ng:commutation as the field
  `representation` (76) and `on_fronts` (83). Consequence: 76 and 83 cannot be accepted before 76b. Reviewers of
  77-82 must be told the binder is `OWord` by design (D-F1/FR-5), not an oversight.
- **R-2 ("represented by").** Read as `s`, `D`, `w` equal and the realization's diagram carrying the record of every
  rounding `S(F)`; the printed proof (1938-1947) constructs the word by reading vertical cuts of a perturbed front —
  a representation up to a deformation without singular event, which preserves exactly these data (row 76 first
  sentence). A reviewer may ask for "the same front up to deformation"; the record reading is what every consumer uses.
- **R-3 (deformation clause on the PL class).** `PLFront.Deform` is the PL rendering; smooth families are not stated.
  Disclosed in the row docstring; the smooth-class analogue is unused by consumers.
- **R-4 (identity rounding).** `d(F) = deg_a P_{S(F)}` with `S(F) = F.diagram` on PL fronts (FR-1's polygonal reading
  of "the resulting ordinary diagram"); ng:smoothing-record (row 74) makes the choice of rounding immaterial on the
  smooth side (`SmoothFront.defect_eq`, FrontRecordBridge.lean:378), which is where `on_fronts` lives.
- **R-5 (deletion directions only; type II right-cusp versions).** `IsTypeI`/`IsTypeII` are the deletion patterns
  (FR-6, sm-3:2278-2279); the printed lemmas speak of "the moves" — the creation direction is the same equality read
  backwards for 77-79 (equalities), and is not needed for 80 (inequalities in the deletion direction, as printed).
- **R-6 (curl vs zigzag detour in 77).** The printed proof deletes the monogon directly; the Lean chain compares the
  curl with the crossing-free zigzag (RI) and deletes the zigzag by the record (β2 §6 (i): an empty factor has no
  literal outside match). Same `P` value; disclosed as a proof device, not a statement change.
- **R-7 (skein via the record, not a literal switch).** `realize A'` is not `(realize A).switch x` (different
  shadows); the identification is a `RecordIso` (printed 2093-2097). `IsSkeinTriple` (D3: `D₋` literally the switch)
  is used exactly as `P_recursion_pos/neg` require.
- **R-8 (statement strength).** `skein_B` for all triples of the symmetric `IsCuspSkein` gives both printed
  inequalities; `standard_circles_B` is on realizations (not on arbitrary PL fronts: `D = 1` per component is a
  planar fact proved by β2 on the grid); `zigzag_s`/`crossedCusp_s` are exact (`+2`, `+1`) as printed.
- **R-9 (effort tail).** T-rec and T-arc are new geometric-combinatorial infrastructure (β2 §6 (ii)-(iii) open
  items); calibration: the smoothing gate landed at 5× its estimate. Mitigation: build the two shared cores first,
  keep every pattern site a separate leaf, accept rows as their leaves close (79, 78 first).
- **R-10 (76b).** 7.5-11k lines, ~40% in horizon (FINAL §8 risk 1); if it stalls, 76/83 stay `implemented` with one
  named open leaf each (`representation_by_word`), and fd:ng-bound (93) waits — or Mark approves the fallback of §1.
