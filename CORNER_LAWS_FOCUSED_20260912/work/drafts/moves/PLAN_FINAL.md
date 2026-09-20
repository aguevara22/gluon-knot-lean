# PLAN FINAL — the moves toolkit (D-RM-1): judge's decision, constructor statements, avoidances, instantiation plan, units

Judge (subagent), 2026-09-15 ≈ 18:25 UTC / 2:25pm ET, from `work/drafts/moves/DESIGN_A.md` + `Sketch_A.lean`
(architect A, constructor architecture) and `DESIGN_B.md` + `Sketch_B.lean` (architect B, consumer-driven
minimality).  Both sketches re-checked by the judge (`cd work/lean && lake env lean <file>`, exit 0): Sketch_A
0 errors / 8 `sorry`; Sketch_B 0 errors / 3 `sorry`.  Also read: AUTHOR_NOTES "Reassessment note … D-RM-1"
(17:24Z); U_S7G_REPORT §0; U_R174_REPORT §4–§5; U_R176_REPORT §5; U_R177_REPORT "Interface Props" / "What
remains"; the interface Props in the unit files (`s7g_switch_value_of_rii`/`s7g_value_of_ri` U_S7G.lean:565/575,
`gsc_fulltwist_triple` U_R174.lean:926 and `gsc_moves.fulltwist` :1086, `est_PortData.port` U_R176.lean:878 and
its consumer `est_omega1_eq_of_port` :915, `esc_MoveData` U_R177.lean:1118 and its consumer :1365-1374);
SM/LinkMoves.lean (`IsDisc`, `Arc`, `IsArc`, `ArcCover`, `OutsideMatch`, `Clean`, `MoveMatch`, `ReparamData`,
`deform`, `PlanarIsotopic`, `RIData` :569, `RIIData` :599, `RIIIData` :639, `OrientedSmoothingData` :713);
SM/Smoothing.lean (header, §§0'–9, `smoothDiagram`, `smoothDiagram_record`, `exists_smoothing_record_visit`);
SM/MarkedProducts.lean (`restrictCrossings` :210, `BlockSupply` :245, `two_component_row` :323/381,
`product_of_blockSupply` :4865, `lowest`/`blocks` :4941/4947); SM/SingleCrossing.lean:155; SM/CBProducts.lean:1358,
:1815-1840; CV/GroupedKnot.lean:655-706 (`blockSupply`), :778 (`carrierDiagram` = `geoPositiveLift`);
CV/FullTwist.lean:188-215; CV/Axioms.lean:260; RProof/GenericTransport.lean (`G11_Config` :111,
`G11_core_statement` :190, `G11_Params` :235, unit headers, the positivity footprint of D8/E, Unit F :10263);
SM/Curl.lean:477-500 (`KinkLocation`, `KinkInsertion`); SM/CS3.lean:1166; SM/LinkRecord.lean (`switch` :655,
`crossingCount`, `writhe`, `RecordIso.crossingCount_eq/writhe_eq`); SM/LinkDiagramRecord.lean (`record_sgn`,
`record_crossingCount`, `record_writhe`, `switchRecordIso` :686, `IsRealizable` :718).

Deliverables (this directory; nothing written under work/lean):
- `Statements_FINAL.lean` — the fixed statements.  `cd work/lean && lake env lean ../drafts/moves/Statements_FINAL.lean`:
  0 errors; exactly 5 declarations use `sorry` = the 5 leaves of §5 (`exists_rii_deletion`,
  `exists_bigonData_of_triangle`, `BigonData.reducedRecord_counts`, `Record.restrictCrossings_switch`, `G11_core_sw`).
  PROVED: the instantiation glue of all four consumers (`s7_rii_witnesses`, `s7_switch_value_of_bigon`,
  `gsc_fulltwist_of_bigon`, `est_port_weak_of_bigon`, `fulltwist_skein_of_port_weak`,
  `fulltwist_coefficient_of_port_weak`, `esc_rii_after_smoothing_of_bigons`, `esc_switch_riii_of_chain`), the
  companions (`rii_deletion_counts`, `reducedRecord_componentCount`) and the two avoidance lemmas
  (`two_component_row_of_recordIso`, `curl_block_value`).
- this file.

## 0. Verdict: **B wins** — coverage 8 / feasibility 8 / minimality 9 = **25** vs A coverage 6 / feasibility 6 / minimality 5 = **17** — with A's grafts (§1b, §3, §5 process)

| aspect | A | B | decision |
|---|---|---|---|
| geometric frame | vertex-CHAIN move on the SAME shadow type (`moveVertices` = `deform` with a one-way crossing inclusion), identity outside match; needs flat subdivision vertices `p, q` first (Unit S: `exists_subdivide_reparam` on an arbitrary diagram, Unit E: parameter existence) | vertex-RUN deletion: the run `M₁…M_j` replaced by `M' ∈ (p,y)` on the entering edge and the exit point `q`; `k − j + 2` vertices; outside match = relabelling with the two cut pieces rescaled (Smoothing's `cutStartS`/`cutEndT` pattern); disc `cthickening (ρ₀/2) K` | **B**: no subdivision, no Reparam, no new units S/E, the reduced diagram agrees with `D` outside `U` LITERALLY, so 174's `gsc_fulltwist_triple` is discharged verbatim (A needs the FR-A-2 interface edit or +1.2–1.8k lines) |
| record clause | NEW op `Record.erase S hS` (a `Finset` of occurrences, pair-closed) — definitionally the accepted `restrictCrossings` with the keep set encoded differently | the ACCEPTED `Record.restrictCrossings keep` (MarkedProducts:210; keeps every circle: `componentCount_restrictCrossings` is `rfl`); consumers compose with the accepted `restrictCrossings_iso_of_recordIso` (CBProducts:1358) | **B**; A's companions `eraseTwo_crossingCount` / `eraseTwo_switch` GRAFTED as `BigonData.reducedRecord_counts` / `Record.restrictCrossings_switch` (leaves, U-M6) |
| 110 curl (RI) | kink INSERTION on the polygonal lift `D₁` (pattern K, `exists_ri_insertion`, U-K 1.0–1.4k + a `KinkSite` instantiation + Unit S ×2).  DEFECT: the record clause `Dp.record.eraseCrossing kink ≅ D₁.record` does not fix the kink's cyclic POSITION (Curl's accepted `KinkLocation.gap` / `KinkInsertion.oldVisit` carry exactly that clause), so `inst_110_curl_avoidance`'s `hK` — universally quantified over every insertion — cannot be discharged by a consumer whose `K` has its curl at one position | RECORD level, PROVED sorry-free: `two_component_row_of_recordIso` (`SM.lowest.two_component_row` reads the curl INSIDE `knotRestrict`) + `curl_block_value` (`SM.blocks.product` + `single_crossing.one_crossing`: a single-self-crossing block has value 1).  Consumer supplies a `BlockSupply` (~0.8–1.2k) | **B**: this is the printed proof's own reading (sm-4:857-866 "the deletion of the curl `y` … is that smoothing with the triangle discarded"); A's pattern K is kept only as the FALLBACK (§6 R6) with the positional clause added |
| 177 (4) RIII | `exists_riii_of_heightOrder` (new `HeightOrder` structure over a strand embedding `ι`): output `∃ M₀ M₁, Reparam D M₀ ∧ RIII M₀ M₁ ∧ homfly M₁ = homfly D` — NO record clause.  DEFECT: `inst_177_switch_riii`'s `hrec` quantifies over ALL `M₀, M₁` with `Reparam D M₀ ∧ RIII M₀ M₁` (any RIII site anywhere on `D`), undischargeable | `G11_ConfigSw` + `G11_core_sw_statement` = `G11_core_statement` verbatim with `D₀^{sw}` (the σ-twisted visit bijection `Ψ` included) → consumable by the G11 Unit-F pattern; `esc_switch_riii_of_chain` PROVED | **B**; A's process point GRAFTED: refactor G11's D8/E to take the six local over bits as a parameter (statement-neutral) BEFORE re-deriving |
| 177 (6) | `BigonChain` with `r = 2` (chain = the smoothing arc `{s⁻, t⁺}`) on planar-isotopic copies of the switched smoothings; `inst_177_rii_after_smoothing` PROVED | `BigonData` with `j = 2` (run = `s⁻, t⁺`), `esc_rii_after_smoothing_of_bigons` PROVED; ∃-form interface `esc_rii_after_smoothing_weak` | same reading; **B's** (no planar isotopy needed) |
| interface edits | FR-A-1 (176 port), FR-A-2 (174 AND 176: planar-isotopic start — caused by the subdivision), FR-A-3 (177 ∀→∃) | F-176-1 (port), F-177-1 (∀→∃) | **B**: two edits, both NECESSARY (the 176 literal is false, the 177 ∀ unrealisable — both architects agree); A's FR-A-2 is an artefact of its frame |
| itemised estimates | toolkit 9.8–13.6k (7 units) + instantiations 6.5–9.7k; Unit T at 2–3k is below B's 4.5k for the same content and excludes the G11 refactor; everything 28–44k | constructor 8.0k (8 units) + `G11_core_sw` 4.5k + sites 6.9k + `hrec` transports 3.2k; everything 34–41k | **B's** table, judge's correction: constructor 8–10k (Smoothing = 8.2k for a HARDER replacement, but M4/M6 are the known sinks); `G11_core_sw` 4.5–6.5k (positivity footprint measured, §6 R2) |
| sketch evidence | 433 lines, 8 `sorry`; instantiations PROVED from the leaves; `Record.erase` compiles | 339 lines, 3 `sorry`; instantiations, ledger adapters and BOTH avoidances PROVED sorry-free | both adequate; B's is the port-ready skeleton |

Reasons in one paragraph.  A found a genuinely elegant frame (same shadow type, identity outside match, one
record op for three patterns) and its fidelity list is careful, but the frame forces a flat subdivision that
(i) needs two extra units (S, E) with no library precedent beyond the positive single-polygon case
(CS3:1166) and no `Reparam → RecordIso` lemma anywhere (grep), (ii) pushes cost onto every consumer (each
site must be rebuilt on the subdivided copy and transported back), and (iii) changes a 174 interface that B
discharges verbatim; and two of its three non-RII statements (`exists_ri_insertion`, `exists_riii_of_heightOrder`)
are under-specified in exactly the clause the consumers need (the kink's position; the σ-twisted occurrence
bijection), so their instantiation lemmas carry hypotheses no consumer can prove.  B did what D-RM-1 asked:
ONE typechecked RII-deletion constructor whose output discharges `gsc_moves.fulltwist` verbatim, the 110 bigon
hypotheses, and the (necessarily weakened) 176 port by instantiation; it read the R-I step at the record level
with two PROVED lemmas, the reading the printed proof itself takes; and it copied the accepted G11 core
statement for 177 (4) instead of inventing a new one.  B's gaps — no companions (counts/writhe), no
switch/restriction commutation for the 110 consumer, the 176 ledger re-base only described — are filled here by
A's grafts and one judge's lemma (`fulltwist_coefficient_of_port_weak`, PROVED: the 176 re-base is ONE call).

### Scores (1–10)

| | A | B |
|---|---|---|
| COVERAGE (discharges every interface by instantiation, or names what stays open) | **6** — RII: 110/174/176/177(6) covered by `BigonChain` (r ≥ 1); RI: `inst_110_curl_avoidance` undischargeable as stated (position); RIII: `inst_177_switch_riii` undischargeable as stated (∀ M₀ M₁); 174 needs an interface edit; open items named honestly | **8** — 110 `hR/hrec`, 174 `fulltwist` VERBATIM, 176 in the (only possible) weak form, 177 (6) in ∃-form, 177 (4) via the exact `G11_core_statement` shape; open: the 177 (6) `j = 2` sites and the reduced-smoothed-record lemma are described, not stated; companions missing (grafted) |
| FEASIBILITY (typechecked statements; honest itemised estimates vs Smoothing 8.2k / G11 11k) | **6** — 8 leaves typecheck; the toolkit total is honest but Unit T (2–3k) is under-estimated and the hidden consumer costs (subdivision transport, Reparam records) are not itemised; the identity-match saving in `MoveMatch` is real (~0.5k) but is eaten by Units S+E (1.8–2.5k) | **8** — 3 leaves; 8 units with a dependency order; the constructor estimate (8.0k) is at Smoothing's scale for a simpler replacement (no component change, 4 strand kinds vs 7) but M4/M6 are where Smoothing and G11 spent 3k each — judge widens to 8–10k; `G11_core_sw` 4.5k is supported by the measured positivity footprint (§6 R2) |
| MINIMALITY (faithful avoidances = the printed proofs' own record-level readings) | **5** — a new record op duplicating an accepted one; RI traded for RI (insertion for deletion); a new `HeightOrder` abstraction; two extra units; one avoidable interface edit | **9** — one constructor, deletion only; RI avoided by two accepted rows exactly as sm-4:857-866 reads it; G11 reused with the minimal generalisation (one switched local crossing); two necessary interface edits |

## 1. Chosen statements (`Statements_FINAL.lean`; exact text there)

### 1a. The constructor (B, verbatim)
```
structure BigonData (D : Diagram)      -- i, a, j ≥ 1, j+3 ≤ k, s, y, z, hy, hz, run_free, no_io, same_over,
                                       -- ty tz tsy tsz + edgePt specs, K convex compact, run_mem, in_iff, out_iff, s_iff, clear
BigonData.keep  : Set D.record.Crossing := {c | c ≠ crossingOf (overVisit y) ∧ c ≠ crossingOf (overVisit z)}
BigonData.reducedRecord : Record := D.record.restrictCrossings B.keep
theorem exists_rii_deletion (D) (B : BigonData D) :
  ∃ D', RII D' D ∧ D'.componentCount = D.componentCount ∧ Nonempty (RecordIso D'.record B.reducedRecord)   -- LEAF
theorem exists_bigonData_of_triangle (D i a) (hk : 4 ≤ k) (s y z) (hy : y.val = {⟨i,a⟩,s}) (hz : z.val = {⟨i,a+1⟩,s})
  (same_over) (clear : ∀ u ≠ ⟨i,a⟩, ⟨i,a+1⟩, s, Disjoint (seg u) (convexHull {pt y, P (a+1), pt z})) :
  ∃ B : BigonData D, B.i = i ∧ B.y = y ∧ B.z = z                                                            -- LEAF
```
### 1b. Record companions (grafts from A; leaves of U-M6)
```
theorem BigonData.reducedRecord_counts : B.reducedRecord.crossingCount + 2 = D.record.crossingCount ∧
  B.reducedRecord.writhe + (sgn (overVisit y) + sgn (overVisit z)) = D.record.writhe                        -- LEAF
theorem Record.restrictCrossings_switch (ρ) (S) (v) (hv : ρ.CrossKeep S v) :
  Nonempty (RecordIso ((ρ.switch v).restrictCrossings S) ((ρ.restrictCrossings S).switch ⟨v, hv⟩))         -- LEAF
theorem rii_deletion_counts : ∃ D', RII D' D ∧ … ∧ card D'.Crossing + 2 = card D.Crossing ∧
  D'.writhe + (sign y + sign z) = D.writhe                                                                  -- PROVED
```
### 1c. Row 177 (4) (B, verbatim)
```
structure G11_ConfigSw (k)   -- G11_Config minus `trans`, plus `sw : Fin 3`, `trans_sw` (switched over-order transitive)
G11_ConfigSw.D₀sw := ((Shadow.single comp).positiveDiagram gen).switch xs
def G11_core_sw_statement C := ∃ D₁ Ψ, componentCount = 1 ∧ homfly D₁ = homfly D₀sw ∧ twin ∧ overBit ∧ sign ∧
  (VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔ D₀sw.VisitBetween (σD u) (σD v) (σD w))        -- = G11_core_statement at D₀sw
theorem G11_core_sw (C) : G11_core_sw_statement C                                                           -- LEAF
```
### 1d. Instantiation glue (all PROVED)
`s7_rii_witnesses`, `s7_switch_value_of_bigon` (110); `gsc_fulltwist_of_bigon` (174, the `fulltwist` field verbatim
via `moves_fulltwist_triple` = `gsc_fulltwist_triple`); `est_port_weak`, `est_port_weak_of_bigon`,
`fulltwist_skein_of_port_weak`, `fulltwist_coefficient_of_port_weak` (176); `esc_rii_after_smoothing_of_bigons`,
`esc_rii_after_smoothing_weak` (177 (6)); `esc_switch_riii_of_chain` (177 (4)).

## 2. The avoidance lemmas (B; PROVED sorry-free; axioms standard + `lp_lm` through `presentations`/`P`)

* `two_component_row_of_recordIso (DA) (h2 : c = 2) (i j) (hij) (K₁ K₂) (h₁ : knotRestrict i ≅ K₁) (h₂) :
  zRow (-1) (P DA) = a^{−2ℓ} (a − a⁻¹) ([z⁰] P K₁ · [z⁰] P K₂)` — `SM.lowest.two_component_row` + `presentations`.
  The curl `y` of `D_A` stays inside `knotRestrict 1`; the ROW never deletes it (the MarkedProducts 323/381 check
  D-RM-1 asked for: confirmed, the field takes ANY two-component `D`).
* `curl_block_value (ρ) (C) (hB : BlockSupply ρ C) (D) (hD : D.record ≅ ρ) (H₀) (x₀) (h1 : (C H₀).Γ.c = 1)
  (hx : ∀ y, y = x₀) : P D = ∏_{H ≠ H₀} P (C H)` — `SM.blocks.product` + `single_crossing.one_crossing`.
* How 110 closes the `[z⁰]` identification without RI (U110-B/H, ≈ 0.8–1.2k lines): `ρ` := the record of
  `component₁(D_A)` = `D₁.record` with the curl inserted (from the smoothing record clause).  Its interlacement
  graph = that of `D₁.record` plus the isolated vertex `{y}` (the two occurrences of `y` are adjacent; a pure
  `Record.interlacementGraph` lemma, ≈ 300 lines).  `BlockSupply ρ C`: for `H ≠ H₀` the piece diagrams of the
  half contact carrier (`CV.GroupedKnot.blockSupply` :671 / `CBProducts.product_of_chain`'s family :1827 — `D₁`
  is a `positiveLift`/`geoPositiveLift`), for `H₀` an explicit one-crossing one-circle polygon (≈ 300 lines, or
  `IsRealizable` from the smoothing witness itself: `knotRestrict` of `D_A` restricted further is not needed —
  the block `{y}`'s restricted record is realised by ANY one-crossing knot diagram of sign `+1`).  Then
  `curl_block_value` for `component₁(D_A)` and `blocks.product` for `D₁` (same leaves) give
  `P (knotRestrict 1) = ∏_{H ≠ H₀} P (C H) = P D₁ = Q₁`.  Writhe: `w_H = w₁ + w₂ + 2ℓ + 2` already counts `y`.
* NOT avoidable (both architects, judge agrees): the RII at 110's wall (sm-4:614-620 IS the move), 174's G10
  deletion, 176's port, 177 (4) (records differ by `σ`), 177 (6) (no record-level RII lemma; policy forbids
  proving RII invariance from the skein — U_S7G §0.4a).

## 3. Fidelity: constructors are library material; where the interface Props are too strong

No row statement changes.  Library homes: `SM/BigonDeletion.lean` (after `SM.Smoothing`; the constructor, the
triangle builder, the record companions) and `RProof/GenericTransportSw.lean` (`G11_core_sw`).  Interface Props are
unit-internal glue (D-F11); the following are proposals to the consuming units:

* **F-176-1 — `est_PortData.port` (U_R176.lean:878) is STRONGER THAN DELIVERABLE, indeed false.**
  `ReflTransGen RII ((carrierDiagram q').switch y) (carrierDiagram q)` relates lifts on DIFFERENT polygons
  (`E.curve t'` vs `E.curve t`); `RIIData.out : MoveMatch` contains `OutsideMatch.eval_eq` (identical traces
  outside the disc), so no RII chain moves a trace, and the two polygons differ along whole edges.  Edit: the field
  becomes `est_port_weak (carrierDiagram q') (carrierDiagram q) y` (= `∃ D₀', ReflTransGen RII (D₊.switch y) D₀' ∧
  homfly D₀' = homfly D₀`, the 174 unit's reading of lem:fulltwist (T2) through ax:gausscode).  Ledger: in
  `est_omega1_eq_of_port` (:915) replace the ONE call `CV.fulltwist_coefficient … D.port rfl rfl hd` by
  `fulltwist_coefficient_of_port_weak … D.port rfl rfl hd` — PROVED in Statements_FINAL with exactly
  `fulltwist_coefficient`'s conclusion; the rest of the ledger is byte-identical (≈ 5 lines changed, not 80).
* **F-177-1 — `esc_MoveData.rii_after_smoothing` (U_R177.lean:1123) quantifies over ALL oriented smoothings.**  An
  arbitrary `OrientedSmoothingData` has arbitrary polygonal arcs in an arbitrary clean disc; the bigon `{y, z}` on
  such a smoothing has an uncontrolled side.  Edit: the field becomes `esc_rii_after_smoothing_weak D_H D_L x_H x_L
  pyH pyL` (ONE pair of smoothings WITH record clauses).  Ledger: at U_R177.lean:1365-1374 obtain `D_H0, D_L0` from
  the interface instead of `exists_smoothing_record_visit` (the record clauses replace the discarded `-` there);
  `knot_after_two`/`three_components` may stay `∀` (record-level, they hold for every smoothing through the record
  clause) or be matched to the same witnesses; ≈ 100 lines.  Both architects propose this edit.
* **F-110-1** — the R-I curl is read at the record level (§2); U110-B/H supply the `BlockSupply`.
  `s7g_value_of_ri` stays available but is not on the route.
* **F-174 — none.**  `gsc_moves.fulltwist : gsc_fulltwist_triple (D_L) (D_H) D₀ qx` is discharged VERBATIM by
  `gsc_fulltwist_of_bigon` given `hq`, the two component counts (`carrierDiagram` is a one-component
  `geoPositiveLift`), a `BigonData ((carrierDiagram (τ qAB)).switch qx)` and `hrec`.  A's FR-A-2 (planar-isotopic
  start) is NOT needed.
* **Record clause vs the printed words.**  "The remaining diagram has the same complete decorated record as
  `D_L`" (sm-4:600-606) = `RecordIso D'.record (D.record.restrictCrossings keep)` composed with the consumer's
  `≅ D_L.record`; `restrictCrossings` keeps every circle, drops the four occurrences (`reducedRecord_counts`), and
  takes the first-return successor (def:gauss-record's forward successor on the retained occurrences).
* **`K` closed vs the printed open emptiness.**  `BigonData.clear` asks every other edge to miss the CLOSED
  region; for the printed sites `K` is the closed contact triangle, whose boundary carries only the three local
  strands — `G11_Config.clear_edge` (GenericTransport:140) is exactly this closed form, derived from the frontier
  clause + the vertex clause by `G11_preconnected_meets_frontier`; the same derivation serves 110/174/176.
* **Axioms.**  The constructor and `G11_core_sw` are standard-axiom (as Smoothing, G11); the glue adds `lp_lm`
  through `P_reidemeister_II`/`presentations`/`P` and `lit_homfly` through `homfly` — the accepted rows' footprint.

## 4. Per-consumer instantiation plan

### 4.1 Row 110 (bigon branch + curl) — corner lane, U110-G's two NO-GO witnesses
* Site: `D := (positiveLift hn hP S q hS).switch x` (LinkPositiveLift:596), `i = 0`, `a` = the label of the corner
  polygon's edge INTO the wall vertex `M`, `j = 1`, `s` = the remote edge, `y = x` (the switched crossing on
  `(M−1, M)`), `z` = the crossing on `(M, M+1)`; `K` = the closed contact triangle `conv{pt x, M, pt y}`.
  `same_over`: after switching the positive `x`, `s` is over at both (`switch_overStrand_self` + `positiveLift_isPositive`
  + the printed sign table sm-4:614-618).  `clear`: U110-A's wall data (no other edge or vertex meets the contact
  triangle) in the closed form (§3 last bullet).  Builder: `exists_bigonData_of_triangle`.  ≈ 0.8k.
* `hrec : B.reducedRecord ≅ D_L.record`: `B.reducedRecord = ((lift).switch x).record.restrictCrossings keep`
  `≅ ((lift).record.switch v).restrictCrossings keep'` (`switchRecordIso` + `restrictCrossings_iso_of_recordIso`)
  `≅ ((lift).record.restrictCrossings keep').switch v'` (`Record.restrictCrossings_switch`, §1b) `≅ D_L.record`
  (U110-A's persistent-visit-order transport: `VertexLocalData.visit_order`; the switch bit of `x` is now on `D_L`'s
  side of the wall as the printed sign table says).  ≈ 1.0k (U110-A/B material).
* Value: `s7_switch_value_of_bigon` gives `P (lift.switch x) = P D_L` = `s7g_switch_value_of_rii`'s conclusion.
* Curl: §2 (BlockSupply, ≈ 0.8–1.2k, U110-B/H).  No `RIData`.

### 4.2 Row 174 (G10 move) — `gsc_moves.fulltwist`
* Site: `D := (carrierDiagram hn hG' hSm' (τ qAB)).switch qx`, the `m`-corner of the corner polygon (a selected
  visit, `geoCornerMark`), entering/exiting edges along `ℓ₃`/`ℓ₁`, `s` = the `ℓ₂` strand through the adjacent
  visits `w(ℓ₂), x(ℓ₂)` (R-LOC (2) — this is `run_free` for `j = 1` vacuously and `s_iff`), `K` = the triangle
  `conv{x_pt, m_pt, w_pt}`; `clear` from R-LOC (2)–(4)/lem:guardconst via `GT_Endpoint.adj1..3` and G11 Unit A's
  "edges of the corner polygon inside the edges of `P`" toolkit (GenericTransport 8780–10263, reusable).
  `same_over` after switching `qx`.  ≈ 1.2k.
* `hrec : B.reducedRecord ≅ (carrierDiagram hn hG hSm qAB).record`: the wall transport of the carried marks
  (`GT_homfly_wall_gen` pattern, G11 Unit F without transpositions; `GT_owner_transport` on good marks).  ≈ 1.2k
  (U-174 item 2 material, partly shared with `omega_wall`).
* Then `gsc_fulltwist_of_bigon` closes `fulltwist`; `D₀` is the library smoothing, consistent with U-174 item 5
  (`smoothing` reads `D₀` through `exists_smoothing_record_visit`'s record clause — the realiser should take the
  SAME `D₀ := smoothDiagram …` in both fields).

### 4.3 Row 176 (port) — `est_PortData.port` in the weak form
* Site: identical shape at the `j`-corner of `carrierDiagram q₀'` switched at `y`; `s` = the third triangle edge
  (`u', v'` the two crossings), `K` = the triangle.  ≈ 1.2k (shares the site-builder glue with 174).
* `hrec : B.reducedRecord ≅ (carrierDiagram q₀).record` — wall transport, ≈ 1.0k.  Then `est_port_weak_of_bigon`.
* Ledger edit: F-176-1 (≈ 5 lines) + the field type change in `est_PortData`.

### 4.4 Row 177 — (4) RIII and (6) RII after smoothing
* (4): extract a `G11_ConfigSw k` from `CompleteLocal` at the K3 side (reuse G11 Unit A's extraction 8780–10263,
  replacing `¬IsAlternating` by `trans_sw`: the K3 over-order is cyclic (1b) and one switch toggles alternation);
  `D₀sw = (carrierDiagram_H q₀).switch x_H` up to the `Shadow.single` identification; `G11_core_sw` gives `D₁, Ψ`;
  Unit F' builds `D₁.record ≅ (D_L.switch x_L).record` from `Ψ` and the `ExactTriangleVisitOrders` transpositions
  (G11 Unit F pattern with the switched bit); `esc_switch_riii_of_chain` closes `switch_riii`.  ≈ 4.5–6.5k (§5 W3).
* (6): with F-177-1, the realiser chooses `D_H0 := smoothDiagram D_H x_H (eps …)` (record clause
  `smoothDiagram_record`), builds `BigonData ((smoothDiagram …).switch y)` with `j = 2`, run = the two ends
  `s⁻, t⁺` of the corner-cut arc (`StrandKind.cutStartS / arcST / cutEndT`; explicit points `p ∓ ε·e`, Smoothing §3),
  `s` = the `g` strand, `K = conv{y, s⁻, t⁺, z}` ⊂ `Δ = conv{x, y, z}`; `clear` for old kinds from the
  configuration's triangle clearance, for the other new kinds from the cone geometry at `x` (they lie in the
  opposite cone); `in/out/s_iff` from the quadrilateral's sides.  Orientation caveat: the corner-cut arc on the
  bigon side is `s⁻ → t⁺` iff `y` precedes `x` on `e` and `z` follows `x` on `f`; otherwise the run is `t⁻, s⁺`
  — the consumer case-splits, the constructor is indifferent.  ≈ 1.2k per side.  Record identity of the two
  reduced two-component records: `(ρ_H.smooth x).restrictCrossings {y,z}ᶜ ≅ (ρ_L.smooth x).restrictCrossings {y,z}ᶜ`
  where `ρ_H, ρ_L` are related by the wall bijection twisted by `σ` on the six local visits — after smoothing `x`
  and deleting `y, z` no local visit remains and the reconnections agree; a pure `Record` lemma (`Record.smooth`,
  `firstReturn`), ≈ 1.2k.  Then `esc_rii_after_smoothing_of_bigons`.  ≈ 3.6k total.

## 5. Units, waves, effort (lines / prover-hours; parallel units in one wave)

### Wave 1 — the constructor (library `SM/BigonDeletion.lean`), 8–10k lines, ≈ 110–150 h, 1.5–2 wall days at 6–8 units
| unit | content | lines | h | after |
|---|---|---|---|---|
| **U-M0** | `BigonData` API (as frozen in Statements_FINAL), `reducedTuple/Shadow/Diagram` (the run replaced by `M', q`; `k − j + 2` vertices, `LabelledTuple` by `ZMod.val` arithmetic with the rotation `M₀ = 0`, Smoothing §7-pre toolbox), strand kinds `old / cutIn / mid / cutOut`, the `orig` map, index laws.  FREEZE FIRST; pre-review the fields against the three `j = 1` sites (half a day) | 700 | 10 | — |
| **U-M1** | gap `ρ₀ := infDist`, `U := cthickening (ρ₀/2) K`, `IsDisc` (`Convex.cthickening`, `IsCompact.cthickening`), `K ⊆ interior U`, entry/exit parameters `t_p, t_q` (min/max of a closed set), frontier membership without a frontier formula, the choice of `M' ∈ (p, y)` off `line(e_out)` | 900 | 12 | M0 |
| **U-M2** | `Generic` of the reduced shadow by kinds (regular pairs at `M', q`; `tail_off`; `transverse`; `no_triple`) | 1200 | 18 | M0 |
| **U-M3** | crossing bijection `D' ≃ D ∖ {y, z}`, equal double points, over data pulled back, signs | 800 | 12 | M0 |
| **U-M4** | the four arcs, `IsArc`, `ArcCover ×2` (`mem_iff` by kind classification), `Clean ×2` (frontier points = the four ends; `exits` by `M₀`, `tail s`), `inner_iff'`, `no_inner`, `Separates`, `same_over` | 1500–2200 | 24–34 | M1–M3 |
| **U-M5** | `OutsideMatch`/`MoveMatch`: `φ` = relabelling with the two cut pieces rescaled (`eval_eq`; `dir_pos`/`dir_pos_before` by positive rescaling), `ψ` = M3's bijection, `e = id` | 800 | 12 | M1–M3 |
| **U-M6** | record bridge: occurrence bijection `Ψ : D'.Visit ≃ {v // v.1 ≠ y ∧ v.1 ≠ z}` preserving twin/bit/sign; monotone traversal key on component `i`; successor = `firstReturn` (`cycNext_unique_on`, `nextVisit_no_between`, `firstReturn_no_between`); `RecordIso.ofOcc` against `restrictCrossings`; PLUS the two record leaves `reducedRecord_counts`, `Record.restrictCrossings_switch` | 1500–2000 | 24–30 | M0, M3 |
| **U-M7** | `RIIData` assembly, `exists_rii_deletion`, `exists_bigonData_of_triangle` (barycentric side lemmas; G11's affine-basis toolkit 9093–9259) | 600 | 10 | all |
Order: M0 alone → M1 ∥ M2 ∥ M3 ∥ M6 → M4 ∥ M5 → M7.

### Wave 2 — the three `j = 1` sites + the interface edits (in parallel with Wave 1 once M0 is frozen), ≈ 3.5k, 45–55 h
I-110 site (0.8k) + `BlockSupply` for the curl-bearing record (0.8–1.2k, U110-B/H); I-174 `m`-corner site (1.2k);
I-176 `j`-corner site (1.2k) + F-176-1 edit (5 lines + field type); F-177-1 edit (≈ 100 lines).  The `hrec`
transports (110: 1.0k, 174: 1.2k, 176: 1.0k) are the consumers' wall bookkeeping and are NOT counted as toolkit.

### Wave 3 — row 177, ≈ 8–10k, 105–140 h, 2 wall days
`G11_core_sw` in 5 units: (a) statement-neutral refactor of G11's D8/E/F to take the six local over bits as a
parameter (A's process graft; the positivity footprint is 37 lines in D8/E, §6 R2) 0.5–1.0k; (b) the five
reparametrizations commuting with `switch` (`Reparam D D' → Reparam (D.switch x) (D'.switch (r x))`) 0.3k;
(c) D8' (height order of the switched diagram — one more instantiation table of the six cases) 1.2k; (d) E'
(record of `M₁^{sw}`: over bits at the six local visits flipped at `xs`) 1.5k; (e) F' + A' (the transposition
record iso against `D_L.switch x_L`; the config extraction with `trans_sw`) 1.5k.  Then I-177b: two `j = 2`
sites on `smoothDiagram` outputs (2.4k) + the reduced-smoothed-record lemma (1.2k).

### Decisive test (D-RM-1 rule step 4), after Wave 1
`s7_rii_witnesses`, `gsc_fulltwist_of_bigon`, `est_port_weak_of_bigon` sorry-free with `exists_rii_deletion` closed
(`#print axioms` = standard + `lp_lm` / `lit_homfly`), and `exists_bigonData_of_triangle` applied to at least one
actual site (I-110's is the smallest).

## 6. Riskiest steps and fallbacks (in order)

* **R1 — U-M4 `ArcCover.mem_iff` and U-M6's key arithmetic.**  G11 U5/U6 spent ≈ 3k on three arcs; Smoothing §8
  is the template for the key.  Mitigation: the `M₀ = 0` rotation removes wrap-around; the kind classification
  has 4 kinds (vs Smoothing's 7).  Fallback: if the general-`j` index laws stall past two attempts / 60 min
  (the reassessment rule), freeze `j ∈ {1, 2}` as two concrete instances of the same skeleton (the only values
  any consumer uses) — no statement change for the consumers (`exists_bigonData_of_triangle` is `j = 1`).
* **R2 — `G11_core_sw`: how far positivity is woven into G11.**  Measured: 37 positivity-touching lines in D8/E
  (GenericTransport 4918–8630), in three blocks — the over strand of a local crossing via `positiveDiagram_det_pos`
  (5580–5600, 5881–5926), the six height-order cases via `crossingSign`/`IsAlternating` (7082–7110), the over
  bits via the divide sign (7852–7876); 57 in Units B–D, almost all the literal `positiveDiagram X₀/X₁` naming
  `M₀, M₁`.  So the re-derivation is local (4.5k) IF the refactor (a) makes D8/E take the six local over bits as a
  parameter; if B–D's `positiveDiagram` naming has to be generalised too, 6–7k.  Fallback: report 177 (4)
  "ledger proved, move stated" (anticipated by the CV/R plan §7).
* **R3 — 177 (6) `j = 2` sites on `smoothDiagram` outputs.**  Discharging `in/out/s_iff` and `clear` through the
  `StrandKind` API against an explicit quadrilateral; the orientation caveat forces a consumer case split.
  Mitigation: the ∃-form interface lets the realiser choose `ε` (the `SmallEps` clearance `r₁` gives the cone
  geometry).  Fallback: as R2.
* **R4 — the two interface edits** (F-176-1, F-177-1) need the unit owners' acceptance; both are D-F11
  unit-internal Props (no row change) and both literal forms are provably unrealisable, so acceptance is expected;
  the 176 re-base is already PROVED here as one lemma.
* **R5 — `hrec` wall transports** (≈ 1k per consumer, G11 Unit-F pattern) are easy to underestimate and are
  consumer bookkeeping; the toolkit contributes `Record.restrictCrossings_switch` (110) and the
  `restrictCrossings` form composes with `restrictCrossings_iso_of_recordIso`, `RecordIso.ofOcc`,
  `CV.recordIsoOfData`.
* **R6 — the 110 `BlockSupply` for the curl-bearing record** (interlacement-graph lemma + a one-crossing knot
  diagram for the curl block).  Fallback: A's pattern K (polygonal kink INSERTION into `D₁`, `RIData` with a
  POSITIONAL record clause in the shape of Curl's `KinkInsertion.oldVisit`, ≈ 2.5k) — RI on the polygon, still
  never on the smoothing output.
* **R7 — machine load**: the consumer files import RProof (20–25 s per check); batch compiles.

## 7. The ≤ 12k-line target of D-RM-1: **NOT met for the lane as a whole** — the honest numbers

| scope | lines |
|---|---|
| the RII constructor + companions (Wave 1) | 8–10k |
| + the three `j = 1` sites and the two interface edits (Wave 2, toolkit part) | 11.5–13.5k |
| the whole moves toolkit the four rows need (+ `G11_core_sw` 4.5–6.5k + two `j = 2` sites and record lemma 3.6k) | **20–24k** |
| + the consumers' `hrec` transports (3.2k) | 23–27k |
| + the consumers' non-move remainder (174 items 1–3, 5–6 ≈ 5–8k; 176 items 3–5 ≈ 3–4k; 177 split ≈ 3–5k; 110 BlockSupply/U110-B/H ≈ 1–1.5k) | **≈ 35–42k** |

D-RM-1's decisive test asked for a typechecked RII-deletion constructor discharging `gsc_moves` /
`est_port_relation` / the 110 bigon hypothesis by instantiation "with a unit decomposition ≤ 12k lines total": the
typechecked statement and the instantiations are delivered (§1, PROVED glue), and the decomposition that
realises THAT scope (Waves 1–2) is 11.5–13.5k — at the boundary, not safely under.  The 12k cut buys the move
obligations of 110-bigon, 174 and 176 (their rows then close modulo their own bookkeeping); row 177 needs Wave 3
(≈ 8–10k more) and otherwise stays "ledger proved, moves stated".  D-RM-1's conjecture ("≈ 8k by splicing two
straight two-edge arcs with flat vertices, reusing the Smoothing separation lemmas") is the constructor alone,
and is plausible at 8–10k.

## 8. Grafts from DESIGN_A adopted / rejected

Adopted: (i) the record companions (`eraseTwo_crossingCount` → `reducedRecord_counts`, `eraseTwo_switch` →
`Record.restrictCrossings_switch`, diagram-level `rii_deletion_counts` PROVED); (ii) the process rule "refactor
G11's D8/E statement-neutrally before generalising"; (iii) the observation that the 177 (6) chain has length 2 and
that the site must be stated for a two-component non-positive diagram (B's `BigonData` already is); (iv) the
fidelity list's argument for F-176-1 (`OutsideMatch.eval_eq`).  Rejected: the identity-match frame (needs Units S,
E and FR-A-2), `Record.erase` (duplicates `restrictCrossings`), pattern K as the primary route (kept as fallback
R6), `HeightOrder`/`exists_riii_of_heightOrder` (no record clause; superseded by `G11_core_sw_statement`).
