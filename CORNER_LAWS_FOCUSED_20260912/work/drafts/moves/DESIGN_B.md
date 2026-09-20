# DESIGN_B — the moves toolkit: consumer-driven minimality (architect B, 2026-09-15 ≈17:45Z / 1:45pm ET)

Sketch: `work/drafts/moves/Sketch_B.lean` (339 lines; `cd work/lean && lake env lean ../drafts/moves/Sketch_B.lean`
→ 0 errors, exactly 3 `sorry` = the constructor `exists_rii_deletion`, its triangle specialisation
`exists_bigonData_of_triangle`, and the switched-G11 core `G11_core_sw`).  Every glue / instantiation /
avoidance lemma is PROVED; `#print axioms`: the avoidances `two_component_row_of_recordIso`, `curl_block_value`
and the ledger adapters `fulltwist_skein_of_port_weak`, `esc_switch_riii_of_chain` are sorry-free (standard +
`lp_lm`/`lit_homfly`); the instantiations inherit `sorryAx` only through the constructor.
Inputs read: AUTHOR_NOTES D-RM-1 (17:24Z); U_S7G_REPORT §0; U_R174/176/177 reports + the interface Props in the
unit files; SM/LinkMoves.lean (RI/RII/RIIIData, MoveMatch, ArcCover, Clean); SM/Smoothing.lean (header, §§0-8,
`exists_smoothing_record_visit`); RProof/GenericTransport.lean (G11_Config/Params, `gu5_Side`, D8, `G11_core`,
`GT_G11_strong`); SM/MarkedProducts.lean (`restrictCrossings`, `lowest`, `blocks`, `BlockSupply`);
SM/SingleCrossing.lean; CV/FullTwist.lean; sm-4:585-632, 728-745, 850-870.

## 0. Verdict in five lines

1. ONE geometric constructor suffices for the RII obligations of all four rows: the **vertex-run bigon deletion**
   `exists_rii_deletion : ∀ D (B : BigonData D), ∃ D', RII D' D ∧ D'.componentCount = D.componentCount ∧
   Nonempty (RecordIso D'.record (D.record.restrictCrossings B.keep))` — the reduced record is the record with the
   four visits of `y, z` deleted (first-return successor, the accepted `Record.restrictCrossings`).  Rows 110/174/176
   are the `j = 1` (one-vertex path) case; row 177 (6) is the `j = 2` case on smoothing outputs.  No insertion
   direction is needed by any consumer.
2. The RI curl of row 110 is AVOIDED at the record level (§2): `mp:lowest` two-component row on `D_A` itself +
   `mp:blocks.product` + `lc:single-crossing` (`curl_block_value`); no `RIData` anywhere.
3. Row 177 (4) needs the G11 core on a **switched** positive diagram (`G11_core_sw`, §4.2): Units B–D of G11 reused
   verbatim (shadow-level), D8/E/F re-derived for over data "positive except at `xs`".  Not avoidable (§4.1).
4. Two consumer interface Props are STRONGER than any constructor can deliver and must be edited (unit-internal
   D-F11 Props, not row statements): 176 `est_PortData.port` (literal RII chain to a diagram on the OTHER polygon —
   false) → `est_port_weak`; 177 `esc_MoveData.rii_after_smoothing` (∀ oriented smoothings, arbitrary arcs in an
   arbitrary clean disc) → `esc_rii_after_smoothing_weak` (one pair, the library's `smoothDiagram`, with record clauses).
   Both ledgers survive with ≤ 100-line edits (§5).
5. Honest totals (§6): constructor ≈ 8.0k; `G11_core_sw` ≈ 4.5k; move INSTANTIATIONS 110/174/176/177 ≈ 6k; record
   identifications the instantiations feed ≈ 4.7k.  "Everything the four rows need" is ≈ 34–41k because 174/176/177
   also carry 11–17k of non-move carrier bookkeeping.  ≤ 12k buys: the constructor + the three `j = 1` sites
   (110 bigon branch, 174 G10, 176 port) ≈ 11–12k.  Rows 110-bigon/174/176 then close modulo their own bookkeeping;
   177 stays "ledger proved, moves stated" unless a further ≈ 8k (G11_sw + two `j = 2` sites) is funded.

## 1. Consumer-driven minimality: what each interface Prop actually needs

| consumer | interface (verbatim) | what the toolkit must deliver | avoidable? |
|---|---|---|---|
| 110 `s7g_switch_value_of_rii` | `hR : RII Dred (D.switch x)`, `hrec : Dred.record ≅ DL.record` | one RII deletion on the corner polygon's positive lift switched at `q = x`; `hrec` = constructor's record clause ∘ U110-A's visit-order transport | no (the printed step IS an RII, sm-4:614-620) — realised by `s7_rii_witnesses`, `s7_switch_value_of_bigon` (PROVED from the constructor) |
| 110 `s7g_value_of_ri` | `hR : RI Dred D_A`, `hrec` | — | YES: §2 (record level), `two_component_row_of_recordIso` + `curl_block_value` |
| 174 `gsc_fulltwist_triple` | `IsPositive q ∧ IsOrientedSmoothing D_H q D₀ ∧ ∃ D_L', ReflTransGen RII (D_H.switch q) D_L' ∧ homfly D_L' = homfly D_L` | one RII deletion on `(carrierDiagram (τ qAB)).switch qx` at the `m`-corner; `homfly` by `gausscode_polynomial` from the record clause ∘ wall transport | no — `gsc_fulltwist_of_bigon` (PROVED) |
| 174 `gsc_smoothing_split`, `gsc_Ledger` rest | record identifications, writhe/rotation ledgers | no move witness; `exists_smoothing_record_visit` + carrier bookkeeping | not a move |
| 176 `est_PortData.port` | `ReflTransGen RII (D₊.switch y) D₀` LITERAL | impossible as stated (§5 F-176-1); `est_port_weak` + `est_port_weak_of_bigon` (PROVED); ledger re-based by `fulltwist_skein_of_port_weak` (PROVED) | the LITERAL form is unrealisable; the weak form needs the same RII deletion as 174 (same shape: the `j`-corner path vs the third triangle edge) |
| 176 `smooth`, `two`, `poly₁₂`, `link`, `writhe`, `rot`, `alt` | smoothing existence + identifications | `exists_smoothing_record_visit`; bookkeeping | not a move |
| 177 `esc_switch_riii` | `homfly (D_H.switch x_H) = homfly (D_L.switch x_L)` | G11 on the switched diagram (§4.2) + Unit-F-type record iso; `esc_switch_riii_of_chain` (PROVED glue) | no (§4.1) |
| 177 `esc_rii_after_smoothing` | ∀ smoothings, `homfly (D_H0.switch y_H) = homfly (D_L0.switch y_L)` | two `j = 2` RII deletions on `smoothDiagram` outputs + record iso of the reduced two-component records; `esc_rii_after_smoothing_of_bigons` (PROVED, via `presentations` — two components) | the ∀ must become ∃ (§5 F-177-1); the move itself is not avoidable (§4.3) |
| 177 `knot_after_two`, `three_components`, `esc_FullSplitData` | record counts, carrier split | not moves | — |

Shared constructor: 174 and 176 have LITERALLY the same site shape (a corner of the corner polygon whose two incident
edges are crossed by one straight remote strand, switched so the strand is over twice) — one `BigonData` builder
`exists_bigonData_of_triangle` serves 110, 174, 176; only the labels/clearance differ.

## 2. The RI avoidance (row 110, ε = 0 branch) — typechecked

sm-4:857-866: "the deletion of the curl `y` from component 1 of `D_A` is that smoothing with the triangle
discarded — which is what the closure at the cut and the successor words of (s7c:component-data) record".  Reading:
never form `D_A^{post}`.  (a) `two_component_row_of_recordIso` (PROVED): `[z⁻¹] P D_A = a^{−2ℓ}(a − a⁻¹)
[z⁰]P K₁ [z⁰]P K₂` for ANY `K₁, K₂` record-isomorphic to the two knot restrictions of `D_A` — `mp:lowest` at `c = 2`
+ `presentations`; the curl stays in component 1.  (b) `curl_block_value` (PROVED): for a one-circle record `ρ`
with a block supply (`BlockSupply ρ C`, mp:blocks), if block `H₀` is a single self crossing then
`P D = ∏_{H ≠ H₀} P (C H)` for every `D` with record `ρ` — `mp:blocks.product` + `lc:single-crossing.one_crossing`.
The curl `y` (adjacent occurrences) interlaces nothing, so it is its own block; the curl-free `Q₁` is the product
over the other blocks, i.e. component 1's value with the curl equals `Q₁` — RI invariance obtained from two
accepted rows, no `RIData`.  Consumer cost (corner lane, U110-B/H): a `BlockSupply` for component 1's record — a
one-crossing one-circle polygon for the curl block (explicit pentagon, ≈ 300 lines, or `IsRealizable` of the
record) and the CB lane's block realisations for the rest (CBProducts GL section) ≈ 800–1200 lines total, versus
≥ 4k for a curl-deletion constructor on a smoothing output.  Writhe: the row's `w_H = w₁ + w₂ + 2ℓ + 2`
(s7c:noninterlacing-writhe) already counts `y`; the slot bookkeeping is unchanged.
Fidelity: the printed proof cites "local LM R-I equality"; the formal route proves the same value identity from
mp:blocks + lc:single-crossing.  thm:C-S7's statement is untouched.

## 3. The constructor: statement, hypotheses, construction, architecture

### 3.1 Statement (Sketch §1–§2)
`BigonData D`: component `i`; entering edge label `a` (`e_in = (M₀, M₁)`), run length `j ≥ 1` (`j + 3 ≤ k`),
exiting edge `a + j` (`e_out = (M_j, M_{j+1})`); remote strand `s` (any component); crossings `y = {e_in, s}`,
`z = {e_out, s}`; `run_free` (the `j − 1` middle edges have no crossing), `no_io` (`e_in`, `e_out` do not cross —
automatic for `j = 1`), `same_over` (both over occurrences on `s`, or neither); the crossing parameters `ty tz tsy
tsz` with their `edgePt` specs; a convex compact region `K` with `run_mem`, `in_iff` (`e_in ∩ K = [y, M₁]`),
`out_iff` (`e_out ∩ K = [M_j, z]`), `s_iff` (`s ∩ K = [y, z]`), `clear` (every other edge segment is disjoint
from `K`).  `keep := {c | c ≠ crossingOf (overVisit y) ∧ c ≠ crossingOf (overVisit z)}`;
`reducedRecord := D.record.restrictCrossings keep`.
Output: `∃ D', RII D' D ∧ D'.componentCount = D.componentCount ∧ Nonempty (RecordIso D'.record reducedRecord)`.
Companions to add in the unit: crossing card `+2`, `D'.writhe = D.writhe − sign y − sign z`, positivity of the
transported crossings, the crossing bijection `D'.Γ.Crossing ≃ {x // x ≠ y ∧ x ≠ z}` with equal double points.

### 3.2 How the consumers supply the hypotheses
* 110: `D := (positiveLift …).switch x`, `i = 0`, `a` = the label of the corner polygon's edge into the wall vertex
  `M`, `j = 1`, `s` = the remote edge, `K` = the closed contact triangle; `same_over` from sm-4:614-618 (after
  switching `q` the remote strand is over at both newborns); `clear` = "the isolated contact disc contains no other
  strand" (the simple-wall hypothesis of the germ); `in/out/s_iff` automatic (`exists_bigonData_of_triangle`).
* 174: `D := (carrierDiagram hn hG' hSm' (τ qAB)).switch qx`, the `m`-corner of the corner polygon (a selected
  visit, `geoCornerMark`), edges along `ℓ₃`/`ℓ₁`, `s` = the strand of `ℓ₂` through the adjacent visits `w(ℓ₂), x(ℓ₂)`
  (R-LOC (2)), `K` = the triangle `conv{x_pt, m_pt, w_pt}`; `clear` from R-LOC's clearance of the local triangle
  (G11 Unit A's "edges of the corner polygon inside the edges of `P`" toolkit gives the corner polygon's edges near
  the triangle, GenericTransport.lean 8780–10263, reusable).
* 176: identical shape at the `j`-corner of `carrierDiagram q'` with `s` = the third triangle edge (`u', v'` the
  two crossings); `K` = the triangle.
* 177 (6): `D := (smoothDiagram D_H x ε).switch y`, `j = 2`, the run = the two ends `s⁻, t⁺` of the corner-cut arc
  (`StrandKind.cutStartS/arcST/cutEndT` of the splice model), `s` = the `g`-strand, `K = conv{y, s⁻, t⁺, z}` ⊂ the
  triangle `Δ = conv{x, y, z}`; `clear` for old kinds from the configuration's triangle clearance, for the other
  four new kinds from the cone geometry at `x` (they lie in the opposite cone); `in/out/s_iff` from the
  quadrilateral's sides (`K` is `Δ` with the corner at `x` cut: convex, `y, s⁻` and `t⁺, z` adjacent vertices).
  Orientation caveat: the corner-cut arc on the bigon side is `s⁻ → t⁺` iff `y` precedes `x` on `e` and `z` follows
  `x` on `f`; otherwise the run is `t⁻, s⁺` — the consumer case-splits, the constructor is indifferent.

### 3.3 Construction (the proof of `exists_rii_deletion`)
Disc: `F := ⋃_{u foreign} seg u ∪ {M₀, M_{j+1}, tail s, head s}` is compact and disjoint from `K` (`clear`,
`in_iff` at `t = 0`, `out_iff` at `t = 1`, `s_iff`), so `ρ₀ := infDist`-gap `> 0`; `U := Metric.cthickening (ρ₀/2) K`
(sup metric of `Plane = ℝ × ℝ`): `IsDisc U` by `Convex.cthickening`, `IsCompact.cthickening`, `K ⊆ interior U`.
Entry/exit: `e_in ∩ U = [p, M₁]` with `p = edgePt e_in t_p`, `t_p := min{t ∈ [0,1] | edgePt e_in t ∈ U}`
(`0 < t_p < ty`, convexity); `e_out ∩ U = [M_j, q]`; `s ∩ U = [b_in, b_out] ∋ y, z`.  Frontier membership of the four
points without a frontier formula: each is in `U` and a limit of points of its edge outside `U`.
Reduced polygon: `M' ∈ (p, y)` on `e_in`, chosen off `line(e_out)`; `D'` = component `i` with the run replaced by
`M', q` (`k − j + 2` vertices, `LabelledTuple` by `ZMod.val` arithmetic as Smoothing §7-pre), other components
unchanged, over data pulled back through the strand map.  NO strict convexity is needed: the reduced arc
`[p → M' → q]` has inner points in `interior U` because `M' ∈ interior U` and `p, q ∈ U`
(`Convex.openSegment_closure_interior_subset_interior`); `[M', q]` misses `s` because both ends are strictly on the
`M₀`-side of `line(s)` (`M₀, M_{j+1}` on one side, the run on the other, `run_free`).  Regularity at `M'`, `q`
is automatic (`q ∉ line(e_in)`: `line(e_in) ∩ frontier U = {p, p'}`, `q ≠ p`, `q = p'` would put `q` on the run's
side).  Crossings of `D'` = crossings of `D` minus `y, z` (foreign edges miss `U`; `e_in`'s other crossings lie on
`[M₀, p)` ⊂ `[M₀, M']`).
Site: `RIIData U D' D` with `a = [p → M₁ → … → M_j → q]` (on `D`), `b = s ∩ U`, `a' = [p → M' → q]`, `b' = b`;
`Clean` (frontier points = the four ends, `exits` by `M₀`, `tail s`), `ArcCover.mem_iff` by kind classification,
`inner_iff'` = `{y, z}`, `no_inner` for `D'`, `Separates`, `same_over`; `MoveMatch`: `φ` = relabelling with the
cut pieces rescaled (`eval_eq`, `dir_pos` by positive rescaling), `ψ` = the crossing bijection, `e = id`.
Record: occurrence bijection `Ψ : D'.Γ.Visit ≃ {v // v.1 ≠ y ∧ v.1 ≠ z}` preserving twin/bit/sign; successor via a
strictly increasing traversal key on component `i` (rotate labels so `M₀ = 0`; the map is monotone on retained
coordinates) and the accepted `cycNext_unique_on` / `nextVisit_no_between` / `firstReturn_no_between`; other
components: identical coordinates.  Then `RecordIso.ofOcc` (or a direct `RecordIso.mk` against
`restrictCrossings`' `firstReturn`).

### 3.4 Units, lines, hours (constructor ≈ 8.0k lines, ≈ 110–140 prover-hours, 1.5–2 wall days at 6–8 parallel units)
| unit | content | lines | h |
|---|---|---|---|
| U-M0 | `BigonData` API, `reducedTuple/Shadow/Diagram`, strand kinds `old/cutIn/mid/cutOut`, `orig` map, index laws (`ZMod.val`, no-wrap normalisation with `M₀ = 0`) | 700 | 10 |
| U-M1 | gap `ρ₀`, `U`, `IsDisc`, `K ⊆ interior U`, entry/exit parameters, frontier membership, `M'` | 900 | 12 |
| U-M2 | `Generic` of the reduced shadow (regular pairs at `M', q`; `tail_off`; `transverse`; `no_triple`) by kinds | 1200 | 18 |
| U-M3 | crossing bijection `D' ≃ D ∖ {y,z}`, double points equal, over data, signs | 800 | 12 |
| U-M4 | the four arcs, `IsArc`, `ArcCover ×2`, `Clean ×2`, `inner_iff'`, `no_inner`, `Separates`, `same_over` | 1500 | 24 |
| U-M5 | `OutsideMatch`/`MoveMatch` (`φ`, `dir_pos`, `dir_pos_before`, `ψ`, `over_eq/under_eq`) | 800 | 12 |
| U-M6 | record bridge (`Ψ`, twin/bit/sign, monotone key, successor = first return, `RecordIso`) | 1500 | 24 |
| U-M7 | `RIIData` assembly, `exists_rii_deletion`, companions, `exists_bigonData_of_triangle` (barycentric side lemmas; G11's affine-basis toolkit 9093–9259 reusable) | 600 | 10 |
Dependencies: M0 first (freeze `BigonData` before the consumers start); M1–M3 parallel; M4, M5 after M1–M3; M6 after
M0/M3; M7 last.  Riskiest: M4 (the `mem_iff` classification, as in G11 U5/U6 ≈ 3k for three arcs) and M6 (index
arithmetic of the key; Smoothing §8 is the template).

## 4. Row 177

### 4.1 Why (4) and (6) cannot be avoided
(4): `D_H.switch x_H` and `D_L.switch x_L` have records differing by the three transpositions `σ`; no record iso,
no skein rewriting: an RIII witness is the content.  (6): reformulating by the skein at `x` gives `(6) ⟺
homfly (D_H^{sw y}) = homfly (D_L^{sw y})` given the RIII for the double switch; but `D_L^{sw y}` has a CYCLIC
over-order (L is transitive, one switch toggles alternation) — not an RIII site; every rewriting returns a bigon
with a smoothed corner.  Both are genuinely geometric.

### 4.2 (4) `esc_switch_riii`: `G11_core_sw` (Sketch §4)
`G11_ConfigSw k` = `G11_Config` minus `trans`, plus `sw : Fin 3` (the switched local pair) and `trans_sw` (the SWITCHED
over-order is transitive); `D₀sw := (positiveDiagram X).switch xs`; `G11_core_sw_statement` = `G11_core_statement`
with `D₀sw` (same `σ`).  Realisation: Units B–D of GenericTransport are shadow-level (`X₀`, `X₁`, `gu5_Side`,
`gu5_ArcParams`, `exists_moveMatch`, `exists_arcCovers`, D1–D7: all stated on `Shadow.single ⟨k+3, _, Y⟩`) —
reused verbatim (≈ 0 new lines); to re-derive: `M₀sw := M₀.switch (lift xs)`, `M₁sw := M₁.switch (lift' xs)`, the
five reparametrizations commuting with `switch` (`Reparam D D' → Reparam (D.switch x) (D'.switch (r x))`, ≈ 300),
D8' (height order of the switched diagram — the six cases exist, one more instantiation table, ≈ 1200), E'
(record of `M₁sw`: over bits at the six local visits flipped at `xs`, ≈ 1500), F' (the transposition record iso
against `D_L.switch x_L`, ≈ 1000), Unit A' (from the K3 contact carrier to a `G11_ConfigSw`: reuse Unit A's
extraction, replace `¬IsAlternating` by `trans_sw`, ≈ 500).  ≈ 4.5k lines, 60–80 h.  Then `esc_switch_riii_of_chain`
(PROVED) closes (4).

### 4.3 (6) `esc_rii_after_smoothing`: two `j = 2` sites + one record lemma
With the interface in the `esc_rii_after_smoothing_weak` form (§5), the realiser takes `D_H0 := smoothDiagram D_H x
(eps …)` (record clause from `smoothDiagram_record`), builds `BigonData ((smoothDiagram …).switch y)` with the run
`s⁻, t⁺` (§3.2; ≈ 1.2k per side, the splice-model `StrandKind` API exposes tail/dir of every strand), and proves the
record identity of the two reduced records (Sketch `esc_rii_after_smoothing_of_bigons`' `hrec`): `(ρ_H.smooth x).
restrictCrossings {y,z}ᶜ ≅ (ρ_L.smooth x).restrictCrossings {y,z}ᶜ` where `ρ_H, ρ_L` are related by the wall bijection
twisted by `σ` on the six local visits — after smoothing `x` and deleting `y, z` no local visit remains and the
reconnections agree (`e`-before-`x` joins `f`-after-`x` on both sides; the swapped local visits are exactly the
deleted ones).  A pure `Record` lemma (`Record.smooth`, `firstReturn`), ≈ 1.2k.  Total (6) ≈ 3.5k, 45–60 h.

## 5. Fidelity: constructors are library material; interface edits; where Props are too strong
* No row statement changes.  `exists_rii_deletion`, `exists_bigonData_of_triangle`, `G11_core_sw` are library
  theorems (suggested `SM/BigonDeletion.lean`, `RProof/GenericTransportSw.lean`).
* **F-176-1 (`est_PortData.port` is stronger than deliverable — and false).** `Relation.ReflTransGen RII
  ((carrierDiagram q').switch y) (carrierDiagram q)` relates diagrams on `E.curve t'` and `E.curve t`; `RII`'s
  `OutsideMatch.eval_eq` forces identical traces outside a disc, but the two polygons differ along whole edges.
  Edit: `port : est_port_weak (carrierDiagram q') (carrierDiagram q) y` (Sketch); ledger: replace
  `CV.fulltwist_coefficient` in `est_omega1_eq_of_port` by `fulltwist_skein_of_port_weak` + the coefficient
  extraction on `slot/Ω₁` exactly as U-174 §5 did (`gsc_d_carrierDiagram/Omega`; ≈ 80 lines).  The RA text
  (T2) reads "deleting it leaves exactly `D_0`" — the record of `D_0`, as U-174 already read lem:fulltwist (T2)
  through ax:gausscode.
* **F-177-1 (`esc_MoveData.rii_after_smoothing` quantifies over ALL oriented smoothings).** An arbitrary
  `OrientedSmoothingData` has arbitrary polygonal arcs inside an arbitrary clean convex disc; the bigon `{y, z}`
  then has an uncontrolled side and its emptiness cannot be established from the configuration.  Edit: the field
  becomes `esc_rii_after_smoothing_weak` (∃ one pair of smoothings with record clauses); `esc_coefficient_identity`
  / `esc_contact_identity` obtain their smoothings from the interface instead of `exists_smoothing_record_visit`
  (the record clauses carry `knot_after_two`/`three_components`' counts); ≈ 100 lines.  Same edit shape for
  `knot_after_two`, `three_components` (∀ → the same ∃ witnesses) or keep them ∀ (they are record-level and hold
  for every smoothing via the record clause — no change needed).
* **F-110-1.** The RI curl is read at the record level (§2); U110-B/H must supply `BlockSupply` for component 1.
* **F-174/176-2.** `hrec` (reduced record ≅ the other side's lift record) is the consumers' wall-transport
  bookkeeping (G11 Unit F pattern without transpositions); the constructor's `restrictCrossings` form composes with
  `restrictCrossings_iso_of_recordIso` (CBProducts:1358) and `CV.recordIsoOfData` / `RecordIso.ofOcc`.
* The constructor's `K`-hypotheses (`in/out/s_iff`) are slightly stronger than "the bigon disc is empty" (they
  ask `K` convex ⊇ the bigon); for the printed sites `K` is the contact triangle / the cut triangle, so nothing is
  lost.

## 6. Estimates, waves, risks
Moves toolkit (library): constructor 8.0k + `G11_core_sw` 4.5k = **12.5k**.
Move instantiations: 110 site 0.8k; 174 site 1.2k; 176 site 1.2k + ledger edit 0.1k; 177 (4) config extraction is
inside 4.5k above, (6) two sites 2.4k + record lemma 1.2k = **6.9k**.
Record identifications feeding the instantiations (wall transports): 110 1.0k, 174 1.2k, 176 1.0k, 177 (4) inside F'
= **3.2k**.  Non-move remainder the rows still need (from the unit reports): 174 items 1–3, 5–6 ≈ 5–8k; 176 items
3–5 ≈ 3–4k; 177 split ≈ 3–5k; 110 BlockSupply + U110-B/H ≈ 1–1.5k = **12–18k**.
Grand total ≈ 34–41k lines.  Within a 12k cap: Wave 1 + Wave 2 below (≈ 11–12k) closes the move obligations of
110-bigon, 174 and 176; 177 needs Wave 3 (≈ 8k more).
* **Wave 1 (constructor, 8k, 1.5–2 wall days):** U-M0 alone (freeze `BigonData` + reduced shadow defs, 1 unit),
  then U-M1/M2/M3/M6 in parallel, then U-M4/M5, then U-M7.  Pre-review: the `BigonData` fields against the three
  consumers' actual configurations BEFORE M1 starts (half a day).
* **Wave 2 (in parallel with Wave 1 once M0 is frozen):** the three `j = 1` sites (`exists_bigonData_of_triangle`
  instantiations: 110 corner wall, 174 `m`-corner, 176 `j`-corner) + the two interface edits (176 port, 177 ∃) +
  the 110 `BlockSupply` (§2).  ≈ 3.5k.
* **Wave 3 (177):** `G11_core_sw` (4.5k, 4 units: Reparam-switch + D8', E', F' + A') and the two `j = 2` sites +
  record lemma (3.6k).  ≈ 8k, 2 wall days.
Main risks, in order: (1) U-M4/M6 index and betweenness arithmetic on `ZMod` labels (Smoothing/G11 precedents
mitigate; the `M₀ = 0` rotation avoids wrap); (2) the `j = 2` sites on `smoothDiagram` outputs — discharging
`in/out/s_iff` and `clear` through the `StrandKind` API (mitigated by the ∃-form interface: we choose `ε`); (3) how
far positivity is woven into G11's U5/U6 (if D8/E cannot be re-instantiated cheaply, `G11_core_sw` grows to 6–7k);
(4) the two interface edits must be accepted by the unit owners (D-F11 material, no row change); (5) `hrec`
transports (G11 Unit F pattern) are 1k each and easy to underestimate; (6) machine load: the consumer files import
RProof (20–25 s per check); batch.
