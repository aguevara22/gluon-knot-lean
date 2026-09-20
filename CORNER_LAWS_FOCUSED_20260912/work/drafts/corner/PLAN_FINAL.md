# PLAN FINAL — rows 103 cb:singleton, 105 lem:corner-values, 110 thm:C-S7, 112 thm:C-soft: judge's decision, fixed statements, route, units

Rows 103 (reference/SM/sm-3-statesum.tex:4697-4702 statement, 4703-4759 proof), 105 (4801-4809, 4810-4820),
110 (reference/SM/sm-4-knotlaws.tex:267-274, 275-908), 112 (984-991, 992-1147). Judge (subagent), 2026-09-15 ~15:40Z /
11:40am ET. Inputs: DESIGN_A.md / Sketch_A.lean (fidelity-first) and DESIGN_B.md / Sketch_B.lean (feasibility-first).
Both re-checked with `cd work/lean && lake env lean <file>`: Sketch_A 0 errors, 4 `sorry` leaves (`cs_split`, `s7_sliding`,
`s7_bigon`, `so_soft_law`), row 105 (i) PROVED; Sketch_B 0 errors, 11 `sorry` leaves, all four row-level assemblies PROVED
(incl. the S7 side-parameter reduction). Also read: the four printed statements and proofs, the accepted siblings
`SM.thm_C_S3 : CS3Data` (SM/CS3.lean:2478-2510) and `SM.thm_C_S5 : CS5Data` (SM/CS5.lean:53-61), the consumers
`UniquenessHypotheses.vertex_edge/.soft` (SM/Uniqueness.lean:57-76), `A_lawful.vertex_edge_law/.soft_theorem`
(SM/ALawful.lean:102-127), the accepted modules cited in §3 (all grep-verified), and — decisive for the interface — the
floor lane's `work/drafts/floor/PLAN_FINAL.md` §1/§2.4 and `Statements_FINAL.lean` §7 (written ~15:00Z, AFTER both corner
designs copied Gap2Statements §8).

Deliverables (this directory; nothing written under work/lean):
- `Statements_FINAL.lean` (764 lines) — the fixed statements, the frozen proof-route leaves, the proved assemblies.
  `cd work/lean && lake env lean ../drafts/corner/Statements_FINAL.lean`: 0 errors, 13 s warm; 14 declarations use `sorry`
  = the 10 unit leaves of §4 (`sg_isolated_undominated`, `sg_daughters_products`, `sg_daughters_rotation`,
  `s7_sliding_law_at`, `s7_bigon_law_at`, `s7_universal_extraction`, `s7_corner_product` (2nd conjunct), `sft_same_sign`,
  `sft_mixed`, `sft_loop`) + the 4 row theorems of §6 (`cb_singleton`, `corner_values`, `thm_C_S7`, `thm_C_soft`, bodies
  `… thm_floor` once row 100 lands). PROVED: `cb_singleton_of_floor`, `corner_values_i` (row 105 (i), UNCONDITIONAL),
  `corner_values_of_singleton/_of_floor`, `thm_C_S7_of` (floor + singleton), `thm_C_S7_of_floor`,
  `thm_C_soft_of_cornerValues/_of_floor`, the interface bridge `carrierUniformOrOneDissent_of_signed`, the companions
  `CS7Data.bigon/.sliding/.contactSign_literal`, `CSoftData.exists_generic/.doubled`, `CornerValuesData.embedded_rotationInt`.
  `#print axioms`: `corner_values_i`, `cornerHomfly_ne_zero` = [propext, Classical.choice, Quot.sound, SM.lit_homfly,
  SM.lp_lm, SM.lp_lm_uniqueness] (the policy literature interfaces behind def:C's `homfly` and lp:core's `P`);
  `cvl_embedded_of_no_crossings`, `carrierUniformOrOneDissent_of_signed`, `coeffAt_mul_eq_zero_of_lt_floor` = standard only.
- this file.

## 0. Verdict: **B wins** (statement shapes = the consumers' shapes with no new definitions; 11 fine leaves; all four
assemblies proved; honest estimates; the RII/RI-witness risk named), with A's grafts (row 105 (i) PROVED outright, the
literal three-conjunct (i), the `∃ hQ` and `2C = (χ₋+χ₊)C` companions, the `bigon`/`sliding`/`contactSign_literal`
readings, the explicit `hsing` parameter of the bigon leaf) and ONE judge's repair neither candidate has (§2.1).

| criterion | A | B | decision |
|---|---|---|---|
| 103 statement | `CbSingletonData.isolated_zero` | identical | equal (adopt) |
| 105 (i) hypothesis | `carrierCrossingCount = 0`, embeddedness a THEOREM (`cv_embedded_of_crossingFree`, PROVED via `nonadjacent_meet_crossing`/`consecutive_meet`) | same reading, embeddedness a LEAF (U105-A, 500 lines, 7 h) | **A's proof grafted**: U105-A closed now, row 105 (i) unconditional in Statements_FINAL |
| 105 (i) conclusion | `\|carrierRotation\| = 1 ∧ cornerSlot = 0 ∧ cornerCoefficient = 1` (3 printed conclusions, real `r_Q` of def:uniform) | + a 4th conjunct `\|carrierRotationInt\| = 1` | **A** (one conjunct per printed conclusion; the integer form is the companion `embedded_rotationInt`, FR-CC-5) |
| 110 shape | two fields `bigon`/`sliding` (`g.BigonAt`/`g.SlidingAt`), `C(λᵢ)` wrapped in NEW defs `firstHalfStateSum`/`secondHalfStateSum` | one field on `g.VertexEdgeAt` with `∀ h₁ h₂` (genericity proofs) and INLINE `cornerStateSum (contactHalfSizes_bounds hn h.1).1.1 h₁` — literally `UniquenessHypotheses.vertex_edge` with `F := C` | **B** (no new definitions in a fixed-name statement; "of bigon or sliding type" is exhaustive, `vertexEdge_bigon_or_sliding`, FR-CC-7); A's two readings kept as the companions `CS7Data.bigon/.sliding` |
| 110 dependency | `thm_C_S7_of hF hsing` (floor + singleton, the printed list) | `thm_C_S7_of_floor hF` only (singleton derived inside) | **A**: the bigon leaf takes `hsing : CbSingletonData` explicitly (sm-4:777-783), `thm_C_S7_of_floor := thm_C_S7_of hF (cb_singleton_of_floor hF)` |
| 110 side parameters | leaves at arbitrary `tp tm` | leaves at ONE parameter `< δ`; reduction by `cornerStateSum_side_eq` PROVED | **B** (the reduction is an actual proof step, done) |
| 112 genericity of `P_ε` | `∃ hQ` (accepted thm:A-soft's shape) | `∀ hQ` (consumer `UniquenessHypotheses.soft`'s shape) | **B** + A's form as the PROVED companion `CSoftData.exists_generic` (via `soft_family_generic`); FR-CC-12 |
| 112 multiplier | `softAmplitudeMultiplier : ℚ`, companion `doubled` in ℤ | `softAmplitudeMultiplier : ℚ` | equal; A's `doubled` grafted |
| 103 leaves | one packaged `cs_split` (5 conjuncts) | `sg_isolated_undominated`, `sg_daughters_products` (with the owner `↔`), `sg_daughters_rotation` (with the real rotation sum) | **B** (three independently auditable leaves; the owner-iff interface lets U103-D and U103-E run in parallel) |
| floor interface | Gap2Statements §8 copy; anticipates the reversal form / real conjunct "by a 40-line bridge" | Gap2Statements §8 copy; lists drift as risk 6 | **NEITHER matches the floor lane's FINAL** (§2.1): repaired here, bridge PROVED |
| route detail | file:line for the accepted inputs; FlatCarriers named as the only transport precedent | same + `IsSkeinTriple`/`RIData`/`RIIData` (LinkMoves.lean:569/599/751), `knotRestrict`/`twoLinking`, CS3 §A `Reparam`/`Deform`, CSilent `sideTransport`, CV `pieceEquiv` | **B** |
| estimates | ≈ 16k lines, 90-120 h (110: 55-75 h) | ≈ 21k lines, 110: 140-190 h; "sliding proved, bigon stated" as honest intermediate | **B's** (CS3, a one-to-one carrier law, took 2.5k lines; 110 has five sectors) |

Scores (1-10). FIDELITY A 8 / B 8.5 — A: literal (i), but two new definitions inside the fixed-name S7 statement and
`∃ hQ` adds a conclusion the printed sentence presupposes; B: consumer-exact S7/soft shapes, no new defs, but a 4th
conjunct in (i). FEASIBILITY A 7 / B 8.5 — both typecheck; A proves 105 (i) outright (real win) but packages 103 in one
5-conjunct leaf and estimates 110 at 55-75 h; B's 11 leaves, proved assemblies incl. the S7 reduction, the RII/RI-witness
diagnosis and the honest sizes. REUSE A 7.5 / B 8.5 — A finds `nonadjacent_meet_crossing`/`consecutive_meet` (closes a
unit); B reaches CS3 §A, CSilent, CV/ChamberInvII, `IsSkeinTriple`, `knotRestrict`. Totals A 22.5 / B 25.5.

## 1. Clause map (printed → Lean; Statements_FINAL.lean)

### Row 103 (sm-3:4697-4702) → `CbSingletonData` (§2), one field `isolated_zero`
| tex | printed | Lean |
|---|---|---|
| 4699 | "Let `A` be a uniform carrier of `S`" | binder of def:C/cb:blocks: `hn : 3 ≤ n`, `[NeZero n]`, `hP : Generic P`, `hS : IsDecomposition hn hP S`, `A : Component hn hP S`; `CarrierUniform hn hP S A` (def:uniform, UniformDefinition.lean:27) |
| 4699-4700 | "one of its self-crossing labels `c`" | `c ∈ carrierCrossings hn hP S A` (def:smoothing, CarrierCrossings.lean:56; lem:carriers (iii): exactly the self-intersections) |
| 4700 | "interlaces no other self-crossing of `A`" | `∀ c' ∈ carrierCrossings hn hP S A, c' ≠ c → ¬ Interlaces hn hP c c'` (def:interlace `Interlaces`, Interlacement.lean:16, in `G_P`; `c' ≠ c` literal, redundant by `interlaces_irrefl` :21) |
| 4700 | "Then `c(A) = 0`" | `cornerCoefficient hn hP S A hS = 0` (def:C, CornerStateSum.lean:110; total coefficient) |

### Row 105 (sm-3:4801-4809) → `CornerValuesData` (§3), fields `embedded_value`, `isolated_zero`
| tex | printed | Lean |
|---|---|---|
| 4803 | "(i) If `Q` is uniform and embedded (`m_Q = 0`)" | `CarrierUniform hn hP S q → carrierCrossingCount hn hP S q = 0 →` (the parenthesis DEFINES embedded; row-104 `Embedded (ccpCornerPolygon …)` is derived, `cvl_embedded_of_no_crossings`) |
| 4803-4804 | "then `\|r_Q\| = 1`, `d_Q = 0` and `c(Q) = 1`" | `\|carrierRotation hn hP S q\| = 1 ∧ cornerSlot hn hP S q = 0 ∧ cornerCoefficient hn hP S q hS = 1` (`r_Q = rot(Q)` real, def:uniform sm-3:245; `d_Q = cornerSlot` in ℤ) |
| 4805-4806 | "(ii) If `Q` is uniform and `{y}` is a crossing of `Q` interlacing no other crossing of `Q`, then `c(Q) = 0`" | row 103's clause with `(q, y)` for `(A, c)` |

### Row 110 (sm-4:267-274) → `CS7Data` (§4), one field `vertex_edge_law`
| tex | printed | Lean |
|---|---|---|
| 269 | "At a simple vertex–edge wall at `(M; a)`" | `g : WallGerm n`, `h : g.VertexEdgeAt M a` (def:walls (V), NamedWallPredicates.lean:19), `hn : 3 ≤ n` (implied: `ContactSeparated` forces `n ≥ 5`) |
| 269 | "of bigon or sliding type" | no hypothesis: exhaustive dichotomy `vertexEdge_bigon_or_sliding` (:46); companions `CS7Data.bigon` (`g.BigonAt`) / `.sliding` (`g.SlidingAt`) |
| 269-270 | "with halves `λ₁, λ₂` (Definition def:deletion-halves)" | `firstHalf g.center M a`, `secondHalf g.center M a` (DeletionHalvesDefinition.lean); `h₁ : Generic (firstHalf …)`, `h₂ : Generic (secondHalf …)` quantified (lem:children (ii) `vertex_halves_children`, Children.lean:12, supplies them; proof-irrelevant); sizes `contactHalfSizes_bounds hn h.1` (ContactHalfSizes.lean:45), `NeZero` instances ContactHalfIndices.lean:11-14 |
| 270-271 | "contact sign `s = χ_{a,a+1,M}(P₋)`" | `(g.contactSign M a : ℤ)` (NamedWallSides.lean:58 = `chi (sideTuple false sideBase) a (a+1) M`; constant on `P₋`: `contactSign_eq_at` :61; `CS7Data.contactSign_literal` shows it is `χ` at the very `tm`) |
| 272 | "`C(P₊) − C(P₋) = s C(λ₁) C(λ₂)`" | `∀ tp tm : g.SideParameter, cornerStateSum hn (g.sideTuple true tp).property − cornerStateSum hn (g.sideTuple false tm).property = s * (cornerStateSum _ h₁ * cornerStateSum _ h₂)` (sides at ALL parameters, the accepted C-row convention of prop:C-silent / hyp:R; chamber values by prop:C-chamber) |

### Row 112 (sm-4:984-991) → `CSoftData` (§5), one field `soft_theorem`
| tex | printed | Lean |
|---|---|---|
| 986 | "Let `P` be generic, `j` a vertex, `q` admissible" | `hn : 3 ≤ n`, `hP : Generic P`, `j : ZMod n`, `q : Plane`, `SoftAdmissible P j q` (SoftInsertionTuple.lean:65) |
| 986-987 | "`P_ε` the soft insertion of Definition def:soft, with attachment signs `χ_±`" | `softInsertion P j q ε : LabelledTuple (n+1)` (:22); `softAttachmentMinus/Plus P j q` (:74/:77) inside `softAmplitudeMultiplier` |
| 987-988 | "for all sufficiently small `ε > 0`" | `∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε, 0 < ε → ε < ε₁ →` |
| 989 | "`C(P_ε) = (χ₋+χ₊)/2 · C(P)`" | `∀ hQ : Generic (softInsertion P j q ε), (cornerStateSum (by omega : 3 ≤ n+1) hQ : ℚ) = SoftDuplication.softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ)` (SoftAmplitudeSectors.lean:96 = `(χ₋+χ₊)/2`) |

Row theorems: `SM.thm_C_S7 : CS7Data`, `SM.thm_C_soft : CSoftData` (FIXED names, work/lean/axiom-policy.json:46-47);
`SM.cb_singleton : CbSingletonData`, `SM.corner_values : CornerValuesData` (proposed, free — grep). Hypothesis style as
`SM.thm_C_S3 : CS3Data`, `SM.thm_C_S5 : CS5Data`; hyp:R never enters this lane.

## 2. Model decisions

### 2.1 The floor interface — JUDGE'S REPAIR (both candidates copied a superseded shape)

Facts. Both sketches copy `CarrierUniformOrOneDissent := CarrierUniform ∨ ∃ τ ≠ 0, one dissent −τ` and
`a_floor : … → cornerSlot ≤ mindegAZ (cornerHomfly …)` from work/drafts/gap2/Gap2Statements.lean §8. The floor lane's
FINAL (work/drafts/floor/Statements_FINAL.lean:350-385, PLAN_FINAL.md §0 "thm:floor alternative: A", "display: A") is
```
def AllLeftOrOneRight {m} (Q : LabelledTuple m) : Prop :=
  (∀ j, turn Q j = 1) ∨ (∃ j₀, turn Q j₀ = -1 ∧ ∀ j, j ≠ j₀ → turn Q j = 1)
def CarrierUniformOrOneDissent hn hP S q : Prop :=
  AllLeftOrOneRight (ccpCornerPolygon hn hP S q) ∨ AllLeftOrOneRight (reversal (ccpCornerPolygon hn hP S q))
structure FloorTheoremData : Prop where
  a_floor : … → CarrierUniformOrOneDissent hn hP S q →
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) ∧
    1 - (carrierCrossingCount hn hP S q : ℝ) - |carrierRotation hn hP S q| ≤ (mindegAZ (cornerHomfly hn hP S q hS) : ℝ)
  z_parity : … → InSupportM 1 (cornerHomfly …) ∧ 0 ≤ mindegZZ (cornerHomfly …)
```
Decision. Statements_FINAL.lean §0 copies this VERBATIM (to be deleted when the floor module lands). The proof routes of
rows 103/110 produce turn patterns in the SIGNED form (this is how lem:uniformrot `uniform_rotation`,
UniformRotation.lean:63, is stated), so §0 adds `SignedUniformOrOneDissent Q := ∃ τ ≠ 0, (∀ j, turn Q j = τ) ∨ (∃ j₀,
turn Q j₀ = −τ ∧ ∀ j ≠ j₀, turn Q j = τ)` and PROVES `allLeftOrOneRight_of_signed` (by `turn_reversal`, Reversal.lean:61:
`turn (reversal Q) i = −turn Q (2 − i)`; the dissent moves to `2 − j₀`), `carrierUniformOrOneDissent_of_signed`,
`signedUniformOrOneDissent_of_uniform`, and the projection `FloorTheoremData.slot_le_of_signed` (= `a_floor`'s `.1` at a
signed pattern) — the ONLY way the floor is consumed (rows 103 and 110). The leaves `sg_daughters_rotation` and the
bigon route hand out `SignedUniformOrOneDissent (ccpCornerPolygon …)`. Load-bearing for the floor lane: (a) keep the
ONE-DISSENT alternative (cb:singleton's second daughter and thm:C-S7's noninterlacing half contact carriers are
one-dissent, never uniform: sm-3:4730-4733, sm-4:765-769, 861-863); (b) keep the ℤ conjunct `cornerSlot ≤ mindegAZ H` on
the WHOLE polynomial (the extraction bounds the `a`-degree of a PRODUCT via `mindegAZ_mul`). Any further drift moves §0
and the 40-line bridge only; no statement of this lane changes. `z_parity` is never used (FR-CC-10; nonnegative
`z`-support where needed is `lp_core.knot_support`, PolynomialBlock.lean:1141).

### 2.2 Retained from B
`CS7Data.vertex_edge_law` (consumer shape); `CSoftData.soft_theorem` (`∀ hQ`); the three `sg_` leaves with the owner-iff
interface; `sg_slot_identity`; `cornerHomfly_ne_zero`, `coeffAt_mul_eq_zero_of_lt_floor`; the `∃ δ`-form branch leaves
`s7_sliding_law_at`, `s7_bigon_law_at` and the PROVED reduction (`vertexEdge_bigon_or_sliding` + `cornerStateSum_side_eq`,
HypR.lean:119, at `t := min δ radius / 2`); the algebra leaves `s7_universal_extraction`, `s7_corner_product`; the three
`sft_` sector leaves and the PROVED sector-exhaustion assembly `thm_C_soft_of_cornerValues`; prefixes `sg_ cvl_ s7_ sft_`.

### 2.3 Grafted from A
`cvl_embedded_of_no_crossings` PROVED (A's `cv_embedded_of_crossingFree`) and `corner_values_i` PROVED with the literal
three conclusions (A's `corner_values_embedded`); `CornerValuesData.embedded_rotationInt`; the explicit
`hsing : CbSingletonData` parameter of `s7_bigon_law_at` and `thm_C_S7_of hF hsing`; `CS7Data.bigon/.sliding`,
`CS7Data.contactSign_literal`; `CSoftData.doubled`; A's `∃ hQ` form as `CSoftData.exists_generic` (PROVED from
`soft_family_generic` (SoftGenericLemma.lean:36) clause (i)'s `∃ δ > 0, ∃ B, ∀ ε ∈ (0, δ), ∃ hQ, …`). Not adopted: A's
`firstHalfStateSum`/`secondHalfStateSum` wrappers (new definitions inside a fixed-name statement), the single `cs_split`
leaf, the leaves at arbitrary `tp tm`.

### 2.4 Names
Rows: `SM.thm_C_S7`, `SM.thm_C_soft` (fixed), `SM.cb_singleton`, `SM.corner_values` (proposed; no clash in work/lean/SM,
CV, Bridge — grep). Library: `cb_singleton_of_floor`, `corner_values_i`, `corner_values_of_singleton/_of_floor`,
`thm_C_S7_of`, `thm_C_S7_of_floor`, `thm_C_soft_of_cornerValues/_of_floor`, `carrierUniformOrOneDissent_of_signed`,
`SignedUniformOrOneDissent`, `FloorTheoremData.slot_le_of_signed`. `AllLeftOrOneRight`, `CarrierUniformOrOneDissent`,
`FloorTheoremData` are the floor lane's (§0 copy, deleted at its port). Leaf prefixes `sg_ cvl_ s7_ sft_`.

## 3. Proof routes (accepted lemmas by file:line, grep-verified; where the floor and the singleton enter)

### 3.1 Row 103 (sm-3:4703-4759) — leaves `sg_*`, assembly `cb_singleton_of_floor` PROVED
1. (4704-4709, U103-A `sg_isolated_undominated`) `c ∈ U(S)`: `c ∉ S` (`carrierCrossings_subset_compl`, CarrierCrossings.lean;
   def:smoothing's `crossings_of` takes unselected crossings), `c ∉ N(S)` (both visits on `A`: contrapositive of
   `neighbor_visits_separated`, CarriersLemma.lean ~95). "An undominated label interlacing `c` would have the same owner
   `A`": lem:carriers (iv) `noncrossing` (CarriersLemma.lean:107-118; `Interlaces` unfolds to `crossingVisitBetween`,
   Interlacement.lean:10-19) + (iii) `nonneighbor_visits_together` ⇒ every undominated interlacer of `c` is in
   `carrierCrossings A`, excluded by `hiso`; so `N(c) ∩ U(S) = ∅`. Then `greedy_independent` (CBProducts.lean:1911) gives
   `hS'`, `greedy_step` (:1917: `U(insert c T) = U(T) ∖ ({c} ∪ N(c))`) gives `U(S') = U(S).erase c`.
2. (4711-4718, U103-D) daughters: `smoothingSuccessor_insert_child_data` (CarrierInsertOrbits.lean:49; `T = S`, `v` a
   visit of `c`, `owner S (inr v) = owner S (inr (twin v)) = A` by `crossings_of`) gives the two cycles `inr v :: BL`,
   `inr (twin v) :: AL` and ownership; `Λ₁ ≠ Λ₂` and the count `component_card_insert` (CarrierComponentCount.lean:58);
   spectators unchanged `owner_insert_iff_of_unaffected` (:99), `componentCycle_insert_unaffected` (:121),
   `smoothingSuccessor_insert_other` (CarrierSingleSwitch.lean:96); refinement only splits `owner_insert_eq_imp`
   (CarrierOrbitRefinement.lean:80). Crossing partition `carrierCrossings S A = {c} ⊔ cc S' Λ₁ ⊔ cc S' Λ₂` (a label not
   interlacing `c` keeps both visits in one slice of the rotated mark list; interlacing case
   `interlaces_twin_different_slices`, CarrierNeighborSeparation.lean) ⇒ `m_A = m₁ + m₂ + 1`.
3. (4719-4724, eq. cb:singleton-products; U103-B/C/D) `cb_products` (CBProducts.lean:1864; bundle CBBlocks.lean:
   `product`, `count`, `one_owner`, `owned_by`, `polynomial_independent`, `block_diagram`) at `S` for `A` and at `S'` for
   `Λ₁, Λ₂`. New: (a) `Piece S' ≃ {H : Piece S // pieceLabels H ≠ {c}}` label-preserving (`c` isolated in `G_P[U(S)]`;
   Mathlib `SimpleGraph.ConnectedComponent`, `induce`, `Reachable` transfer) [U103-B]; (b) `blockPoly S H = blockPoly S' H'`
   for equal labels: an `IsBlockCarrierDiagram S' H' D` over a refinement `T ⊇ S' ⊇ S` (`exists_blockCarrier`,
   CBProducts.lean:1740) is one of `H`, and `polynomial_independent` on both sides pins `SM.P D` (the
   `blockPoly_eq_of_labels_eq` promised at CBBlocks.lean:105); `blockPoly S {c} = 1`: the block diagram has one crossing
   (`carrierCrossingEquiv`, LinkPositiveLift.lean:799) so `single_crossing.one_crossing` (SingleCrossing.lean:152-165)
   [U103-C]; (c) a block `H ≠ {c}` owned by `A` is owned at `S'` by exactly one daughter (`one_owner` at `S'` +
   `owner_insert_eq_imp`; connectedness induction on `H`), other carriers' blocks stay [U103-D]. `cornerHomfly =
   carrierPoly` by `equals_Hplus` / `P_eq_homfly` (PolynomialBlock.lean:667).
4. (4725-4741, eq. cb:singleton-rotations; U103-E `sg_daughters_rotation`) corners of `Λᵢ` = `A`'s corners in the slice +
   one new smoothing corner (`ccpCornerMark`, lem:carriers (i) `component_cycle`); inherited turns unchanged
   (`ccpCornerPolygon_turn_vertex/_smoothing`, CarrierCornerPolygon.lean:598-620 — the turn is a function of the mark,
   CX1's `markTurn`); the two new turns are `crossingSign(dᵢ,dⱼ)` and its negative (lem:carriers (ii), last clause of
   `corner_polygons`; `crossingSign_swap`); `≥ 3` corners (`ccpCornerCount_ge_three`, CarrierCornerPolygon.lean:691) ⇒ one
   daughter uniform of `A`'s sign `τ`, the other one-dissent — `SignedUniformOrOneDissent` for both. Real sum: a real
   `markPrincipalTurn` extending `markTurn`, `principalTurn (ccpCornerPolygon …) j = markPrincipalTurn (ccpCornerMark …
   j)`, inherited corners keep their direction pairs (corner edges are positive multiples of the original edges,
   `corner_polygons.2.1`), the two new principal angles cancel (`det ≠ 0`, principal-angle antisymmetry) ⇒
   `carrierRotation A = r₁ + r₂`; `uniform_rotation` (UniformRotation.lean:63, clauses (i)/(ii)/(iii)/(iv)) puts all three
   on `τ`'s ray ⇒ `|r_A| = |r₁| + |r₂|`, cast by `carrierRotationInt_cast` (CornerStateSum.lean:73).
5. (4742-4757) FLOOR ENTERS (PROVED assembly): `hF.slot_le_of_signed … Λᵢ` gives `dᵢ ≤ mindegAZ Hᵢ`; `Hᵢ ≠ 0`
   (`cornerHomfly_ne_zero` = `lp_core.ne_zero` PolynomialBlock.lean:1136 via `P_eq_homfly`); `d_A = d₁ + d₂ − 2`
   (`sg_slot_identity`); `coeffAt_mul_eq_zero_of_lt_floor` (`mindegAZ_spec` LinkLaurentRing.lean:513, `mindegAZ_mul` :757).
   FR-CC-3: the printed `[z⁰]`-row detour (`f_A = g₁g₂`, case `f_A = 0`) is replaced by the full-polynomial bound.

### 3.2 Row 105 (sm-3:4810-4820) — (i) PROVED, (ii) = row 103
(i) `corner_values_i`: `carrierCrossings = ∅` (`Finset.card_eq_zero`); `cvl_embedded_of_no_crossings` (nonzero edges
`corner_polygons.2.1`, remote edges disjoint `nonadjacent_meet_crossing` LinkPositiveLift.lean:520 (any common point is a
carrier crossing), consecutive edges meet at the corner `consecutive_meet` :698 + `edgePoint_one/zero`);
`cb_embedded_rotation` (EmbeddedRotation.lean:1081; `3 ≤ ccpCornerCount` = `corner_polygons.2.2.1`,
`ccpCornerPolygon_regular` :679) `.pm_one` ⇒ `|carrierRotation| = 1`; `carrierRotationInt_cast` ⇒ `|rInt| = 1`;
`cornerSlot = 1 − 0 − 1 = 0`; `P_circle` (PolynomialBlock.lean:609) on `positiveLift_isCrossingFreeCircle`
(LinkPositiveLift.lean:833), `P_eq_homfly`, `coeffAt_one` (LinkLaurentRing.lean:306). No floor. thm:comparison (f) can
consume `corner_values_i` at once (library). (ii) `corner_values_of_singleton` (PROVED).

### 3.3 Row 110 (sm-4:277-908) — reduction PROVED; leaves `s7_sliding_law_at` (floor-free), `s7_bigon_law_at hF hsing`
Setup (276-289): lem:wall-sides (V) `vertex_sides` (VertexSides.lean:40; `VertexSidesData`: interior crossings,
`VertexCrossingData` `X(P₊) ∆ X(P₋) = {{a,M−1},{a,M}}` ContactCrossingSides.lean:12, `SlidingCrossingPattern`, persistent
visit order `VertexLocalData.visit_order`, `contactVisitTransport` VertexSides.lean:16-28), `vertex_halves_children`
(Children.lean:12), `vertex_contact_signs` (NamedWallSides.lean:65: `χ(P₋) = s`, `χ(P₊) = −s`), selector form
`C_X1.selector_form` / `stateTerm` (CX1.lean; CS3.lean:2360-2380 as a sum over all supports).
Sliding (300-406; U110-A/B/C/D/E): (1) supports avoiding `x₋` cancel term by term — a partial `MarkTransport`
`P₋ ↔ P₊` on persistent crossings (CSilent `sideTransport` pattern, CSilent.lean:1668, contact crossing removed), corner
polygons regular through the wall, rotation constant (lem:rot (ii) as in CChamber `cornerCoefficient_path`), homfly equal
(`cornerCoefficient_transport` CChamber.lean:481 via `positiveLiftRecordIso` CBProducts.lean:946, or a `Deform` as CS3
§E); (2) supports containing `x₋`: bijection eq. s7c:sliding-bijection with `Ind(λ₁) × Ind(λ₂)`
(`HalvesData.first/second_interior_inclusions`, `cut_segments`, DeletionHalvesDefinition.lean), carriers of `S` ↔ carriers
of `S₁ ⊔ S₂` (NEW half-support transport: the only precedent is cor:flat-carriers, SM/FlatCarriers.lean), the only changed
direction lists eq. s7c:short-direction-lists, equal signed rotations by principal-angle addition in one open half-plane
(eq. s7c:turn-short-a/b); (3) selector table eq. s7c:short-selector on `carrierWeight` ⇒ `W₊ − W₋ = s W₁W₂`; (4)
`Finset.sum_bij` + distributivity.
Bigon (407-874): (1) `B = (1−ε)J` (U110-F): ineligible `T` cancel by the partial transport `P₀ ↔ P₂`; eligible `T` ↔
`(T₁,T₂)` (eq. s7c:eligible-bijection); at `ε = 0`, `T ∪ {x,y}` smooths to the contact triangle (three corners of sign
`−s₀`, crossing-free uniform carrier: `corner_values_i` gives `|rot| = 1, d = 0, c = 1`) plus the successors of `T₁,T₂`.
(2) universal skein (U110-G): `lp_core.skein` (PolynomialBlock.lean:1122) at `q = x` with `IsSkeinTriple` (LinkMoves.lean:
751: `Dm = Dp.switch x`, `IsOrientedSmoothing` :743); `D_H.switch x` ≃ `D_L` after an R-II deletion of the bigon `{x,y}` —
`lp_core.reidemeister_II` (:1147) with an `RIIData` witness (:599) on the actual polygonal lifts, then `presentations`
(PolynomialBlock.lean:1177) / `record_polynomial` (:1096); the smoothing `D_A` is a two-component diagram whose
`knotRestrict`s (MarkedProducts.lean:126) have the records of the half contact carriers (at `ε = 0` after an `RIData`
(:569) curl deletion, `lp_core.reidemeister_I` :1146); `s7_universal_extraction` (coefficient shifts of `R.aInv`, `R.z` —
no shift lemmas in LinkLaurentRing yet; `coeffAt_mul_of_max_weight` :719 is the nearest tool). (3) two-component row
(U110-H): `homflyrows.two_component_row` (MarkedProducts.lean:323/381, `two_component_row_of_lowest` :2500) with
`twoLinking D_A 0 1 = 2ℓ` (:144), writhe counts eq. s7c:interlacing-writhe-row / s7c:noninterlacing-writhe from
`positiveLift_writhe_eq_carrierCrossingCount` (LinkPositiveLift.lean:820) + the crossing partition. (4) rotation ledger
(U110-I): eq. s7c:full-rotation (regular family through the wall, lem:rot (ii)), eq. s7c:rotation-ledger (contact turns
`β`, `π−α`, `β−α∓π`: TurnLift/principalAngle library, `rotationNumber_integer`), same-sign uniformity ⇒ `R_L = R₁+R₂`
(`ε=1`) or `R₁+R₂−R_L = −1` (`ε=0`) via `uniform_rotation`. (5) FLOOR ENTERS (U110-J; sm-4:655-660, 765-769):
interlacing — `hF.slot_le_of_signed` at the two UNIFORM half contact carriers `Lᵢ`, read as carriers of the decompositions
`Tᵢ` of the generic halves `λᵢ` (the printed hypothesis discharge 800-835: `Lᵢ` is the boundary successor of `T` closed at
the cut; `Component hn' hλᵢ Tᵢ` literally — U110-B), then `s7_corner_product` (2nd conjunct uses `lp_core.knot_support`
:1141 for nonnegative `z`-support) ⇒ `Ω_H − Ω_L = −ω₁ω₂`; noninterlacing — the floor at the two ONE-DISSENT half contact
carriers, both reads `K−4, K−2` below the floor `K` (`coeffAt_mul_eq_zero_of_lt_floor`); SINGLETON ENTERS (777-783):
`hsing.isolated_zero` at the support `T ∪ {x}` with the isolated block `{y}` (owner uniform, else the selector is zero);
different-block alternative (785-813): both newborns singletons, `f_H = f_L = f₁f₂`, floors again at `K−2, K−4`. (6)
`B + R_ret = J` (eq. s7c:bigon-total; U110-K `s7_bigon_law_at`).
Genuinely new (no accepted analogue): the contact-wall partial mark transport; the half ↔ interval carrier correspondence
incl. the contact carriers at the nongeneric centre; `RII`/`RI` witnesses on polygonal lifts and the identification of
`switch`/oriented smoothing with the half lifts; two-component bookkeeping on actual lifts; the contact rotation ledger.
Reusable: CS3 §A `Deform`/`Reparam` (CS3.lean:41-1300), CChamber `MarkTransport` + `cornerStateSum_transport`
(CChamber.lean:122, 503), CSilent's family machinery, CV/ChamberInvII `pieceEquiv` / `homfly_geoPositiveLift_eq_of_mem_chamber`
(:305, :261) for spectator blocks, the CB record bridge (KL1) for `RecordIso`s.

### 3.4 Row 112 (sm-4:993-1147) — three sector leaves; assembly PROVED
Sector dichotomy (proved): `χ₋, χ₊ ≠ 0` (`sft_attachment_ne_zero`, admissibility), `τ = turn P j ≠ 0` (`sft_turn_ne_zero`,
(G1)); patterns `(−τ,−τ)`, `χ₋ ≠ χ₊`, `(τ,τ)` with multipliers `−τ, 0, τ` = `softAmplitudeMultiplier`.
Same-sign (1024-1057, U112-A/C, NO floor): `soft_family_generic` (SoftGenericLemma.lean:36) (iv) same Gauss word, (ii)
turns `τ` at `M` become `τ, τ` at `M, M_ε`, (iii) inherited visits with order and determinant signs; a soft mark transport
`Mark P ↪ Mark P_ε` (vertex `softOldIndex`, visits `softInheritedVisit`, mark list = parent list with `inl (softNewIndex j)`
inserted; `smoothingSuccessor` related by contracting the new vertex) ⇒ `Component ≃`, owners, corner marks, uniformity
`↔`; rotation equality by principal-angle addition in the turn wedge + `rotationNumber_integer` for small `ε`; coefficient
equality by CS3's flat subdivision `Reparam` (`reparam_positiveDiagram_single_appendVertex`, CS3.lean:1166) at the foot on
`E_j` and a `Deform` of the one-component shadow moving the flat vertex to `M_ε` with constant crossing set
(`homfly_positiveDiagram_single_of_family`, CS3.lean:592); `ℓ(P_ε) = ℓ(P) + [τ=1]` ⇒ `C(P_ε) = −τ C(P)`.
Mixed (1059-1065, U112-B, NO floor): the soft edge has no crossing (clause (i)), so `M, M_ε` are consecutive corners of one
carrier with turns `−χ₋ ≠ −χ₊` — thm:C-S5's argument verbatim (`Carrier.markSuccessor_vertex_of_no_crossing`, CS5.lean:30;
`ccpCornerPolygon_turn_vertex`; the draft lemma `cornerStateSum_eq_zero_of_consecutive_opposite`, work/drafts/CS5B.lean:171,
is exactly this and can be re-proved as `sft_`): `C(P_ε) = 0`.
Loop (1067-1143, U112-D; floor via 105 (ii)): newborn `y` with adjacent visits ⇒ interlaces nothing; `Ind(P_ε) = {S} ⊔
{S ∪ {y}}`; supports omitting `y`: the carrier `Q'` through `y` has `y` isolated ⇒ `hCV.isolated_zero` kills the term
when uniform (HERE the floor enters, through 103); `S ∪ {y}`: smooth `y` first (`smoothingSuccessor_insert_child_data`
at `y`; order independence is definitional, `smoothingSuccessor = ρ ∘ selectedMarkPerm S`), the triangle `(b, M, M_ε)` is
crossing-free uniform ⇒ `corner_values_i` (value 1), the residual cycle ≅ `P`'s traversal with corner `M` replaced by the
smoothing corner `y` of sign `τ` (clause (ii) `sgn det(u, D_ε) = τ`): the same transport/deformation as same-sign;
`ℓ(P_ε) − ℓ(P) = −[τ=1] + 2[τ=−1]`, one extra selected crossing, one factor 1 ⇒ `C(P_ε) = τ C(P)`.

## 4. Unit decomposition (byte-identical copies of Statements_FINAL.lean; statements frozen; leaves `sorry`; helpers prefixed)

Check per unit: `cd work/lean && lake env lean ../drafts/corner/U_<unit>.lean`. Assembly: concatenate in file order, clash
scan, `#print axioms` (expected [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]),
port after statement review; §0 deleted when the floor module lands; §6 row theorems declared only then (D-F11/D-F14).
Reassessment rule per UNIT (2 attempts / 60 min), not per row.

| unit | prefix | leaf / content | lines | hours | deps | wave |
|---|---|---|---|---|---|---|
| U103-A | `sg_` | `sg_isolated_undominated` (Interlaces ⇒ alternating visits, `noncrossing`, `greedy_*`) | 300 | 4 | accepted | 1 |
| U103-B | `sgb_` | `Piece (insert c S) ≃ {H : Piece S // labels ≠ {c}}` label-preserving (Mathlib ConnectedComponent/induce) | 450 | 6 | U103-A stmt | 1 |
| U103-C | `sgc_` | `blockPoly` determined by labels across `S ⊆ S'`; `blockPoly {c} = 1` (lc:single-crossing) | 250 | 3 | accepted | 1 |
| U103-D | `sgd_` | `sg_daughters_products` (daughters, owner `↔`, block redistribution, `P_A = P₁P₂`, `m_A = m₁+m₂+1`) | 650 | 9 | A, B, C | 2 (critical) |
| U103-E | `sge_` | `sg_daughters_rotation` (`markPrincipalTurn`, rotation as mark sum, signed patterns, `\|r_A\| = \|r₁\|+\|r₂\|`) | 700 | 9 | accepted | 1 (HIGH) |
| U103-F | — | assembly `cb_singleton_of_floor` — DONE; review | 0 | 1 | D, E | 3 |
| U105 | `cvl_` | `cvl_embedded_of_no_crossings`, `corner_values_i` — DONE (grafted from A); review | 0 | 0.5 | — | — |
| U110-A | `s7a_` | contact-wall partial mark transport on persistent crossings (turns, rotations, homfly of lifts) | 1500 | 20 | accepted | 1 (critical) |
| U110-B | `s7b_` | halves ↔ intervals: support bijections (sliding, eligible), carrier correspondences, `L*, L₁, L₂` as carriers of `Tᵢ` on `λᵢ` (floor-domain discharge) | 2000 | 25 | accepted | 1 (critical, HIGH) |
| U110-C | `s7c_` | selector algebra on `carrierWeight` (s7c:short-selector, interlacing/noninterlacing, triangle weight) | 600 | 7 | accepted | 1 |
| U110-D | `s7d_` | coefficient transport for spectators / relocated carriers (RecordIso via CB record bridge, or Deform) | 1500 | 20 | A stmt | 1 |
| U110-E | `s7e_` | `s7_sliding_law_at` | 500 | 6 | A, B, C, D | 2 |
| U110-F | `s7f_` | bigon two-newborn sector, ineligible cancellation (`B = (1−ε)J`; uses `corner_values_i`) | 1200 | 15 | A, B | 2 |
| U110-G | `s7g_` | skein extraction: `IsSkeinTriple` at `q`, `RIIData` witness (bigon `{x,y}`), `RIData` witness (curl `y`), record identifications of `switch`/smoothing with `D_L`/`D_A`, `s7_universal_extraction` | 2500 | 35 | accepted | 1 (RISKIEST) |
| U110-H | `s7h_` | two-component row: `knotRestrict`, `twoLinking = 2ℓ`, writhe counts | 600 | 8 | G stmt | 1 |
| U110-I | `s7i_` | contact rotation ledger (s7c:full-rotation, s7c:rotation-ledger, `R`-identities) | 900 | 12 | accepted | 1 |
| U110-J | `s7j_` | floor leaves: `s7_corner_product` 2nd conjunct, noninterlacing rows zero, one-newborn rows via `hsing`, different-block rows | 700 | 9 | G, H, I stmts | 2 |
| U110-K | `s7k_` | `s7_bigon_law_at` (assembly of F, G, H, I, J) | 500 | 6 | all 110 | 3 |
| U112-A | `sfta_` | soft mark transport and `Component ≃` for common supports | 900 | 12 | accepted | 1 (critical) |
| U112-B | `sftb_` | `sft_mixed` (CS5 pattern) | 200 | 3 | accepted | 1 |
| U112-C | `sftc_` | `sft_same_sign` (uniformity `↔`, rotation equality, coefficient equality by CS3 §A, `ℓ` count) | 1800 | 24 | A | 2 |
| U112-D | `sftd_` | `sft_loop` (isolated newborn, `Ind(P_ε)`, triangle via `corner_values_i`, residual transport, signs) | 2200 | 28 | A, `hCV` | 2 |
| U112-E | — | assembly `thm_C_soft_of_cornerValues` — DONE | 0 | 0.5 | — | — |
| total | | 10 leaves open | **≈ 19,950 (say 20,000)** | ≈ 263 prover-h; 3 waves; ~5-8 days wall with 6-8 lanes | | |

Per row: 103 ≈ 2,350 / 32 h; 105 done; 110 ≈ 12,500 / 163 h (critical path U110-B → U110-E/F → U110-J → U110-K, ≈ 90 h
wall); 112 ≈ 5,100 / 67 h. Order: 103 (A, B, C, E parallel → D → F) and 110/112's floor-free units start NOW; 110's sliding
branch (`s7_sliding_law_at`) and 112's same-sign/mixed sectors are unconditional library theorems on their own. FINAL_REVIEW
should be prepared for the honest intermediate state "103/105/112 conditional-complete, 110 sliding proved, bigon stated".
First units to launch (wave 1, all against the frozen statements): U110-G (probe `RIData`/`RIIData` on a polygonal lift
FIRST — go/no-go for the whole bigon route), U110-B, U110-A, U103-E, U103-A, U103-B, U103-C, U112-A, U112-B, U110-C, U110-D,
U110-H, U110-I.

## 5. Fidelity risks FR-CC-* — the executor writes these into AUTHOR_NOTES BEFORE the rows are stated

FR-CC-1 (103, 105 (ii)). "self-crossing labels of `A`" = `carrierCrossings hn hP S A` (def:smoothing's `crossings_of`:
unselected crossings with both visits on `A`; lem:carriers (iii) identifies them with the traced carrier's
self-intersections); "labels" (Gauss-word letters) are crossings (def:gauss). "interlaces no other self-crossing" is
`Interlaces` of `G_P` (def:interlace), the graph the printed proof uses ("singleton block of `G_P[U(S)]`", sm-3:4705-4706),
NOT the record interlacement of `D_A` (equal by cb:products' KL2 but not the printed object); `c' ≠ c` is kept literally.
FR-CC-2 (103). Binder as def:C / cb:blocks (sm-3:4624-4625): `hn : 3 ≤ n`, `[NeZero n]`, `hP`, `hS : IsDecomposition`
(needed to form `c(A)`); "uniform" = `CarrierUniform`; `c(A) = cornerCoefficient` (total coefficient; the printed
"without assigning a degree to it", 4744-4745, needs no case split). One field; `S'`, the daughters and eqs.
cb:singleton-products/-rotations/-gap are proof sentences (leaves `sg_*`), not clauses.
FR-CC-3 (103, proof route). The printed proof passes through the `[z⁰]` rows `f_A = g₁g₂` with lp:core's knot support and a
case `f_A = 0`; the Lean route bounds `mindeg_a` of the FULL product (`mindegAZ_mul`) and extracts `[a^{d_A} z⁰]`
directly (`coeffAt_mul_eq_zero_of_lt_floor`). Same conclusion; `z_parity` unused.
FR-CC-4 (105 (i)). "uniform and embedded (`m_Q = 0`)": the hypothesis is the printed gloss `carrierCrossingCount = 0`;
row-104 embeddedness (`Embedded (ccpCornerPolygon …)`) is a THEOREM (`cvl_embedded_of_no_crossings`). The converse is
neither needed nor asserted (thm:C-soft's loop triangle discharges `m = 0` combinatorially, sm-4:1091-1093). "uniform" is
unused by the proof (an embedded regular polygon has `|rot| = 1` regardless) and kept literally (cf. FR-ER-3 of row 104).
FR-CC-5 (105 (i)). `|r_Q| = 1` for the REAL `carrierRotation` (def:uniform's `r_Q = rot(Q)`, sm-3:245); the integer form
of def:C's slot follows by `carrierRotationInt_cast` (companion `embedded_rotationInt`). `d_Q = 0` is `cornerSlot = 0`
in ℤ. Three conclusions, one conjunction (as def:C's fields).
FR-CC-6 (105 (ii)). Literally 103's clause with `(Q, y)`; "a crossing of `Q`" = `y ∈ carrierCrossings q`. Two fields, one
per printed item.
FR-CC-7 (110). "simple vertex–edge wall at `(M; a)`, of bigon or sliding type": hypothesis `g.VertexEdgeAt M a` (def:walls
(V), NamedWallPredicates.lean:19); the type clause is the exhaustive dichotomy `vertexEdge_bigon_or_sliding` (:46) — a
description, not a hypothesis; the two typed readings are the companions `CS7Data.bigon/.sliding` (`g.BigonAt`/
`g.SlidingAt` :25-29). `hn : 3 ≤ n` bundle parameter (`ContactSeparated` forces `n ≥ 5`).
FR-CC-8 (110). `s = χ_{a,a+1,M}(P₋)` = `g.contactSign M a` (NamedWallSides.lean:58 = `chi (sideTuple false sideBase) a (a+1) M`,
constant on `P₋` by `contactSign_eq_at`, nonzero by `vertex_contact_signs`; the rendering of the accepted thm:A-S7);
`contactSign_literal` shows it equals `χ` at the very `tm`; cast `SignType → ℤ`.
FR-CC-9 (110). `C(λᵢ)` is `cornerStateSum (contactHalfSizes_bounds hn h.1).i.1 hᵢ` with the genericity proofs `h₁ h₂`
QUANTIFIED (lem:children (ii) `vertex_halves_children` supplies them; `Generic` is a Prop, so the value is independent of
the proof) — the shape of `UniquenessHypotheses.vertex_edge`; no wrapper definition. The halves' labelling (label 0 =
`μ_M`) is def:deletion-halves' own; `C` is shift-invariant (`cornerStateSum_genericShift`).
FR-CC-10 (110, 103; interface). `P₊, P₋` are read at every pair of side parameters `tp tm` (the accepted C-row convention
of prop:C-silent / hyp:R; equivalent to def:germ's chamber values by `sidePolygon_mem_side` + prop:C-chamber). Only
`a_floor`'s ℤ conjunct is consumed, at signed turn patterns via the bridge (§2.1); `z_parity` never.
FR-CC-11 (112). The identity `C(P_ε) = (χ₋+χ₊)/2 · C(P)` is read in ℚ with `softAmplitudeMultiplier P j q = (χ₋+χ₊)/2`
(SoftAmplitudeSectors.lean:96; def:soft's `softAttachmentMinus/Plus` = `χ_{*,j,j∓1}(P_ε)` for every `ε > 0`, functions of
`(P,j,q)` alone as printed); companion `doubled`: `2 C(P_ε) = (χ₋+χ₊) C(P)` in ℤ. Integer division rejected (reads as a
convention).
FR-CC-12 (112). "for all sufficiently small `ε > 0`" = `∃ ε₁ > 0, ∀ ε ∈ (0, ε₁)`; `C(P_ε)` presupposes `P_ε` generic
(lem:soft-generic (i)), quantified `∀ hQ : Generic (softInsertion P j q ε)` (the consumer's shape); the accepted
thm:A-soft's `∃ hQ` form is the PROVED companion `CSoftData.exists_generic`. `P_ε : LabelledTuple (n+1)`, `3 ≤ n+1` by
`omega`, `[NeZero (n+1)]` automatic; `q ≠ 0` implied by admissibility.
FR-CC-13 (110/112, consumer). `C` is evaluated on labelled tuples; thm:comparison consumes it on the quotient
`GenericPolygon` through `cornerStateSum_genericShift` (CChamber.lean) — the consumer's business, no adapter here.
FR-CC-14 (110, proof). The printed "actual ordinary R-II template" and the R-I curl deletion are consumed through
`lp_core.reidemeister_II/I` and need `RIIData`/`RIData` WITNESSES on the actual polygonal positive lifts (LinkMoves.lean:
569/599) — genuinely new constructions (U110-G); the statement is unaffected.
FR-CC-15 (interface). `AllLeftOrOneRight`, `CarrierUniformOrOneDissent`, `FloorTheoremData` are the floor lane's (verbatim
copy of work/drafts/floor/Statements_FINAL.lean §7), NOT this lane's statements; they are deleted at the floor port. The
rows stay conditional (`_of_floor`) until `SM.thm_floor` is accepted; the row theorems of §6 are declared and mapped only
then (D-F11/D-F14).

## 6. Riskiest steps (ranked) and fallbacks

1. U110-G — `RII`/`RI` witnesses on actual polygonal lifts; identification of `D_H.switch x` with `D_L` (after the bigon
   deletion) and of the oriented smoothing's components with the half contact carriers' lifts. Inspect `RIData`/`RIIData`
   (LinkMoves.lean:569/599) against a polygonal `positiveLift` FIRST (go/no-go). Fallback: prove the skein-triple identities
   through `presentations` after constructing the reduced diagrams directly as positive lifts of carriers of enlarged
   supports (the printed "the daughters of a singleton row are the carriers of the support enlarged by the singleton",
   sm-4:862-864).
2. U110-A/B — carriers through the contact at a nongeneric centre; `Lᵢ` must be a literal `Component hn' hλᵢ Tᵢ` of a
   decomposition of the generic half (the floor's domain). Build the half transport on MARKS, not on plane curves; the
   only precedent is FlatCarriers (5667 lines).
3. U103-E — `|r_A| = |r₁| + |r₂|` needs "inherited corners keep their principal turn under the refinement `S → S ∪ {c}`"
   (true: corner edges are positive multiples of fixed original edges, `corner_polygons.2.1`) and antisymmetry of the two
   smoothing turns; not accepted lemmas.
4. U112-A/C/D — a mark transport with DIFFERENT mark sets (one extra vertex; in the loop sector two newborn visits); the
   accepted `MarkTransport` of CSilent/CChamber assumes equal mark sets. Coefficient equality by deformation: the family
   must stay a generic one-component shadow (constant crossing set) — guaranteed on `(0, δ)` by lem:soft-generic
   (i)/(iii); the subdivision step reuses CS3 §A verbatim. The residual-cycle correspondence after "processing `y`".
5. U103-B — `Piece (insert c S) ≃ …` under `insert` (Mathlib ConnectedComponent/induce bookkeeping). Fallback: avoid
   `Piece` and prove `P_A = P₁P₂` through mp:blocks (`SM.blocks`) on the record of `D_A` — heavier.
6. Interface drift (§2.1): the floor lane must keep the one-dissent alternative and the ℤ `cornerSlot ≤ mindegAZ` conjunct
   on the full polynomial; any renaming/reshaping moves §0 and the 40-line bridge only. Freeze before U103-F / U110-J ports.
7. Row 100 is the ONLY unconditional blocker: `cb_singleton`, `corner_values`, `thm_C_S7`, `thm_C_soft` cannot be declared
   until `SM.thm_floor` exists (itself waiting on row 94 fd:contact). Everything else is conditional library material;
   `corner_values_i`, the sliding branch and the same-sign/mixed sectors are unconditional and portable after their own
   review.
8. Size: 110 is the largest row of the document (~630 TeX lines vs ~80 for thm:C-S3, which took 2.5k Lean lines); the
   11-15k estimate assumes CS3-like efficiency. Report by unit; accept "sliding proved, bigon stated" as an honest
   intermediate FINAL_REVIEW sentence.
