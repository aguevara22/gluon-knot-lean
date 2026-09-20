# DESIGN A — rows 103 cb:singleton, 105 lem:corner-values, 110 thm:C-S7, 112 thm:C-soft (fidelity-first), 2026-09-15

Architect A of the corner lane (the chain after thm:floor). Sketch: work/drafts/corner/Sketch_A.lean
(`cd work/lean && lake env lean ../drafts/corner/Sketch_A.lean`: 0 errors, 380 lines; statements sorry-free;
4 proof-route leaves `sorry`: `cs_split`, `s7_sliding`, `s7_bigon`, `so_soft_law`; PROVED outright:
`corner_values_embedded` = row 105 clause (i) [axioms standard + lit_homfly/lp_lm/lp_lm_uniqueness, as def:C],
`cs_coeff_product_zero` [standard], `CSoftData.doubled`, `CS7Data.vertex_edge_law`, `CS7Data.contactSign_literal`).

Sources (SM15): sm-3-statesum.tex 4697-4702 / 4703-4759 (103), 4801-4809 / 4810-4819 (105);
sm-4-knotlaws.tex 267-274 / 275-905 (110), 984-991 / 992-1128 (112). Dependencies (tools/claims.py):
103 ← thm:floor; 105 ← cb:singleton; 110 ← cb:singleton, thm:floor; 112 ← lem:corner-values.
Fixed names (lean/axiom-policy.json): `SM.thm_C_S7`, `SM.thm_C_soft`. Proposed: `SM.cb_singleton : CbSingletonData`,
`SM.corner_values : CornerValuesData`. Row theorems are one-liners once `SM.thm_floor : FloorTheoremData` lands (§5).

## 0. Assumed interface (to be unified with the floor lane)

Copied verbatim into Sketch_A §0 from work/drafts/gap2/Gap2Statements.lean §8 (= floor/Sketch_B.lean §2):
`CarrierUniformOrOneDissent hn hP S q := CarrierUniform ∨ ∃ τ ≠ 0, ∃ j₀, turn j₀ = −τ ∧ ∀ j ≠ j₀, turn j = τ` and
`FloorTheoremData` with `a_floor : … CarrierUniformOrOneDissent → cornerSlot ≤ mindegAZ (cornerHomfly …)` and
`z_parity`. This lane consumes ONLY `a_floor` (rows 103, 110); `z_parity` is never used (FR-CC-8). Two things the
floor lane must keep for us: (a) the ONE-DISSENT alternative in the hypothesis — cb:singleton's second daughter
and thm:C-S7's noninterlacing half contact carriers are one-dissent, never uniform (sm-3:4730-4733, sm-4:765-769,
861-863); (b) `mindegAZ` on the whole polynomial (not the `[z⁰]` row) — our extraction bounds the `a`-degree of a
PRODUCT via `mindegAZ_mul`. If the floor lane adopts floor/Sketch_A's reversal form `AllLeftOrOneRight Q ∨
AllLeftOrOneRight (reversal Q)` or adds the real-form conjunct, the consumers change by a 40-line bridge
(`turn_reversal`, SM/Reversal.lean:61) or a `.1`; statements here are unaffected.

## 1. Fidelity risks — recorded BEFORE stating (to be copied into AUTHOR_NOTES)

Row 103 (sm-3:4697-4702).
- FR-CC-1 Binder "carrier `A` of `S`": `S` is the independent support of cb:blocks' binder (sm-3:4624-4625), so
  `hS : IsDecomposition hn hP S` (also required by `c(A) = cornerCoefficient … hS`, def:C). `hn : 3 ≤ n`, `[NeZero n]`
  bundle parameters as in every accepted C-row.
- FR-CC-2 "self-crossing labels of `A`" = `carrierCrossings hn hP S A` (def:smoothing `crossings_of`: unselected
  crossings both of whose visits lie on `A`; lem:carriers (iii) `self_intersections`: exactly the self-intersections
  of the traced carrier). "Labels" (Gauss-word letters) are crossings (def:gauss).
- FR-CC-3 "interlaces no other self-crossing of `A`" = `∀ c' ∈ carrierCrossings A, c' ≠ c → ¬ Interlaces hn hP c c'`
  in `G_P` (def:interlace), the graph the printed proof uses ("singleton block of `G_P[U(S)]`", 4705-4706); `c' ≠ c`
  is redundant (`interlaces_irrefl`, SM/Interlacement.lean:22) but literal ("other"). NOT the record interlacement
  of `D_A` (equal by cb:products' KL2, but not the printed object).
- FR-CC-4 "uniform" = `CarrierUniform` (def:uniform), the index predicate of def:C.
- FR-CC-5 `c(A) = 0` = `cornerCoefficient hn hP S A hS = 0`, total coefficient (0 if the monomial is absent) — the
  printed "without assigning a degree to it" (4744-4745) needs no case split in Lean.
- FR-CC-6 the conclusion is about `A` as a carrier of `S` (not of `S' = S ∪ {c}`), as printed.
- FR-CC-7 one field; the enlarged support `S'`, the daughters, eqs. cb:singleton-products/-rotations/-gap are proof
  sentences, not clauses (companion lemmas `cs_*`).
- FR-CC-8 (proof route, disclosed) the printed proof passes through the `z⁰` rows `f_A = g₁g₂` using lp:core's knot
  support (4742-4744); the Lean route bounds `mindeg_a` of the full product (`mindegAZ_mul`, LinkLaurentRing.lean:757)
  and extracts `[a^{d_A} z⁰]` directly (`cs_coeff_product_zero`, PROVED); no `z`-parity is consumed anywhere.

Row 105 (sm-3:4801-4809).
- FR-CV-1 (i) "uniform and embedded (`m_Q = 0`)": the hypothesis is the printed gloss `carrierCrossingCount = 0`.
  Embeddedness of the corner polygon in row 104's sense (`Embedded`: nonzero edges, remote edges disjoint,
  consecutive edges meet in the shared corner) is then a THEOREM — `cv_embedded_of_crossingFree`, PROVED in the
  sketch from lem:carriers (ii) and the accepted `nonadjacent_meet_crossing` / `consecutive_meet`
  (SM/LinkPositiveLift.lean:520, 698). The converse (`Embedded ⇒ m_Q = 0`) is neither needed nor asserted; the only
  consumer (thm:C-soft's loop triangle, sm-4:1091-1093) discharges `m_Q = 0` combinatorially (the triangle cycle
  `(b, M, M_ε)` carries no unselected visit, soft-generic (iv)). Alternative reading — hypothesis `Embedded
  (ccpCornerPolygon …)` — rejected: it is the consumer-unfriendly half of the gloss and not what the parenthesis says.
- FR-CV-2 `|r_Q| = 1` stated for the real `carrierRotation` (def:uniform's `r_Q`) as printed; the integer form
  (`carrierRotationInt`) follows by `carrierRotationInt_cast`. `d_Q = 0` is `cornerSlot = 0` in `ℤ`.
- FR-CV-3 the hypothesis "uniform" in (i) is unused by the proof (an embedded regular polygon has `|rot| = 1`
  regardless, row 104); kept literally (cf. FR-ER-3 of row 104).
- FR-CV-4 (ii) is cb:singleton verbatim in CV's letters (`Q`, `y`); "a crossing of `Q`" = `y ∈ carrierCrossings q`,
  "interlacing no other crossing of `Q`" as FR-CC-3. Proved by row 103 (as printed: "satisfy Lemma cb:singleton").
- FR-CV-5 two fields, one per printed item; (i)'s three conclusions are one conjunction (as def:C's fields).

Row 110 (sm-4:267-274).
- FR-S7-1 "simple vertex–edge wall at `(M;a)`, of bigon or sliding type": the accepted def:walls (V) predicates
  `g.BigonAt M a` / `g.SlidingAt M a` (SM/NamedWallPredicates.lean:19-25 = `VertexEdgeAt` + the type clause
  `χ_{a,a+1,M−1}(P(0)) = / ≠ χ_{a,a+1,M+1}(P(0))`), one field each (as prop:C-silent's (E)/(C)). The dichotomy is
  exhaustive (`vertexEdge_bigon_or_sliding`), so `CS7Data.vertex_edge_law` (PROVED) gives the law from
  `VertexEdgeAt` alone — the shape the accepted thm:A-S7 (SM/VertexEdgeLawTree.lean) and its consumers use.
- FR-S7-2 `P₊`, `P₋`: `g.sideTuple true tp`, `g.sideTuple false tm` at ALL side parameters, independent `tp tm`
  (the accepted C-row convention of prop:C-silent and hyp:R; equivalent to def:germ's chamber values by
  `sidePolygon_mem_side` + prop:C-chamber, reviewers of C-silent/hyp:R accepted this as non-blocking).
- FR-S7-3 contact sign `s = χ_{a,a+1,M}(P₋)`: the accepted `g.contactSign M a` (SM/NamedWallSides.lean:58 =
  `chi (sideTuple false sideBase) a (a+1) M`, constant on `P₋` by `contactSign_eq_at`, nonzero by
  `vertex_contact_signs`; the rendering of the accepted thm:A-S7). `CS7Data.contactSign_literal` (PROVED) shows it
  equals `χ_{a,a+1,M}` at the very parameter `tm` of the `C(P₋)` term. Cast `SignType → ℤ`.
- FR-S7-4 "halves `λ₁, λ₂` (Definition def:deletion-halves)": the accepted `firstHalf g.center M a`,
  `secondHalf g.center M a` (SM/DeletionHalvesDefinition.lean, `HalvesData.first_vertices/second_vertices` = the
  printed vertex lists `(μ_M, …, μ_a)`, `(μ_M, μ_b, …, μ_{M−1})` at `t = 0`); generic with `≥ 3` vertices by the
  accepted lem:children (ii) (`vertex_halves_children`, `contactHalfSizes_bounds`), discharged inline as thm:C-S3
  inlined `generic_deleteVertex`. `C(λᵢ)` is wrapped as `WallGerm.firstHalfStateSum`/`secondHalfStateSum` — one
  `cornerStateSum` application under a `haveI : NeZero (…HalfSize M a)`; definitional, unfoldable. Risk: a reviewer
  may prefer the application inlined (`@cornerStateSum _ ⟨_⟩ …`); a 4-line change, no content.
- FR-S7-5 the halves' labelling (label 0 = `μ_M`) is def:deletion-halves' own; `C` is shift-invariant
  (`cornerStateSum_genericShift`, CChamber), so no labelling convention is asserted.
- FR-S7-6 `hn : 3 ≤ n` bundle parameter (implied: `ContactSeparated` forces `n ≥ 5`); `[NeZero n]`.

Row 112 (sm-4:984-991).
- FR-CS-1 "`P` generic, `j` a vertex, `q` admissible": `hP : Generic P`, `j : ZMod n`, `SoftAdmissible P j q`
  (def:soft's `admissible_iff`); `q ≠ 0` is implied.
- FR-CS-2 "for all sufficiently small `ε > 0`": `∃ ε₁, 0 < ε₁ ∧ ∀ ε, 0 < ε → ε < ε₁ → …` (the accepted thm:A-soft's
  shape without its `ε₁ ≤ ε₀` bound, which thm:C-soft does not print).
- FR-CS-3 the identity `C(P_ε) = (χ₋+χ₊)/2 · C(P)` is read in `ℚ` with the accepted
  `SoftDuplication.softAmplitudeMultiplier P j q = (χ₋+χ₊)/2` (SM/SoftAmplitudeSectors.lean:96, the accepted
  thm:A-soft's multiplier). Companion `CSoftData.doubled` (PROVED): `2·C(P_ε) = (χ₋+χ₊)·C(P)` in `ℤ`. Integer
  division `((χ₋+χ₊)/2 : ℤ)` rejected (exact, but reads as a convention).
- FR-CS-4 `P_ε` generic is part of the conclusion (`∃ hQ : Generic (softInsertion P j q ε)`, lem:soft-generic (i));
  `C(P_ε)` presupposes it. Equivalent to `∀ hQ` under lem:soft-generic; `∃` is the accepted A-soft shape.
- FR-CS-5 "with attachment signs `χ_±`" = `softAttachmentMinus/Plus P j q` (def:soft: `= χ_{*,j,j∓1}(P_ε)` for every
  `ε > 0`, fields `attachment_minus/plus`), functions of `(P, j, q)` alone, as printed ("the two equalities holding
  for every ε").
- FR-CS-6 `P_ε = softInsertion P j q ε : LabelledTuple (n+1)`; `3 ≤ n+1` by `omega`; `[NeZero (n+1)]` automatic.

## 2. Statements (Sketch_A §1-§4; one field per printed clause)

| row | bundle / field | printed clause → Lean |
|---|---|---|
| 103 | `CbSingletonData.isolated_zero` | `∀ n [NeZero n] hn P hP S hS (A : Component hn hP S), CarrierUniform hn hP S A → ∀ c ∈ carrierCrossings hn hP S A, (∀ c' ∈ carrierCrossings hn hP S A, c' ≠ c → ¬ Interlaces hn hP c c') → cornerCoefficient hn hP S A hS = 0` |
| 105 | `CornerValuesData.embedded` (i) | `… CarrierUniform → carrierCrossingCount hn hP S q = 0 → \|carrierRotation hn hP S q\| = 1 ∧ cornerSlot hn hP S q = 0 ∧ cornerCoefficient hn hP S q hS = 1` |
| 105 | `CornerValuesData.isolated` (ii) | as 103 with `q, y` |
| 110 | `CS7Data.bigon` / `.sliding` | `∀ n [NeZero n] hn (g : WallGerm n) M a (h : g.BigonAt M a ∣ g.SlidingAt M a), ∀ tp tm : g.SideParameter, C(g.sideTuple true tp) − C(g.sideTuple false tm) = (g.contactSign M a : ℤ) * g.firstHalfStateSum hn M a h.1 * g.secondHalfStateSum hn M a h.1` |
| 112 | `CSoftData.soft_law` | `∀ n [NeZero n] hn P hP j q, SoftAdmissible P j q → ∃ ε₁, 0 < ε₁ ∧ ∀ ε, 0 < ε → ε < ε₁ → ∃ hQ : Generic (softInsertion P j q ε), (cornerStateSum _ hQ : ℚ) = softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ)` |

Row theorems: `theorem SM.thm_C_S7 : CS7Data`, `theorem SM.thm_C_soft : CSoftData` (fixed names; the same
hypothesis style as `SM.thm_C_S3 : CS3Data`, `SM.thm_C_S5 : CS5Data`, hyp:R never enters this lane).

## 3. Proof routes (accepted lemmas by file:line; where the floor enters)

Row 103 (sm-3:4703-4758), leaves `cs_*`, assembled in `cb_singleton_of_floor` (PROVED modulo `cs_split`):
1. 4704-4709: `c ∈ U(S)`: `c ∉ S` (def:smoothing `crossings_of`, SM/SmoothingDefinition.lean:150-153), `c ∉ N(S)`
   (`neighbor_no_carrier` :157-159). "An undominated label interlacing `c` would have the same owner `A`":
   lem:carriers (iv) `noncrossing` (SM/CarriersLemma.lean:107-118) + (iii) `nonneighbor_visits_together` ⇒ with
   `hiso`, `N(c) ∩ U(S) = ∅`. `hS' := greedy_independent` and `U(S') = U(S) ∖ {c}` by `greedy_step`
   (SM/CBProducts.lean, companion lemmas at the end of the file).
2. 4711-4718: the split. `smoothingSuccessor_insert_child_data` (SM/CarrierInsertOrbits.lean; `T = S`, `v` a visit
   of `c`, both visits on `A` by `crossings_of`) gives the two daughters `Λ₁ = owner S' (inr v)`,
   `Λ₂ = owner S' (inr (twin v))` and the mark partition; other carriers are untouched
   (`owner_insert_iff_of_unaffected` :99); refinement only splits (`owner_insert_eq_imp`,
   SM/CarrierOrbitRefinement.lean:80). Crossing partition `carrierCrossings S A = {c} ⊔ cc S' Λ₁ ⊔ cc S' Λ₂`
   (a label not interlacing `c` keeps both visits in one slice `A`/`B` of the rotated mark list; the interlacing
   case is `interlaces_twin_different_slices`, SM/CarrierNeighborSeparation.lean) ⇒ `m_A = m₁ + m₂ + 1`.
3. 4719-4724 (eq. cb:singleton-products): `cb_products` (SM/CBProducts.lean:1864; bundle SM/CBBlocks.lean) `product`
   and `count` at `S` and at `S'`; the blocks of `S'` are the blocks of `S` other than `{c}` (`U(S') = U(S) ∖ {c}`,
   `c` isolated: Mathlib `SimpleGraph.ConnectedComponent` on the two induced graphs); a block `H ≠ {c}` owned by `A`
   is owned in `S'` by exactly one daughter (its labels do not interlace `c`; interlacing labels of `H` stay on one
   daughter by `noncrossing` at `S'`; connectedness induction on `H`); `blockPoly` transfer: an
   `IsBlockCarrierDiagram S' H' D` (`T ⊇ S' ⊇ S`, same labels) is an `IsBlockCarrierDiagram S H D`, so
   `polynomial_independent` at both gives `blockPoly hS H = blockPoly hS' H'` (the `blockPoly_eq_of_labels_eq`
   promised in SM/CBBlocks.lean:105); the singleton block: `block_diagram` gives a one-crossing actual diagram,
   `single_crossing.one_crossing` (SM/SingleCrossing.lean:152-159) gives `P = 1`, `|{c}| = 1`. Through
   `equals_Hplus` (CbBlocksDefinitionData): `cornerHomfly S A = cornerHomfly S' Λ₁ * cornerHomfly S' Λ₂`.
4. 4725-4741 (eq. cb:singleton-rotations): corners of `Λᵢ` = `A`'s corners in the slice + one new smoothing corner
   (`ccpCornerMark`, lem:carriers (i) `component_cycle`); inherited turns unchanged
   (`ccpCornerPolygon_turn_vertex/_smoothing`, SM/CarrierCornerPolygon.lean — the turn is a function of the mark,
   `markTurn` of SM/CX1.lean); the two new turns are `crossingSign(dᵢ,dⱼ)` and its negative (lem:carriers (ii),
   last clause of `corner_polygons`); `≥ 3` corners (`ccpCornerCount_ge_three`, CarrierCornerPolygon.lean:691) ⇒
   one daughter uniform (sign `τ` of `A`), the other one-dissent — EXACTLY `CarrierUniformOrOneDissent` (§0(a)).
   Real sum: `Σθ(A) = Σθ(Λ₁) + Σθ(Λ₂)` since the inherited corners keep their direction pairs (corner edges are
   positive multiples of the original edges, `corner_polygons.2.1`; `ccpOutSlot`) and the new principal turns are
   opposite (`det ≠ 0`, principal angle antisymmetry); `uniform_rotation` (SM/UniformRotation.lean:64-82) puts all
   three rotations on `τ`'s ray (`≥ 1` / `≤ −1`) ⇒ `|r_A| = |r₁| + |r₂|`, cast by `carrierRotationInt_cast`.
5. 4742-4757: FLOOR ENTERS: `hF.a_floor hn P hP (insert c S) hS' Λᵢ (hᵢ : CarrierUniformOrOneDissent …)` gives
   `kᵢ ≤ mindegAZ (cornerHomfly S' Λᵢ)`; nonvanishing `P_ne_zero` (SM/PolynomialBlock.lean:793) via `P_eq_homfly`;
   `d_A = k₁ + k₂ − 2` (slot arithmetic from 2-4, in the sketch); `cs_coeff_product_zero`
   (`coeffAt_eq_zero_of_lt_mindegA` LinkLaurentRing.lean:480, `mindegAZ_mul` :757, `mindegA_eq_mindegAZ` :508).
   `z_parity` is NOT used (FR-CC-8).

Row 105 (sm-3:4810-4819): (i) PROVED in the sketch (`corner_values_embedded`): `cv_embedded_of_crossingFree` →
`cb_embedded_rotation` (SM/EmbeddedRotation.lean:1081) `.pm_one` on `ccpCornerPolygon_regular` ⇒ `|r_Q| = 1`;
`cornerSlot = 1 − 0 − 1 = 0`; `P_circle` (PolynomialBlock.lean:609) on `positiveLift_isCrossingFreeCircle`
(LinkPositiveLift.lean:833), `coeffAt_one` (LinkLaurentRing.lean:306). No floor. (ii) = `isolated_zero` of row 103.

Row 110 (sm-4:275-905), leaves `s7_sliding` (no floor, no singleton) and `s7_bigon` (both):
- 276-289 setup: lem:wall-sides (V) `vertex_sides` (SM/VertexSides.lean:40; `VertexSidesData`: interior crossings
  = crossings not contact-affected, `VertexCrossingData` between `P₊`/`P₋`, parameter windows), lem:children (ii)
  `vertex_halves_children` (SM/Children.lean:17), contact signs `vertex_contact_signs` (NamedWallSides.lean:65:
  `χ(P₋) = s`, `χ(P₊) = −s`), selector form `C_X1.selector_form` (SM/CX1.lean), one parameter per side by
  `cornerStateSum_side_eq` (SM/HypR.lean) / `prop_C_chamber`.
- 291-372 sliding: support bijection `{S ∋ x₋} ↔ Ind(λ₁) × Ind(λ₂)` (eq. s7c:sliding-bijection), residual splitting
  (s7c:sliding-residual), relocation `φ`, equal rotations (s7c:turn-short-a/b: principal-angle additivity in one
  open half-plane), selector table (s7c:short-selector) and `W₊ − W₋ = s W₁W₂`. Needs a NEW half-support transport
  (carriers of `λᵢ` at `Tᵢ` ↔ the interval part of the carriers of `P_∓` at `S`), the analogue of the accepted
  cor:flat-carriers correspondence (SM/FlatCarriers.lean, 5667 lines) for the vertex–edge wall.
- 374-457 bigon, two-newborn sector: eligibility, bijection (s7c:eligible-bijection), the contact triangle
  (s7c:triangle-data: `rot = −s₀`, `P = 1`, `[a⁰z⁰] = 1`) — `corner_values_embedded` applies verbatim (a
  crossing-free uniform carrier), `B = (1−ε)J`.
- 459-540 the coambient diagram: the full contact carrier `L*`, the low/high lifts `D_L, D_H`, the oriented smoothing
  `D_A` of `q = x` (actual: `exists_smoothing_record`, SM/Smoothing.lean), components = the half contact carriers'
  lifts (records: `record_polynomial`/`presentations`, PolynomialBlock.lean:1096), curl deletion (`ε = 0`:
  `lp_core.reidemeister_I`), linking `ℓ = twoLinking`, writhe partition (s7c:crossing-partition).
- 542-621 turns/selectors: half/full contact turns, `wt(L*) = −s₀ wt(L₁)wt(L₂)` (interlacing),
  `W_T W₁ W₂ = 0` (noninterlacing), rotation ledger (s7c:rotation-ledger) by `rotationNumber_integer` and
  principal-angle bookkeeping; `≥ 3` corners everywhere.
- 623-724 universal skein: `lp_core.skein` on the actual triple `(D_H, D_L', D_A)` where `D_L'` (crossing switched
  at `q`) is `D_L` after an R-II deletion (`lp_core.reidemeister_II` + `record_polynomial` for "the same complete
  decorated record"); `Ω_H − Ω_L = [a^{k_L−1} z^{−1}] F_A` (s7c:universal-extraction); interlacing branch:
  `homflyrows.two_component_row` (SM/MarkedProducts.lean:363-390) + writhe count ⇒ `k_L = K − 2ℓ`; FLOOR ENTERS
  (655-660): `hF.a_floor` at the two UNIFORM half contact carriers `Lᵢ` as carriers of the decomposition `Tᵢ` of
  the generic half `λᵢ` (`vertex_halves_children` for `Generic λᵢ`; the printed "hypothesis discharge", 827-861) ⇒
  `Ω_H − Ω_L = −ω₁ω₂`, then `R_ret = J`.
- 726-791 noninterlacing: same-block alternative — FLOOR ENTERS (765-769) at the two ONE-DISSENT half contact
  carriers (their selectors may be zero; this is why `a_floor`'s hypothesis must be `CarrierUniformOrOneDissent`,
  §0(a)); one-newborn rows — SINGLETON ENTERS (777-783): `hsing.isolated_zero` at the support `T ∪ {x}` with the
  isolated block `{y}` (owner uniform, else the selector is zero); different-block alternative (785-813): both
  singletons, `f_H = f_L = f₁f₂`, floors again at `K−2, K−4`.
- 826-905 hypothesis discharge and assembly: `B + R_ret = J` for bigons; sliding separately.

Row 112 (sm-4:992-1128), leaf `so_soft_law` (needs `CornerValuesData` only):
- 993-1000: lem:soft-generic `soft_family_generic` (SM/SoftGenericLemma.lean:36-151, clauses (i)-(iv) incl. the
  loop-sector newborn `y` with adjacent visits and the oriented arc `a → M → M_ε → b` free of other visits);
  `prop_C_chamber` for constancy on the initial interval (so one small `ε₁` suffices).
- 1002-1022 records and coefficients: corresponding carriers have isomorphic named records (over/under from
  determinant signs, soft-generic (iii)) ⇒ equal `H⁺` by `record_polynomial` + `P_eq_homfly`, or by the planar
  family route of C-S3/C-silent (`homfly_positiveDiagram_single_of_family`); equal rotations ⇒ equal `d_Q`, `c(Q)`.
- 1024-1053 same-sign sector: contracting `M_ε` identifies carriers (a NEW vertex-insertion mark transport; the
  accepted `MarkTransport` of CSilent/CChamber assumes equal mark sets), turns `τ, τ` at `M, M_ε`, rotation
  convergence + `rotationNumber_integer` (SM/RotationTheorem.lean) ⇒ equality for small `ε`; `ℓ(P_ε) = ℓ(P) + [τ=1]`
  ⇒ `C(P_ε) = −τ C(P)`.
- 1055-1062 mixed sector: consecutive corners `M, M_ε` of opposite turn on one carrier, soft edge crossing-free
  (soft-generic (i)) ⇒ no uniform support ⇒ `C(P_ε) = 0` — reuse `cornerStateSum_eq_zero_of_consecutive_opposite`
  (work/drafts/CS5B.lean, the C-S5 cross-check draft, exactly this lemma).
- 1064-1128 loop sector: supports omitting `y`: `y` isolated (adjacent visits ⇒ interlaces nothing) and on one
  carrier `Q'` ⇒ CORNER-VALUES (ii) ENTERS (`hcv.isolated`, 1075-1076); supports `S ∪ {y}`: "process `y` first"
  (order independence is definitional: `smoothingSuccessor` is `ρ ∘ selectedMarkPerm S`, SmoothingDefinition
  `reconnection`), the triangle `(b, M, M_ε)` — CORNER-VALUES (i) ENTERS (`hcv.embedded`, 1091-1093; `m = 0`
  combinatorially), the residual cycle ↔ carriers of `S` on `P`, rotation convergence again,
  `ℓ(P_ε) − ℓ(P) = −[τ=1] + 2[τ=−1]` ⇒ multiplier `τ`; the three multipliers are `(χ₋+χ₊)/2`
  (`softAmplitudeMultiplier` sector lemmas, SM/SoftAmplitudeSectors.lean).

## 4. Conditional forms (library material, D-F11/D-F14 pattern; never mapped)

Sketch §5: `cb_singleton_of_floor : FloorTheoremData → CbSingletonData` (PROVED modulo `cs_split`);
`corner_values_of_singleton : CbSingletonData → CornerValuesData` (PROVED; (i) unconditional);
`corner_values_of_floor`; `thm_C_S7_of : FloorTheoremData → CbSingletonData → CS7Data` (the printed dependency
list) and `thm_C_S7_of_floor`; `thm_C_soft_of_corner_values : CornerValuesData → CSoftData` (no floor
directly) and `thm_C_soft_of_floor`. Unconditional NOW: `corner_values_embedded` (row 105 (i)) — portable as
library at once (the ROW stays pending until 103 lands, a bundle is accepted whole). Once `SM.thm_floor` exists:
`theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor`, `theorem thm_C_soft : CSoftData :=
thm_C_soft_of_floor thm_floor`, `theorem cb_singleton := cb_singleton_of_floor thm_floor`,
`theorem corner_values := corner_values_of_floor thm_floor` — and the leaves become the units' targets.

## 5. Units (byte-identical skeleton copies, frozen statements, leaves `sorry`, helper prefixes), estimates

| unit | leaves / content | prefix | lines | hours | risk |
|---|---|---|---|---|---|
| U-CS1 | `c ∈ U(S)`, `N(c) ∩ U(S) = ∅`, `hS'`, `U(S') = U(S) ∖ {c}` | `cs1_` | 150 | 1 | low |
| U-CS2 | daughters from `smoothingSuccessor_insert_child_data`; mark partition; crossing partition, `m_A = m₁+m₂+1` | `cs2_` | 400 | 3 | medium |
| U-CS3 | blocks of `S'` = blocks of `S` ∖ `{c}`; owner assignment to one daughter; `blockPoly` transfer; singleton block `P = 1`; product identity | `cs3_` | 600 | 4-5 | medium-high |
| U-CS4 | corner correspondence, turn patterns, `CarrierUniformOrOneDissent Λᵢ` | `cs4_` | 350 | 2-3 | medium |
| U-CS5 | inherited principal turns invariant, new turns opposite, `|r_A| = |r₁|+|r₂|` via `uniform_rotation` | `cs5_` | 500 | 3-4 | HIGH |
| U-CS6 | `cs_split` assembly (statement fixed in the sketch) | `cs_` | 100 | 1 | low |
| Row 103 total | | | ≈ 2.1k | 14-17 | |
| U-CV | port `corner_values_embedded` (done), (ii) one-liner, bundle | `cv_` | 80 | 0.5 | low |
| U-S7-0 | reductions: one parameter per side, contact sign, selector form, `VertexSidesData` unpacking | `s70_` | 400 | 3 | low |
| U-S7-1 | half-support transport `Ind`-bijections, residual graphs, owners (sliding + eligible rows) | `s71_` | 1500 | 8-10 | HIGH |
| U-S7-2 | half-carrier geometry: carriers of `Tᵢ` on `λᵢ` vs boundary successors on `P_∓`; corner polygons, rotations, records | `s72_` | 2000 | 10-14 | HIGH |
| U-S7-3 | sliding branch: relocation `φ`, equal rotations, selector table, distributivity | `s73_` | 1200 | 6-8 | medium |
| U-S7-4 | bigon two-newborn sector, contact triangle (`corner_values_embedded`), `B = (1−ε)J` | `s74_` | 800 | 4-6 | medium |
| U-S7-5 | coambient diagram: smoothing at `q`, R-II identification with `D_L`, components = half lifts, `ℓ`, writhes, curl deletion | `s75_` | 2000 | 12-16 | HIGH |
| U-S7-6 | universal skein, two-component row, slots, FLOORS (both `ε` branches) | `s76_` | 900 | 5-7 | medium |
| U-S7-7 | one-newborn rows (SINGLETON), different-block alternative | `s77_` | 700 | 4-5 | medium |
| U-S7-8 | assembly `s7_sliding`, `s7_bigon`, `thm_C_S7_of` | `s7_` | 400 | 3 | low |
| Row 110 total | | | ≈ 10k (8-14k) | 55-75 | the largest row of the document |
| U-SO-0 | reductions, `ε₁` from soft-generic's `δ`, chamber constancy | `so0_` | 200 | 1-2 | low |
| U-SO-1 | vertex-insertion mark transport (supports, carriers, corner marks, turns, `m_Q`) for same-sign/mixed | `so1_` | 1200 | 6-8 | HIGH |
| U-SO-2 | rotation equality by convergence + integrality | `so2_` | 500 | 3-4 | medium |
| U-SO-3 | equal `H⁺` of corresponding positive lifts (record bridge or planar family) | `so3_` | 600 | 3-4 | medium |
| U-SO-4 | mixed sector (`cornerStateSum_eq_zero_of_consecutive_opposite` from CS5B) | `so4_` | 200 | 1-2 | low |
| U-SO-5 | loop sector: isolated `y` (CORNER-VALUES (ii)), triangle (CORNER-VALUES (i)), residual transport, left-turn count, assembly | `so5_` | 1200 | 6-8 | HIGH |
| Row 112 total | | | ≈ 3.9k | 20-28 | |

Grand total ≈ 16k lines (13-20k), 90-120 agent-hours; critical path = row 110 (U-S7-1/2/5 in parallel, then 3-7).
Order: 103 (U-CS1..6 parallel on one skeleton) → 105 (trivial) → 112 and 110 in parallel lanes; 112 needs only
`CornerValuesData` and can start as soon as its skeleton is frozen (its leaves take `hcv` as a parameter).

## 6. Riskiest steps

1. Row 110's sheer size (the printed proof is ~630 TeX lines vs ~80 for thm:C-S3, which took 2.5k Lean lines) and
   its two NEW transport lanes: half supports/carriers of `λᵢ` vs `P_∓` (U-S7-1/2, no accepted analogue — FlatCarriers
   is the only precedent) and the actual-diagram surgery of U-S7-5 (smoothing at `q`, R-II template, component
   identification, linking number) on the Link layer. Fallback: none cheaper; the printed proof has no shortcut.
2. Row 103, U-CS5: `|r_A| = |r₁| + |r₂|` needs "inherited corners keep their principal turn under refinement" — true
   (the corner edges are positive multiples of fixed original edges) but not an accepted lemma; and principal-angle
   antisymmetry of the two smoothing corners.
3. Row 103, U-CS3: identifying `CV.Piece (insert c S)` with `CV.Piece S ∖ {c}` (Mathlib connected components of two
   induced subgraphs) and routing each block to one daughter.
4. Row 112, U-SO-1/5: a mark transport with DIFFERENT mark sets (one extra vertex; in the loop sector two extra
   visits) — the accepted `MarkTransport` does not apply; the residual-cycle correspondence after "processing `y`".
5. Interface drift with the floor lane (§0): only the one-dissent alternative and `mindegAZ` on the full polynomial
   are load-bearing; any renaming is a mechanical fix in `cb_singleton_of_floor` and U-S7-6.
6. Fidelity calls a reviewer may contest: FR-CV-1 (`m_Q = 0` for "embedded (`m_Q = 0`)"), FR-S7-4 (the two
   `…HalfStateSum` wrappers), FR-CS-3 (`ℚ` identity via `softAmplitudeMultiplier`); each has a disclosed
   alternative and a ≤ 5-line statement change.
