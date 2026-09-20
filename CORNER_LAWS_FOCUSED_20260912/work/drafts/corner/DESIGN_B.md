# DESIGN_B — the corner chain after thm:floor: rows 103 cb:singleton, 105 lem:corner-values, 110 thm:C-S7, 112 thm:C-soft

Architect B, 2026-09-15 (~15:30Z / 11:30am ET). Emphasis: PROOF FEASIBILITY. Companion sketch
`work/drafts/corner/Sketch_B.lean` (568 lines, `lake env lean` 0 errors, 11 `sorry` = the frozen leaves of §5;
the four row-level assemblies `cb_singleton_of_floor`, `corner_values_of_singleton`, `thm_C_S7_of_floor`,
`thm_C_soft_of_cornerValues` are PROVED from the leaves, so the composition — and exactly where `a_floor`
enters — is fixed now). Sources: sm-3-statesum.tex:4697-4759 (103), 4801-4820 (105); sm-4-knotlaws.tex:267-908
(110), 984-1147 (112). Row 100's interface is ASSUMED in the shape of Gap2Statements.lean §8
(`FloorTheoremData`: `a_floor`, `z_parity`), copied verbatim into Sketch_B §0 — TO BE UNIFIED WITH THE FLOOR LANE.

## 0. Verdict in one table

| row | statement | floor needed? | new proof matter | est. lines | est. hours (unit work) | feasibility |
|---|---|---|---|---|---|---|
| 103 cb:singleton | `CbSingletonData` (1 field) | yes — `a_floor` twice (both daughters) | daughter split of one carrier at an isolated crossing + block bijection under `insert`; turn ledger | 2,300-2,800 | 30-38 | good: the split infrastructure exists (Carrier insert lane) |
| 105 lem:corner-values | `CornerValuesData` (2 fields) | (i) NO; (ii) only via 103 | (i) `m_Q = 0 ⇒ Embedded (ccpCornerPolygon)` bridge | 550-850 | 8-11 | good; (i) provable NOW |
| 110 thm:C-S7 | `CS7Data` (1 field), target `SM.thm_C_S7` | yes — `a_floor` at the two half contact carriers (bigon branch only) + row 103 | contact-wall carrier transport, half bijections, skein/R-II/R-I on actual lifts, homflyrows row, rotation ledger | 11,000-15,000 | 140-190 (critical path ~90) | HARD — the largest remaining item of the project |
| 112 thm:C-soft | `CSoftData` (1 field), target `SM.thm_C_soft` | only via 105 (ii), loop sector | soft mark transport, one-vertex insertion deformation of positive lifts, isolated newborn | 4,500-6,000 | 60-80 | medium; two of three sectors floor-free |

Total ≈ 18,500-24,500 lines (mid estimate 21,000). Dependency order: 103 → 105 → 112; 110 needs 103 and the floor
directly. 110 and 112 are independent of each other; 110's sliding branch (~4k lines) and 112's same-sign/mixed
sectors (~2.5k lines) need no floor at all and can start today.

## 1. Fidelity risks recorded BEFORE stating (FR-CC-*)

FR-CC-1 (103) "self-crossing labels of A" = `carrierCrossings hn hP S A` (def:smoothing, SM/CarrierCrossings.lean:56;
lem:carriers (iii) identifies them with the self-intersections); "interlaces no other self-crossing of A" =
`∀ c' ∈ carrierCrossings … A, c' ≠ c → ¬ Interlaces hn hP c c'` (def:interlace, SM/Interlacement.lean:16). Blocks,
`U(S)`, owners appear only in the PROOF.
FR-CC-2 (103) Binder as def:C / cb:blocks: `hn : 3 ≤ n`, `[NeZero n]`, `hP : Generic P`, `hS : IsDecomposition hn hP S`;
"uniform carrier" = `CarrierUniform` (def:uniform); `c(A) = cornerCoefficient hn hP S A hS`.
FR-CC-3 (103, proof route, not a reading) the printed proof argues on the `[z⁰]` rows (`f_A = g₁g₂`, case `f_A = 0`);
the Lean route argues on the full polynomials, nonzero by lp:core (`lp_core.ne_zero`), with `mindegAZ_mul`
(LinkLaurentRing.lean:757). Same conclusion; `z_parity` and the knot support are not needed.
FR-CC-4 (105 (i)) "uniform and embedded (m_Q = 0)": the hypothesis is `carrierCrossingCount hn hP S q = 0` (the printed
parenthetical DEFINES embedded); `Embedded (ccpCornerPolygon …)` (cb:embedded-rotation's class,
EmbeddedRotation.lean:33) is DERIVED in the proof from lem:carriers (iii). Uniformity is kept as a hypothesis though
the proof does not use it. Conclusions: `|carrierRotationInt| = 1` (def:C's integer) AND `|carrierRotation| = 1`
(the accepted real), `cornerSlot = 0`, `cornerCoefficient = 1`.
FR-CC-5 (105 (ii)) literally the clause of 103 with `(Q, y)` for `(A, c)`; "crossing of Q" = `carrierCrossings`.
FR-CC-6 (110) `P₊, P₋` read at every pair of side parameters `tp tm` (the accepted convention of prop:C-silent,
hyp:R, cor:A-lawful `vertex_edge_law`; equivalent to chamber values by prop:C-chamber); `s = g.contactSign M a` =
`χ_{a,a+1,M}` on the negative side, constant there (`contactSign_eq_at`, `vertex_contact_signs`,
NamedWallSides.lean:58-69); halves = `firstHalf/secondHalf g.center M a` (def:deletion-halves, accepted); their
genericity (lem:children (ii), `vertex_halves_children`) is a presupposition of `C(λᵢ)`, quantified as `∀ h₁ h₂`
(proof-irrelevant; the consumer thm:uniqueness (c) has the same binders); "of bigon or sliding type" is the
exhaustive dichotomy `vertexEdge_bigon_or_sliding` (NamedWallPredicates.lean:46) — not a hypothesis; the half
sizes carry `NeZero` instances (ContactHalfIndices.lean:11-14) and `3 ≤ size` from `contactHalfSizes_bounds`.
FR-CC-7 (112) the multiplier `(χ₋+χ₊)/2` is `softAmplitudeMultiplier P j q : ℚ` (SM.SoftDuplication,
SoftAmplitudeSectors.lean:96, def:soft's `softAttachmentMinus/Plus`; the shape of cor:A-lawful `soft_theorem` and
thm:uniqueness (e)); the ℤ-valued `C` is cast to ℚ; "for all sufficiently small ε > 0" = `∃ ε₁ > 0, ∀ ε ∈ (0, ε₁)`;
`P_ε` generic (lem:soft-generic (i)) is quantified `∀ hQ` (A-lawful uses `∃ hQ`; equivalent given lem:soft-generic,
and `∀` is the consumer's shape). `hn : 3 ≤ n` on the parent; the child's `3 ≤ n+1` is `by omega`.
FR-CC-8 (110/112) `C` is evaluated on labelled tuples; thm:comparison consumes it on the quotient `GenericPolygon`
through the accepted `cornerStateSum_genericShift` (CChamber.lean:1362) — the consumer's business.
FR-CC-9 (interface) only `FloorTheoremData.a_floor` is consumed (rows 103, 110), at carriers of decompositions with
`CarrierUniformOrOneDissent` (Gap2Statements §8 / Sketch_B §0). If the floor lane states the bound on `SM.P`
instead of `homfly`, or with `mindegA : WithTop ℤ`, the `_of_floor` theorems need a 5-line adapter
(`P_eq_homfly`, `mindegA_eq_mindegAZ`). `z_parity` is redundant with `lp_core.knot_support` for this lane.
FR-CC-10 (110, proof) the printed R-II deletion ("the actual ordinary R-II template") and R-I curl deletion are
consumed through `lp_core.reidemeister_II/I` and need `RII`/`RI` WITNESSES (LinkMoves.lean:590 `RIData`) on the
actual polygonal positive lifts — genuinely new constructions, the riskiest step of the chain (§5, U110-G).

## 2. The statements (Sketch_B.lean; all typecheck against the accepted modules)

Row 103 — `structure CbSingletonData : Prop` with `isolated_zero : ∀ n [NeZero n] hn P hP S hS (A : Component hn hP S),
CarrierUniform hn hP S A → ∀ c ∈ carrierCrossings hn hP S A, (∀ c' ∈ carrierCrossings hn hP S A, c' ≠ c →
¬ Interlaces hn hP c c') → cornerCoefficient hn hP S A hS = 0`.

Row 105 — `structure CornerValuesData : Prop` with `embedded_value : … CarrierUniform … → carrierCrossingCount … = 0 →
|carrierRotationInt …| = 1 ∧ |carrierRotation …| = 1 ∧ cornerSlot … = 0 ∧ cornerCoefficient … = 1` and
`isolated_zero` (= 103's clause on `(q, y)`).

Row 110 — `structure CS7Data : Prop` with `vertex_edge_law : ∀ n [NeZero n] hn (g : WallGerm n) (M a) (h : g.VertexEdgeAt M a)
(h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)), ∀ tp tm : g.SideParameter,
cornerStateSum hn (g.sideTuple true tp).property − cornerStateSum hn (g.sideTuple false tm).property =
(g.contactSign M a : ℤ) * (cornerStateSum (contactHalfSizes_bounds hn h.1).1.1 h₁ * cornerStateSum (…).2.1 h₂)`.
Row theorem (fixed name): `theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor` once row 100 lands.

Row 112 — `structure CSoftData : Prop` with `soft_theorem : ∀ n [NeZero n] hn P hP (j : ZMod n) (q : Plane),
SoftAdmissible P j q → ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
(cornerStateSum (by omega) hQ : ℚ) = softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ)`.
Row theorem (fixed name): `theorem thm_C_soft : CSoftData := thm_C_soft_of_floor thm_floor`.

Consumer check: `UniquenessHypotheses.vertex_edge` / `.soft` (SM/Uniqueness.lean:57-76) are literally these
shapes with `F n Q` for `C`; `A_lawful.vertex_edge_law` / `soft_theorem` (SM/ALawful.lean:102, ~140) are the
accepted A-side twins. No adapter beyond FR-CC-8.

## 3. Proof routes, accepted lemmas by file:line, and exactly where the floor enters

### 3.1 Row 103 (printed sm-3:4703-4759)

1. `{c}` is a singleton block: `c ∈ U(S)` — `c ∉ S` (`carrierCrossings_subset_compl`, CarrierCrossings.lean:95) and
   `c ∉ N(S)` (both visits on `A`, contrapositive of `neighbor_visits_separated`, CarriersLemma.lean:~95); an
   undominated `x` interlacing `c` has both visits on ONE carrier (`nonneighbor_visits_together`) which must be `A`
   by lem:carriers (iv) `noncrossing` (CarriersLemma.lean:~104; needs `Interlaces` ⇒ alternating visits,
   Interlacement.lean:16 unfolds to `crossingVisitBetween`), so `x ∈ carrierCrossings A` — excluded by the
   hypothesis. Then `insert c S` is a decomposition (`greedy_independent` = `insert_unselected_mem_independentSupports`,
   CarrierCrossings.lean:399) and `U(insert c S) = U(S) ∖ {c}` (`greedy_step`, CBProducts.lean:~1907). [leaf U103-A]
2. Daughters: `smoothingSuccessor_insert_child_data` (CarrierInsertOrbits.lean:49) gives the two cycles
   `inr v :: BL`, `inr (twin v) :: AL` and the ownership iff; `component_card_insert` (CarrierComponentCount.lean:58);
   spectators unchanged: `owner_insert_iff_of_unaffected` (:99), `componentCycle_insert_unaffected` (:121),
   `smoothingSuccessor_insert_other` (CarrierSingleSwitch.lean:96). [U103-D]
3. `P_A = P_{Λ₁}P_{Λ₂}`, `m_A = m₁ + m₂ + 1` (eq. cb:singleton-products): cb:products (CBBlocks.lean `CbProductsData`:
   `product`, `count`, `one_owner`, `owned_by`, `polynomial_independent`, `block_diagram`) at `S` for `A` and at
   `S' = insert c S` for `Λ₁, Λ₂`. New: (a) `Piece S' ≃ {H : Piece S // pieceLabels H ≠ {c}}` preserving labels — `c`
   is isolated in `G_P[U(S)]`, so the components of the induced graph on `U(S)∖{c}` are the other components
   (Mathlib `SimpleGraph.ConnectedComponent`, `induce`, `Reachable` transfer) [U103-B]; (b) `blockPoly S H = blockPoly
   S' H'` when the labels agree: a block carrier diagram of `H'` (`exists_blockCarrier`, CBProducts.lean:1740, over a
   refinement `T ⊇ S' ⊇ S`) is one of `H` (`IsBlockCarrierDiagram`, CBBlocks.lean), and `polynomial_independent` on
   both sides pins `SM.P D` — no record isomorphism needed; `blockPoly S {c} = 1`: its block carrier diagram has one
   crossing (`carrierCrossingEquiv`, LinkPositiveLift.lean:799) so `single_crossing.one_crossing`
   (SingleCrossing.lean:165) [U103-C]; (c) blocks owned by `A` other than `{c}` split between `Λ₁, Λ₂`
   (`one_owner` at `S'` + `owner_insert_eq_imp`, CarrierOrbitRefinement.lean:80), blocks of other carriers stay
   (`owner_insert_iff_of_unaffected`) [U103-D]. `cornerHomfly = carrierPoly` by `equals_Hplus` / `P_eq_homfly`
   (PolynomialBlock.lean:667).
4. Turn ledger (eq. cb:singleton-rotations): a real-valued `markPrincipalTurn` extending CX1's `markTurn`
   (CX1.lean:~45) with `principalTurn (ccpCornerPolygon …) j = markPrincipalTurn (ccpCornerMark … j)` (from
   `ccpCornerPolygon_turn_eq_sign`'s in/out-edge lemmas, CarrierCornerPolygon.lean:598-620) gives
   `carrierRotation = (1/2π) Σ_{true corners owned} markPrincipalTurn`; the corner sets of `Λ₁ ⊔ Λ₂` = corners of `A`
   ⊔ `{inr v, inr (twin v)}` whose two new angles cancel (`crossingSign_swap`, principal angle antisymmetry);
   old turns unchanged (`ccpCornerPolygon_turn_vertex/_smoothing` at `S'`); one daughter uniform of sign `τ`, the
   other one-dissent; `uniform_rotation` (UniformRotation.lean:63; clauses (i)/(ii)/(iv)) puts all three rotations
   on `τ`'s ray; `carrierRotationInt_cast` (CornerStateSum.lean:~66) transfers to ℤ. [U103-E]
5. Assembly (PROVED in Sketch_B, `cb_singleton_of_floor`): **`a_floor` at `Λ₁` and at `Λ₂`** (the uniform and the
   one-dissent daughter — the printed "Theorem thm:floor applies to the actual uniform and one-dissent daughters");
   `mindegAZ H_A = mindegAZ H₁ + mindegAZ H₂ ≥ d₁ + d₂ = d_A + 2` (`sg_slot_identity`, `mindegAZ_mul`,
   `cornerHomfly_ne_zero`), so `coeffAt d_A 0 H_A = 0` (`mindegAZ_spec`, LinkLaurentRing.lean:513). This is the
   ONLY floor consumption of row 103.

### 3.2 Row 105 (printed sm-3:4809-4820)

(i) NO floor. `cvl_embedded_of_no_crossings` [U105-A]: from `self_intersections` (CarriersLemma.lean:~83: no
self-intersection when `carrierCrossings = ∅`) and `corner_polygons` (traced curve = ⋃ edge segments of the corner
polygon) derive the three `Embedded` clauses (nonzero edges = `ccpCornerPolygon_edge_ne_zero`; remote edge segments
disjoint and consecutive ones meeting only at the vertex — two distinct corner-polygon edges are traced at distinct
carrier parameters, `IsCarrierParameter`/`carrierTrace`, CarrierSelfIntersections.lean:403-417). Then
`cb_embedded_rotation` (EmbeddedRotation.lean:1081; needs `3 ≤ ccpCornerCount` = `carriers_clause_ii …2.2.1` and
`ccpCornerPolygon_regular` :679) gives `rot = ±1`; `carrierRotationInt_cast`; `cornerSlot = 1 − 0 − 1 = 0`; the lift
is a crossing-free circle (`positiveLift_isCrossingFreeCircle`, LinkPositiveLift.lean:833), `P_circle`
(PolynomialBlock.lean:609), `P_eq_homfly`, `coeffAt_one` (LinkLaurentRing.lean:306). PROVED in Sketch_B
(`corner_values_i`) modulo the one leaf. Exposed unconditionally: thm:comparison (f) consumes exactly it.
(ii) = row 103 (`corner_values_of_singleton`, proved).

### 3.3 Row 110 (printed sm-4:277-908) — reduction, then two branches

Reduction (PROVED, `thm_C_S7_of_floor`): `vertexEdge_bigon_or_sliding`; both side parameters moved below the
branch radius by `cornerStateSum_side_eq` (HypR.lean, = chamber constancy along a side, prop:C-chamber).

Sliding branch (sm-4:300-406) — NO floor. Objects: the relocated crossing `x₋ ↦ x₊` (`VertexCrossingData`,
ContactCrossingSides.lean:12: `X(P₊) ∆ X(P₋) = {{a,M−1},{a,M}}`, `SlidingCrossingPattern`; persistent visits and their
order: `VertexLocalData.visit_order`, `contactVisitTransport`, VertexSides.lean:16-28). Steps: (1) supports avoiding
`x₋` cancel term by term — a `MarkTransport`-like partial transport `P₋ ↔ P₊` on persistent crossings (the CSilent
`sideTransport` pattern, CSilent.lean:1668, with the contact crossing removed), corner polygons regular through the
wall, rotation constant (`lem:rot (ii)` as in CChamber `cornerCoefficient_path`), homfly equal
(`cornerCoefficient_transport`, CChamber.lean:481, via `presentations` on the record bridge `positiveLiftRecordIso`,
CBProducts.lean:946, or a `Deform` as in CS3 §E); (2) supports containing `x₋`: the bijection eq. s7c:sliding-bijection
with `Ind(λ₁) × Ind(λ₂)` (`HalvesData.first/second_interior_inclusions`, `cut_segments`, DeletionHalvesDefinition.lean),
carriers of `S` ↔ carriers of `S₁ ⊔ S₂` with equal coefficient products (the only changed direction lists
eq. s7c:short-direction-lists; equal signed rotations by angle addition eq. s7c:turn-short-a/b — no wrap since both
tangents lie in one open half-plane of `r`); (3) selector algebra eq. s7c:short-selector →
eq. s7c:sliding-selector-difference `W₊ − W₋ = s W₁ W₂` (on `carrierWeight`, CX1.lean); (4) sum via `stateTerm`
(CS3.lean:2360-2380, lem:C-X1 as a sum over all supports) and `Finset.sum_bij`. Leaf `s7_sliding_law_at`.

Bigon branch (sm-4:407-874). (1) `B = (1−ε)J`: ineligible `T` (meeting `N`) — both newborns dominated, terms cancel by
the partial transport `P₀ ↔ P₂`; eligible `T`: bijection eq. s7c:eligible-bijection; for `ε = 0` the support
`T ∪ {x,y}` smooths to the contact triangle (three corners of sign `−s₀`, embedded: value `1`, `R = 1`, `w = 0` —
the `corner_values_i` route) plus the successors of `T₁, T₂`. (2) Universal skein extraction on the newborn-free high
row: `lp_core.skein` (PolynomialBlock.lean:1117) at `q = x` with `IsSkeinTriple` (LinkMoves.lean:751:
`Dm = Dp.switch x`, `IsOrientedSmoothing`); `D_H.switch x ≃ D_L` after an R-II deletion of the bigon `{x, y}`:
`lp_core.reidemeister_II` with an `RII` witness on the actual lifts (FR-CC-10), then `presentations`
(PolynomialBlock.lean:1177); the smoothing `D_A` is a two-component diagram whose `knotRestrict`s
(MarkedProducts.lean:126) have the records of the half contact carriers `L₁, L₂` (for `ε = 0` after an `RI`
deletion of the curl `y`); algebra `s7_universal_extraction` (leaf, ~50 lines: coefficient shifts of `R.aInv`, `R.z`
— no shift lemmas exist yet in LinkLaurentRing). (3) `homflyrows.two_component_row` (MarkedProducts.lean:363-380)
with `twoLinking D_A 0 1 = 2ℓ` = mixed sign sum over `M_T ∪ ({y} if ε=1)`; writhe counts eq. s7c:interlacing-writhe-row /
s7c:noninterlacing-writhe from `positiveLift_writhe_eq_carrierCrossingCount` + the crossing partition. (4) Rotation
ledger eq. s7c:full-rotation (the newborn-free contact carrier is a regular family through the wall: lem:rot (ii)),
eq. s7c:rotation-ledger (explicit contact turns `β`, `π−α`, `β−α∓π`: TurnLift/principalAngle library), same-sign
uniformity ⇒ `R_L = R₁ + R₂` (ε=1) or `R₁ + R₂ − R_L = −1` (ε=0) via `uniform_rotation`. (5) **Floor consumption**:
interlacing branch — `a_floor` at the two UNIFORM half contact carriers `L₁, L₂` read as carriers of the decompositions
`T_i` of `λ_i` (the printed hypothesis discharge sm-4:800-835: `L_i` is the boundary successor of `T_i` closed at the
cut; needs the half↔interval carrier correspondence of (1)), then `s7_corner_product` (`[a^{K−2}](f₁f₂) = 0`,
`[a^K](f₁f₂) = ω₁ω₂`; the second conjunct uses nonnegative `z`-support = `lp_core.knot_support`, not `z_parity`);
noninterlacing branch — `a_floor` at the two ONE-DISSENT half contact carriers: both reads `K−4, K−2` lie below the
floor `K` (`coeffAt_mul_eq_zero_of_lt_floor`, PROVED in Sketch_B §1); the one-newborn rows vanish by **row 103**
(`cb_singleton_of_floor`) at the isolated newborn; the different-block alternative by the same two facts. (6) Sum the
sectors: `s7c:bigon-total`. Leaf `s7_bigon_law_at`.

Genuinely new for 110 (not in any accepted module): the contact-wall partial mark transport and the half↔interval
carrier correspondence including the contact carriers at the nongeneric centre; the `RII`/`RI` witnesses on
polygonal lifts and the identification of `switch`/oriented smoothing with the half lifts; the two-component
bookkeeping (`knotRestrict`, `twoLinking`) on actual lifts; the contact rotation ledger. Reusable: CS3 §A
(one-component `Deform`/`Reparam`, CS3.lean:41-1300), CChamber `MarkTransport` + `cornerStateSum_transport`
(CChamber.lean:122, 503), CSilent's family machinery, CV/ChamberInvII `pieceEquiv`/`homfly_geoPositiveLift_eq_of_mem_chamber`
(:305, :261) for spectator blocks, the CB record bridge (KL1) for `RecordIso`s between lifts.

### 3.4 Row 112 (printed sm-4:989-1147) — three sectors, assembly PROVED (`thm_C_soft_of_cornerValues`)

Sector dichotomy (proved in Sketch_B): `χ₋, χ₊ ≠ 0` (admissibility), `τ = turn P j ≠ 0` (`sft_turn_ne_zero`, (G1)), so
`(χ₋,χ₊) = (−τ,−τ)`, `χ₋ ≠ χ₊`, or `(τ,τ)`; multipliers `−τ, 0, τ` = `softAmplitudeMultiplier`.
Same-sign (sm-4:1024-1057), NO floor: `soft_family_generic` (SoftGenericLemma.lean:52) (iv) gives the same Gauss word
(`gaussWord.map softInheritedCrossing = gaussWord hQ`), (ii) the turns (`τ` at `M` becomes `τ, τ` at `M, M_ε`),
(iii) inherited visits with order and determinant signs; a "soft mark transport" `Mark P ↪ Mark P_ε` (vertex
`softOldIndex`, visits `softInheritedVisit`, mark list = parent list with `inl (softNewIndex j)` inserted) with
`smoothingSuccessor` related by contracting the new vertex ⇒ `Component ≃`, owners, corner marks (the carrier
through `M` gains one corner), `UniformDecomposition ↔`; rotation equality: principal-angle addition
`∠(u,q) + ∠(q, v−εq) → ∠(u,v)` (q strictly inside the turn wedge) + integrality (`rotationNumber_integer`) for small
`ε`, or directly by angle addition; coefficient equality: the child corner polygon = parent corner polygon with one
vertex inserted near `M` — CS3's flat subdivision `Reparam` (`reparam_positiveDiagram_single_appendVertex`,
CS3.lean:1166) at the foot on `E_j` followed by a `Deform` of the one-component shadow moving the flat vertex to
`M_ε` with constant crossing set (`homfly_positiveDiagram_single_of_family`, CS3.lean:592), then
`cornerCoefficient_transport`-style assembly; `ℓ(P_ε) = ℓ(P) + [τ=1]`; `C(P_ε) = −τ C(P)`. Leaf `sft_same_sign`.
Mixed (sm-4:1059-1065), NO floor: the soft edge has no crossing (clause (i): its segment meets others only at its
endpoints), so `M, M_ε` are consecutive corners of one carrier with turns `−χ₋ ≠ −χ₊` — the thm:C-S5 argument verbatim
(`markSuccessor_vertex_of_no_crossing`, CS5.lean:30; `ccpCornerPolygon_turn_vertex`): no uniform decomposition,
`C(P_ε) = 0`. Leaf `sft_mixed` (~200 lines).
Loop (sm-4:1067-1143), floor via 105 (ii): newborn `y` with adjacent visits (`nextGaussVisit … = softNewbornReturnVisit`,
the `traversalBetween` clauses) ⇒ `y` interlaces no crossing; `Ind(P_ε) = {S} ⊔ {S ∪ {y}}`; supports omitting `y`:
the carrier `Q'` through `y` has `y` isolated among its self-crossings ⇒ **`corner_values.isolated_zero`** (⇐ 103 ⇐
`a_floor`) kills the term when uniform; `S ∪ {y}`: smooth `y` first (`smoothingSuccessor_insert_child_data` at `y`)
— the triangle cycle `(b, M, M_ε)` is embedded with three turns `−τ`: `corner_values_i` (value `1`), and the
residual cycle ≅ `P`'s traversal with corner `M` replaced by the smoothing corner `y` of sign `τ` (clause (ii)
`sgn det(u, D_ε) = τ`): the same transport/deformation as the same-sign sector; sign bookkeeping
`ℓ(P_ε) − ℓ(P) = −[τ=1] + 2[τ=−1]` plus one extra selected crossing and one factor `1` ⇒ `C(P_ε) = τ C(P)`. Leaf `sft_loop`.

## 4. Conditional forms (D-F11/D-F14 pattern; library material, never mapped)

* `cb_singleton_of_floor : FloorTheoremData → CbSingletonData` — PROVED from leaves (Sketch_B §2).
* `corner_values_i` — UNCONDITIONAL (row 105 (i); one leaf U105-A); `corner_values_of_singleton : CbSingletonData →
  CornerValuesData` — PROVED; `corner_values_of_floor := corner_values_of_singleton ∘ cb_singleton_of_floor`.
* `thm_C_S7_of_floor : FloorTheoremData → CS7Data` — PROVED from `s7_sliding_law_at` (floor-free) and
  `s7_bigon_law_at hF`. The sliding branch can be ported as an unconditional library theorem on its own.
* `thm_C_soft_of_cornerValues : CornerValuesData → CSoftData` — PROVED from the three sector leaves;
  `thm_C_soft_of_floor := thm_C_soft_of_cornerValues ∘ corner_values_of_floor`. Sectors same-sign and mixed are
  unconditional library theorems.
* Row theorems, assembled once row 100 (`SM.thm_floor : FloorTheoremData`, or its unified form) is accepted:
  `SM.cb_singleton := cb_singleton_of_floor thm_floor`, `SM.corner_values := corner_values_of_floor thm_floor`,
  `SM.thm_C_S7 := thm_C_S7_of_floor thm_floor`, `SM.thm_C_soft := thm_C_soft_of_floor thm_floor`.

## 5. Unit decomposition (byte-identical skeleton copies of Sketch_B; leaves frozen; helper prefixes fixed)

Prefixes: `sg_` (103), `cvl_` (105), `s7_` (110), `sft_` (112). Each unit works on a copy of the skeleton, proves only
its leaves, adds helpers with its prefix, never edits a statement. Lines = new Lean lines; hours = one prover lane.

Row 103 (leaves `sg_isolated_undominated`, `sg_daughters_products`, `sg_daughters_rotation`):
* U103-A isolated ⇒ undominated & `U(S') = U(S)∖{c}` — 300 lines, 4 h (Interlaces ⇒ alternating visits + noncrossing).
* U103-B `Piece S' ≃ {H : Piece S // labels ≠ {c}}` label-preserving — 450 lines, 6 h (Mathlib ConnectedComponent/induce).
* U103-C `sg_blockPoly_eq_of_labels_eq`, `sg_blockPoly_singleton = 1` — 250 lines, 3 h.
* U103-D daughters, block redistribution, `P_A = P₁P₂`, `m_A = m₁+m₂+1` (proves `sg_daughters_products` from A-C) — 650
  lines, 9 h (critical path).
* U103-E `markPrincipalTurn`, rotation as a mark sum, `sg_daughters_rotation` — 700 lines, 9 h (critical path, parallel to D).
* U103-F assembly = Sketch_B (done) + port/review — 0 new lines, 1 h.
Row 105: U105-A `cvl_embedded_of_no_crossings` — 500 lines, 7 h (RISK: bookkeeping `carrierTrace` runs ↔ corner-polygon
edges); U105-B/C assembly = Sketch_B (done).
Row 110 (leaves `s7_sliding_law_at`, `s7_bigon_law_at`, `s7_universal_extraction`, `s7_corner_product`):
* U110-A contact-wall partial mark transport (`VertexLocalData` → transport on persistent crossings, corner turns,
  rotations, homfly of lifts) — 1,500 lines, 20 h (critical path).
* U110-B halves ↔ intervals: support bijections (sliding, eligible), carrier correspondences, the contact carriers
  `L*`, `L₁`, `L₂` as carriers of decompositions of `λᵢ` (floor-domain discharge) — 2,000 lines, 25 h (critical path).
* U110-C selector algebra (`carrierWeight` tables s7c:short-selector, interlacing/noninterlacing selectors, triangle
  weight) — 600 lines, 7 h (independent).
* U110-D coefficient transport for spectators and relocated carriers (RecordIso via the CB record bridge, or Deform)
  — 1,500 lines, 20 h.
* U110-E sliding assembly `s7_sliding_law_at` — 500 lines, 6 h.
* U110-F bigon two-newborn sector and ineligible cancellation (`B = (1−ε)J`) — 1,200 lines, 15 h.
* U110-G skein extraction: `IsSkeinTriple` at `q`, `RII` witness (bigon `{x,y}`), `RI` witness (curl `y`), record
  identifications of `switch`/smoothing with `D_L`/`D_A`, `s7_universal_extraction` — 2,500 lines, 35 h (RISKIEST).
* U110-H two-component row: `knotRestrict`, `twoLinking = 2ℓ`, writhe counts — 600 lines, 8 h.
* U110-I contact rotation ledger (s7c:full-rotation, s7c:rotation-ledger, same-sign ⇒ `R`-identities) — 900 lines, 12 h.
* U110-J floor leaves: interlacing `Ω_H − Ω_L = −ω₁ω₂` (`s7_corner_product` 2nd conjunct ~80 lines), noninterlacing rows
  zero, one-newborn rows via `cb_singleton_of_floor`, different-block rows — 700 lines, 9 h.
* U110-K bigon assembly `s7_bigon_law_at` + reduction (Sketch_B) — 500 lines, 6 h.
Row 112 (leaves `sft_same_sign`, `sft_mixed`, `sft_loop`):
* U112-A soft mark transport and `Component ≃` for common supports — 900 lines, 12 h (critical path).
* U112-B `sft_mixed` — 200 lines, 3 h (independent, CS5 pattern).
* U112-C same-sign: uniformity ↔, rotation equality, coefficient equality (CS3 §A Reparam + Deform), `ℓ` count — 1,800
  lines, 24 h.
* U112-D loop: isolated newborn, `Ind(P_ε)`, the triangle (`corner_values_i`), residual transport, sign bookkeeping —
  2,200 lines, 28 h.
* U112-E assembly = Sketch_B (done).

Scheduling: start now (floor-free): U103-A..E, U105-A, U110-A/B/C, U112-A/B/C. Row 103 accepted-conditional in ~1 day
(6 parallel lanes); 105 with it; 112 in ~2-3 days; 110 in ~5-8 days of 6-8 parallel lanes. Apply the reassessment
rule per unit (2 attempts / 60 min), not per row: 110's units are individually auditable.

## 6. Riskiest steps (ranked) and fallbacks

1. U110-G (R-II/R-I witnesses on actual polygonal lifts; identification of `D_H.switch x` with `D_L` and of the smoothing
   with the half lifts): inspect `RIData`/`RIIData` (LinkMoves.lean:590) first; fallback: prove the skein-triple identities
   through `presentations` after constructing the reduced diagrams directly as positive lifts of carriers of enlarged
   supports (the printed "the daughters of a singleton row are the carriers of the support enlarged by the singleton").
2. U110-A/B (carriers through the contact at a nongeneric centre; `L_i` as carriers of `T_i` on `λ_i`): the floor's
   domain must be met literally (`Component hn' hλ T_i` for `λ_i`); build the half transport on marks, not on plane curves.
3. U105-A `Embedded` bridge: parametrisation bookkeeping; fallback: prove `pm_one` directly for the corner polygon
   through the traced-curve version of embeddedness if `cb_embedded_rotation`'s class resists (it is stated on
   `LabelledTuple`, so the bridge is the honest route).
4. U112-C/D coefficient equality by deformation: the family must stay a generic one-component shadow (constant
   crossing set) — guaranteed on `(0, δ)` by lem:soft-generic (i)/(iii); the subdivision step reuses CS3 §A verbatim.
5. U103-B piece bijection under `insert`; fallback: avoid `Piece` and prove `P_A = P₁P₂` through mp:blocks
   (`SM.blocks`) on the record of `D_A` directly — heavier.
6. Interface drift (FR-CC-9): freeze the floor lane's `a_floor` signature before U103-F/U110-J start; the adapter is
   trivial if the bound is stated on `homfly (positiveLift …)` with `cornerSlot` and `mindegAZ`.
7. Estimates: CS3 (a one-to-one carrier law) took 2,511 lines; 110 has five interacting sectors, two floor
   consumptions and three link-move identifications — the 11-15k estimate assumes CS3-like efficiency; the C-S7 lane
   should report by unit, and the FINAL_REVIEW sentence for 110 should be prepared for "sliding branch proved,
   bigon branch stated" as an honest intermediate state.
