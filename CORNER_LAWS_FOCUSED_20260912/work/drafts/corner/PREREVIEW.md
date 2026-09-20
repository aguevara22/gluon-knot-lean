# PREREVIEW — corner chain statements (rows 103 cb:singleton, 105 lem:corner-values, 110 thm:C-S7, 112 thm:C-soft)

Independent Lean 4 auditor, 2026-09-15 15:53 UTC / 11:53am ET. Object: the FROZEN statements
`work/drafts/corner/Statements_FINAL.lean` (764 lines) with `PLAN_FINAL.md` §4 (units) and §5 (FR-CC-1..15). This is the
pre-review of non-vacuity / fidelity red flags / triviality / truth of the 10 open leaves, NOT the formal fidelity review.
Sources read: sm-3-statesum.tex 4697-4759 (103), 4801-4820 (105), 242-249 (def:uniform), 1688-1700 (def:C), 4576-4600
(thm:floor), 4760-4800 (cb:embedded-rotation), 9-52 (def:decomposition/def:smoothing), 54-90 (lem:carriers);
sm-4-knotlaws.tex 267-300, 650-672, 760-790, 855-908 (110), 984-1147 (112); sm-1-polygons.tex 259-268 (def:interlace),
440-462 (lem:uniformrot), 737-780 (def:walls), 1254-1268 (def:deletion-halves); sm-2-amplitude.tex 996-1016 (def:soft).
Accepted Lean read: CS3.lean 2477-2510, CS5.lean 1-70, Uniqueness.lean 30-95, ALawful.lean 85-135, NamedWallPredicates,
NamedWallSides 58-80, WallGerm, Children, ContactHalfSizes/Indices/Tuples, SoftInsertionTuple, SoftAmplitudeSectors,
SoftGenericLemma (whole statement), UniformDefinition, CarrierCrossings, Interlacement, CornerStateSum, UniformRotation,
Reversal, CarrierCornerPolygon (defs + turn lemmas), CarrierSmoothing, CBProducts 1905-1925, PolynomialBlock 1121-1160,
LinkLaurentRing (coeffAt, mindegAZ), StarGenericLaw, BowTie; work/drafts/floor/Statements_FINAL.lean 350-386.

Checks run (`source /workspace/envs/lean/env.sh; cd work/lean`):
- `lake env lean ../drafts/corner/Statements_FINAL.lean`: 0 errors, 14 `sorry` warnings at the documented lines (208, 223,
  243, 458, 476, 491, 499, 620, 630, 641 = the 10 leaves; 736, 741, 746, 751 = the 4 row theorems). 16 s.
- `lake env lean ../drafts/corner/PREREVIEW_probes.lean` (= Statements_FINAL + 2 imports `SM.StarGenericLaw`, `SM.BowTie` +
  the probes of §6 below): 0 errors. Original in the auditor scratchpad
  `/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/Probe2.lean`.
- `#print axioms`: `corner_values_i`, `cornerHomfly_ne_zero` → [propext, Classical.choice, Quot.sound, lit_homfly, lp_lm,
  lp_lm_uniqueness]; `carrierUniformOrOneDissent_of_signed`, `coeffAt_mul_eq_zero_of_lt_floor` → standard only;
  `CSoftData.exists_generic`, `CSoftData.doubled` → standard + lit_homfly; the assemblies `cb_singleton_of_floor`,
  `thm_C_S7_of`, `thm_C_soft_of_cornerValues` → the same + `sorryAx` (from the leaves only). Matches PLAN_FINAL.

## 0. Verdict

**SATISFIABLE / NON-VACUOUS, no blocking issue.** No provably contradictory hypothesis combination in `CbSingletonData`,
`CornerValuesData`, `CS7Data`, `CSoftData` or the §0 floor interface. Joint satisfiability reduces to the truth of
`FloorTheoremData` (the paper's Theorem 2, refereed) because `example (hF : FloorTheoremData) : CS7Data ∧ CSoftData ∧
CbSingletonData ∧ CornerValuesData` is PROVED in the file (modulo the leaves). Hypothesis non-vacuity is instantiated in
Lean for rows 105 (i) and 112 (all three sectors) and for the floor's turn hypothesis (§2), numerically for row 103 (§2.1),
and structurally for row 110 (no `VertexEdgeAt` germ is constructed anywhere in the accepted library; the hypothesis is
shared verbatim with the accepted `A_lawful.vertex_edge_law` and the consumer `UniquenessHypotheses.vertex_edge`).
Fidelity: every printed clause of the four rows has a field; every field has a printed counterpart; nothing weaker than the
sibling convention (`SM.thm_C_S5` / consumer shape; STRONGER than `SM.thm_C_S3`'s `∃ δ`-restricted form). Triviality: none.
Truth probes: all 10 leaves TRUE; one of them (`s7_universal_extraction`) is PROVED in the probe file in 12 lines
(standard axioms) and can be closed now.

## 1. Compile, axioms, interface copy

- §0 is a verbatim copy of work/drafts/floor/Statements_FINAL.lean 353-385 (`diff` after stripping docstrings: only the
  `section Floor`/`variable` wrapper and the trailing docstring differ). The `SignedUniformOrOneDissent` bridge is PROVED and
  exercised in both branches by the probes (τ = 1 uniform on `star 1`; τ = −1 one-dissent, §6 P4).
- Port hazard (non-blocking, already FR-CC-15): §0 redeclares `SM.AllLeftOrOneRight`, `SM.CarrierUniformOrOneDissent`,
  `SM.FloorTheoremData` under the floor lane's names; the corner module must drop §0 at port or the two modules clash.

## 2. Non-vacuity / satisfiability (Q1)

| structure / hypothesis set | witness | how checked |
|---|---|---|
| `CornerValuesData.embedded_value` (uniform carrier, `m_Q = 0`) and `FloorTheoremData.a_floor`'s hypothesis `CarrierUniformOrOneDissent` | `SM.star 1` (triangle, `Generic` by `star_generic_law`), `S = ∅`, `q = owner … (Sum.inl 0)` | Lean (§6 P2): `CarrierUniform` (τ = 1 via `ccpCornerMark_isTrueCorner` + `ccpCornerPolygon_turn_vertex`), `carrierCrossingCount = 0` (`IsEmpty (Crossing (star 1))`: no remote pair in `ZMod 3`), `CarrierUniformOrOneDissent` via the bridge, and `corner_values_i` then gives `cornerSlot = 0`, `cornerCoefficient = 1` — consistent with the floor conclusion `0 ≤ mindegAZ 1 = 0`. |
| `CSoftData.soft_theorem`: `SoftAdmissible` + nonempty ε-range of generic `P_ε` | `bowTie` (`Generic` by `star_generic_law`), `j = 1` (`turn = −1`), `q = (1, 3)` | Lean (§6 P1): `SoftAdmissible bowTie 1 (1,3)`; `∃ δ > 0, ∀ ε ∈ (0, δ), Generic (softInsertion bowTie 1 (1,3) ε)` from `soft_family_generic` (i). So the `∀ hQ` clause is NOT vacuous on `(0, min ε₁ δ)`. |
| the three sector hypotheses of `sft_same_sign` / `sft_loop` / `sft_mixed` | `bowTie`, `j = 1`, `q = (1,3)` / `(1,−1)` / `(−3,−1)` | Lean (§6 P1): `χ₋ = χ₊ = −τ`, `χ₋ = χ₊ = τ`, `χ₋ ≠ χ₊` respectively, each with `SoftAdmissible`. The sector split is exhaustive and each sector is inhabited. |
| `CbSingletonData.isolated_zero` (uniform carrier with an isolated self-crossing) | limaçon octagon `(1,−2),(8,0),(7,8),(−1,8),(0,2),(3,0),(3,5),(0,4)`, `S = ∅` | numeric (Python, exact rationals): all 8 turns left, no collinear vertex triple (G1), exactly one crossing (edges 4 and 7 at parameters 1/8, 3/8) hence no triple concurrence (G2), `r_A = 2`; the single self-crossing interlaces nothing. Not built in Lean (a `Generic` proof for an 8-gon has no library support beyond the 3- and 4-gons; BowTie.lean spends ~280 lines on the 4-gon). |
| `sg_daughters_rotation`'s ledger on that witness | same octagon, `c` = its crossing | numeric: daughters `Λ₁` (4 corners, all L, rot 1) and `Λ₂` (6 corners, one R, rot 1); `r_A = r₁ + r₂`, `|r_A| = |r₁| + |r₂|`, `d_A = 1−1−2 = −2 = d₁ + d₂ − 2 = 0 + 0 − 2`. The positive lift of `A` is a one-crossing unknot diagram, `H⁺ = 1`, so `c(A) = [a⁻² z⁰] 1 = 0` — the printed conclusion holds on the witness. |
| `CS7Data.vertex_edge_law`: `VertexEdgeAt` + `h₁ h₂` | — | structural: `vertex_halves_children hn g h` PROVES `Generic (firstHalf …) ∧ Generic (secondHalf …)` from `h`, so `(h, h₁, h₂)` is satisfiable iff `h` is; `hn : 3 ≤ n` is implied by `h.1` (`contactSeparated_size : 5 ≤ n`); `g.SideParameter = Ioo 0 radius` is nonempty (`radius_pos`). No `WallGerm` with `VertexEdgeAt` is constructed in SM/CV/Bridge (grep: every occurrence is a hypothesis), so vacuity cannot be excluded in Lean — exactly the status of the accepted `A_lawful.vertex_edge_law`, `UniquenessHypotheses.vertex_edge`, `SM.thm_C_S5` (`CuspAt`). Mathematically a vertex sliding across a remote edge is a standard germ. |
| §0 `FloorTheoremData` internal consistency | — | the two `a_floor` conjuncts are equivalent by `cornerSlot_cast` (harmless redundancy, floor lane's business); `z_parity` is never consumed (FR-CC-10). The one-dissent alternative and the ℤ conjunct on the WHOLE polynomial are the two load-bearing features (PLAN §2.1); both present. |

Provably contradictory combinations: **none found**. Specifically checked: `VertexEdgeAt` ∧ half-genericity (implied, not
contradictory); `SoftAdmissible` ∧ `0 < ε < ε₁` ∧ `Generic P_ε` (inhabited); `CarrierUniform` ∧ `carrierCrossingCount = 0`
(inhabited); `CarrierUniform` ∧ isolated self-crossing (inhabited numerically); `SignedUniformOrOneDissent` with the
one-dissent branch at `τ = −1` (bridge closes it).

## 3. Fidelity red flags (Q2)

### 3.1 Printed clause → field (all four rows): complete
- 103 (sm-3:4699-4700): "uniform carrier `A` of `S`" → `hS : IsDecomposition`, `A : Component`, `CarrierUniform`; "self-crossing
  label `c`" → `c ∈ carrierCrossings hn hP S A` (def:smoothing's crossings of `Q`, lem:carriers (iii)); "interlaces no other
  self-crossing of `A`" → `∀ c' ∈ carrierCrossings …, c' ≠ c → ¬ Interlaces hn hP c c'` (`Interlaces` = def:interlace's
  alternating visits, symmetric by `interlaces_symm`); "`c(A) = 0`" → `cornerCoefficient … = 0`. One field. ✓
- 105 (4803-4806): (i) `CarrierUniform → carrierCrossingCount = 0 → |carrierRotation| = 1 ∧ cornerSlot = 0 ∧
  cornerCoefficient = 1` (real `r_Q` = def:uniform's `rot(Q)`; `d_Q` in ℤ = def:C's slot); (ii) = 103's clause at `(q, y)`.
  Two fields, one per printed item. ✓
- 110 (sm-4:269-272): "simple vertex–edge wall at `(M;a)`" → `g.VertexEdgeAt M a`, which is LITERALLY def:walls (V)
  (`ContactSeparated` = `M ∉ {a−1,a,a+1,a+2}`, `pointZeros = {contactSupport M a}`, `concurrences = ∅`, `center M ∈
  edgeInterior center a`, `SignChanges (χ_{a,a+1,M})`); "of bigon or sliding type" → exhaustive (`vertexEdge_bigon_or_sliding`;
  `BigonAt` = def:walls' `χ_{a,a+1,M−1}(P(0)) = χ_{a,a+1,M+1}(P(0))`); "halves λ₁, λ₂ (def:deletion-halves)" → `firstHalf`
  = `(μ_M, …, μ_a)` (size `(a−M).val + 1`), `secondHalf` = `(μ_M, μ_{a+1}, …, μ_{M−1})` (index 0 ↦ M, i ≥ 1 ↦ a + i), both
  at the centre — matches sm-1:1258-1262; "`s = χ_{a,a+1,M}(P₋)`" → `g.contactSign M a` (= `chi (sideTuple false sideBase)
  a (a+1) M`, constant along `P₋` by `contactSign_eq_at`, `CS7Data.contactSign_literal` PROVED); the law with `C(P±)` at all
  side parameters. One field. ✓
- 112 (sm-4:986-989): generic `P` (`hP`, `hn`), vertex `j`, admissible `q` (`SoftAdmissible` = def:soft's three determinant
  conditions verbatim), `P_ε = softInsertion P j q ε` (accepted def:soft rendering), `χ_± = softAttachmentMinus/Plus`
  (`−sgn det(ℓ_{j−1}, q)`, `−sgn det(q, ℓ_j)` — def:soft's formulas), "for all sufficiently small `ε > 0`" → `∃ ε₁ > 0, ∀ ε ∈
  (0, ε₁)`, the identity in ℚ with `softAmplitudeMultiplier = (χ₋+χ₊)/2`. One field. ✓

### 3.2 Field → printed counterpart: nothing outside FR-CC-1..15
All deviations are recorded: `c' ≠ c` redundant (FR-CC-1); binder `hn/hS` (FR-CC-2); `m_Q = 0` as the definition of embedded
(FR-CC-4); real `r_Q` (FR-CC-5); `hn : 3 ≤ n` in `CS7Data` though `VertexEdgeAt` forces `n ≥ 5` (FR-CC-7 "bundle parameter");
`contactSign` (FR-CC-8); quantified `h₁ h₂` (FR-CC-9); `∀ tp tm` (FR-CC-10); ℚ multiplier (FR-CC-11); `∀ hQ` (FR-CC-12).
Companions (`CS7Data.bigon/.sliding/.contactSign_literal`, `CSoftData.exists_generic/.doubled`,
`CornerValuesData.embedded_rotationInt`) are theorems, not fields.

### 3.3 Fixed-name shapes vs the accepted siblings
| | `SM.thm_C_S3 : CS3Data` (SM.CS3) | `SM.thm_C_S5 : CS5Data` (SM.CS5) | `thm_C_S7 : CS7Data` | `thm_C_soft : CSoftData` |
|---|---|---|---|---|
| form | `structure … : Prop`, one field, `∀ (n) [NeZero n]` inside | same | same | same |
| wall hypothesis | spelled-out clauses (`hz hb hc hsc`) | `g.CuspAt j` (def:walls predicate) | `g.VertexEdgeAt M a` (def:walls predicate) | `SoftAdmissible P j q` |
| side parameters | `∃ δ, 0 < δ ∧ δ ≤ radius ∧ ∀ tR tL < δ` (RESTRICTED) | `∀ t : SideParameter` (all) | `∀ tp tm : SideParameter` (all) — as CS5, as the consumer `UniquenessHypotheses.vertex_edge`, as `A_lawful.vertex_edge_law` | `∃ ε₁ > 0, ∀ ε ∈ (0, ε₁)` — as `A_lawful.soft_theorem` and `UniquenessHypotheses.soft` |
| `hn` | parameter `hn : 3 ≤ n` (with `n+1`) | derived from `h.1` | parameter `hn : 3 ≤ n` (consumer's shape; redundant, FR-CC-7) | parameter (as both siblings) |
| genericity of derived polygons | `generic_deleteVertex hn hz hb hc` (proof term inline) | — | `h₁ h₂` quantified (consumer's shape); `A_lawful` instead ASSERTS `Generic λᵢ ∧ …` in the conclusion — equivalent by `vertex_halves_children` | `∀ hQ` (consumer's shape); `A_lawful` has `∃ hQ` — recovered by the PROVED companion `exists_generic` |
Nothing is weaker than the sibling convention; the S7 shape is strictly stronger than CS3's `∃ δ` form and identical to the
consumer's. The only formal weakening relative to an accepted sibling is `∀ hQ` vs `A_lawful.soft_theorem`'s `∃ hQ`
(FR-CC-12), closed by `CSoftData.exists_generic` via the accepted `soft_family_generic`.

### 3.4 Non-blocking fidelity notes (none new; for the AUTHOR_NOTES)
1. `CS7Data.vertex_edge_law` takes `hn : 3 ≤ n` although `h.1` gives `5 ≤ n` (`contactSeparated_size`) — redundant, kept for
   the consumer's shape; harmless.
2. `sg_daughters_rotation` does NOT assume isolation (`hiso`) — the ledger is true for ANY self-crossing `c` of a uniform `A`
   with `insert c S` a decomposition. This is a strength (the bigon route's "singleton rows have a uniform and a one-dissent
   daughter", sm-4:861-863, can reuse it), not a fidelity issue; worth a docstring sentence.
3. The docstring of `CbSingletonData` says "in `G_P`" for `Interlaces`; `Interlaces` is the geometric alternating-visit
   relation of def:interlace, which IS `G_P`'s edge relation — consistent.

## 4. Triviality (Q3): none
- `CS7Data`: hypotheses satisfiable iff `VertexEdgeAt` is (shared with accepted siblings); the conclusion is a genuine
  identity between four state sums.
- `CSoftData`: `∀ hQ` is inhabited on a nonempty ε-range (§2); the conclusion `C(P_ε) = ((χ₋+χ₊)/2) C(P)` is not forced by any
  hypothesis (e.g. the mixed sector forces `C(P_ε) = 0`, a real claim).
- `CbSingletonData`: inhabited (limaçon); on the witness `c(A) = 0` is a genuine value (`d_A = −2`, `H⁺ = 1`).
- `CornerValuesData` (i): inhabited (`star 1`); values `|r| = 1, d = 0, c = 1` are computed, not forced — and PROVED.
- No hypothesis of any field is refutable (`Interlaces` requires `x ≠ y` so `hiso` at `c' = c` is not contradictory; `τ ≠ 0`
  in `CarrierUniform` is satisfiable).

## 5. Truth probes of the 10 open leaves (Q4)

| leaf (unit) | verdict | one-line reason |
|---|---|---|
| `sg_isolated_undominated` (U103-A) | TRUE | `c ∉ S` (def of `carrierCrossings`); `c ∉ N(S)` else its visits split (`neighbor_visits_separated`); an `x ∈ U(S)` interlacing `c` has both visits on one carrier (`nonneighbor_visits_together`) which must be `A` by noncrossing (iv), so `x ∈ carrierCrossings A`; then `hiso` + `interlaces_symm` empties `N({c}) ∩ U(S)` and `greedy_step` gives `U(S') = U(S) ∖ {c}`. |
| `sg_daughters_products` (U103-D) | TRUE | smoothing one self-crossing of `A` splits exactly `A` into two nonempty daughters (`smoothingSuccessor_insert_child_data`, `component_card_insert`), the selected visits of `c` going to the daughters by the incoming-visit convention (owner-iff); a self-crossing `x ≠ c` of `A` does not interlace `c` so both its visits lie in one arc ⇒ `cc_A = {c} ⊔ cc₁ ⊔ cc₂`; cb:products at `S` and `S'` with `blockPoly {c} = 1` (lc:single-crossing) gives `P_A = P₁P₂`. Heaviest leaf (block redistribution), but the statement is the printed eq. cb:singleton-products. |
| `sg_daughters_rotation` (U103-E) | TRUE | inherited corners keep their direction pairs (corner edges are positive multiples of the ORIGINAL edges, `corner_polygons.2.1`, and the edge through the crossing point keeps its direction when cut), the two new smoothing turns are `sgn det(dᵢ,dⱼ)` and its negative (lem:carriers (ii)) with principal angles cancelling (antisymmetry, `det ≠ 0`) ⇒ `r_A = r₁ + r₂`; one daughter is uniform of sign τ, the other one-dissent (≥ 3 corners each); `uniform_rotation` (i)/(iii) puts τ·rᵢ ≥ 1 and τ·r_A ≥ 1 ⇒ `|r_A| = |r₁| + |r₂|`; `carrierRotationInt_cast` transfers to ℤ. Verified numerically on the limaçon (2 = 1 + 1). Isolation is not needed. |
| `s7_sliding_law_at` (U110-E) | TRUE | the printed sliding branch (sm-4:300-406) cites neither thm:floor nor cb:singleton (grep) and is refereed; the leaf is that branch at one side parameter below a radius — the side-parameter reduction is PROVED (`cornerStateSum_side_eq`). Not independently re-derived here (≈100 TeX lines of transport). |
| `s7_bigon_law_at` (U110-K) | TRUE | the printed bigon branch (407-874), refereed; floor at the half contact carriers (uniform for ε=1, one-dissent for ε=0 — both are `SignedUniformOrOneDissent`, hence in the §0 domain via the bridge) and cb:singleton at one-newborn rows, both explicit parameters. Feasibility risk FR-CC-14 (RII/RI witnesses), not a truth risk. |
| `s7_universal_extraction` (U110-G) | TRUE — PROVED | in the probe file (`probe_universal_extraction`, standard axioms): `aInv*aInv = single (−2,0) 1`, `aInv*z = single (−1,1) 1` (`AddMonoidAlgebra.single_mul_single`), then Mathlib `AddMonoidAlgebra.coeff_single_mul_apply` shifts the exponent. Consistent with `lp_core.skein` (`a P₊ − a⁻¹ P₋ = z P₀` ⇒ `P₊ = a⁻² P₋ + a⁻¹ z P₀`). Recommend closing the leaf now. |
| `s7_corner_product` 2nd conjunct (U110-J) | TRUE | `(fg)(k₁+k₂, 0) = Σ f(d₁,e₁) g(d₂,e₂)` over `(d₁,e₁)+(d₂,e₂) = (k₁+k₂,0)`; `dᵢ ≥ mindegAZ ≥ kᵢ` forces `dᵢ = kᵢ`, and `eᵢ ≥ 0` (the `hz` hypotheses — NECESSARY: without them `(k₁, e)+(k₂, −e)` terms survive) forces `eᵢ = 0`; the sum is the single term `f(k₁,0) g(k₂,0)` (also correct when `kᵢ < mindegAZ`: both sides 0). |
| `sft_same_sign` (U112-C) | TRUE | with the accepted `soft_family_generic` (ii): turns at `M, M_ε` are `−χ₋ = −χ₊ = τ`, all other turns and determinant signs persist; (iv): same Gauss word ⇒ same supports; carriers correspond by contracting `M_ε` (uniformity ↔), rotations equal (integer + continuity), coefficients equal (record isomorphism); `ℓ(P_ε) = ℓ(P) + [τ = 1]` ⇒ `C(P_ε) = (−1)^{[τ=1]} C(P) = −τ C(P)`. Multiplier check: `(−τ−τ)/2 = −τ` ✓ (assembly PROVED). |
| `sft_mixed` (U112-B) | TRUE | (i): the soft edge carries no crossing visit, so `M_ε` is the traversal successor of `M` (`Carrier.markSuccessor_vertex_of_no_crossing`) in EVERY carrier through `M`; they are consecutive corners with turns `−χ₋ ≠ −χ₊` (`ccpCornerPolygon_turn_vertex`), so no decomposition is uniform and `C(P_ε) = 0` (thm:C-S5's argument). Multiplier `(1 + (−1))/2 = 0` ✓. |
| `sft_loop` (U112-D) | TRUE | (iv)-loop: newborn `y` has adjacent visits (`nextGaussVisit a = b`, no visit between) ⇒ isolated; supports omitting `y`: `y` is an isolated self-crossing of its carrier ⇒ `hCV.isolated_zero` kills uniform terms (non-uniform ones are excluded anyway); `S ∪ {y}`: the triangle `(b, M, M_ε)` is crossing-free with three turns `−τ` ⇒ `corner_values_i` gives 1; the residual cycle replaces `M` (turn τ) by the smoothing corner `y` (turn τ, (ii): `sgn det(u, D_ε) = τ`) ⇒ uniformity ↔, rotations/coefficients equal; `ℓ(P_ε) − ℓ(P) = −[τ=1] + 2[τ=−1]`, one more selected crossing ⇒ multiplier `(−1)^{−[τ=1]+2[τ=−1]+1} = τ` (exponent 0 for τ=1, 3 for τ=−1) ✓ `(τ+τ)/2 = τ`. Longest 112 leaf; depends on `hCV` as printed. |

DOUBTFUL: none. FALSE: none. The three leaves whose truth rests on the refereed printed proof without an independent
re-derivation here are `s7_sliding_law_at`, `s7_bigon_law_at`, `sft_loop` (each ≥ 70 TeX lines); their STATEMENTS are the
printed per-branch/per-sector claims and their hypotheses are inhabited (§2).

## 6. Probe file (work/drafts/corner/PREREVIEW_probes.lean; 0 errors)
P1 `probe_soft_same_sign / _loop / _mixed`: `SoftAdmissible bowTie 1 q` and the sector equations for `q = (1,3), (1,−1),
(−3,−1)`; `probe_soft_nonvacuous`: generic `P_ε` on `(0, δ)`. P2 `probe_star1_uniform_embedded`: on `star 1`, `S = ∅`,
a component that is `CarrierUniform`, `carrierCrossingCount = 0`, `CarrierUniformOrOneDissent`, `cornerSlot = 0`,
`cornerCoefficient = 1` (axioms: standard + lit_homfly, lp_lm, lp_lm_uniqueness). P3 `probe_universal_extraction`: the
leaf `s7_universal_extraction` PROVED (standard axioms). P4: the bridge on the `τ = −1` one-dissent branch.

## 7. Lists for the executor

BLOCKING: none.

NON-BLOCKING (recommendations):
1. Close `s7_universal_extraction` now with the 12-line probe proof (copy from `PREREVIEW_probes.lean`, section P3); it
   removes one `sorry` from U110-G's statement layer at zero risk.
2. Docstring of `sg_daughters_rotation`: say explicitly that isolation is not assumed (reusable for sm-4:861-863).
3. `CS7Data`: the redundant `hn : 3 ≤ n` (implied by `h.1`) is the consumer's shape — keep, but FR-CC-7 could name the
   implication `contactSeparated_size`.
4. Port hazard (FR-CC-15): §0 must be deleted when the floor module lands (same names in `SM`).
5. Non-vacuity of `CS7Data` is only structural (no `VertexEdgeAt` germ exists in the accepted library); consider a small
   constructed germ as library material later — the same gap exists for the accepted `thm_C_S5` and `A_lawful`, so it is
   not this lane's blocker.
6. `s7_corner_product`'s `hz₁ hz₂` hypotheses are load-bearing (see §5); the consumer must discharge them via
   `lp_core.knot_support` on the two half contact carriers — already planned (U110-J), just confirming they cannot be dropped.
